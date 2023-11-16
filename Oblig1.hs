{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Move guards forward" #-}

module Oblig1 where

import Control.Applicative (Alternative (empty, many, (<|>)))
import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State
import Data.List (genericLength, intersperse, transpose)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import System.Exit
import System.IO
import Text.Read (reads)

-- | A data type to represent expressions that can be evaluated to a number.
-- This type is parametric over both the number type and the cell reference type.
data Expression number cell
  = -- | Reference to another cell
    Ref cell
  | -- | Constant numerical value
    Constant number
  | -- | Summation over a range of cells
    Sum (CellRange cell)
  | Add
      (Expression number cell)
      -- ^ Left operand of addition
      (Expression number cell)
      -- ^ Right operand of addition
  | Mul
      (Expression number cell)
      -- ^ Left operand of multiplication
      (Expression number cell)
      -- ^ Right operand of multiplication
  deriving (Eq, Ord)

instance (Show number, Show cell) => Show (Expression number cell) where
  show (Ref cell) = "!" ++ show cell
  show (Constant n) = show n
  show (Sum (Box ul lr)) = "SUM(" ++ show ul ++ ":" ++ show lr ++ ")"
  show (Add a b) = "(" ++ show a ++ "+" ++ show b ++ ")"
  show (Mul a b) = "(" ++ show a ++ "*" ++ show b ++ ")"

data CellRange cell = Box
  { upperLeft :: cell,
    lowerRight :: cell
  }
  deriving (Eq, Ord, Show)

-- | The ranged class gives a method of indexing ranges of cells
--   in the spreadsheet
class (Ord cell, Show cell) => Ranged cell where
  data Dimension cell
  cellRange :: Dimension cell -> CellRange cell -> Set cell

-- | A data type representing a sheet.
-- It consists of a name and a mapping from cell references to expressions.
data Sheet number cell = Sheet
  { -- | The name of the sheet
    name :: String,
    -- | The dimension of the sheet
    dimension :: Dimension cell,
    -- | The content of the sheet as a mapping from cell references to expressions
    content :: Map cell (Expression number cell)
  }

-- | CellRef is the standard way to refer to a cell in the spreadsheet.
data CellRef = Cell {column :: Char, row :: Integer}
  deriving (Eq, Ord)

instance Show CellRef where
  show (Cell c r) = c : show r

instance Ranged CellRef where
  data Dimension CellRef = Dimension
    { columns :: [Char],
      rows :: [Integer]
    }
  cellRange :: Dimension CellRef -> CellRange CellRef -> Set CellRef
  cellRange (Dimension cols rows) (Box upperLeft lowerRight) =
    Set.fromList [Cell col row | col <- cols, row <- rows, inRange (Cell col row)]
    where
      inRange (Cell c r) =
        c >= column upperLeft
          && c <= column lowerRight
          && r >= row upperLeft
          && r <= row lowerRight

-- | A sample spreadsheet using Double for numeric type
sheet1 :: Sheet Double CellRef
sheet1 =
  Sheet
    { name = "Sheet1",
      -- \^ Name of the sheet
      dimension = Dimension "ABC" [1 .. 3],
      content =
        Map.fromList
          [ ((Cell 'A' 1), Constant 12),
            ((Cell 'B' 1), Mul (Ref (Cell 'A' 1)) (Ref (Cell 'A' 2))),
            ((Cell 'C' 1), Ref (Cell 'C' 3)),
            ((Cell 'A' 2), Constant 4),
            ((Cell 'B' 2), Add (Ref (Cell 'B' 1)) (Ref (Cell 'A' 2))),
            ((Cell 'C' 2), Constant 0),
            ((Cell 'A' 3), Constant 9),
            ( (Cell 'B' 3),
              Sum (Box (Cell 'A' 1) (Cell 'B' 2))
            ),
            ((Cell 'C' 3), Constant 0)
          ]
    }

sheet2 :: Sheet Double CellRef
sheet2 =
  Sheet
    { name = "Sheet1",
      -- \^ Name of the sheet
      dimension = Dimension "ABC" [1 .. 2],
      content =
        Map.fromList
          [ ((Cell 'A' 1), Constant 12),
            ((Cell 'B' 1), Mul (Constant 4) (Ref (Cell 'A' 2))),
            ((Cell 'C' 1), Add (Ref (Cell 'A' 1)) (Ref (Cell 'C' 2))),
            ((Cell 'A' 2), Constant 2),
            ((Cell 'B' 2), Constant 4),
            ((Cell 'C' 2), Sum (Box (Cell 'A' 1) (Cell 'C' 1)))
          ]
    }

-- | Evaluate an expression within the context of a sheet.
-- Return Nothing if the expression cannot be evaluated.

{-
evaluate ::
  (Num number, Ranged cell) =>
  Sheet number cell ->
  Expression number cell ->
  Maybe number
evaluate sheet (Ref cell) =
  case Map.lookup cell (content sheet) of
    Just ex -> evaluate sheet ex
    Nothing -> Nothing
evaluate _ (Constant n) = Just n
evaluate sheet (Sum cells) = do
  let cellList = Set.toList $ cellRange (dimension sheet) cells
  values <- sequence [evaluate sheet (Ref cells) | cells <- cellList]
  return (sum values)
evaluate sheet (Add expr1 expr2) = do
  val1 <- evaluate sheet expr1
  val2 <- evaluate sheet expr2
  return (val1 + val2)
evaluate sheet (Mul expr1 expr2) = do
  val1 <- evaluate sheet expr1
  val2 <- evaluate sheet expr2
  return (val1 * val2)

-}

evaluate :: Sheet Double CellRef -> Expression Double CellRef -> Maybe Double
evaluate sheet expr = evaluateHelper sheet expr Set.empty

evaluateHelper :: Sheet Double CellRef -> Expression Double CellRef -> Set.Set CellRef -> Maybe Double
evaluateHelper sheet (Ref cell) visited
  | Set.member cell visited = Nothing -- Detect cyclic reference
  | otherwise = case Map.lookup cell (content sheet) of
      Just ex -> evaluateHelper sheet ex (Set.insert cell visited)
      Nothing -> Nothing
evaluateHelper _ (Constant n) _ = Just n
evaluateHelper sheet (Sum cells) visited = do
  let cellList = Set.toList $ cellRange (dimension sheet) cells
  values <- sequence [evaluateHelper sheet (Ref cell) visited | cell <- cellList]
  return (sum values)
evaluateHelper sheet (Add expr1 expr2) visited = do
  val1 <- evaluateHelper sheet expr1 visited
  val2 <- evaluateHelper sheet expr2 visited
  return (val1 + val2)
evaluateHelper sheet (Mul expr1 expr2) visited = do
  val1 <- evaluateHelper sheet expr1 visited
  val2 <- evaluateHelper sheet expr2 visited
  return (val1 * val2)

-- The type of parsers
newtype Parser a = Parser {runParser :: String -> Maybe (String, a)}

-- Functor instance for Parser
instance Functor Parser where
  fmap f p = Parser (fmap (id *** f) . runParser p)

-- Applicative instance for Parser
instance Applicative Parser where
  pure x = Parser (\s -> Just (s, x))
  f <*> x = Parser $ \s -> do
    (s', f') <- runParser f s
    (s'', x') <- runParser x s'
    return (s'', f' x')

-- Monad instance for Parser
instance Monad Parser where
  return = pure
  p >>= f =
    Parser
      ( \s -> do
          (s', x) <- runParser p s
          runParser (f x) s'
      )

-- Alternative instance for Parser
instance Alternative Parser where
  empty = Parser $ const Nothing
  p <|> q = Parser $ \s -> runParser p s <|> runParser q s

-- A set of utility parsers

-- | Parse a single character
pChar :: Parser Char
pChar = Parser pHead
  where
    pHead "" = Nothing
    pHead (c : cs) = Just (cs, c)

exactChar :: Char -> Parser ()
exactChar c = do
  x <- pChar
  guard (x == c)

-- | Eat a single space
pSpace :: Parser ()
pSpace = exactChar ' '

-- | Eat a single newline
pNewLine :: Parser ()
pNewLine = exactChar '\n'

-- | Parse a keyword
keyword :: String -> Parser ()
keyword [] = return ()
keyword (k : ks) = do
  c <- pChar
  guard (c == k)
  keyword ks

between :: Parser a -> Parser b -> Parser c -> Parser c
between pOpen pClose pContent = do
  _ <- pOpen
  x <- pContent
  _ <- pClose
  return x

-- | Parse parenthesis
inParenthesis :: Parser a -> Parser a
inParenthesis = between (exactChar '(') (exactChar ')')

-- | Parse brackets
inBrackets = between (exactChar '[') (exactChar ']')

-- | Parse an operator
pOperator :: String -> (t -> t -> t) -> Parser t -> Parser t
pOperator symbol constructor pOperand = do
  a <- pOperand
  rest a
  where
    rest a =
      ( do
          keyword symbol
          b <- pOperand
          rest (constructor a b)
      )
        <|> return a

-- | Convert a Read instance to a parser
pRead :: (Read a) => Parser a
pRead =
  Parser
    ( \s -> case reads s of
        [] -> Nothing
        ((v, s) : _) -> Just (s, v)
    )

-- | Parse cell expressions
pExpression ::
  (Read number) =>
  Parser (Expression number CellRef)
pExpression = pAdd <|> pMul <|> pTerm

-- | Parse an atomic term
pTerm :: Read number => Parser (Expression number CellRef)
pTerm =
  inParenthesis pExpression
    <|> pConstant
    <|> pRef
    <|> pSum

-- | Parse a numeric constant
pConstant :: (Read number) => Parser (Expression number cell)
pConstant = Constant <$> pRead

-- | Parse a cell name
pCell :: Parser CellRef
pCell = do
  c <- pColName
  Cell c <$> pRowNumber

-- | Parse a cell reference
pRef :: Parser (Expression number CellRef)
pRef = do
  _ <- exactChar '!'
  Ref <$> pCell

-- | Parse a multiplication expression
pMul :: Read number => Parser (Expression number CellRef)
pMul = pOperator "*" Mul pTerm

-- | Parse an addition expression
pAdd :: Read number => Parser (Expression number CellRef)
pAdd = pOperator "+" Add pMul

-- | Parse a sum of cell refences like SUM(A1:C3)
pSum :: Parser (Expression number CellRef)
pSum = do
  _ <- keyword "SUM"
  (start, end) <-
    inParenthesis
      ( do
          startCell <- pCell
          _ <- exactChar ':'
          endCell <- pCell
          return (startCell, endCell)
      )
  return (Sum (Box start end))

-- Now follows parsers for the sheet structure itself

alphanum :: Char -> Bool
alphanum x = elem x (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'])

alpha :: Char -> Bool
alpha x = elem x ['A' .. 'Z']

num :: Char -> Bool
num x = elem x (['0' .. '9'])

-- | Parse a row number
pRowNumber :: Parser Integer
pRowNumber = Parser (\s -> Just (dropWhile num s, read (takeWhile num s) :: Integer))

-- | Parse a column name
pColName :: Parser Char
pColName = do
  c <- pChar
  guard (alpha c)
  return c

-- | Parse a sheet name
pSheetName :: Parser String
pSheetName = Parser (\s -> Just (dropWhile alphanum s, takeWhile alphanum s))

-- | Parse a row, starting with "[n]" indicating the row number
pRow :: Read number => String -> Parser (Integer, [(CellRef, Expression number CellRef)])
pRow cols = do
  row <- inBrackets pRowNumber
  many pSpace
  cells <- many (inBrackets pExpression <* many pSpace)
  return (row, [((Cell col row), ce) | (ce, col) <- zip cells cols])

-- | Parse a spreadsheet
pSheet :: (Read number) => Parser (Sheet number CellRef)
pSheet = do
  name <- inBrackets pSheetName
  many pSpace
  cols <- many (inBrackets pColName <* many pSpace)
  pNewLine
  rows <- many (pRow cols <* many pSpace <* pNewLine)
  let dim = Dimension cols (fst <$> rows)
  return (Sheet name dim (Map.fromList (concat $ snd <$> rows)))

-- | Utility function to pad a list of columns to
--   specified lengths
padColumns :: [Integer] -> [String] -> String
padColumns lengths columns = concat $ intersperse " " $ zipWith pad lengths columns
  where
    pad len str = zipWith const (str ++ repeat ' ') [0 .. len - 1]

-- | Pretty print a spreadsheet
instance (Show number) => Show (Sheet number CellRef) where
  show sheet = unlines (padColumns maxWidths <$> printedRows)
    where
      bracket s = "[" ++ s ++ "]"
      printedRows =
        (bracket (name sheet) : ((bracket . pure) <$> columns (dimension sheet)))
          : [ bracket (show r)
                : [ maybe
                      ""
                      (bracket . show)
                      ( Map.lookup
                          (Cell c r)
                          (content sheet)
                      )
                    | c <- columns (dimension sheet)
                  ]
              | r <- rows (dimension sheet)
            ]
      maxWidths = (maximum . map genericLength) <$> transpose printedRows

--  | Read a spreadsheet from file, evaluate and print it
getSpreadSheet :: FilePath -> IO (Sheet Double CellRef)
getSpreadSheet file = do
  unparsed <- readFile file
  case runParser pSheet unparsed of
    Nothing -> do
      hPutStrLn stderr "No spreadsheet found"
      exitWith (ExitFailure 1)
    (Just (_, sheet)) -> return sheet

--  | Read a spreadsheet from file, evaluate and print it
runSpreadSheet :: FilePath -> IO (Sheet Double CellRef)
runSpreadSheet file = do
  sheet <- getSpreadSheet file
  let evaluated =
        Map.mapMaybe
          ((Constant <$>) . evaluate sheet)
          (content sheet)
  return $
    Sheet
      (name sheet)
      (dimension sheet)
      evaluated
