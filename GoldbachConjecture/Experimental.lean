import Std.Data.HashSet
import Std.Data.HashMap
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Init.Data.Nat.Basic
import Mathlib.Tactic

open Std

/-- Very naive primality test (sufficient for the experiment scale). -/
def isPrime (n : ℕ) : Bool :=
  if n < 2 then
    false
  else
    let rec go (d : ℕ) : Bool :=
      if h : d * d > n then
        true
      else if n % d = 0 then
        false
      else
        go (d + 1)
    termination_by n - d
    decreasing_by
      have hn : n ≥ 2 := by omega
      by_contra! H  -- H: n - (d + 1) ≥ n - d
      have : d ≥ n := by omega
      have hsq : d * d ≥ n * n := Nat.mul_le_mul this this
      have : n * n ≥ 2 * n := by
        exact calc
          n * n ≥ 2 * n := Nat.mul_le_mul_right n hn
      have h_le : d * d ≤ n := by omega
      linarith
    go 2

/-- Next prime strictly greater than `n` (naive). -/
def nextPrime (n : ℕ) : ℕ :=
  let rec go (k : ℕ) : ℕ :=
    if isPrime k then
      k
    else
      go (k + 1)
  termination_by 2 * n + 10 - k
  decreasing_by
    omega
  go (n + 1)

/-- Generate all primes ≤ `limit`. -/
def generatePrimesUpTo (limit : ℕ) : List ℕ :=
  let rec go (p : ℕ) (acc : List ℕ) : List ℕ :=
    if h : p > limit then
      acc.reverse
    else
      let acc' := if isPrime p then p :: acc else acc
      go (p + 1) acc'
  termination_by limit - p
  decreasing_by omega
  go 2 []

/-- Generate all primes in `(start, end)`. -/
def generatePrimesInInterval (start end_ : ℕ) : List ℕ :=
  let rec go (p : ℕ) (acc : List ℕ) : List ℕ :=
    if h : p ≥ end_ then
      acc.reverse
    else
      let acc' := if isPrime p then p :: acc else acc
      go (p + 1) acc'
  termination_by end_ - p
  decreasing_by omega
  go (start + 1) []

/-- Compute the set of values `(p - q) / 2` for `p` in `primesInInterval`, `q` in `allPrimes`,
    skipping `q = n` and duplicates. -/
def computeDifferences (primesInInterval allPrimes : List ℕ) (n : ℕ) : HashSet ℤ :=
  Id.run do
    let mut diff : HashSet ℤ := {}
    for p in primesInInterval do
      for q in allPrimes do
        if q = n then
          continue
        else
          let value : ℤ := (p : ℤ) - (q : ℤ)
          let value := value / 2
          diff := diff.insert value
    return diff

/-- Simple logger: prints to console (can be extended to log to file). -/
structure FileLogger where
  logLevel : String := "INFO"

namespace FileLogger

def info (logger : FileLogger) (msg : String) : IO Unit :=
  IO.println s!"[{logger.logLevel}] {msg}"

end FileLogger

/-- Main execution function for the prime gap experiment,
    analogous to the Python `test` function. -/
def test (minExp maxExp : ℕ) : IO Unit := do
  -- Validate the input
  if minExp = 0 || maxExp = 0 then
    throw <| IO.userError "Input must be two natural numbers (positive)."
  if minExp ≥ maxExp then
    throw <| IO.userError "The first input integer value must be lesser than the second one."

  let printer : FileLogger := { logLevel := "INFO" }

  let upperBound : ℕ := 2 ^ maxExp
  let start : ℕ := 2 ^ minExp
  let mut ngap : ℕ := 0
  let mut minGap : Float := 2 * (start : Float)
  let mut log2 : ℕ := minExp

  printer.info s!"Starting test for 2^{minExp} to 2^{maxExp}"

  -- Generate initial primes ≤ start
  let mut primes : List ℕ := generatePrimesUpTo start

  -- Generate initial primes in (start, 2 * start)
  let mut primesInInterval : List ℕ := generatePrimesInInterval start (2 * start)

  -- Next prime after the initial interval
  let mut r : ℕ :=
    if primesInInterval.isEmpty then
      nextPrime start
    else
      nextPrime (2 * start - 1)

  -- Main iteration over n from start to upperBound
  for n in [start:upperBound+1] do
    -- Add the next prime if n matches the smallest in the interval
    match primesInInterval with
    | [] => pure ()
    | p :: ps =>
      if p = n then
        primes := primes ++ [p]
        primesInInterval := ps
      else
        pure ()

    -- Generate additional primes if needed (primes < 2 * n)
    while r < 2 * n do
      if isPrime r then
        primesInInterval := primesInInterval ++ [r]
      r := nextPrime r

    -- Compute D = {(p - q) / 2}
    let D := computeDifferences primesInInterval primes n
    let logSquare : Float := (Float.log (2 * (n : Float))) ^ 2
    let countD : ℕ := D.size
    let gap : Float := logSquare - ((n - 3 : Float) - (countD : Float))

    if gap ≤ 0 then
      printer.info s!"The Experimental Result failed for {n}: {(n - 3) - countD} ≥ {logSquare}"
      throw <| IO.userError "The Experimental Result failed."
    else if gap < minGap then
      ngap := n
      minGap := gap

    -- Logging progress when crossing powers of 2
    let currentLog2 : ℕ := Nat.log 2 n
    if currentLog2 > log2 then
      log2 := currentLog2
      printer.info s!"Minimum gap between 2^{log2 - 1} and 2^{log2} for N = {ngap} with G(N) = {minGap}"
      minGap := 2 * (n : Float)

  printer.info s!"Finished test for 2^{minExp} to 2^{maxExp}"

/-- Example: run the experiment from 2^2 to 2^14 (like the Python `__main__`). -/
def main : IO Unit :=
  test 2 14
