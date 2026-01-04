import Std.Data.HashSet
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
    termination_by Nat.sqrt n + 1 - d
    decreasing_by
      simp_wf
      have hd : d ≤ Nat.sqrt n := Nat.le_sqrt.mpr (Nat.le_of_not_gt h)
      omega
    go 2

/-- Generate all primes ≤ `limit`. -/
def generatePrimesUpTo (limit : ℕ) : List ℕ :=
  let rec go (p : ℕ) (acc : List ℕ) : List ℕ :=
    if h : p > limit then
      acc.reverse
    else
      let acc' := if isPrime p then p :: acc else acc
      go (p + 1) acc'
  termination_by limit + 1 - p
  decreasing_by
    simp_wf
    have _ : p ≤ limit := Nat.le_of_not_gt h
    omega
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
  decreasing_by
    have _ : p < end_ := Nat.lt_of_not_ge h
    omega
  go (start + 1) []

/-- Compute the set of values `(p - q) / 2` for `p` in `primesInInterval`, `q` in `allPrimes`,
    skipping `q = n`. -/
def computeDifferences (primesInInterval allPrimes : List ℕ) (n : ℕ) : HashSet ℤ :=
  primesInInterval.foldl (init := {}) fun diff p =>
    allPrimes.foldl (init := diff) fun diff q =>
      if q = n then
        diff
      else
        let value := ((p : ℤ) - (q : ℤ)) / 2
        diff.insert value

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
  let printer : FileLogger := {}
  let upperBound : ℕ := 2 ^ maxExp
  let start : ℕ := 2 ^ minExp
  let toFloat (k : ℕ) : Float := Float.ofNat k
  let mut ngap : ℕ := 0
  let mut minGap : Float := toFloat 2 * toFloat start
  let mut log2 : ℕ := minExp
  printer.info s!"Starting test for 2^{minExp} to 2^{maxExp}"
  -- Generate initial primes ≤ start
  let mut primes : List ℕ := generatePrimesUpTo start
  -- Generate initial primes in (start, 2 * start)
  let mut primesInInterval : List ℕ := generatePrimesInInterval start (2 * start)
  -- Next candidate to check for primality
  let mut r : ℕ := 2 * start
  -- Main iteration over n from start to upperBound (inclusive)
  let mut n := start
  while n ≤ upperBound do
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
      r := r + 1
    -- Compute D = {(p - q) / 2}
    let D := computeDifferences primesInInterval primes n
    let logSquare : Float := (Float.log (toFloat 2 * toFloat n)) ^ (toFloat 2)
    let countD : ℕ := D.size
    let gap : Float := logSquare - (toFloat (n - 3) - toFloat countD)
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
      printer.info s!"Minimum gap between 2^{log2 - 1} and 2^{log2} \
      for N = {ngap} with G(N) = {minGap}"
      minGap := toFloat 2 * toFloat n
    n := n + 1
  printer.info s!"Finished test for 2^{minExp} to 2^{maxExp}"

/-- Example: run the experiment from 2^2 to 2^14 (like the Python `__main__`). -/
def main : IO Unit := do
  test 2 14
