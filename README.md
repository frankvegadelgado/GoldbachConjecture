# Lean on Goldbach's conjecture

![Goldbach's pyramid](docs/goldbach.png)

This work builds upon [Geometric Insights into the Goldbach Conjecture](https://hackmd.io/@frankvega/S1ABKPZ1Wl).

**Author:** Frank Vega  
**Institution:** Information Physics Institute, Hialeah, FL, USA

**Keywords:** Goldbach conjecture, geometric construction, semiprimes, pigeonhole principle

---

## Abstract

The Goldbach conjecture states that every even integer greater than 2 is the sum of two primes. We present a computational approach that provides strong evidence for a variant: **every even integer ≥ 8 is the sum of two distinct primes**.

Our key insight is a geometric equivalence: this is true if and only if for every $N ≥ 4$, there exists an integer $M$ such that the L-shaped region $N^2 - M^2$ between nested squares has a semiprime area $P \cdot Q$, where $P = N - M$ and $Q = N + M$ are both prime.

Through computational analysis up to $N = 2^{14}$ and application of the pigeonhole principle, we demonstrate this variant holds for all $N ≥ 4$ within our verified range and provide strong theoretical evidence for its general validity.

---

## 1. Introduction

The Goldbach conjecture is one of mathematics' oldest unsolved problems: can every even integer greater than 2 be expressed as the sum of two primes?

We study a variant that excludes identical primes:

> **Variant:** Every even integer ≥ 8 is the sum of two **distinct** primes.

This excludes $4 = 2 + 2$ and $6 = 3 + 3$ while preserving the essence of the original conjecture.

We provide strong computational and theoretical evidence for this variant by connecting it to a surprising geometric property of nested squares.

---

## 2. The Geometric Connection

### Construction

Start with a square $S_N$ of side length $N ≥ 4$. Inside it, place a smaller square $S_M$ of side length $M$ (where $1 ≤ M ≤ N-3$) sharing the same corner. The L-shaped region between them has area:

$$N^2 - M^2 = (N - M)(N + M)$$

Let $P = N - M$ and $Q = N + M$. Then:

- $P + Q = 2N$ (an even number)
- $P \cdot Q = N^2 - M^2$ (the L-shaped area)
- Both $P$ and $Q$ must be odd (same parity)

### The Key Equivalence

**The Goldbach variant is true ⟺ For every $N ≥ 4$, there exists an $M$ making both $P$ and $Q$ prime.**

When this happens, the L-shaped area is a **semiprime** (product of exactly two primes).

![Geometric Construction](docs/geometric.jpg)

**Figure 1:** The L-shaped region between nested squares. For N=5, M=2: P=3 and Q=7 (both prime), giving area 21 = 3×7 and sum 3+7=10.

---

## 3. Why This Connection Matters

For any even number $2N$, finding a Goldbach partition means finding primes $P$ and $Q$ where $P + Q = 2N$.

Geometrically, this is equivalent to finding an $M$ value such that:

- $P = N - M$ is prime
- $Q = N + M$ is prime
- The L-shaped area $P \cdot Q$ is a semiprime

This transforms an arithmetic problem into a geometric search.

---

## Files and Structure

The Lean development is contained in a **single** core file:

- **`GoldbachConjecture.lean`**  
  - Introduces the main predicates and structures (even numbers, semiprimes, squares, L‑shapes, the set $D_N$, and the gap function G(N)).  
  - Encodes the experimental data for G(N) over $4 \le N \le 2^{14}$ (dyadic intervals and minima) and axiomatizes the verified positivity of G(N) and the validity of the Goldbach variant in the tested range.  
  - Develops the analytic bounds on primes and candidate $M$-values and applies a pigeonhole argument to obtain Goldbach partitions for all relevant $N$.  
  - Proves that, under the global inequality $|D_N| > (N-3) - \log^{2}(2N)$, every even integer at least 8 admits a representation as a sum of two distinct primes, and derives corollaries such as a geometric Goldbach statement.

No code snippets are shown here; all implementation details are inside the Lean source file.

## Dependencies and Setup

The project is written for **Lean 4** and relies on **mathlib4**, particularly its number theory and analysis components:

- Prime numbers and prime counting (`Mathlib.NumberTheory.PrimeCounting`)  
- Logarithmic and real analysis tools (`Mathlib.Analysis.SpecialFunctions.Log.Basic`, `Mathlib.Data.Real.Basic`)  
- Basic arithmetic on natural numbers (`Mathlib.Data.Nat.Prime.Basic`)

To work with this repository:

- Install Lean 4 and mathlib4 using the standard community toolchain (e.g., `elan` and `lake`) with a mathlib-enabled project template.
- Ensure that your `lakefile` imports mathlib4 so that all `Mathlib.*` modules used in the source files are available.

Users are expected to be familiar with the Lean 4 ecosystem and mathlib conventions; the repository does not include special build scripts beyond the usual Lean project setup.

## Documentation

The conceptual and mathematical documentation for this Lean codebase is maintained externally:

- **HackMD article (rich exposition with inline math):**  
  “Geometric Insights into the Goldbach Conjecture” – available at  
  
  [https://hackmd.io/@frankvega/S1ABKPZ1Wl](https://hackmd.io/@frankvega/S1ABKPZ1Wl)
  
  This note explains the geometric framework, the definition of the set $D_N$, the gap function G(N), and the computational strategy, using LaTeX-style mathematics in HackMD.

- **MDPI Preprint (formal write‑up):**  
  The work is also available as a preprint at  
  
  [https://www.preprints.org/manuscript/202511.0701/v3](https://www.preprints.org/manuscript/202511.0701/v3)
  
  The preprint presents the full argument, including the equivalence between the geometric construction and the Goldbach variant, the experimental evidence, and the conditional theorem that links the bound on $|D_N|$ to the distinct‑primes Goldbach statement.

These documents are the primary references for understanding the mathematical motivations and theorems formalized in the Lean files.