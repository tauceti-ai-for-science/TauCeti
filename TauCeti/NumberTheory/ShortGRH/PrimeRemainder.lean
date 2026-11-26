/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The remainders `R_q` of the shorter route to GRH

Let `d` be a prime, `χ_K = (·/d)` the Legendre symbol (the character of `K = ℚ(√-d)` when
`d ≡ 3 (mod 4)`), and `q ≥ 1`. The weight `λ_q(n) = Λ(n) (1 - χ_K(n))` on the integers
`n ≡ 1 (mod q)`, and `0` on the others, is nonnegative and at most `2 Λ(n)`. The remainder

`R_q(y) = ∑_{1 ≤ n ≤ y} λ_q(n) (1/n - 1/y) - (log y)/φ(q) - c_q`

is a smoothed count of these prime powers less its main term and a constant `c_q`. The constant
is the real part of `G_q(1)`, where

`G_q(s) = φ(q)⁻¹ (∑_ψ (E'_{ψ χ_K}/E_{ψ χ_K}(s) - E'_ψ/E_ψ(s)) - 1)`,

the sum over all Dirichlet characters `ψ` modulo `q`, and `E_ψ` is `L(s, ψ)` for nonprincipal `ψ`
and the entire function `(s - 1) L(s, ψ)` for principal `ψ`. For odd `d` prime to `q`, `G_q`
continues `∑ λ_q(n) n ^ (-s) - s / (φ(q) (s - 1))` from `re s > 1`, and `c_q` is the constant for
which `R_q(y) → 0`; these analytic properties are not needed for the facts proved here.

The facts are elementary. The sum in `R_q(z)` may be taken over any longer range `1 ≤ n ≤ A` with
the positive part `(1/n - 1/z)⁺`, which vanishes for `n > z`. Comparing the positive parts at two
points `y ≤ z` term by term shows that `R_q(z) - R_q(y)` lies between `-(log z - log y)/φ(q)` and
`(1/y - 1/z) ∑_{n ≤ z} λ_q(n)`; Chebyshev's bound `ψ(z) ≤ (log 4 + 4) z` then gives the slow
variation `|R_q(z) - R_q(y)| ≤ 13 (z - y)/y`.

## Main definitions

* `TauCeti.ShortGRH.entireL`: `E_ψ`, the `L`-function of `ψ`, made entire for principal `ψ`.
* `TauCeti.ShortGRH.quadTwist`: the twist `ψ χ_K` of a character modulo `q`, modulo `q d`.
* `TauCeti.ShortGRH.primeWeight`: the weight `λ_q`.
* `TauCeti.ShortGRH.logDerivMean`: the mean `G_q` of logarithmic derivatives.
* `TauCeti.ShortGRH.remainderConst`: `c_q = re G_q(1)`.
* `TauCeti.ShortGRH.primeRemainder`: the remainder `R_q`.

## Main results

* `TauCeti.ShortGRH.primeWeight_nonneg`, `TauCeti.ShortGRH.primeWeight_le_two_mul_vonMangoldt`:
  `0 ≤ λ_q(n) ≤ 2 Λ(n)`.
* `TauCeti.ShortGRH.sum_primeWeight_mul_posPart_eq`: for `0 < z ≤ A` with `A` an integer,
  `∑_{n=1}^{A} λ_q(n) (A/n - A/z)⁺ = A (R_q(z) + (log z)/φ(q) + c_q)`.
* `TauCeti.ShortGRH.abs_primeRemainder_sub_le`: `|R_q(z) - R_q(y)| ≤ 13 (z - y)/y` for
  `0 < y ≤ z`.

## References

The definitions and facts are those of OneSidedPrimeSumBoundsAndAdmissibleData §0.1 in the
`ShortGRH` family of the Tau Ceti roadmap. They are adapted from the shorter formal proof
https://github.com/lsernau/grh-lean (Apache 2.0, Copyright 2026 Anthropic, PBC), file
`grh/src/New/Reduction/Zeros/PrimeError.lean` (`New.lambdaKResidueClass`, `New.logDerivMean`,
`New.primeRemainder`, `New.lambdaKResidueClass_le_two_mul_vonMangoldt`,
`New.primeRemainder_eq_sum_posPart`, `New.primeRemainder_eq_sum`) and file
`grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean` (`New.abs_primeRemainder_sub_le`), and from
`grh/src/Lib/General/NumberTheory/ImaginaryQuadraticField.lean` (`New.entireL`, `New.quadTwist`).
There the slow variation is proved by writing `R_q` as an integral of the error of the weighted
count; here it is read off term by term. For the orthogonality of characters behind `G_q` see
H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer GTM 74 (2000), Chapters 4 and 7.
-/

public section

noncomputable section

open ArithmeticFunction DirichletCharacter Finset

namespace TauCeti.ShortGRH

open scoped Classical in
/-- The function `E_ψ`: the `L`-function `L(s, ψ)` of a nonprincipal character `ψ`, and the entire
function `(s - 1) L(s, ψ)` (Mathlib's `LFunctionTrivChar₁`, with its residue as value at `1`) of
the principal one. It is entire in both cases. -/
@[expose] def entireL {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  if ψ = 1 then LFunctionTrivChar₁ N else ψ.LFunction

variable (d : ℕ) [Fact d.Prime]

/-- The Legendre symbol `χ_K = (·/d)` as a complex Dirichlet character modulo the prime `d`. -/
def chiK : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

/-- The twist `ψ χ_K` of a character `ψ` modulo `q` by `χ_K = (·/d)`, a character modulo `q d`. -/
def quadTwist {q : ℕ} (ψ : DirichletCharacter ℂ q) : DirichletCharacter ℂ (q * d) :=
  changeLevel (dvd_mul_right q d) ψ * changeLevel (dvd_mul_left d q) (chiK d)

variable (q : ℕ)

/-- The weight `λ_q(n) = Λ(n) (1 - χ_K(n))` for `n ≡ 1 (mod q)`, and `0` for the other `n`; here
`Λ` is the von Mangoldt function and `χ_K(n) = (n/d)` the Legendre symbol. -/
def primeWeight (n : ℕ) : ℝ :=
  vonMangoldt.residueClass (1 : ZMod q) n * (1 - legendreSym d n)

/-- The mean `G_q(s) = φ(q)⁻¹ (∑_ψ (E'_{ψ χ_K}/E_{ψ χ_K}(s) - E'_ψ/E_ψ(s)) - 1)` of logarithmic
derivatives, over all Dirichlet characters `ψ` modulo `q`, with `E_ψ = entireL ψ`. -/
def logDerivMean [NeZero q] (s : ℂ) : ℂ :=
  ((∑ ψ : DirichletCharacter ℂ q,
    (logDeriv (entireL (quadTwist d ψ)) s - logDeriv (entireL ψ) s)) - 1) / q.totient

/-- The constant `c_q = re G_q(1)` of the remainder. -/
def remainderConst [NeZero q] : ℝ := (logDerivMean d q 1).re

/-- The remainder `R_q(y) = ∑_{1 ≤ n ≤ y} λ_q(n) (1/n - 1/y) - (log y)/φ(q) - c_q`. -/
def primeRemainder [NeZero q] (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / n - 1 / y) - Real.log y / q.totient -
    remainderConst d q

variable {d q}

/-- The values `1 - (n/d)` of `1 - χ_K` lie in `[0, 2]`. -/
theorem one_sub_legendreSym_mem_Icc (n : ℕ) : (1 - legendreSym d n : ℝ) ∈ Set.Icc 0 2 := by
  obtain h | h | h : legendreSym d n = 0 ∨ legendreSym d n = 1 ∨ legendreSym d n = -1 :=
    quadraticChar_isQuadratic (ZMod d) _
  all_goals rw [h]; norm_num

/-- **0.1 (a)**, lower bound: `0 ≤ λ_q(n)`. -/
theorem primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight d q n :=
  mul_nonneg (vonMangoldt.residueClass_nonneg _ n) (one_sub_legendreSym_mem_Icc n).1

/-- **0.1 (a)**, upper bound: `λ_q(n) ≤ 2 Λ(n)`. -/
theorem primeWeight_le_two_mul_vonMangoldt (n : ℕ) : primeWeight d q n ≤ 2 * vonMangoldt n := by
  rw [primeWeight, mul_comm 2]
  exact mul_le_mul (vonMangoldt.residueClass_le _ n) (one_sub_legendreSym_mem_Icc n).2
    (one_sub_legendreSym_mem_Icc n).1 vonMangoldt_nonneg

/-- The sum `∑_{1 ≤ n ≤ z} λ_q(n) (1/n - 1/z)` may be taken over any range `1 ≤ n ≤ A` with
`A ≥ ⌊z⌋`, with the positive part `(1/n - 1/z)⁺`, which vanishes for `n > z`. -/
theorem sum_primeWeight_mul_eq_sum_posPart {A : ℕ} {z : ℝ} (hz : 0 < z) (hA : ⌊z⌋₊ ≤ A) :
    ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n * (1 / n - 1 / z) =
      ∑ n ∈ Icc 1 A, primeWeight d q n * (1 / n - 1 / z)⁺ := by
  refine sum_subset_zero_on_sdiff (Icc_subset_Icc_right hA) (fun n hn ↦ ?_) fun n hn ↦ ?_
  · have hzn : z < n := Nat.lt_of_floor_lt (by simp at hn; omega)
    rw [posPart_eq_zero.2 (sub_nonpos.2 (one_div_le_one_div_of_le hz hzn.le)), mul_zero]
  · have hn_le : (n : ℝ) ≤ z := (Nat.le_floor_iff hz.le).1 (mem_Icc.1 hn).2
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
    rw [posPart_eq_self.2 (sub_nonneg.2 (one_div_le_one_div_of_le hn_pos hn_le))]

/-- The weighted count `∑_{1 ≤ n ≤ z} λ_q(n)` is at most `2 (log 4 + 4) z`, by Chebyshev's bound. -/
theorem sum_primeWeight_le {z : ℝ} (hz : 0 ≤ z) :
    ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n ≤ 2 * (Real.log 4 + 4) * z := by
  calc ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, 2 * vonMangoldt n :=
        sum_le_sum fun n _ ↦ primeWeight_le_two_mul_vonMangoldt n
    _ = 2 * Chebyshev.psi z := by
        rw [← mul_sum, Chebyshev.psi, show Icc 1 ⌊z⌋₊ = Ioc 0 ⌊z⌋₊ by ext; simp; omega]
    _ ≤ 2 * ((Real.log 4 + 4) * z) := by gcongr; exact Chebyshev.psi_le_const_mul_self hz
    _ = 2 * (Real.log 4 + 4) * z := by ring

/-- For `a` real and `0 < y ≤ z`, the difference `(a - 1/z)⁺ - (a - 1/y)⁺` lies in
`[0, 1/y - 1/z]`. -/
private theorem posPart_sub_posPart_mem_Icc (a : ℝ) {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    (a - 1 / z)⁺ - (a - 1 / y)⁺ ∈ Set.Icc 0 (1 / y - 1 / z) := by
  have h := one_div_le_one_div_of_le hy hyz
  rcases le_total (a - 1 / y) 0 with h1 | h1 <;> rcases le_total (a - 1 / z) 0 with h2 | h2 <;>
    simp only [posPart_of_nonpos, posPart_of_nonneg, h1, h2, Set.mem_Icc] <;>
    constructor <;> linarith

/-- The smoothed counts at `0 < y ≤ z` differ by an amount between `0` and
`(1/y - 1/z) ∑_{1 ≤ n ≤ z} λ_q(n)`. -/
theorem sum_primeWeight_mul_sub_mem_Icc {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n * (1 / n - 1 / z) -
        ∑ n ∈ Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / n - 1 / y) ∈
      Set.Icc 0 ((1 / y - 1 / z) * ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n) := by
  rw [sum_primeWeight_mul_eq_sum_posPart (hy.trans_le hyz) le_rfl,
    sum_primeWeight_mul_eq_sum_posPart hy (Nat.floor_le_floor hyz), ← sum_sub_distrib, mul_sum]
  refine ⟨sum_nonneg fun n _ ↦ ?_, sum_le_sum fun n _ ↦ ?_⟩
  · rw [← mul_sub]
    exact mul_nonneg (primeWeight_nonneg n) (posPart_sub_posPart_mem_Icc _ hy hyz).1
  · rw [← mul_sub, mul_comm]
    exact mul_le_mul_of_nonneg_right (posPart_sub_posPart_mem_Icc _ hy hyz).2
      (primeWeight_nonneg n)

variable [NeZero q]

/-- The remainder plus its main term and constant is the smoothed count:
`R_q(z) + (log z)/φ(q) + c_q = ∑_{1 ≤ n ≤ z} λ_q(n) (1/n - 1/z)`. -/
theorem primeRemainder_add_log_add_const (z : ℝ) :
    primeRemainder d q z + Real.log z / q.totient + remainderConst d q =
      ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n * (1 / n - 1 / z) := by
  rw [primeRemainder]
  ring

/-- **0.1 (b)**: for `0 < z ≤ A` with `A` an integer,
`∑_{n=1}^{A} λ_q(n) (A/n - A/z)⁺ = A (R_q(z) + (log z)/φ(q) + c_q)`. -/
theorem sum_primeWeight_mul_posPart_eq {A : ℕ} {z : ℝ} (hz : 0 < z) (hzA : z ≤ A) :
    ∑ n ∈ Icc 1 A, primeWeight d q n * ((A : ℝ) / n - A / z)⁺ =
      A * (primeRemainder d q z + Real.log z / q.totient + remainderConst d q) := by
  have hA : (0 : ℝ) ≤ A := hz.le.trans hzA
  have h_scale (n : ℕ) : ((A : ℝ) / n - A / z)⁺ = A * (1 / n - 1 / z)⁺ := by
    rw [posPart_def, posPart_def, mul_max_of_nonneg _ _ hA, mul_zero, mul_sub, mul_one_div,
      mul_one_div]
  rw [primeRemainder_add_log_add_const,
    sum_primeWeight_mul_eq_sum_posPart hz (Nat.floor_le_of_le hzA), mul_sum]
  exact sum_congr rfl fun n _ ↦ by rw [h_scale]; ring

/-- **0.1 (c)**: the remainder varies slowly, `|R_q(z) - R_q(y)| ≤ 13 (z - y)/y` for `0 < y ≤ z`. -/
theorem abs_primeRemainder_sub_le {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    |primeRemainder d q z - primeRemainder d q y| ≤ 13 * ((z - y) / y) := by
  have hz : 0 < z := hy.trans_le hyz
  obtain ⟨hD₀, hD₁⟩ := sum_primeWeight_mul_sub_mem_Icc (d := d) (q := q) hy hyz
  have hS := sum_primeWeight_le (d := d) (q := q) hz.le
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)
  -- The main terms differ by `(log z - log y)/φ(q) ∈ [0, (z - y)/y]`.
  have h_log₀ : 0 ≤ Real.log z - Real.log y := sub_nonneg.2 (Real.log_le_log hy hyz)
  have h_log₁ : Real.log z - Real.log y ≤ (z - y) / y := by
    rw [← Real.log_div hz.ne' hy.ne', sub_div, div_self hy.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hz hy)
  have h_main : (Real.log z - Real.log y) / q.totient ≤ (z - y) / y :=
    (div_le_self h_log₀ hφ).trans h_log₁
  -- The counts differ by at most `(1/y - 1/z) · 2 (log 4 + 4) z ≤ 11 (z - y)/y`.
  have h_log4 : Real.log 4 < 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have h_count : (1 / y - 1 / z) * ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n ≤ 11 * ((z - y) / y) := by
    have h_diff : 1 / y - 1 / z = (z - y) / y / z := by field_simp
    have h_nonneg : 0 ≤ (z - y) / y / z := by
      rw [← h_diff]
      linarith [one_div_le_one_div_of_le hy hyz]
    calc (1 / y - 1 / z) * ∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n
        ≤ (z - y) / y / z * (2 * (Real.log 4 + 4) * z) := by
          rw [h_diff]; exact mul_le_mul_of_nonneg_left hS h_nonneg
      _ = 2 * (Real.log 4 + 4) * ((z - y) / y) := by field_simp
      _ ≤ 11 * ((z - y) / y) := by
          gcongr
          linarith
  have h_eq : primeRemainder d q z - primeRemainder d q y =
      (∑ n ∈ Icc 1 ⌊z⌋₊, primeWeight d q n * (1 / n - 1 / z) -
        ∑ n ∈ Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / n - 1 / y)) -
        (Real.log z - Real.log y) / q.totient := by
    rw [primeRemainder, primeRemainder]
    ring
  rw [h_eq, abs_le]
  constructor <;> linarith [div_nonneg (sub_nonneg.2 hyz) hy.le,
    div_nonneg h_log₀ (by positivity : (0 : ℝ) ≤ q.totient)]

end TauCeti.ShortGRH
