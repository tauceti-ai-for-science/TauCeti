/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Sobolev.Trace.Estimate

/-!
# Fourier-mode estimates on a finite cylinder

A function on the finite cylinder `[a, b] × (ℝ ⧸ Tℤ)` is a path `t ↦ u t` of functions on the
circle. This file reads such a path in the Fourier-coefficient Sobolev spaces `H^s` of the circle:
`u t ∈ H^s`, with `t`-derivative `u' t ∈ H^(s - 1)`. The quantity

`∫ₐᵇ ‖u t‖²_{H^s} + ‖u' t‖²_{H^(s - 1)} dt`

is the squared norm of `L²(a, b; H^s) ∩ H¹(a, b; H^(s - 1))`; for `s = 1`, by Parseval's identity,
it is comparable to the squared `H¹` norm of the function on the cylinder. Both estimates below
hold one Fourier mode `n` at a time, uniformly in `n`, and are summed over the modes.

* **The trace theorem.** The boundary values `u a` and `u b` are bounded in `H^(s - 1/2)`:
  `‖u a‖² + ‖u b‖² ≤ ∫ₐᵇ (2 / (b - a) + 1) ‖u t‖² + ‖u' t‖²`. On the mode `n` this is the
  one-dimensional estimate `TauCeti.mul_norm_sq_add_norm_sq_le_integral` with weight `1 + |n|`:
  the high frequencies gain half a derivative.
* **The Cauchy–Riemann estimate.** In the coordinate `z = t + iθ` of the cylinder,
  `2 ∂/∂z̄ = ∂/∂t + i ∂/∂θ`, which acts on `u` as `u' + i ∂_θ u`, with `∂_θ = derivative T` the
  derivative on the circle. On the mode `n` it is `c' - (2πn/T) c`. Its energy identity
  (`TauCeti.integral_norm_sub_smul_sq`) controls the positive modes by their values at `b`, the
  negative modes by their values at `a`, and the constant mode by both
  (`TauCeti.integral_norm_sq_le_mul_norm_sq_add_mul_integral`). Summing,
  `∫ₐᵇ ‖u t‖² + ‖u' t‖²` is bounded by a constant, depending only on `T` and `b - a`, times
  `∫ₐᵇ ‖u' t + i ∂_θ (u t)‖² + ‖u a‖²_{H^(s - 1/2)} + ‖u b‖²_{H^(s - 1/2)}`.

These are the model estimates on a collar of a boundary circle: the boundary trace
`H^k → H^(k - 1/2)` and the elliptic estimate for `∂̄` with boundary values.

## Main statements

* `TauCeti.CircleSobolev.norm_inclusion_sq_add_norm_inclusion_sq_le_integral`: the trace theorem
  on the cylinder.
* `TauCeti.CircleSobolev.integral_norm_sq_add_norm_sq_le`: the Cauchy–Riemann estimate on the
  cylinder with boundary values in `H^(s - 1/2)`.

## References

* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications I*,
  Springer, 1972, Chapter 1, §3 (traces of `L²(a, b; X) ∩ H¹(a, b; Y)` in the intermediate
  space).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (the half-order boundary Sobolev spaces of the
  Cauchy–Riemann operator on cut Riemann surfaces).
-/

public section

open Complex MeasureTheory Set
open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {a b : ℝ}
  {u : ℝ → CircleSobolev s E} {u' : ℝ → CircleSobolev (s - 1) E}

/-! ### The Fourier modes of a path -/

private theorem continuousOn_coeff {r : ℝ} {v : ℝ → CircleSobolev r E}
    (hv : ContinuousOn v (Icc a b)) (n : ℤ) :
    ContinuousOn (fun t ↦ (v t).coeff n) (Icc a b) := by
  simpa only [Function.comp_def, coeffCLM_apply] using (coeffCLM n).continuous.comp_continuousOn hv

private theorem hasDerivAt_coeff {t : ℝ}
    (hd : HasDerivAt (fun t ↦ inclusion (sub_le_self s zero_le_one) (u t)) (u' t) t) (n : ℤ) :
    HasDerivAt (fun t ↦ (u t).coeff n) ((u' t).coeff n) t := by
  simpa [Function.comp_def, coeff_inclusion] using
    ((coeffCLM n : CircleSobolev (s - 1) E →L[ℂ] E).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      t hd

/-- The weights of the orders `s - 1/2` and `s` in terms of the weight of the order `s - 1`. -/
private theorem weight_two_mul_sub_half (n : ℤ) :
    weight (2 * (s - 1 / 2)) n = weight (2 * (s - 1)) n * weight 1 n := by
  rw [← weight_add]
  ring_nf

private theorem weight_two_mul (n : ℤ) :
    weight (2 * s) n = weight (2 * (s - 1)) n * weight 1 n ^ 2 := by
  rw [sq, ← mul_assoc, ← weight_add, ← weight_add]
  ring_nf

/-- On the `n`-th Fourier coefficient, the Cauchy–Riemann operator `u' + i ∂_θ u` is
`c' - (2πn/T) c`. -/
private theorem coeff_add_I_smul_derivative (T : ℝ) [Fact (0 < T)] (x : CircleSobolev s E)
    (y : CircleSobolev (s - 1) E) (n : ℤ) :
    (y + I • derivative T (sub_add_cancel s 1).le x).coeff n =
      y.coeff n - (2 * π * n / T : ℝ) • x.coeff n := by
  have h : I * (2 * π * I * n / T) = -((2 * π * n / T : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [coeff_add, coeff_smul, Pi.add_apply, Pi.smul_apply, coeff_derivative, smul_smul, h, neg_smul,
    Complex.coe_smul, ← sub_eq_add_neg]

/-! ### The trace theorem -/

/-- The trace estimate on the Fourier mode `n`. -/
private theorem weight_mul_norm_coeff_sq_add_le_integral (hab : a < b)
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hd : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ inclusion (sub_le_self s zero_le_one) (u t)) (u' t) t) (n : ℤ) :
    weight (2 * (s - 1 / 2)) n * ‖(u a).coeff n‖ ^ 2 +
        weight (2 * (s - 1 / 2)) n * ‖(u b).coeff n‖ ^ 2 ≤
      ∫ t in a..b, (2 / (b - a) + 1) * (weight (2 * s) n * ‖(u t).coeff n‖ ^ 2) +
        weight (2 * (s - 1)) n * ‖(u' t).coeff n‖ ^ 2 := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have hba : 0 < b - a := sub_pos.2 hab
  have hc := continuousOn_coeff hu n
  have hc' := continuousOn_coeff hu' n
  set ω := weight (2 * (s - 1)) n
  set w := weight 1 n
  have hω : 0 ≤ ω := weight_nonneg _ _
  have hw : 1 ≤ w := one_le_weight zero_le_one n
  have key := mul_norm_sq_add_norm_sq_le_integral hab (zero_le_one.trans hw) hc hc'
    fun t ht ↦ hasDerivAt_coeff (hd t ht) n
  rw [weight_two_mul_sub_half]
  calc ω * w * ‖(u a).coeff n‖ ^ 2 + ω * w * ‖(u b).coeff n‖ ^ 2
      = ω * (w * (‖(u a).coeff n‖ ^ 2 + ‖(u b).coeff n‖ ^ 2)) := by ring
    _ ≤ ω * ∫ t in a..b, (2 * w / (b - a) + w ^ 2) * ‖(u t).coeff n‖ ^ 2 +
          ‖(u' t).coeff n‖ ^ 2 := mul_le_mul_of_nonneg_left key hω
    _ = ∫ t in a..b, ω * ((2 * w / (b - a) + w ^ 2) * ‖(u t).coeff n‖ ^ 2 +
          ‖(u' t).coeff n‖ ^ 2) := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hab.le
        (ContinuousOn.intervalIntegrable_of_Icc hab.le (by fun_prop))
        (ContinuousOn.intervalIntegrable_of_Icc hab.le (by fun_prop)) fun t _ ↦ ?_
      rw [weight_two_mul]
      have hww : 2 * w / (b - a) ≤ 2 / (b - a) * w ^ 2 := by
        rw [show 2 * w / (b - a) = 2 / (b - a) * w by ring]
        exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have := mul_le_mul_of_nonneg_left hww (mul_nonneg hω (sq_nonneg ‖(u t).coeff n‖))
      nlinarith

/-- **The trace theorem on a finite cylinder.** Let `u` be a path in `H^s`, continuous on
`[a, b]`, whose image in `H^(s - 1)` is differentiable on `(a, b)` with derivative `u'`,
continuous on `[a, b]`. Then its values at both ends are bounded in `H^(s - 1/2)`:
`‖u a‖² + ‖u b‖² ≤ ∫ₐᵇ (2 / (b - a) + 1) ‖u t‖²_{H^s} + ‖u' t‖²_{H^(s - 1)}`. -/
theorem norm_inclusion_sq_add_norm_inclusion_sq_le_integral (hab : a < b)
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hd : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ inclusion (sub_le_self s zero_le_one) (u t)) (u' t) t) :
    ‖inclusion (sub_le_self s one_half_pos.le) (u a)‖ ^ 2 +
        ‖inclusion (sub_le_self s one_half_pos.le) (u b)‖ ^ 2 ≤
      ∫ t in a..b, (2 / (b - a) + 1) * ‖u t‖ ^ 2 + ‖u' t‖ ^ 2 := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hS := (hasSum_norm_sq (inclusion (sub_le_self s one_half_pos.le) (u a))).add
    (hasSum_norm_sq (inclusion (sub_le_self s one_half_pos.le) (u b)))
  simp only [coeff_inclusion] at hS
  refine hasSum_le_of_sum_le hS fun S ↦ ?_
  have hc (n : ℤ) : ContinuousOn (fun t ↦ (u t).coeff n) (Icc a b) := continuousOn_coeff hu n
  have hc' (n : ℤ) : ContinuousOn (fun t ↦ (u' t).coeff n) (Icc a b) := continuousOn_coeff hu' n
  calc _ ≤ ∑ n ∈ S, ∫ t in a..b, (2 / (b - a) + 1) * (weight (2 * s) n * ‖(u t).coeff n‖ ^ 2) +
          weight (2 * (s - 1)) n * ‖(u' t).coeff n‖ ^ 2 :=
        Finset.sum_le_sum fun n _ ↦ weight_mul_norm_coeff_sq_add_le_integral hab hu hu' hd n
    _ = ∫ t in a..b, ∑ n ∈ S, ((2 / (b - a) + 1) * (weight (2 * s) n * ‖(u t).coeff n‖ ^ 2) +
          weight (2 * (s - 1)) n * ‖(u' t).coeff n‖ ^ 2) :=
        (intervalIntegral.integral_finsetSum fun n _ ↦
          ContinuousOn.intervalIntegrable_of_Icc hab.le (by fun_prop)).symm
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hab.le
        (ContinuousOn.intervalIntegrable_of_Icc hab.le (by fun_prop))
        (ContinuousOn.intervalIntegrable_of_Icc hab.le (by fun_prop)) fun t _ ↦ ?_
      exact sum_le_hasSum S (fun n _ ↦ by
          have := weight_nonneg (2 * s) n
          have := weight_nonneg (2 * (s - 1)) n
          positivity)
        (((hasSum_norm_sq (u t)).mul_left (2 / (b - a) + 1)).add (hasSum_norm_sq (u' t)))

/-! ### The Cauchy–Riemann estimate -/

/-- The Cauchy–Riemann estimate on the Fourier mode `n`, after division by the weight of
`H^(s - 1)`: with `κ = 2π/T`, `ℓ = b - a` and `K = 1 + 2/κ² + 2ℓ²`, the mode `c` of frequency
`n` and weight `w = 1 + |n|` satisfies
`w² ∫ ‖c‖² + ∫ ‖c'‖² ≤ K ∫ ‖c' - κ n c‖² + (K κ + 2 ℓ) w (‖c a‖² + ‖c b‖²)`. -/
private theorem weight_sq_mul_integral_add_integral_le (T : ℝ) [hT : Fact (0 < T)] (hab : a ≤ b)
    {c c' : ℝ → E} (hc : ContinuousOn c (Icc a b)) (hc' : ContinuousOn c' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt c (c' t) t) (n : ℤ) :
    weight 1 n ^ 2 * (∫ t in a..b, ‖c t‖ ^ 2) + ∫ t in a..b, ‖c' t‖ ^ 2 ≤
      (1 + 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2) *
          (∫ t in a..b, ‖c' t - (2 * π * n / T : ℝ) • c t‖ ^ 2) +
        ((1 + 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2) * (2 * π / T) + 2 * (b - a)) *
          (weight 1 n * (‖c a‖ ^ 2 + ‖c b‖ ^ 2)) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have hT0 := hT.out
  set r : ℝ := 2 * π * n / T
  set K := 1 + 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2
  set w := weight 1 n with hw_def
  set X := ∫ t in a..b, ‖c' t‖ ^ 2
  set Z := ∫ t in a..b, ‖c t‖ ^ 2
  set B := ‖c a‖ ^ 2 + ‖c b‖ ^ 2
  have hX : 0 ≤ X := intervalIntegral.integral_nonneg hab fun t _ ↦ sq_nonneg _
  have hZ : 0 ≤ Z := intervalIntegral.integral_nonneg hab fun t _ ↦ sq_nonneg _
  have hB : 0 ≤ B := by positivity
  have hw : 1 ≤ w := one_le_weight zero_le_one n
  have hK : 1 ≤ K := by
    have : 0 ≤ 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2 := by positivity
    linarith
  -- The energy identity: `X + r² Z = G + r (‖c b‖² - ‖c a‖²) ≤ G + |r| B`.
  have hE := integral_norm_sub_smul_sq hab r hc hc' hd
  rw [intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop))
    (ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)),
    intervalIntegral.integral_const_mul] at hE
  have hrB : r * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) ≤ 2 * π / T * w * B := by
    have h1 : |r| ≤ 2 * π / T * w := by
      rw [show r = 2 * π / T * n by simp only [r]; ring, abs_mul,
        abs_of_pos (by positivity : 0 < 2 * π / T), hw_def, weight_def, Real.rpow_one]
      gcongr
      linarith
    have h2 : |‖c b‖ ^ 2 - ‖c a‖ ^ 2| ≤ B := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖c a‖, sq_nonneg ‖c b‖]
    calc r * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) ≤ |r| * |‖c b‖ ^ 2 - ‖c a‖ ^ 2| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ 2 * π / T * w * B := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  -- The Poincaré inequality with boundary values: `Z ≤ ℓ B + ℓ² X`.
  have hP := integral_norm_sq_le_mul_norm_sq_add_mul_integral hab hc hc' hd
  -- The weight: `w² ≤ 2 + 2 n² = 2 + 2 (T / 2π)² r²`.
  have hw2 : w ^ 2 ≤ 2 + 2 * (T / (2 * π)) ^ 2 * r ^ 2 := by
    have hr : (T / (2 * π)) ^ 2 * r ^ 2 = (n : ℝ) ^ 2 := by
      simp only [r]; field_simp
    rw [mul_assoc, hr, hw_def, weight_def, Real.rpow_one]
    nlinarith [sq_abs (n : ℝ), sq_nonneg (|(n : ℝ)| - 1)]
  have hr2 : 0 ≤ r ^ 2 * Z := mul_nonneg (sq_nonneg r) hZ
  have hwZ : w ^ 2 * Z ≤ 2 * Z + 2 * (T / (2 * π)) ^ 2 * (r ^ 2 * Z) := by nlinarith
  have hKpos : 0 ≤ 2 * (T / (2 * π)) ^ 2 := by positivity
  have hℓ : 0 ≤ b - a := sub_nonneg.2 hab
  -- Combine: `w² Z + X ≤ 2 ℓ B + K (X + r² Z) ≤ 2 ℓ B + K (G + κ w B)`.
  have hXr : X + r ^ 2 * Z ≤ (∫ t in a..b, ‖c' t - r • c t‖ ^ 2) + 2 * π / T * w * B := by
    linarith
  have hBw : B ≤ w * B := le_mul_of_one_le_left hB hw
  nlinarith [mul_le_mul_of_nonneg_left hXr (zero_le_one.trans hK),
    mul_nonneg (sq_nonneg (b - a)) hX, mul_nonneg hKpos hr2,
    mul_le_mul_of_nonneg_left hBw hℓ]

/-- The Cauchy–Riemann estimate on the Fourier mode `n` of a path, with the weights of the
Sobolev norms. -/
private theorem integral_weight_mul_norm_coeff_sq_add_le (T : ℝ) [hT : Fact (0 < T)]
    (hab : a ≤ b) (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hd : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ inclusion (sub_le_self s zero_le_one) (u t)) (u' t) t) (n : ℤ) :
    ∫ t in a..b, weight (2 * s) n * ‖(u t).coeff n‖ ^ 2 +
        weight (2 * (s - 1)) n * ‖(u' t).coeff n‖ ^ 2 ≤
      ((1 + 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2) * (1 + 2 * π / T) + 2 * (b - a)) *
        ((∫ t in a..b, weight (2 * (s - 1)) n *
            ‖(u' t + I • derivative T (sub_add_cancel s 1).le (u t)).coeff n‖ ^ 2) +
          (weight (2 * (s - 1 / 2)) n * ‖(u a).coeff n‖ ^ 2 +
            weight (2 * (s - 1 / 2)) n * ‖(u b).coeff n‖ ^ 2)) := by
  have hT0 := hT.out
  set K := 1 + 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2
  have hℓ : 0 ≤ b - a := sub_nonneg.2 hab
  have hK : 0 ≤ K := by positivity
  have hKC : K ≤ K * (1 + 2 * π / T) + 2 * (b - a) := by
    have : 0 ≤ K * (2 * π / T) := by positivity
    nlinarith
  have hKC' : K * (2 * π / T) + 2 * (b - a) ≤ K * (1 + 2 * π / T) + 2 * (b - a) := by nlinarith
  have hc := continuousOn_coeff hu n
  have hc' := continuousOn_coeff hu' n
  have hm := weight_sq_mul_integral_add_integral_le T hab hc hc'
    (fun t ht ↦ hasDerivAt_coeff (hd t ht) n) n
  set ω := weight (2 * (s - 1)) n
  set w := weight 1 n
  have hω : 0 ≤ ω := weight_nonneg _ _
  have hw : 0 ≤ w := weight_nonneg _ _
  set G := ∫ t in a..b, ‖(u' t).coeff n - (2 * π * n / T : ℝ) • (u t).coeff n‖ ^ 2
  have hG : 0 ≤ G := intervalIntegral.integral_nonneg hab fun t _ ↦ sq_nonneg _
  have hB : 0 ≤ w * (‖(u a).coeff n‖ ^ 2 + ‖(u b).coeff n‖ ^ 2) := by positivity
  rw [weight_two_mul (s := s) n, weight_two_mul_sub_half,
    intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop))
      (ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [coeff_add_I_smul_derivative]
  rw [intervalIntegral.integral_const_mul]
  calc ω * w ^ 2 * (∫ t in a..b, ‖(u t).coeff n‖ ^ 2) + ω * ∫ t in a..b, ‖(u' t).coeff n‖ ^ 2
      = ω * (w ^ 2 * (∫ t in a..b, ‖(u t).coeff n‖ ^ 2) + ∫ t in a..b, ‖(u' t).coeff n‖ ^ 2) := by
        ring
    _ ≤ ω * (K * G + (K * (2 * π / T) + 2 * (b - a)) *
          (w * (‖(u a).coeff n‖ ^ 2 + ‖(u b).coeff n‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hm hω
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hKC hG, mul_le_mul_of_nonneg_right hKC' hB]

/-- **The Cauchy–Riemann estimate on a finite cylinder.** Let `u` be a path in `H^s`, continuous
on `[a, b]`, whose image in `H^(s - 1)` is differentiable on `(a, b)` with derivative `u'`,
continuous on `[a, b]`. Then `∫ₐᵇ ‖u t‖²_{H^s} + ‖u' t‖²_{H^(s - 1)}` is at most
`C (∫ₐᵇ ‖u' t + i ∂_θ (u t)‖²_{H^(s - 1)} + ‖u a‖²_{H^(s - 1/2)} + ‖u b‖²_{H^(s - 1/2)})`, where
`u' + i ∂_θ u` is twice the Cauchy–Riemann operator `∂/∂z̄` of the cylinder in the coordinate
`z = t + iθ`, `θ ∈ ℝ ⧸ Tℤ`, and the constant
`C = (1 + 2 (T / 2π)² + 2 (b - a)²) (1 + 2π / T) + 2 (b - a)` depends neither on `s` nor on `E`. -/
theorem integral_norm_sq_add_norm_sq_le (T : ℝ) [hT : Fact (0 < T)] (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hd : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t ↦ inclusion (sub_le_self s zero_le_one) (u t)) (u' t) t) :
    ∫ t in a..b, ‖u t‖ ^ 2 + ‖u' t‖ ^ 2 ≤
      ((1 + 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2) * (1 + 2 * π / T) + 2 * (b - a)) *
        ((∫ t in a..b, ‖u' t + I • derivative T (sub_add_cancel s 1).le (u t)‖ ^ 2) +
          ‖inclusion (sub_le_self s one_half_pos.le) (u a)‖ ^ 2 +
          ‖inclusion (sub_le_self s one_half_pos.le) (u b)‖ ^ 2) := by
  set g : ℝ → CircleSobolev (s - 1) E :=
    fun t ↦ u' t + I • derivative T (sub_add_cancel s 1).le (u t)
  set C := (1 + 2 * (T / (2 * π)) ^ 2 + 2 * (b - a) ^ 2) * (1 + 2 * π / T) + 2 * (b - a)
  have hg : ContinuousOn g (Icc a b) :=
    hu'.add (((derivative T _).continuous.comp_continuousOn hu).const_smul I)
  have hc (n : ℤ) : ContinuousOn (fun t ↦ (u t).coeff n) (Icc a b) := continuousOn_coeff hu n
  have hc' (n : ℤ) : ContinuousOn (fun t ↦ (u' t).coeff n) (Icc a b) := continuousOn_coeff hu' n
  have hcg (n : ℤ) : ContinuousOn (fun t ↦ (g t).coeff n) (Icc a b) := continuousOn_coeff hg n
  -- The energy of the mode `n`, and the boundary quantities bounding it.
  set f : ℤ → ℝ → ℝ := fun n t ↦
    weight (2 * s) n * ‖(u t).coeff n‖ ^ 2 + weight (2 * (s - 1)) n * ‖(u' t).coeff n‖ ^ 2
  set β : ℤ → ℝ := fun n ↦
    weight (2 * (s - 1 / 2)) n * ‖(u a).coeff n‖ ^ 2 +
      weight (2 * (s - 1 / 2)) n * ‖(u b).coeff n‖ ^ 2
  have hβ : HasSum β (‖inclusion (sub_le_self s one_half_pos.le) (u a)‖ ^ 2 +
      ‖inclusion (sub_le_self s one_half_pos.le) (u b)‖ ^ 2) := by
    have := (hasSum_norm_sq (inclusion (sub_le_self s one_half_pos.le) (u a))).add
      (hasSum_norm_sq (inclusion (sub_le_self s one_half_pos.le) (u b)))
    simpa only [coeff_inclusion] using this
  have hf0 (n : ℤ) (t : ℝ) : 0 ≤ f n t := by
    have := weight_nonneg (2 * s) n
    have := weight_nonneg (2 * (s - 1)) n
    positivity
  have hfi (n : ℤ) : IntervalIntegrable (f n) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)
  -- Summing the modes: every finite partial sum is bounded by `C` times the right side.
  have hR (S : Finset ℤ) : ∑ n ∈ S, ∫ t in a..b, f n t ≤
      C * ((∫ t in a..b, ‖g t‖ ^ 2) + (‖inclusion (sub_le_self s one_half_pos.le) (u a)‖ ^ 2 +
        ‖inclusion (sub_le_self s one_half_pos.le) (u b)‖ ^ 2)) := by
    have hgS : ∑ n ∈ S, ∫ t in a..b, weight (2 * (s - 1)) n * ‖(g t).coeff n‖ ^ 2 ≤
        ∫ t in a..b, ‖g t‖ ^ 2 := by
      rw [← intervalIntegral.integral_finsetSum fun n _ ↦
        ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)]
      refine intervalIntegral.integral_mono_on hab
        (ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop))
        (ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)) fun t _ ↦ ?_
      exact sum_le_hasSum S (fun n _ ↦ mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
        (hasSum_norm_sq (g t))
    have hβS : ∑ n ∈ S, β n ≤ ‖inclusion (sub_le_self s one_half_pos.le) (u a)‖ ^ 2 +
        ‖inclusion (sub_le_self s one_half_pos.le) (u b)‖ ^ 2 :=
      sum_le_hasSum S (fun n _ ↦ by
        have := weight_nonneg (2 * (s - 1 / 2)) n
        positivity) hβ
    calc ∑ n ∈ S, ∫ t in a..b, f n t
        ≤ ∑ n ∈ S, C * ((∫ t in a..b, weight (2 * (s - 1)) n * ‖(g t).coeff n‖ ^ 2) + β n) :=
          Finset.sum_le_sum fun n _ ↦
            integral_weight_mul_norm_coeff_sq_add_le T hab hu hu' hd n
      _ = C * ((∑ n ∈ S, ∫ t in a..b, weight (2 * (s - 1)) n * ‖(g t).coeff n‖ ^ 2) +
            ∑ n ∈ S, β n) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ _ := by
        have : 0 ≤ C := by
          have := hT.out
          have := sub_nonneg.2 hab
          positivity
        gcongr
  -- Exchange the sum over the modes with the integral.
  have hsum := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioc a b))
    (F := f) (fun n ↦ (hfi n).1) (by
      simp_rw [Real.norm_of_nonneg (hf0 _ _), ← intervalIntegral.integral_of_le hab]
      exact summable_of_sum_le (fun n ↦ intervalIntegral.integral_nonneg hab fun t _ ↦ hf0 n t)
        hR)
  have htsum (t : ℝ) : ∑' n, f n t = ‖u t‖ ^ 2 + ‖u' t‖ ^ 2 :=
    ((hasSum_norm_sq (u t)).add (hasSum_norm_sq (u' t))).tsum_eq
  simp_rw [htsum, ← intervalIntegral.integral_of_le hab] at hsum
  rw [add_assoc]
  exact hasSum_le_of_sum_le hsum hR

end CircleSobolev

end TauCeti
