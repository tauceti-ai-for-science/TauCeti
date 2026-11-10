/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalities

/-!
# One-dimensional energy estimates for traces

A `C¹` function with values in a real inner product space has both endpoint norms controlled
by its value and derivative energies on a finite interval, with an explicit width-dependent
constant. No compact support is needed for this finite-interval estimate. With a weight `w ≥ 0`,
`w (‖g a‖² + ‖g b‖²) ≤ ∫ₐᵇ (2 w / (b - a) + w²) ‖g‖² + ‖g'‖²`
(`TauCeti.mul_norm_sq_add_norm_sq_le_integral`); applied to the Fourier mode of frequency `n` of
a function on a collar `[a, b] × S¹`, with `w = 1 + |n|`, this is the half-order trace estimate.
On the same interval, the value energy is controlled by the endpoint values and the derivative
energy (`TauCeti.integral_norm_sq_le_mul_norm_sq_add_mul_integral`), and the operator
`d/dt - r` satisfies the energy identity
`∫ₐᵇ ‖g' - r g‖² = ∫ₐᵇ (‖g'‖² + r² ‖g‖²) - r (‖g b‖² - ‖g a‖²)`
(`TauCeti.integral_norm_sub_smul_sq`), the identity behind elliptic estimates for the
Cauchy–Riemann operator on a cylinder, read frequency by frequency.

For `1 ≤ r`, a compactly supported `C¹` real function has the `r`-th power of its value at the
endpoint of a half-line bounded by the integral of `(r - 1) |g|ʳ + |g'|ʳ` on that half-line
(`TauCeti.abs_rpow_le_integral_Ioi`); for `r = 2` this is the `H¹` energy. Integrating this
estimate over the transverse variables supplies the flat-boundary `W^{1,p}` trace inequality.
The energy density `(r - 1) |u|ʳ + ‖Du‖ʳ` of a compactly supported `C¹` function on any normed
space is continuous with compact support (`TauCeti.continuous_rpow_energy`,
`TauCeti.hasCompactSupport_rpow_energy`), and `TauCeti.le_rpow_inv_mul_of_rpow_le` turns an
inequality `xʳ ≤ (r - 1) yʳ + zʳ` into the linear bound `x ≤ r ^ (1 / r) n` for `y, z ≤ n`.

The estimate follows the fundamental-theorem-of-calculus proof of the trace theorem in
L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

namespace TauCeti

open MeasureTheory Set

section Interval

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {g g' : ℝ → F} {a b : ℝ}

/-- The fundamental theorem of calculus for `‖g‖²` against the affine weight `κ t + β`. -/
private theorem integral_affine_mul_inner (hab : a ≤ b) (κ β : ℝ)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) :
    ∫ t in a..b, κ * ‖g t‖ ^ 2 + (κ * t + β) * (2 * inner ℝ (g t) (g' t)) =
      (κ * b + β) * ‖g b‖ ^ 2 - (κ * a + β) * ‖g a‖ ^ 2 := by
  have hw : ContinuousOn (fun t ↦ κ * t + β) (Icc a b) := by fun_prop
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t ↦ (κ * t + β) * ‖g t‖ ^ 2) hab (hw.mul (hg.norm.pow 2)) (fun t ht ↦ ?_)
    (ContinuousOn.intervalIntegrable_of_Icc hab
      ((continuousOn_const.mul (hg.norm.pow 2)).add (hw.mul (continuousOn_const.mul
        (hg.inner hg')))))
  simpa only [mul_one] using
    (((hasDerivAt_id' t).const_mul κ).add_const β).fun_mul (hd t ht).norm_sq

/-- **The weighted endpoint estimate.** For every weight `w ≥ 0`, both endpoint norms of a curve
`g`, `C¹` on `[a, b]`, satisfy
`w (‖g a‖² + ‖g b‖²) ≤ ∫ₐᵇ (2 w / (b - a) + w²) ‖g‖² + ‖g'‖²`.
For large `w` the derivative energy keeps its coefficient `1`: this is the gain of half a
derivative in the trace of a Sobolev function on a collar, read frequency by frequency. -/
theorem mul_norm_sq_add_norm_sq_le_integral (hab : a < b) {w : ℝ} (hw : 0 ≤ w)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) :
    w * (‖g a‖ ^ 2 + ‖g b‖ ^ 2) ≤
      ∫ t in a..b, (2 * w / (b - a) + w ^ 2) * ‖g t‖ ^ 2 + ‖g' t‖ ^ 2 := by
  have hba : 0 < b - a := sub_pos.2 hab
  -- The affine weight `q t = (2 t - a - b) / (b - a)` is `-1` at `a` and `1` at `b`.
  have hid := integral_affine_mul_inner hab.le (2 / (b - a)) (-(a + b) / (b - a)) hg hg' hd
  have hqa : 2 / (b - a) * a + -(a + b) / (b - a) = -1 := by field_simp; ring
  have hqb : 2 / (b - a) * b + -(a + b) / (b - a) = 1 := by field_simp; ring
  rw [hqa, hqb] at hid
  have hint : IntervalIntegrable (fun t ↦ 2 / (b - a) * ‖g t‖ ^ 2 +
      (2 / (b - a) * t + -(a + b) / (b - a)) * (2 * inner ℝ (g t) (g' t))) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le (by fun_prop)
  -- On `[a, b]` the weight has absolute value at most one; then use Young's inequality.
  have hle : ∫ t in a..b, w * (2 / (b - a) * ‖g t‖ ^ 2 +
      (2 / (b - a) * t + -(a + b) / (b - a)) * (2 * inner ℝ (g t) (g' t))) ≤
      ∫ t in a..b, (2 * w / (b - a) + w ^ 2) * ‖g t‖ ^ 2 + ‖g' t‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hab.le (hint.const_mul w)
      (ContinuousOn.intervalIntegrable_of_Icc hab.le
        ((continuousOn_const.mul (hg.norm.pow 2)).add (hg'.norm.pow 2))) fun t ht ↦ ?_
    set q := 2 / (b - a) * t + -(a + b) / (b - a) with hq_def
    have hq : |q| ≤ 1 := by
      rw [abs_le]
      constructor
      · rw [← hqa, hq_def]; gcongr; exact ht.1
      · rw [← hqb, hq_def]; gcongr; exact ht.2
    have hi : |q * inner ℝ (g t) (g' t)| ≤ ‖g t‖ * ‖g' t‖ := by
      rw [abs_mul]
      exact (mul_le_mul hq (abs_real_inner_le_norm _ _) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    have h1 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hi) hw
    have h2 : 2 * w * (‖g t‖ * ‖g' t‖) ≤ w ^ 2 * ‖g t‖ ^ 2 + ‖g' t‖ ^ 2 := by
      nlinarith [sq_nonneg (w * ‖g t‖ - ‖g' t‖)]
    have e : 2 * w / (b - a) = w * (2 / (b - a)) := by ring
    rw [e]
    nlinarith [h1, h2]
  rw [intervalIntegral.integral_const_mul, hid] at hle
  linarith

/-- Both endpoint norms of a curve that is `C¹` near a closed interval are controlled by
its energy on that interval.
The coefficient of the value energy depends on the interval width; no compact support or
integrability outside the interval is required. -/
theorem norm_sq_add_norm_sq_le_integral_norm_sq_add_norm_deriv_sq
    (hg : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 g t) (hab : a < b) :
    ‖g a‖ ^ 2 + ‖g b‖ ^ 2 ≤
      ∫ t in a..b, (2 / (b - a) + 1) * ‖g t‖ ^ 2 + ‖deriv g t‖ ^ 2 := by
  simpa only [one_mul, mul_one, one_pow] using mul_norm_sq_add_norm_sq_le_integral hab zero_le_one
    (fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ ((hg t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
    fun t ht ↦ ((hg t (Ioo_subset_Icc_self ht)).differentiableAt one_ne_zero).hasDerivAt

/-- **A Poincaré inequality with boundary values.** A curve `g`, `C¹` on `[a, b]`, has its
value energy controlled by its endpoint norms and its derivative energy:
`∫ₐᵇ ‖g‖² ≤ (b - a) (‖g a‖² + ‖g b‖²) + (b - a)² ∫ₐᵇ ‖g'‖²`. -/
theorem integral_norm_sq_le_mul_norm_sq_add_mul_integral (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) :
    ∫ t in a..b, ‖g t‖ ^ 2 ≤
      (b - a) * (‖g a‖ ^ 2 + ‖g b‖ ^ 2) + (b - a) ^ 2 * ∫ t in a..b, ‖g' t‖ ^ 2 := by
  -- The affine weight `q t = t - (a + b) / 2` has absolute value at most `(b - a) / 2`.
  have hid := integral_affine_mul_inner hab 1 (-(a + b) / 2) hg hg' hd
  have hv : IntervalIntegrable (fun t ↦ ‖g t‖ ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)
  have hv' : IntervalIntegrable (fun t ↦ ‖g' t‖ ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)
  have hw : IntervalIntegrable (fun t ↦ (1 * t + -(a + b) / 2) * (2 * inner ℝ (g t) (g' t)))
      volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (by fun_prop)
  rw [intervalIntegral.integral_add (by simpa only [one_mul] using hv) hw] at hid
  have hle : ∫ t in a..b, -((1 * t + -(a + b) / 2) * (2 * inner ℝ (g t) (g' t))) ≤
      ∫ t in a..b, 2⁻¹ * ‖g t‖ ^ 2 + 2⁻¹ * (b - a) ^ 2 * ‖g' t‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hab hw.neg
      ((hv.const_mul _).add (hv'.const_mul _)) fun t ht ↦ ?_
    set q := 1 * t + -(a + b) / 2 with hq_def
    have hq : q ^ 2 ≤ (b - a) ^ 2 / 4 := by
      have : |q| ≤ (b - a) / 2 := by
        rw [abs_le, hq_def]; constructor <;> linarith [ht.1, ht.2]
      nlinarith [abs_nonneg q, sq_abs q]
    have hi : |q * inner ℝ (g t) (g' t)| ≤ |q| * (‖g t‖ * ‖g' t‖) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg q)
    have := neg_abs_le (q * inner ℝ (g t) (g' t))
    nlinarith [sq_nonneg (‖g t‖ - 2 * |q| * ‖g' t‖), sq_abs q, abs_nonneg q,
      mul_nonneg (abs_nonneg q) (mul_nonneg (norm_nonneg (g t)) (norm_nonneg (g' t))),
      sq_nonneg (‖g' t‖)]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_add (hv.const_mul _)
    (hv'.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hle
  simp only [one_mul] at hid hle
  rw [show b + -(a + b) / 2 = (b - a) / 2 by ring, show a + -(a + b) / 2 = -((b - a) / 2) by ring]
    at hid
  linarith

/-- **The energy identity of `d/dt - r`.** For a curve `g`, `C¹` on `[a, b]`, and a real `r`,
`∫ₐᵇ ‖g' - r g‖² = ∫ₐᵇ (‖g'‖² + r² ‖g‖²) - r (‖g b‖² - ‖g a‖²)`.
So `‖g' - r g‖` controls both energies up to the endpoint value at `b` when `r > 0`, and at `a`
when `r < 0`. -/
theorem integral_norm_sub_smul_sq (hab : a ≤ b) (r : ℝ)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) :
    ∫ t in a..b, ‖g' t - r • g t‖ ^ 2 =
      (∫ t in a..b, ‖g' t‖ ^ 2 + r ^ 2 * ‖g t‖ ^ 2) - r * (‖g b‖ ^ 2 - ‖g a‖ ^ 2) := by
  have hid := integral_affine_mul_inner hab 0 1 hg hg' hd
  simp only [zero_mul, zero_add, one_mul] at hid
  have hpt (t : ℝ) : ‖g' t - r • g t‖ ^ 2 =
      (‖g' t‖ ^ 2 + r ^ 2 * ‖g t‖ ^ 2) - r * (2 * inner ℝ (g t) (g' t)) := by
    rw [norm_sub_sq_real, norm_smul, inner_smul_right, real_inner_comm, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, hid]
  · exact ContinuousOn.intervalIntegrable_of_Icc hab
      ((hg'.norm.pow 2).add (continuousOn_const.mul (hg.norm.pow 2)))
  · exact (ContinuousOn.intervalIntegrable_of_Icc hab
      (continuousOn_const.mul (hg.inner hg'))).const_mul r

end Interval

section Energy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For `1 ≤ r`, the `Lʳ` energy density `(r - 1) |u|ʳ + ‖Du‖ʳ` of a `C¹` function is
continuous. -/
theorem continuous_rpow_energy {u : F → ℝ} (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r) :
    Continuous fun x ↦ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r :=
  (continuous_const.mul (hu.continuous.abs.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))).add
    ((hu.continuous_fderiv one_ne_zero).norm.rpow_const fun _ ↦ Or.inr (zero_le_one.trans hr))

/-- For `1 ≤ r`, the `Lʳ` energy density `(r - 1) |u|ʳ + ‖Du‖ʳ` of a compactly supported
function has compact support. -/
theorem hasCompactSupport_rpow_energy {u : F → ℝ} (hsupp : HasCompactSupport u) {r : ℝ}
    (hr : 1 ≤ r) : HasCompactSupport fun x ↦ (r - 1) * |u x| ^ r + ‖fderiv ℝ u x‖ ^ r := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  exact (hsupp.mono fun x hx hz ↦ hx (by simp [hz, hr0])).add
    ((hsupp.fderiv ℝ).mono fun x hx hz ↦ hx (by
      simp only [hz, norm_zero (E := F →L[ℝ] ℝ), Real.zero_rpow hr0]))

end Energy

private theorem integrable_rpow_energy {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) {r : ℝ} (hr : 1 ≤ r) :
    Integrable (fun t ↦ (r - 1) * |g t| ^ r + |deriv g t| ^ r) volume := by
  simpa only [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] using
    (continuous_rpow_energy hg hr).integrable_of_hasCompactSupport
      (hasCompactSupport_rpow_energy hs hr)

/-- If `x ^ r ≤ (r - 1) y ^ r + z ^ r` for `1 ≤ r` and nonnegative `x`, `y`, `z`, with `y` and `z`
at most `n`, then `x ≤ r ^ (1 / r) n`. This turns the `Lʳ` trace inequality into a bound with
constant `r ^ (1 / r)` by the Sobolev norm. -/
theorem le_rpow_inv_mul_of_rpow_le {r x y z n : ℝ} (hr : 1 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hyn : y ≤ n) (hzn : z ≤ n) (h : x ^ r ≤ (r - 1) * y ^ r + z ^ r) :
    x ≤ r ^ r⁻¹ * n := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hn : 0 ≤ n := hy.trans hyn
  have h1 : y ^ r ≤ n ^ r := Real.rpow_le_rpow hy hyn hr0.le
  have h2 : z ^ r ≤ n ^ r := Real.rpow_le_rpow hz hzn hr0.le
  rw [← Real.rpow_le_rpow_iff hx (by positivity) hr0, Real.mul_rpow (by positivity) hn,
    ← Real.rpow_mul hr0.le, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  nlinarith [sub_nonneg.2 hr]

/-- **The one-dimensional `Lᵖ` trace estimate.** For `1 ≤ r`, the `r`-th power of the value at
the endpoint of a half-line of a compactly supported `C¹` function is controlled by
`(r - 1) |g|ʳ + |g'|ʳ` on that half-line. For `r = 2` the right side is the `H¹` energy. -/
theorem abs_rpow_le_integral_Ioi {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    |g a| ^ r ≤ ∫ t in Ioi a, (r - 1) * |g t| ^ r + |deriv g t| ^ r := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hint := integrable_rpow_energy hg hs hr
  rcases hr.eq_or_lt with rfl | hr1
  · -- For `r = 1`, the fundamental theorem of calculus on `[a, ∞)`.
    have hi := hs.integral_Ioi_deriv_eq hg a
    simp only [Real.rpow_one, sub_self, zero_mul, zero_add] at hint ⊢
    calc |g a| = |∫ t in Ioi a, deriv g t| := by rw [hi, abs_neg]
      _ ≤ ∫ t in Ioi a, |deriv g t| := abs_integral_le_integral_abs
  · -- For `r > 1`, the same argument for the `C¹` function `|g|ʳ`, whose derivative
    -- `r |g|ʳ⁻¹ g'` is bounded by Young's inequality.
    have hv : ContDiff ℝ 1 (fun t ↦ ‖g t‖ ^ r) := hg.norm_rpow hr1
    have hvs : HasCompactSupport (fun t ↦ ‖g t‖ ^ r) :=
      hs.mono fun t ht hzero ↦ ht (by simp [hzero, hr0])
    have hi := hvs.integral_Ioi_deriv_eq hv a
    have hdv : Integrable (fun t ↦ deriv (fun t ↦ ‖g t‖ ^ r) t) volume :=
      (hv.continuous_deriv le_rfl).integrable_of_hasCompactSupport hvs.deriv
    have hyoung : ∀ t, |deriv (fun t ↦ ‖g t‖ ^ r) t| ≤ (r - 1) * |g t| ^ r + |deriv g t| ^ r := by
      intro t
      have hd := norm_fderiv_norm_rpow_le (hg.differentiable one_ne_zero) (x := t) hr1
      rw [← norm_deriv_eq_norm_fderiv, ← norm_deriv_eq_norm_fderiv] at hd
      simp only [Real.norm_eq_abs] at hd
      refine hd.trans ?_
      -- Weighted AM-GM with weights `(r - 1) / r` and `1 / r`.
      have hw := Real.geom_mean_le_arith_mean2_weighted
        (div_nonneg (sub_nonneg.2 hr) (zero_le_one.trans hr))
        (one_div_nonneg.2 (zero_le_one.trans hr))
        (Real.rpow_nonneg (abs_nonneg (g t)) r) (Real.rpow_nonneg (abs_nonneg (deriv g t)) r)
        (by field_simp; ring)
      rw [← Real.rpow_mul (abs_nonneg _), ← Real.rpow_mul (abs_nonneg _),
        show r * ((r - 1) / r) = r - 1 by field_simp, show r * (1 / r) = 1 by field_simp,
        Real.rpow_one] at hw
      have hr' : 0 < r := zero_lt_one.trans hr1
      calc r * |g t| ^ (r - 1) * |deriv g t| = r * (|g t| ^ (r - 1) * |deriv g t|) := by ring
        _ ≤ r * ((r - 1) / r * |g t| ^ r + 1 / r * |deriv g t| ^ r) := by gcongr
        _ = (r - 1) * |g t| ^ r + |deriv g t| ^ r := by field_simp
    calc |g a| ^ r = ∫ t in Ioi a, -deriv (fun t ↦ ‖g t‖ ^ r) t := by
          rw [integral_neg, hi, neg_neg, Real.norm_eq_abs]
      _ ≤ ∫ t in Ioi a, (r - 1) * |g t| ^ r + |deriv g t| ^ r :=
          integral_mono hdv.neg.integrableOn hint.integrableOn fun t ↦
            (neg_le_abs _).trans (hyoung t)

/-- For `1 ≤ r`, the `r`-th power of a point value of a compactly supported `C¹` function is
controlled by `(r - 1) |g|ʳ + |g'|ʳ` on the whole line. -/
theorem abs_rpow_le_integral {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (a : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    |g a| ^ r ≤ ∫ t, (r - 1) * |g t| ^ r + |deriv g t| ^ r := by
  refine (abs_rpow_le_integral_Ioi hg hs a hr).trans
    (setIntegral_le_integral (integrable_rpow_energy hg hs hr)
      (Filter.Eventually.of_forall fun t ↦ ?_))
  have := Real.rpow_nonneg (abs_nonneg (g t)) r
  have := Real.rpow_nonneg (abs_nonneg (deriv g t)) r
  have := sub_nonneg.2 hr
  positivity

end TauCeti
