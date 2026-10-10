/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.WeakType

/-!
# Standard Calderón–Zygmund kernels satisfy Hörmander's condition

The Calderón–Zygmund theorem (`ContinuousLinearMap.mul_volume_lt_enorm_le_of_hormander`) asks of
the kernel `K` of a singular integral operator only **Hörmander's condition**

`∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`.

The kernels met in practice (the Hilbert and Riesz transforms, the second derivatives of the
Newtonian kernel) are instead known to satisfy the pointwise **standard smoothness estimate**

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ / dist x y' ^ (n + δ)` whenever `dist x y' > 2 dist y y'`,

for some `δ > 0`. This file shows that the pointwise estimate implies Hörmander's condition with
`B = C A 2ⁿ / (2^δ - 1)`, in any metric measure space whose balls satisfy the growth bound
`μ (closedBall y r) ≤ A rⁿ` (`TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow`). The
exponent `n` need not be an integer. On `ℝⁿ = ι → ℝ` with Lebesgue measure, where closed balls
are cubes of volume `(2r)ⁿ`, this gives `B = 4ⁿ C / (2^δ - 1)`
(`TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi`), and so the Calderón–Zygmund
theorem for operators with a standard kernel: they are of weak type `(1, 1)` as soon as they are
bounded on `L²` (`ContinuousLinearMap.mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`). The same
bound is the hypothesis of the strong type `(p, p)` theorem for `1 < p < 2`
(`ContinuousLinearMap.eLpNorm_le_of_hormander`).

The proof splits the region `dist x y' > R` into the dyadic annuli
`2ᵏ R ≤ dist x y' < 2ᵏ⁺¹ R`. On the `k`-th annulus `dist x y' ^ (-s)` is at most `(2ᵏ R) ^ (-s)`,
and the annulus lies in a ball of measure at most `A (2ᵏ⁺¹ R)ⁿ`, so for `s > n` the annuli
contribute a convergent geometric series, `∫_{dist x y' > R} dist x y' ^ (-s) dx ≤
A 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))` (`TauCeti.setLIntegral_ofReal_dist_rpow_neg_le`). Taking
`R = 2 dist y y'` and `s = n + δ` gives Hörmander's condition, with a bound independent of `y`
and `y'`.

## Main declarations

* `TauCeti.setLIntegral_ofReal_dist_rpow_neg_le`: the tail bound for `dist x y ^ (-s)` under the
  growth bound `μ (closedBall y r) ≤ A rⁿ`, `n < s`.
* `TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow`: the standard smoothness estimate
  implies Hörmander's condition.
* `TauCeti.setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi`: the same on `ℝⁿ`.
* `ContinuousLinearMap.mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow`: an operator bounded on
  `L²(ℝⁿ)` with a kernel satisfying the standard smoothness estimate is of weak type `(1, 1)`.

## References

* E. Stein, *Harmonic Analysis*, Chapter I, §6.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal NNReal

section Metric

variable {X E F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The tail of a power of the distance.** If the closed balls about `y` satisfy the growth
bound `μ (closedBall y r) ≤ A rⁿ`, then for `0 ≤ s`, `n < s` and `R > 0`,

`∫_{dist x y > R} dist x y ^ (-s) dx ≤ A 2ⁿ R ^ (n - s) / (1 - 2 ^ (n - s))`. -/
theorem setLIntegral_ofReal_dist_rpow_neg_le {y : X} {A : ℝ≥0∞} {n s : ℝ}
    (hμ : ∀ r, 0 < r → μ (closedBall y r) ≤ A * ENNReal.ofReal (r ^ n)) (hs : 0 ≤ s)
    (hns : n < s) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in {x | R < dist x y}, ENNReal.ofReal (dist x y ^ (-s)) ∂μ ≤
      A * ENNReal.ofReal (2 ^ n / (1 - 2 ^ (n - s)) * R ^ (n - s)) := by
  set q : ℝ := 2 ^ (n - s)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  -- The dyadic annuli `2ᵏ R ≤ dist x y < 2ᵏ⁺¹ R` cover the region `R < dist x y`.
  set S : ℕ → Set X := fun k => (fun x => dist x y) ⁻¹' Ico (2 ^ k * R) (2 ^ (k + 1) * R)
  have hcover : {x | R < dist x y} ⊆ ⋃ k, S k := by
    intro x hx
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near ((one_le_div hR).2 (le_of_lt hx))
      one_lt_two
    refine mem_iUnion.2 ⟨k, ?_, ?_⟩
    · exact (le_div_iff₀ hR).1 hk
    · rw [pow_succ] at hk' ⊢
      exact (div_lt_iff₀ hR).1 hk'
  -- On the `k`-th annulus the integrand is at most `(2ᵏ R) ^ (-s)`, and the annulus lies in a
  -- ball of measure at most `A (2ᵏ⁺¹ R)ⁿ`.
  have hS (k : ℕ) : ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ ≤
      A * ENNReal.ofReal (2 ^ n * R ^ (n - s) * q ^ k) := by
    have hk : 0 < 2 ^ k * R := by positivity
    have hmeas : MeasurableSet (S k) :=
      measurableSet_Ico.preimage (continuous_id.dist continuous_const).measurable
    calc ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ
        ≤ ∫⁻ _ in S k, ENNReal.ofReal ((2 ^ k * R) ^ (-s)) ∂μ :=
          setLIntegral_mono' hmeas fun x hx => ENNReal.ofReal_le_ofReal <|
            Real.rpow_le_rpow_of_nonpos hk hx.1 (neg_nonpos.2 hs)
      _ ≤ ENNReal.ofReal ((2 ^ k * R) ^ (-s)) * (A * ENNReal.ofReal ((2 ^ (k + 1) * R) ^ n)) := by
          rw [setLIntegral_const]
          gcongr
          exact (measure_mono fun x hx => mem_closedBall.2 hx.2.le).trans
            (hμ _ (by positivity))
      _ = A * ENNReal.ofReal (2 ^ n * R ^ (n - s) * q ^ k) := by
          rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          have h2 : (0 : ℝ) < 2 ^ k := by positivity
          have hq : q ^ k = (2 : ℝ) ^ ((k : ℝ) * n) / 2 ^ ((k : ℝ) * s) := by
            rw [← Real.rpow_mul_natCast zero_le_two, ← Real.rpow_sub two_pos]
            ring_nf
          rw [hq, Real.mul_rpow h2.le hR.le, Real.mul_rpow (by positivity) hR.le, pow_succ,
            Real.mul_rpow h2.le zero_le_two, Real.rpow_sub hR, Real.rpow_neg hR.le,
            Real.rpow_neg h2.le, ← Real.rpow_natCast_mul zero_le_two,
            ← Real.rpow_natCast_mul zero_le_two]
          field_simp
  calc ∫⁻ x in {x | R < dist x y}, ENNReal.ofReal (dist x y ^ (-s)) ∂μ
      ≤ ∫⁻ x in ⋃ k, S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ x in S k, ENNReal.ofReal (dist x y ^ (-s)) ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' k, A * ENNReal.ofReal (2 ^ n * R ^ (n - s) * q ^ k) := ENNReal.tsum_le_tsum hS
    _ = A * ENNReal.ofReal (2 ^ n / (1 - q) * R ^ (n - s)) := by
        simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n * R ^ (n - s)),
          ENNReal.ofReal_pow hq0]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0,
          ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- **The standard smoothness estimate implies Hörmander's condition.** Let the closed balls
about `y'` satisfy the growth bound `μ (closedBall y' r) ≤ A rⁿ` with `0 ≤ n`, and let `K` satisfy
the standard smoothness estimate with exponent `δ > 0`,

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ dist x y' ^ (-(n + δ))` whenever `dist x y' > 2 dist y y'`.

Then `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ C A 2ⁿ / (2^δ - 1)`. -/
theorem setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow {K : X → X → E →L[ℝ] F} {y y' : X}
    {A : ℝ≥0∞} {n : ℝ} (hμ : ∀ r, 0 < r → μ (closedBall y' r) ≤ A * ENNReal.ofReal (r ^ n))
    (hn : 0 ≤ n) {C : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x, 2 * dist y y' < dist x y' →
      ‖K x y - K x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(n + δ)))) :
    ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ∂μ ≤
      C * A * ENNReal.ofReal (2 ^ n / (2 ^ δ - 1)) := by
  set t := dist y y'
  have hmeas : MeasurableSet {x | 2 * t < dist x y'} :=
    measurableSet_lt measurable_const (continuous_id.dist continuous_const).measurable
  have hpt : ∀ x ∈ {x | 2 * t < dist x y'}, ‖K x y - K x y'‖ₑ ≤
      ENNReal.ofReal (C * t ^ δ) * ENNReal.ofReal (dist x y' ^ (-(n + δ))) := fun x hx => by
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, mul_assoc]
    exact ENNReal.ofReal_le_ofReal (hK x hx)
  calc ∫⁻ x in {x | 2 * t < dist x y'}, ‖K x y - K x y'‖ₑ ∂μ
      ≤ ∫⁻ x in {x | 2 * t < dist x y'},
          ENNReal.ofReal (C * t ^ δ) * ENNReal.ofReal (dist x y' ^ (-(n + δ))) ∂μ :=
        setLIntegral_mono' hmeas hpt
    _ = ENNReal.ofReal (C * t ^ δ) *
          ∫⁻ x in {x | 2 * t < dist x y'}, ENNReal.ofReal (dist x y' ^ (-(n + δ))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ C * A * ENNReal.ofReal (2 ^ n / (2 ^ δ - 1)) := by
        rcases eq_or_lt_of_le (show 0 ≤ t from dist_nonneg) with ht | ht
        · rw [← ht, Real.zero_rpow hδ.ne', mul_zero, ENNReal.ofReal_zero, zero_mul]
          exact bot_le
        have h := setLIntegral_ofReal_dist_rpow_neg_le hμ (by positivity) (by linarith : n < n + δ)
          (by positivity : 0 < 2 * t)
        calc ENNReal.ofReal (C * t ^ δ) *
              ∫⁻ x in {x | 2 * t < dist x y'}, ENNReal.ofReal (dist x y' ^ (-(n + δ))) ∂μ
            ≤ ENNReal.ofReal (C * t ^ δ) *
                (A * ENNReal.ofReal (2 ^ n / (1 - 2 ^ (n - (n + δ))) * (2 * t) ^ (n - (n + δ)))) :=
              by gcongr
          _ = C * A * ENNReal.ofReal (2 ^ n / (2 ^ δ - 1)) := by
              have hr : (C : ℝ) * t ^ δ *
                  (2 ^ n / (1 - 2 ^ (n - (n + δ))) * (2 * t) ^ (n - (n + δ))) =
                    C * (2 ^ n / (2 ^ δ - 1)) := by
                have h2 : (1 : ℝ) < 2 ^ δ := Real.one_lt_rpow one_lt_two hδ
                rw [show n - (n + δ) = -δ by ring, Real.rpow_neg zero_le_two,
                  Real.rpow_neg (by positivity), Real.mul_rpow zero_le_two ht.le]
                have : (2 : ℝ) ^ δ - 1 ≠ 0 := by linarith
                have : 1 - ((2 : ℝ) ^ δ)⁻¹ ≠ 0 := by
                  rw [sub_ne_zero, ne_comm, inv_ne_one]; exact h2.ne'
                have : t ^ δ ≠ 0 := (Real.rpow_pos_of_pos ht δ).ne'
                field_simp
              rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), hr,
                ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
              ring

end Metric

section Pi

variable {ι : Type*} [Fintype ι] {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The standard smoothness estimate implies Hörmander's condition** on `ℝⁿ = ι → ℝ`, with the
sup norm and Lebesgue measure. If `δ > 0` and

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ dist x y' ^ (-(n + δ))` whenever `dist x y' > 2 dist y y'`,

then `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ 4ⁿ C / (2^δ - 1)`. -/
theorem setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}
    {y y' : ι → ℝ} {C : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x, 2 * dist y y' < dist x y' →
      ‖K x y - K x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Fintype.card ι + δ)))) :
    ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ≤
      C * ENNReal.ofReal (4 ^ Fintype.card ι / (2 ^ δ - 1)) := by
  -- Closed balls in the sup norm are cubes, of volume `(2r)ⁿ = 2ⁿ rⁿ`.
  have hμ (r : ℝ) (hr : 0 < r) : volume (closedBall y' r) ≤
      (2 : ℝ≥0∞) ^ Fintype.card ι * ENNReal.ofReal (r ^ (Fintype.card ι : ℝ)) := by
    rw [Real.volume_pi_closedBall y' hr.le, Real.rpow_natCast, mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  refine (setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow hμ (Nat.cast_nonneg _) hδ hK).trans
    (le_of_eq ?_)
  rw [mul_assoc, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
    ← ENNReal.ofReal_mul (by positivity), Real.rpow_natCast, ← mul_div_assoc, ← mul_pow]
  norm_num

end Pi

end TauCeti

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The Calderón–Zygmund theorem** for an operator with a standard kernel. Let `T` be a bounded
linear operator on `L²(ℝⁿ)` such that `T b x = ∫ K x y (b y) dy` for almost every `x` off any
closed ball outside which `b` vanishes, where for some `δ > 0` the kernel `K` satisfies the
standard smoothness estimate

`‖K x y - K x y'‖ ≤ C dist y y' ^ δ dist x y' ^ (-(n + δ))` whenever `dist x y' > 2 dist y y'`.

Then for every `f ∈ L²` and every `t`,

`t · |{‖T f‖ > t}| ≤ (2ⁿ (4 ‖T‖² + 1) + 4 · 4ⁿ C / (2^δ - 1)) ‖f‖₁`. -/
theorem mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow [Nonempty ι]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hKm : StronglyMeasurable (Function.uncurry K))
    {C : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x y y', 2 * dist y y' < dist x y' →
      ‖K x y - K x y'‖ ≤ C * (dist y y' ^ δ * dist x y' ^ (-(Fintype.card ι + δ))))
    (hrep : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) →
        ∀ᵐ x, x ∉ closedBall y r → T b x = ∫ z, K x z (b z))
    (f : Lp E 2 (volume : Measure (ι → ℝ))) (t : ℝ≥0∞) :
    t * volume {x | t < ‖T f x‖ₑ} ≤
      (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) +
        4 * (C * ENNReal.ofReal (4 ^ Fintype.card ι / (2 ^ δ - 1)))) * ∫⁻ x, ‖f x‖ₑ :=
  mul_volume_lt_enorm_le_of_hormander T hKm
    (fun _ _ => setLIntegral_enorm_sub_le_of_norm_sub_le_mul_rpow_pi hδ fun x => hK x _ _) hrep f t

end ContinuousLinearMap
