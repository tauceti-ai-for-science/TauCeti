/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# From geometric decay along powers to power decay

Let `φ` be a nonincreasing function with values in `ℝ≥0∞`, bounded by `V`, which decays
geometrically along the powers of `M > 1`: `φ (M ^ j) ≤ δ ^ j V` with `0 < δ ≤ 1`. Writing
`δ = M ^ (-ε)` with `ε = log δ⁻¹ / log M`, monotonicity between consecutive powers of `M` gives
the power decay

`φ t ≤ δ⁻¹ t ^ (-ε) V` for every `t > 0`

(`TauCeti.le_ofReal_mul_rpow_of_forall_pow_le`). This is the last step of the Krylov–Safonov
`L^ε` lemma and of other iterations whose outcome is the decay of a distribution function.
-/

public section

open scoped ENNReal

namespace TauCeti

/-- If a nonincreasing function `φ` is bounded by `V` and decays geometrically along the powers of
`M > 1`, `φ (M ^ j) ≤ δ ^ j V` with `0 < δ ≤ 1`, then it decays like the power
`t ^ (-log δ⁻¹ / log M)`. -/
theorem le_ofReal_mul_rpow_of_forall_pow_le {φ : ℝ → ℝ≥0∞} (hφ : Antitone φ)
    {V : ℝ≥0∞} {M δ : ℝ} (hM : 1 < M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hV : ∀ t, φ t ≤ V)
    (hpow : ∀ j : ℕ, φ (M ^ j) ≤ ENNReal.ofReal (δ ^ j) * V) {t : ℝ} (ht : 0 < t) :
    φ t ≤ ENNReal.ofReal (δ⁻¹ * t ^ (-(Real.log δ⁻¹ / Real.log M))) * V := by
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hε : 0 ≤ Real.log δ⁻¹ / Real.log M :=
    div_nonneg (Real.log_nonneg (one_le_inv₀ hδ0 |>.2 hδ1)) hlogM.le
  rcases lt_or_ge t 1 with ht1 | ht1
  · -- Below the level `1` the bound `V` suffices, since the right-hand factor is at least `1`.
    refine (hV t).trans (le_mul_of_one_le_left' ?_)
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_mul_of_one_le_of_one_le ((one_le_inv₀ hδ0).2 hδ1)
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (neg_nonpos.2 hε)))
  · obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near ht1 hM
    refine (hφ hj).trans ((hpow j).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) V))
    -- `δ = M ^ (-ε)`, so `δ ^ j = δ⁻¹ (M ^ (j + 1)) ^ (-ε) ≤ δ⁻¹ t ^ (-ε)`.
    have hδM : M ^ (-(Real.log δ⁻¹ / Real.log M)) = δ := by
      rw [Real.rpow_def_of_pos (one_pos.trans hM), mul_neg, mul_div_cancel₀ _ hlogM.ne',
        Real.log_inv, neg_neg, Real.exp_log hδ0]
    have hM0 : 0 ≤ M := (one_pos.trans hM).le
    calc δ ^ j = δ⁻¹ * (M ^ (j + 1)) ^ (-(Real.log δ⁻¹ / Real.log M)) := by
          rw [← Real.rpow_natCast_mul hM0, mul_comm ((j + 1 : ℕ) : ℝ),
            Real.rpow_mul_natCast hM0, hδM, pow_succ, mul_comm _ δ, inv_mul_cancel_left₀ hδ0.ne']
      _ ≤ δ⁻¹ * t ^ (-(Real.log δ⁻¹ / Real.log M)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht hj'.le (neg_nonpos.2 hε))
            (inv_nonneg.2 hδ0.le)

end TauCeti
