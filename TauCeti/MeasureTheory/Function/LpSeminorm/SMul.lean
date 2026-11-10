/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Scaling the positive part in `Lᵖ`

Multiplying a real function by `c ≥ 0` multiplies its positive part by `c`, so it multiplies the
`Lᵖ` seminorm of the positive part by `c` (`MeasureTheory.eLpNorm_posPart_const_mul`). Such
seminorms measure the size of the right-hand side of a differential inequality `L u ≤ f`, which is
rescaled together with `u`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Multiplying a real function by `c ≥ 0` multiplies the `Lᵖ` seminorm of its positive part by
`c`. -/
theorem eLpNorm_posPart_const_mul {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (fun x ↦ (c * f x)⁺) p μ = ENNReal.ofReal c * eLpNorm (fun x ↦ (f x)⁺) p μ := by
  have hpos : (fun x ↦ (c * f x)⁺) = c • fun x ↦ (f x)⁺ := by
    ext x
    rw [Pi.smul_apply, smul_eq_mul]
    rcases le_total 0 (f x) with h | h
    · rw [posPart_eq_self.2 h, posPart_eq_self.2 (mul_nonneg hc h)]
    · rw [posPart_eq_zero.2 h, posPart_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos hc h),
        mul_zero]
  rw [hpos, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]

end MeasureTheory
