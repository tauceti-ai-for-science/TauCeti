/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Proportions of a set inside and outside a measurable set

A measurable set `T` splits a set `S` of finite measure into `S ∩ T` and `S \ T`, whose measures
add up to that of `S`. So if `S \ T` has at least the fraction `c` of the measure of `S`, then
`S ∩ T` has at most the fraction `1 - c` (`MeasureTheory.measure_inter_le_ofReal_one_sub_mul`).
This is how a lower bound on the measure of a good set turns into an upper bound on the measure
of the bad set in density arguments.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- If the part of a set `S` of finite measure outside a measurable set `T` has at least the
fraction `c ≥ 0` of its measure, the part inside `T` has at most the fraction `1 - c`. -/
theorem measure_inter_le_ofReal_one_sub_mul {μ : Measure α} {S T : Set α} (hT : MeasurableSet T)
    (hS : μ S ≠ ∞) {c : ℝ} (hc : 0 ≤ c) (h : ENNReal.ofReal c * μ S ≤ μ (S \ T)) :
    μ (S ∩ T) ≤ ENNReal.ofReal (1 - c) * μ S := by
  have hadd := measure_inter_add_sdiff (μ := μ) S hT
  have hfin : μ (S \ T) ≠ ∞ := ne_top_of_le_ne_top hS (hadd ▸ le_add_self)
  rw [ENNReal.eq_sub_of_add_eq hfin hadd, ENNReal.ofReal_sub _ hc, ENNReal.ofReal_one,
    ENNReal.sub_mul fun _ _ ↦ hS, one_mul]
  exact tsub_le_tsub_left h _

end MeasureTheory
