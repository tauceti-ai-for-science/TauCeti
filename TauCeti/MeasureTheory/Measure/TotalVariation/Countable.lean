/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance on countable spaces

For two finite measures on a countable space with measurable singletons, total variation
distance is the sum of the absolute differences of their singleton masses. We give the extended
and real formulas, together with summability of the real series. No probability normalization
is required, and the formulas also cover the empty space.

These identities identify total variation distance between distributions on a countable state
space with the ℓ¹ distance of their point masses. We use Mathlib's normalization: the distance
between probability measures is at most two, not one.

The proof uses Mathlib's `VectorMeasure.variation_apply_singleton` and the decomposition of a
measure into its singleton masses, rather than constructing a separate discrete distance.

The largest excess `⨆ A, μ A - ν A` over measurable events has the same kind of description: it
is the sum of the truncated differences `μ {x} - ν {x}` of singleton masses, attained at the
event `{x | ν {x} < μ {x}}`. Only `ν` needs to be finite here. Combined with
`etvDist_eq_two_mul_iSup_sub`, this computes the total variation distance between measures of
equal total mass from the points where the first one is larger.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing
  Times*, second edition, American Mathematical Society, 2017, Proposition 4.2 and Remark 4.3.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- On a countable space, extended total variation distance is the sum of the extended norms
of the differences of singleton masses. -/
theorem etvDist_eq_tsum_enorm_singleton :
    etvDist μ ν = ∑' x, ‖μ.real {x} - ν.real {x}‖ₑ := by
  rw [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist]
  rw [← (μ.toSignedMeasure - ν.toSignedMeasure).variation.tsum_indicator_apply_singleton
    Set.univ MeasurableSet.univ]
  simp [VectorMeasure.variation_apply_singleton, Measure.toSignedMeasure_apply]

/-- The absolute differences of singleton masses of two finite measures form a summable family
on a countable space. -/
theorem summable_abs_measureReal_singleton_sub :
    Summable (fun x => |μ.real {x} - ν.real {x}|) := by
  have h := ENNReal.summable_toReal (etvDist_eq_tsum_enorm_singleton (μ := μ) (ν := ν) ▸
    etvDist_ne_top μ ν)
  simpa using h

/-- On a countable space, total variation distance is the ℓ¹ distance of the singleton masses.
In particular, no factor of one half occurs with Mathlib's normalization. -/
theorem tvDist_eq_tsum_abs_singleton :
    tvDist μ ν = ∑' x, |μ.real {x} - ν.real {x}| := by
  rw [tvDist, etvDist_eq_tsum_enorm_singleton, ENNReal.tsum_toReal_eq (by simp)]
  simp

omit [IsFiniteMeasure μ] in
/-- On a countable space, the event where `μ` puts more mass than `ν` on singletons has excess
`μ - ν` equal to the sum of the truncated differences of singleton masses. -/
theorem measure_sub_eq_tsum_singleton_sub :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑' x, (μ {x} - ν {x}) := by
  have hS : MeasurableSet {x | ν {x} < μ {x}} := (Set.to_countable _).measurableSet
  have hμ : μ {x | ν {x} < μ {x}} = ν {x | ν {x} < μ {x}} + ∑' x, (μ {x} - ν {x}) := by
    rw [← Measure.tsum_indicator_apply_singleton μ _ hS,
      ← Measure.tsum_indicator_apply_singleton ν _ hS, ← tsum_add]
    congr 1
    ext x
    by_cases hx : ν {x} < μ {x}
    · simp [Set.indicator_of_mem (s := {x | ν {x} < μ {x}}) hx, add_tsub_cancel_of_le hx.le]
    · simp [Set.indicator_of_notMem (s := {x | ν {x} < μ {x}}) hx,
        tsub_eq_zero_of_le (not_lt.mp hx)]
  rw [hμ, ENNReal.add_sub_cancel_left (measure_ne_top ν _)]

omit [IsFiniteMeasure μ] in
/-- **Excess on a countable space.** The largest excess `μ A - ν A` over measurable events is the
sum over points of the truncated differences `μ {x} - ν {x}` of singleton masses. It is attained
at the event `{x | ν {x} < μ {x}}`, see `measure_sub_eq_tsum_singleton_sub`. On a finite type the
right-hand side is the finite sum `∑ x, (μ {x} - ν {x})` by `tsum_fintype`. -/
theorem iSup_sub_eq_tsum_singleton_sub :
    ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A = ∑' x, (μ {x} - ν {x}) := by
  refine le_antisymm (iSup₂_le fun A hA => tsub_le_iff_left.mpr ?_) ?_
  · rw [← Measure.tsum_indicator_apply_singleton μ A hA,
      ← Measure.tsum_indicator_apply_singleton ν A hA, ← tsum_add]
    refine tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ A
    · simpa [Set.indicator_of_mem hx] using le_add_tsub
    · simp [Set.indicator_of_notMem hx]
  · rw [← measure_sub_eq_tsum_singleton_sub]
    exact le_iSup₂ (f := fun (A : Set α) (_ : MeasurableSet A) => μ A - ν A) _
      (Set.to_countable _).measurableSet

end MeasureTheory
