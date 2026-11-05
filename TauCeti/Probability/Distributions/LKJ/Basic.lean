/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Correlation
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.LKJ.Normalizer
import Mathlib.Algebra.Order.Star.Real

/-!
# The LKJ law of random correlation matrices

The LKJ law of shape `η > 0` on `p × p` correlation matrices has density proportional to
`(det R) ^ (η - 1)` on the positive-definite correlation matrices, against the reference measure
`TauCeti.correlationLebesgue p`, which is Lebesgue measure in the strictly lower correlation
coordinates. The proportionality constant is the reciprocal of `TauCeti.Probability.lkjNormalizer`.
For `η ≤ 0` the law is the zero measure.

The density is taken against the correlation-coordinate volume, not against the full symmetric
Lebesgue measure `TauCeti.symmetricLebesgue`: in positive dimension the unit-diagonal matrices form
a proper affine subspace of the symmetric matrices, so the law is singular with respect to the
latter.

The results here use only the shape of the density, not the value of the normalizing integral:
the density and its measurability, the support, the law in dimension at most one, where it is the
Dirac mass at the identity, the law at the uniform shape `η = 1`, invariance under permutation and
sign-change conjugation, measurability in the shape parameter, and the density and Radon–Nikodym
theorems.

## Main definitions

* `TauCeti.Probability.lkjPDFReal` and `TauCeti.Probability.lkjPDF` — the LKJ density, real- and
  `ℝ≥0∞`-valued.
* `TauCeti.Probability.lkjMeasure` — the LKJ law.

## Main results

* `TauCeti.Probability.lkjMeasure_eq_map_withDensity` — the law read in correlation coordinates.
* `TauCeti.Probability.ae_posDef_lkjMeasure`, `TauCeti.Probability.ae_diag_eq_one_lkjMeasure` — an
  LKJ matrix is almost surely positive definite with unit diagonal.
* `TauCeti.Probability.support_lkjMeasure` — the topological support is the set of
  positive-semidefinite unit-diagonal matrices.
* `TauCeti.Probability.lkjMeasure_of_le_one` — in dimension at most one the law is the Dirac mass at
  the identity.
* `TauCeti.Probability.lkjMeasure_one` — at shape one the law is normalized correlation volume on
  the positive-definite correlation matrices.
* `TauCeti.Probability.map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure`,
  `TauCeti.Probability.map_symmetricCongruenceLinearMap_diagonal_lkjMeasure` — invariance under
  simultaneous permutation of rows and columns and under sign changes of the coordinate axes.
* `TauCeti.Probability.measurable_lkjMeasure` — measurability in the shape parameter.
* `TauCeti.Probability.hasPDF_of_hasLaw_lkjMeasure`, `TauCeti.Probability.rnDeriv_lkjMeasure` — an
  LKJ random matrix has a density against `TauCeti.correlationLebesgue`, and the law's
  Radon–Nikodym derivative is `TauCeti.Probability.lkjPDF`.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-! ### The density -/

open Classical in
/-- The **LKJ density** of shape `η`, as a real-valued function of a symmetric matrix: on the
positive-definite matrices it is `(det R) ^ (η - 1) / lkjNormalizer p η`, and it vanishes
elsewhere. It is a density against `TauCeti.correlationLebesgue p`, which only charges
unit-diagonal matrices. -/
def lkjPDFReal (p : ℕ) (η : ℝ) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ :=
  if (R : Matrix (Fin p) (Fin p) ℝ).PosDef then
    (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η
  else 0

open Classical in
/-- The defining branch expression of the real-valued LKJ density. -/
theorem lkjPDFReal_def (p : ℕ) (η : ℝ) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDFReal p η R =
      if (R : Matrix (Fin p) (Fin p) ℝ).PosDef then
        (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η
      else 0 :=
  (rfl)

/-- On the positive-definite matrices the LKJ density is its defining formula. -/
@[simp]
theorem lkjPDFReal_of_posDef (η : ℝ) {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDFReal p η R = (R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η := by
  classical
  rw [lkjPDFReal, ite_eq_left hR]

/-- Off the positive-definite matrices the LKJ density vanishes. -/
@[simp]
theorem lkjPDFReal_of_not_posDef (η : ℝ)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : ¬ (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDFReal p η R = 0 := by
  classical
  rw [lkjPDFReal, ite_eq_right hR]

/-- At a positive shape the LKJ density is nonnegative. -/
theorem lkjPDFReal_nonneg (hη : 0 < η) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    0 ≤ lkjPDFReal p η R := by
  by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [lkjPDFReal_of_posDef η hR]
    exact div_nonneg (Real.rpow_nonneg hR.det_pos.le _) (lkjNormalizer_pos hη).le
  · rw [lkjPDFReal_of_not_posDef η hR]

/-- At a positive shape the LKJ density is positive exactly on the positive-definite matrices. -/
theorem lkjPDFReal_pos_iff (hη : 0 < η)
    {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < lkjPDFReal p η R ↔ (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  refine ⟨fun h => ?_, fun hR => ?_⟩
  · by_contra hR
    rw [lkjPDFReal_of_not_posDef η hR] at h
    exact lt_irrefl 0 h
  · rw [lkjPDFReal_of_posDef η hR]
    exact div_pos (Real.rpow_pos_of_pos hR.det_pos _) (lkjNormalizer_pos hη)

/-- The `ℝ≥0∞`-valued LKJ density, the one that defines the measure. -/
def lkjPDF (p : ℕ) (η : ℝ) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (lkjPDFReal p η R)

/-- The `ℝ≥0∞`-valued LKJ density is `ENNReal.ofReal` of the real-valued one. -/
theorem lkjPDF_def (p : ℕ) (η : ℝ) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDF p η R = ENNReal.ofReal (lkjPDFReal p η R) :=
  (rfl)

/-- On the positive-definite matrices the `ℝ≥0∞`-valued LKJ density is its defining formula. -/
@[simp]
theorem lkjPDF_of_posDef (η : ℝ) {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDF p η R =
      ENNReal.ofReal ((R : Matrix (Fin p) (Fin p) ℝ).det ^ (η - 1) / lkjNormalizer p η) := by
  rw [lkjPDF_def, lkjPDFReal_of_posDef η hR]

/-- Off the positive-definite matrices the `ℝ≥0∞`-valued LKJ density vanishes. -/
@[simp]
theorem lkjPDF_of_not_posDef (η : ℝ) {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hR : ¬ (R : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    lkjPDF p η R = 0 := by
  rw [lkjPDF_def, lkjPDFReal_of_not_posDef η hR, ENNReal.ofReal_zero]

/-- At a positive shape the `ℝ≥0∞`-valued LKJ density is positive exactly on the positive-definite
matrices. -/
theorem lkjPDF_pos_iff (hη : 0 < η) {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} :
    0 < lkjPDF p η R ↔ (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [lkjPDF_def, ENNReal.ofReal_pos]
  exact lkjPDFReal_pos_iff hη

/-- The LKJ density is finite. -/
@[simp]
theorem lkjPDF_ne_top (p : ℕ) (η : ℝ) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDF p η R ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- At a positive shape the `ℝ≥0∞`-valued density carries the real one. -/
theorem toReal_lkjPDF (hη : 0 < η) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (lkjPDF p η R).toReal = lkjPDFReal p η R :=
  ENNReal.toReal_ofReal (lkjPDFReal_nonneg hη R)

/-- The real-valued LKJ density is measurable jointly in its shape and the point. -/
@[fun_prop]
theorem measurable_uncurry_lkjPDFReal (p : ℕ) :
    Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      lkjPDFReal p q.1 q.2 := by
  classical
  have hrpow : Measurable fun z : ℝ × ℝ => z.1 ^ z.2 := by fun_prop
  have hdet : Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (q.2 : Matrix (Fin p) (Fin p) ℝ).det :=
    (Continuous.matrix_det continuous_id).measurable.comp
      (measurable_subtype_coe.comp measurable_snd)
  simp only [lkjPDFReal]
  refine Measurable.ite (measurable_snd (measurableSet_posDefMatrix p)) ?_ measurable_const
  exact (hrpow.comp (hdet.prodMk (measurable_fst.sub_const 1))).div
    ((measurable_lkjNormalizer p).comp measurable_fst)

/-- The real-valued LKJ density is measurable in the point. -/
@[fun_prop]
theorem measurable_lkjPDFReal (p : ℕ) (η : ℝ) : Measurable (lkjPDFReal p η) :=
  (measurable_uncurry_lkjPDFReal p).comp (measurable_const.prodMk measurable_id)

/-- The `ℝ≥0∞`-valued LKJ density is measurable jointly in its shape and the point. -/
@[fun_prop]
theorem measurable_uncurry_lkjPDF (p : ℕ) :
    Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      lkjPDF p q.1 q.2 :=
  (measurable_uncurry_lkjPDFReal p).ennreal_ofReal

/-- The `ℝ≥0∞`-valued LKJ density is measurable in the point. -/
@[fun_prop]
theorem measurable_lkjPDF (p : ℕ) (η : ℝ) : Measurable (lkjPDF p η) :=
  (measurable_lkjPDFReal p η).ennreal_ofReal

/-- Congruence by a matrix of determinant `±1` preserves the LKJ density: it preserves positive
definiteness and the determinant. -/
private theorem lkjPDF_symmetricCongruenceLinearMap {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1) (η : ℝ) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDF p η (Matrix.symmetricCongruenceLinearMap M R) = lkjPDF p η R := by
  have hU : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 fun h => by simp [h] at hM)
  have hpos : (Matrix.symmetricCongruenceLinearMap M R : Matrix (Fin p) (Fin p) ℝ).PosDef ↔
      (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
    rw [Matrix.coe_symmetricCongruenceLinearMap_apply,
      ← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose,
      Matrix.IsUnit.posDef_star_right_conjugate_iff hU]
  by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [lkjPDF_of_posDef η (hpos.2 hR), lkjPDF_of_posDef η hR,
      Matrix.det_coe_symmetricCongruenceLinearMap_apply, hM, one_mul]
  · rw [lkjPDF_of_not_posDef η (mt hpos.1 hR), lkjPDF_of_not_posDef η hR]

/-! ### The measure -/

/-- The **LKJ law** of shape `η` on `p × p` correlation matrices: for `0 < η`, the density
`TauCeti.Probability.lkjPDF p η`, proportional to `(det R) ^ (η - 1)` on the positive-definite
correlation matrices, against `TauCeti.correlationLebesgue p`. For `η ≤ 0` it is the zero
measure. -/
def lkjMeasure (p : ℕ) (η : ℝ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  if 0 < η then (correlationLebesgue p).withDensity (lkjPDF p η) else 0

/-- The defining branch expression of the LKJ law. -/
theorem lkjMeasure_def (p : ℕ) (η : ℝ) :
    lkjMeasure p η =
      if 0 < η then (correlationLebesgue p).withDensity (lkjPDF p η) else 0 :=
  (rfl)

/-- At a positive shape the LKJ law is its density against `TauCeti.correlationLebesgue`. -/
theorem lkjMeasure_of_pos (hη : 0 < η) :
    lkjMeasure p η = (correlationLebesgue p).withDensity (lkjPDF p η) := by
  rw [lkjMeasure, ite_eq_left hη]

/-- At a nonpositive shape the LKJ law is the zero measure. -/
@[simp]
theorem lkjMeasure_of_nonpos (hη : η ≤ 0) : lkjMeasure p η = 0 := by
  rw [lkjMeasure, ite_eq_right (not_lt.2 hη)]

/-- The LKJ law is absolutely continuous with respect to `TauCeti.correlationLebesgue`. -/
theorem lkjMeasure_absolutelyContinuous (p : ℕ) (η : ℝ) :
    lkjMeasure p η ≪ correlationLebesgue p := by
  rcases le_or_gt η 0 with hη | hη
  · rw [lkjMeasure_of_nonpos hη]
    exact Measure.AbsolutelyContinuous.zero _
  · rw [lkjMeasure_of_pos hη]
    exact withDensity_absolutelyContinuous _ _

/-- **The LKJ law in correlation coordinates.** At a positive shape it is the image under
`TauCeti.correlationMatrix p` of coordinate Lebesgue measure weighted by the LKJ density read in
coordinates. -/
theorem lkjMeasure_eq_map_withDensity (hη : 0 < η) :
    lkjMeasure p η =
      (volume.withDensity fun x => lkjPDF p η (correlationMatrix p x)).map
        (correlationMatrix p) := by
  rw [lkjMeasure_of_pos hη]
  refine (Measure.map_withDensity_eq_withDensity (jac := 1)
    (correlationMatrix p).continuous.measurable measurable_one (measurable_lkjPDF p η) ?_
    (ae_of_all _ fun x => by rw [Pi.one_apply, one_mul])).symm
  rw [withDensity_one, (measurePreserving_correlationMatrix p).map_eq]

/-- The LKJ law gives no mass to the complement of the positive-definite matrices. -/
@[simp]
theorem lkjMeasure_compl_posDef (p : ℕ) (η : ℝ) :
    lkjMeasure p η
        {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (R : Matrix (Fin p) (Fin p) ℝ).PosDef}ᶜ = 0 := by
  rcases le_or_gt η 0 with hη | hη
  · simp [lkjMeasure_of_nonpos hη]
  · rw [lkjMeasure_of_pos hη, withDensity_apply _ (measurableSet_posDefMatrix p).compl]
    exact setLIntegral_eq_zero (measurableSet_posDefMatrix p).compl fun R hR =>
      lkjPDF_of_not_posDef η hR

/-- A matrix sampled from the LKJ law is almost surely positive definite. -/
theorem ae_posDef_lkjMeasure (p : ℕ) (η : ℝ) :
    ∀ᵐ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂lkjMeasure p η,
      (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  rw [ae_iff]
  exact lkjMeasure_compl_posDef p η

/-- A matrix sampled from the LKJ law almost surely has unit diagonal. -/
theorem ae_diag_eq_one_lkjMeasure (p : ℕ) (η : ℝ) :
    ∀ᵐ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂lkjMeasure p η,
      ∀ i, (R : Matrix (Fin p) (Fin p) ℝ) i i = 1 :=
  lkjMeasure_absolutelyContinuous p η (ae_correlationLebesgue_diag_eq_one p)

/-- **The support of the LKJ law.** At a positive shape the topological support of the LKJ law is
the set of correlation matrices: the positive-semidefinite symmetric matrices with unit diagonal. -/
theorem support_lkjMeasure (hη : 0 < η) :
    (lkjMeasure p η).support =
      {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          ∀ i, (R : Matrix (Fin p) (Fin p) ℝ) i i = 1} := by
  set g : (strictLowerTriangle p → ℝ) → ℝ≥0∞ := fun x => lkjPDF p η (correlationMatrix p x)
  have hg : Measurable g :=
    (measurable_lkjPDF p η).comp (correlationMatrix p).continuous.measurable
  have hsupp : Function.support g = posDefCorrelationRegion p := by
    ext x
    rw [Function.mem_support, ← pos_iff_ne_zero, lkjPDF_pos_iff hη, mem_posDefCorrelationRegion]
  -- In coordinates the density is positive exactly on the open positive-definite region, whose
  -- closure is the positive-semidefinite region.
  have hcoord : (volume.withDensity g).support =
      {x | (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).PosSemidef} := by
    rw [Measure.support_withDensity_eq_closure hg (isOpen_posDefCorrelationRegion p) hsupp,
      closure_posDefCorrelationRegion]
  have hclosed : IsClosed
      {x | (correlationMatrix p x : Matrix (Fin p) (Fin p) ℝ).PosSemidef} := by
    rw [← closure_posDefCorrelationRegion]
    exact isClosed_closure
  rw [lkjMeasure_eq_map_withDensity hη,
    Measure.support_map_eq_closure_image _ Measure.support_mem_ae
      (correlationMatrix p).continuous, hcoord,
    ((isClosedEmbedding_correlationMatrix p).isClosedMap _ hclosed).closure_eq]
  ext R
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, coe_correlationMatrix_apply_self x⟩
  · rintro ⟨hR, hdiag⟩
    refine ⟨correlationCoordinates p R, ?_, correlationMatrix_correlationCoordinates hdiag⟩
    rwa [mem_ofPred_eq, correlationMatrix_correlationCoordinates hdiag]

/-! ### Special shapes and dimensions -/

/-- **The LKJ law in dimension at most one.** There the only correlation matrix is the identity,
and at every positive shape the LKJ law is the Dirac mass there. -/
theorem lkjMeasure_of_le_one (hp : p ≤ 1) (hη : 0 < η) :
    lkjMeasure p η = Measure.dirac ⟨1, IsSelfAdjoint.one _⟩ := by
  have hZ : lkjNormalizer p η = 1 := by
    interval_cases p <;> simp
  rw [lkjMeasure_of_pos hη, correlationLebesgue_of_le_one hp,
    dirac_withDensity' (measurable_lkjPDF p η),
    lkjPDF_of_posDef η (R := ⟨1, IsSelfAdjoint.one _⟩) Matrix.PosDef.one]
  simp [hZ]

/-- **The LKJ law of shape one** is the normalized correlation volume of the positive-definite
correlation matrices: `TauCeti.correlationLebesgue p` restricted to the positive-definite matrices
and scaled by `1 / lkjNormalizer p 1`. -/
theorem lkjMeasure_one (p : ℕ) :
    lkjMeasure p 1 = ENNReal.ofReal (lkjNormalizer p 1)⁻¹ •
      (correlationLebesgue p).restrict
        {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (R : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  have h : lkjPDF p 1 =
      {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (R : Matrix (Fin p) (Fin p) ℝ).PosDef}.indicator
        fun _ => ENNReal.ofReal (lkjNormalizer p 1)⁻¹ := by
    ext R
    by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef
    · rw [lkjPDF_of_posDef 1 hR, indicator_of_mem hR, sub_self, Real.rpow_zero,
        one_div]
    · rw [lkjPDF_of_not_posDef 1 hR, indicator_of_notMem hR]
  rw [lkjMeasure_of_pos one_pos, h, withDensity_indicator (measurableSet_posDefMatrix p),
    withDensity_const]

/-! ### Invariance -/

/-- Congruence by a matrix of determinant `±1` that preserves `TauCeti.correlationLebesgue` also
preserves every LKJ law. -/
private theorem map_symmetricCongruenceLinearMap_lkjMeasure_of_map {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1)
    (hmap : (correlationLebesgue p).map (Matrix.symmetricCongruenceLinearMap M) =
      correlationLebesgue p) (η : ℝ) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap M) = lkjMeasure p η := by
  rcases le_or_gt η 0 with hη | hη
  · simp [lkjMeasure_of_nonpos hη]
  rw [lkjMeasure_of_pos hη]
  refine Measure.map_withDensity_eq_withDensity (jac := 1)
    (LinearMap.continuous_of_finiteDimensional _).measurable measurable_one
    (measurable_lkjPDF p η) (by rwa [withDensity_one]) (ae_of_all _ fun R => ?_)
  rw [Pi.one_apply, one_mul, lkjPDF_symmetricCongruenceLinearMap hM]

variable (p) in
/-- **The LKJ law is invariant under simultaneous permutation of rows and columns**: conjugation by
a permutation matrix preserves it. -/
theorem map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure (σ : Equiv.Perm (Fin p))
    (η : ℝ) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap (σ.permMatrix ℝ)) =
      lkjMeasure p η := by
  refine map_symmetricCongruenceLinearMap_lkjMeasure_of_map ?_
    (map_symmetricCongruenceLinearMap_permMatrix_correlationLebesgue p σ) η
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

variable (p) in
/-- **The LKJ law is invariant under sign changes of the coordinate axes**: conjugation by a
diagonal matrix with entries `±1` preserves it. -/
theorem map_symmetricCongruenceLinearMap_diagonal_lkjMeasure {s : Fin p → ℝ}
    (hs : ∀ i, |s i| = 1) (η : ℝ) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s)) =
      lkjMeasure p η := by
  refine map_symmetricCongruenceLinearMap_lkjMeasure_of_map ?_
    (map_symmetricCongruenceLinearMap_diagonal_correlationLebesgue p hs) η
  rw [Matrix.det_diagonal, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← sq_abs, hs i, one_pow]

/-! ### Measurability in the shape -/

variable (p) in
/-- The LKJ law is measurable in its shape parameter, for the Giry measurable structure on
measures. -/
@[fun_prop]
theorem measurable_lkjMeasure : Measurable (lkjMeasure p) := by
  have h : lkjMeasure p = fun η =>
      if 0 < η then (correlationLebesgue p).withDensity (lkjPDF p η) else 0 :=
    funext (lkjMeasure_def p)
  rw [h]
  exact Measurable.ite measurableSet_Ioi
    (measurable_withDensity (measurable_uncurry_lkjPDF p)) measurable_const

/-! ### The density of an LKJ random matrix -/

section Density

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}

/-- A random symmetric matrix with an LKJ law has a density against
`TauCeti.correlationLebesgue`, at every shape: at a nonpositive shape the law is zero, which
trivially has one. -/
theorem hasPDF_of_hasLaw_lkjMeasure (hX : HasLaw X (lkjMeasure p η) P) :
    HasPDF X P (correlationLebesgue p) := by
  rcases le_or_gt η 0 with hη | hη
  · refine Probability.hasPDF_of_hasLaw_withDensity (f := 0) aemeasurable_const ?_
    rwa [withDensity_zero, ← lkjMeasure_of_nonpos hη]
  · exact Probability.hasPDF_of_hasLaw_withDensity (measurable_lkjPDF p η).aemeasurable
      (by rwa [← lkjMeasure_of_pos hη])

/-- The density against `TauCeti.correlationLebesgue` of a random symmetric matrix with an LKJ law
of positive shape is `TauCeti.Probability.lkjPDF`. -/
theorem pdf_eq_lkjPDF_of_hasLaw_lkjMeasure (hη : 0 < η) (hX : HasLaw X (lkjMeasure p η) P) :
    pdf X P (correlationLebesgue p) =ᵐ[correlationLebesgue p] lkjPDF p η :=
  Probability.pdf_eq_of_hasLaw_withDensity (measurable_lkjPDF p η).aemeasurable
    (by rwa [← lkjMeasure_of_pos hη])

/-- **The Radon–Nikodym derivative of the LKJ law** against `TauCeti.correlationLebesgue` is the
LKJ density. -/
theorem rnDeriv_lkjMeasure (hη : 0 < η) :
    (lkjMeasure p η).rnDeriv (correlationLebesgue p) =ᵐ[correlationLebesgue p] lkjPDF p η := by
  rw [lkjMeasure_of_pos hη]
  exact Measure.rnDeriv_withDensity _ (measurable_lkjPDF p η)

end Density

end TauCeti.Probability
