/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.AlgHom
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Classification
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteMap
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# The projective line is the two-chart model of `k(X)`

The projective line `ℙ¹_k = Proj k[X₀, X₁]` over a field `k`
(`TauCeti.AlgebraicGeometry.projectiveLine`) is a regular proper curve over `k` whose function
field is the rational function field `k(X)`, the function `X₁ / X₀` going to `X`
(`TauCeti.AlgebraicGeometry.projectiveLine.functionFieldEquiv`). By the classification of regular
proper curves (`AlgebraicGeometry.Scheme.isoTwoChartModel`), it is therefore isomorphic over `k` to
the two-chart model of `k(X)` built from `X`, the scheme glued from `Spec k[X]` and `Spec k[X⁻¹]`.

For a function field `F` finite over `k(X)`, the two-chart model of `F` built from the image `x` of
`X` maps finitely to the two-chart model of `k(X)`
(`TauCeti.AlgebraicGeometry.twoChartModel.isFinite_map`), and is the normalization of the latter in
`F` (`TauCeti.AlgebraicGeometry.twoChartModel.normalizationIso`). Composing with the isomorphism
above gives the projection `ν_F` of the two-chart model of `F` onto `ℙ¹_k` itself: a finite
morphism over `k` whose pullback of rational functions is the inclusion `k(X) → F`.

## Main definitions

* `TauCeti.AlgebraicGeometry.projectiveLine.isoTwoChartModel`: the isomorphism of `ℙ¹_k` with the
  two-chart model of `k(X)` built from `X`.
* `TauCeti.AlgebraicGeometry.twoChartModel.toProjectiveLine`: the projection `ν_F` of the
  two-chart model of `F` to `ℙ¹_k`.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.isCurveOver`: `ℙ¹_k` is a curve over `k`. Its local
  rings are regular (`TauCeti.AlgebraicGeometry.projectiveLine.isRegularLocalRing_stalk`), so those
  at codimension-one points are discrete valuation rings.
* `TauCeti.AlgebraicGeometry.projectiveLine.isIntegrallyClosedIn_functionField`: `k` is integrally
  closed in the function field of `ℙ¹_k`.
* `TauCeti.AlgebraicGeometry.projectiveLine.exists_residueDegree_eq_one`: `ℙ¹_k` has a
  codimension-one point of residue degree one, the image of a `k`-rational point.
* `projectiveLine.functionFieldEquiv_functionFieldMap_isoTwoChartModel_hom` and
  `projectiveLine.functionFieldEquiv_functionFieldMap_isoTwoChartModel_inv`, in the namespace
  `TauCeti.AlgebraicGeometry`: the pullbacks of rational functions along the isomorphism with the
  two-chart model and along its inverse are the identity of `k(X)`.
* `TauCeti.AlgebraicGeometry.twoChartModel.isFinite_toProjectiveLine`: `ν_F` is finite.
* `TauCeti.AlgebraicGeometry.twoChartModel.functionFieldEquiv_functionFieldMap_toProjectiveLine`:
  the pullback of rational functions along `ν_F` is the inclusion `k(X) → F`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace projectiveLine

variable (k : Type u) [Field k]

/-! ### The projective line is a regular proper curve -/

/-- **The projective line is a curve over `k`**: it is integral and proper over `k`, and its
dimension is the transcendence degree one of its function field `k(X)`. -/
instance isCurveOver : (projectiveLine k).IsCurveOver k where
  topologicalKrullDim_eq_one := by
    rw [topologicalKrullDim_eq_toNat_trdeg_functionField k, (functionFieldEquiv k).trdeg_eq,
      (IsFunctionField.ratFunc k).trdeg_eq_one]
    simp

/-- Every point of the projective line over a field has codimension at most one. -/
instance fact_coheight_le_one : Fact (∀ y : projectiveLine k, Order.coheight y ≤ 1) :=
  ⟨fun y ↦ Scheme.IsCurveOver.coheight_le_one (k := k) y⟩

/-- `k` is integrally closed in the function field `k(t)` of the projective line. -/
theorem isIntegrallyClosedIn_functionField :
    IsIntegrallyClosedIn k (projectiveLine k).functionField :=
  (functionFieldEquiv k).isIntegrallyClosedIn.mpr inferInstance

/-- The origin `[1 : 0]` of the chart `D₊(X₀) = Spec k[X]`, as a `k`-rational point. -/
private noncomputable def origin : Spec (.of k) ⟶ projectiveLine k :=
  Spec.map (CommRingCat.ofHom ((Polynomial.aeval (0 : k)).comp
    (awayEquivPolynomial k 0).toAlgHom).toRingHom) ≫ awayι k 0

/-- The origin is a section of the structure morphism of the projective line. -/
private lemma origin_comp_over : origin k ≫ (projectiveLine k ↘ Spec (.of k)) = 𝟙 _ := by
  rw [origin, Category.assoc, awayι_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, Algebra.algebraMap_self,
    CommRingCat.ofHom_id, Spec.map_id]

/-- The projective line over a field has a codimension-one point of residue degree one. -/
theorem exists_residueDegree_eq_one : ∃ x₀ : CodimensionOnePoint (projectiveLine k),
    (projectiveLine k ↘ Spec (.of k)).residueDegree x₀ = 1 :=
  ⟨⟨origin k (IsLocalRing.closedPoint k),
    Scheme.IsCurveOver.coheight_section_eq_one k (origin_comp_over k)⟩,
    residueDegree_eq_one_of_section (origin_comp_over k) _⟩

/-! ### The projective line is the two-chart model of `k(X)` -/

/-- The rational function `X₁ / X₀` of the projective line, the preimage of `X` in its function
field. -/
private noncomputable abbrev coordinateFunction : (projectiveLine k).functionField :=
  (functionFieldEquiv k).symm RatFunc.X

private theorem coordinateFunction_ne_zero : coordinateFunction k ≠ 0 := by
  simp [coordinateFunction, RatFunc.X_ne_zero]

private theorem transcendental_coordinateFunction : Transcendental k (coordinateFunction k) :=
  fun h ↦ RatFunc.transcendental_X (by simpa using h.algHom (functionFieldEquiv k).toAlgHom)

/-- **The projective line is the two-chart model of `k(X)`**: the isomorphism over `k` of
`ℙ¹_k = Proj k[X₀, X₁]` with the scheme glued from `Spec k[X]` and `Spec k[X⁻¹]`, whose pullback of
rational functions is the identity of `k(X)`
(`functionFieldEquiv_functionFieldMap_isoTwoChartModel_hom`). -/
noncomputable def isoTwoChartModel :
    projectiveLine k ≅ twoChartModel (IsFunctionField.ratFunc k) RatFunc.X_ne_zero :=
  (projectiveLine k).isoTwoChartModel (coordinateFunction_ne_zero k)
      (transcendental_coordinateFunction k) ≪≫
    (twoChartModel.isoOfAlgEquiv _ (IsFunctionField.ratFunc k) _ RatFunc.X_ne_zero
      (functionFieldEquiv k) (hxt := transcendental_coordinateFunction k)
      (hx't := RatFunc.transcendental_X)).symm

/-- The isomorphism `ℙ¹_k ⟶ twoChartModel` is a morphism over `k`. -/
instance : (isoTwoChartModel k).hom.IsOver (Spec (.of k)) := by
  rw [isoTwoChartModel, Iso.trans_hom, Iso.symm_hom, twoChartModel.isoOfAlgEquiv_inv]
  infer_instance

/-- The isomorphism `twoChartModel ⟶ ℙ¹_k` is a morphism over `k`. -/
instance : (isoTwoChartModel k).inv.IsOver (Spec (.of k)) := by
  rw [isoTwoChartModel, Iso.trans_inv, Iso.symm_inv, twoChartModel.isoOfAlgEquiv_hom]
  infer_instance

/-- **The pullback of rational functions along `ℙ¹_k ≅ twoChartModel` is the identity of `k(X)`**:
under the identifications of both function fields with `k(X)`, the pullback along the isomorphism
`ℙ¹_k ⟶ twoChartModel` fixes every rational function. -/
@[simp]
theorem functionFieldEquiv_functionFieldMap_isoTwoChartModel_hom (z : RatFunc k) :
    functionFieldEquiv k ((isoTwoChartModel k).hom.functionFieldMap
      ((twoChartModel.functionFieldEquiv RatFunc.transcendental_X).symm z)) = z := by
  have hF : IsFunctionField k (projectiveLine k).functionField :=
    Scheme.IsCurveOver.isFunctionField
  have h : (twoChartModel.homOfAlgHom (IsFunctionField.ratFunc k) hF RatFunc.X_ne_zero
      (coordinateFunction_ne_zero k) RatFunc.transcendental_X
      (transcendental_coordinateFunction k) (functionFieldEquiv k).symm.toAlgHom).functionFieldMap
        ((twoChartModel.functionFieldEquiv RatFunc.transcendental_X).symm z) =
      (twoChartModel.functionFieldEquiv (hF := hF) (transcendental_coordinateFunction k)).symm
        ((functionFieldEquiv k).symm z) := by
    rw [AlgEquiv.eq_symm_apply, twoChartModel.functionFieldEquiv_functionFieldMap_homOfAlgHom,
      AlgEquiv.coe_toAlgHom]
  simp only [isoTwoChartModel, Iso.trans_hom, Iso.symm_hom, twoChartModel.isoOfAlgEquiv_inv,
    Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply]
  rw [h, Scheme.functionFieldMap_isoTwoChartModel_hom, AlgEquiv.apply_symm_apply]

/-- The pullback of rational functions along the isomorphism `twoChartModel ⟶ ℙ¹_k` is the identity
of `k(X)`, under the identifications of both function fields with `k(X)`. -/
@[simp]
theorem functionFieldEquiv_functionFieldMap_isoTwoChartModel_inv (z : RatFunc k) :
    twoChartModel.functionFieldEquiv RatFunc.transcendental_X
      ((isoTwoChartModel k).inv.functionFieldMap ((functionFieldEquiv k).symm z)) = z := by
  conv_lhs => rw [← functionFieldEquiv_functionFieldMap_isoTwoChartModel_hom k z]
  rw [AlgEquiv.symm_apply_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.functionFieldMap_comp]
  simp

end projectiveLine

/-! ### The projection of a two-chart model to the projective line -/

namespace twoChartModel

variable {k F : Type u} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [Algebra.IsIntegral (RatFunc k) F]
  (hF : IsFunctionField k F) (hx : algebraMap (RatFunc k) F RatFunc.X ≠ 0)

/-- **The projection `ν_F` of the two-chart model of `F` to the projective line**, for a function
field `F` integral, equivalently finite, over `k(X)`: the morphism from the two-chart model of `F`
built from the image `x` of `X` to `ℙ¹_k`, glued from `Spec` of the inclusions `k[X] → 𝒪_x` and
`k[X⁻¹] → 𝒪_{x⁻¹}` and read through the isomorphism of `ℙ¹_k` with the two-chart model of
`k(X)`. -/
noncomputable def toProjectiveLine : twoChartModel hF hx ⟶ projectiveLine k :=
  map (IsFunctionField.ratFunc k) hF RatFunc.X_ne_zero hx rfl ≫
    (projectiveLine.isoTwoChartModel k).inv

/-- The projection to the projective line is a morphism over `k`. -/
instance : (toProjectiveLine hF hx).IsOver (Spec (.of k)) := by
  rw [toProjectiveLine]
  infer_instance

/-- The projection to the projective line is dominant. -/
instance : IsDominant (toProjectiveLine hF hx) := by
  rw [toProjectiveLine]
  infer_instance

/-- **The projection of the two-chart model of `F` to the projective line is finite.** This
includes inseparable extensions `F / k(X)`. -/
instance isFinite_toProjectiveLine : IsFinite (toProjectiveLine hF hx) := by
  have := isFinite_map (IsFunctionField.ratFunc k) hF RatFunc.X_ne_zero hx rfl
    RatFunc.transcendental_X
  rw [toProjectiveLine]
  infer_instance

/-- **The pullback of rational functions along the projection to the projective line is the
inclusion `k(X) → F`**, under the identifications of the function fields of `ℙ¹_k` and of the
two-chart model of `F` with `k(X)` and `F`. -/
@[simp]
theorem functionFieldEquiv_functionFieldMap_toProjectiveLine (z : RatFunc k) :
    functionFieldEquiv
        ((transcendental_algebraMap_iff (algebraMap (RatFunc k) F).injective).mpr
          RatFunc.transcendental_X)
        ((toProjectiveLine hF hx).functionFieldMap ((projectiveLine.functionFieldEquiv k).symm z)) =
      algebraMap (RatFunc k) F z := by
  have h : (projectiveLine.isoTwoChartModel k).inv.functionFieldMap
      ((projectiveLine.functionFieldEquiv k).symm z) =
        (functionFieldEquiv RatFunc.transcendental_X).symm z := by
    rw [AlgEquiv.eq_symm_apply,
      projectiveLine.functionFieldEquiv_functionFieldMap_isoTwoChartModel_inv]
  simp only [toProjectiveLine, Scheme.Hom.functionFieldMap_comp, CommRingCat.comp_apply, h]
  exact functionFieldEquiv_functionFieldMap_map _ hF _ hx rfl RatFunc.transcendental_X z

end twoChartModel

end TauCeti.AlgebraicGeometry
