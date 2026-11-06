/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Refinements
public import TauCeti.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.Algebra.Homology.Homotopy

/-!
# Maps from a projective object placed in one degree

Let `C` be an abelian category, `X` a projective object of `C` and `n : ℤ`. For every object `M`
of the derived category of `C`, taking cohomology in degree `n` identifies maps from `X` placed in
degree `n` to `M` with maps from `X` to the `n`-th cohomology object of `M`
(`DerivedCategory.fromSingleEquivOfProjective`). For `C` the category of modules over a ring `A`
and `X = A`, this says that the maps `A[0] ⟶ M⟦n⟧` in the derived category are the elements of
`Hⁿ(M)`, so that the functor `Hom(A[0], -)` computes cohomology.

Represent `M` by a cochain complex `K`. Since `X` is projective, `X` placed in degree `n` is
K-projective, so maps from it to `K` in the derived category come from chain maps, that is,
from maps `X ⟶ Kⁿ` killed by the differential. Such a map induces zero on cohomology exactly when
it factors through the differential `Kⁿ⁻¹ ⟶ Kⁿ`, because a cycle defined on a projective object
whose cohomology class vanishes is a boundary
(`HomologicalComplex.exists_comp_d_eq_of_liftCycles_comp_homologyπ_eq_zero`); this is when the
chain map is null-homotopic (`CochainComplex.nonempty_homotopy_zero_iff_of_single`). Every map
`X ⟶ Hⁿ(K)` lifts along the epimorphism from the cycles, again by projectivity.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)

/-- A cycle `x : X ⟶ Kⁱ` defined on a projective object `X` whose cohomology class vanishes is a
boundary: it factors through the differential `Kʰ ⟶ Kⁱ`. -/
lemma exists_comp_d_eq_of_liftCycles_comp_homologyπ_eq_zero {X : C} [Projective X]
    (h i j : ι) (hh : c.prev i = h) (hj : c.next i = j) (x : X ⟶ K.X i) (hx : x ≫ K.d i j = 0)
    (hx' : K.liftCycles x j hj hx ≫ K.homologyπ i = 0) :
    ∃ y : X ⟶ K.X h, y ≫ K.d h i = x := by
  obtain ⟨X', π, _, y, hy⟩ :=
    (K.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements h i j hh hj x hx).1 hx'
  exact ⟨Projective.factorThru (𝟙 X) π ≫ y, by
    rw [Category.assoc, ← hy, Projective.factorThru_comp_assoc, Category.id_comp]⟩

end HomologicalComplex

namespace DerivedCategory

variable [HasDerivedCategory.{w} C]

open HomologicalComplex

omit [HasDerivedCategory C] in
/-- The component `X ⟶ Kⁿ` of a chain map from `X` placed in degree `n` to `K` is a cycle. -/
private lemma singleObjXSelf_inv_comp_f_comp_d (n : ℤ) (X : C) {K : CochainComplex C ℤ}
    (χ : (single C (.up ℤ) n).obj X ⟶ K) :
    ((singleObjXSelf (.up ℤ) n X).inv ≫ χ.f n) ≫ K.d n (n + 1) = 0 := by
  rw [Category.assoc, χ.comm]
  simp

/-- On a chain map `χ` from `X` placed in degree `n` to a complex `K`, the cohomology of its
image in the derived category is the cohomology class of its component `X ⟶ Kⁿ`. -/
private lemma inv_app_comp_homologyFunctor_map_Q_map (n : ℤ) (X : C) {K : CochainComplex C ℤ}
    (χ : (single C (.up ℤ) n).obj X ⟶ K) :
    (singleFunctorCompHomologyFunctorIso C n).inv.app X ≫ (homologyFunctor C n).map (Q.map χ) ≫
        (homologyFunctorFactors C n).hom.app K =
      K.liftCycles ((singleObjXSelf (.up ℤ) n X).inv ≫ χ.f n) (n + 1) (by simp)
        (singleObjXSelf_inv_comp_f_comp_d n X χ) ≫ K.homologyπ n := by
  have h₁ : (singleFunctorCompHomologyFunctorIso C n).inv.app X ≫
      (homologyFunctorFactors C n).hom.app (((CochainComplex.singleFunctors C).functor n).obj X) =
        (singleObjHomologySelfIso (.up ℤ) n X).inv := by
    simp only [Functor.id_obj, Functor.comp_obj, singleFunctorCompHomologyFunctorIso,
      SingleFunctors.evaluation_obj, SingleFunctors.postcomp_functor, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Category.assoc, Functor.isoWhiskerRight_inv, Functor.mapIso_inv,
      SingleFunctors.evaluation_map, singleFunctorsPostcompQIso_inv_hom, NatTrans.comp_app,
      homologyFunctorSingleIso_inv_app, Q_obj_single_obj, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
    -- The remaining composite `(homologyFunctorFactors C n).inv ≫ (homologyFunctorFactors C n).hom`
    -- is stated at objects that agree only up to unfolding `CochainComplex.singleFunctors`.
    exact (Category.assoc _ _ _).trans (by erw [Iso.inv_hom_id_app]; exact Category.comp_id _)
  have h₂ : (singleObjCyclesSelfIso (.up ℤ) n X).inv ≫ cyclesMap χ n =
      K.liftCycles ((singleObjXSelf (.up ℤ) n X).inv ≫ χ.f n) (n + 1) (by simp)
        (singleObjXSelf_inv_comp_f_comp_d n X χ) := by
    rw [← cancel_mono (K.iCycles n)]
    simp
  rw [homologyFunctorFactors_hom_naturality]
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ homologyMap χ n) h₁)).trans ?_
  rw [← singleObjCyclesSelfIso_inv_homologyπ, Category.assoc, homologyπ_naturality,
    reassoc_of% h₂]

variable (n : ℤ) (X : C)

/-- Taking cohomology in degree `n` of maps from `X` placed in degree `n`, as an additive map to
maps from `X` to the cohomology. -/
private noncomputable def toHomology (M : DerivedCategory C) :
    ((singleFunctor C n).obj X ⟶ M) →+ (X ⟶ (homologyFunctor C n).obj M) :=
  (Preadditive.leftComp _ ((singleFunctorCompHomologyFunctorIso C n).inv.app X)).comp
    (homologyFunctor C n).mapAddHom

private lemma toHomology_apply {M : DerivedCategory C} (φ : (singleFunctor C n).obj X ⟶ M) :
    toHomology n X M φ =
      (singleFunctorCompHomologyFunctorIso C n).inv.app X ≫ (homologyFunctor C n).map φ :=
  rfl

/-- The cohomology of an object represented by a complex `K` is the cohomology of `K`. -/
private noncomputable def homologyIso (K : CochainComplex C ℤ) :
    (homologyFunctor C n).obj (Q.obj K) ≅ K.homology n :=
  (homologyFunctorFactors C n).app K

private lemma toHomology_Q_map_comp_homologyIso_hom {K : CochainComplex C ℤ}
    (χ : (single C (.up ℤ) n).obj X ⟶ K) :
    toHomology n X (Q.obj K) (Q.map χ) ≫ (homologyIso n K).hom =
      K.liftCycles _ (n + 1) (by simp) (singleObjXSelf_inv_comp_f_comp_d n X χ) ≫
        K.homologyπ n :=
  (Category.assoc _ _ _).trans (inv_app_comp_homologyFunctor_map_Q_map n X χ)

variable [Projective X]

/-- Maps from a projective object `X` placed in degree `n` to an object represented by a complex
`K` are detected by their cohomology in degree `n`, and every map from `X` to `Hⁿ(K)` arises. -/
private lemma bijective_toHomology_Q_obj (K : CochainComplex C ℤ) :
    Function.Bijective (toHomology n X (Q.obj K)) := by
  have := CochainComplex.isKProjective_of_projective ((single C (.up ℤ) n).obj X) n
  have hQ := CochainComplex.IsKProjective.Q_map_surjective ((single C (.up ℤ) n).obj X) K
  let Ψ := (Preadditive.rightComp X (homologyIso n K).hom).comp (toHomology n X (Q.obj K))
  suffices Function.Bijective Ψ by
    convert! (Iso.homCongr (Iso.refl X) (homologyIso n K).symm).bijective.comp this using 1
    ext φ
    simp [Ψ, Preadditive.rightComp]
  refine ⟨(injective_iff_map_eq_zero Ψ).2 fun φ hφ ↦ ?_, fun β ↦ ?_⟩
  · -- A map whose cohomology vanishes comes from a chain map whose component is a boundary,
    -- that is, from a null-homotopic chain map.
    obtain ⟨χ, rfl⟩ := hQ φ
    have h₀ := (toHomology_Q_map_comp_homologyIso_hom n X χ).symm.trans hφ
    obtain ⟨y, hy⟩ := K.exists_comp_d_eq_of_liftCycles_comp_homologyπ_eq_zero (n - 1) n (n + 1)
      (by simp) (by simp) _ _ h₀
    obtain ⟨H⟩ := (CochainComplex.nonempty_homotopy_zero_iff_of_single K (sub_add_cancel n 1)
      χ).2 ⟨y, hy⟩
    rw [DerivedCategory.Q_map_eq_of_homotopy _ H, Q.map_zero]
  · -- A map `X ⟶ Hⁿ(K)` lifts to the cycles, and then to a chain map, since `X` is projective.
    let γ : X ⟶ K.cycles n := Projective.factorThru β (K.homologyπ n)
    let χ : (single C (.up ℤ) n).obj X ⟶ K := mkHomFromSingle (γ ≫ K.iCycles n) (by
      rintro _ rfl
      simp)
    have hγ : K.liftCycles _ (n + 1) (by simp) (singleObjXSelf_inv_comp_f_comp_d n X χ) = γ := by
      rw [← cancel_mono (K.iCycles n)]
      simp [χ, mkHomFromSingle_f]
    refine ⟨Q.map χ, (toHomology_Q_map_comp_homologyIso_hom n X χ).trans ?_⟩
    rw [hγ]
    exact Projective.factorThru_comp _ _

/-- For a projective object `X` of an abelian category `C` and `n : ℤ`, taking cohomology in
degree `n` identifies maps from `X` placed in degree `n` to an object `M` of the derived category
with maps from `X` to the `n`-th cohomology object `Hⁿ(M)`. -/
noncomputable def fromSingleEquivOfProjective (M : DerivedCategory C) :
    ((singleFunctor C n).obj X ⟶ M) ≃+ (X ⟶ (homologyFunctor C n).obj M) :=
  AddEquiv.ofBijective (toHomology n X M) (by
    -- Replace `M` by an isomorphic object represented by a cochain complex.
    let e := Q.objObjPreimageIso M
    convert! ((Iso.homCongr (Iso.refl X) ((homologyFunctor C n).mapIso e)).bijective.comp
      (bijective_toHomology_Q_obj n X (Q.objPreimage M))).comp
      (Iso.homCongr (Iso.refl _) e.symm).bijective using 1
    ext φ
    simp [toHomology_apply, ← Functor.map_comp])

/-- `fromSingleEquivOfProjective` takes the cohomology in degree `n` of a map, composed with the
identification of `X` with the cohomology of `X` placed in degree `n`. -/
@[simp]
lemma fromSingleEquivOfProjective_apply {M : DerivedCategory C}
    (φ : (singleFunctor C n).obj X ⟶ M) :
    fromSingleEquivOfProjective n X M φ =
      (singleFunctorCompHomologyFunctorIso C n).inv.app X ≫ (homologyFunctor C n).map φ :=
  (rfl)

/-- The identification `fromSingleEquivOfProjective` is natural in the target. -/
lemma fromSingleEquivOfProjective_comp {M M' : DerivedCategory C}
    (φ : (singleFunctor C n).obj X ⟶ M) (ψ : M ⟶ M') :
    fromSingleEquivOfProjective n X M' (φ ≫ ψ) =
      fromSingleEquivOfProjective n X M φ ≫ (homologyFunctor C n).map ψ := by
  simp

variable {X} in
/-- The identification `fromSingleEquivOfProjective` is natural in the projective object. -/
lemma fromSingleEquivOfProjective_singleFunctor_map_comp {X' : C} [Projective X'] (g : X' ⟶ X)
    {M : DerivedCategory C} (φ : (singleFunctor C n).obj X ⟶ M) :
    fromSingleEquivOfProjective n X' M ((singleFunctor C n).map g ≫ φ) =
      g ≫ fromSingleEquivOfProjective n X M φ := by
  simp only [fromSingleEquivOfProjective_apply, Functor.map_comp]
  exact ((singleFunctorCompHomologyFunctorIso C n).inv.naturality_assoc g _).symm

end DerivedCategory
