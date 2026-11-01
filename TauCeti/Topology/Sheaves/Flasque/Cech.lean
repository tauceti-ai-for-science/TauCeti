/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech
public import TauCeti.Topology.Sheaves.Flasque.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.FullSubcategory
import TauCeti.Algebra.Homology.Functor.Resolution
import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
import TauCeti.Topology.Sheaves.Exact
import TauCeti.Topology.Sheaves.Flasque.Products

/-!
# Flasque sheaves are Čech acyclic for every open cover

Let `F` be a flasque sheaf of abelian groups on a topological space `X` and let `U i` be a family
of opens covering `X`, indexed by a type of any size. This file proves that the augmented Čech
complex `0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is exact
(`TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque`): `F` has no Čech cohomology for `U` in
positive degrees. For finite covers, and more generally for finite covers of an open `Y`, this is
also proved without derived functors in `TauCeti.Topology.Sheaves.Cech`; for infinite covers there
is no induction on the number of members, and the proof goes through sheaf cohomology instead.

The Čech complexes of the restrictions `F(Y ∩ -)` form a complex of sheaves
`Y ↦ Č(U, F(Y ∩ -))`, the sheafified Čech complex. In degree `k` it is the product, over the
tuples `a : Fin (k + 1) → ι`, of the sheaves `Y ↦ F(Y ∩ U (a 0) ∩ ⋯ ∩ U (a k))`
(`TopCat.Sheaf.isSheaf_prod_functor_flip_obj_op_comp`). These are flasque, and products of
flasque sheaves of abelian groups of any size are flasque
(`TopCat.Presheaf.isFlasque_piObj_of_hasExactLimitsOfShape`). On an open `Y` contained in a member
of the cover, the augmented complex `F(Y) ⟶ Č(U, F(Y ∩ -))` is exact
(`TauCeti.CategoryTheory.quasiIso_cechAugmentation_prod_of_hom`). Such opens form a basis of the
topology, so the sheafified Čech complex is a resolution of `F` by flasque sheaves
(`TopCat.Sheaf.exact_of_isBasis`). Since `F` and the terms of the resolution have no cohomology in
positive degrees, the complex of global sections of the resolution, which is `Č(U, F)`, is exact
in positive degrees (`CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution`). In degree `0`
this is the sheaf condition.

## Main results

* `TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque`: a flasque sheaf has an exact augmented
  Čech complex for every open cover of `X`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Lemma III.4.2 (the sheafified Čech
  complex is a resolution) and Proposition III.4.3, whose proof is followed here.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.CategoryTheory ZeroObject

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u})

/-! ### The Čech resolution of a sheaf -/

section Resolution

variable {ι : Type u} (U : ι → Opens X)

/-- The presheaf of complexes `Y ↦ Č(U, F(Y ∩ -))`. -/
private abbrev cechPresheaf : (Opens X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  prodRestriction F.presheaf ⋙ cechComplexFunctor U

/-- In each degree, `Y ↦ Čᵏ(U, F(Y ∩ -))` is a sheaf, as a product of sheaves `Y ↦ F(Y ∩ W)`. -/
private lemma isSheaf_cechPresheaf_X (k : ℕ) :
    Presheaf.IsSheaf (cechPresheaf F U ⋙ HomologicalComplex.eval _ _ k) :=
  Presheaf.isSheaf_of_iso (cechComplexProdRestrictionXIso F.presheaf U k).symm
    (TopCat.limit_isSheaf _ fun _ ↦ isSheaf_prod_functor_flip_obj_op_comp F _)

/-- The complex of presheaves `Y ↦ Č(U, F(Y ∩ -))`. -/
private abbrev cechResolutionPresheaf : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ where
  X k := cechPresheaf F U ⋙ HomologicalComplex.eval _ _ k
  d i j :=
    { app Y := ((cechPresheaf F U).obj Y).d i j
      naturality _ _ f := ((cechPresheaf F U).map f).comm i j }
  shape i j h := NatTrans.ext <| funext fun Y ↦ ((cechPresheaf F U).obj Y).shape i j h
  d_comp_d' i j k _ _ := NatTrans.ext <| funext fun Y ↦ ((cechPresheaf F U).obj Y).d_comp_d i j k

/-- The Čech resolution `Y ↦ Č(U, F(Y ∩ -))`, as a complex of sheaves. -/
private abbrev cechResolution :
    CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ :=
  (cechResolutionPresheaf F U).liftObjectProperty _ (isSheaf_cechPresheaf_X F U)

/-- The sheaf `Y ↦ F(Y ∩ X)`, isomorphic to `F`, which the Čech resolution resolves. -/
private def prodTop : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨prodRestriction F.presheaf ⋙ (evaluation _ _).obj (op ⊤),
    Presheaf.isSheaf_of_iso (prodRestrictionTerminalIso isTerminalTop F.presheaf).symm F.2⟩

/-- The augmentations of the complexes `Č(U, F(Y ∩ -))`. -/
private abbrev cechResolutionε :
    (prodTop F).obj ⋙ CochainComplex.single₀ AddCommGrpCat.{u} ⟶ cechPresheaf F U :=
  Functor.whiskerLeft (prodRestriction F.presheaf) (cechAugmentationNatTrans U isTerminalTop)

/-- The augmentation of the Čech resolution. -/
private def cechResolutionι : prodTop F ⟶ (cechResolution F U).X 0 :=
  ObjectProperty.homMk (cechResolutionε F U).augmentationι

private lemma cechResolutionι_comp_d : cechResolutionι F U ≫ (cechResolution F U).d 0 1 = 0 := by
  have h : (cechResolutionε F U).augmentationι ≫ (cechResolutionPresheaf F U).d 0 1 = 0 :=
    NatTrans.ext <| funext fun Y ↦ by
      simp only [NatTrans.comp_app, NatTrans.augmentationι_app, Category.assoc, NatTrans.app_zero]
      exact (congrArg _ (HomologicalComplex.single_f_d _ 1)).trans comp_zero
  exact (sheafToPresheaf _ _).map_injective h

variable {U}

/-- On an open contained in a member of the cover, the augmented complex
`F(Y) ⟶ Č(U, F(Y ∩ -))` is exact. -/
private lemma quasiIso_cechResolutionε_app {V : Opens X} (hV : ∃ i, V ≤ U i) :
    QuasiIso ((cechResolutionε F U).app (op V)) := by
  obtain ⟨_, hi⟩ := hV
  rw [Functor.whiskerLeft_app, cechAugmentationNatTrans_app]
  exact quasiIso_cechAugmentation_prod_of_hom U isTerminalTop F.presheaf V (homOfLE hi)

/-- The opens contained in some member of a cover of `X` form a basis. -/
private lemma isBasis_le (hU : ⨆ i, U i = ⊤) : Opens.IsBasis {V : Opens X | ∃ i, V ≤ U i} := by
  refine Opens.isBasis_iff_nbhd.2 fun {Y x} hx ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show x ∈ ⨆ i, U i by rw [hU]; trivial)
  exact ⟨Y ⊓ U i, ⟨i, inf_le_right⟩, ⟨hx, hi⟩, inf_le_left⟩

/-- In degree `0`, the sections of the Čech resolution over an open contained in a member of the
cover are the image of the augmentation, which is injective there. -/
private lemma exists_cechResolutionι_eq {V : Opens X} (hV : ∃ i, V ≤ U i) :
    Function.Injective ((cechResolutionι F U).hom.app (op V)) ∧
      ∀ s : ((cechPresheaf F U).obj (op V)).X 0, ((cechPresheaf F U).obj (op V)).d 0 1 s = 0 →
          ∃ t, (cechResolutionι F U).hom.app (op V) t = s := by
  have h := (cechResolutionε F U).shortExact_map_augmentationShortComplex
    ((quasiIso_cechResolutionε_app F hV).quasiIsoAt 0)
    ((quasiIso_cechResolutionε_app F hV).quasiIsoAt 1)
  rw [NatTrans.map_augmentationShortComplex] at h
  have hι : (cechResolutionι F U).hom.app (op V) =
      (HomologicalComplex.singleObjXSelf _ 0 _).inv ≫ ((cechResolutionε F U).app (op V)).f 0 :=
    NatTrans.augmentationι_app _ _
  refine ⟨hι ▸ (AddCommGrpCat.mono_iff_injective _).1 h.mono_f, fun s hs ↦ ?_⟩
  -- a cocycle has zero image in the cycles, as the inclusion of the cycles is injective
  have hc : ((cechPresheaf F U).obj (op V)).toCycles 0 1 s = 0 := by
    refine (AddCommGrpCat.mono_iff_injective (((cechPresheaf F U).obj (op V)).iCycles 1)).1
      inferInstance ?_
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, map_zero]
    exact hs
  exact hι ▸ (ShortComplex.ab_exact_iff _).1 h.exact s hc

/-- In positive degrees, the sections of the Čech resolution over an open contained in a member of
the cover form an exact complex. -/
private lemma exists_cechResolution_d_eq {V : Opens X} (hV : ∃ i, V ≤ U i) (j : ℕ)
    (s : ((cechPresheaf F U).obj (op V)).X (j + 1))
    (hs : ((cechPresheaf F U).obj (op V)).d (j + 1) (j + 2) s = 0) :
    ∃ t, ((cechPresheaf F U).obj (op V)).d j (j + 1) t = s := by
  have h := (quasiIsoAt_iff_exactAt _ (j + 1) (CochainComplex.exactAt_succ_single_obj _ j)).1
    ((quasiIso_cechResolutionε_app F hV).quasiIsoAt (j + 1))
  rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at h
  exact h s hs

variable [F.presheaf.IsFlasque]

private instance isFlasque_prodTop : Presheaf.IsFlasque (prodTop F).obj :=
  Presheaf.IsFlasque.of_iso (prodRestrictionTerminalIso isTerminalTop F.presheaf).symm

private instance isFlasque_cechResolution_X (k : ℕ) :
    Presheaf.IsFlasque ((cechResolution F U).X k).obj :=
  have := Presheaf.isFlasque_piObj_of_hasExactLimitsOfShape
    (fun b : Fin (k + 1) → ι ↦ (prod.functor.flip.obj (∏ᶜ fun j ↦ U (b j))).op ⋙ F.presheaf)
  Presheaf.IsFlasque.of_iso (cechComplexProdRestrictionXIso F.presheaf U k).symm

end Resolution

variable {ι : Type u} (U : ι → Opens X)

/-- **Flasque sheaves are acyclic for every open cover.** For a flasque sheaf `F` of abelian
groups on `X` and a family of opens `U i` covering `X`, indexed by a type of any size, the
augmented Čech complex `0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is exact: `F` has no Čech
cohomology for `U` in positive degrees, and its degree `0` Čech cohomology is `F(X)`. -/
theorem quasiIso_cechAugmentation_of_isFlasque [F.presheaf.IsFlasque] (hU : ⨆ i, U i = ⊤) :
    QuasiIso (cechAugmentation U isTerminalTop F.presheaf) := by
  have hB := isBasis_le hU
  -- the Čech resolution is a resolution of `F` by sheaves, exact on the basis of opens contained
  -- in members of the cover
  have hmono : Mono (cechResolutionι F U) :=
    (ShortComplex.exact_iff_mono (ShortComplex.mk (0 : 0 ⟶ prodTop F) _ zero_comp) rfl).1 <|
      exact_of_isBasis hB fun V hV s hs ↦ ⟨0, (map_zero _).trans
        ((exists_cechResolutionι_eq F hV).1 (hs.trans (map_zero _).symm)).symm⟩
  have hι' : (ShortComplex.mk _ _ (cechResolutionι_comp_d F U)).Exact :=
    exact_of_isBasis hB fun V hV ↦ (exists_cechResolutionι_eq F hV).2
  have hK (j : ℕ) : (cechResolution F U).ExactAt (j + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (by simp) (by simp)]
    exact exact_of_isBasis hB fun V hV ↦ exists_cechResolution_d_eq F hV j
  -- its terms and `F` are flasque, so its sections over `X` are exact in positive degrees
  have hX (n : ℕ) : ((cechPresheaf F U).obj (op ⊤)).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    exact CategoryTheory.Sheaf.H'.exists_d_hom_app_eq_of_resolution (cechResolutionι F U)
      (cechResolutionι_comp_d F U) hι' hK ⊤ (fun _ _ ↦ inferInstance) n inferInstance
  rw [quasiIso_cechAugmentation_iff]
  exact ⟨TauCeti.Topology.isSheafFor_ofArrows_of_iSup_eq_top U hU F, fun n ↦ (hX n).of_iso
    ((cechComplexFunctor U).mapIso
      (Functor.isoWhiskerRight (NatIso.op isTerminalTop.prodLeftUnitor) F.presheaf).symm)⟩

end TopCat.Sheaf
