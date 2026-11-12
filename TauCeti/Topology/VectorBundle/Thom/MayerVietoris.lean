/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The Mayer–Vietoris step of the Thom isomorphism

Let `E → B` be a fibre bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section, and
let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The Thom
isomorphism theorem says that for a Thom class `u` of a real vector bundle of rank `n`, the Thom
map `Φ_u : Hᵖ(B; M) ⟶ Hᵖ⁺ⁿ(E, E₀; M)`, `a ↦ π^*a ⌣ u` (`TauCeti.thomMap`), is bijective in every
degree. Milnor and Stasheff (proof of Theorem 10.4) and Hatcher (proof of Theorem 4D.10) prove it
first over an open set of the base on which the bundle is trivial, and then pass from open sets
`U` and `V` to their union by comparing the Mayer–Vietoris sequences of the base and of the Thom
pairs with the five lemma. This file proves that comparison.

Over a subset `W` of the base, the restriction of the bundle has the Thom pair
`(E|_W, E₀|_W)` (`TauCeti.thomPairOver`) and the projection `E|_W ⟶ W`
(`TauCeti.thomPairOverProj`), and a class `u ∈ Hⁿ(E|_W, E₀|_W; K)` has the Thom map
`a ↦ π^*a ⌣ u` from `Hᵖ(W; M)` (`TauCeti.thomMapOver`). Restricting from `W'` to `W ⊆ W'`
commutes with these maps (`TauCeti.thomMapOver_naturality`), and so does restricting from the
whole Thom pair (`TauCeti.thomMapOver_singularCohomologyMap_subtypeVal`).

For open sets `U` and `V` covering the base, the Thom maps of the restrictions of `u` to `U`, `V`
and `U ∩ V` form a map from the Mayer–Vietoris sequence of the base to the Mayer–Vietoris
sequence of the Thom pairs over `U` and over `V`. The squares through restrictions commute by
naturality, and the square through the connecting morphisms commutes because the connecting
morphism of the Thom pairs is linear over the cohomology of the base, the cup product with a
relative class intertwining the two connecting morphisms
(`TopCat.singularCohomologyPairMayerVietorisδ_singularCup`), and because the connecting morphism of
the cover of the total space by the vectors over `U` and over `V` is the pull-back of that of the
base (`TopCat.singularCohomologyMayerVietorisδ_naturality`). The five lemma then gives the
**Mayer–Vietoris step** (`TauCeti.thomMap_bijective_of_thomMapOver_bijective`): if the Thom maps
over `U`, over `V` and over `U ∩ V` are bijective in every degree, then so is the Thom map of `u`.
In degree `0` the five lemma needs one term to the left of `Hⁿ(E, E₀)`, the cohomology
`Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V})`, to vanish; for a Thom class this is the vanishing of the relative
cohomology of a Thom pair below the rank
(`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`).

## Main definitions and results

* `TauCeti.thomPairOverProj`: the projection `E|_W ⟶ W`.
* `TauCeti.thomMapOver`: the Thom map `a ↦ π^*a ⌣ u` over a subset `W` of the base.
* `TauCeti.thomMapOver_naturality`, `TauCeti.thomMapOver_singularCohomologyMap_subtypeVal`: its
  naturality under restriction.
* `TauCeti.thomMap_bijective_of_thomMapOver_bijective`: the Mayer–Vietoris step of the Thom
  isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, proof of Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Set

universe w

namespace TauCeti

variable {B : Type w} (F : Type*) (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, Zero (E b)] {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

section Over

variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The projection `E|_W ⟶ W` of the restriction of a fibre bundle to a subset `W` of its base,
as a morphism of topological spaces out of the ambient space of the Thom pair over `W`: the
restriction of the bundle projection to the preimage of `W`. -/
def thomPairOverProj (W : Set B) : (thomPairOver F E W).fst ⟶ TopCat.of W :=
  TopCat.ofHom (ContinuousMap.restrictPreimage ⟨π F E, FiberBundle.continuous_proj F E⟩ W)

@[simp]
theorem thomPairOverProj_apply (W : Set B) (v : π F E ⁻¹' W) :
    thomPairOverProj F E W v = ⟨v.1.proj, v.2⟩ :=
  (rfl)

/-- For `W ⊆ W'`, the inclusion `E|_W ⟶ E|_{W'}` covers the inclusion `W ⟶ W'`. -/
@[reassoc]
theorem thomPairOverMap_fst_comp_thomPairOverProj {W W' : Set B} (hW : W ⊆ W') :
    TopPair.Hom.fst (thomPairOverMap F E hW) ≫ thomPairOverProj F E W' =
      thomPairOverProj F E W ≫ TopCat.ofHom (ContinuousMap.inclusion hW) := by
  ext v
  exact congrArg (fun x : π F E ⁻¹' W' ↦ x.1.proj) (thomPairOverMap_fst_apply F E hW v)

/-- The inclusion `E|_W ⟶ E` covers the inclusion `W ⟶ B`. -/
@[reassoc]
theorem thomPairOverMap_fst_comp_thomPairProj (W : Set B) :
    TopPair.Hom.fst (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) ≫
        thomPairProj F E =
      thomPairOverProj F E W ≫ TopCat.ofHom (ContinuousMap.subtypeVal W) := by
  ext v
  exact (thomPairProj_apply F E _).trans (congrArg TotalSpace.proj
    ((thomPairOverUnivIso_hom_fst_apply F E _).trans (congrArg Subtype.val
      (thomPairOverMap_fst_apply F E (subset_univ W) v))))

/-- **The Thom map over a subset `W` of the base**: for a relative class
`u ∈ Hⁿ(E|_W, E₀|_W; K)`, the map `a ↦ π^*a ⌣ u` from `Hᵖ(W; M)` to `Hᵐ(E|_W, E₀|_W; M)`,
`p + n = m`, as a `K`-bilinear map of `u` and `a`. It is the Thom map `TauCeti.thomMap` of the
restriction of the bundle to `W`, read on the Thom pair `(E|_W, E₀|_W)` inside the total space. -/
def thomMapOver (W : Set B) (n p m : ℕ) (h : p + n = m) :
    (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  ((thomPairOver F E W).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h ∘ₗ
    (TopCat.singularCohomologyMap (thomPairOverProj F E W) p).hom).flip

theorem thomMapOver_apply (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p) :
    thomMapOver F E M W n p m h u a =
      (thomPairOver F E W).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (thomPairOverProj F E W) p a) u :=
  (rfl)

/-- **Naturality of the Thom map over subsets of the base**: for `W ⊆ W'`, restricting the Thom map
of `u` over `W'` to `W` gives the Thom map over `W` of the restriction of `u`, applied to the
restriction of `a`. -/
theorem thomMapOver_naturality {W W' : Set B} (hW : W ⊆ W') {n p m : ℕ} (h : p + n = m)
    (u : (thomPairOver F E W').singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of W').singularCohomology (ModuleCat.of K K) K M p) :
    thomMapOver F E M W n p m h (TopPair.singularCohomologyMap (thomPairOverMap F E hW) n u)
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.inclusion hW)) p a) =
      TopPair.singularCohomologyMap (thomPairOverMap F E hW) m
        (thomMapOver F E M W' n p m h u a) := by
  rw [thomMapOver_apply, thomMapOver_apply, ← TopPair.singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    thomPairOverMap_fst_comp_thomPairOverProj]
  -- The two sides differ only in how the ambient space of the Thom pair over `W` is written.
  rfl

/-- **The Thom map restricted to a subset of the base**: restricting the Thom map of
`u ∈ Hⁿ(E, E₀; K)` to the Thom pair over `W` gives the Thom map over `W` of the restriction of `u`,
applied to the restriction of `a`. -/
theorem thomMapOver_singularCohomologyMap_subtypeVal (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMapOver F E M W n p m h
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) n u)
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal W)) p a) =
      TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) m
        (thomMap F E M n p m h u a) := by
  rw [thomMapOver_apply, thomMap_apply, ← TopPair.singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    thomPairOverMap_fst_comp_thomPairProj]
  -- The two sides differ only in how the ambient space of the Thom pair over `W` is written.
  rfl

end Over

section MayerVietoris

variable {U V : Set B}

variable (U V) in
/-- The inclusion of the union pair `(E|_U ∪ E|_V, E₀|_U ∪ E₀|_V)` of the Mayer–Vietoris sequence of
the Thom pairs over `U` and over `V` into the Thom pair `(E, E₀)`. -/
private abbrev unionToThomPair :
    TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
        (union_subset_union (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)) ⟶
      thomPair F E :=
  (thomPairOverUnionIso F E U V).hom ≫ thomPairOverMap F E (subset_univ _) ≫
    (thomPairOverUnivIso F E).hom

private theorem ofInclusionMap_comp_unionToThomPair_left :
    TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion subset_union_left)
        (fun _ hx ↦ subset_union_left hx) ≫ unionToThomPair F E U V =
      thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom := by
  rw [unionToThomPair, reassoc_of% ofInclusionMap_comp_thomPairOverUnionIso_hom_left,
    thomPairOverMap_comp_thomPairOverMap_assoc]

private theorem ofInclusionMap_comp_unionToThomPair_right :
    TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion subset_union_right)
        (fun _ hx ↦ subset_union_right hx) ≫ unionToThomPair F E U V =
      thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom := by
  rw [unionToThomPair, reassoc_of% ofInclusionMap_comp_thomPairOverUnionIso_hom_right,
    thomPairOverMap_comp_thomPairOverMap_assoc]

/-- The restriction from the intersection pair of the Mayer–Vietoris sequence to the pair over
`U`, written through the Thom pair over `U ∩ V`. -/
private theorem ofInclusionMap_inter_left_eq :
    TopPair.ofInclusionMap _ (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (ContinuousMap.inclusion inter_subset_left) (fun _ hx ↦ inter_subset_left hx) =
      (thomPairOverInterIso F E U V).inv ≫ thomPairOverMap F E inter_subset_left := by
  rw [Iso.eq_inv_comp, thomPairOverInterIso_hom_comp_ofInclusionMap_left]

/-- The restriction from the intersection pair of the Mayer–Vietoris sequence to the pair over
`V`, written through the Thom pair over `U ∩ V`. -/
private theorem ofInclusionMap_inter_right_eq :
    TopPair.ofInclusionMap _ (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
        (ContinuousMap.inclusion inter_subset_right) (fun _ hx ↦ inter_subset_right hx) =
      (thomPairOverInterIso F E U V).inv ≫ thomPairOverMap F E inter_subset_right := by
  rw [Iso.eq_inv_comp, thomPairOverInterIso_hom_comp_ofInclusionMap_right]

private theorem thomPairOverInterIso_inv_comp_thomPairOverMap :
    (thomPairOverInterIso F E U V).inv ≫ thomPairOverMap F E (subset_univ (U ∩ V)) ≫
        (thomPairOverUnivIso F E).hom =
      TopCat.interToUnionMap (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) ≫
        unionToThomPair F E U V := by
  have hCA : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U := inter_subset_left
  have hDB : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V := inter_subset_left
  have h : TopCat.interToUnionMap (X := TopCat.of (TotalSpace F E)) hCA hDB =
      TopPair.ofInclusionMap (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of (TotalSpace F E))
          (inter_subset_inter hCA hDB) hCA (ContinuousMap.inclusion inter_subset_left)
          (fun _ hx ↦ inter_subset_left hx) ≫
        TopPair.ofInclusionMap (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of (TotalSpace F E))
          hCA (union_subset_union hCA hDB) (ContinuousMap.inclusion subset_union_left)
          (fun _ hx ↦ subset_union_left hx) := by
    rw [← TopPair.ofInclusionMap_comp]
    -- The composite of two inclusions of subspaces is the inclusion, by definition.
    rfl
  rw [h, Category.assoc, ofInclusionMap_comp_unionToThomPair_left, ofInclusionMap_inter_left_eq,
    Category.assoc, thomPairOverMap_comp_thomPairOverMap_assoc]

/-- The union pair of the Mayer–Vietoris sequence includes into the Thom pair as a subspace. -/
private theorem unionToThomPair_fst :
    TopPair.Hom.fst (unionToThomPair F E U V) =
      TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' U ∪ π F E ⁻¹' V)) := by
  ext v
  -- `TopPair.Hom.fst` of a composite applies its components only up to unfolding.
  erw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, thomPairOverUnionIso_hom_fst_apply, thomPairOverMap_fst_apply,
    thomPairOverUnivIso_hom_fst_apply]
  rfl

variable {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)

/-- Restricting the restriction of `u` to `W'` further to `W ⊆ W'` gives its restriction to `W`. -/
private theorem singularCohomologyMap_thomPairOverMap_restrict {W W' : Set B} (hW : W ⊆ W') :
    TopPair.singularCohomologyMap (thomPairOverMap F E hW) n
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ W') ≫ (thomPairOverUnivIso F E).hom) n u) =
      TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) n u := by
  rw [← TopPair.singularCohomologyMap_comp_apply, thomPairOverMap_comp_thomPairOverMap_assoc]

/-- When `U ∪ V` is the whole base, the union pair of the Mayer–Vietoris sequence is the Thom pair,
so its inclusion induces bijections on cohomology. -/
private theorem bijective_singularCohomologyMap_unionToThomPair (hUV : U ∪ V = univ) (m : ℕ) :
    Function.Bijective (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := M)
      (unionToThomPair F E U V) m) := by
  have : IsIso (thomPairOverMap F E (subset_univ (U ∪ V))) := by
    have key : ∀ W : Set B, W = univ → IsIso (thomPairOverMap F E (subset_univ W)) := by
      rintro W rfl
      simp only [thomPairOverMap_self]
      infer_instance
    exact key _ hUV
  exact (ConcreteCategory.isIso_iff_bijective _).1
    ((TopPair.singularCohomologyFunctor _ K M m).map_isIso (unionToThomPair F E U V).op)

variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (U) in
/-- The bundle projection maps the vectors over `U` into `U`. -/
private theorem mapsTo_thomPairProj : MapsTo (thomPairProj F E) (π F E ⁻¹' U) U :=
  fun x hx ↦ by erw [thomPairProj_apply]; exact hx

/-- Over the intersection pair of the Mayer–Vietoris sequence, the projection to `U ∩ V` is the
restriction of the bundle projection. -/
private theorem thomPairOverInterIso_inv_fst_comp_thomPairOverProj :
    TopPair.Hom.fst (thomPairOverInterIso F E U V).inv ≫ thomPairOverProj F E (U ∩ V) =
      TopCat.ofHom ⟨((mapsTo_thomPairProj F E U).inter_inter
          (mapsTo_thomPairProj F E V)).restrict,
        (thomPairProj F E).hom.continuous.restrict _⟩ := by
  ext v
  -- The fibre component of the intersection pair is read off through the apply lemma.
  erw [ConcreteCategory.comp_apply, thomPairOverInterIso_inv_fst_apply]
  exact (thomPairProj_apply F E _).symm


/-- The Thom maps commute with the first maps of the two Mayer–Vietoris sequences, the
restrictions to `U` and to `V`. -/
private theorem thomMap_comp_singularCohomologyPairMayerVietorisToBiprod {p m : ℕ}
    (h : p + n = m) :
    ConcreteCategory.ofHom (C := ModuleCat K) (thomMap F E M n p m h u) ≫
        TopPair.singularCohomologyMap (unionToThomPair F E U V) m ≫
          TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
            (X := TopCat.of (TotalSpace F E))
            (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
            (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) m =
      TopCat.singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
          U V p ≫
        biprod.map
          (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M U n p m h
            (TopPair.singularCohomologyMap
              (thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom) n u)))
          (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M V n p m h
            (TopPair.singularCohomologyMap
              (thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom) n u))) := by
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, TopCat.singularCohomologyPairMayerVietorisToBiprod_fst,
      ← TopPair.singularCohomologyMap_comp, ofInclusionMap_comp_unionToThomPair_left,
      Category.assoc, biprod.map_fst, TopCat.singularCohomologyMayerVietorisToBiprod_fst_assoc]
    ext a
    exact (thomMapOver_singularCohomologyMap_subtypeVal F E M U h u a).symm
  · rw [Category.assoc, Category.assoc, TopCat.singularCohomologyPairMayerVietorisToBiprod_snd,
      ← TopPair.singularCohomologyMap_comp, ofInclusionMap_comp_unionToThomPair_right,
      Category.assoc, biprod.map_snd, TopCat.singularCohomologyMayerVietorisToBiprod_snd_assoc]
    ext a
    exact (thomMapOver_singularCohomologyMap_subtypeVal F E M V h u a).symm

/-- The Thom maps of the restrictions of `u` to `W ⊆ W'` commute with the restriction from `W'` to
`W`. -/
private theorem thomMapOver_comp_singularCohomologyMap_thomPairOverMap {W W' : Set B}
    (hW : W ⊆ W') {p m : ℕ} (h : p + n = m) :
    ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M W' n p m h
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ W') ≫ (thomPairOverUnivIso F E).hom) n u)) ≫
        TopPair.singularCohomologyMap (thomPairOverMap F E hW) m =
      TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.inclusion hW)) p ≫
        ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M W n p m h
          (TopPair.singularCohomologyMap
            (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) n u)) := by
  ext a
  exact (thomMapOver_naturality F E M hW h _ a).symm.trans (by
    rw [singularCohomologyMap_thomPairOverMap_restrict]; rfl)

/-- The Thom maps commute with the second maps of the two Mayer–Vietoris sequences, the
differences of the restrictions to `U ∩ V`. -/
private theorem singularCohomologyPairMayerVietorisFromBiprod_thomMapOver {p m : ℕ}
    (h : p + n = m) :
    biprod.map
          (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M U n p m h
            (TopPair.singularCohomologyMap
              (thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom) n u)))
          (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M V n p m h
            (TopPair.singularCohomologyMap
              (thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom) n u))) ≫
        TopCat.singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) m =
      TopCat.singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
          U V p ≫
        ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M (U ∩ V) n p m h
          (TopPair.singularCohomologyMap
            (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u)) ≫
          TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m := by
  apply biprod.hom_ext'
  · rw [biprod.inl_map_assoc, TopCat.inl_singularCohomologyPairMayerVietorisFromBiprod,
      ← Category.assoc biprod.inl, TopCat.inl_singularCohomologyMayerVietorisFromBiprod
        (ModuleCat.of K K) K M (X := TopCat.of B) U V p,
      ofInclusionMap_inter_left_eq,
      TopPair.singularCohomologyMap_comp (thomPairOverInterIso F E U V).inv, ← Category.assoc,
      thomMapOver_comp_singularCohomologyMap_thomPairOverMap, Category.assoc]
  · rw [biprod.inr_map_assoc, TopCat.inr_singularCohomologyPairMayerVietorisFromBiprod,
      ← Category.assoc biprod.inr, TopCat.inr_singularCohomologyMayerVietorisFromBiprod
        (ModuleCat.of K K) K M (X := TopCat.of B) U V p,
      ofInclusionMap_inter_right_eq,
      TopPair.singularCohomologyMap_comp (thomPairOverInterIso F E U V).inv, Preadditive.comp_neg,
      Preadditive.neg_comp, ← Category.assoc,
      thomMapOver_comp_singularCohomologyMap_thomPairOverMap, Category.assoc]

variable (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)

/-- The Thom maps commute with the connecting morphisms of the two Mayer–Vietoris sequences: the
connecting morphism of the Thom pairs, applied to `π^*a ⌣ u|_{U ∩ V}`, is `π^*(δ a) ⌣ u`. -/
private theorem thomMapOver_comp_singularCohomologyPairMayerVietorisδ {p p' m m' : ℕ}
    (h : p + n = m) (h' : p' + n = m') (hp : p + 1 = p') (hm : m + 1 = m') :
    (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M (U ∩ V) n p m h
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u)) ≫
        TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m) ≫
      TopCat.singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
          (isOpen_thomPairOver_mayerVietoris hU hV).1 (isOpen_thomPairOver_mayerVietoris hU hV).2.1
          (isOpen_thomPairOver_mayerVietoris hU hV).2.2.1
          (isOpen_thomPairOver_mayerVietoris hU hV).2.2.2 m m' hm =
      TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M (X := TopCat.of B) hU hV hUV
          p p' hp ≫
        ConcreteCategory.ofHom (C := ModuleCat K) (thomMap F E M n p' m' h' u) ≫
          TopPair.singularCohomologyMap (unionToThomPair F E U V) m' := by
  have hUV' : π F E ⁻¹' U ∪ π F E ⁻¹' V = univ := by rw [← preimage_union, hUV, preimage_univ]
  have hπU := (hU.preimage (FiberBundle.continuous_proj F E) : IsOpen (π F E ⁻¹' U))
  have hπV := (hV.preimage (FiberBundle.continuous_proj F E) : IsOpen (π F E ⁻¹' V))
  ext a
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom]
  -- The left side is the connecting morphism of the Thom pairs applied to a cup product on the
  -- intersection pair, of the pull-back of `a` to the total space with the restriction of the
  -- class `u` from the union pair.
  have hcup : TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m
      (thomMapOver F E M (U ∩ V) n p m h (TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u) a) =
      (TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) (inter_subset_inter
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))).singularCup K
        (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom ⟨((mapsTo_thomPairProj F E U).inter_inter
          (mapsTo_thomPairProj F E V)).restrict,
          (thomPairProj F E).hom.continuous.restrict _⟩) p a)
        (TopPair.singularCohomologyMap (TopCat.interToUnionMap (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)) n
          (TopPair.singularCohomologyMap (unionToThomPair F E U V) n u)) := by
    rw [thomMapOver_apply, ← TopPair.singularCup_naturality, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, thomPairOverInterIso_inv_fst_comp_thomPairOverProj,
      ← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      thomPairOverInterIso_inv_comp_thomPairOverMap, TopPair.singularCohomologyMap_comp_apply]
    rfl
  rw [hcup]
  erw [TopCat.singularCohomologyPairMayerVietorisδ_singularCup K hπU hπV hUV' _ _ _ _ _ _
    h hp hm h']
  -- The connecting morphism of the cover of the total space by the vectors over `U` and over `V`
  -- is the pull-back of that of the cover of the base.
  have hnat := ConcreteCategory.congr_hom
    (TopCat.singularCohomologyMayerVietorisδ_naturality (ModuleCat.of K K) K M hπU hπV hUV' hU hV
      hUV (thomPairProj F E) (mapsTo_thomPairProj F E U) (mapsTo_thomPairProj F E V) p p' hp) a
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [thomMap_apply, ← TopPair.singularCup_naturality, unionToThomPair_fst]
  erw [← hnat]
  rfl

/-- The intersection pair of the Mayer–Vietoris sequence is the Thom pair over `U ∩ V`, so the Thom
map over `U ∩ V`, read on the intersection pair, is bijective if it is. -/
private theorem bijective_thomMapOver_inter {p m : ℕ} (h : p + n = m)
    (hΦ : Function.Bijective (thomMapOver F E M (U ∩ V) n p m h (TopPair.singularCohomologyMap
      (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u))) :
    Function.Bijective (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M (U ∩ V) n p m h
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u)) ≫
        TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m) := by
  rw [ConcreteCategory.coe_comp]
  have := (TopPair.singularCohomologyFunctor (ModuleCat.of K K) K M m).map_isIso
    (thomPairOverInterIso F E U V).inv.op
  exact ((ConcreteCategory.isIso_iff_bijective _).1 this).comp hΦ

/-- The Thom maps over `U` and over `V` together, on the middle terms of the Mayer–Vietoris
sequences, are bijective if both are. -/
private theorem bijective_biprod_map_thomMapOver {p m : ℕ} (h : p + n = m)
    (hΦU : Function.Bijective (thomMapOver F E M U n p m h (TopPair.singularCohomologyMap
      (thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hΦV : Function.Bijective (thomMapOver F E M V n p m h (TopPair.singularCohomologyMap
      (thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom) n u))) :
    Function.Bijective (biprod.map
      (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M U n p m h
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom) n u)))
      (ConcreteCategory.ofHom (C := ModuleCat K) (thomMapOver F E M V n p m h
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom) n u)))) := by
  have := (ConcreteCategory.isIso_iff_bijective (C := ModuleCat K) (ConcreteCategory.ofHom
    (thomMapOver F E M U n p m h _))).2 hΦU
  have := (ConcreteCategory.isIso_iff_bijective (C := ModuleCat K) (ConcreteCategory.ofHom
    (thomMapOver F E M V n p m h _))).2 hΦV
  exact (ConcreteCategory.isIso_iff_bijective _).1 (biprod.mapIso (asIso _) (asIso _)).isIso_hom

include hU hV in
/-- The first map of the Mayer–Vietoris sequence of the Thom pairs, from `Hⁿ(E, E₀)` read on the
union pair, is injective when the cohomology of the Thom pair over `U ∩ V` vanishes in degree
`n - 1` (or `n = 0`). -/
private theorem injective_singularCohomologyPairMayerVietorisToBiprod
    (hUV₀ : ∀ q, q + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).singularCohomology (ModuleCat.of K K) K M q)) :
    Function.Injective (TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n) := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  refine (ModuleCat.mono_iff_injective _).1 ?_
  obtain rfl | ⟨q, rfl⟩ : n = 0 ∨ ∃ q, n = q + 1 := by rcases n with _ | q <;> simp
  · exact TopCat.mono_singularCohomologyPairMayerVietorisToBiprod_zero _ K M _ _ hA hB hC hD
  · refine (TopCat.singularCohomologyPairMayerVietoris_exact₁ _ K M _ _ hA hB hC hD q
      (q + 1)).mono_g (IsZero.eq_of_src ?_ _ _)
    exact (hUV₀ q rfl).of_iso ((TopPair.singularCohomologyFunctor _ K M q).mapIso
      (thomPairOverInterIso F E U V).op)

include hU hV hUV in
/-- **The Mayer–Vietoris step in degree `0`**: the four lemma applied to the start of the two
Mayer–Vietoris sequences. -/
private theorem bijective_thomMap_comp_unionToThomPair_zero (h : 0 + n = n)
    (hΦU : Function.Bijective (thomMapOver F E M U n 0 n h (TopPair.singularCohomologyMap
      (thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hΦV : Function.Bijective (thomMapOver F E M V n 0 n h (TopPair.singularCohomologyMap
      (thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hΦUV : Function.Bijective (thomMapOver F E M (U ∩ V) n 0 n h (TopPair.singularCohomologyMap
      (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hUV₀ : ∀ q, q + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).singularCohomology (ModuleCat.of K K) K M q)) :
    Function.Bijective (ConcreteCategory.ofHom (C := ModuleCat K) (thomMap F E M n 0 n h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) n) := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (TopCat.singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
      U V 0).hom
    (TopCat.singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
      U V 0).hom
    (TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n).hom
    (TopCat.singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) n).hom
    _ _ _
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, Category.assoc,
      thomMap_comp_singularCohomologyPairMayerVietorisToBiprod])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
      singularCohomologyPairMayerVietorisFromBiprod_thomMapOver])
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyMayerVietoris_exact₂ _ K M hU hV hUV 0))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyPairMayerVietoris_exact₂ _ K M _ _ hA hB hC hD n))
    (bijective_biprod_map_thomMapOver F E M u h hΦU hΦV)
    (bijective_thomMapOver_inter F E M u h hΦUV).1
    ((ModuleCat.mono_iff_injective _).1
      (TopCat.mono_singularCohomologyMayerVietorisToBiprod_zero _ K M hU hV hUV))
    (injective_singularCohomologyPairMayerVietorisToBiprod F E M hU hV hUV₀)

include hU hV hUV in
/-- **The Mayer–Vietoris step in positive degree**: the five lemma applied to the two Mayer–Vietoris
sequences around `Hᵠ⁺¹(B)` and `Hᵐ⁺¹(E, E₀)`. -/
private theorem bijective_thomMap_comp_unionToThomPair_succ {q m : ℕ} (hq : q + n = m)
    (hq' : q + 1 + n = m + 1)
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u))) :
    Function.Bijective (ConcreteCategory.ofHom (C := ModuleCat K) (thomMap F E M n (q + 1) (m + 1)
      hq' u) ≫ TopPair.singularCohomologyMap (unionToThomPair F E U V) (m + 1)) := by
  obtain ⟨hA, hB, hC, hD⟩ := isOpen_thomPairOver_mayerVietoris (F := F) (E := E) hU hV
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (TopCat.singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
      U V q).hom
    (TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M (X := TopCat.of B) hU hV hUV
      q (q + 1)).hom
    (TopCat.singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
      U V (q + 1)).hom
    (TopCat.singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
      U V (q + 1)).hom
    (TopCat.singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) m).hom
    (TopCat.singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) hA hB hC hD
      m (m + 1)).hom
    (TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) (m + 1)).hom
    (TopCat.singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
      (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) (m + 1)).hom
    _ _ _ _ _
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
      singularCohomologyPairMayerVietorisFromBiprod_thomMapOver])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
      thomMapOver_comp_singularCohomologyPairMayerVietorisδ F E M u hU hV hUV hq hq' rfl rfl])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, Category.assoc,
      thomMap_comp_singularCohomologyPairMayerVietorisToBiprod])
    (by rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
      singularCohomologyPairMayerVietorisFromBiprod_thomMapOver])
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyMayerVietoris_exact₃ _ K M hU hV hUV q (q + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyMayerVietoris_exact₁ _ K M hU hV hUV q (q + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyMayerVietoris_exact₂ _ K M hU hV hUV (q + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyPairMayerVietoris_exact₃ _ K M _ _ hA hB hC hD m (m + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyPairMayerVietoris_exact₁ _ K M _ _ hA hB hC hD m (m + 1)))
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (TopCat.singularCohomologyPairMayerVietoris_exact₂ _ K M _ _ hA hB hC hD (m + 1)))
    (bijective_biprod_map_thomMapOver F E M u hq (hΦU _ _ hq) (hΦV _ _ hq)).2
    (bijective_thomMapOver_inter F E M u hq (hΦUV _ _ hq))
    (bijective_biprod_map_thomMapOver F E M u hq' (hΦU _ _ hq') (hΦV _ _ hq'))
    (bijective_thomMapOver_inter F E M u hq' (hΦUV _ _ hq')).1

include hU hV hUV in
/-- **The Mayer–Vietoris step of the Thom isomorphism.** Let `U` and `V` be open sets covering the
base, and let `u ∈ Hⁿ(E, E₀; K)`. Suppose that the Thom maps `a ↦ π^*a ⌣ u` of the restrictions of
`u` to the Thom pairs over `U`, over `V` and over `U ∩ V` are bijective in every degree, and that
`Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V}; M) = 0` if `n ≥ 1`. Then the Thom map
`Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)` of `u` is bijective for every `p + n = m`.

The vanishing hypothesis holds for a Thom class, whose degree is the rank of the bundle, whenever
`U ∩ V` is a finite union of trivializing open sets
(`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`): the relative cohomology of a Thom pair
vanishes below the rank. -/
theorem thomMap_bijective_of_thomMapOver_bijective
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ U) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ V) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ (U ∩ V)) ≫ (thomPairOverUnivIso F E).hom) n u)))
    (hUV₀ : ∀ q, q + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).singularCohomology (ModuleCat.of K K) K M q))
    {p m : ℕ} (h : p + n = m) :
    Function.Bijective (thomMap F E M n p m h u) := by
  -- It suffices to read the Thom map on the union pair of the Mayer–Vietoris sequence of the Thom
  -- pairs over `U` and over `V`, which is the Thom pair since `U ∪ V` is the whole base.
  suffices hι : Function.Bijective (ConcreteCategory.ofHom (C := ModuleCat K)
      (thomMap F E M n p m h u) ≫ TopPair.singularCohomologyMap (unionToThomPair F E U V) m) by
    rw [ConcreteCategory.coe_comp] at hι
    exact (Function.Bijective.of_comp_iff'
      (bijective_singularCohomologyMap_unionToThomPair F E M hUV m) _).1 hι
  obtain _ | q := p
  · obtain rfl : m = n := by omega
    exact bijective_thomMap_comp_unionToThomPair_zero F E M u hU hV hUV h (hΦU _ _ h) (hΦV _ _ h)
      (hΦUV _ _ h) hUV₀
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact bijective_thomMap_comp_unionToThomPair_succ F E M u hU hV hUV (by omega) h hΦU hΦV hΦUV

end MayerVietoris

end TauCeti
