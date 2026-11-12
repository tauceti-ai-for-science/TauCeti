/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.Geometry.Manifold.Boundary.Collar.Deformation

/-!
# The fundamental class of a compact manifold relative to a collared boundary

Let `X` be a compact space and `j : M → X` an open embedding of a topological `n`-manifold `M`
without boundary, oriented by `o`, whose complement `∂X = X ∖ j(M)` is collared: it is the zero
slice `range f` of an open embedding `c : N × [0, 1) → X` (`TauCeti.IsCollar f c`). This is how a
compact topological manifold with boundary, or with corners, sits around its interior. This file
constructs its fundamental class relative to the boundary, the class
`[X, ∂X] ∈ Hₙ(X, ∂X; ℤ)` of `TauCeti.HomologicalOrientation.relativeFundamentalClass`. It is
written as a class of the local homology `Hₙ(X, X ∖ j(M); ℤ)` along the interior.

The class is characterized by its local images: for every point `m` of `M`, the image of
`[X, ∂X]` in the local homology `Hₙ(X, X ∖ {j m}; ℤ)` is the local orientation `o m`, read in `X`
through the excision isomorphism `TauCeti.localHomologyIsoOfIsOpenEmbedding`
(`TauCeti.HomologicalOrientation.localHomologyRestriction_relativeFundamentalClass`), and it is the
only class with this property (`TauCeti.HomologicalOrientation.eq_relativeFundamentalClass`). In
particular it does not depend on the collar. Along every compact subset `K` of the interior it
restricts to the fundamental class `o.fundamentalClassOn` of `M` along `K`
(`TauCeti.HomologicalOrientation.localHomologyRestriction_relativeFundamentalClass_image`).

The construction removes an open collar. The inclusion of the boundary into the collar
neighbourhood `range c` is a homotopy equivalence, the collar deforming onto its zero slice
(`TauCeti.IsCollar.homotopyEquiv`), so by the five lemma removing the collar does not change the
relative homology: `Hₖ(X, ∂X) → Hₖ(X, range c)` is an isomorphism in every degree and for all
coefficients (`TauCeti.IsCollar.isIso_localHomologyRestriction`). The complement `K` of the open
collar is compact and lies in the interior, so by excision `Hₖ(X, range c)` is the local homology
`Hₖ(M, M ∖ K)` along `K`, where the fundamental class of `M` along `K` lives. Every point of the
interior lies in the complement of a thinner collar, which gives the local images at all points.

The relative fundamental class is the homological input of the fundamental chains rel boundary of
the compactified trajectory spaces in Morse and Floer theory: the representing chain systems of
Barraud and Cornea represent such classes (`TauCeti.TwistingChainSystem.IsRepresenting`).

## Main definitions

* `TauCeti.HomologicalOrientation.relativeFundamentalClass`: the fundamental class
  `[X, ∂X] ∈ Hₙ(X, X ∖ j(M); ℤ)`.

## Main results

* `TauCeti.IsCollar.isIso_localHomologyRestriction`: removing an open collar of the boundary does
  not change the homology relative to the boundary.
* `TauCeti.HomologicalOrientation.localHomologyRestriction_relativeFundamentalClass`,
  `TauCeti.HomologicalOrientation.eq_relativeFundamentalClass`: the characterization of the
  relative fundamental class.
* `TauCeti.HomologicalOrientation.relativeFundamentalClass_neg`: reversing the orientation negates
  it.
* `TauCeti.HomologicalOrientation.localHomologyRestriction_relativeFundamentalClass_image`: it
  restricts to the fundamental class of `M` along every compact subset of the interior.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the relative fundamental class of a compact manifold with boundary, constructed
  through a collar (proof of Theorem 3.43).
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, Appendix A.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology

universe w v u

namespace TauCeti

namespace IsCollar

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {X : Type w} [TopologicalSpace X] {N : Type*} [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

/-- **Removing an open collar does not change the homology relative to the boundary.** If the
complement of `S` is the boundary `range f`, collared by `c`, then the map
`Hₖ(X, X ∖ S) ⟶ Hₖ(X, range c)` induced by the identity of `X` is an isomorphism in every degree:
the inclusion of the boundary into the collar neighbourhood is a homotopy equivalence
(`TauCeti.IsCollar.homotopyEquiv`), and the five lemma applies. -/
theorem isIso_localHomologyRestriction (hc : IsCollar f c) {S : Set X} (hS : Sᶜ = range f)
    (k : ℕ) : IsIso (localHomologyRestriction R (hc.compl_range_subset hS) k) := by
  rw [localHomologyRestriction_def]
  set g := TopPair.ofSubsetMap (𝟙 (TopCat.of X)) (B := Sᶜ) (B' := (range c)ᶜᶜ)
    (compl_subset_compl.2 (hc.compl_range_subset hS))
  have hfst (m : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopPair.Hom.fst g)) R m) := by
    have hg : TopPair.Hom.fst g = 𝟙 (TopCat.of X) := TopPair.ofSubsetMap_fst _ _
    have : IsIso (TopPair.Hom.fst g) := by
      rw [hg]
      exact IsIso.id _
    infer_instance
  have hsnd (m : ℕ) : IsIso (SSet.homologyMap (TopCat.toSSet.map (TopPair.Hom.snd g)) R m) := by
    let e := hc.homotopyEquiv hS (compl_compl _)
    have he : TopCat.ofHom e.toFun = TopPair.Hom.snd g := by
      ext y
      exact (hc.coe_homotopyEquiv_apply hS (compl_compl _) y).trans
        (TopPair.ofSubsetMap_snd_apply (𝟙 (TopCat.of X)) (B := Sᶜ) (B' := (range c)ᶜᶜ)
          (compl_subset_compl.2 (hc.compl_range_subset hS)) y).symm
    rw [← he]
    have := (e.singularHomologyIso R m).isIso_hom
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom] at this
    exact this
  exact TopPair.isIso_singularHomologyMap_of_isIso R g k (hfst k) (hsnd k) (fun m _ ↦ hfst m)
    fun m _ ↦ hsnd m

end IsCollar

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n)
  {X : Type} [TopologicalSpace X] [T1Space X] [CompactSpace X] {j : M → X}
  (hj : IsOpenEmbedding j) {N : Type*} [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

omit [T2Space M] [CompactSpace X] in
/-- Restricting to a point and then reading the local homology at that point in `X` through
excision is restricting after the map of local homology induced by the open embedding `j`. -/
private theorem localHomologyIsoOfIsOpenEmbedding_hom_localHomologyRestriction {S : Set M}
    {T : Set X} (h : j ⁻¹' T ⊆ S) {m : M} (hm : m ∈ S) (hjm : j m ∈ T)
    (ν : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) S n) :
    (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom
        (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hm) n ν) =
      localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hjm) n
        (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ h n ν) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    localHomologyIsoOfIsOpenEmbedding_hom, localHomologyRestriction_comp_localHomologyMap,
    localHomologyMap_comp_localHomologyRestriction]

omit [CompactSpace X] in
include hj in
/-- A class of the local homology of `X` along a closed set `T` of the interior is the fundamental
class of `M` along `j ⁻¹' T`, read in `X`, as soon as it restricts to the local orientation at
every point of `T`. -/
private theorem eq_localHomologyMap_fundamentalClassOn {K : Set M} (hK : IsCompact K) {T : Set X}
    (hT : IsClosed T) (hTj : T ⊆ range j) (hKT : j ⁻¹' T = K)
    {ν : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) T n}
    (hν : ∀ m (hm : j m ∈ T), localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 hm) n ν =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom (o m).val) :
    ν = localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ hKT.subset n
      (o.fundamentalClassOn hn hK) := by
  have := isIso_localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ hj hKT hT hTj n
  obtain ⟨ν', rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ hKT.subset n)).2 ν
  congr 1
  refine o.eq_fundamentalClassOn hn hK fun x hx ↦ ?_
  have hx' : j x ∈ T := by
    rw [← hKT] at hx
    exact hx
  refine (ConcreteCategory.bijective_of_isIso
    (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj x n).hom).1 ?_
  rw [localHomologyIsoOfIsOpenEmbedding_hom_localHomologyRestriction hj hKT.subset hx hx',
    hν x hx']

omit [TopologicalSpace M] [T2Space M] [T1Space X] [CompactSpace X] in
/-- The complement of the collar neighbourhood lies in the interior. -/
private theorem compl_range_subset_range (hc : IsCollar f c) (hf : range f = (range j)ᶜ) :
    (range c)ᶜ ⊆ range j :=
  compl_subset_comm.2 (by rw [← hf]; exact hc.range_subset_range)

omit [T2Space M] [T1Space X] in
include hj in
/-- The points of `M` whose image lies outside the collar neighbourhood `range c` form a compact
set. -/
private theorem isCompact_preimage_compl_range (hc : IsCollar f c) (hf : range f = (range j)ᶜ) :
    IsCompact (j ⁻¹' (range c)ᶜ) :=
  hj.isInducing.isCompact_preimage' hc.isOpenEmbedding.isOpen_range.isClosed_compl.isCompact
    (compl_range_subset_range hc hf)

/-- The class of `Hₙ(X, X ∖ j(M); ℤ)` built from a collar `c`: the class whose image in
`Hₙ(X, range c; ℤ)` is the fundamental class of `M` along the complement of the collar. -/
private def classOfCollar (hc : IsCollar f c) (hf : range f = (range j)ᶜ) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range j) n :=
  have := hc.isIso_localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) hf.symm n
  inv (localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (hc.compl_range_subset hf.symm) n)
    (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩ subset_rfl n
      (o.fundamentalClassOn hn (isCompact_preimage_compl_range hj hc hf)))

/-- A class restricting to the local orientation at every point outside the collar neighbourhood
is the class built from the collar. -/
private theorem eq_classOfCollar (hc : IsCollar f c) (hf : range f = (range j)ᶜ)
    {μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range j) n}
    (hμ : ∀ m, j m ∈ (range c)ᶜ → localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 (mem_range_self m)) n μ =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom (o m).val) :
    μ = o.classOfCollar hn hj hc hf := by
  have := hc.isIso_localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) hf.symm n
  refine (ConcreteCategory.bijective_of_isIso (localHomologyRestriction
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (hc.compl_range_subset hf.symm) n)).1 ?_
  rw [classOfCollar, IsIso.inv_hom_id_apply]
  refine o.eq_localHomologyMap_fundamentalClassOn hn hj _
    hc.isOpenEmbedding.isOpen_range.isClosed_compl
    (compl_range_subset_range hc hf) rfl fun m hm ↦ ?_
  rw [localHomologyRestriction_comp_apply]
  exact hμ m hm

/-- The class built from a collar restricts to the local orientation at every point outside the
collar neighbourhood. -/
private theorem localHomologyRestriction_classOfCollar (hc : IsCollar f c)
    (hf : range f = (range j)ᶜ) {m : M} (hm : j m ∈ (range c)ᶜ) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 (mem_range_self m)) n (o.classOfCollar hn hj hc hf) =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom
          (o m).val := by
  have := hc.isIso_localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) hf.symm n
  have hK := isCompact_preimage_compl_range hj hc hf
  rw [← localHomologyRestriction_comp_apply (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 hm) (hc.compl_range_subset hf.symm), classOfCollar,
    IsIso.inv_hom_id_apply, ← o.localHomologyRestriction_fundamentalClassOn hn hK hm,
    localHomologyIsoOfIsOpenEmbedding_hom_localHomologyRestriction hj subset_rfl hm hm]

include hn hj in
/-- **Existence and uniqueness of the fundamental class relative to a collared boundary.** If the
complement of the image of the open embedding `j : M → X` of the oriented manifold `M` into the
compact space `X` is collared, then exactly one class of `Hₙ(X, X ∖ j(M); ℤ)` restricts at every
point `j m` to the local orientation `o m`, read in `X` through excision. -/
private theorem existsUnique_localHomologyRestriction_eq (hc : IsCollared f)
    (hf : range f = (range j)ᶜ) :
    ∃! μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range j) n,
      ∀ m, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 (mem_range_self m)) n μ =
          (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom
            (o m).val := by
  obtain ⟨c, hc⟩ := isCollared_iff.1 hc
  refine ⟨o.classOfCollar hn hj hc hf, fun m ↦ ?_, fun μ hμ ↦
    o.eq_classOfCollar hn hj hc hf fun m _ ↦ hμ m⟩
  obtain ⟨c', hc', hc'c, hm⟩ := hc.exists_isCollar_range_subset_notMem (x := j m)
    (by rw [hf]; exact not_notMem.2 (mem_range_self m))
  rw [← o.eq_classOfCollar hn hj hc hf (μ := o.classOfCollar hn hj hc' hf) fun x hx ↦
    o.localHomologyRestriction_classOfCollar hn hj hc' hf (compl_subset_compl.2 hc'c hx)]
  exact o.localHomologyRestriction_classOfCollar hn hj hc' hf hm

/-- **The fundamental class relative to a collared boundary** `[X, ∂X] ∈ Hₙ(X, X ∖ j(M); ℤ)`, for
an open embedding `j : M → X` of the oriented manifold `M` into a compact space `X` whose
complement `∂X = range f` is collared: the unique class restricting at every point `j m` to the
local orientation `o m`, read in `X` through excision. -/
def relativeFundamentalClass (hc : IsCollared f) (hf : range f = (range j)ᶜ) :
    localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range j) n :=
  (o.existsUnique_localHomologyRestriction_eq hn hj hc hf).exists.choose

/-- The relative fundamental class restricts at every point `j m` of the interior to the local
orientation `o m`, read in `X` through excision. -/
theorem localHomologyRestriction_relativeFundamentalClass (hc : IsCollared f)
    (hf : range f = (range j)ᶜ) (m : M) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 (mem_range_self m)) n (o.relativeFundamentalClass hn hj hc hf) =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom
          (o m).val :=
  (o.existsUnique_localHomologyRestriction_eq hn hj hc hf).exists.choose_spec m

/-- **Uniqueness of the relative fundamental class**: a class of `Hₙ(X, X ∖ j(M); ℤ)` restricting
at every point `j m` to the local orientation `o m` is the relative fundamental class. -/
theorem eq_relativeFundamentalClass (hc : IsCollared f) (hf : range f = (range j)ᶜ)
    {μ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) (range j) n}
    (hμ : ∀ m, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 (mem_range_self m)) n μ =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom
          (o m).val) :
    μ = o.relativeFundamentalClass hn hj hc hf :=
  (o.existsUnique_localHomologyRestriction_eq hn hj hc hf).unique hμ
    (o.localHomologyRestriction_relativeFundamentalClass hn hj hc hf)

/-- Reversing the orientation negates the relative fundamental class. -/
@[simp]
theorem relativeFundamentalClass_neg (hc : IsCollared f) (hf : range f = (range j)ᶜ) :
    (-o).relativeFundamentalClass hn hj hc hf = -o.relativeFundamentalClass hn hj hc hf := by
  refine ((-o).eq_relativeFundamentalClass hn hj hc hf fun m ↦ ?_).symm
  rw [map_neg, o.localHomologyRestriction_relativeFundamentalClass, neg_apply,
    LocalOrientation.coe_neg, map_neg]

/-- The relative fundamental class of a nonempty manifold is nonzero: its image at every point is
a local orientation, a generator of `Hₙ(X, X ∖ {j m}; ℤ) ≅ ℤ`. -/
theorem relativeFundamentalClass_ne_zero [Nonempty M] (hc : IsCollared f)
    (hf : range f = (range j)ᶜ) : o.relativeFundamentalClass hn hj hc hf ≠ 0 := by
  obtain ⟨m⟩ := ‹Nonempty M›
  intro h
  have h0 : (o m).val = 0 := by
    refine (ConcreteCategory.bijective_of_isIso
      (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ)) hj m n).hom).1 ?_
    rw [← o.localHomologyRestriction_relativeFundamentalClass hn hj hc hf m, h, map_zero,
      map_zero]
  subst hn
  let e := singularHomologyComplSingletonFinrankIso (ModuleCat.of ℤ (ULift.{0} ℤ)) (chartAt E m)
    (mem_chart_source E m)
  obtain ⟨a, ha⟩ := (isLocalOrientation_iff m _ _).1 (o m).2 (e.inv 1)
  rw [h0] at ha
  -- `a • 0 = e.inv 1`, so applying `e.hom` gives `0 = 1` in `ULift ℤ`.
  have h1 := congrArg e.hom ha
  simp at h1

/-- **The relative fundamental class restricts to the fundamental class along compact subsets of
the interior.** For a compact `K ⊆ M`, the image of `[X, ∂X]` in `Hₙ(X, X ∖ j(K); ℤ)` is the
fundamental class of `M` along `K`, read in `X` along `j`. -/
theorem localHomologyRestriction_relativeFundamentalClass_image [T2Space X] (hc : IsCollared f)
    (hf : range f = (range j)ᶜ) {K : Set M} (hK : IsCompact K) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (image_subset_range j K) n
      (o.relativeFundamentalClass hn hj hc hf) =
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟨j, hj.continuous⟩
          (hj.injective.preimage_image K).subset n (o.fundamentalClassOn hn hK) := by
  refine o.eq_localHomologyMap_fundamentalClassOn hn hj hK (hK.image hj.continuous).isClosed
    (image_subset_range j K) (hj.injective.preimage_image K) fun m hm ↦ ?_
  rw [localHomologyRestriction_comp_apply]
  exact o.localHomologyRestriction_relativeFundamentalClass hn hj hc hf m

end HomologicalOrientation

end TauCeti
