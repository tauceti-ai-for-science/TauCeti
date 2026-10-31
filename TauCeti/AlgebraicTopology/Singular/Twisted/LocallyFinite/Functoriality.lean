/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Basic
public import TauCeti.Topology.LocallyFinite
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# Functoriality of Borel–Moore homology with local coefficients

Locally finite singular chains, and hence Borel–Moore homology, are functorial in two ways.

* A morphism of local coefficient systems `η : L ⟶ K` acts on a locally finite chain coefficient
  by coefficient. This gives a chain map `locallyFiniteChainComplexCoefficientMap η`.
* A **proper** map `f : X ⟶ Y` pushes a locally finite chain of `X`, with coefficients in the
  pullback `f⁎L` of a system `L` on `Y`, forward to a locally finite chain of `Y`: the coefficient
  on a simplex `τ` of `Y` is the sum of the coefficients of the simplices `σ` of `X` with
  `f ∘ σ = τ`. Properness is what makes this sum finite (the preimage of the image of `τ` is
  compact) and the resulting chain locally finite (the image of a locally finite family under a
  proper map is locally finite). This gives a chain map `locallyFiniteChainComplexMap f L hf`.
  For a map which is not proper both statements fail; for instance, an infinite locally finite
  sum of points pushed forward to a point is not a chain.

Both constructions agree with the corresponding maps of finite twisted chains under the inclusion
`toLocallyFiniteChainComplex`, are compatible with identities and composition, and commute with
each other. Combined, a proper map `f` together with a morphism of coefficient systems
`η : L' ⟶ f⁎L` induces the map of Borel–Moore homology
`borelMooreHomologyCoefficientMap η k ≫ borelMooreHomologyMap f L hf k`.

## Main declarations

* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexCoefficientMap` and
  `borelMooreHomologyCoefficientMap`: change of coefficients.
* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexMap` and `borelMooreHomologyMap`: the
  pushforward along a proper map.
* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexMap_comp` and
  `locallyFiniteChainComplexMap_id`: functoriality of the pushforward.
* `TauCeti.LocalCoefficientSystem.locallyFiniteChainComplexMap_naturality`: naturality of the
  pushforward in the coefficient system.

## Implementation notes

All of these maps, and the boundary of locally finite chains itself, are instances of one
construction: the coefficientwise extension of a map of finite twisted chains which moves each
simplex only within its image under a fixed proper map. Extensions of such maps compose, so the
compatibilities reduce to the corresponding identities of finite twisted chains.

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory SimplexCategory

open scoped Simplicial

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y Z : TopCat.{v}}

section Extension

variable {L : LocalCoefficientSystem.{u, v, max v w} R X}
  {K : LocalCoefficientSystem.{u, v, max v w} R Y}
  {J : LocalCoefficientSystem.{u, v, max v w} R Z} {i j k : ℕ}

/-- The coefficientwise extension of a map of finite twisted chains to arbitrary families of
coefficients: the coefficient on `τ` is the sum, over all simplices `σ`, of the coefficient on `τ`
of the image of the chain supported on `σ`. -/
private def extendFun (T : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X j)
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ))
    (τ : (TopCat.toSSet.obj Y) _⦋j⦌) : K.obj (initialVertex τ) :=
  ∑ᶠ σ, (twistedChainComplexCoeff K τ).hom (T.hom ((ιTwistedChainComplex L k σ).hom (c σ)))

/-- A map of finite twisted chains is supported along `g` when the image of a chain supported on a
simplex `σ` only involves simplices whose image lies in the image of `σ` under `g`. -/
private def IsSupportedAlong (g : X → Y)
    (T : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X j) : Prop :=
  ∀ σ x τ, (twistedChainComplexCoeff K τ).hom (T.hom ((ιTwistedChainComplex L k σ).hom x)) ≠ 0 →
    Set.range (TopCat.simplexMap τ) ⊆ g '' Set.range (TopCat.simplexMap σ)

/-- Given a locally finite family of coefficients and a proper map `g`, only finitely many
simplices with nonzero coefficient have an image under `g` containing the image of a given
simplex. -/
private lemma finite_setOf_range_subset_image {g : X → Y} (hg : IsProperMap g)
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) (ρ : (TopCat.toSSet.obj Y) _⦋j⦌) :
    {σ | c σ ≠ 0 ∧
      Set.range (TopCat.simplexMap ρ) ⊆ g '' Set.range (TopCat.simplexMap σ)}.Finite :=
  have : CompactSpace (toTop.{v}.obj ⦋j⦌) :=
    (Homeomorph.ulift (X := Convexity.StdSimplex ℝ (Fin (j + 1)))).symm.compactSpace
  (hc.finite_setOf_inter_nonempty (hg.isCompact_preimage
    (isCompact_range (TopCat.simplexMap ρ).continuous))).subset fun σ ⟨hσ, hsub⟩ ↦ by
      obtain ⟨x, hx, hxρ⟩ := hsub ⟨toTopInitialVertex _, rfl⟩
      exact ⟨hσ, x, hx, _, hxρ.symm⟩

/-- The sums defining the extension of a supported map along a proper map are finite. -/
private lemma IsSupportedAlong.finite_support {g : X → Y}
    {T : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X j} (hT : IsSupportedAlong g T)
    (hg : IsProperMap g) {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) (τ : (TopCat.toSSet.obj Y) _⦋j⦌) :
    (Function.support fun σ ↦
      (twistedChainComplexCoeff K τ).hom (T.hom ((ιTwistedChainComplex L k σ).hom (c σ)))).Finite :=
  (finite_setOf_range_subset_image hg hc τ).subset fun σ hσ ↦
    ⟨fun h ↦ hσ (by simp [h]), hT σ (c σ) τ hσ⟩

/-- The extension of a supported map along a proper map preserves local finiteness. -/
private lemma IsSupportedAlong.isLocallyFiniteChain_extendFun {g : X → Y}
    {T : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X j} (hT : IsSupportedAlong g T)
    (hg : IsProperMap g) {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) : IsLocallyFiniteChain K (extendFun T c) := by
  rw [isLocallyFiniteChain_iff]
  intro y
  obtain ⟨V, hV, hfin⟩ := (isLocallyFiniteChain_iff_locallyFinite.1 hc).image_of_isProperMap hg y
  refine ⟨V, hV, (hfin.biUnion fun σ _ ↦ finite_setOf_twistedChainComplexCoeff_ne_zero K
    (T.hom ((ιTwistedChainComplex L k σ).hom (c σ)))).subset ?_⟩
  rintro τ ⟨hτ, z, hz, hzV⟩
  -- A simplex with nonzero coefficient comes from a simplex `σ` of the chain whose image under
  -- `g` meets `V`.
  obtain ⟨σ, hσ⟩ : ∃ σ, (twistedChainComplexCoeff K τ).hom
      (T.hom ((ιTwistedChainComplex L k σ).hom (c σ))) ≠ 0 := by
    by_contra! h
    exact hτ (finsum_eq_zero_of_forall_eq_zero h)
  obtain ⟨x, hx, rfl⟩ := hT σ (c σ) τ hσ hz
  exact Set.mem_biUnion (x := σ) ⟨g x, ⟨x, ⟨fun h ↦ hσ (by simp [h]), hx⟩, rfl⟩, hzV⟩ hσ

/-- Composites of supported maps are supported along the composite. -/
private lemma IsSupportedAlong.comp {g : X → Y} {g' : Y → Z}
    {S : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X j}
    {T : (twistedChainComplex K).X j ⟶ (twistedChainComplex J).X i}
    (hS : IsSupportedAlong g S) (hT : IsSupportedAlong g' T) :
    IsSupportedAlong (g' ∘ g) (S ≫ T) := fun σ x ρ h ↦ by
  have hfin := finite_setOf_twistedChainComplexCoeff_ne_zero K
    (S.hom ((ιTwistedChainComplex L k σ).hom x))
  have hsum := sum_ιTwistedChainComplex_twistedChainComplexCoeff K
    (S.hom ((ιTwistedChainComplex L k σ).hom x)) (s := hfin.toFinset)
    fun τ hτ ↦ (Set.Finite.mem_toFinset _).2 hτ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ← hsum, map_sum, map_sum] at h
  obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hy : (twistedChainComplexCoeff K τ).hom (S.hom ((ιTwistedChainComplex L k σ).hom x)) ≠ 0 :=
    fun h' ↦ hτ (by simp [h'])
  rw [Set.image_comp]
  exact (hT τ _ ρ hτ).trans (Set.image_mono (hS σ x τ hy))

/-- Extending supported maps along proper maps is compatible with composition. -/
private lemma extendFun_extendFun {g : X → Y} {g' : Y → Z}
    {S : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X j}
    {T : (twistedChainComplex K).X j ⟶ (twistedChainComplex J).X i}
    (hS : IsSupportedAlong g S) (hT : IsSupportedAlong g' T) (hg : IsProperMap g)
    (hg' : IsProperMap g') {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) : extendFun T (extendFun S c) = extendFun (S ≫ T) c := by
  funext ρ
  let a := fun τ σ ↦
    (twistedChainComplexCoeff K τ).hom (S.hom ((ιTwistedChainComplex L k σ).hom (c σ)))
  let G := fun τ ↦
    (twistedChainComplexCoeff J ρ).hom ∘ₗ T.hom ∘ₗ (ιTwistedChainComplex K j τ).hom
  have hF := finite_setOf_range_subset_image (hg'.comp hg) hc ρ
  have hST : ∀ σ, (twistedChainComplexCoeff J ρ).hom
      ((S ≫ T).hom ((ιTwistedChainComplex L k σ).hom (c σ))) ≠ 0 → σ ∈ hF.toFinset :=
    fun σ h ↦ (Set.Finite.mem_toFinset _).2 ⟨fun h' ↦ h (by simp [h']), (hS.comp hT) σ (c σ) ρ h⟩
  -- Every nonzero term involves a simplex `σ` of the chain whose image under `g' ∘ g` contains
  -- the image of `ρ`, so both iterated sums run over the finite set `hF.toFinset`.
  have hvanish : ∀ τ σ, G τ (a τ σ) ≠ 0 → σ ∈ hF.toFinset := fun τ σ h ↦ by
    have ha : a τ σ ≠ 0 := fun h' ↦ h (by rw [h', map_zero])
    refine (Set.Finite.mem_toFinset _).2 ⟨fun h' ↦ ha (by simp [a, h']), ?_⟩
    rw [Set.image_comp]
    exact (hT τ _ ρ h).trans (Set.image_mono (hS σ (c σ) τ ha))
  calc extendFun T (extendFun S c) ρ = ∑ᶠ τ, G τ (∑ᶠ σ, a τ σ) := (rfl)
    _ = ∑ᶠ τ, ∑ᶠ σ, G τ (a τ σ) :=
        finsum_congr fun τ ↦ map_finsum (G τ) (hS.finite_support hg hc τ)
    _ = ∑ᶠ τ, ∑ σ ∈ hF.toFinset, G τ (a τ σ) :=
        finsum_congr fun τ ↦ finsum_eq_sum_of_support_subset _ fun σ hσ ↦ hvanish τ σ hσ
    _ = ∑ σ ∈ hF.toFinset, ∑ᶠ τ, G τ (a τ σ) :=
        (sum_finsum_comm _ _ fun σ _ ↦ (finite_setOf_twistedChainComplexCoeff_ne_zero K
          (S.hom ((ιTwistedChainComplex L k σ).hom (c σ)))).subset fun τ hτ h ↦
            hτ (by simp [G, a, h])).symm
    _ = ∑ σ ∈ hF.toFinset, (twistedChainComplexCoeff J ρ).hom
          ((S ≫ T).hom ((ιTwistedChainComplex L k σ).hom (c σ))) :=
        Finset.sum_congr rfl fun σ _ ↦ finsum_ιTwistedChainComplex_twistedChainComplexCoeff K
          ((twistedChainComplexCoeff J ρ).hom ∘ₗ T.hom).toAddMonoidHom _
    _ = extendFun (S ≫ T) c ρ := (finsum_eq_sum_of_support_subset _ hST).symm

/-- Extending a map of finite chains on the coefficients of a finite chain gives the coefficients
of its image. -/
private lemma extendFun_twistedChainComplexCoeff
    (T : (twistedChainComplex L).X k ⟶ (twistedChainComplex K).X j)
    (y : (twistedChainComplex L).X k) :
    extendFun T (fun σ ↦ (twistedChainComplexCoeff L σ).hom y) =
      fun τ ↦ (twistedChainComplexCoeff K τ).hom (T.hom y) :=
  funext fun τ ↦ finsum_ιTwistedChainComplex_twistedChainComplexCoeff L
    ((twistedChainComplexCoeff K τ).hom ∘ₗ T.hom).toAddMonoidHom y

/-- The boundary of locally finite chains is the extension of the twisted boundary. -/
private lemma locallyFiniteBoundaryFun_eq_extendFun
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k + 1⦌, L.obj (initialVertex σ)) :
    locallyFiniteBoundaryFun L c = extendFun ((twistedChainComplex L).d (k + 1) k) c :=
  funext fun ρ ↦ locallyFiniteBoundaryFun_apply c ρ

/-- The twisted boundary is supported along the identity. -/
private lemma isSupportedAlong_d : IsSupportedAlong id ((twistedChainComplex L).d (k + 1) k) :=
  fun σ x τ h ↦ by
    by_contra hsub
    refine h ?_
    have hne : ∀ i : Fin (k + 2), (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ ≠ τ := by
      rintro i rfl
      exact hsub (by rw [Set.image_id]; exact TopCat.range_simplexMap_map_subset _ σ)
    have h0 := ιTwistedChainComplex_d_twistedChainComplexCoeff_of_forall_ne L hne
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using congrArg (fun φ ↦ φ.hom x) h0

end Extension

section Components

variable {L : LocalCoefficientSystem.{u, v, max v w} R X}
  {K : LocalCoefficientSystem.{u, v, max v w} R Y}
  {J : LocalCoefficientSystem.{u, v, max v w} R Z} {i j k : ℕ}

/-- The morphism between terms of locally finite chain complexes given by a linear map of locally
finite chains. -/
private def lfHom (φ : locallyFiniteChains L k →ₗ[R] locallyFiniteChains K j) :
    (locallyFiniteChainComplex L).X k ⟶ (locallyFiniteChainComplex K).X j :=
  eqToHom (locallyFiniteChainComplex_X L k) ≫ ModuleCat.ofHom φ ≫
    eqToHom (locallyFiniteChainComplex_X K j).symm

private lemma lfHom_comp (φ : locallyFiniteChains L k →ₗ[R] locallyFiniteChains K j)
    (ψ : locallyFiniteChains K j →ₗ[R] locallyFiniteChains J i) :
    lfHom φ ≫ lfHom ψ = lfHom (ψ ∘ₗ φ) := by
  simp [lfHom, ModuleCat.ofHom_comp]

private lemma lfHom_id :
    lfHom (LinearMap.id : locallyFiniteChains L k →ₗ[R] locallyFiniteChains L k) = 𝟙 _ := by
  simp [lfHom]

private lemma eqToHom_comp_lfHom (φ : locallyFiniteChains L k →ₗ[R] locallyFiniteChains K j) :
    eqToHom (locallyFiniteChainComplex_X L k).symm ≫ lfHom φ =
      ModuleCat.ofHom φ ≫ eqToHom (locallyFiniteChainComplex_X K j).symm := by
  simp [lfHom]

private lemma locallyFiniteChainComplex_d_eq_lfHom :
    (locallyFiniteChainComplex L).d (k + 1) k = lfHom (locallyFiniteBoundary L k) :=
  locallyFiniteChainComplex_d L k

end Components

section CoefficientMap

variable {L K J : LocalCoefficientSystem.{u, v, max v w} R X} {k : ℕ}

/-- Applying a morphism of local coefficient systems to every coefficient of a locally finite
chain gives a locally finite chain. -/
lemma IsLocallyFiniteChain.coefficientMap (η : L ⟶ K)
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain L c) :
    IsLocallyFiniteChain K fun σ ↦ (η.app (initialVertex σ)).hom (c σ) :=
  isLocallyFiniteChain_iff_locallyFinite.2 <|
    LocallyFinite.subset (isLocallyFiniteChain_iff_locallyFinite.1 hc) fun σ _ ⟨h, hx⟩ ↦
      ⟨fun h' ↦ h (by simp [h']), hx⟩

/-- The map of locally finite chains induced by a morphism of local coefficient systems, applying
the morphism to every coefficient. -/
def locallyFiniteChainsCoefficientMap (η : L ⟶ K) (k : ℕ) :
    locallyFiniteChains L k →ₗ[R] locallyFiniteChains K k where
  toFun c := ⟨fun σ ↦ (η.app (initialVertex σ)).hom
      ((c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)) σ),
    mem_locallyFiniteChains.2 ((mem_locallyFiniteChains.1 c.2).coefficientMap η)⟩
  map_add' _ _ := Subtype.ext <| funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := Subtype.ext <| funext fun _ ↦ map_smul _ _ _

/-- A morphism of coefficient systems acts on locally finite chains coefficient by
coefficient. -/
@[simp]
lemma coe_locallyFiniteChainsCoefficientMap (η : L ⟶ K) (c : locallyFiniteChains L k) :
    (locallyFiniteChainsCoefficientMap η k c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌,
      K.obj (initialVertex σ)) =
      fun σ ↦ (η.app (initialVertex σ)).hom
        ((c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)) σ) :=
  (rfl)

/-- Applying a morphism of coefficient systems coefficientwise is the extension of its action on
finite twisted chains. -/
private lemma extendFun_twistedChainComplexCoefficientMap (η : L ⟶ K)
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, L.obj (initialVertex σ)) :
    extendFun ((twistedChainComplexCoefficientMap η).f k) c =
      fun σ ↦ (η.app (initialVertex σ)).hom (c σ) := funext fun τ ↦ by
  rw [extendFun, finsum_eq_single _ τ fun σ hσ ↦ by
      rw [twistedChainComplexCoefficientMap_f_ι_apply,
        twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne _ hσ],
    twistedChainComplexCoefficientMap_f_ι_apply,
    twistedChainComplexCoeff_ιTwistedChainComplex_apply]

/-- A morphism of coefficient systems is supported along the identity. -/
private lemma isSupportedAlong_twistedChainComplexCoefficientMap (η : L ⟶ K) :
    IsSupportedAlong id ((twistedChainComplexCoefficientMap η).f k) := fun σ x τ h ↦ by
  rw [twistedChainComplexCoefficientMap_f_ι_apply] at h
  obtain rfl : σ = τ := by_contra fun hne ↦ h
    (twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne _ hne _)
  simp

/-- Change of coefficients commutes with the boundary of locally finite chains. -/
lemma locallyFiniteChainsCoefficientMap_comp_locallyFiniteBoundary (η : L ⟶ K) :
    locallyFiniteChainsCoefficientMap η k ∘ₗ locallyFiniteBoundary L k =
      locallyFiniteBoundary K k ∘ₗ locallyFiniteChainsCoefficientMap η (k + 1) := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  replace hc := mem_locallyFiniteChains.1 hc
  simp only [LinearMap.comp_apply, coe_locallyFiniteChainsCoefficientMap,
    coe_locallyFiniteBoundary]
  rw [← extendFun_twistedChainComplexCoefficientMap, ← extendFun_twistedChainComplexCoefficientMap,
    locallyFiniteBoundaryFun_eq_extendFun, locallyFiniteBoundaryFun_eq_extendFun,
    extendFun_extendFun isSupportedAlong_d (isSupportedAlong_twistedChainComplexCoefficientMap η)
      isProperMap_id isProperMap_id hc,
    extendFun_extendFun (isSupportedAlong_twistedChainComplexCoefficientMap η) isSupportedAlong_d
      isProperMap_id isProperMap_id hc, HomologicalComplex.Hom.comm]

/-- The identity morphism of a coefficient system induces the identity of locally finite
chains. -/
@[simp]
lemma locallyFiniteChainsCoefficientMap_id :
    locallyFiniteChainsCoefficientMap (𝟙 L) k = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

/-- A composite of morphisms of coefficient systems induces the composite of the induced maps of
locally finite chains. -/
@[simp]
lemma locallyFiniteChainsCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    locallyFiniteChainsCoefficientMap (η ≫ θ) k =
      locallyFiniteChainsCoefficientMap θ k ∘ₗ locallyFiniteChainsCoefficientMap η k :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

/-- The morphism of locally finite chain complexes induced by a morphism of local coefficient
systems. -/
def locallyFiniteChainComplexCoefficientMap (η : L ⟶ K) :
    locallyFiniteChainComplex L ⟶ locallyFiniteChainComplex K where
  f k := lfHom (locallyFiniteChainsCoefficientMap η k)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [locallyFiniteChainComplex_d_eq_lfHom, locallyFiniteChainComplex_d_eq_lfHom, lfHom_comp,
      lfHom_comp, locallyFiniteChainsCoefficientMap_comp_locallyFiniteBoundary]

/-- The components of the chain map induced by a change of coefficients are the coefficientwise
maps of locally finite chains. -/
lemma locallyFiniteChainComplexCoefficientMap_f (η : L ⟶ K) (k : ℕ) :
    (locallyFiniteChainComplexCoefficientMap η).f k =
      eqToHom (locallyFiniteChainComplex_X L k) ≫
        ModuleCat.ofHom (locallyFiniteChainsCoefficientMap η k) ≫
          eqToHom (locallyFiniteChainComplex_X K k).symm :=
  (rfl)

private lemma locallyFiniteChainComplexCoefficientMap_f_eq_lfHom (η : L ⟶ K) (k : ℕ) :
    (locallyFiniteChainComplexCoefficientMap η).f k =
      lfHom (locallyFiniteChainsCoefficientMap η k) :=
  (rfl)

/-- The identity morphism of a coefficient system induces the identity of locally finite chain
complexes. -/
@[simp]
lemma locallyFiniteChainComplexCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X) :
    locallyFiniteChainComplexCoefficientMap (𝟙 L) = 𝟙 _ := by
  ext k : 1
  rw [locallyFiniteChainComplexCoefficientMap_f_eq_lfHom, locallyFiniteChainsCoefficientMap_id,
    lfHom_id, HomologicalComplex.id_f]

/-- A composite of morphisms of coefficient systems induces the composite of the induced maps of
locally finite chain complexes. -/
@[simp, reassoc]
lemma locallyFiniteChainComplexCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) :
    locallyFiniteChainComplexCoefficientMap (η ≫ θ) =
      locallyFiniteChainComplexCoefficientMap η ≫ locallyFiniteChainComplexCoefficientMap θ := by
  ext k : 1
  rw [HomologicalComplex.comp_f, locallyFiniteChainComplexCoefficientMap_f_eq_lfHom,
    locallyFiniteChainComplexCoefficientMap_f_eq_lfHom,
    locallyFiniteChainComplexCoefficientMap_f_eq_lfHom, lfHom_comp,
    locallyFiniteChainsCoefficientMap_comp]

/-- In each degree, change of coefficients on locally finite chains extends change of
coefficients on finite twisted chains. -/
@[reassoc]
lemma twistedChainComplexCoefficientMap_f_comp_toLocallyFiniteChains (η : L ⟶ K) (k : ℕ) :
    (twistedChainComplexCoefficientMap η).f k ≫ toLocallyFiniteChains K k =
      toLocallyFiniteChains L k ≫ ModuleCat.ofHom (locallyFiniteChainsCoefficientMap η k) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ Subtype.ext (funext fun σ ↦ ?_))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    coe_locallyFiniteChainsCoefficientMap]
  refine (toLocallyFiniteChains_apply K _ σ).trans ?_
  rw [toLocallyFiniteChains_apply]
  exact congrFun ((extendFun_twistedChainComplexCoeff _ y).symm.trans
    (extendFun_twistedChainComplexCoefficientMap η _)) σ

/-- Change of coefficients on locally finite chains extends change of coefficients on finite
twisted chains. -/
@[reassoc]
lemma twistedChainComplexCoefficientMap_comp_toLocallyFiniteChainComplex (η : L ⟶ K) :
    twistedChainComplexCoefficientMap η ≫ toLocallyFiniteChainComplex K =
      toLocallyFiniteChainComplex L ≫ locallyFiniteChainComplexCoefficientMap η := by
  ext k : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, toLocallyFiniteChainComplex_f,
    toLocallyFiniteChainComplex_f, locallyFiniteChainComplexCoefficientMap_f_eq_lfHom,
    Category.assoc, eqToHom_comp_lfHom,
    twistedChainComplexCoefficientMap_f_comp_toLocallyFiniteChains_assoc]

/-- The map of Borel–Moore homology induced by a morphism of local coefficient systems. -/
abbrev borelMooreHomologyCoefficientMap (η : L ⟶ K) (k : ℕ) :
    borelMooreHomology L k ⟶ borelMooreHomology K k :=
  HomologicalComplex.homologyMap (locallyFiniteChainComplexCoefficientMap η) k

/-- The identity morphism of a coefficient system induces the identity of Borel–Moore
homology. -/
@[simp]
lemma borelMooreHomologyCoefficientMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (k : ℕ) : borelMooreHomologyCoefficientMap (𝟙 L) k = 𝟙 _ := by
  rw [borelMooreHomologyCoefficientMap, locallyFiniteChainComplexCoefficientMap_id,
    HomologicalComplex.homologyMap_id]

/-- A composite of morphisms of coefficient systems induces the composite of the induced maps of
Borel–Moore homology. -/
@[simp, reassoc]
lemma borelMooreHomologyCoefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (k : ℕ) :
    borelMooreHomologyCoefficientMap (η ≫ θ) k =
      borelMooreHomologyCoefficientMap η k ≫ borelMooreHomologyCoefficientMap θ k := by
  rw [borelMooreHomologyCoefficientMap, locallyFiniteChainComplexCoefficientMap_comp,
    HomologicalComplex.homologyMap_comp]

/-- Change of coefficients on Borel–Moore homology extends change of coefficients on twisted
singular homology. -/
@[reassoc]
lemma twistedHomologyCoefficientMap_comp_twistedHomologyToBorelMooreHomology (η : L ⟶ K)
    (k : ℕ) :
    twistedHomologyCoefficientMap η k ≫ twistedHomologyToBorelMooreHomology K k =
      twistedHomologyToBorelMooreHomology L k ≫ borelMooreHomologyCoefficientMap η k := by
  rw [twistedHomologyCoefficientMap, twistedHomologyToBorelMooreHomology,
    twistedHomologyToBorelMooreHomology, borelMooreHomologyCoefficientMap,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    twistedChainComplexCoefficientMap_comp_toLocallyFiniteChainComplex]

end CoefficientMap

section Map

variable (f : X ⟶ Y) (L : LocalCoefficientSystem.{u, v, max v w} R Y) {k : ℕ}

/-- The coefficients of the pushforward of a family of coefficients along a continuous map `f`:
the coefficient on a simplex `τ` of `Y` is the sum, over all simplices `σ` of `X`, of the
coefficient on `τ` of the image under `f` of the twisted chain supported on `σ`. Only the
simplices `σ` with `f ∘ σ = τ` contribute (`locallyFiniteMapFun_apply`). -/
def locallyFiniteMapFun
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, ((pullback f.hom).obj L).obj (initialVertex σ))
    (τ : (TopCat.toSSet.obj Y) _⦋k⦌) : L.obj (initialVertex τ) :=
  ∑ᶠ σ, (twistedChainComplexCoeff L τ).hom
    (((twistedChainComplexMap f L).f k).hom ((ιTwistedChainComplex _ k σ).hom (c σ)))

private lemma locallyFiniteMapFun_eq_extendFun
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, ((pullback f.hom).obj L).obj (initialVertex σ)) :
    locallyFiniteMapFun f L c = extendFun ((twistedChainComplexMap f L).f k) c :=
  (rfl)

/-- The pushforward coefficient on a simplex `τ` is the sum of the coefficients of the simplices
`σ` with `f ∘ σ = τ`, each placed on `f ∘ σ`. -/
lemma locallyFiniteMapFun_apply
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, ((pullback f.hom).obj L).obj (initialVertex σ))
    (τ : (TopCat.toSSet.obj Y) _⦋k⦌) :
    locallyFiniteMapFun f L c τ = ∑ᶠ σ, (twistedChainComplexCoeff L τ).hom
      ((ιTwistedChainComplex L k ((TopCat.toSSet.map f).app _ σ)).hom (c σ)) :=
  finsum_congr fun σ ↦ congrArg (twistedChainComplexCoeff L τ).hom
    (congrArg (fun φ ↦ φ.hom (c σ)) (ιTwistedChainComplex_twistedChainComplexMap_f f L k σ))

/-- A simplex of `Y` which is not the image of any simplex of `X` gets coefficient zero. -/
lemma locallyFiniteMapFun_apply_of_forall_ne
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, ((pullback f.hom).obj L).obj (initialVertex σ))
    {τ : (TopCat.toSSet.obj Y) _⦋k⦌} (hτ : ∀ σ, (TopCat.toSSet.map f).app _ σ ≠ τ) :
    locallyFiniteMapFun f L c τ = 0 := by
  rw [locallyFiniteMapFun_apply]
  exact finsum_eq_zero_of_forall_eq_zero fun σ ↦
    twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L (hτ σ) _

/-- Along an injective map, the pushforward coefficient on the image of a simplex is its
coefficient. -/
lemma locallyFiniteMapFun_apply_map (hf : Function.Injective f)
    (c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, ((pullback f.hom).obj L).obj (initialVertex σ))
    (σ : (TopCat.toSSet.obj X) _⦋k⦌) :
    locallyFiniteMapFun f L c ((TopCat.toSSet.map f).app _ σ) = c σ := by
  have hinj : Function.Injective ((TopCat.toSSet.map f).app (Opposite.op ⦋k⦌)) :=
    fun σ σ' h ↦ TopCat.simplexMap_injective <| ContinuousMap.ext fun p ↦ hf <| by
      simpa only [TopCat.simplexMap_app, ContinuousMap.comp_apply] using
        congrArg (fun s ↦ TopCat.simplexMap s p) h
  rw [locallyFiniteMapFun_apply]
  refine (finsum_eq_single _ σ fun σ' hσ' ↦
    twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L (hinj.ne hσ') _).trans ?_
  exact twistedChainComplexCoeff_ιTwistedChainComplex_apply L _ _

/-- A continuous map acts on finite twisted chains supported along itself. -/
private lemma isSupportedAlong_twistedChainComplexMap :
    IsSupportedAlong f ((twistedChainComplexMap f L).f k) := fun σ x τ h ↦ by
  have e := congrArg (fun φ ↦ φ.hom x) (ιTwistedChainComplex_twistedChainComplexMap_f f L k σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [e] at h
  obtain rfl : (TopCat.toSSet.map f).app _ σ = τ := by_contra fun hne ↦
    h (twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne _)
  rw [TopCat.simplexMap_app, ContinuousMap.coe_comp, Set.range_comp]

variable {f L} in
/-- The pushforward of a locally finite chain along a proper map is locally finite. -/
lemma IsLocallyFiniteChain.locallyFiniteMapFun (hf : IsProperMap f)
    {c : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌, ((pullback f.hom).obj L).obj (initialVertex σ)}
    (hc : IsLocallyFiniteChain _ c) : IsLocallyFiniteChain L (locallyFiniteMapFun f L c) :=
  (isSupportedAlong_twistedChainComplexMap f L).isLocallyFiniteChain_extendFun hf hc

/-- The pushforward of locally finite chains along a proper map `f`, from chains with
coefficients in the pullback `f⁎L` to chains with coefficients in `L`. -/
def locallyFiniteChainsMap (hf : IsProperMap f) (k : ℕ) :
    locallyFiniteChains ((pullback f.hom).obj L) k →ₗ[R] locallyFiniteChains L k where
  toFun c := ⟨locallyFiniteMapFun f L c,
    mem_locallyFiniteChains.2 ((mem_locallyFiniteChains.1 c.2).locallyFiniteMapFun hf)⟩
  map_add' c c' := Subtype.ext <| funext fun τ ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, locallyFiniteMapFun, map_add]
    exact finsum_add_distrib
      ((isSupportedAlong_twistedChainComplexMap f L).finite_support hf
        (mem_locallyFiniteChains.1 c.2) τ)
      ((isSupportedAlong_twistedChainComplexMap f L).finite_support hf
        (mem_locallyFiniteChains.1 c'.2) τ)
  map_smul' a c := Subtype.ext <| funext fun τ ↦ by
    simp only [SetLike.val_smul, Pi.smul_apply, locallyFiniteMapFun, map_smul, RingHom.id_apply]
    exact (smul_finsum' a ((isSupportedAlong_twistedChainComplexMap f L).finite_support hf
      (mem_locallyFiniteChains.1 c.2) τ)).symm

/-- The underlying coefficients of the pushforward of a locally finite chain. -/
-- Not `@[simp]`: the `simpNF` linter rejects it, since `LocalCoefficientSystem.pullback_obj_obj`
-- rewrites the coefficient type of the chain `c` on its left-hand side.
lemma coe_locallyFiniteChainsMap (hf : IsProperMap f)
    (c : locallyFiniteChains ((pullback f.hom).obj L) k) :
    (locallyFiniteChainsMap f L hf k c : ∀ τ : (TopCat.toSSet.obj Y) _⦋k⦌,
      L.obj (initialVertex τ)) = locallyFiniteMapFun f L c :=
  (rfl)

/-- The pushforward along a proper map commutes with the boundary of locally finite chains. -/
lemma locallyFiniteChainsMap_comp_locallyFiniteBoundary (hf : IsProperMap f) :
    locallyFiniteChainsMap f L hf k ∘ₗ locallyFiniteBoundary _ k =
      locallyFiniteBoundary L k ∘ₗ locallyFiniteChainsMap f L hf (k + 1) := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  replace hc := mem_locallyFiniteChains.1 hc
  simp only [LinearMap.comp_apply, coe_locallyFiniteChainsMap, coe_locallyFiniteBoundary]
  rw [locallyFiniteBoundaryFun_eq_extendFun, locallyFiniteMapFun_eq_extendFun,
    locallyFiniteMapFun_eq_extendFun, locallyFiniteBoundaryFun_eq_extendFun,
    extendFun_extendFun isSupportedAlong_d (isSupportedAlong_twistedChainComplexMap f L)
      isProperMap_id hf hc,
    extendFun_extendFun (isSupportedAlong_twistedChainComplexMap f _) isSupportedAlong_d
      hf isProperMap_id hc, HomologicalComplex.Hom.comm]

/-- The morphism of locally finite chain complexes induced by a proper map. -/
def locallyFiniteChainComplexMap (hf : IsProperMap f) :
    locallyFiniteChainComplex ((pullback f.hom).obj L) ⟶ locallyFiniteChainComplex L where
  f k := lfHom (locallyFiniteChainsMap f L hf k)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [locallyFiniteChainComplex_d_eq_lfHom, locallyFiniteChainComplex_d_eq_lfHom, lfHom_comp,
      lfHom_comp, locallyFiniteChainsMap_comp_locallyFiniteBoundary]

/-- The components of the chain map induced by a proper map are the pushforwards of locally
finite chains. -/
lemma locallyFiniteChainComplexMap_f (hf : IsProperMap f) (k : ℕ) :
    (locallyFiniteChainComplexMap f L hf).f k =
      eqToHom (locallyFiniteChainComplex_X _ k) ≫
        ModuleCat.ofHom (locallyFiniteChainsMap f L hf k) ≫
          eqToHom (locallyFiniteChainComplex_X L k).symm :=
  (rfl)

private lemma locallyFiniteChainComplexMap_f_eq_lfHom (hf : IsProperMap f) (k : ℕ) :
    (locallyFiniteChainComplexMap f L hf).f k = lfHom (locallyFiniteChainsMap f L hf k) :=
  (rfl)

/-- In each degree, the pushforward of locally finite chains along a proper map extends the
pushforward of finite twisted chains. -/
@[reassoc]
lemma twistedChainComplexMap_f_comp_toLocallyFiniteChains (hf : IsProperMap f) (k : ℕ) :
    (twistedChainComplexMap f L).f k ≫ toLocallyFiniteChains L k =
      toLocallyFiniteChains _ k ≫ ModuleCat.ofHom (locallyFiniteChainsMap f L hf k) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ Subtype.ext (funext fun τ ↦ ?_))
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    coe_locallyFiniteChainsMap]
  refine (toLocallyFiniteChains_apply L _ τ).trans ?_
  rw [show (((toLocallyFiniteChains _ k).hom y : ∀ σ : (TopCat.toSSet.obj X) _⦋k⦌,
      ((pullback f.hom).obj L).obj (initialVertex σ))) =
        fun σ ↦ (twistedChainComplexCoeff _ σ).hom y from
      funext (toLocallyFiniteChains_apply _ y), locallyFiniteMapFun_eq_extendFun,
    extendFun_twistedChainComplexCoeff]

/-- The pushforward of locally finite chains along a proper map extends the pushforward of finite
twisted chains. -/
@[reassoc]
lemma twistedChainComplexMap_comp_toLocallyFiniteChainComplex (hf : IsProperMap f) :
    twistedChainComplexMap f L ≫ toLocallyFiniteChainComplex L =
      toLocallyFiniteChainComplex _ ≫ locallyFiniteChainComplexMap f L hf := by
  ext k : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, toLocallyFiniteChainComplex_f,
    toLocallyFiniteChainComplex_f, locallyFiniteChainComplexMap_f_eq_lfHom, Category.assoc,
    eqToHom_comp_lfHom, twistedChainComplexMap_f_comp_toLocallyFiniteChains_assoc f L hf]

/-- The map of Borel–Moore homology induced by a proper map `f`, from the homology of `X` with
coefficients in the pullback `f⁎L` to the homology of `Y` with coefficients in `L`. -/
abbrev borelMooreHomologyMap (hf : IsProperMap f) (k : ℕ) :
    borelMooreHomology ((pullback f.hom).obj L) k ⟶ borelMooreHomology L k :=
  HomologicalComplex.homologyMap (locallyFiniteChainComplexMap f L hf) k

/-- The map of Borel–Moore homology induced by a proper map extends the map of twisted singular
homology. -/
@[reassoc]
lemma twistedHomologyMap_comp_twistedHomologyToBorelMooreHomology (hf : IsProperMap f) (k : ℕ) :
    twistedHomologyMap f L k ≫ twistedHomologyToBorelMooreHomology L k =
      twistedHomologyToBorelMooreHomology _ k ≫ borelMooreHomologyMap f L hf k := by
  rw [twistedHomologyMap, twistedHomologyToBorelMooreHomology, borelMooreHomologyMap,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    twistedChainComplexMap_comp_toLocallyFiniteChainComplex f L hf]

end Map

section MapFunctoriality

/-- In each degree, the pushforward along a composite of proper maps is the composite of the
pushforwards, after the identification of the pullback along the composite with the iterated
pullback. -/
lemma locallyFiniteChainsMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : LocalCoefficientSystem.{u, v, max v w} R Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfg : IsProperMap (f ≫ g)) (k : ℕ) :
    locallyFiniteChainsMap (f ≫ g) L hfg k =
      locallyFiniteChainsMap g L hg k ∘ₗ locallyFiniteChainsMap f ((pullback g.hom).obj L) hf k ∘ₗ
        locallyFiniteChainsCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) k := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  replace hc := mem_locallyFiniteChains.1 hc
  simp only [LinearMap.comp_apply, coe_locallyFiniteChainsMap,
    coe_locallyFiniteChainsCoefficientMap]
  rw [locallyFiniteMapFun_eq_extendFun, locallyFiniteMapFun_eq_extendFun,
    locallyFiniteMapFun_eq_extendFun, ← extendFun_twistedChainComplexCoefficientMap,
    extendFun_extendFun (isSupportedAlong_twistedChainComplexCoefficientMap _)
      (isSupportedAlong_twistedChainComplexMap f _) isProperMap_id hf hc,
    extendFun_extendFun ((isSupportedAlong_twistedChainComplexCoefficientMap _).comp
      (isSupportedAlong_twistedChainComplexMap f _)) (isSupportedAlong_twistedChainComplexMap g L)
      (hf.comp isProperMap_id) hg hc,
    twistedChainComplexMap_comp, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Category.assoc]

/-- In each degree, the pushforward along a proper map is natural in the coefficient system. -/
lemma locallyFiniteChainsMap_naturality (f : X ⟶ Y)
    {L K : LocalCoefficientSystem.{u, v, max v w} R Y} (η : L ⟶ K) (hf : IsProperMap f) (k : ℕ) :
    locallyFiniteChainsCoefficientMap η k ∘ₗ locallyFiniteChainsMap f L hf k =
      locallyFiniteChainsMap f K hf k ∘ₗ
        locallyFiniteChainsCoefficientMap ((pullback f.hom).map η) k := by
  refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
  replace hc := mem_locallyFiniteChains.1 hc
  simp only [LinearMap.comp_apply, coe_locallyFiniteChainsMap,
    coe_locallyFiniteChainsCoefficientMap]
  rw [locallyFiniteMapFun_eq_extendFun, locallyFiniteMapFun_eq_extendFun,
    ← extendFun_twistedChainComplexCoefficientMap, ← extendFun_twistedChainComplexCoefficientMap,
    extendFun_extendFun (isSupportedAlong_twistedChainComplexMap f L)
      (isSupportedAlong_twistedChainComplexCoefficientMap η) hf isProperMap_id hc,
    extendFun_extendFun (isSupportedAlong_twistedChainComplexCoefficientMap _)
      (isSupportedAlong_twistedChainComplexMap f K) isProperMap_id hf hc,
    ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, twistedChainComplexMap_naturality]

/-- The pushforward along the identity map is the change of coefficients along the
identification of a coefficient system with its pullback along the identity. -/
@[simp]
lemma locallyFiniteChainComplexMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hf : IsProperMap (𝟙 X)) :
    locallyFiniteChainComplexMap (𝟙 X) L hf =
      locallyFiniteChainComplexCoefficientMap ((pullbackIdIso X).hom.app L) := by
  ext k : 1
  rw [locallyFiniteChainComplexMap_f_eq_lfHom, locallyFiniteChainComplexCoefficientMap_f_eq_lfHom]
  refine congrArg lfHom (LinearMap.ext fun c ↦ Subtype.ext ?_)
  rw [coe_locallyFiniteChainsMap, coe_locallyFiniteChainsCoefficientMap,
    locallyFiniteMapFun_eq_extendFun, twistedChainComplexMap_id,
    extendFun_twistedChainComplexCoefficientMap]

/-- The pushforward along a composite of proper maps is the composite of the pushforwards, after
the identification of the pullback along the composite with the iterated pullback. -/
@[reassoc]
lemma locallyFiniteChainComplexMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : LocalCoefficientSystem.{u, v, max v w} R Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfg : IsProperMap (f ≫ g)) :
    locallyFiniteChainComplexMap (f ≫ g) L hfg =
      locallyFiniteChainComplexCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) ≫
        locallyFiniteChainComplexMap f ((pullback g.hom).obj L) hf ≫
          locallyFiniteChainComplexMap g L hg := by
  ext k : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, locallyFiniteChainComplexMap_f_eq_lfHom,
    locallyFiniteChainComplexMap_f_eq_lfHom, locallyFiniteChainComplexMap_f_eq_lfHom,
    locallyFiniteChainComplexCoefficientMap_f_eq_lfHom, lfHom_comp, lfHom_comp,
    locallyFiniteChainsMap_comp f g L hf hg hfg, LinearMap.comp_assoc]

/-- The pushforward along a proper map is natural in the coefficient system. -/
@[reassoc]
lemma locallyFiniteChainComplexMap_naturality (f : X ⟶ Y)
    {L K : LocalCoefficientSystem.{u, v, max v w} R Y} (η : L ⟶ K) (hf : IsProperMap f) :
    locallyFiniteChainComplexMap f L hf ≫ locallyFiniteChainComplexCoefficientMap η =
      locallyFiniteChainComplexCoefficientMap ((pullback f.hom).map η) ≫
        locallyFiniteChainComplexMap f K hf := by
  ext k : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, locallyFiniteChainComplexMap_f_eq_lfHom,
    locallyFiniteChainComplexMap_f_eq_lfHom, locallyFiniteChainComplexCoefficientMap_f_eq_lfHom,
    locallyFiniteChainComplexCoefficientMap_f_eq_lfHom, lfHom_comp, lfHom_comp,
    locallyFiniteChainsMap_naturality f η hf k]

/-- The homology form of `locallyFiniteChainComplexMap_id`. -/
@[simp]
lemma borelMooreHomologyMap_id (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (hf : IsProperMap (𝟙 X)) (k : ℕ) :
    borelMooreHomologyMap (𝟙 X) L hf k =
      borelMooreHomologyCoefficientMap ((pullbackIdIso X).hom.app L) k := by
  rw [borelMooreHomologyMap, locallyFiniteChainComplexMap_id]

/-- The homology form of `locallyFiniteChainComplexMap_comp`. -/
@[reassoc]
lemma borelMooreHomologyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : LocalCoefficientSystem.{u, v, max v w} R Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfg : IsProperMap (f ≫ g)) (k : ℕ) :
    borelMooreHomologyMap (f ≫ g) L hfg k =
      borelMooreHomologyCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) k ≫
        borelMooreHomologyMap f ((pullback g.hom).obj L) hf k ≫ borelMooreHomologyMap g L hg k := by
  rw [borelMooreHomologyMap, locallyFiniteChainComplexMap_comp f g L hf hg hfg,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]

/-- The homology form of `locallyFiniteChainComplexMap_naturality`. -/
@[reassoc]
lemma borelMooreHomologyMap_naturality (f : X ⟶ Y)
    {L K : LocalCoefficientSystem.{u, v, max v w} R Y} (η : L ⟶ K) (hf : IsProperMap f) (k : ℕ) :
    borelMooreHomologyMap f L hf k ≫ borelMooreHomologyCoefficientMap η k =
      borelMooreHomologyCoefficientMap ((pullback f.hom).map η) k ≫
        borelMooreHomologyMap f K hf k := by
  rw [borelMooreHomologyMap, borelMooreHomologyCoefficientMap, borelMooreHomologyMap,
    borelMooreHomologyCoefficientMap, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, locallyFiniteChainComplexMap_naturality f η hf]

end MapFunctoriality

end LocalCoefficientSystem

end TauCeti
