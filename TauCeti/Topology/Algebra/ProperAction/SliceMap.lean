/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.IsLocalHomeomorph
import TauCeti.Topology.IsLocalHomeomorph

/-!
# Slice maps of proper actions

Let a group `G` act on a topological space `X`, and let `σ : S → X` be a map from a topological
space `S`, thought of as a slice through the point `σ s₀`. The **slice map**
`(g, s) ↦ g • σ s : G × S → X` sweeps the slice along the orbits of the action. This file proves
the topological half of the construction of quotient charts for free proper actions.

* Near a point `x` with trivial stabilizer, a proper action can only relate nearby points by group
  elements near `1`: if `u a → x`, `v a → x` and `f a • u a = v a`, then `f a → 1`
  (`ProperSMul.tendsto_nhds_one_of_smul_eq`).
* Hence, if the slice map of a proper action is injective near `(1, s₀)` and the stabilizer of
  `σ s₀` is trivial, then it is injective on all of `G × U` for some neighbourhood `U` of `s₀`
  (`ProperSMul.exists_mem_nhds_injOn_smul`): shrinking the slice, no orbit meets it twice.
* If the slice map is injective on `G × U` and a local homeomorphism there, for an open set `U`,
  then it is an open embedding of `G × U` onto an open invariant neighbourhood of the orbits
  through `σ '' U` (`TauCeti.MulAction.isOpenEmbedding_smul_slice`), and `s ↦ [σ s]` is an open
  embedding of `U` into the orbit space `X ⧸ G`
  (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`). These are the charts of the orbit
  space.

For a smooth action of a Lie group, the inverse function theorem supplies slices whose slice maps
are local diffeomorphisms near `(1, s₀)` at every point where the action is locally free; see
`TauCeti.Geometry.Manifold.GroupAction.SliceChart`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003, proof of
  Theorem 1.21.
-/

public section

open Filter Function Set Topology

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]

namespace ProperSMul

variable [ProperSMul G X]

/-- **Near a free point, a proper action relates nearby points only by elements near `1`.** Let
`x` have trivial stabilizer. If `u a` and `v a` both tend to `x` along a filter `l` and eventually
`f a • u a = v a`, then `f a` tends to `1`. -/
@[to_additive /-- **Near a free point, a proper additive action relates nearby points only by
elements near `0`.** Let `x` have trivial stabilizer. If `u a` and `v a` both tend to `x` along a
filter `l` and eventually `f a +ᵥ u a = v a`, then `f a` tends to `0`. -/]
theorem tendsto_nhds_one_of_smul_eq {α : Type*} {l : Filter α} {f : α → G} {u v : α → X} {x : X}
    (hx : MulAction.stabilizer G x = ⊥) (hu : Tendsto u l (𝓝 x)) (hv : Tendsto v l (𝓝 x))
    (h : ∀ᶠ a in l, f a • u a = v a) : Tendsto f l (𝓝 1) := by
  rw [tendsto_iff_ultrafilter]
  intro 𝒰 h𝒰
  -- Along `𝒰`, the pairs `(f a, u a)` are sent by `(g, y) ↦ (g • y, y)` to pairs tending to
  -- `(x, x)`, so properness makes `f a` converge to an element of the stabilizer of `x`.
  have hT : Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) (𝒰.map fun a ↦ (f a, u a))
      (𝓝 (x, x)) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    refine ((hv.mono_left h𝒰).prodMk_nhds (hu.mono_left h𝒰)).congr' ?_
    filter_upwards [h𝒰 h] with a ha
    simp [ha]
  obtain ⟨g, hg, hfst⟩ :=
    (properSMul_iff_continuousSMul_ultrafilter_tendsto.1 ‹_›).2 _ x x hT
  have hg1 : g = 1 := by
    have hmem : g ∈ MulAction.stabilizer G x := MulAction.mem_stabilizer_iff.2 hg
    rwa [hx, Subgroup.mem_bot] at hmem
  rw [Ultrafilter.coe_map, tendsto_map'_iff, hg1] at hfst
  exact hfst

/-- **Slice maps of proper actions are injective after shrinking the slice.** Let `σ : S → X` be
continuous at `s₀`, let the stabilizer of `σ s₀` be trivial, and let the slice map
`(g, s) ↦ g • σ s` be injective on a neighbourhood of `(1, s₀)`. Then it is injective on `G × U`
for some neighbourhood `U` of `s₀`: distinct points of `U` lie in distinct orbits, and the action
on the orbit through each point of `U` is free. -/
@[to_additive /-- **Slice maps of proper additive actions are injective after shrinking the
slice.** Let `σ : S → X` be continuous at `s₀`, let the stabilizer of `σ s₀` be trivial, and let
the slice map `(g, s) ↦ g +ᵥ σ s` be injective on a neighbourhood of `(0, s₀)`. Then it is
injective on `G × U` for some neighbourhood `U` of `s₀`. -/]
theorem exists_mem_nhds_injOn_smul {S : Type*} [TopologicalSpace S] {σ : S → X} {s₀ : S}
    (hσ : ContinuousAt σ s₀) (hx : MulAction.stabilizer G (σ s₀) = ⊥) {N : Set (G × S)}
    (hN : N ∈ 𝓝 ((1 : G), s₀)) (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) N) :
    ∃ U ∈ 𝓝 s₀, InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  obtain ⟨V, hV, U₀, hU₀, hVU⟩ := mem_nhds_prod_iff.1 hN
  -- Along pairs of points of the slice tending to `(s₀, s₀)`, any element relating their images
  -- tends to `1`, so it eventually lies in `V`.
  let l : Filter (G × S × S) :=
    comap (fun q ↦ q.2) (𝓝 (s₀, s₀)) ⊓ 𝓟 {q | q.1 • σ q.2.1 = σ q.2.2}
  have hpair : Tendsto (fun q : G × S × S ↦ q.2) l (𝓝 (s₀, s₀)) :=
    tendsto_comap.mono_left inf_le_left
  have hl : Tendsto (fun q : G × S × S ↦ q.1) l (𝓝 1) :=
    tendsto_nhds_one_of_smul_eq hx (hσ.tendsto.comp ((continuous_fst.tendsto (s₀, s₀)).comp hpair))
      (hσ.tendsto.comp ((continuous_snd.tendsto (s₀, s₀)).comp hpair))
      (mem_inf_of_right (mem_principal_self _))
  have hV' : ∀ᶠ q in l, q.1 ∈ V := hl hV
  rw [eventually_inf_principal, eventually_comap, nhds_prod_eq] at hV'
  obtain ⟨U₁, hU₁, hU₁V⟩ := eventually_prod_self_iff'.1 hV'
  refine ⟨U₀ ∩ U₁, inter_mem hU₀ hU₁, ?_⟩
  rintro ⟨g, s⟩ ⟨-, hs⟩ ⟨g', s'⟩ ⟨-, hs'⟩ heq
  simp only at heq
  -- `g'⁻¹ * g` relates `σ s` to `σ s'`, so it lies in `V`, where the slice map is injective.
  have hrel : (g'⁻¹ * g) • σ s = σ s' := by rw [mul_smul, heq, inv_smul_smul]
  have hmem : g'⁻¹ * g ∈ V := hU₁V s hs.2 s' hs'.2 (g'⁻¹ * g, s, s') rfl hrel
  have h1 := hinj (x₁ := (g'⁻¹ * g, s)) (x₂ := (1, s')) (hVU ⟨hmem, hs.1⟩)
    (hVU ⟨mem_of_mem_nhds hV, hs'.1⟩)
    (by simpa only [one_smul] using hrel)
  obtain ⟨hg, rfl⟩ := Prod.ext_iff.1 h1
  rw [inv_mul_eq_one] at hg
  rw [hg]

end ProperSMul

namespace TauCeti.MulAction

variable {S : Type*} [TopologicalSpace S] {σ : S → X} {U : Set S}

/-- **Slice maps parametrize open invariant neighbourhoods of orbits.** If the slice map
`(g, s) ↦ g • σ s` is injective on `G × U` and a local homeomorphism there, for an open set `U`,
then its restriction to `G × U` is an open embedding into `X`. -/
theorem isOpenEmbedding_smul_slice (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hloc : IsLocalHomeomorphOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    IsOpenEmbedding fun p : G × U ↦ p.1 • σ p.2 := by
  -- Identify `G × U` with the open subset `univ ×ˢ U` of `G × S`.
  let e : G × U ≃ₜ (univ ×ˢ U : Set (G × S)) := (Homeomorph.Set.univ G).symm.prodCongr
    (Homeomorph.refl U) |>.trans (Homeomorph.Set.prod univ U).symm
  have he : (fun p : G × U ↦ p.1 • σ p.2) =
      (univ ×ˢ U).domRestrict (fun p : G × S ↦ p.1 • σ p.2) ∘ e :=
    rfl
  rw [he]
  refine IsOpenEmbedding.comp ?_ e.isOpenEmbedding
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2
    ⟨hloc.continuousOn.domRestrict, hinj.injective, fun W hW ↦ ?_⟩
  -- An open subset of `univ ×ˢ U` is open in `G × S`, and the slice map is open there.
  obtain ⟨W', hW', rfl⟩ := hW
  rw [domRestrict_eq, image_comp, Subtype.image_preimage_coe]
  exact (hloc.mono inter_subset_left).isOpen_image ((isOpen_univ.prod hU).inter hW')

/-- **Quotient charts from slices.** If the slice map `(g, s) ↦ g • σ s` is injective on `G × U`
and a local homeomorphism there, for an open set `U`, then `s ↦ [σ s]` is an open embedding of `U`
into the orbit space `X ⧸ G`: distinct points of `U` lie in distinct orbits, and the orbits
through an open subset of `U` form an open subset of `X ⧸ G`. -/
theorem isOpenEmbedding_quotientMk_slice (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hloc : IsLocalHomeomorphOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    IsOpenEmbedding fun s : U ↦ Quotient.mk (MulAction.orbitRel G X) (σ s) := by
  -- On `U`, the slice `σ` is the restriction of the slice map to `{1} × U`.
  have hσ : ContinuousOn σ U := by
    have h1 : ContinuousOn (fun s : S ↦ (1 : G) • σ s) U :=
      hloc.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        fun s hs ↦ ⟨mem_univ _, hs⟩
    simpa only [one_smul] using h1
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, ?_, fun W hW ↦ ?_⟩
  · exact continuous_quot_mk.comp hσ.domRestrict
  · intro s s' hss'
    obtain ⟨g, hg⟩ := Quotient.exact hss'
    have h1 := hinj (x₁ := (g, s')) (x₂ := (1, s)) ⟨mem_univ _, s'.2⟩ ⟨mem_univ _, s.2⟩
      (by simpa only [one_smul] using hg)
    exact Subtype.ext (Prod.ext_iff.1 h1).2.symm
  · -- The orbits through the image of `W` pull back to the image of the open set `G × W` under
    -- the slice map.
    have hT : IsOpen (((↑) : U → S) '' W) := hU.isOpenMap_subtype_val W hW
    have hpre : Quotient.mk (MulAction.orbitRel G X) ⁻¹'
        ((fun s : U ↦ Quotient.mk (MulAction.orbitRel G X) (σ s)) '' W) =
        (fun p : G × S ↦ p.1 • σ p.2) '' (univ ×ˢ (((↑) : U → S) '' W)) := by
      ext y
      simp only [mem_preimage, mem_image, mem_prod, mem_univ, true_and, Prod.exists]
      constructor
      · rintro ⟨s, hs, hsy⟩
        obtain ⟨g, hg⟩ :=
          MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hsy))
        exact ⟨g⁻¹, s, ⟨s, hs, rfl⟩, by rw [← hg, inv_smul_smul]⟩
      · rintro ⟨g, _, ⟨s, hs, rfl⟩, rfl⟩
        refine ⟨s, hs, Quotient.sound ?_⟩
        exact MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g⁻¹, inv_smul_smul g _⟩)
    -- The quotient topology is coinduced; `hpre` computes the preimage.
    rw [isOpen_coinduced]
    convert (hloc.mono (prod_mono_right (Subtype.coe_image_subset U W))).isOpen_image
      (isOpen_univ.prod hT) using 1
    exact hpre

end TauCeti.MulAction
