/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
public import TauCeti.Topology.Algebra.ProperAction.SliceMap
import TauCeti.Geometry.Lie.Subgroup.Stabilizer

/-!
# Slice charts of free proper actions

Let a Lie group `G` act smoothly and properly on a manifold `M`. This file builds the charts of the
orbit space `M ⧸ G` near the orbit of a point `x` with trivial stabilizer, and shows that their
transition maps are smooth. These are the local ingredients of the quotient manifold theorem for
free proper actions.

Let `σ : S → M` be a slice through `σ s₀ = x` whose slice map `(g, s) ↦ g • σ s` is a local
diffeomorphism at `(1, s₀)`; by `TauCeti.isLocalDiffeomorphAt_smul_slice_iff` this means that
the action is locally free at `x` and that `σ` is an immersion at `s₀` whose tangent image is a
complement of the orbit tangent space. Such slices exist at every locally free point
(`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`). Properness then lets us shrink the
slice to an open neighbourhood `U` of `s₀` on which the slice map is injective on all of `G × U`
and a local diffeomorphism at every point of `G × U`
(`IsLocalDiffeomorphAt.exists_isOpen_injOn_smul_slice`). So `U` meets every orbit at most once,
the slice map is an open embedding of `G × U` onto an invariant open neighbourhood of the orbit
of `x` (`TauCeti.MulAction.isOpenEmbedding_smul_slice`), and `s ↦ [σ s]` is an open embedding of
`U` into the orbit space (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`).

Given such a chart `s ↦ [τ s]` on `U`, the point of `U` on the orbit of `f z` depends smoothly on
`z` for every map `f` into `M` that is smooth at `z`
(`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`). Applied to the slice of a second chart,
this says that the transition maps between these charts are smooth.

For finite-dimensional `G` and `M`, the chart slice through a complement `W` of the orbit tangent
space `𝔤 · x` gives such a chart of `M ⧸ G` at the orbit of every point `x` with trivial
stabilizer, defined on an open neighbourhood of `0` in `W`, where
`dim W + dim G = dim M` (`TauCeti.exists_isOpenEmbedding_quotientMk_extChartAt_symm`).

Assembling these charts into a smooth manifold structure on `M ⧸ G` of dimension
`dim M - dim G`, with the orbit projection a submersion, is not done here.

## Main results

* `IsLocalDiffeomorphAt.exists_isOpen_injOn_smul_slice`: a transverse slice through a point with
  trivial stabilizer of a proper smooth action shrinks to an open slice meeting each orbit at
  most once, on which the slice map is a local diffeomorphism.
* `TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`: the slice coordinate of the orbit of a
  smoothly varying point varies smoothly.
* `TauCeti.exists_isOpenEmbedding_quotientMk_extChartAt_symm`: charts of the orbit space of a free
  proper action, modelled on a complement of the orbit tangent space.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, proof of Theorem 21.10
  (the quotient manifold theorem).
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003, proof of
  Theorem 1.21.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners 𝕜 F K}
  {S : Type*} [TopologicalSpace S] [ChartedSpace K S]
  {σ : S → M} {s₀ : S}

/-- **Slices of proper actions meet each orbit at most once after shrinking.** Let a Lie group act
smoothly and properly, let the stabilizer of `σ s₀` be trivial, and let the slice map
`(g, s) ↦ g • σ s` be a `C^n` local diffeomorphism at `(1, s₀)`. Then there is an open
neighbourhood `U` of `s₀` such that the slice map is injective on `G × U` and a `C^n` local
diffeomorphism at every point of `G × U`. -/
theorem _root_.IsLocalDiffeomorphAt.exists_isOpen_injOn_smul_slice {n : ℕ∞ω} [LieGroup I n G]
    [ContMDiffSMul I I' n G M] [ProperSMul G M] (hx : MulAction.stabilizer G (σ s₀) = ⊥)
    (h : IsLocalDiffeomorphAt (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (1, s₀)) :
    ∃ U : Set S, IsOpen U ∧ s₀ ∈ U ∧ InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  -- The slice `σ` is the restriction of the slice map to `{1} × S`, so it is continuous at `s₀`.
  have hσ : ContinuousAt σ s₀ := by
    have h1 : ContinuousAt (fun s : S ↦ (1 : G) • σ s) s₀ :=
      h.contMDiffAt.continuousAt.comp (x := s₀) (continuous_const.prodMk continuous_id).continuousAt
    simpa only [one_smul] using h1
  -- The slice map is injective near `(1, s₀)`, where its local inverse undoes it.
  obtain ⟨U₀, hU₀, hinj⟩ := ProperSMul.exists_mem_nhds_injOn_smul hσ hx
    (N := {p | (h.localInverse ∘ fun p : G × S ↦ p.1 • σ p.2) p = id p})
    h.localInverse_eventuallyEq_left fun p hp q hq hpq ↦
      hp.symm.trans ((congrArg h.localInverse hpq).trans hq)
  obtain ⟨U, hUsub, hU, hs₀⟩ :=
    mem_nhds_iff.1 (inter_mem hU₀ h.eventually_forall_smul_slice)
  exact ⟨U, hU, hs₀, hinj.mono (prod_mono_right fun s hs ↦ (hUsub hs).1),
    fun p ↦ (hUsub p.2.2).2 p.1.1⟩

/-- **Smooth transitions of slice charts.** Let the slice map `(g, s) ↦ g • τ s` be injective on
`G × U` and a `C^n` local diffeomorphism at every point of `G × U`, for an open set `U`, so that
`s ↦ [τ s]` is a chart of the orbit space. Let `f : P → M` be `C^n` at `z`, with `f z` in the orbit
of `τ s` for some `s ∈ U`. Then the point of `U` on the orbit of `f z'` depends smoothly on `z'`
near `z`: there is a map `t`, `C^n` at `z` with `t z = s`, such that for `z'` near `z` the points
`s' ∈ U` with `[τ s'] = [f z']` are exactly `t z'`. Applied to the slice of another chart, this is
the smoothness of the chart transitions of the orbit space. -/
theorem exists_contMDiffAt_quotientMk_slice_eq_iff {n : ℕ∞ω} {τ : S → M} {U : Set S} (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • τ p.2) (univ ×ˢ U))
    (hloc : IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • τ p.2) (univ ×ˢ U))
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    {K' : Type*} [TopologicalSpace K'] {L : ModelWithCorners 𝕜 F' K'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace K' P] {f : P → M} {z : P}
    (hf : ContMDiffAt L I' n f z) {s : S} (hs : s ∈ U)
    (hfs : Quotient.mk (MulAction.orbitRel G M) (τ s) = Quotient.mk _ (f z)) :
    ∃ t : P → S, ContMDiffAt L J n t z ∧ t z = s ∧ ∀ᶠ z' in 𝓝 z, t z' ∈ U ∧
      ∀ s' ∈ U, Quotient.mk (MulAction.orbitRel G M) (τ s') = Quotient.mk _ (f z') ↔ s' = t z' := by
  obtain ⟨g, hg⟩ :=
    MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hfs.symm))
  -- Invert the slice map near `(g, s)`, which it sends to `f z`.
  have hl := hloc ⟨(g, s), mem_univ _, hs⟩
  have hgs : (fun p : G × S ↦ p.1 • τ p.2) (g, s) = f z := hg
  have hq : ContMDiffAt L (I.prod J) n (hl.localInverse ∘ f) z :=
    hl.contMDiffAt_localInverse.comp_of_eq hf hgs.symm
  have hqz : (hl.localInverse ∘ f) z = (g, s) := by
    rw [comp_apply, ← hgs]
    exact hl.localInverse_left_inv hl.localInverse_mem_target
  refine ⟨fun z' ↦ (hl.localInverse (f z')).2, contMDiffAt_snd.comp z hq,
    congrArg Prod.snd hqz, ?_⟩
  have hmemU : ∀ᶠ z' in 𝓝 z, (hl.localInverse ∘ f) z' ∈ univ ×ˢ U :=
    hq.continuousAt.preimage_mem_nhds
      ((isOpen_univ.prod hU).mem_nhds (by rw [hqz]; exact ⟨mem_univ _, hs⟩))
  have hmemS : ∀ᶠ z' in 𝓝 z, f z' ∈ hl.localInverse.source :=
    hf.continuousAt.preimage_mem_nhds
      (hl.localInverse_open_source.mem_nhds (hgs ▸ hl.localInverse_mem_source))
  filter_upwards [hmemU, hmemS] with z' hzU hzS
  -- The local inverse writes `f z'` as `γ • τ (t z')` with `t z' ∈ U`.
  have hrel : (hl.localInverse (f z')).1 • τ (hl.localInverse (f z')).2 = f z' :=
    hl.localInverse_right_inv hzS
  refine ⟨hzU.2, fun s' hs' ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩⟩
  · obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact h'))
    -- `τ s'` and `τ (t z')` lie on one orbit, so injectivity on `G × U` identifies them.
    have h1 := hinj (x₁ := (k * (hl.localInverse (f z')).1, (hl.localInverse (f z')).2))
      (x₂ := (1, s')) ⟨mem_univ _, hzU.2⟩ ⟨mem_univ _, hs'⟩
      (by simp only [mul_smul, hrel, hk, one_smul])
    exact ((Prod.ext_iff.1 h1).2).symm
  · subst h'
    exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
      ⟨(hl.localInverse (f z')).1⁻¹, inv_smul_eq_iff.2 hrel.symm⟩))

end General

section Real

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [BoundarylessManifold I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M]

/-- **Charts of the orbit space of a free proper action.** Let a finite-dimensional Lie group act
smoothly and properly on a finite-dimensional boundaryless manifold `M`, and let `x` have trivial
stabilizer. Then there are a complement `W` of the orbit tangent space `𝔤 · x` in `T_x M`, so that
`dim W + dim 𝔤 = dim M`, and an open neighbourhood `U` of `0` in `W` such that, writing `φ` for the
extended chart at `x`, the map `w ↦ [φ⁻¹ (φ x + w)]` is an open embedding of `U` into the orbit
space `M ⧸ G`. Moreover the slice map `(g, w) ↦ g • φ⁻¹ (φ x + w)` is injective on `G × U` and a
smooth local diffeomorphism at every point of `G × U`. -/
theorem exists_isOpenEmbedding_quotientMk_extChartAt_symm {x : M}
    (hx : MulAction.stabilizer G x = ⊥) :
    ∃ (W : Submodule ℝ E') (U : Set W),
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) W ∧
      Module.finrank ℝ W + Module.finrank ℝ (GroupLieAlgebra I G) = Module.finrank ℝ E' ∧
      IsOpen U ∧ (0 : W) ∈ U ∧
      InjOn (fun p : G × W ↦ p.1 • (extChartAt I' x).symm (extChartAt I' x x + p.2))
        (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, W)) I' ∞
        (fun p : G × W ↦ p.1 • (extChartAt I' x).symm (extChartAt I' x x + p.2)) (univ ×ˢ U) ∧
      IsOpenEmbedding fun w : U ↦
        Quotient.mk (MulAction.orbitRel G M)
          ((extChartAt I' x).symm (extChartAt I' x x + ((w : W) : E'))) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace E' := FiniteDimensional.complete ℝ E'
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  -- A trivial stabilizer is discrete, so the action is locally free at `x`.
  have hiso : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
    have : Subsingleton (MulAction.stabilizer G x) := by
      rw [hx]
      infer_instance
    exact (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := I) (I' := I')).1
      inferInstance
  -- The tangent space `T_x M` is the model space `E'`, where the complement is taken.
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ E',
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) W :=
    Submodule.exists_isCompl _
  have hloc := isLocalDiffeomorphAt_smul_extChartAt_symm (G := G) hiso hW
  -- The chart slice passes through `x` at `0`.
  have hx0 : (extChartAt I' x).symm (extChartAt I' x x + ((0 : W) : E')) = x := by
    rw [Submodule.coe_zero, add_zero, extChartAt_to_inv]
  have hstab : MulAction.stabilizer G
      ((extChartAt I' x).symm (extChartAt I' x x + ((0 : W) : E'))) = ⊥ := by
    rwa [hx0]
  obtain ⟨U, hU, h0, hinj, hlocU⟩ := hloc.exists_isOpen_injOn_smul_slice
    (σ := fun w : W ↦ (extChartAt I' x).symm (extChartAt I' x x + w)) hstab
  refine ⟨W, U, hW, ?_, hU, h0, hinj, hlocU,
    MulAction.isOpenEmbedding_quotientMk_slice
      (σ := fun w : W ↦ (extChartAt I' x).symm (extChartAt I' x x + w)) hU hinj
      hlocU.isLocalHomeomorphOn⟩
  rw [← (InfinitesimalAction.fundamental I G I' M).finrank_orbitTangent_of_isotropy_eq_bot x hiso,
    add_comm]
  exact Submodule.finrank_add_eq_of_isCompl hW

end Real

end TauCeti
