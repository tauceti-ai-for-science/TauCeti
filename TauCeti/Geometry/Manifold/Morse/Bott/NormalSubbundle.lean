/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Splitting
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.Morse.Bott.Index
import TauCeti.Geometry.Manifold.Morse.Bott.NegativeNormal
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.LinearAlgebra.Projection.Intertwiner
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The negative and positive normal bundles of a Morse–Bott submanifold

Let `i : S → M` be a nondegenerate critical submanifold of a function `f` on a boundaryless
manifold, and let `g` be a `C^k` fibre metric on its normal bundle `ν`. At each point `s` the
normal space splits into the negative normal space `ν⁻ s`, spanned by the normal vectors `v` with
`Hess v = μ g v` for some `μ < 0`, and the positive normal space `ν⁺ s`, defined with `μ > 0`
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.negativeNormalSpace` and
`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.positiveNormalSpace`). Their dimensions are the
Morse indices of `f` and of `-f` at `i s`.

This file shows that, when `f` is `C^{k+2}` along `S`, the embedding is `C^{k+1}` and these
indices are constant, the spaces `ν⁻ s` and `ν⁺ s` have `C^k` local frames near every point of `S`
(`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_negativeNormalSpace` and
`IsNondegenerateCriticalSubmanifold.hasLocalContMDiffSubbundleFrames_positiveNormalSpace`, in the
namespace `TauCeti.SmoothEmbedding`). By the smooth local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle` they are therefore `C^k`
subbundles of the normal bundle, the **negative and positive normal bundles** `ν⁻` and `ν⁺`; the
rank of `ν⁻` is the index of the submanifold. The indices are locally constant along a Morse–Bott
submanifold, so on a connected one the hypothesis holds automatically (the `_of_preconnectedSpace`
versions). The negative normal bundle is the bundle whose disc bundle is attached when the
critical level of the submanifold is crossed.

The subbundles depend on the metric `g`, but their ranks do not. No eigenbasis of the normal
Hessian is chosen. In the preferred normal-bundle trivialization at `s₀`, with fibre model `P`, the
metric becomes a `C^k` family `G` of bilinear forms on `P`
(`Bundle.Trivialization.contMDiffOn_compl₁₂_symmₗ`). The projections onto the negative relative
spectral subspaces of the normal Hessian with respect to `G`, along the positive ones, are then a
`C^k` family of operators on `P` whose ranges and kernels read the negative and positive normal
spaces in the trivialization
(`IsNondegenerateCriticalSubmanifold.exists_contMDiffOn_negativeNormalProjection`), and a `C^k`
family of operators of constant rank has `C^k` local frames of its ranges
(`Bundle.Trivialization.exists_isSubbundleFrameOn_map_symmₗ`).

Up to isomorphism the subbundles do not depend on the metric either. For two `C^k` fibre metrics
`g₀` and `g₁`, the negative normal space for `g₀` and the positive normal space for `g₁` are
complementary, since the normal Hessian is negative definite on the first and positive definite on
the second. So for the projections `π₀` and `π₁` onto the negative normal spaces along the
positive ones, the intertwining operators `π₁ π₀ + (1 - π₁) (1 - π₀)` form a `C^k` family of linear
automorphisms of the normal spaces carrying `ν⁻(g₀)` onto `ν⁻(g₁)` and `ν⁺(g₀)` onto `ν⁺(g₁)`
(`LinearMap.IsIdempotentElem.bijective_mul_add_one_sub_mul_one_sub`;
`exists_contMDiff_map_negativeNormalSpace_eq_and_map_positiveNormalSpace_eq`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`). In the trivialization they read
`p₁ p₀ + (1 - p₁) (1 - p₀)` for the two families of projections `p₀` and `p₁` of `P`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5.
-/

public section

open Bundle Function Set Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {k : ℕ∞ω} [IsManifold I (k + 2) M] [IsManifold J (k + 1) S]

/-- In the preferred normal-bundle trivialization at `s₀`, the negative and positive normal
spaces relative to a `C^k` fibre metric are the images of the range and of the kernel of a `C^k`
family of projections of the fibre model. -/
private theorem exists_contMDiffOn_negativeNormalSpace_eq_map
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    let e := trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
    ∃ p : S → P →L[ℝ] P, ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k p e.baseSet ∧
      ∀ s ∈ e.baseSet, IsIdempotentElem (p s) ∧
        h.negativeNormalSpace hn g.toRiemannianMetric s = (p s).range.map (e.symmₗ ℝ s) ∧
        h.positiveNormalSpace hn g.toRiemannianMetric s = (p s).ker.map (e.symmₗ ℝ s) ∧
        finrank ℝ (p s).range = manifoldMorseIndex I f (i s) ∧
        finrank ℝ (p s).ker = manifoldMorseIndex I (-f) (i s) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  set e := trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
  -- The metric read in the trivialization.
  set G : S → P →L[ℝ] P →L[ℝ] ℝ := fun s ↦
    ((g.inner s).toLinearMap₁₂.compl₁₂ (e.symmₗ ℝ s) (e.symmₗ ℝ s)).toContinuousBilinearMap
  have hG : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P →L[ℝ] ℝ) k G e.baseSet :=
    e.contMDiffOn_compl₁₂_symmₗ g.contMDiff.contMDiffOn
  obtain ⟨p, hp, hps⟩ := h.exists_contMDiffOn_negativeNormalProjection hn (le_self_add.trans hk)
    hf hdim s₀ hG (fun s _ u v ↦ by simpa [G] using g.symm s _ _) fun s hs u hu ↦ by
      simpa [G] using g.pos s _ ((map_ne_zero_iff _ (e.symmₗ_injective ℝ hs)).mpr hu)
  -- The normal-bundle trivialization at `s₀` is the bundle chart `e` at `s₀`.
  simp only [← normalSpaceFiberBundle_trivializationAt] at hp hps
  refine ⟨p, hp.mono fun s hs ↦ ⟨hs, hs⟩, fun s hs ↦ ?_⟩
  obtain ⟨hidem, hrange, hker, -, -, -, -, hrank, hnull⟩ := hps s ⟨hs, hs⟩
  -- Pulled back along the inverse trivialization, the metric is `G s`.
  set L := (e.linearEquivAt ℝ s hs).symm
  have hgL : (g.toRiemannianMetric.inner s).toBilinForm.compl₁₂ (L : P →ₗ[ℝ] i.NormalSpace s hn)
      (L : P →ₗ[ℝ] i.NormalSpace s hn) = (G s).toBilinForm := by
    ext u v
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, L,
      Trivialization.linearEquivAt_symm_apply, ContinuousLinearMap.toBilinForm_apply, G,
      LinearMap.toContinuousBilinearMap_apply, ContinuousLinearMap.toLinearMap₁₂_apply,
      e.symmₗ_apply hs]
    -- The underlying metric of `g` has the inner products of `g`, by definition.
    rfl
  have hL : (L : P →ₗ[ℝ] i.NormalSpace s hn) = e.symmₗ ℝ s := e.coe_linearEquivAt_symm ℝ hs
  refine ⟨hidem, ?_, ?_, hrank, hnull⟩
  · rw [IsCriticalSubmanifold.negativeNormalSpace_def, ← hL,
      ← LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂ L, hgL, hL, hrange]
  · rw [IsCriticalSubmanifold.positiveNormalSpace_def, ← hL,
      ← LinearMap.BilinForm.map_relativeSpectralSubspace_compl₁₂ L, hgL, hL, hker]

/-- **The negative normal bundle of a Morse–Bott submanifold.** Let `i` be a nondegenerate
critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class `C^{k+1}`, and
let `g` be a `C^k` fibre metric on the normal bundle, with fibre model `P`. If the Morse index of
`f` is `r` at every point of the submanifold, then the negative normal spaces relative to `g` have
`C^k` local frames of size `r` near every point: with the subspace topology they form a `C^k`
subbundle of rank `r` of the normal bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I f (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin r)
      (h.negativeNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun s₀ ↦ ?_
  obtain ⟨p, hp, hps⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g s₀
  obtain ⟨U, hUe, hU, hs₀U, X, hX, hXk⟩ :=
    (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).exists_isSubbundleFrameOn_map_symmₗ
      (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).open_baseSet subset_rfl hp
      (fun s hs ↦ (hps s hs).2.2.2.1.trans (hr s))
      (mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀)
  exact ⟨U, hU, hs₀U, X, ⟨hX.continuousOn, hX.linearIndependent,
    fun hy ↦ (hX.span_eq hy).trans (hps _ (hUe hy)).2.1.symm⟩, hXk⟩

/-- **The positive normal bundle of a Morse–Bott submanifold.** Let `i` be a nondegenerate
critical submanifold of `f`, with `f` of class `C^{k+2}` along it and `i` of class `C^{k+1}`, and
let `g` be a `C^k` fibre metric on the normal bundle, with fibre model `P`. If the Morse index of
`-f` is `r` at every point of the submanifold, then the positive normal spaces relative to `g`
have `C^k` local frames of size `r` near every point: with the subspace topology they form a `C^k`
subbundle of rank `r` of the normal bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiffVectorBundle`). -/
theorem hasLocalContMDiffSubbundleFrames_positiveNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex I (-f) (i s) = r) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin r)
      (h.positiveNormalSpace hn g.toRiemannianMetric) := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
  let := i.normalSpaceContMDiffVectorBundle hn hk hdim
  refine hasLocalContMDiffSubbundleFrames_iff.mpr fun s₀ ↦ ?_
  obtain ⟨p, hp, hps⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g s₀
  -- The kernel of a projection `p` is the range of the complementary projection `1 - p`.
  have hker (s : S) (hs : s ∈ (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).baseSet) :
      (1 - p s).range = (p s).ker := by
    have hP : IsIdempotentElem (p s : P →ₗ[ℝ] P) := congr(($((hps s hs).1) : P →ₗ[ℝ] P))
    rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP,
      ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one]
  obtain ⟨U, hUe, hU, hs₀U, X, hX, hXk⟩ :=
    (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).exists_isSubbundleFrameOn_map_symmₗ
      (trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀).open_baseSet subset_rfl
      (A := fun s ↦ 1 - p s) ((contDiff_const.sub contDiff_id :
        ContDiff ℝ k fun A : P →L[ℝ] P ↦ 1 - A).contMDiff.comp_contMDiffOn hp)
      (fun s hs ↦ (hker s hs ▸ (hps s hs).2.2.2.2).trans (hr s))
      (mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀)
  exact ⟨U, hU, hs₀U, X, ⟨hX.continuousOn, hX.linearIndependent, fun hy ↦
    (hX.span_eq hy).trans (by rw [hker _ (hUe hy), (hps _ (hUe hy)).2.2.1])⟩, hXk⟩

/-- **The negative normal bundle of a connected Morse–Bott submanifold.** On a connected
critical submanifold the Morse index is constant, so the negative normal spaces relative to a
`C^k` fibre metric form a `C^k` subbundle of the normal bundle whose rank is the index at any
point `s₀`. -/
theorem hasLocalContMDiffSubbundleFrames_negativeNormalSpace_of_preconnectedSpace
    [PreconnectedSpace S] (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin (manifoldMorseIndex I f (i s₀)))
      (h.negativeNormalSpace hn g.toRiemannianMetric) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  h.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g fun s ↦
    (h.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀

/-- **The positive normal bundle of a connected Morse–Bott submanifold.** On a connected
critical submanifold the Morse index of `-f` is constant, so the positive normal spaces relative to
a `C^k` fibre metric form a `C^k` subbundle of the normal bundle whose rank is the index of `-f`
at any point `s₀`. -/
theorem hasLocalContMDiffSubbundleFrames_positiveNormalSpace_of_preconnectedSpace
    [PreconnectedSpace S] (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) (s₀ : S) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    HasLocalContMDiffSubbundleFrames J k P (Fin (manifoldMorseIndex I (-f) (i s₀)))
      (h.positiveNormalSpace hn g.toRiemannianMetric) :=
  haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  h.hasLocalContMDiffSubbundleFrames_positiveNormalSpace hn hk hf hdim g fun s ↦
    (h.neg.isLocallyConstant_manifoldMorseIndex hn).apply_eq_of_preconnectedSpace s s₀

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ P] in
/-- Read in a trivialization, the projection of a normal space onto the negative normal space
along the positive one is the projection `p` of the fibre model with the corresponding range and
kernel. -/
private theorem apply_projection_negativeNormalSpace
    (h : i.IsNondegenerateCriticalSubmanifold f) [IsManifold I 2 M]
    (g : RiemannianMetric fun s ↦ i.NormalSpace s hn) {s : S}
    (L : i.NormalSpace s hn ≃ₗ[ℝ] P) {p : P →ₗ[ℝ] P} (hp : IsIdempotentElem p)
    (hN : h.negativeNormalSpace hn g s = (LinearMap.range p).map (L.symm : P →ₗ[ℝ] _))
    (hK : h.positiveNormalSpace hn g s = (LinearMap.ker p).map (L.symm : P →ₗ[ℝ] _))
    (x : i.NormalSpace s hn) :
    L ((h.negativeNormalSpace hn g s).projection (h.positiveNormalSpace hn g s)
      (h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s) x) = p (L x) := by
  -- Split `x = a + b` into its negative and positive parts; `L` carries them into the range and
  -- the kernel of `p`.
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    ((h.isCompl_negativeNormalSpace_positiveNormalSpace hn g g s).codisjoint.eq_top ▸
      Submodule.mem_top : x ∈ h.negativeNormalSpace hn g s ⊔ h.positiveNormalSpace hn g s)
  obtain ⟨y, hy, rfl⟩ := hN ▸ ha
  obtain ⟨z, hz, rfl⟩ := hK ▸ hb
  rw [LinearEquiv.coe_coe] at ha hb
  simp only [map_add, Submodule.projection_apply_of_mem_left _ ha,
    Submodule.projection_apply_of_mem_right _ hb, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    add_zero, (LinearMap.IsIdempotentElem.mem_range_iff hp).mp hy, LinearMap.mem_ker.mp hz]

/-- **The negative and positive normal bundles do not depend on the metric, up to isomorphism.**
Let `i` be a nondegenerate critical submanifold of `f`, with `f` of class `C^{k+2}` along it and
`i` of class `C^{k+1}`, and let `g₀` and `g₁` be two `C^k` fibre metrics on the normal bundle, with
fibre model `P`. Then there is a `C^k` family of linear automorphisms `e s` of the normal spaces
which carries the negative and positive normal spaces relative to `g₀` onto those relative to
`g₁`. By `TauCeti.bundleDiffeomorph` it is a `C^k` diffeomorphism of the total space of the normal
bundle over the identity of `S`, carrying the negative normal bundle `ν⁻(g₀)` onto `ν⁻(g₁)` and the
positive normal bundle `ν⁺(g₀)` onto `ν⁺(g₁)`. -/
theorem exists_contMDiff_map_negativeNormalSpace_eq_and_map_positiveNormalSpace_eq
    (h : i.IsNondegenerateCriticalSubmanifold f) (hk : k + 1 ≤ n)
    (hf : ∀ s, ContMDiffAt I 𝓘(ℝ) (k + 2) f (i s))
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (g₀ g₁ : haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
      haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
      letI := i.normalSpaceFiberBundle hn hdim
      letI := i.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric J k P fun s ↦ i.NormalSpace s hn) :
    haveI : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
    haveI : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
    haveI : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
    letI := i.normalSpaceFiberBundle hn hdim
    letI := i.normalSpaceVectorBundle hn hdim
    ∃ e : ∀ s, i.NormalSpace s hn ≃L[ℝ] i.NormalSpace s hn,
      ContMDiff (J.prod 𝓘(ℝ, P)) (J.prod 𝓘(ℝ, P)) k
        (fun v : TotalSpace P (fun s ↦ i.NormalSpace s hn) ↦
          TotalSpace.mk' P (E := fun s ↦ i.NormalSpace s hn) v.proj (e v.proj v.2)) ∧
      ∀ s, (h.negativeNormalSpace hn g₀.toRiemannianMetric s).map
            (e s : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn) =
          h.negativeNormalSpace hn g₁.toRiemannianMetric s ∧
        (h.positiveNormalSpace hn g₀.toRiemannianMetric s).map
            (e s : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn) =
          h.positiveNormalSpace hn g₁.toRiemannianMetric s := by
  have : IsManifold I 2 M := .of_le (n := k + 2) le_add_self
  have : IsManifold I 1 M := .of_le (n := k + 2) (one_le_two.trans le_add_self)
  have : IsManifold J 1 S := .of_le (n := k + 1) le_add_self
  let := i.normalSpaceFiberBundle hn hdim
  let := i.normalSpaceVectorBundle hn hdim
  set G₀ := g₀.toRiemannianMetric
  set G₁ := g₁.toRiemannianMetric
  -- The projections onto the negative normal spaces along the positive ones.
  let proj (G : RiemannianMetric fun s ↦ i.NormalSpace s hn) (s : S) :
      Module.End ℝ (i.NormalSpace s hn) :=
    (h.negativeNormalSpace hn G s).projection (h.positiveNormalSpace hn G s)
      (h.isCompl_negativeNormalSpace_positiveNormalSpace hn G G s)
  have hproj (G : RiemannianMetric fun s ↦ i.NormalSpace s hn) (s : S) :
      IsIdempotentElem (proj G s) :=
    Submodule.isIdempotentElem_projection _
  have hrange (G : RiemannianMetric fun s ↦ i.NormalSpace s hn) (s : S) :
      LinearMap.range (proj G s) = h.negativeNormalSpace hn G s :=
    Submodule.range_projection _
  have hker (G : RiemannianMetric fun s ↦ i.NormalSpace s hn) (s : S) :
      LinearMap.ker (proj G s) = h.positiveNormalSpace hn G s :=
    Submodule.ker_projection _
  have hbij (s : S) : Function.Bijective
      ⇑(proj G₁ s * proj G₀ s + (1 - proj G₁ s) * (1 - proj G₀ s)) :=
    LinearMap.IsIdempotentElem.bijective_mul_add_one_sub_mul_one_sub (hproj G₀ s) (hproj G₁ s)
      (by rw [hrange, hker]; exact h.isCompl_negativeNormalSpace_positiveNormalSpace hn G₀ G₁ s)
      (by
        rw [hker, hrange]
        exact (h.isCompl_negativeNormalSpace_positiveNormalSpace hn G₁ G₀ s).symm)
  let e (s : S) : i.NormalSpace s hn ≃L[ℝ] i.NormalSpace s hn :=
    (LinearEquiv.ofBijective _ (hbij s)).toContinuousLinearEquiv
  have he (s : S) : ⇑(e s) = ⇑(proj G₁ s * proj G₀ s + (1 - proj G₁ s) * (1 - proj G₀ s)) := rfl
  have he' (s : S) : (e s : i.NormalSpace s hn →ₗ[ℝ] i.NormalSpace s hn) =
      proj G₁ s * proj G₀ s + (1 - proj G₁ s) * (1 - proj G₀ s) := rfl
  refine ⟨e, ?_, fun s ↦ ⟨?_, ?_⟩⟩
  · have : IsManifold I (k + 1) M := .of_le (n := k + 2) (by gcongr; exact one_le_two)
    let := i.normalSpaceContMDiffVectorBundle hn hk hdim
    refine (contMDiff_hom_bundle_iff fun s ↦
      (e s : i.NormalSpace s hn →L[ℝ] i.NormalSpace s hn)).1 fun s₀ ↦ ?_
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    obtain ⟨p₀, hp₀, hps₀⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g₀ s₀
    obtain ⟨p₁, hp₁, hps₁⟩ := exists_contMDiffOn_negativeNormalSpace_eq_map hn h hk hf hdim g₁ s₀
    set t := trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
    have hs₀ : s₀ ∈ t.baseSet := mem_baseSet_trivializationAt P (fun s ↦ i.NormalSpace s hn) s₀
    -- In the trivialization, the automorphism is the intertwining operator of `p₀` and `p₁`.
    have hT : ContMDiffOn J 𝓘(ℝ, P →L[ℝ] P) k
        (fun s ↦ p₁ s * p₀ s + (1 - p₁ s) * (1 - p₀ s)) t.baseSet := by
      simp only [ContinuousLinearMap.mul_def]
      exact (hp₁.clm_comp hp₀).add ((contMDiffOn_const.sub hp₁).clm_comp
        (contMDiffOn_const.sub hp₀))
    refine (hT.contMDiffAt (t.open_baseSet.mem_nhds hs₀)).congr_of_eventuallyEq ?_
    filter_upwards [t.open_baseSet.mem_nhds hs₀] with s hs
    set L := t.continuousLinearEquivAt ℝ s hs
    have hsymm : t.symmₗ ℝ s = (L.symm : P →ₗ[ℝ] i.NormalSpace s hn) := by
      ext u
      simp [L, t.symmₗ_apply hs]
    -- `L` intertwines the projections of the normal space with `p₀` and `p₁`.
    have key (G : RiemannianMetric fun s ↦ i.NormalSpace s hn) (p : P →L[ℝ] P)
        (hp : IsIdempotentElem p)
        (hN : h.negativeNormalSpace hn G s = p.range.map (t.symmₗ ℝ s))
        (hK : h.positiveNormalSpace hn G s = p.ker.map (t.symmₗ ℝ s)) (x : i.NormalSpace s hn) :
        L (proj G s x) = p (L x) :=
      apply_projection_negativeNormalSpace hn h G L.toLinearEquiv (p := p)
        congr(($hp : P →ₗ[ℝ] P)) (by rw [hN, hsymm]; rfl) (by rw [hK, hsymm]; rfl) x
    obtain ⟨hi₀, hN₀, hK₀, -⟩ := hps₀ s hs
    obtain ⟨hi₁, hN₁, hK₁, -⟩ := hps₁ s hs
    ext u
    obtain ⟨x, rfl⟩ := L.surjective u
    rw [ContinuousLinearMap.inCoordinates_eq hs hs, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe]
    -- The bundle chart at `s` in the coordinate expression is `L`.
    rw [show t.continuousLinearEquivAt ℝ s hs = L from rfl, L.symm_apply_apply, he]
    simp only [LinearMap.add_apply, mul_apply_eq_comp,
      LinearMap.sub_apply, one_apply_eq_self, map_add, map_sub, key G₀ (p₀ s) hi₀ hN₀ hK₀,
      key G₁ (p₁ s) hi₁ hN₁ hK₁]
    simp only [add_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self, map_sub]
  · rw [he', ← hrange G₀, ← hrange G₁]
    exact LinearMap.IsIdempotentElem.map_range_mul_add_one_sub_mul_one_sub (hproj G₀ s) (hproj G₁ s)
      (by rw [hrange, hker]; exact h.isCompl_negativeNormalSpace_positiveNormalSpace hn G₀ G₁ s)
  · rw [he', ← hker G₀, ← hker G₁]
    exact LinearMap.IsIdempotentElem.map_ker_mul_add_one_sub_mul_one_sub (hproj G₀ s) (hproj G₁ s)
      (by
        rw [hker, hrange]
        exact (h.isCompl_negativeNormalSpace_positiveNormalSpace hn G₁ G₀ s).symm)

end TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold
