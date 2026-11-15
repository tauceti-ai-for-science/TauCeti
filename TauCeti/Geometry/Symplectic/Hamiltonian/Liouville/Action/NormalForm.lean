/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart

/-!
# The Liouville–Arnold normal form on the cotangent bundle of a torus

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Let `L` be the connected component of `x` in
its level `F⁻¹(F x)`, and suppose that `L` is compact and consists of regular points of `F`. The
Hamiltonian vector fields of the `F_i` need not be complete.

This file states the local Liouville–Arnold theorem as a normal form on the model
`T*Tⁿ = T*(ι → AddCircle p)`, for any period `p > 0`, with its canonical symplectic form
`ω = -dλ = ∑ i, dθ_i ∧ dI_i` (`TauCeti.CotangentBundle.symplecticForm`) and the actions
`I_i = ξ(e_i)` of its covectors (`TauCeti.CotangentBundle.torusActions`). There are an open
neighbourhood `U` of `L`, an open set `D ⊆ ℝ^ι` and a map `φ : M → T*Tⁿ` such that

* `φ` is injective on `U` and a local diffeomorphism at every point of `U`;
* `φ` maps `U` onto the covectors whose actions lie in `D`;
* `φ` pulls `ω` back to `σ` on `U`;
* `F = h ∘ I ∘ φ` on `U` for a smooth function `h` on `D`: the integrals are functions of the
  actions alone (`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`).

So `φ` restricts to a symplectomorphism of `U` onto the open subset `Tⁿ × D` of `T*Tⁿ`.

The map is assembled from the angle map `Ψ` and the action variables `A` of
`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact`.
There, `Ψ(θ, c)` is a local diffeomorphism identifying points exactly when their values `c` agree
and their angles `θ` differ by `2πℤ^ι`, and `Ψ^* σ = ∑ i, dθ_i ∧ dA_i`. The angle–action
parametrization `TauCeti.CotangentBundle.torusActionAngle p` of `T*Tⁿ`, which identifies points
exactly when their actions agree and their angles differ by `pℤ^ι`, pulls `ω` back to
`∑ i, dθ_i ∧ dI_i`. Rescaling the angles by `p / 2π` and the actions by `2π / p` matches the two
period lattices and preserves `∑ i, dθ_i ∧ dI_i`, so

`G(θ, c) = torusActionAngle p ((p / 2π) θ, (2π / p) A(c))`

satisfies `G^* ω = Ψ^* σ` and is constant on the fibres of `Ψ`. The map `φ` sends `Ψ(θ, c)` to
`G(θ, c)`. Where `Ψ` is a local diffeomorphism, `G` has injective differential because `σ` is
nondegenerate, so `φ` is a local diffeomorphism by the inverse function theorem.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`: the action–angle normal form near a
  compact regular component of a level.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem and action–angle
  variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1 (the local normal form on `T*Tⁿ`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4 (the Arnold–Liouville theorem).
-/

public section

noncomputable section

open Set Filter Function Module Bundle Real
open scoped Manifold ContDiff Topology Pointwise

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {ι : Type*} [Fintype ι] {F : M → ι → ℝ}

/-! ### The rescaled angle–action map -/

section Rescaled

variable (p : ℝ) (A : (ι → ℝ) → ι → ℝ)

/-- The angle–action parametrization of `T*Tⁿ`, read in angles `θ` of period `2π` and values `c`
of the integrals through action variables `A`:
`(θ, c) ↦ torusActionAngle p ((p / 2π) θ, (2π / p) A(c))`. -/
private def rescaledActionAngle [Fact (0 < p)] (q : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  CotangentBundle.torusActionAngle p ((p / (2 * π)) • q.1, (2 * π / p) • A q.2)

/-- The rescaled angle–action map identifies two pairs exactly when their action variables agree
and their angles differ by a vector of `2πℤ^ι`. -/
private theorem rescaledActionAngle_eq_iff [Fact (0 < p)] (θ c θ' c' : ι → ℝ) :
    rescaledActionAngle p A (θ, c) = rescaledActionAngle p A (θ', c') ↔
      A c' = A c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i := by
  have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
  have h2π : 2 * π ≠ 0 := by positivity
  rw [rescaledActionAngle, rescaledActionAngle,
    CotangentBundle.torusActionAngle_eq_torusActionAngle_iff,
    smul_right_injective _ (div_ne_zero h2π hp) |>.eq_iff]
  refine and_congr Iff.rfl (exists_congr fun m ↦ ?_)
  rw [funext_iff, funext_iff]
  refine forall_congr' fun i ↦ ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro h
  · field_simp at h
    linear_combination h
  · rw [h]
    field_simp

/-- The rescaled angle–action map sends `ℝ^ι × S` onto the covectors whose actions lie in
`(2π / p) • A(S)`. -/
private theorem image_rescaledActionAngle [DecidableEq ι] [Fact (0 < p)] (S : Set (ι → ℝ)) :
    rescaledActionAngle p A '' (univ ×ˢ S) =
      {z | CotangentBundle.torusActions p z ∈ (2 * π / p) • (A '' S)} := by
  have hκ : p / (2 * π) * (2 * π / p) = 1 := by
    have : p ≠ 0 := (Fact.out : 0 < p).ne'
    field_simp
  ext z
  constructor
  · rintro ⟨⟨θ, c⟩, hq, rfl⟩
    rw [mem_ofPred_eq, rescaledActionAngle, CotangentBundle.torusActions_torusActionAngle]
    exact smul_mem_smul_set (mem_image_of_mem A hq.2)
  · rintro ⟨_, ⟨c, hc, rfl⟩, hz⟩
    obtain ⟨⟨θ', I'⟩, rfl⟩ := CotangentBundle.torusActionAngle_surjective p z
    rw [CotangentBundle.torusActions_torusActionAngle] at hz
    dsimp only at hz
    refine ⟨((2 * π / p) • θ', c), ⟨mem_univ _, hc⟩, ?_⟩
    rw [rescaledActionAngle, smul_smul, hκ, one_smul, hz]

variable {p A}

/-- **The rescaled angle–action map pulls `ω` back to `∑ i, dθ_i ∧ dA_i`.** At a point where the
action variables are differentiable, the rescalings of the angles by `p / 2π` and of the actions
by `2π / p` cancel in the standard form `∑ i, dθ_i ∧ dI_i`. -/
private theorem eval₂_mfderiv_rescaledActionAngle [Fact (0 < p)] {c : ι → ℝ}
    (hA : DifferentiableAt ℝ A c) (θ a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (rescaledActionAngle p A (θ, c))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledActionAngle p A) (θ, c) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledActionAngle p A) (θ, c) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b) := by
  have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  -- The derivative of the rescaling `(θ, c) ↦ ((p / 2π) θ, (2π / p) A(c))`.
  have hR : HasFDerivAt (fun q : (ι → ℝ) × (ι → ℝ) ↦ ((p / (2 * π)) • q.1, (2 * π / p) • A q.2))
      (((p / (2 * π)) • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
        ((2 * π / p) • (fderiv ℝ A c).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) (θ, c) :=
    (hasFDerivAt_fst.const_smul (p / (2 * π))).prodMk
      ((hA.hasFDerivAt.comp (θ, c) hasFDerivAt_snd).const_smul (2 * π / p))
  -- The chain rule through the rescaling, a map between model vector spaces.
  have hd (v : (ι → ℝ) × (ι → ℝ)) :
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledActionAngle p A) (θ, c) v =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (CotangentBundle.torusActionAngle p) ((p / (2 * π)) • θ, (2 * π / p) • A c)
          ((p / (2 * π)) • v.1, (2 * π / p) • fderiv ℝ A c v.2) := by
    have hcomp := ((CotangentBundle.contMDiff_torusActionAngle p (ι := ι) _).mdifferentiableAt
      (by simp)).hasMFDerivAt.comp (θ, c) hR.hasMFDerivAt
    rw [show rescaledActionAngle p A = CotangentBundle.torusActionAngle p ∘
      fun q : (ι → ℝ) × (ι → ℝ) ↦ ((p / (2 * π)) • q.1, (2 * π / p) • A q.2) from rfl,
      hcomp.mfderiv]
    rfl
  have hcoord (w : ι → ℝ) (i : ι) : fderiv ℝ A c w i = fderiv ℝ (fun c ↦ A c i) c w := by
    rw [show (fun c ↦ A c i) = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) ∘ A
      from rfl, ((ContinuousLinearMap.proj i).hasFDerivAt.comp c hA.hasFDerivAt).fderiv]
    rfl
  rw [hd, hd, rescaledActionAngle, CotangentBundle.eval₂_mfderiv_torusActionAngle]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, hcoord]
  field_simp

end Rescaled

/-! ### The normal form -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [BoundarylessManifold I M] in
/-- A map `G` into `T*Tⁿ` which pulls `ω` back to the pullback of the nondegenerate form `σ` along
a local diffeomorphism `Ψ` at `q` has injective differential at `q`. -/
private theorem injective_mfderiv_of_eval₂_eq (hσ : σ.IsSymplectic) (p : ℝ) [Fact (0 < p)]
    {Ψ : (ι → ℝ) × (ι → ℝ) → M}
    {G : (ι → ℝ) × (ι → ℝ) → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)} {q : (ι → ℝ) × (ι → ℝ)}
    (hΨ : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ q)
    (hG : ∀ v w : (ι → ℝ) × (ι → ℝ), SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (G q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G q w) =
      SmoothBundleForm.eval₂ σ (Ψ q) (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q w)) :
    Injective (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G q) := by
  obtain ⟨e, he⟩ := hΨ.isInvertible_mfderiv (by simp)
  rw [injective_iff_map_eq_zero]
  intro v hv
  -- `dΨ v` pairs to zero with every `dΨ w`, hence with every vector since `dΨ` is onto.
  have h0 : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q v = 0 := by
    refine (isNondegenerate_iff_separatingLeft.1 hσ.isNondegenerate) (Ψ q) _ fun u ↦ ?_
    obtain ⟨w, rfl⟩ : ∃ w, mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q w = u :=
      ⟨e.symm u, by rw [← he]; exact e.apply_symm_apply u⟩
    refine (hG v w).symm.trans ?_
    rw [hv]
    exact SmoothBundleForm.eval₂_zero_left _ _ _
  rw [← he] at h0
  exact e.map_eq_zero_iff.1 h0

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [BoundarylessManifold I M] in
/-- Let `φ` agree near `y` with `G ∘ L`, where `L` is a local right inverse of `Ψ` at `y`. If `G`
pulls `ω` back to `Ψ^* σ` at `L y`, then `φ` pulls `ω` back to `σ` at `y`. -/
private theorem eval₂_mfderiv_of_eventuallyEq (p : ℝ) [Fact (0 < p)]
    {Ψ : (ι → ℝ) × (ι → ℝ) → M} {L : M → (ι → ℝ) × (ι → ℝ)}
    {G : (ι → ℝ) × (ι → ℝ) → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)}
    {φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)} {y : M}
    (hφ : φ =ᶠ[𝓝 y] G ∘ L) (hΨL : Ψ ∘ L =ᶠ[𝓝 y] id)
    (hL : MDifferentiableAt I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) L y)
    (hG : MDifferentiableAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G (L y))
    (hΨ : MDifferentiableAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (L y))
    (hpull : ∀ v w : (ι → ℝ) × (ι → ℝ), SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (G (L y))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G (L y) v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G (L y) w) =
      SmoothBundleForm.eval₂ σ (Ψ (L y)) (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (L y) v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (L y) w))
    (v w : TangentSpace I y) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (φ y)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y v)
        (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y w) =
      SmoothBundleForm.eval₂ σ y v w := by
  have hy : Ψ (L y) = y := hΨL.self_of_nhds
  -- Differentials of germs which agree are equal; `tangentSpaceCast` is the identity.
  have hφd (u : TangentSpace I y) :
      mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y u =
        mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G (L y)
          (mfderiv I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) L y u) := by
    rw [hφ.mfderiv_eq, ContinuousLinearMap.comp_apply, mfderiv_comp_apply y hG hL]
    rfl
  -- The differential of `Ψ` inverts that of `L`.
  have hΨL' (u : TangentSpace I y) :
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (L y) (mfderiv I 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) L y u) =
        u := by
    have h := congrArg (· u) (Filter.EventuallyEq.mfderiv_eq (I := I) (I' := I) hΨL)
    simp only [ContinuousLinearMap.comp_apply, mfderiv_comp_apply y hΨ hL, mfderiv_id,
      ContinuousLinearMap.id_apply] at h
    exact h
  rw [hφd, hφd, hφ.self_of_nhds, Function.comp_apply]
  refine (hpull _ _).trans ?_
  rw [hΨL', hΨL', hy]

omit [I.Boundaryless] [T2Space M] in
/-- **Descending a map along a local diffeomorphism.** Let `Ψ` be a local diffeomorphism at every
point of an open set `V`, and let `G` be a local diffeomorphism into `T*Tⁿ` at every point of `V`,
constant on the fibres of `Ψ` in `V`, which pulls `ω` back to `Ψ^* σ`. Then `G` descends to a map
`φ` on the open set `Ψ(V)`, `φ ∘ Ψ = G` on `V`, which is a local diffeomorphism pulling `ω` back
to `σ` at every point of `Ψ(V)`. -/
private theorem exists_descend (p : ℝ) [Fact (0 < p)] {Ψ : (ι → ℝ) × (ι → ℝ) → M}
    {G : (ι → ℝ) × (ι → ℝ) → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)} {V : Set ((ι → ℝ) × (ι → ℝ))} (hV : IsOpen V)
    (hΨ : ∀ q ∈ V, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ q)
    (hG : ∀ q ∈ V, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ G q)
    (hfib : ∀ q ∈ V, ∀ q' ∈ V, Ψ q = Ψ q' → G q = G q')
    (hpull : ∀ q ∈ V, ∀ v w : (ι → ℝ) × (ι → ℝ), SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (G q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) G q w) =
      SmoothBundleForm.eval₂ σ (Ψ q) (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q w)) :
    ∃ φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
      IsOpen (Ψ '' V) ∧ (∀ q ∈ V, φ (Ψ q) = G q) ∧
      (∀ y ∈ Ψ '' V, IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ y) ∧
      ∀ y ∈ Ψ '' V, ∀ v w : TangentSpace I y, SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p))
          (φ y)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y w) =
        SmoothBundleForm.eval₂ σ y v w := by
  classical
  set φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
    fun y ↦ G (invFunOn Ψ V y)
  have hφΨ (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ V) : φ (Ψ q) = G q :=
    hfib _ (invFunOn_mem ⟨q, hq, rfl⟩) q hq (invFunOn_eq ⟨q, hq, rfl⟩)
  -- `Ψ(V)` is open, and near `Ψ q` the map `φ` is `G` composed with a local inverse of `Ψ`.
  have hU : IsOpen (Ψ '' V) := by
    have hΨV : IsLocalHomeomorphOn Ψ V :=
      IsLocalDiffeomorphOn.isLocalHomeomorphOn (n := ∞) fun q ↦ hΨ q q.2
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [← hΨV.map_nhds_eq hq]
    exact image_mem_map (hV.mem_nhds hq)
  have hli (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ V) : (hΨ q hq).localInverse (Ψ q) = q :=
    (hΨ q hq).localInverse_left_inv (hΨ q hq).localInverse_mem_target
  have hgerm (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ V) :
      φ =ᶠ[𝓝 (Ψ q)] G ∘ (hΨ q hq).localInverse := by
    filter_upwards [(hΨ q hq).localInverse.open_source.mem_nhds (hΨ q hq).localInverse_mem_source,
      (hΨ q hq).continuousAt_localInverse.preimage_mem_nhds
        (by rw [hli q hq]; exact hV.mem_nhds hq)] with y hy hyV
    calc φ y = φ (Ψ ((hΨ q hq).localInverse y)) := by rw [(hΨ q hq).localInverse_right_inv hy]
      _ = G ((hΨ q hq).localInverse y) := hφΨ _ hyV
  have hcomp (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ V) :
      IsLocalDiffeomorphAt I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod
        𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (G ∘ (hΨ q hq).localInverse) (Ψ q) := by
    have hG' : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ G
        ((hΨ q hq).localInverse (Ψ q)) := by
      rw [hli q hq]
      exact hG q hq
    exact (hΨ q hq).localInverse_isLocalDiffeomorphAt.comp (hg := hG')
  -- Hence `φ` is smooth with injective differential on `Ψ(V)`, a local diffeomorphism there.
  have hφsmooth : ContMDiffOn I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ (Ψ '' V) := by
    rintro _ ⟨q, hq, rfl⟩
    exact ((hcomp q hq).contMDiffAt.congr_of_eventuallyEq (hgerm q hq)).contMDiffWithinAt
  refine ⟨φ, hU, hφΨ, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨e, he⟩ := (hcomp q hq).isInvertible_mfderiv (by simp)
    refine isLocalDiffeomorphAt_of_injective_mfderiv hφsmooth hU ⟨q, hq, rfl⟩
      BoundarylessManifold.isInteriorPoint (by simp) ?_ e.toLinearEquiv.finrank_eq
    rw [(hgerm q hq).mfderiv_eq, ← he]
    exact e.injective
  · rintro _ ⟨q, hq, rfl⟩ v w
    have hq' : (hΨ q hq).localInverse (Ψ q) ∈ V := by rw [hli q hq]; exact hq
    exact eval₂_mfderiv_of_eventuallyEq p (hgerm q hq) (hΨ q hq).localInverse_eventuallyEq_right
      ((hΨ q hq).mdifferentiableAt_localInverse (by simp)) ((hG _ hq').mdifferentiableAt (by simp))
      ((hΨ _ hq').mdifferentiableAt (by simp)) (hpull _ hq') v w

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [BoundarylessManifold I M] in
/-- Action variables which are a local diffeomorphism at `c₀` restrict to an open set `S ∋ c₀`
inside a given open set `U₀`, on which they are smooth, with open image and a smooth inverse `g`
on that image. -/
private theorem exists_restrict_actions {A : (ι → ℝ) → ι → ℝ} {c₀ : ι → ℝ}
    (hA : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A c₀) {U₀ : Set (ι → ℝ)}
    (hU₀ : IsOpen U₀) (hc₀ : c₀ ∈ U₀) :
    ∃ (S : Set (ι → ℝ)) (g : (ι → ℝ) → ι → ℝ), IsOpen S ∧ c₀ ∈ S ∧ S ⊆ U₀ ∧
      ContDiffOn ℝ ∞ A S ∧ IsOpen (A '' S) ∧ ContDiffOn ℝ ∞ g (A '' S) ∧ ∀ c ∈ S, g (A c) = c := by
  -- Restrict to the target of the local inverse `Ξ` of `A`, where `A` agrees with `Ξ⁻¹`.
  set Ξ := hA.localInverse
  have hAΞ (c : ι → ℝ) (hc : c ∈ Ξ.target) : A c = Ξ.symm c := by
    have h := hA.localInverse_right_inv (Ξ.toPartialEquiv.map_target hc)
    rwa [Ξ.toPartialEquiv.right_inv hc] at h
  have hS : IsOpen (Ξ.target ∩ U₀) := Ξ.open_target.inter hU₀
  have himage : A '' (Ξ.target ∩ U₀) = Ξ.symm '' (Ξ.target ∩ U₀) :=
    image_congr fun c hc ↦ hAΞ c hc.1
  refine ⟨Ξ.target ∩ U₀, Ξ, hS, ⟨hA.localInverse_mem_target, hc₀⟩, inter_subset_right,
    (contMDiffOn_iff_contDiffOn.1 Ξ.symm.contMDiffOn).mono inter_subset_left |>.congr
      fun c hc ↦ hAΞ c hc.1, ?_, ?_, fun c hc ↦ hA.localInverse_left_inv hc.1⟩
  · rw [himage]
    exact Ξ.symm.toOpenPartialHomeomorph.isOpen_image_of_subset_source hS inter_subset_left
  · refine (contMDiffOn_iff_contDiffOn.1 Ξ.contMDiffOn).mono ?_
    rw [himage]
    rintro _ ⟨c, hc, rfl⟩
    exact Ξ.toPartialEquiv.map_target hc.1

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [BoundarylessManifold I M] in
/-- Let `Ψ` and action variables `A`, smooth on an open set `S`, have the properties of the angle
map of `exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact` over `S`. Then on `ℝ^ι × S` the
rescaled angle–action map `G` pulls `ω` back to `Ψ^* σ`, is a local diffeomorphism, and is
constant on the fibres of `Ψ`. -/
private theorem rescaledActionAngle_spec (hσ : σ.IsSymplectic) (p : ℝ) [Fact (0 < p)]
    {Ψ : (ι → ℝ) × (ι → ℝ) → M} {A : (ι → ℝ) → ι → ℝ} {S : Set (ι → ℝ)} (hS : IsOpen S)
    (hA : ContDiffOn ℝ ∞ A S)
    (hΨ : ∀ c ∈ S, ∀ θ, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ (θ, c))
    (hΨpull : ∀ c ∈ S, ∀ θ a a' b b', SmoothBundleForm.eval₂ σ (Ψ (θ, c))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, c) (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ (θ, c) (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) c b' - a' i * fderiv ℝ (fun c ↦ A c i) c b))
    (hΨfib : ∀ c ∈ S, ∀ c' ∈ S, ∀ θ θ', Ψ (θ, c) = Ψ (θ', c') ↔
      c' = c ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ 2 * π * m i) :
    (∀ q ∈ univ ×ˢ S, ∀ v w : (ι → ℝ) × (ι → ℝ), SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (rescaledActionAngle p A q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledActionAngle p A) q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledActionAngle p A) q w) =
      SmoothBundleForm.eval₂ σ (Ψ q) (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q v)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ q w)) ∧
    (∀ q ∈ univ ×ˢ S, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (rescaledActionAngle p A) q) ∧
    ∀ q ∈ univ ×ˢ S, ∀ q' ∈ univ ×ˢ S, Ψ q = Ψ q' →
      rescaledActionAngle p A q = rescaledActionAngle p A q' := by
  have hpull (q : (ι → ℝ) × (ι → ℝ)) (hq : q ∈ univ ×ˢ S) (v w : (ι → ℝ) × (ι → ℝ)) :=
    (eval₂_mfderiv_rescaledActionAngle (p := p)
      ((hA.contDiffAt (hS.mem_nhds hq.2)).differentiableAt (by simp)) q.1 v.1 w.1 v.2 w.2).trans
      (hΨpull q.2 hq.2 q.1 v.1 w.1 v.2 w.2).symm
  -- The differential of `G` is injective since `Ψ^* σ` is nondegenerate, so the inverse function
  -- theorem applies.
  have hsmooth : ContMDiffOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (rescaledActionAngle p A) (univ ×ˢ S) :=
    (CotangentBundle.contMDiff_torusActionAngle p).comp_contMDiffOn
      (contMDiffOn_iff_contDiffOn.2 ((contDiff_fst.const_smul _).contDiffOn.prodMk
        ((hA.comp contDiff_snd.contDiffOn fun q (hq : q ∈ univ ×ˢ S) ↦ hq.2).const_smul _)))
  refine ⟨hpull, fun q hq ↦ isLocalDiffeomorphAt_of_injective_mfderiv hsmooth
    (isOpen_univ.prod hS) hq BoundarylessManifold.isInteriorPoint (by simp)
    (injective_mfderiv_of_eval₂_eq hσ p (hΨ q.2 hq.2 q.1) (hpull q hq))
    ((CotangentBundle.isLocalDiffeomorph_torusActionAngle p q).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv.finrank_eq, ?_⟩
  rintro ⟨θ, c⟩ hq ⟨θ', c'⟩ hq' h
  obtain ⟨rfl, m, rfl⟩ := (hΨfib c hq.2 c' hq'.2 θ θ').1 h
  exact (rescaledActionAngle_eq_iff p A _ _ _ _).2 ⟨rfl, m, rfl⟩

/-- **The Liouville–Arnold theorem: action–angle normal form on `T*Tⁿ`.** On a symplectic manifold
`(M, σ)` of dimension `2 |ι|`, let `F` be a smooth family of pairwise Poisson-commuting functions,
and let the connected component `L` of `x` in its level `F⁻¹(F x)` be compact and consist of regular
points of `F`; the Hamiltonian vector fields of the `F_i` need not be complete. Fix a period
`p > 0` and let `T*Tⁿ` be the cotangent bundle of the torus `ι → AddCircle p`, with its canonical
symplectic form `ω`. Then there are an open neighbourhood `U` of `L`, an open set `D ⊆ ℝ^ι`, a map
`φ : M → T*Tⁿ` and a smooth function `h` on `D` such that

* `φ` is injective on `U` and a local diffeomorphism at every point of `U`;
* `φ` maps `U` onto the covectors whose actions `I` lie in `D`;
* `φ` pulls `ω` back to `σ` at every point of `U`;
* `F = h(I(φ))` on `U`.

So the actions `I ∘ φ` and the angles of `φ` are action–angle coordinates on `U`, in which
`σ = ∑ i, dθ_i ∧ dI_i` and every `F_i` is a function of the actions alone. -/
theorem exists_actionAngle [DecidableEq ι] (hσ : σ.IsSymplectic)
    (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F) (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) (p : ℝ) [Fact (0 < p)] :
    ∃ (U : Set M) (D : Set (ι → ℝ))
      (φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (h : (ι → ℝ) → ι → ℝ),
      IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ U ∧ IsOpen D ∧ InjOn φ U ∧
      (∀ y ∈ U, IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ φ y) ∧
      φ '' U = {z | CotangentBundle.torusActions p z ∈ D} ∧
      (∀ y ∈ U, ∀ v w : TangentSpace I y, SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p))
          (φ y)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) φ y w) =
        SmoothBundleForm.eval₂ σ y v w) ∧
      ContDiffOn ℝ ∞ h D ∧ ∀ y ∈ U, F y = h (CotangentBundle.torusActions p (φ y)) := by
  classical
  obtain ⟨Ψ, A, U₀, hU₀, hxU₀, hA, hrange, hUc⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  -- Restrict the values `c` to an open set `S` on which `A` has a smooth inverse `g`.
  obtain ⟨S, g, hS, hxS, hSU₀, hAS, hAS', hg, hgA⟩ := exists_restrict_actions hA hU₀ hxU₀
  -- The rescaled angle–action map `G` on `ℝ^ι × S` descends along `Ψ` to `φ`.
  obtain ⟨hGpull, hGloc, hfib⟩ := rescaledActionAngle_spec hσ p hS hAS
    (fun c hc ↦ (hUc c (hSU₀ hc)).2.1) (fun c hc ↦ (hUc c (hSU₀ hc)).2.2.1)
    fun c hc c' hc' ↦ (hUc c (hSU₀ hc)).2.2.2 c' (hSU₀ hc')
  obtain ⟨φ, hU, hφΨ, hφloc, hφpull⟩ := exists_descend p (isOpen_univ.prod hS)
    (fun q hq ↦ (hUc q.2 (hSU₀ hq.2)).2.1 q.1) hGloc hfib hGpull
  -- The actions of `φ (Ψ (θ, c))` are `(2π / p) A(c)`, from which `h` recovers `c`.
  have hκ : p / (2 * π) * (2 * π / p) = 1 := by
    have : p ≠ 0 := (Fact.out : 0 < p).ne'
    field_simp
  have hhA (c : ι → ℝ) (hc : c ∈ S) : g ((p / (2 * π)) • (2 * π / p) • A c) = c := by
    rw [smul_smul, hκ, one_smul, hgA c hc]
  refine ⟨Ψ '' (univ ×ˢ S), (2 * π / p) • (A '' S), φ, fun I' ↦ g ((p / (2 * π)) • I'), hU, ?_,
    hAS'.smul₀ (by have : 0 < p := Fact.out; positivity), ?_, hφloc, ?_, hφpull, ?_, ?_⟩
  · rw [← hrange]
    rintro _ ⟨θ, rfl⟩
    exact ⟨(θ, F x), ⟨mem_univ _, hxS⟩, rfl⟩
  · rintro _ ⟨⟨θ, c⟩, hq, rfl⟩ _ ⟨⟨θ', c'⟩, hq', rfl⟩ h
    rw [hφΨ _ hq, hφΨ _ hq'] at h
    obtain ⟨hAc, m, rfl⟩ := (rescaledActionAngle_eq_iff p A θ c θ' c').1 h
    have hcc : c' = c := by rw [← hgA c' hq'.2, hAc, hgA c hq.2]
    exact ((hUc c (hSU₀ hq.2)).2.2.2 c' (hSU₀ hq'.2) θ _).2 ⟨hcc, m, rfl⟩
  · rw [← image_rescaledActionAngle, image_image]
    exact image_congr fun q hq ↦ hφΨ q hq
  · refine hg.comp (contDiff_const_smul _).contDiffOn ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    dsimp only
    rw [smul_smul, hκ, one_smul]
    exact mem_image_of_mem A hc
  · rintro _ ⟨⟨θ, c⟩, hq, rfl⟩
    rw [hφΨ _ hq, rescaledActionAngle, CotangentBundle.torusActions_torusActionAngle]
    exact ((hUc c (hSU₀ hq.2)).1 θ).trans (hhA c hq.2).symm

end IsSymplectic

end SmoothTwoForm

end TauCeti
