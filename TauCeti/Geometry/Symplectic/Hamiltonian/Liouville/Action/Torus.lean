/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle
public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Chart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Action–angle coordinates with values in the cotangent bundle of a torus

Let `σ` be a symplectic form on a boundaryless manifold `M` of dimension `2 |ι|`, and let
`F : M → (ι → ℝ)` be a smooth family of pairwise Poisson-commuting functions. Near a compact
connected component `L` of a level `F⁻¹(F x)` consisting of regular points, the angle map
`Ψ : ℝ^ι × ℝ^ι → M` of
`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact` is a
local diffeomorphism on `ℝ^ι × U`, identifies two points exactly when their angles differ by
`2πℤ^ι`, and pulls `σ` back to `∑ i, dθ_i ∧ dA_i` for action variables `A`.

This file descends `Ψ` to the torus: it constructs the **action–angle coordinates** of the
Liouville–Arnold theorem as a map `Φ` from a neighbourhood of `L` into the cotangent bundle of the
torus `ι → AddCircle p`, for any period `p > 0`, with its canonical symplectic form `ω = -dλ`
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`). On an open neighbourhood `U` of `L`:

* `Φ` is an injective local diffeomorphism, whose image is the set of covectors `ξ` whose actions
  `(ξ(e_i))_i` lie in an open set `D ⊆ ℝ^ι`;
* `Φ` pulls `ω` back to `σ`;
* `F` is a smooth function of the actions: `F = f ∘ (actions ∘ Φ)` for a smooth `f` on `D`.

Concretely, `Φ (Ψ (θ, c))` is the covector `∑ i, I_i dθ'_i` at the angles `θ' = (p / 2π) θ`, with
actions `I = (2π / p) A(c)` (`TauCeti.CotangentBundle.actionAngleMap`). The rescaling of the angles
from period `2π` to period `p` multiplies the actions by `2π / p` and preserves
`∑ i, dθ_i ∧ dI_i`.

## Main results

* `TauCeti.SmoothTwoForm.IsSymplectic.exists_actionAngle`: action–angle coordinates near a compact
  regular component of a level of an integrable system, with values in `T*(ι → AddCircle p)`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the Liouville–Arnold theorem and action–angle
  variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706.
-/

public section

noncomputable section

open Set Filter Function Real Module Bundle
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {ι : Type*} [Fintype ι] (p : ℝ) [Fact (0 < p)]

/-! ### The rescaled action–angle map -/

/-- The action–angle map of `T*(ι → AddCircle p)` read in angles of period `2π` and actions `A`:
it sends `(θ, c)` to the covector with angles `(p / 2π) θ` and actions `(2π / p) A(c)`. -/
private def rescaledActionAngleMap (A : (ι → ℝ) → ι → ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  CotangentBundle.actionAngleMap p ((p / (2 * π)) • z.1, (p / (2 * π))⁻¹ • A z.2)

private theorem contMDiffAt_rescaledActionAngleMap {A : (ι → ℝ) → ι → ℝ} {z : (ι → ℝ) × (ι → ℝ)}
    (hA : ContDiffAt ℝ ∞ A z.2) :
    ContMDiffAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (rescaledActionAngleMap p A) z :=
  (CotangentBundle.contMDiff_actionAngleMap (ι := ι) p _).comp z
    ((contDiffAt_fst.const_smul _).prodMk ((hA.comp z contDiffAt_snd).const_smul _)).contMDiffAt

/-- The chain rule for the rescaled action–angle map. -/
private theorem mfderiv_rescaledActionAngleMap {A : (ι → ℝ) → ι → ℝ} {z : (ι → ℝ) × (ι → ℝ)}
    (hA : DifferentiableAt ℝ A z.2) :
    mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (rescaledActionAngleMap p A) z =
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (CotangentBundle.actionAngleMap p)
          ((p / (2 * π)) • z.1, (p / (2 * π))⁻¹ • A z.2)).comp
        (((p / (2 * π)) • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
          ((p / (2 * π))⁻¹ • (fderiv ℝ A z.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) :=
  have hd : HasFDerivAt
      (fun z : (ι → ℝ) × (ι → ℝ) ↦ ((p / (2 * π)) • z.1, (p / (2 * π))⁻¹ • A z.2))
      (((p / (2 * π)) • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
        ((p / (2 * π))⁻¹ • (fderiv ℝ A z.2).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) z :=
    ((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasFDerivAt.const_smul (p / (2 * π))).prodMk
      ((hA.hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).hasFDerivAt).const_smul
        (p / (2 * π))⁻¹)
  mfderiv_comp z ((CotangentBundle.contMDiff_actionAngleMap (ι := ι) p _).mdifferentiableAt
    (by simp)) hd.differentiableAt.mdifferentiableAt |>.trans (by rw [hd.hasMFDerivAt.mfderiv]; rfl)

/-- The rescaled action–angle map pulls `ω` back to `∑ i, dθ_i ∧ dA_i`. -/
private theorem eval₂_symplecticForm_mfderiv_rescaledActionAngleMap {A : (ι → ℝ) → ι → ℝ}
    {z : (ι → ℝ) × (ι → ℝ)} (hA : ContDiffAt ℝ ∞ A z.2) (a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (rescaledActionAngleMap p A z)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledActionAngleMap p A) z (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (rescaledActionAngleMap p A) z (a', b')) =
      ∑ i, (a i * fderiv ℝ (fun c ↦ A c i) z.2 b' - a' i * fderiv ℝ (fun c ↦ A c i) z.2 b) := by
  -- By the chain rule, the tangent vector `(a, b)` is sent to `((p / 2π) a, (2π / p) dA b)`.
  rw [mfderiv_rescaledActionAngleMap p (hA.differentiableAt (by simp))]
  refine (CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleMap p _
    ((p / (2 * π)) • a, (p / (2 * π))⁻¹ • fderiv ℝ A z.2 b)
    ((p / (2 * π)) • a', (p / (2 * π))⁻¹ • fderiv ℝ A z.2 b')).trans ?_
  have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, fderiv_apply (hA.differentiableAt (by simp)),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  field_simp

/-- The differential of the rescaled action–angle map is injective where that of `A` is. -/
private theorem injective_mfderiv_rescaledActionAngleMap {A : (ι → ℝ) → ι → ℝ}
    {z : (ι → ℝ) × (ι → ℝ)} (hA : DifferentiableAt ℝ A z.2)
    (hA' : Injective (fderiv ℝ A z.2)) :
    Injective (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (rescaledActionAngleMap p A) z) := by
  have hκ : p / (2 * π) ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  have hL : Injective fun u : (ι → ℝ) × (ι → ℝ) ↦
      ((p / (2 * π)) • u.1, (p / (2 * π))⁻¹ • fderiv ℝ A z.2 u.2) := fun u u' h ↦ by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (smul_right_injective _ hκ h₁)
      (hA' (smul_right_injective _ (inv_ne_zero hκ) h₂))
  rw [mfderiv_rescaledActionAngleMap p hA]
  exact (CotangentBundle.injective_mfderiv_actionAngleMap p _).comp hL

/-- Two points of `ℝ^ι × U` have the same image under the rescaled action–angle map exactly when
they have the same image under an angle map of period `2π`, provided `A` is injective on `U`. -/
private theorem rescaledActionAngleMap_eq_iff {A : (ι → ℝ) → ι → ℝ} {U : Set (ι → ℝ)}
    (hA : InjOn A U) {z z' : (ι → ℝ) × (ι → ℝ)} (hz : z.2 ∈ U) (hz' : z'.2 ∈ U) :
    rescaledActionAngleMap p A z = rescaledActionAngleMap p A z' ↔
      z'.2 = z.2 ∧ ∃ m : ι → ℤ, z'.1 = z.1 + fun i ↦ 2 * π * m i := by
  have hκ : p / (2 * π) ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  rw [rescaledActionAngleMap, rescaledActionAngleMap,
    CotangentBundle.actionAngleMap_eq_actionAngleMap_iff]
  refine and_congr ⟨fun h ↦ hA hz' hz (smul_right_injective _ (inv_ne_zero hκ) h),
    fun h ↦ by rw [h]⟩ (exists_congr fun m ↦ ?_)
  -- An integer multiple of `p` is `p / 2π` times the same multiple of `2π`.
  have hm : (fun i ↦ (m i : ℝ) * p) = (p / (2 * π)) • fun i ↦ 2 * π * m i := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hm, ← smul_add, (smul_right_injective _ hκ).eq_iff]

/-! ### Descending the rescaled action–angle map through an angle map -/

section Descent

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {A : (ι → ℝ) → ι → ℝ} {Ψ : (ι → ℝ) × (ι → ℝ) → M} {S : Set ((ι → ℝ) × (ι → ℝ))}

/-- The rescaled action–angle map read through `Ψ` on `S`: at `Ψ z` it is the rescaled action–angle
map at `z`, when the two maps have the same fibres on `S`. -/
private def descendedChart (A : (ι → ℝ) → ι → ℝ) (Ψ : (ι → ℝ) × (ι → ℝ) → M)
    (S : Set ((ι → ℝ) × (ι → ℝ))) (y : M) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  rescaledActionAngleMap p A (invFunOn Ψ S y)

omit [TopologicalSpace M] [ChartedSpace H M] in
private theorem descendedChart_apply
    (hfib : ∀ z ∈ S, ∀ z' ∈ S,
      Ψ z = Ψ z' ↔ rescaledActionAngleMap p A z = rescaledActionAngleMap p A z')
    {z : (ι → ℝ) × (ι → ℝ)} (hz : z ∈ S) :
    descendedChart p A Ψ S (Ψ z) = rescaledActionAngleMap p A z :=
  (hfib _ (invFunOn_mem ⟨z, hz, rfl⟩) z hz).1 (invFunOn_eq ⟨z, hz, rfl⟩)

private theorem contMDiffAt_descendedChart (hS : IsOpen S)
    (hfib : ∀ z ∈ S, ∀ z' ∈ S,
      Ψ z = Ψ z' ↔ rescaledActionAngleMap p A z = rescaledActionAngleMap p A z')
    {z : (ι → ℝ) × (ι → ℝ)} (hz : z ∈ S)
    (hΨ : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ z) (hA : ContDiffAt ℝ ∞ A z.2) :
    ContMDiffAt I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (descendedChart p A Ψ S) (Ψ z) :=
  (hΨ.contMDiffAt_comp_iff le_rfl).1 <|
    (contMDiffAt_rescaledActionAngleMap p hA).congr_of_eventuallyEq
      (eventually_of_mem (hS.mem_nhds hz) fun _ ↦ descendedChart_apply p hfib)

/-- The differential of the descended chart composed with that of `Ψ` is that of the rescaled
action–angle map. -/
private theorem mfderiv_descendedChart_apply (hS : IsOpen S)
    (hfib : ∀ z ∈ S, ∀ z' ∈ S,
      Ψ z = Ψ z' ↔ rescaledActionAngleMap p A z = rescaledActionAngleMap p A z')
    {z : (ι → ℝ) × (ι → ℝ)} (hz : z ∈ S)
    (hΨ : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ z) (hA : ContDiffAt ℝ ∞ A z.2)
    (u : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) z) :
    mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (descendedChart p A Ψ S) (Ψ z) (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I Ψ z u) =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (rescaledActionAngleMap p A) z u := by
  have heq : descendedChart p A Ψ S ∘ Ψ =ᶠ[𝓝 z] rescaledActionAngleMap p A :=
    eventually_of_mem (hS.mem_nhds hz) fun _ ↦ descendedChart_apply p hfib
  rw [← mfderiv_comp_apply z
    ((contMDiffAt_descendedChart p hS hfib hz hΨ hA).mdifferentiableAt (by simp))
    (hΨ.mdifferentiableAt (by simp)), heq.mfderiv_eq]
  -- The two maps agree at `z`, so the cast between their tangent spaces is the identity.
  rfl

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [BoundarylessManifold I M]

/-- The descended chart is a local diffeomorphism on `Ψ '' S`. -/
private theorem isLocalDiffeomorphAt_descendedChart (hdim : 2 * Fintype.card ι = finrank ℝ E)
    (hS : IsOpen S)
    (hfib : ∀ z ∈ S, ∀ z' ∈ S,
      Ψ z = Ψ z' ↔ rescaledActionAngleMap p A z = rescaledActionAngleMap p A z')
    (hΨ : ∀ z ∈ S, IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ z)
    (hA : ∀ z ∈ S, ContDiffAt ℝ ∞ A z.2) (hA' : ∀ z ∈ S, Injective (fderiv ℝ A z.2))
    {z : (ι → ℝ) × (ι → ℝ)} (hz : z ∈ S) :
    IsLocalDiffeomorphAt I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      ∞ (descendedChart p A Ψ S) (Ψ z) := by
  refine isLocalDiffeomorphAt_of_injective_mfderiv (s := Ψ '' S)
    (fun _ ⟨z', hz', h⟩ ↦ h ▸ (contMDiffAt_descendedChart p hS hfib hz' (hΨ z' hz')
      (hA z' hz')).contMDiffWithinAt)
    ((show IsLocalDiffeomorphOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ S from fun z ↦ hΨ z.1 z.2)
      |>.isLocalHomeomorphOn.isOpen_image hS)
    ⟨z, hz, rfl⟩ BoundarylessManifold.isInteriorPoint (by simp) ?_ ?_
  · -- `dΦ ∘ dΨ` is the injective differential of the rescaled map, and `dΨ` is onto.
    intro v v' h
    obtain ⟨a, rfl⟩ := (hΨ z hz).isInvertible_mfderiv (by simp) |>.surjective v
    obtain ⟨a', rfl⟩ := (hΨ z hz).isInvertible_mfderiv (by simp) |>.surjective v'
    rw [mfderiv_descendedChart_apply p hS hfib hz (hΨ z hz) (hA z hz),
      mfderiv_descendedChart_apply p hS hfib hz (hΨ z hz) (hA z hz)] at h
    rw [injective_mfderiv_rescaledActionAngleMap p ((hA z hz).differentiableAt (by simp))
      (hA' z hz) h]
  · rw [← hdim, Module.finrank_prod, ← (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
      (E := ι → ℝ) (F' := ℝ)).finrank_eq, Module.finrank_linearMap, Module.finrank_self,
      mul_one, Module.finrank_fintype_fun_eq_card, two_mul]

/-- The actions of the rescaled action–angle map at `(θ, c)` are `(2π / p) A(c)`. -/
private theorem rescaledActionAngleMap_snd_apply_single [DecidableEq ι]
    (z : (ι → ℝ) × (ι → ℝ)) :
    (fun i ↦ (rescaledActionAngleMap p A z).2 (Pi.single i 1)) = (p / (2 * π))⁻¹ • A z.2 :=
  funext fun i ↦ CotangentBundle.actionAngleMap_snd_apply_single p _ i

omit [TopologicalSpace M] [ChartedSpace H M] in
/-- The descended chart maps `Ψ '' (ℝ^ι × U)` onto the covectors whose actions lie in
`(2π / p) A(U)`. -/
private theorem image_descendedChart [DecidableEq ι] {U : Set (ι → ℝ)}
    (hfib : ∀ z ∈ univ ×ˢ U, ∀ z' ∈ univ ×ˢ U,
      Ψ z = Ψ z' ↔ rescaledActionAngleMap p A z = rescaledActionAngleMap p A z') :
    descendedChart p A Ψ (univ ×ˢ U) '' (Ψ '' (univ ×ˢ U)) =
      {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ (fun c ↦ (p / (2 * π))⁻¹ • A c) '' U} := by
  have hκ : p / (2 * π) ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  ext ξ
  refine ⟨?_, fun ⟨c, hc, hξ⟩ ↦ ?_⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [mem_ofPred_eq, descendedChart_apply p hfib hz, rescaledActionAngleMap_snd_apply_single]
    exact ⟨z.2, hz.2, rfl⟩
  -- A covector is the action–angle map at a lift of its base point and its actions.
  obtain ⟨θ, hθ⟩ : ∃ θ : ι → ℝ, (fun i ↦ (θ i : AddCircle p)) = ξ.proj :=
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (ξ.proj i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (ξ.proj i)).choose_spec⟩
  refine ⟨_, ⟨((p / (2 * π))⁻¹ • θ, c), ⟨mem_univ _, hc⟩, rfl⟩, ?_⟩
  rw [descendedChart_apply p hfib ⟨mem_univ _, hc⟩]
  refine Eq.trans ?_ (CotangentBundle.actionAngleMap_eq_self p ξ hθ)
  rw [← hξ, rescaledActionAngleMap, smul_inv_smul₀ hκ]

end Descent

/-- Near a point `c₀` where `A` is a local diffeomorphism of `ℝ^ι`, inside any neighbourhood of
`c₀`, there is an open set `U ∋ c₀` on which `A` is a local diffeomorphism with a smooth left
inverse `g`; the rescaled actions `(2π / p) A(U)` form an open set on which the function
`J ↦ g((p / 2π) J)` recovering `c` is smooth. -/
private theorem exists_isOpen_actionDomain {A : (ι → ℝ) → ι → ℝ} {c₀ : ι → ℝ}
    (hA : IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A c₀) {U₀ : Set (ι → ℝ)}
    (hU₀ : U₀ ∈ 𝓝 c₀) :
    ∃ U ⊆ U₀, IsOpen U ∧ c₀ ∈ U ∧ ∃ g : (ι → ℝ) → ι → ℝ,
      IsOpen ((fun c ↦ (p / (2 * π))⁻¹ • A c) '' U) ∧
      ContDiffOn ℝ ∞ (fun J ↦ g ((p / (2 * π)) • J)) ((fun c ↦ (p / (2 * π))⁻¹ • A c) '' U) ∧
      ∀ c ∈ U, IsLocalDiffeomorphAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A c ∧ ContDiffAt ℝ ∞ A c ∧
        Injective (fderiv ℝ A c) ∧ g (A c) = c := by
  have hκ : p / (2 * π) ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  obtain ⟨U, hUsub, hU, hc₀U⟩ := mem_nhds_iff.1 <| inter_mem
    (inter_mem (hA.localInverse.open_target.mem_nhds hA.localInverse_mem_target) hU₀)
    (inter_mem (hA.contMDiffAt.continuousAt.preimage_mem_nhds
      (hA.localInverse.open_source.mem_nhds hA.localInverse_mem_source)) hA.eventually)
  have hsm (c) (hc : c ∈ U) : ContDiffAt ℝ ∞ A c :=
    contMDiffAt_iff_contDiffAt.1 (hUsub hc).2.2.contMDiffAt
  refine ⟨U, fun c hc ↦ (hUsub hc).1.2, hU, hc₀U, hA.localInverse, ?_, ?_, fun c hc ↦
    ⟨(hUsub hc).2.2, hsm c hc, ?_, hA.localInverse_left_inv (hUsub hc).1.1⟩⟩
  · -- The image of `U` under the local diffeomorphism `A`, rescaled, is open.
    rw [← image_image (fun J : ι → ℝ ↦ (p / (2 * π))⁻¹ • J) A]
    exact isOpenMap_smul₀ (inv_ne_zero hκ) _
      ((show IsLocalDiffeomorphOn 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) ∞ A U from fun c ↦ (hUsub c.2).2.2)
        |>.isLocalHomeomorphOn.isOpen_image hU)
  · rintro _ ⟨c, hc, rfl⟩
    have hg : ContDiffAt ℝ ∞ hA.localInverse ((p / (2 * π)) • (p / (2 * π))⁻¹ • A c) := by
      rw [smul_inv_smul₀ hκ]
      exact contMDiffAt_iff_contDiffAt.1 <| hA.contMDiffOn_localInverse.contMDiffAt
        (hA.localInverse.open_source.mem_nhds (hUsub hc).2.1)
    exact (hg.comp _ (contDiff_const_smul _).contDiffAt).contDiffWithinAt
  · have hL := (hUsub hc).2.2.isInvertible_mfderiv (by simp)
    rw [((hsm c hc).differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt.mfderiv] at hL
    exact hL.injective

/-! ### Action–angle coordinates in the cotangent bundle of the torus -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {F : M → ι → ℝ} [DecidableEq ι]

/-- **Action–angle coordinates near a compact regular component of a level** (the
Liouville–Arnold theorem). On a symplectic manifold of dimension `2 · |ι|`, let `F` be a smooth
family of pairwise Poisson-commuting functions, and let the connected component `L` of `x` in its
level `F⁻¹(F x)` be compact and consist of regular points of `F`. Let `p > 0`. Then there are an
open neighbourhood `U` of `L`, an open set `D ⊆ ℝ^ι`, a map `Φ` into the cotangent bundle of the
torus `ι → AddCircle p` and a smooth function `f` on `D` such that:

* `Φ` is injective on `U`, and a local diffeomorphism at every point of `U`;
* `Φ` maps `U` onto the covectors `ξ` whose actions `(ξ(e_i))_i` lie in `D`;
* `Φ` pulls the canonical symplectic form `ω = ∑ i, dθ_i ∧ dI_i` back to `σ` on `U`;
* on `U`, `F` is the function `f` of the actions of `Φ`. -/
theorem exists_actionAngle (hσ : σ.IsSymplectic) (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
    (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
    (hdim : 2 * Fintype.card ι = finrank ℝ E) {x : M}
    (hreg : ∀ y ∈ connectedComponentIn (F ⁻¹' {F x}) x, IsRegularPoint I 𝓘(ℝ, ι → ℝ) F y)
    (hK : IsCompact (connectedComponentIn (F ⁻¹' {F x}) x)) :
    ∃ (U : Set M) (D : Set (ι → ℝ))
      (Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
      (f : (ι → ℝ) → ι → ℝ),
      IsOpen U ∧ connectedComponentIn (F ⁻¹' {F x}) x ⊆ U ∧ IsOpen D ∧ ContDiffOn ℝ ∞ f D ∧
      InjOn Φ U ∧ Φ '' U = {ξ | (fun i ↦ ξ.2 (Pi.single i 1)) ∈ D} ∧
      (∀ y ∈ U, IsLocalDiffeomorphAt I
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y) ∧
      (∀ y ∈ U, ∀ v w : TangentSpace I y,
        SmoothBundleForm.eval₂
          (CotangentBundle.symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
            (ι → AddCircle p)) (Φ y)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y w) =
          SmoothBundleForm.eval₂ σ y v w) ∧
      ∀ y ∈ U, F y = f fun i ↦ (Φ y).2 (Pi.single i 1) := by
  obtain ⟨Ψ, A, U₀, hU₀, hxU₀, hA, hrange, hΨ⟩ :=
    hσ.exists_isLocalDiffeomorphAt_eval₂_mfderiv_eq_of_isCompact hF hcomm hdim hreg hK
  have hκ : p / (2 * π) ≠ 0 := div_ne_zero (Fact.out : 0 < p).ne' (by positivity)
  obtain ⟨U', hU'sub, hU', hxU', g, hD, hg, hAg⟩ :=
    exists_isOpen_actionDomain p hA (hU₀.mem_nhds hxU₀)
  set S : Set ((ι → ℝ) × (ι → ℝ)) := univ ×ˢ U'
  have hS : IsOpen S := isOpen_univ.prod hU'
  -- On `S`, the angle map `Ψ` and the rescaled action–angle map have the same fibres.
  have hfib (z) (hz : z ∈ S) (z') (hz' : z' ∈ S) :
      Ψ z = Ψ z' ↔ rescaledActionAngleMap p A z = rescaledActionAngleMap p A z' := by
    rw [rescaledActionAngleMap_eq_iff p (fun c hc c' hc' h ↦ by
      rw [← (hAg c hc).2.2.2, h, (hAg c' hc').2.2.2]) hz.2 hz'.2]
    exact (hΨ z.2 (hU'sub hz.2)).2.2.2 z'.2 (hU'sub hz'.2) z.1 z'.1
  have hΨS (z) (hz : z ∈ S) : IsLocalDiffeomorphAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ z :=
    (hΨ z.2 (hU'sub hz.2)).2.1 z.1
  refine ⟨Ψ '' S, _, descendedChart p A Ψ S, _,
    (show IsLocalDiffeomorphOn 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) I ∞ Ψ S from fun z ↦ hΨS z.1 z.2)
      |>.isLocalHomeomorphOn.isOpen_image hS, ?_, hD, hg, ?_, image_descendedChart p hfib,
    fun _ ⟨z, hz, h⟩ ↦ h ▸ isLocalDiffeomorphAt_descendedChart p hdim hS hfib hΨS
      (fun z hz ↦ (hAg z.2 hz.2).2.1) (fun z hz ↦ (hAg z.2 hz.2).2.2.1) hz, ?_, ?_⟩
  · rw [← hrange]
    rintro _ ⟨θ, rfl⟩
    exact ⟨(θ, F x), ⟨mem_univ _, hxU'⟩, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ h
    rw [descendedChart_apply p hfib hz, descendedChart_apply p hfib hz'] at h
    exact (hfib z hz z' hz').2 h
  · rintro _ ⟨z, hz, rfl⟩ v w
    obtain ⟨a, rfl⟩ := (hΨS z hz).isInvertible_mfderiv (by simp) |>.surjective v
    obtain ⟨b, rfl⟩ := (hΨS z hz).isInvertible_mfderiv (by simp) |>.surjective w
    rw [mfderiv_descendedChart_apply p hS hfib hz (hΨS z hz) (hAg z.2 hz.2).2.1,
      mfderiv_descendedChart_apply p hS hfib hz (hΨS z hz) (hAg z.2 hz.2).2.1,
      descendedChart_apply p hfib hz]
    -- Both sides are `∑ i, dθ_i ∧ dA_i` in the coordinates `(θ, c)`.
    exact (eval₂_symplecticForm_mfderiv_rescaledActionAngleMap p (hAg z.2 hz.2).2.1 a.1 b.1 a.2
      b.2).trans ((hΨ z.2 (hU'sub hz.2)).2.2.1 z.1 a.1 b.1 a.2 b.2).symm
  · rintro _ ⟨z, hz, rfl⟩
    rw [descendedChart_apply p hfib hz, rescaledActionAngleMap_snd_apply_single,
      smul_inv_smul₀ hκ, (hAg z.2 hz.2).2.2.2]
    exact (hΨ z.2 (hU'sub hz.2)).1 z.1

end IsSymplectic

end SmoothTwoForm

end TauCeti
