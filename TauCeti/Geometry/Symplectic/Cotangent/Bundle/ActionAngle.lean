/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import TauCeti.Geometry.Symplectic.Liouville.Linear

/-!
# Action–angle coordinates on the cotangent bundle of a torus

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus, whose tangent space at every point is
`ι → ℝ`. A covector `ξ` over `[θ] ∈ Tⁿ` has **actions** `I_i = ξ(e_i)`, its values on the
coordinate vectors, and `ξ = ∑ i, I_i dθ_i`. This file studies the map

`μ : (ι → ℝ) × (ι → ℝ) → T*Tⁿ`,  `(θ, I) ↦ ∑ i, I_i dθ_i` at `[θ]`

(`TauCeti.CotangentBundle.actionAngleMap p`), which reads a point of `T*Tⁿ` in its angles `θ`,
defined modulo `pℤ^ι`, and its actions `I`. It is the model of action–angle coordinates: the
Liouville–Arnold theorem identifies a neighbourhood of a regular compact level of an integrable
system with an open subset of `T*Tⁿ` through such coordinates.

* `μ` is smooth and surjective, and two points have the same image exactly when their actions
  agree and their angles differ by an element of `pℤ^ι`
  (`TauCeti.CotangentBundle.actionAngleMap_eq_actionAngleMap_iff`).
* It pulls the Liouville form back to `∑ i, I_i dθ_i`
  (`TauCeti.CotangentBundle.mpullback_actionAngleMap_liouvilleForm_apply`), and the canonical
  symplectic form `ω = -dλ` back to `∑ i, dθ_i ∧ dI_i`
  (`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_actionAngleMap`).
* Since `∑ i, dθ_i ∧ dI_i` is nondegenerate, the differential of `μ` is injective, and `μ` is a
  local diffeomorphism (`TauCeti.CotangentBundle.isLocalDiffeomorph_actionAngleMap`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action–angle variables).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 2 and 18.
-/

public section

noncomputable section

open Bundle Set
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι]

/-- The **action–angle map** of the cotangent bundle of the torus `ι → AddCircle p`: it sends
`(θ, I)` to the covector `∑ i, I_i dθ_i` over the point `[θ]` of the torus. -/
def actionAngleMap (z : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ (z.1 i : AddCircle p)) (∑ i, z.2 i • proj i)

/-- The action–angle map lies over the image `[θ]` of the angles in the torus. -/
@[simp]
theorem proj_actionAngleMap (z : (ι → ℝ) × (ι → ℝ)) :
    (actionAngleMap p z).proj = fun i ↦ (z.1 i : AddCircle p) :=
  (rfl)

/-- The covector `actionAngleMap p (θ, I)` sends a tangent vector `v : ι → ℝ` to
`∑ i, I_i * v_i`. -/
@[simp]
theorem actionAngleMap_snd_apply (z : (ι → ℝ) × (ι → ℝ)) (v : ι → ℝ) :
    (actionAngleMap p z).2 v = ∑ i, z.2 i * v i := by
  -- The fibre of `T*Tⁿ` is a type synonym of `(ι → ℝ) →L[ℝ] ℝ`.
  have h (w : ι → ℝ) : (∑ i, z.2 i • proj i : (ι → ℝ) →L[ℝ] ℝ) w = ∑ i, z.2 i * w i := by
    simp
  exact h v

variable [DecidableEq ι] in
/-- The actions of the covector `actionAngleMap p (θ, I)`, its values on the coordinate vectors, are
`I`. -/
theorem actionAngleMap_snd_apply_single (z : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (actionAngleMap p z).2 (Pi.single i 1) = z.2 i := by
  simp [Pi.single_apply]

variable [DecidableEq ι] in
/-- A covector of the torus is the image under the action–angle map of any lift of its base point
and of its actions. -/
theorem actionAngleMap_eq_self
    (ξ : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
    {θ : ι → ℝ} (hθ : (fun i ↦ (θ i : AddCircle p)) = ξ.proj) :
    actionAngleMap p (θ, fun i ↦ ξ.2 (Pi.single i 1)) = ξ := by
  refine ext hθ fun v ↦ (actionAngleMap_snd_apply p _ v).trans ?_
  -- A covector on `ι → ℝ` is determined by its values on the coordinate vectors.
  refine Eq.trans ?_ (LinearMap.pi_apply_eq_sum_univ ξ.2.toLinearMap v).symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_eq_mul, mul_comm]
  exact congrArg (v i * ξ.2 ·) (funext fun j ↦ by simp [Pi.single_apply, eq_comm])

/-- The action–angle map is surjective. -/
theorem actionAngleMap_surjective : Function.Surjective (actionAngleMap (ι := ι) p) := by
  classical
  intro ξ
  obtain ⟨θ, hθ⟩ : ∃ θ : ι → ℝ, (fun i ↦ (θ i : AddCircle p)) = ξ.proj :=
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (ξ.proj i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (ξ.proj i)).choose_spec⟩
  exact ⟨_, actionAngleMap_eq_self p ξ hθ⟩

/-- Two points have the same image under the action–angle map exactly when their actions agree and
their angles agree modulo `pℤ^ι`. -/
theorem actionAngleMap_eq_actionAngleMap_iff (z z' : (ι → ℝ) × (ι → ℝ)) :
    actionAngleMap p z = actionAngleMap p z' ↔
      z'.2 = z.2 ∧ ∃ m : ι → ℤ, z'.1 = z.1 + fun i ↦ m i * p := by
  classical
  constructor
  · intro h
    refine ⟨funext fun i ↦ ?_, ?_⟩
    · have hi := congrArg (fun ξ ↦ ξ.2 (Pi.single i 1)) h
      simp only [actionAngleMap_snd_apply_single] at hi
      exact hi.symm
    · -- The base points agree, so each angle difference is an integer multiple of `p`.
      have hproj := congrArg TotalSpace.proj h
      choose m hm using fun i ↦ (AddCircle.coe_eq_zero_iff (p := p) (x := z'.1 i - z.1 i)).1 <| by
        rw [AddCircle.coe_sub, sub_eq_zero]
        exact (congrFun hproj i).symm
      refine ⟨m, funext fun i ↦ ?_⟩
      rw [Pi.add_apply, ← zsmul_eq_mul, hm i, add_sub_cancel]
  · rintro ⟨h2, m, h1⟩
    refine ext (funext fun i ↦ ?_) fun v ↦ ?_
    · simp only [proj_actionAngleMap, h1, Pi.add_apply, AddCircle.coe_add, ← zsmul_eq_mul,
        AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
    · exact (actionAngleMap_snd_apply p z v).trans
        ((congrArg (fun J ↦ ∑ i, J i * v i) h2).symm.trans (actionAngleMap_snd_apply p z' v).symm)

/-! ### Smoothness -/

/-- The action–angle map is smooth. -/
theorem contMDiff_actionAngleMap :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (actionAngleMap (ι := ι) p) := by
  intro z₀
  have hb : ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞
      (fun z : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (z.1 i : AddCircle p)) :=
    contMDiff_pi_iff.2 fun i ↦ (AddCircle.contMDiff_coe p ∞).comp
      (proj i ∘L ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).contDiff.contMDiff
  -- Along `z ↦ [θ]`, the coordinate time form `dθ_i` is the covector `proj i`.
  have hs (i : ι) : ContMDiffAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (fun z : (ι → ℝ) × (ι → ℝ) ↦ (TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ)
        (fun j ↦ (z.1 j : AddCircle p)) (proj i) :
          CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))) z₀ := by
    refine ((SmoothForm.degreeOneEquiv (torusTimeForm (fun _ ↦ p) i)).contMDiff.comp hb
      z₀).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
    refine ext rfl fun v ↦ ?_
    simp only [Function.comp_apply, SmoothForm.degreeOneEquiv_apply_apply_vec, torusTimeForm_apply,
      Matrix.cons_val_zero]
    -- `proj i` evaluates the tangent vector `v`, of the type synonym `TangentSpace`, at `i`.
    rfl
  refine (contMDiffAt_hom_bundle _).2 ⟨hb z₀, ?_⟩
  have h := ContMDiffAt.sum (t := Finset.univ) fun i _ ↦
    ((proj i ∘L ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).contDiff.contMDiff z₀).smul
      ((contMDiffAt_hom_bundle _).1 (hs i)).2
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
  -- In coordinates, `∑ i, I_i dθ_i` is the combination of the coordinate covectors of the `dθ_i`.
  ext v
  simp only [ContinuousLinearMap.inCoordinates, actionAngleMap,
    Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_apply, sum_apply, Pi.smul_apply', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.proj_apply, smul_apply, smul_eq_mul]
  -- The scalar multiple of `proj i` evaluates as a product, the fibre being a type synonym.
  exact Finset.sum_congr rfl fun i _ ↦ rfl

/-! ### The pulled-back forms -/

/-- The derivative of `(θ, I) ↦ [θ]` is `(a, b) ↦ a`. -/
private theorem hasMFDerivAt_coe_fst (z : (ι → ℝ) × (ι → ℝ)) :
    HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun z : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (z.1 i : AddCircle p)) z
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)) :=
  ((AddCircle.hasMFDerivAt_coe_pi p z.1).comp z
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasMFDerivAt).congr_mfderiv
    (ContinuousLinearMap.id_comp _)

/-- **The action–angle map pulls the Liouville form back to `∑ i, I_i dθ_i`**: at `(θ, I)` the
pulled-back form sends a tangent vector `(a, b)` to `∑ i, I_i a_i`. -/
theorem mpullback_actionAngleMap_liouvilleForm_apply (z : (ι → ℝ) × (ι → ℝ))
    (u : Fin 1 → TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) z) :
    (SmoothForm.mpullback (actionAngleMap p) (contMDiff_actionAngleMap p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))).1 z u =
      ∑ i, z.2 i * (u 0).1 i := by
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_comp_eq
    (g := fun z : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (z.1 i : AddCircle p)) (fun _ ↦ rfl)
    ((contMDiff_actionAngleMap p z).mdifferentiableAt (by simp)),
    (hasMFDerivAt_coe_fst p z).mfderiv]
  exact actionAngleMap_snd_apply p z _

/-- **The action–angle map pulls the canonical symplectic form back to `∑ i, dθ_i ∧ dI_i`**: at
`(θ, I)` the pulled-back form pairs tangent vectors `(a, b)` and `(a', b')` to
`∑ i, (a_i b'_i - a'_i b_i)`. -/
theorem eval₂_symplecticForm_mfderiv_actionAngleMap (z u u' : (ι → ℝ) × (ι → ℝ)) :
    SmoothBundleForm.eval₂ (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (actionAngleMap p z)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (actionAngleMap p) z u)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (actionAngleMap p) z u') =
      ∑ i, (u.1 i * u'.2 i - u'.1 i * u.2 i) := by
  -- The pulled-back Liouville form is the linear one-form `(θ, I) ↦ B (θ, I) ·` of the bilinear
  -- form `B ((θ, I), (a, b)) = ∑ i, I_i a_i`.
  let B : ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ℝ :=
    ∑ i, (proj i ∘L ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).smulRight
      (proj i ∘L ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))
  have hB (w w' : (ι → ℝ) × (ι → ℝ)) : B w w' = ∑ i, w.2 i * w'.1 i := by
    simp [B]
  have hlam : (SmoothForm.mpullback (actionAngleMap p) (contMDiff_actionAngleMap p)
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))).1 =
        ⇑(ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • B)) := by
    funext w
    ext u
    refine (mpullback_actionAngleMap_liouvilleForm_apply p w u).trans ?_
    refine Eq.trans ?_ (ContinuousLinearMap.liouvilleFormCLM_apply _ w u).symm
    have h2 (a : (ι → ℝ) × (ι → ℝ)) : (2 : ℝ)⁻¹ • ((2 : ℝ) • B w) a = B w a := by
      rw [smul_apply, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    exact (hB w (u 0)).symm.trans (h2 (u 0)).symm
  have hd : mextDeriv (SmoothForm.mpullback (actionAngleMap p) (contMDiff_actionAngleMap p)
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))).1 z ![u, u'] =
        B u u' - B u' u := by
    rw [hlam]
    refine (congrArg (· ![u, u']) (mextDeriv_eq_extDeriv
      (ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • B) :
        RoughForm 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) ((ι → ℝ) × (ι → ℝ)) ℝ 1) z)).trans ?_
    have h2 (a b : (ι → ℝ) × (ι → ℝ)) :
        (2 : ℝ)⁻¹ • (((2 : ℝ) • B) a b - ((2 : ℝ) • B) b a) = B a b - B b a := by
      rw [smul_apply, smul_apply, smul_apply, smul_apply, ← smul_sub, smul_smul,
        inv_mul_cancel₀ two_ne_zero, one_smul]
    exact (ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply _ z ![u, u']).trans (h2 u u')
  rw [SmoothBundleForm.eval₂_apply, symplecticForm_eq_neg_mextDeriv, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply]
  -- `ω = -dλ`, and pullback commutes with `d`.
  refine (congrArg Neg.neg ((SmoothForm.mextDeriv_mpullback_apply_two (actionAngleMap p)
    (contMDiff_actionAngleMap p) _ z u u').symm.trans hd)).trans ?_
  rw [hB, hB, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### The action–angle map is a local diffeomorphism -/

/-- The differential of the action–angle map is injective at every point: the pulled-back form
`∑ i, dθ_i ∧ dI_i` is nondegenerate. -/
theorem injective_mfderiv_actionAngleMap (z : (ι → ℝ) × (ι → ℝ)) :
    Function.Injective (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (actionAngleMap p) z) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun (u : (ι → ℝ) × (ι → ℝ)) hu ↦ ?_
  -- Every pairing of `u` with another tangent vector vanishes.
  have h (u' : (ι → ℝ) × (ι → ℝ)) : ∑ i, (u.1 i * u'.2 i - u'.1 i * u.2 i) = 0 :=
    (eval₂_symplecticForm_mfderiv_actionAngleMap p z u u').symm.trans
      (by rw [hu, SmoothBundleForm.eval₂_zero_left])
  have h₁ : u.1 = 0 := funext fun j ↦ by simpa [Pi.single_apply] using h (0, Pi.single j 1)
  have h₂ : u.2 = 0 := funext fun j ↦ by simpa [Pi.single_apply] using h (Pi.single j 1, 0)
  exact Prod.ext h₁ h₂

/-- **The action–angle map is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_actionAngleMap :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (actionAngleMap (ι := ι) p) := fun z ↦
  isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_actionAngleMap p).contMDiffOn isOpen_univ
    (mem_univ z) BoundarylessManifold.isInteriorPoint (by simp)
    (injective_mfderiv_actionAngleMap p z) <| by
      rw [Module.finrank_prod, Module.finrank_prod,
        ← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ι → ℝ) (F' := ℝ)).finrank_eq,
        Module.finrank_linearMap, Module.finrank_self, mul_one]

end CotangentBundle

end TauCeti
