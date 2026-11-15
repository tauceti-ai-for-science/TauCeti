/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Action–angle coordinates on the cotangent bundle of a torus

Let `p > 0` and let `Tⁿ = ι → AddCircle p` be the torus with all periods `p`, whose tangent space
at every point is `ι → ℝ`. Its cotangent bundle `T*Tⁿ`, with the canonical symplectic form
`ω = -dλ` (`TauCeti.CotangentBundle.symplecticForm`), is the model space of action–angle
coordinates. A covector `ξ` over a point of `Tⁿ` has **actions** `I_i = ξ(e_i)`, its values on the
coordinate vectors (`TauCeti.CotangentBundle.torusActions`), and `ξ = ∑ i, I_i dθ_i` in terms of the
coordinate time forms `dθ_i` (`TauCeti.torusTimeForm`).

This file parametrizes `T*Tⁿ` by angles and actions. The map

`(θ, I) ↦ ∑ i, I_i dθ_i` at the point `([θ_i])ᵢ` of `Tⁿ`

(`TauCeti.CotangentBundle.torusActionAngle p`), from `(ι → ℝ) × (ι → ℝ)` to `T*Tⁿ`, is a smooth
surjective local diffeomorphism. It identifies two pairs exactly when their actions agree and their
angles differ by a vector of `pℤ^ι`, so it descends to a diffeomorphism of `Tⁿ × ℝ^ι` with
`T*Tⁿ`. It pulls the Liouville form back to `∑ i, I_i dθ_i` and the canonical symplectic form back
to the standard form

`∑ i, dθ_i ∧ dI_i`,

which pairs `(a, b)` with `(a', b')` to `∑ i, (a_i b'_i - a'_i b_i)`. These are the coordinates in
which the Liouville–Arnold theorem states the normal form `σ = ∑ i, dθ_i ∧ dI_i` near a compact
regular level of an integrable system.

The pullback of `ω` is computed without charts of `T*Tⁿ`: the map lies over the covering
`(θ, I) ↦ [θ]` of the torus, whose derivative is the identity of `ι → ℝ`, so the Liouville form
pulls back to the one-form `(θ, I) ↦ ∑ i, I_i dθ_i` of the vector space `(ι → ℝ) × (ι → ℝ)`. That
one-form is the pullback of the linear Liouville form `TauCeti.cotangentLiouvilleForm` along the
linear map `(θ, I) ↦ (θ, ∑ i, I_i dθ_i)`, so the pullback of `ω = -dλ` is the pullback of the linear
symplectic form `TauCeti.strongDualCotangentSymplecticForm` along that map. Since this
standard form is nondegenerate, the differential of the map is injective, and the inverse
function theorem makes it a local diffeomorphism.

## Main definitions

* `TauCeti.CotangentBundle.torusActions p z`: the actions `z(e_i)` of a covector of `T*Tⁿ`.
* `TauCeti.CotangentBundle.torusActionAngle p`: the map `(θ, I) ↦ ∑ i, I_i dθ_i` at `[θ]`.

## Main results

* `TauCeti.CotangentBundle.contMDiff_torusActionAngle`: the parametrization is smooth.
* `TauCeti.CotangentBundle.mpullback_torusActionAngle_liouvilleForm_apply`: it pulls the Liouville
  form back to `∑ i, I_i dθ_i`.
* `TauCeti.CotangentBundle.eval₂_mfderiv_torusActionAngle`: it pulls the canonical symplectic form
  back to `∑ i, dθ_i ∧ dI_i`.
* `TauCeti.CotangentBundle.isLocalDiffeomorph_torusActionAngle`: it is a local diffeomorphism.
* `TauCeti.CotangentBundle.torusActionAngle_eq_torusActionAngle_iff`: two pairs have the same
  image exactly when their actions agree and their angles differ by a vector of `pℤ^ι`.
* `TauCeti.CotangentBundle.torusActionAngle_surjective`: every covector has angle–action
  coordinates.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action–angle variables).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2 (the canonical forms of a cotangent bundle in coordinates).
-/

public section

noncomputable section

open Bundle Set Function Module
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι]

/-- The **actions** of a covector `z` of `T*Tⁿ`: its values `z(e_i)` on the coordinate vectors
`e_i` of the tangent space `ι → ℝ`. -/
def torusActions [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) : ι → ℝ :=
  fun i ↦ z.2 (Pi.single i 1)

/-- The `i`-th action of a covector is its value on the `i`-th coordinate vector. -/
@[simp]
theorem torusActions_apply [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (i : ι) :
    torusActions p z i = z.2 (Pi.single i 1) :=
  (rfl)

/-- A covector of the torus evaluates a tangent vector `v` as `∑ i, I_i v_i`, in terms of its
actions `I`. -/
theorem snd_apply_eq_sum_torusActions [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z.proj) :
    z.2 v = ∑ i, torusActions p z i * v i := by
  -- `z.2` is a covector on the tangent space, a type synonym of `ι → ℝ`, so it is expanded in the
  -- standard basis through its underlying linear map.
  have h := LinearMap.pi_apply_eq_sum_univ (z.2 : (ι → ℝ) →L[ℝ] ℝ).toLinearMap v
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  have hi : (fun j ↦ if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hi, smul_eq_mul, mul_comm]
  rfl

/-- **Action–angle coordinates of `T*Tⁿ`.** The pair `(θ, I)` of angles and actions is sent to the
covector `∑ i, I_i dθ_i` at the point `([θ_i])ᵢ` of the torus `ι → AddCircle p`. -/
def torusActionAngle (q : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) :=
  ⟨fun i ↦ (q.1 i : AddCircle p), ∑ i, q.2 i •
    SmoothForm.degreeOneEquiv (torusTimeForm (fun _ : ι ↦ p) i) fun i ↦ (q.1 i : AddCircle p)⟩

/-- The base point of `torusActionAngle p (θ, I)` is the point `([θ_i])ᵢ` of the torus. -/
@[simp]
theorem torusActionAngle_proj (q : (ι → ℝ) × (ι → ℝ)) :
    (torusActionAngle p q).proj = fun i ↦ (q.1 i : AddCircle p) :=
  (rfl)

/-- The covector `torusActionAngle p (θ, I)` evaluates a tangent vector `v` as `∑ i, I_i v_i`. -/
@[simp]
theorem torusActionAngle_snd_apply (q : (ι → ℝ) × (ι → ℝ))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusActionAngle p q).proj) :
    (torusActionAngle p q).2 v = ∑ i, q.2 i * v i := by
  refine (sum_apply Finset.univ _ v).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  -- The scalar multiple of a covector evaluates as the multiple of the value, and `dθ_i` reads
  -- the `i`-th coordinate.
  exact congrArg (q.2 i * ·) ((SmoothForm.degreeOneEquiv_apply_apply _ _ _).trans
    (torusTimeForm_apply _ i _ _))

/-- The actions of `torusActionAngle p (θ, I)` are `I`. -/
@[simp]
theorem torusActions_torusActionAngle [DecidableEq ι] (q : (ι → ℝ) × (ι → ℝ)) :
    torusActions p (torusActionAngle p q) = q.2 := by
  funext i
  exact (torusActionAngle_snd_apply p q (Pi.single i 1)).trans (by simp [Pi.single_apply])

/-- The angle–action parametrization of `T*Tⁿ` is smooth. -/
theorem contMDiff_torusActionAngle :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (torusActionAngle p (ι := ι)) := by
  have hb : ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (q.1 i : AddCircle p)) :=
    contMDiff_pi_iff.2 fun i ↦ (AddCircle.contMDiff_coe p ∞).comp
      ((contDiff_apply ℝ (fun _ : ι ↦ ℝ) i).comp contDiff_fst).contMDiff
  exact ContMDiff.sum_sectionAlong _ _ hb fun i _ ↦
    ContMDiff.smul_totalSpace (a := fun q : (ι → ℝ) × (ι → ℝ) ↦ q.2 i)
      (g := fun q : (ι → ℝ) × (ι → ℝ) ↦ (⟨fun i ↦ (q.1 i : AddCircle p),
        SmoothForm.degreeOneEquiv (torusTimeForm (fun _ : ι ↦ p) i)
          fun i ↦ (q.1 i : AddCircle p)⟩ :
        CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)))
      ((contDiff_apply ℝ (fun _ : ι ↦ ℝ) i).comp contDiff_snd).contMDiff
      ((SmoothForm.degreeOneEquiv (torusTimeForm (fun _ : ι ↦ p) i)).contMDiff.comp hb)

/-! ### Pullbacks of the canonical forms -/

/-- The linear map `(θ, I) ↦ (θ, ∑ i, I_i dθ_i)` from `(ι → ℝ) × (ι → ℝ)` to the linear cotangent
space of `ι → ℝ`. -/
private def angleActionCLM :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ((ι → ℝ) × StrongDual ℝ (ι → ℝ)) :=
  (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod <|
    ∑ i, ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).smulRight
      (ContinuousLinearMap.proj i)

private theorem angleActionCLM_fst (q : (ι → ℝ) × (ι → ℝ)) : (angleActionCLM q).1 = q.1 :=
  (rfl)

private theorem angleActionCLM_snd_apply (q : (ι → ℝ) × (ι → ℝ)) (v : ι → ℝ) :
    (angleActionCLM q).2 v = ∑ i, q.2 i * v i := by
  simp [angleActionCLM, sum_apply]

/-- **The angle–action parametrization pulls the Liouville form back to `∑ i, I_i dθ_i`.** At
`(θ, I)` the pulled-back Liouville form evaluates a tangent vector `(a, b)` as `∑ i, I_i a_i`. -/
theorem mpullback_torusActionAngle_liouvilleForm_apply (q : (ι → ℝ) × (ι → ℝ))
    (v : Fin 1 → (ι → ℝ) × (ι → ℝ)) :
    (SmoothForm.mpullback (torusActionAngle p) (contMDiff_torusActionAngle p)
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))).1 q v =
      ∑ i, q.2 i * (v 0).1 i := by
  -- The parametrization lies over the covering `(θ, I) ↦ [θ]`, whose derivative is `(a, b) ↦ a`.
  have hg : HasMFDerivAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (q.1 i : AddCircle p)) q
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)) :=
    (AddCircle.hasMFDerivAt_coe_pi p q.1).comp q
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasMFDerivAt
  rw [SmoothForm.coe_mpullback]
  refine (mpullback_liouvilleForm_apply_of_proj_comp_eq
    (g := fun q : (ι → ℝ) × (ι → ℝ) ↦ fun i ↦ (q.1 i : AddCircle p)) (fun _ ↦ rfl)
    ((contMDiff_torusActionAngle p q).mdifferentiableAt (by simp)) v).trans ?_
  rw [hg.mfderiv]
  exact torusActionAngle_snd_apply p q _

/-- The pulled-back Liouville form is the pullback of the linear Liouville form along
`(θ, I) ↦ (θ, ∑ i, I_i dθ_i)`. -/
private theorem coe_mpullback_torusActionAngle_liouvilleForm :
    (SmoothForm.mpullback (torusActionAngle p) (contMDiff_torusActionAngle p)
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))).1 =
      fun q ↦ (cotangentLiouvilleForm (angleActionCLM q)).compContinuousLinearMap
        (fderiv ℝ angleActionCLM q) := by
  funext q
  ext v
  have h (u : Fin 1 → (ι → ℝ) × (ι → ℝ)) :
      (cotangentLiouvilleForm (angleActionCLM q)).compContinuousLinearMap
        (fderiv ℝ angleActionCLM q) u = ∑ i, q.2 i * (u 0).1 i := by
    rw [ContinuousLinearMap.fderiv, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      cotangentLiouvilleForm_apply, angleActionCLM_snd_apply]
    rfl
  exact (mpullback_torusActionAngle_liouvilleForm_apply p q v).trans (h v).symm

/-- **The angle–action parametrization is symplectic.** It pulls the canonical symplectic form
`ω = -dλ` of `T*Tⁿ` back to the standard form `∑ i, dθ_i ∧ dI_i`, which pairs `(a, b)` with
`(a', b')` to `∑ i, (a_i b'_i - a'_i b_i)`. -/
theorem eval₂_mfderiv_torusActionAngle (q : (ι → ℝ) × (ι → ℝ)) (a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))
        (torusActionAngle p q)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusActionAngle p) q (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusActionAngle p) q (a', b')) =
      ∑ i, (a i * b' i - a' i * b i) := by
  -- The flat exterior derivative of the pullback of the linear Liouville form along
  -- `(θ, I) ↦ (θ, ∑ i, I_i dθ_i)` is the pullback of the linear symplectic form.
  have flat (v w : (ι → ℝ) × (ι → ℝ)) :
      -extDeriv (fun q ↦ (cotangentLiouvilleForm (angleActionCLM q)).compContinuousLinearMap
        (fderiv ℝ angleActionCLM q)) q ![v, w] =
        strongDualCotangentSymplecticForm (angleActionCLM v) (angleActionCLM w) := by
    rw [extDeriv_pullback (x := q) (r := 2) (differentiableAt_cotangentLiouvilleForm _)
        (angleActionCLM (ι := ι)).contDiff.contDiffAt (by simp),
      ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.fderiv]
    exact neg_extDeriv_cotangentLiouvilleForm_apply _ _
  -- On the vector space `(ι → ℝ) × (ι → ℝ)`, the pullback of `ω = -dλ` is minus the flat
  -- exterior derivative of the pulled-back Liouville form `∑ i, I_i dθ_i`.
  have key (v w : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) q) :
      SmoothBundleForm.eval₂ (SmoothForm.mpullback (torusActionAngle p)
          (contMDiff_torusActionAngle p)
          (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p))) q v w =
        strongDualCotangentSymplecticForm (angleActionCLM v) (angleActionCLM w) := by
    rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
      SmoothBundleForm.eval₂_neg, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
      mextDeriv_eq_extDeriv, coe_mpullback_torusActionAngle_liouvilleForm]
    exact flat v w
  refine (SmoothForm.eval₂_mpullback _ (contMDiff_torusActionAngle p) _ q (a, b)
    (a', b')).symm.trans ((key _ _).trans ?_)
  rw [strongDualCotangentSymplecticForm_apply, angleActionCLM_snd_apply, angleActionCLM_snd_apply,
    angleActionCLM_fst, angleActionCLM_fst, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### Local diffeomorphism, fibres and surjectivity -/

/-- **The differential of the angle–action parametrization is injective**, since it pulls `ω` back
to the nondegenerate form `∑ i, dθ_i ∧ dI_i`. -/
theorem injective_mfderiv_torusActionAngle (q : (ι → ℝ) × (ι → ℝ)) :
    Injective (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      (torusActionAngle p) q) := by
  classical
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ hab
  -- Pairing `(a, b)` with every `(a', b')` gives `∑ i, (a_i b'_i - a'_i b_i) = 0`.
  have h0 (a' b' : ι → ℝ) : ∑ i, (a i * b' i - a' i * b i) = 0 := by
    rw [← eval₂_mfderiv_torusActionAngle p q a a' b b', hab]
    exact SmoothBundleForm.eval₂_zero_left _ _ _
  have ha : a = 0 := funext fun j ↦ by simpa [Pi.single_apply] using h0 0 (Pi.single j 1)
  have hb : b = 0 := funext fun j ↦ by simpa [Pi.single_apply] using h0 (Pi.single j 1) 0
  rw [ha, hb]
  rfl

/-- **The angle–action parametrization of `T*Tⁿ` is a local diffeomorphism.** -/
theorem isLocalDiffeomorph_torusActionAngle :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞
      (torusActionAngle p (ι := ι)) := fun q ↦
  isLocalDiffeomorphAt_of_injective_mfderiv (contMDiff_torusActionAngle p).contMDiffOn isOpen_univ
    (mem_univ q) BoundarylessManifold.isInteriorPoint (by simp)
    (injective_mfderiv_torusActionAngle p q) (by
      rw [finrank_prod, finrank_prod, (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
        (E := ι → ℝ) (F' := ℝ)).finrank_eq.symm, Module.finrank_linearMap, finrank_self,
        mul_one])

/-- Pairs with the same actions whose angles have the same classes in `AddCircle p` are sent to
the same covector. -/
theorem torusActionAngle_eq_of_coe_eq {θ θ' : ι → ℝ} (h : ∀ i, (θ i : AddCircle p) = θ' i)
    (I : ι → ℝ) : torusActionAngle p (θ, I) = torusActionAngle p (θ', I) := by
  have h' : (fun i ↦ (θ i : AddCircle p)) = fun i ↦ (θ' i : AddCircle p) := funext h
  simp only [torusActionAngle]
  rw [h']

/-- **The fibres of the angle–action parametrization.** Two pairs `(θ, I)` and `(θ', I')` are sent
to the same covector of `T*Tⁿ` exactly when `I' = I` and `θ' - θ ∈ pℤ^ι`. -/
theorem torusActionAngle_eq_torusActionAngle_iff (θ I θ' I' : ι → ℝ) :
    torusActionAngle p (θ, I) = torusActionAngle p (θ', I') ↔
      I' = I ∧ ∃ m : ι → ℤ, θ' = θ + fun i ↦ p * m i := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hI := congrArg (torusActions p) h
      rwa [torusActions_torusActionAngle, torusActions_torusActionAngle, eq_comm] at hI
    · have hθ (i : ι) : ((θ i : ℝ) : AddCircle p) = θ' i :=
        congrFun (congrArg TotalSpace.proj h) i
      choose m hm using fun i ↦ AddSubgroup.mem_zmultiples_iff.1
        (QuotientAddGroup.eq_iff_sub_mem.1 (hθ i).symm)
      refine ⟨m, funext fun i ↦ ?_⟩
      have := hm i
      simp only [zsmul_eq_mul] at this
      simp only [Pi.add_apply]
      linarith
  · rintro ⟨rfl, m, rfl⟩
    refine torusActionAngle_eq_of_coe_eq p (fun i ↦ ?_) I'
    simp only [Pi.add_apply]
    rw [eq_comm, QuotientAddGroup.eq_iff_sub_mem]
    exact AddSubgroup.mem_zmultiples_iff.2 ⟨m i, by simp only [zsmul_eq_mul]; ring⟩

/-- **Every covector of `T*Tⁿ` has angle–action coordinates.** -/
theorem torusActionAngle_surjective : Surjective (torusActionAngle p (ι := ι)) := by
  classical
  rintro ⟨y, ξ⟩
  choose θ hθ using fun i ↦ QuotientAddGroup.mk_surjective (y i)
  obtain rfl : (fun i ↦ (θ i : AddCircle p)) = y := funext hθ
  refine ⟨(θ, torusActions p ⟨_, ξ⟩), TotalSpace.ext rfl (heq_of_eq ?_)⟩
  ext v
  exact (torusActionAngle_snd_apply p _ v).trans (snd_apply_eq_sum_torusActions p ⟨_, ξ⟩ v).symm

end CotangentBundle

end TauCeti
