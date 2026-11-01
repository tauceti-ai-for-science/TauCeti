/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# The special orthogonal group of a real inner product space

The orthogonal group of a real inner product space `V` is the unitary group
`unitary (V →L[ℝ] V)` of its operator algebra, as used for the structure group of orthonormal
frame bundles. This file defines its special orthogonal subgroup
`TauCeti.specialOrthogonalGroup V`, the orthogonal transformations of positive determinant. These
are the orthogonal transformations preserving each orientation of a finite-dimensional `V`, so
they form the structure group of the positively oriented orthonormal frames of an oriented
Riemannian vector bundle.

The determinant of an orthogonal transformation is a unit (`Unitary.det_ne_zero`), so an
orthogonal transformation either lies in the special orthogonal group or has negative determinant.
When `V` is finite-dimensional the determinant squares to `1` (`Unitary.det_mul_self`), so the
special orthogonal group consists of the orthogonal transformations of determinant `1`
(`TauCeti.mem_specialOrthogonalGroup_iff_det_eq_one`).
-/

public section

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The determinant of operators of `V`, restricted to the orthogonal group, as a homomorphism to
the units of `ℝ`. -/
private def detUnits : unitary (V →L[ℝ] V) →* ℝˣ :=
  MonoidHom.toHomUnits <| LinearMap.det.comp <|
    (ContinuousLinearMap.toLinearMapRingHom : (V →L[ℝ] V) →+* _).toMonoidHom.comp
      (unitary (V →L[ℝ] V)).subtype

private theorem coe_detUnits (g : unitary (V →L[ℝ] V)) :
    (detUnits g : ℝ) = (g : V →L[ℝ] V).det :=
  rfl

/-- The determinant of an orthogonal transformation is nonzero. -/
theorem Unitary.det_ne_zero (g : unitary (V →L[ℝ] V)) : (g : V →L[ℝ] V).det ≠ 0 :=
  coe_detUnits g ▸ (detUnits g).ne_zero

/-- The determinant of an orthogonal transformation of a finite-dimensional space squares to `1`:
the adjoint is the inverse and has the same determinant. -/
theorem Unitary.det_mul_self [FiniteDimensional ℝ V] (g : unitary (V →L[ℝ] V)) :
    (g : V →L[ℝ] V).det * (g : V →L[ℝ] V).det = 1 := by
  have h := congrArg ContinuousLinearMap.det (Unitary.coe_star_mul_self g)
  have ha : ((ContinuousLinearMap.adjoint (g : V →L[ℝ] V) : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      LinearMap.adjoint ((g : V →L[ℝ] V) : V →ₗ[ℝ] V) := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    -- The continuous linear map built from the underlying linear map of `g` is `g` itself.
    rfl
  rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.det, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_mul, map_mul, ha, LinearMap.det_adjoint, star_trivial,
    ContinuousLinearMap.toLinearMap_one, map_one] at h

namespace TauCeti

variable (V) in
/-- The special orthogonal group of the real inner product space `V`: the orthogonal
transformations of positive determinant, as a subgroup of the unitary group of `V →L[ℝ] V`.
For finite-dimensional `V` these are the orthogonal transformations of determinant `1`
(`TauCeti.mem_specialOrthogonalGroup_iff_det_eq_one`). -/
def specialOrthogonalGroup : Subgroup (unitary (V →L[ℝ] V)) :=
  (Units.posSubgroup ℝ).comap detUnits

/-- An orthogonal transformation lies in the special orthogonal group exactly when its
determinant is positive. -/
@[simp]
theorem mem_specialOrthogonalGroup_iff {g : unitary (V →L[ℝ] V)} :
    g ∈ specialOrthogonalGroup V ↔ 0 < (g : V →L[ℝ] V).det := by
  rw [specialOrthogonalGroup, Subgroup.mem_comap, Units.mem_posSubgroup, coe_detUnits]

/-- For finite-dimensional `V`, the special orthogonal group consists of the orthogonal
transformations of determinant `1`. -/
theorem mem_specialOrthogonalGroup_iff_det_eq_one [FiniteDimensional ℝ V]
    {g : unitary (V →L[ℝ] V)} : g ∈ specialOrthogonalGroup V ↔ (g : V →L[ℝ] V).det = 1 := by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ one_pos⟩
  exact (mul_self_eq_one_iff.1 (Unitary.det_mul_self g)).resolve_right fun h' ↦ by linarith

/-- An orthogonal transformation outside the special orthogonal group has negative
determinant. -/
theorem det_neg_of_notMem_specialOrthogonalGroup {g : unitary (V →L[ℝ] V)}
    (hg : g ∉ specialOrthogonalGroup V) : (g : V →L[ℝ] V).det < 0 :=
  (Unitary.det_ne_zero g).lt_of_le (not_lt.1 (mem_specialOrthogonalGroup_iff.not.1 hg))

end TauCeti
