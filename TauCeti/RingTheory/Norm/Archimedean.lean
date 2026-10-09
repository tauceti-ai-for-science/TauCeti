/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.Complex
public import TauCeti.RingTheory.Norm.Equiv
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Norm groups of finite real extensions

Every finite extension of `ℝ` is isomorphic to `ℝ` or `ℂ`, by Mathlib's
`Real.nonempty_algEquiv_or`. Its norm group is therefore all real units in degree one,
and the positive units in degree two. In both cases its norm index equals its degree.
The degree-two computation uses `TauCeti.normGroup_real_complex` and Mathlib's
`Units.index_posSubgroup`.

The same description holds over any field `K` identified with `ℝ` by a ring isomorphism `e`, such
as the completion of a number field at a real place: the norm group of a finite extension of degree
two consists of the units that `e` sends to positive reals (`normGroup_eq_of_ringEquiv_real`).
-/

public section

namespace TauCeti

/-- The norm group of a finite real extension is all real units in degree one and the
positive real units in degree two. -/
theorem normGroup_real_eq (L : Type*) [Field L] [Algebra ℝ L] [FiniteDimensional ℝ L] :
    normGroup ℝ L = if Module.finrank ℝ L = 1 then ⊤ else Units.posSubgroup ℝ := by
  rcases Real.nonempty_algEquiv_or L with h | h
  · obtain ⟨e⟩ := h
    rw [e.normGroup_eq, e.toLinearEquiv.finrank_eq, Module.finrank_self, ite_eq_left rfl,
      normGroup_self]
  · obtain ⟨e⟩ := h
    rw [e.normGroup_eq, e.toLinearEquiv.finrank_eq, Complex.finrank_real_complex,
      ite_eq_right (by decide), normGroup_real_complex]

/-- The norm index of every finite extension of the reals equals its degree. -/
@[simp]
theorem index_normGroup_real (L : Type*) [Field L] [Algebra ℝ L] [FiniteDimensional ℝ L] :
    (normGroup ℝ L).index = Module.finrank ℝ L := by
  rcases Real.nonempty_algEquiv_or L with h | h
  · obtain ⟨e⟩ := h
    rw [normGroup_real_eq, e.toLinearEquiv.finrank_eq, Module.finrank_self, ite_eq_left rfl,
      Subgroup.index_top]
  · obtain ⟨e⟩ := h
    rw [normGroup_real_eq, e.toLinearEquiv.finrank_eq, Complex.finrank_real_complex,
      ite_eq_right (by decide), Units.index_posSubgroup]

/-- The norm group of a finite extension of a field `K` identified with `ℝ` by a ring isomorphism
`e` is all of `Kˣ` in degree one, and the units that `e` sends to positive reals in degree two. -/
theorem normGroup_eq_of_ringEquiv_real {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (e : K ≃+* ℝ) :
    normGroup K L = if Module.finrank K L = 1 then ⊤ else
      (Units.posSubgroup ℝ).comap (Units.map e.toMonoidHom) := by
  -- Make `L` an `ℝ`-algebra through `e⁻¹`, so that `e` carries `N_{L/K}` to `N_{L/ℝ}`.
  let _ : Algebra ℝ K := e.symm.toRingHom.toAlgebra
  let _ : Algebra ℝ L := ((algebraMap K L).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower ℝ K L := .of_algebraMap_eq' rfl
  let f : ℝ ≃ₐ[ℝ] K := AlgEquiv.ofRingEquiv (f := e.symm) fun _ ↦ rfl
  have : Module.Finite ℝ K := .equiv f.toLinearEquiv
  have : Module.Finite ℝ L := .trans K L
  have hrank : Module.finrank ℝ L = Module.finrank K L := by
    rw [← Module.finrank_mul_finrank ℝ K L, ← f.toLinearEquiv.finrank_eq, Module.finrank_self,
      one_mul]
  have hnorm (y : L) : e (Algebra.norm K y) = Algebra.norm ℝ y :=
    Algebra.norm_eq_of_ringEquiv e (by ext; simp [RingHom.algebraMap_toAlgebra]) y
  have hmem (x : Kˣ) : x ∈ normGroup K L ↔ Units.map e.toMonoidHom x ∈ normGroup ℝ L := by
    simp only [mem_normGroup_iff, Units.coe_map, ← hnorm]
    exact exists_congr fun y ↦ e.injective.eq_iff.symm
  ext x
  rw [hmem, normGroup_real_eq, hrank]
  split_ifs <;> simp

end TauCeti
