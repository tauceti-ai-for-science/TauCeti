/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ColumnRowFixing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Block triangular, Levi, parahoric and root subgroups of a general linear group

Label the indices of `GL_ι(R)` by a function `τ : ι → α` to a linear order. This file defines the
following subgroups of `GL_ι(R)`.

* `TauCeti.blockTriangularSubgroup R b`: the invertible matrices that are block triangular for
  `b` in the sense of `Matrix.BlockTriangular` (the entry `(i, j)` vanishes when `b j < b i`).
* `TauCeti.leviSubgroup R τ`: the matrices whose entry `(i, j)` vanishes whenever `τ i ≠ τ j`,
  the Levi subgroup `L_τ(R)` of the labelling.
* `TauCeti.parahoricSubgroup W τ`: for a local ring `W`, the matrices whose entry `(i, j)` lies in
  the maximal ideal whenever `τ i < τ j`, the parahoric subgroup `P_τ(W)`: the preimage of a block
  triangular subgroup over the residue field.
* `TauCeti.rootSL R a a'`: the matrices of determinant `1` that agree with the identity matrix
  outside the rows and columns `a`, `a'`, a copy of `SL₂(R)` in `GL_ι(R)`.

## Main results

* `TauCeti.mem_parahoricSubgroup_iff`: the entries above the diagonal blocks lie in the maximal
  ideal.
* `TauCeti.rootSL_le_leviSubgroup`: the root subgroup of two indices with the same label lies in the
  Levi subgroup.
-/

@[expose] public section

namespace TauCeti

open Matrix IsLocalRing

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder α]

section BlockTriangular

variable (R : Type*) [CommRing R]

/-- The invertible matrices that are block triangular for the labelling `b` of the indices: the
entry `(i, j)` vanishes whenever `b j < b i`. -/
def blockTriangularSubgroup (b : ι → α) : Subgroup (GL ι R) where
  carrier := {g | (g : Matrix ι ι R).BlockTriangular b}
  one_mem' := blockTriangular_one
  mul_mem' hg hh := by simpa using hg.mul hh
  inv_mem' {g} hg := by
    simpa only [Set.mem_ofPred_eq, coe_units_inv] using blockTriangular_inv_of_blockTriangular hg

variable {R}

@[simp]
theorem mem_blockTriangularSubgroup_iff {b : ι → α} {g : GL ι R} :
    g ∈ blockTriangularSubgroup R b ↔ (g : Matrix ι ι R).BlockTriangular b :=
  Iff.rfl

variable (R) in
/-- The Levi subgroup `L_τ(R)` of a labelling `τ` of the indices: the invertible matrices whose
entry `(i, j)` vanishes whenever `τ i ≠ τ j`. -/
def leviSubgroup (τ : ι → α) : Subgroup (GL ι R) where
  carrier := {g | ∀ i j, τ i ≠ τ j → (g : Matrix ι ι R) i j = 0}
  one_mem' _ _ h := one_apply_ne (ne_of_apply_ne τ h)
  mul_mem' {g h} hg hh i j hij := by
    -- Each term `g i l * h l j` has `τ l ≠ τ i` or `τ l ≠ τ j`.
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rcases eq_or_ne (τ i) (τ l) with hil | hil
    · exact mul_eq_zero_of_right _ (hh l j (hil ▸ hij))
    · exact mul_eq_zero_of_left (hg i l hil) _
  inv_mem' {g} hg i j hij := by
    -- `g` is block triangular for `τ` and for the reversed order, and so is its inverse.
    have h_up : g ∈ blockTriangularSubgroup R τ := fun _ _ h ↦ hg _ _ h.ne'
    have h_down : g ∈ blockTriangularSubgroup R (OrderDual.toDual ∘ τ) :=
      fun _ _ h ↦ hg _ _ (ne_of_lt (α := α) h)
    rcases hij.lt_or_gt with h | h
    · exact (inv_mem h_down) (show OrderDual.toDual (τ j) < OrderDual.toDual (τ i) from h)
    · exact (inv_mem h_up) h

@[simp]
theorem mem_leviSubgroup_iff {τ : ι → α} {g : GL ι R} :
    g ∈ leviSubgroup R τ ↔ ∀ i j, τ i ≠ τ j → (g : Matrix ι ι R) i j = 0 :=
  Iff.rfl

end BlockTriangular

section Parahoric

variable (W : Type*) [CommRing W] [IsLocalRing W]

/-- The parahoric subgroup `P_τ(W)` of a labelling `τ` of the indices, for a local ring `W`: the
invertible matrices whose entry `(i, j)` lies in the maximal ideal whenever `τ i < τ j`. It is
the preimage of the block lower triangular matrices over the residue field. -/
def parahoricSubgroup (τ : ι → α) : Subgroup (GL ι W) :=
  (blockTriangularSubgroup (ResidueField W) (OrderDual.toDual ∘ τ)).comap
    (GeneralLinearGroup.map (residue W))

variable {W}

theorem mem_parahoricSubgroup_iff {τ : ι → α} {g : GL ι W} :
    g ∈ parahoricSubgroup W τ ↔ ∀ i j, τ i < τ j → (g : Matrix ι ι W) i j ∈ maximalIdeal W := by
  simp only [parahoricSubgroup, Subgroup.mem_comap, mem_blockTriangularSubgroup_iff,
    BlockTriangular, Function.comp_apply, OrderDual.toDual_lt_toDual,
    ← residue_eq_zero_iff]
  rfl

/-- The Levi subgroup lies in the parahoric subgroup. -/
theorem leviSubgroup_le_parahoricSubgroup (τ : ι → α) : leviSubgroup W τ ≤ parahoricSubgroup W τ :=
  fun _ hg ↦ mem_parahoricSubgroup_iff.2 fun i j h ↦ by simp [hg i j h.ne]

end Parahoric

section Root

variable (R : Type*) [CommRing R]

/-- The group `SL₂(R)` placed in the rows and columns `a`, `a'` of `GL_ι(R)`: the matrices of
determinant `1` that agree with the identity matrix at `(i, j)` unless both `i` and `j` are among
`a`, `a'`. It is trivial for `a = a'`. -/
def rootSL (a a' : ι) : Subgroup (GL ι R) :=
  columnRowFixingSubgroup R ({a, a'}ᶜ : Set ι) {a, a'}ᶜ ⊓ GeneralLinearGroup.det.ker

variable {R}

theorem mem_rootSL_iff {a a' : ι} {g : GL ι R} :
    g ∈ rootSL R a a' ↔
      (∀ i j, (i ≠ a ∧ i ≠ a') ∨ (j ≠ a ∧ j ≠ a') → (g : Matrix ι ι R) i j = (1 : Matrix ι ι R) i j)
        ∧ (g : Matrix ι ι R).det = 1 := by
  simp only [rootSL, Subgroup.mem_inf, mem_columnRowFixingSubgroup_iff, MonoidHom.mem_ker,
    Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
  constructor
  · rintro ⟨⟨hc, hr⟩, hdet⟩
    exact ⟨fun i j h ↦ h.elim (fun hi ↦ hr i (by simpa using hi) j)
      (fun hj ↦ hc j (by simpa using hj) i), hdet⟩
  · rintro ⟨h, hdet⟩
    exact ⟨⟨fun j hj i ↦ h i j (.inr (by simpa using hj)),
      fun i hi j ↦ h i j (.inl (by simpa using hi))⟩, hdet⟩

/-- The root subgroup of two indices with the same label lies in the Levi subgroup. -/
theorem rootSL_le_leviSubgroup {τ : ι → α} {a a' : ι} (hτ : τ a = τ a') :
    rootSL R a a' ≤ leviSubgroup R τ :=
  fun _ hg i j hij ↦ ((mem_rootSL_iff.1 hg).1 i j (by grind)).trans
    (one_apply_ne (ne_of_apply_ne τ hij))

end Root

end TauCeti
