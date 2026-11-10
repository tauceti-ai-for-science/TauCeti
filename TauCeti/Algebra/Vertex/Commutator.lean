/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.Dong

/-!
# The commutator formula in a formal vertex algebra

For states `a` and `b` of a formal vertex algebra and `j ≥ 0`, the field of the state `a₍ⱼ₎b`
is the `j`th residue product of the fields of `a` and `b`:

`Y(a₍ⱼ₎b, z) = Res_x (x - z)ʲ [Y(a,x), Y(b,z)]`

(`TauCeti.FormalVertexAxioms.field_ncoeff_natCast_apply`). Combined with the delta expansion of
the commutator of local fields, this gives the **commutator formula**

`[a₍ₘ₎, b₍ₙ₎] = ∑_{j ≥ 0} (m choose j) (a₍ⱼ₎b)₍ₘ₊ₙ₋ⱼ₎`

for all integers `m` and `n` (`TauCeti.FormalVertexAxioms.ncoeff_field_mul_sub_mul`). The sum is
finite: `a₍ⱼ₎b = 0` for all large `j`. The commutator formula is a special case of the Borcherds
identity.

The proof applies Goddard's uniqueness theorem to the residue product. Dong's lemma makes it
local to every field, it is translation covariant by the Leibniz rule, and its values on the
vacuum are computed from the creation axiom. Identifying a translation covariant field from its
value on the vacuum divides by factorials, so the module is assumed torsion-free
(`HasUniqueDiv`).

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., Chapter 4, for the `n`th product identity
  and the commutator formula.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., Chapter 3.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset VertexOperator

namespace TauCeti.FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-- Residue products of fields of a formal vertex algebra are translation covariant. -/
private theorem lie_translation_ncoeff_nonnegResidueProduct (a b : V) (j : ℕ) (m : ℤ) :
    ⁅A.translation, (nonnegResidueProduct j (A.field a) (A.field b))[[m]]⁆ =
      (derivative (nonnegResidueProduct j (A.field a) (A.field b)))[[m]] := by
  rw [lie_ncoeff_nonnegResidueProduct _ (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b),
    derivative_nonnegResidueProduct]

/-- On the vacuum, a residue product of fields of a formal vertex algebra only involves the modes
of the first field after those of the second. -/
private theorem ncoeff_nonnegResidueProduct_apply_vacuum (a b : V) (j : ℕ) (m : ℤ) :
    ((nonnegResidueProduct j (A.field a) (A.field b))[[m]]) A.vacuum =
      ∑ ij ∈ antidiagonal j, j.choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((A.field a)[[(ij.1 : ℤ)]]) (((A.field b)[[m + ij.2]]) A.vacuum) := by
  simp only [ncoeff_nonnegResidueProduct, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, mul_apply_eq_comp]
  refine sum_congr rfl fun ij _ ↦ ?_
  rw [A.ncoeff_field_apply_vacuum_of_nonneg a _ (by positivity), map_zero, sub_zero]

/-- **The `j`th product identity** for `j ≥ 0`: the field of `a₍ⱼ₎b` is the `j`th residue
product `Y(a,z)₍ⱼ₎Y(b,z) = Res_x (x - z)ʲ [Y(a,x), Y(b,z)]`. -/
theorem field_ncoeff_natCast_apply [HasUniqueDiv V] (a b : V) (j : ℕ) :
    A.field (((A.field a)[[(j : ℤ)]]) b) = nonnegResidueProduct j (A.field a) (A.field b) := by
  have hloc (c : V) : ∃ N, (nonnegResidueProduct j (A.field a) (A.field b)).IsLocalOfOrder
      (A.field c) N := by
    obtain ⟨N₁, h₁⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨N₂, h₂⟩ := A.exists_isLocalOfOrder a c
    obtain ⟨N₃, h₃⟩ := A.exists_isLocalOfOrder b c
    exact ⟨_, isLocalOfOrder_nonnegResidueProduct h₁ h₂ h₃ j⟩
  have hvac₀ (m : ℤ) (hm : 0 ≤ m) :
      ((nonnegResidueProduct j (A.field a) (A.field b))[[m]]) A.vacuum = 0 := by
    rw [A.ncoeff_nonnegResidueProduct_apply_vacuum]
    refine sum_eq_zero fun ij _ ↦ ?_
    rw [A.ncoeff_field_apply_vacuum_of_nonneg b _ (by positivity), map_zero, smul_zero,
      smul_zero]
  -- On the vacuum, the mode `-1` of the residue product only keeps the term `a₍ⱼ₎b`.
  have hvac : ((nonnegResidueProduct j (A.field a) (A.field b))[[-1]]) A.vacuum =
      ((A.field a)[[(j : ℤ)]]) b := by
    rw [A.ncoeff_nonnegResidueProduct_apply_vacuum, sum_eq_single (j, 0)]
    · simp
    · intro ij hij hne
      have hij₂ : ij.2 ≠ 0 := fun h ↦ hne (Prod.ext (by simpa [h] using mem_antidiagonal.1 hij) h)
      rw [A.ncoeff_field_apply_vacuum_of_nonneg b _ (by omega), map_zero, smul_zero, smul_zero]
    · simp
  conv_rhs => rw [A.eq_field_of_lie hloc (A.lie_translation_ncoeff_nonnegResidueProduct a b j)
    hvac₀, hvac]

/-- **The commutator formula** in a formal vertex algebra:
`[a₍ₘ₎, b₍ₙ₎] = ∑_{j < N} (m choose j) (a₍ⱼ₎b)₍ₘ₊ₙ₋ⱼ₎`, for every `N` with `a₍ⱼ₎b = 0` for all
`j ≥ N`. The binomial coefficients are integer binomial coefficients, so negative `m` is
allowed. -/
theorem ncoeff_field_mul_sub_mul [HasUniqueDiv V] (a b : V) {N : ℕ}
    (hN : ∀ j : ℕ, N ≤ j → ((A.field a)[[(j : ℤ)]]) b = 0) (m n : ℤ) :
    (A.field a)[[m]] * (A.field b)[[n]] - (A.field b)[[n]] * (A.field a)[[m]] =
      ∑ j ∈ range N, Ring.choose m j • (A.field (((A.field a)[[(j : ℤ)]]) b))[[m + n - j]] := by
  obtain ⟨L, hL⟩ := A.exists_isLocalOfOrder a b
  rw [(hL.mono (le_max_left L N)).ncoeff_mul_sub_mul m n]
  simp only [← A.field_ncoeff_natCast_apply]
  refine (sum_subset (range_mono (le_max_right L N)) fun j _ hj ↦ ?_).symm
  rw [hN j (by simpa using hj), map_zero, map_zero, Pi.zero_apply, smul_zero]

end TauCeti.FormalVertexAxioms
