/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import TauCeti.RingTheory.Cyclotomic.ComplexField
import TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# Cyclotomic polynomials over a subfield of `ℂ` meeting `ℚ(ζ_n)` in `ℚ`

Let `F ⊆ ℂ` be a finite extension of `ℚ` with `F ∩ ℚ(ζ_n) = ℚ`. As `ℚ(ζ_n)` is Galois over `ℚ`,
the two fields are linearly disjoint, so `[F(ζ_n) : F] = [ℚ(ζ_n) : ℚ] = φ(n)`. Since `F(ζ_n)` is
an `n`-th cyclotomic extension of `F`, the cyclotomic polynomial `Φ_n` is irreducible over `F`
(`IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank`).

## Main results

* `TauCeti.Cyclotomic.finrank_adjoin_complexRoot_of_inf_eq_bot`: `[F(ζ_n) : F] = φ(n)`.
* `TauCeti.Cyclotomic.irreducible_cyclotomic_of_inf_eq_bot`: `Φ_n` is irreducible over `F`.

## References

* S. Lang, *Algebra*, revised 3rd ed., Springer GTM 211 (2002), Chapter VI, Theorem 1.12
  (translation of a Galois extension) and Chapter VI, §3 (cyclotomic extensions).
-/

public section

open IntermediateField Polynomial

namespace TauCeti.Cyclotomic

variable {n : ℕ} (F : IntermediateField ℚ ℂ)

/-- The field `F(ζ_n)` generated over `F` by `ζ_n = complexRoot n` is generated over `F` by the
whole cyclotomic field `ℚ(ζ_n)`. -/
theorem adjoin_complexField_eq :
    adjoin F (complexField n : Set ℂ) = F⟮complexRoot n⟯ := by
  refine le_antisymm (adjoin_le_iff.2 fun x hx ↦ ?_)
    (adjoin_simple_le_iff.2 (subset_adjoin _ _ (complexRoot_mem_complexField n)))
  have h : complexField n ≤ (F⟮complexRoot n⟯).restrictScalars ℚ :=
    complexField_def n ▸ adjoin_simple_le_iff.2 (mem_adjoin_simple_self F (complexRoot n))
  exact h hx

variable [NeZero n] [FiniteDimensional ℚ F]

/-- If `F ∩ ℚ(ζ_n) = ℚ`, then `[F(ζ_n) : F] = φ(n)`. -/
theorem finrank_adjoin_complexRoot_of_inf_eq_bot (h : F ⊓ complexField n = ⊥) :
    Module.finrank F F⟮complexRoot n⟯ = n.totient := by
  have : IsGalois ℚ (complexField n) := IsCyclotomicExtension.isGalois {n} ℚ _
  have hdisj : (complexField n).LinearDisjoint F :=
    LinearDisjoint.of_inf_eq_bot (by rwa [inf_comm])
  have hrank := hdisj.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  rw [adjoin_complexField_eq] at hrank
  rw [← IsCyclotomicExtension.Rat.finrank n (complexField n)]
  exact congrArg Cardinal.toNat hrank

/-- **Cyclotomic polynomials stay irreducible over a field meeting `ℚ(ζ_n)` in `ℚ`.** If a finite
extension `F ⊆ ℂ` of `ℚ` satisfies `F ∩ ℚ(ζ_n) = ℚ`, then `Φ_n` is irreducible over `F`. -/
theorem irreducible_cyclotomic_of_inf_eq_bot (h : F ⊓ complexField n = ⊥) :
    Irreducible (cyclotomic n F) := by
  have : IsCyclotomicExtension {n} F F⟮complexRoot n⟯ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin n F ℂ _
      isPrimitiveRoot_complexRoot).2 rfl
  exact IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank F F⟮complexRoot n⟯
    (finrank_adjoin_complexRoot_of_inf_eq_bot F h).ge

end TauCeti.Cyclotomic
