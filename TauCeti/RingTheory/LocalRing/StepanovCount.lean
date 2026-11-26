/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Stepanov's count of zeros at the residue classes of a local ring

A non-zero polynomial over a field with zeros of multiplicity at least `E` at `q` distinct points
has degree at least `E q`; this comparison of zeros against degree is the counting step of
Stepanov's method. Here it is stated over an arbitrary commutative ring `R`, at the images under a
ring map `ι : W → R` of the residue classes of a local ring `W`: representatives of distinct
residue classes differ by units of `W`, so their images differ by units of `R`, and the polynomials
`(X - ι y) ^ E` are pairwise coprime.

## Main results

* `TauCeti.stepanov_count`: if `X ^ E` divides `Φ(X + ι y)` for every `y ∈ W` and `Φ ≠ 0`, then
  `E q ≤ deg Φ`, where `q` is the number of residue classes of `W`.

## References

* W. M. Schmidt, *Equations over finite fields: an elementary approach*, Lecture Notes in
  Mathematics 536, Springer (1976), Chapter I.
* E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*,
  Séminaire Bourbaki, exp. 430 (1973).

The statement and its proof are adapted from `New.stepanov_count` in the file
`New/UpperBound/ElementaryDivisors/RootLemma.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Polynomial IsLocalRing Function

/-- **Stepanov's count.** Let `W` be a local ring with `q` residue classes and `ι : W → R` a ring
map to a commutative ring. If a non-zero polynomial `Φ` over `R` has `X ^ E ∣ Φ(X + ι y)` for every
`y ∈ W`, that is, a zero of order at least `E` at every point `ι y`, then `E q ≤ deg Φ`. For an
infinite residue field `q` is read as `Nat.card = 0` and the statement is empty. -/
theorem stepanov_count {R W : Type*} [CommRing R] [CommRing W] [IsLocalRing W] (ι : W →+* R)
    {Φ : R[X]} (E : ℕ) (hΦ : Φ ≠ 0) (h_zero : ∀ y : W, X ^ E ∣ Φ.comp (X + C (ι y))) :
    E * Nat.card (ResidueField W) ≤ Φ.natDegree := by
  -- Lift the residue classes to points `a x` of `R` with unit differences. The coprime polynomials
  -- `(X - a x) ^ E` all divide `Φ`, hence so does their product, monic of degree `E q`.
  cases fintypeOrInfinite (ResidueField W) with
  | inr _ => simp
  | inl _ =>
  have : Nontrivial R := Nontrivial.of_polynomial_ne hΦ
  let a (x : ResidueField W) : R := ι (surjInv residue_surjective x)
  have h_unit (x y : ResidueField W) (hxy : x ≠ y) : IsUnit (a x - a y) := by
    rw [← map_sub]
    exact .map ι (by simpa [sub_eq_zero, ← residue_ne_zero_iff_isUnit, surjInv_eq] using hxy)
  have h_dvd : ∏ x : ResidueField W, (X - C (a x)) ^ E ∣ Φ := Fintype.prod_dvd_of_coprime
    (fun x y hxy ↦ (isCoprime_X_sub_C_of_isUnit_sub (h_unit x y hxy)).pow)
    fun x ↦ X_sub_C_pow_dvd_iff.2 (h_zero _)
  have h_monic : (∏ x : ResidueField W, (X - C (a x))).Monic := monic_prod_X_sub_C a _
  by_contra! h_lt
  exact (h_monic.pow E).not_dvd_of_natDegree_lt hΦ (by simpa [h_monic.natDegree_pow] using h_lt)
    (by rwa [← Finset.prod_pow])

end TauCeti
