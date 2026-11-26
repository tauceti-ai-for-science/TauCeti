/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.NumberTheory.Padics.Cardinality

/-!
# Pairs of a prime and an isomorphism `ℂ ≃ PadicAlgCl ℓ`

A *pair* `ι` is a prime `ℓ = ι.prime` with a field isomorphism `ι : ℂ ≃+* PadicAlgCl ℓ` onto
Mathlib's algebraic closure `PadicAlgCl ℓ` of `ℚ_[ℓ]`. Such isomorphisms exist (both fields are
algebraically closed of characteristic zero with the cardinality of the continuum) and are not
continuous. Through `ι`, the `ℓ`-adic absolute value is read on `ℂ`: the complex numbers `z` with
`‖ι z‖ ≤ 1` form a valuation ring `𝒪_ι` of `ℂ`, which is not noetherian. The pair `ι.conj`, with
`ι.conj z = ι (conj z)`, has the same prime.

The pairs serve as the finite places of `ℂ` in a product formula: a complex number whose images
under all pairs at one prime are bounded is algebraic
(`TauCeti.PrimePadicIso.isAlgebraic_of_norm_le`), since a transcendental number can be sent to
any transcendental element of `PadicAlgCl ℓ`, and these have unbounded norm.

## Main definitions

* `TauCeti.PrimePadicIso`: a prime `ℓ` with an isomorphism `ℂ ≃+* PadicAlgCl ℓ`.
* `TauCeti.PrimePadicIso.conj`: the pair `ι.conj`, with `ι.conj z = ι (conj z)`.
* `TauCeti.PrimePadicIso.integers`: the valuation ring `𝒪_ι = {z : ‖ι z‖ ≤ 1}` of `ℂ`.

## Main results

* `TauCeti.PrimePadicIso.isAlgebraic_of_norm_le`: if the images of `x : ℂ` under all isomorphisms
  `ℂ ≃+* PadicAlgCl ℓ`, for one prime `ℓ`, are bounded, then `x` is algebraic over `ℚ`.

## References

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC): `New.PrimePadicIso` and `New.PrimePadicIso.conj`, `New.PrimePadicIso.integers` in
`New/Reduction/Lattices/{Heights,TwistedLattice}.lean`, and
`New.isAlgebraic_of_norm_complexToCp_le` in `Lib/General/NumberTheory/PadicLimitsValuation.lean`.
-/

@[expose] public section

noncomputable section

open Cardinal

namespace TauCeti

/-- A *pair*: a prime `ℓ` together with a field isomorphism `ℂ ≃+* PadicAlgCl ℓ` onto the algebraic
closure `PadicAlgCl ℓ` of `ℚ_[ℓ]`. -/
structure PrimePadicIso : Type where
  /-- The prime `ℓ`. -/
  prime : ℕ
  [fact_prime : Fact prime.Prime]
  /-- The isomorphism `ℂ ≃+* PadicAlgCl ℓ`. -/
  iso : ℂ ≃+* PadicAlgCl prime

namespace PrimePadicIso

attribute [instance] fact_prime

variable (ι : PrimePadicIso)

/-- The pair `ι.conj` with the same prime and `ι.conj z = ι (conj z)`. -/
def conj : PrimePadicIso := ⟨ι.prime, starRingAut.trans ι.iso⟩

@[simp]
theorem prime_conj : ι.conj.prime = ι.prime := rfl

theorem conj_iso_apply (z : ℂ) : ι.conj.iso z = ι.iso (starRingEnd ℂ z) := rfl

/-- The valuation ring `𝒪_ι = {z ∈ ℂ : ‖ι z‖ ≤ 1}` of the absolute value that `ι` induces on
`ℂ`. -/
def integers : ValuationSubring ℂ :=
  ((Valued.v : Valuation (PadicAlgCl ι.prime) NNReal).comap ι.iso.toRingHom).valuationSubring

@[simp]
theorem mem_integers {z : ℂ} : z ∈ ι.integers ↔ ‖ι.iso z‖ ≤ 1 := by
  simp [integers, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe,
    PadicAlgCl.valuation_coe]

/-- The prime `ℓ` of a pair has absolute value `ℓ⁻¹` under the pair. -/
theorem norm_iso_natCast_prime : ‖ι.iso ι.prime‖ = (ι.prime : ℝ)⁻¹ := by
  rw [map_natCast, ← map_natCast (algebraMap ℚ_[ι.prime] (PadicAlgCl ι.prime)),
    PadicAlgCl.norm_extends, Padic.norm_p]

/-- If `x` divides `ℓ ^ j` in the valuation ring `𝒪_ι`, then `|ι x| ≥ ℓ ^ (-j)`. -/
theorem inv_pow_le_norm_of_dvd {x : ι.integers} {j : ℕ}
    (hx : x ∣ (ι.prime : ι.integers) ^ j) : ((ι.prime : ℝ) ^ j)⁻¹ ≤ ‖ι.iso x‖ := by
  obtain ⟨c, hc⟩ := hx
  have hc' : ‖ι.iso c‖ ≤ 1 := (mem_integers ι).1 c.property
  have h := congrArg (fun y : ι.integers ↦ ‖ι.iso y‖) hc
  have hp : ((ι.prime : ι.integers) : ℂ) = ι.prime := map_natCast ι.integers.subtype _
  simp only [SubmonoidClass.coe_pow, map_pow, norm_pow, MulMemClass.coe_mul, map_mul, norm_mul,
    hp, norm_iso_natCast_prime, inv_pow] at h
  rw [h]
  exact mul_le_of_le_one_right (norm_nonneg _) hc'

/-- **An `ℓ`-adic criterion for algebraicity.** Let `ℓ` be a prime. If the images of `x : ℂ` under
all field isomorphisms `ℂ ≃+* PadicAlgCl ℓ` have a common bound, then `x` is algebraic over `ℚ`. -/
theorem isAlgebraic_of_norm_le {ℓ : ℕ} [Fact ℓ.Prime] {x : ℂ} {c : ℝ}
    (h_bound : ∀ ι : ℂ ≃+* PadicAlgCl ℓ, ‖ι x‖ ≤ c) : IsAlgebraic ℚ x := by
  by_contra hx
  -- the algebraic elements are countable, so the others are dense; take one of norm `> c`
  obtain ⟨y, hy, hcy⟩ : ∃ y : PadicAlgCl ℓ, ¬IsAlgebraic ℚ y ∧ c < ‖y‖ :=
    ((Algebraic.countable ℚ (PadicAlgCl ℓ)).dense_compl ℚ_[ℓ]).exists_mem_open
      (isOpen_Ioi.preimage continuous_norm) (NormedField.exists_lt_norm _ c)
  -- an isomorphism over `ℚ` sends `y` to `x`
  obtain ⟨φ, hφ⟩ := Complex.exists_algEquiv_apply_eq (k := ℚ)
    (Padic.cardinalMk_eq_continuum_of_isAlgebraic ℓ (PadicAlgCl ℓ)) hy hx
  exact hcy.not_ge (by simpa [← hφ] using h_bound φ.symm.toRingEquiv)

end PrimePadicIso

end TauCeti

end
