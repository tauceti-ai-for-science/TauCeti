/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.PrimePadicIso
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.NumberTheory.Padics.Cardinality

/-!
# Heights of families over all pairs

A *pair* `ι` is a prime `ℓ = ι.prime` with a field isomorphism `ι.iso : ℂ ≃+* PadicAlgCl ℓ`
(`TauCeti.PrimePadicIso`). A family `y = (y_ι)` of complex numbers, one for each pair, has *height
at most `c`* (`TauCeti.HeightLe c y`) if there are a multiplier `H ≠ 0`, a real number `α` and
numbers `h_ℓ ≥ 0`, one for each prime, with `|σ H| ≤ e^α` for every automorphism `σ` of `ℂ`,
`|ι (H y_ι)| ≤ ℓ^{h_ℓ}` for every pair `ι`, and `α + ∑_{ℓ ∈ S} h_ℓ log ℓ ≤ c` for every finite set
`S` of primes. Only this upper bound is defined. The multiplier, and so the bound at infinity, is
common to all pairs, while `y_ι` may depend on the pair, so that each prime may be read through its
own twist.

Heights add under products, and the product formula for `ℚ` makes them nonnegative on the
constant family `1`: the multiplier `H` is algebraic by the `ℓ`-adic criterion
`TauCeti.PrimePadicIso.isAlgebraic_of_norm_le`, and its norm `q` from `ℚ(H)` to `ℚ` is a product
of conjugates of `H`, each the image of `H` under an automorphism of `ℂ` or under a pair, because
every embedding of `ℚ(H)` extends to such a map (`TauCeti.Complex.exists_ringEquiv_apply_eq`).

## Main definitions

* `TauCeti.HeightLe c y`: the family `y` has height at most `c`.

## Main results

* `TauCeti.HeightLe.mono`, `TauCeti.HeightLe.rpow_mul`, `TauCeti.HeightLe.of_mul_le`,
  `TauCeti.HeightLe.inv_const`, `TauCeti.HeightLe.mul`, `TauCeti.HeightLe.prod`,
  `TauCeti.HeightLe.pow`: the calculus of heights.
* `Rat.log_add_sum_log_padicNorm_eq_zero`: the product formula for `ℚ` in logarithms,
  `log |q| + ∑_{p < B} log |q|_p = 0` for `B` above the numerator and the denominator of `q`.
* `TauCeti.HeightLe.nonneg_of_one`, `TauCeti.HeightLe.neg_le_of_norm_map_le`: the constant family
  `1` has nonnegative height, and so a number `z ≠ 0` of height at most `c` with conjugates at most
  `e^{c'}` has `-c ≤ c'`.

## References

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `New/Reduction/Lattices/Heights.lean` (`New.HeightLe` and the lemmas named after it,
`New.log_product_formula`). Related work: E. Gaudron, *Pentes des fibrés vectoriels adéliques sur
un corps global*, Rend. Sem. Mat. Univ. Padova 119 (2008); E. Bombieri and W. Gubler, *Heights in
Diophantine Geometry*, Chapter 1.
-/

public section

open Real Finset IntermediateField

/-- **The product formula for `ℚ`, in logarithms.** For `q : ℚ` and `B` larger than the absolute
value of the numerator and than the denominator of `q`, `log |q| + ∑_{p < B prime} log |q|_p = 0`.
For `q = 0` both terms vanish, as `log 0 = 0`. -/
theorem Rat.log_add_sum_log_padicNorm_eq_zero {B : ℕ} {q : ℚ} (h_num : q.num.natAbs < B)
    (h_den : q.den < B) : log q + ∑ p ∈ range B with p.Prime, log (padicNorm p q) = 0 := by
  -- the term of `p` in `log |q|` is `v_p(q) log p`, which cancels `log |q|_p = -v_p(q) log p`
  obtain rfl | hq := eq_or_ne q 0
  · simp
  have log_nat {n : ℕ} (hn : n ≠ 0) (hnB : n < B) :
      log n = ∑ p ∈ range B with p.Prime, multiplicity p n * log p := by
    conv_lhs => rw [← Nat.prod_pow_prime_multiplicity n hn B hnB]
    simp +contextual [log_prod, Nat.Prime.ne_zero]
  have log_q : log q = log q.num.natAbs - log q.den := by simp [q.cast_def, log_div, hq]
  have log_norm (p : ℕ) :
      log (padicNorm p q) = (multiplicity p q.den - multiplicity p q.num.natAbs) * log p := by
    simp [padicNorm.eq_zpow_of_ne_zero hq, padicValRat, padicValInt]
  rw [log_q, log_nat (by simpa using hq) h_num, log_nat q.den_nz h_den]
  simp [log_norm, sub_mul]

namespace TauCeti

variable {c c' : ℝ} {y y' : PrimePadicIso → ℂ}

/-- The family `y`, with one complex number for each pair `ι` of a prime `ℓ = ι.prime` and an
isomorphism `ι.iso : ℂ ≃+* PadicAlgCl ℓ`, has *height at most `c`*: there are a multiplier `H ≠ 0`
and real numbers `α` and `h ℓ ≥ 0` with `|σ H| ≤ e^α` for every automorphism `σ` of `ℂ`,
`|ι (H y_ι)| ≤ ℓ ^ h ℓ` for every pair `ι`, and `α + ∑_{ℓ ∈ S} h ℓ log ℓ ≤ c` for every finite set
`S` of primes. -/
@[expose] def HeightLe (c : ℝ) (y : PrimePadicIso → ℂ) : Prop :=
  ∃ (H : ℂ) (α : ℝ) (h : ℕ → ℝ), H ≠ 0 ∧ (∀ ℓ, 0 ≤ h ℓ) ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ exp α) ∧
    (∀ ι : PrimePadicIso, ‖ι.iso (H * y ι)‖ ≤ (ι.prime : ℝ) ^ h ι.prime) ∧
    ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → α + ∑ ℓ ∈ S, h ℓ * log ℓ ≤ c

namespace HeightLe

/-- If `y` has height at most `c ≤ c'` and `|ι (y' ι)| ≤ |ι (y ι)|` for every pair `ι`, then `y'`
has height at most `c'`. -/
theorem mono (hy : HeightLe c y) (hc : c ≤ c')
    (h_le : ∀ ι : PrimePadicIso, ‖ι.iso (y' ι)‖ ≤ ‖ι.iso (y ι)‖) : HeightLe c' y' := by
  obtain ⟨H, α, e, hH, he_nonneg, hα, he, h_sum⟩ := hy
  refine ⟨H, α, e, hH, he_nonneg, hα, fun ι ↦ ?_, fun S hS ↦ (h_sum S hS).trans hc⟩
  calc ‖ι.iso (H * y' ι)‖ ≤ ‖ι.iso (H * y ι)‖ := by
        simpa only [map_mul, norm_mul] using mul_le_mul_of_nonneg_left (h_le ι) (norm_nonneg _)
    _ ≤ (ι.prime : ℝ) ^ e ι.prime := he ι

/-- A positive integer prime to `ℓ` has absolute value `1` in `PadicAlgCl ℓ`. -/
private theorem norm_natCast_eq_one {ℓ N : ℕ} [Fact ℓ.Prime] (hN : ℓ.Coprime N) :
    ‖(N : PadicAlgCl ℓ)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)), PadicAlgCl.norm_extends,
    Padic.norm_natCast_eq_one_iff]
  exact hN

/-- If `y` has height at most `c ≤ c'`, then multiplying each `y ι` by a real power `N ι ^ e ι`,
with `e ι` rational and `N ι` a natural number prime to `ι.prime`, gives a family of height at most
`c'`. -/
theorem rpow_mul (hy : HeightLe c y) (hc : c ≤ c') {N : PrimePadicIso → ℕ}
    (hN : ∀ ι : PrimePadicIso, ι.prime.Coprime (N ι)) (e : PrimePadicIso → ℚ) :
    HeightLe c' fun ι ↦ ((N ι : ℝ) ^ (e ι : ℝ) : ℝ) * y ι := by
  -- the `(e ι).den`-th power of `N ι ^ e ι` is an integral power of `N ι`, a unit at `ι.prime`
  refine hy.mono hc fun ι ↦ ?_
  have h_exp : (e ι : ℝ) * (e ι).den = (e ι).num := mod_cast (e ι).mul_den_eq_num
  have h_pow : (((N ι : ℝ) ^ (e ι : ℝ) : ℝ) : ℂ) ^ (e ι).den = (N ι : ℂ) ^ (e ι).num := by
    simp [← Complex.ofReal_pow, ← rpow_mul_natCast, h_exp]
  have h_unit : ‖ι.iso ((N ι : ℝ) ^ (e ι : ℝ) : ℝ)‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) (e ι).den_nz, ← norm_pow, ← map_pow, h_pow]
    simp [norm_natCast_eq_one (hN ι)]
  rw [map_mul, norm_mul, h_unit, one_mul]

/-- Let `H ≠ 0` with `|σ H| ≤ e^α` for every automorphism `σ` of `ℂ`, and let real numbers `e ℓ`,
of any sign, satisfy `|ι (H y_ι)| ≤ exp (e ι.prime)` for every pair `ι` and `α + ∑_{ℓ ∈ S} e ℓ ≤ c`
for every finite set `S` of primes. Then `y` has height at most `c`. -/
theorem of_mul_le {H : ℂ} {α : ℝ} {e : ℕ → ℝ} (hH : H ≠ 0)
    (hα : ∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ exp α)
    (he : ∀ ι : PrimePadicIso, ‖ι.iso (H * y ι)‖ ≤ exp (e ι.prime))
    (h_sum : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → α + ∑ ℓ ∈ S, e ℓ ≤ c) : HeightLe c y := by
  -- take `h ℓ = (e ℓ)⁺ / log ℓ`; the sum of the `(e ℓ)⁺` over `S` is that of `e ℓ` over a part
  have h_cancel {ℓ : ℕ} (hℓ : ℓ.Prime) : (e ℓ)⁺ / log ℓ * log ℓ = (e ℓ)⁺ := by
    simp [hℓ.log_pos.ne']
  refine ⟨H, α, fun ℓ ↦ (e ℓ)⁺ / log ℓ, hH, fun ℓ ↦ by positivity, hα, fun ι ↦ ?_,
    fun S hS ↦ ?_⟩
  · rw [rpow_def_of_pos (mod_cast (Fact.out : ι.prime.Prime).pos), mul_comm (log _),
      h_cancel Fact.out]
    exact (he ι).trans (exp_le_exp.2 (le_posPart _))
  · calc α + ∑ ℓ ∈ S, (e ℓ)⁺ / log ℓ * log ℓ = α + ∑ ℓ ∈ S with 0 ≤ e ℓ, e ℓ := by
          rw [sum_filter, sum_congr rfl fun ℓ hℓ ↦ h_cancel (hS ℓ hℓ)]
          simp only [posPart_def, max_def']
      _ ≤ c := h_sum _ fun ℓ hℓ ↦ hS ℓ (mem_filter.1 hℓ).1

/-- If real numbers `e ℓ` have sum at most `c` over every finite set of primes and
`|ι (y ι)| ≤ exp (e ι.prime)` for every pair `ι`, then `y` has height at most `c`. -/
theorem of_le {e : ℕ → ℝ} (h_sum : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → ∑ ℓ ∈ S, e ℓ ≤ c)
    (h_norm : ∀ ι : PrimePadicIso, ‖ι.iso (y ι)‖ ≤ exp (e ι.prime)) : HeightLe c y :=
  of_mul_le (α := 0) one_ne_zero (by simp) (by simpa using h_norm) (by simpa using h_sum)

/-- If `H ≠ 0` and `|σ H| ≤ e^c` for every automorphism `σ` of `ℂ`, the constant family `H⁻¹` has
height at most `c`. -/
theorem inv_const {H : ℂ} (hH : H ≠ 0) (h_conj : ∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ exp c) :
    HeightLe c fun _ ↦ H⁻¹ :=
  of_mul_le (e := 0) hH h_conj (by simp [hH]) (by simp)

/-- **Heights add.** If `y` and `y'` have heights at most `c` and `c'`, their product has height
at most `c + c'`. -/
theorem mul (hy : HeightLe c y) (hy' : HeightLe c' y') : HeightLe (c + c') (y * y') := by
  obtain ⟨H, α, e, hH, he_nonneg, hα, he, h_sum⟩ := hy
  obtain ⟨H', α', e', hH', he_nonneg', hα', he', h_sum'⟩ := hy'
  -- multiply the multipliers and add the exponents at every place
  refine ⟨H * H', α + α', e + e', mul_ne_zero hH hH',
    fun ℓ ↦ add_nonneg (he_nonneg ℓ) (he_nonneg' ℓ), fun σ ↦ ?_, fun ι ↦ ?_, fun S hS ↦ ?_⟩
  · simpa [exp_add] using mul_le_mul (hα σ) (hα' σ) (norm_nonneg _) (exp_nonneg _)
  · calc ‖ι.iso (H * H' * (y * y') ι)‖ = ‖ι.iso (H * y ι)‖ * ‖ι.iso (H' * y' ι)‖ := by
          rw [Pi.mul_apply, mul_mul_mul_comm, map_mul, norm_mul]
      _ ≤ (ι.prime : ℝ) ^ e ι.prime * (ι.prime : ℝ) ^ e' ι.prime :=
        mul_le_mul (he ι) (he' ι) (norm_nonneg _) (by positivity)
      _ = (ι.prime : ℝ) ^ (e + e') ι.prime :=
        (rpow_add (mod_cast (Fact.out : ι.prime.Prime).pos) _ _).symm
  · simp only [Pi.add_apply, add_mul, sum_add_distrib]
    linarith [h_sum S hS, h_sum' S hS]

/-- Heights add in finite products. -/
theorem prod {κ : Type*} {s : Finset κ} {c : κ → ℝ} {y : κ → PrimePadicIso → ℂ}
    (hy : ∀ i ∈ s, HeightLe (c i) (y i)) : HeightLe (∑ i ∈ s, c i) (∏ i ∈ s, y i) := by
  induction s using cons_induction with
  | empty => exact of_le (e := 0) (by simp) (by simp)
  | cons i s hi ih =>
    simpa using (hy i (mem_cons_self i s)).mul (ih fun j hj ↦ hy j (mem_cons_of_mem hj))

/-- If `y` has height at most `c`, then `y ^ n` has height at most `n c`. -/
theorem pow (hy : HeightLe c y) (n : ℕ) : HeightLe (n * c) (y ^ n) := by
  simpa using prod (s := range n) fun _ _ ↦ hy

/-- Let `F` be an algebraically closed normed field with `#F = 𝔠`, for instance `ℂ` or
`PadicAlgCl ℓ`, and `H` a complex number algebraic over `ℚ`. If `‖ι H‖ ≤ e^b` for every
isomorphism `ι : ℂ ≃+* F`, then the norm of `H` from `ℚ(H)` to `ℚ` has absolute value at most
`e^{n b}` in `F`, with `n = [ℚ(H) : ℚ]`: it is the product of the conjugates of `H` in `F`, each
of the form `ι H`. -/
private theorem norm_algebraMap_norm_le {F : Type*} [NormedField F] [CharZero F] [IsAlgClosed F]
    (hF : Cardinal.mk F = Cardinal.continuum) {H : ℂ} (h_alg : IsAlgebraic ℚ H) {b : ℝ}
    (hb : ∀ ι : ℂ ≃+* F, ‖ι H‖ ≤ exp b) :
    ‖algebraMap ℚ F (Algebra.norm ℚ (AdjoinSimple.gen ℚ H))‖ ≤
      exp (Module.finrank ℚ ℚ⟮H⟯ * b) := by
  have : FiniteDimensional ℚ ℚ⟮H⟯ := adjoin.finiteDimensional h_alg.isIntegral
  have : Countable ℚ⟮H⟯ := Countable.of_moduleFinite (R := ℚ)
  -- each conjugate of `H` in `F` is `ι H` for an isomorphism `ι` extending the embedding
  have conj_le (σ : ℚ⟮H⟯ →ₐ[ℚ] F) : ‖σ (AdjoinSimple.gen ℚ H)‖ ≤ exp b := by
    obtain ⟨ι, hι⟩ := Complex.exists_ringEquiv_apply_eq hF ℚ⟮H⟯.val.toRingHom σ.toRingHom
    exact (congrArg norm (hι _)).symm.trans_le (hb ι)
  calc _ = ∏ σ : ℚ⟮H⟯ →ₐ[ℚ] F, ‖σ (AdjoinSimple.gen ℚ H)‖ := by
        rw [Algebra.norm_eq_prod_embeddings, norm_prod]
    _ ≤ ∏ _σ : ℚ⟮H⟯ →ₐ[ℚ] F, exp b :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun σ _ ↦ conj_le σ
    _ = exp (Module.finrank ℚ ℚ⟮H⟯ * b) := by
        rw [prod_const, card_univ, ← exp_natCast_mul, ← AlgHom.card ℚ ℚ⟮H⟯ F]

/-- **The product formula.** If the constant family `1` has height at most `c`, then `0 ≤ c`.

Let `q` be the norm of the multiplier `H` from `ℚ(H)` to `ℚ` and `n = [ℚ(H) : ℚ]`. At every place
`q` is a product of `n` conjugates of `H`, so `log |q| ≤ n α` and `log |q|_ℓ ≤ n h_ℓ log ℓ`, and
the product formula for `q` gives `0 ≤ n c`. -/
theorem nonneg_of_one (h_one : HeightLe c 1) : 0 ≤ c := by
  obtain ⟨H, α, e, hH, -, hα, he, h_sum⟩ := h_one
  have h_padic (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (ι : ℂ ≃+* PadicAlgCl ℓ) :
      ‖ι H‖ ≤ exp (e ℓ * log ℓ) := by
    simpa [rpow_def_of_pos, hℓ.out.pos, mul_comm] using he ⟨ℓ, ι⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `H` is algebraic, as its `2`-adic size is bounded uniformly in `ι`
  have h_alg : IsAlgebraic ℚ H := PrimePadicIso.isAlgebraic_of_norm_le (h_padic 2)
  have : FiniteDimensional ℚ ℚ⟮H⟯ := adjoin.finiteDimensional h_alg.isIntegral
  set q : ℚ := Algebra.norm ℚ (AdjoinSimple.gen ℚ H)
  set n : ℕ := Module.finrank ℚ ℚ⟮H⟯
  have hq : q ≠ 0 := Algebra.norm_ne_zero_iff.2 (by simpa [Subtype.ext_iff] using hH)
  have h_inf : log q ≤ n * α := by
    rw [← log_abs, log_le_iff_le_exp (by simpa using hq)]
    simpa using norm_algebraMap_norm_le Cardinal.mk_complex h_alg hα
  have h_fin (ℓ : ℕ) (hℓ : ℓ.Prime) : log (padicNorm ℓ q) ≤ n * (e ℓ * log ℓ) := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    rw [← Padic.eq_padicNorm, log_le_iff_le_exp (norm_pos_iff.2 (Rat.cast_ne_zero.2 hq)),
      ← PadicAlgCl.norm_extends]
    simpa using norm_algebraMap_norm_le
      (Padic.cardinalMk_eq_continuum_of_isAlgebraic ℓ (PadicAlgCl ℓ)) h_alg (h_padic ℓ)
  -- sum over the primes below a bound `B` exceeding the numerator and the denominator
  set B : ℕ := q.num.natAbs + q.den + 1
  refine nonneg_of_mul_nonneg_right ?_ (Nat.cast_pos.2 (Module.finrank_pos : 0 < n))
  calc 0 = log q + ∑ ℓ ∈ range B with ℓ.Prime, log (padicNorm ℓ q) :=
      (Rat.log_add_sum_log_padicNorm_eq_zero (by omega) (by omega)).symm
    _ ≤ n * α + ∑ ℓ ∈ range B with ℓ.Prime, n * (e ℓ * log ℓ) :=
      add_le_add h_inf (sum_le_sum fun ℓ hℓ ↦ h_fin ℓ (mem_filter.1 hℓ).2)
    _ = n * (α + ∑ ℓ ∈ range B with ℓ.Prime, e ℓ * log ℓ) := by rw [mul_add, mul_sum]
    _ ≤ n * c := mul_le_mul_of_nonneg_left (h_sum _ fun ℓ hℓ ↦ (mem_filter.1 hℓ).2) n.cast_nonneg

/-- If `z ≠ 0`, the constant family `z` has height at most `c`, and `|σ z| ≤ e^{c'}` for every
automorphism `σ` of `ℂ`, then `-c ≤ c'`. -/
theorem neg_le_of_norm_map_le {z : ℂ} (h_height : HeightLe c fun _ ↦ z) (hz : z ≠ 0)
    (h_conj : ∀ σ : ℂ ≃+* ℂ, ‖σ z‖ ≤ exp c') : -c ≤ c' := by
  -- the product of the constant families `z⁻¹` and `z` is the constant family `1`
  have h_one : HeightLe (c' + c) 1 := by
    simpa [Pi.mul_def, Pi.one_def, hz] using (inv_const hz h_conj).mul h_height
  linarith [h_one.nonneg_of_one]

end HeightLe

end TauCeti
