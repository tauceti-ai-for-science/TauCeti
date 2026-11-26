/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-!
# The parameters `(q₀, d)` of the shorter route to GRH

The shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions fixes, once and for
all, a modulus `q₀` divisible by `18480 = 16 · 3 · 5 · 7 · 11` and a prime `d` with
`d ≡ q₀/2 - 1 (mod q₀)`. The congruence is stored as the two divisibilities `q₀ ∣ 2 (d + 1)` and
`q₀ ∤ d + 1`. Write `K = ℚ(√-d)` and `χ_K = (·/d)`, the Legendre symbol. For `s : ℕ` put
`l₀(s) = 3 ^ (⌊log₃ s⌋ + 4)`, `T(s) = 3 ^ (⌊log₃ s⌋ + 5) · 2 ^ s = 3 l₀(s) 2 ^ s`,
`q₁(s) = q₀ T(s)` and `q₂(s) = (q₀ d) ^ (s + 6)`, with Mathlib's `Nat.log 3 0 = 0`.

The facts recorded here are elementary congruences. Every prime dividing `q₁(s)` divides `q₀`
(the primes of `T(s)` are `2` and `3`), hence divides `2 (d + 1)`; as `d ≡ 7 (mod 8)`, it divides
`(d + 1)/4`. Then `d ≡ -1 (mod 4p)`, and since the Jacobi symbol `(p/·)` depends only on its
argument modulo `4p`, `(p/d) = (p/(4p - 1)) = 1`. So the primes dividing `q₁(s)` split in `K`, and
`d`, which satisfies `(d/d) = 0`, does not divide `q₁(s)`. Finally `d² ≡ 1 (mod q₀)`, so the powers
of `d` modulo `q₀` are `1` and `d`, neither of which is `-1`.

## Main definitions

* `TauCeti.ShortGRH.Parameters`: the pair `(q₀, d)`.
* `TauCeti.ShortGRH.l₀`, `TauCeti.ShortGRH.towerDegree`: the numbers `l₀(s)` and `T(s)`.
* `TauCeti.ShortGRH.Parameters.q₁`, `TauCeti.ShortGRH.Parameters.q₂`: the orders `q₁(s)` and
  `q₂(s)`.

## Main results

* `TauCeti.ShortGRH.dvd_two_mul_succ_and_not_dvd_succ`: for even `q₀ > 0`, the congruence
  `d ≡ q₀/2 - 1 (mod q₀)` gives the two divisibilities.
* `TauCeti.ShortGRH.Parameters.d_mod_eight`, `TauCeti.ShortGRH.Parameters.sixty_four_lt_d`:
  `d ≡ 7 (mod 8)` and `d > 64`.
* `TauCeti.ShortGRH.mul_lt_l₀`, `TauCeti.ShortGRH.l₀_le_mul`,
  `TauCeti.ShortGRH.Parameters.two_pow_dvd_q₁`: `27 s < l₀(s) ≤ 81 s` and `2 ^ (s + 1) ∣ q₁(s)`.
* `TauCeti.ShortGRH.Parameters.dvd_d_add_one_div_four_of_dvd_q₁`,
  `TauCeti.ShortGRH.Parameters.legendreSym_eq_one_of_dvd_q₁`,
  `TauCeti.ShortGRH.Parameters.thirteen_le_of_legendreSym_ne_one`: the primes dividing `q₁(s)`
  divide `(d + 1)/4` and split in `K`; a prime that does not split is at least `13`.
* `TauCeti.ShortGRH.Parameters.coprime_q₁_d`, `TauCeti.ShortGRH.Parameters.q₁_mul_d_dvd_q₂`:
  `q₁(s)` is prime to `d`, and `q₁(s) d ∣ q₂(s)`.
* `TauCeti.ShortGRH.Parameters.d_pow_ne_neg_one`: no power of `d` is `-1` modulo `q₀`.

## References

The definitions and facts are those of OneSidedPrimeSumBoundsAndAdmissibleData §2.1 in the
`ShortGRH` family of the Tau Ceti roadmap. They are adapted from the shorter formal proof
https://github.com/lsernau/grh-lean (Apache 2.0, Copyright 2026 Anthropic, PBC), file
`grh/src/New/Reduction/Data/FieldsAndPlaces.lean` (`New.Parameters`, `New.l₀`, `New.towerDeg`,
`New.Parameters.q₁`, `New.Parameters.q₂`, `New.Parameters.instPrimeSevenModEight`,
`New.Parameters.sixty_four_lt_d`, `New.Parameters.dvd_d_add_one_div_four_of_dvd_q₁`,
`New.Parameters.chiK_eq_one_of_dvd`, `New.Parameters.thirteen_le_of_chiK_ne_one`,
`New.Parameters.coprime_q₁_d`, `New.Parameters.q₁_mul_d_dvd_q₂`, `New.Parameters.d_pow_ne_neg_one`)
and `grh/src/New/Reduction/OneSidedBound.lean` (`New.dvd_two_mul_succ_and_not_dvd_succ`).
-/

public section

open scoped NumberTheorySymbols

namespace TauCeti.ShortGRH

/-- If `q₀ > 0` is even and `d ≡ q₀/2 - 1 (mod q₀)`, then `q₀ ∣ 2 (d + 1)` and `q₀ ∤ d + 1`. This
is the form in which `Parameters` stores the congruence. -/
theorem dvd_two_mul_succ_and_not_dvd_succ {q₀ d : ℕ} (hq₀ : 0 < q₀) (h_even : 2 ∣ q₀)
    (hd : d ≡ q₀ / 2 - 1 [MOD q₀]) : q₀ ∣ 2 * (d + 1) ∧ ¬q₀ ∣ d + 1 := by
  obtain ⟨q, rfl⟩ := h_even
  have h_succ : d + 1 ≡ q [MOD 2 * q] := by
    simpa only [show 2 * q / 2 - 1 + 1 = q by omega] using hd.add_right 1
  have h_mod : (d + 1) % (2 * q) = q := by
    rw [h_succ, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨X, hX⟩ : ∃ X, 2 * q * X + q = d + 1 := ⟨_, h_mod ▸ Nat.div_add_mod (d + 1) (2 * q)⟩
  exact ⟨⟨2 * X + 1, by rw [← hX]; ring⟩, fun h ↦ by omega⟩

/-- The parameters of the shorter route to GRH: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11`
and a prime `d` with `d ≡ q₀/2 - 1 (mod q₀)`. The congruence is stored as `q₀ ∣ 2 (d + 1)` and
`q₀ ∤ d + 1`; the first forces `q₀ ≠ 0`, and as `q₀` is even the two together say that `d + 1` is
an odd multiple of `q₀/2` (`dvd_two_mul_succ_and_not_dvd_succ`). -/
structure Parameters where
  /-- The modulus `q₀`. -/
  q₀ : ℕ
  /-- The prime `d`, with `K = ℚ(√-d)`. -/
  d : ℕ
  /-- `18480 ∣ q₀`. -/
  dvd_q₀ : 18480 ∣ q₀
  /-- `d` is prime. -/
  prime_d : d.Prime
  /-- `q₀ ∣ 2 (d + 1)`. -/
  dvd_two_mul_succ : q₀ ∣ 2 * (d + 1)
  /-- `q₀ ∤ d + 1`. -/
  not_dvd_succ : ¬q₀ ∣ d + 1

/-- The number `l₀(s) = 3 ^ (⌊log₃ s⌋ + 4)`; for `s ≥ 1` it is the least power of `3` above
`27 s`. -/
@[expose] def l₀ (s : ℕ) : ℕ := 3 ^ (Nat.log 3 s + 4)

/-- The degree `T(s) = 3 ^ (⌊log₃ s⌋ + 5) · 2 ^ s = 3 l₀(s) 2 ^ s` of the tower: the ratio
`q₁(s) / q₀`. -/
@[expose] def towerDegree (s : ℕ) : ℕ := 3 ^ (Nat.log 3 s + 5) * 2 ^ s

/-- `T(s) = 3 l₀(s) 2 ^ s`. -/
theorem towerDegree_eq (s : ℕ) : towerDegree s = 3 * l₀ s * 2 ^ s := by
  rw [towerDegree, l₀, ← pow_succ']

instance (s : ℕ) : NeZero (towerDegree s) := ⟨by simp [towerDegree]⟩

/-- `27 s < l₀(s)` for every `s`. -/
theorem mul_lt_l₀ (s : ℕ) : 27 * s < l₀ s := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) s
  rw [l₀, pow_add]
  rw [pow_succ] at h
  omega

/-- `l₀(s) ≤ 81 s` for `s ≠ 0`. -/
theorem l₀_le_mul {s : ℕ} (hs : s ≠ 0) : l₀ s ≤ 81 * s := by
  have h := Nat.pow_log_le_self 3 hs
  rw [l₀, pow_add]
  omega

namespace Parameters

variable (P : Parameters)

instance : Fact P.d.Prime := ⟨P.prime_d⟩

instance : NeZero P.q₀ := ⟨fun h ↦ by
  have := P.dvd_two_mul_succ
  rw [h, zero_dvd_iff] at this
  omega⟩

/-- The order `q₁(s) = q₀ T(s)` of the root of unity that generates `E` over `K`. -/
@[expose] def q₁ (s : ℕ) : ℕ := P.q₀ * towerDegree s

/-- The number `q₂(s) = (q₀ d) ^ (s + 6)`, a multiple of `q₁(s) d`. -/
@[expose] def q₂ (s : ℕ) : ℕ := (P.q₀ * P.d) ^ (s + 6)

instance (s : ℕ) : NeZero (P.q₁ s) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩

instance (s : ℕ) : NeZero (P.q₂ s) := ⟨pow_ne_zero _ (mul_ne_zero (NeZero.ne _) P.prime_d.ne_zero)⟩

/-- Every divisor of `18480` divides `q₀`. -/
theorem dvd_q₀_of_dvd_18480 {m : ℕ} (hm : m ∣ 18480) : m ∣ P.q₀ := hm.trans P.dvd_q₀

/-- `q₀ ∣ q₁(s)`. -/
theorem q₀_dvd_q₁ (s : ℕ) : P.q₀ ∣ P.q₁ s := dvd_mul_right _ _

/-- `d ≡ 7 (mod 8)`, since `16 ∣ q₀ ∣ 2 (d + 1)`. -/
theorem d_mod_eight : P.d % 8 = 7 := by
  have : 16 ∣ 2 * (P.d + 1) := (P.dvd_q₀_of_dvd_18480 (by norm_num)).trans P.dvd_two_mul_succ
  omega

/-- `d > 64`: `2 (d + 1)` is a positive multiple of `q₀ ≥ 18480`. -/
theorem sixty_four_lt_d : 64 < P.d := by
  have := Nat.le_of_dvd (by omega) (P.dvd_q₀.trans P.dvd_two_mul_succ)
  omega

/-- `d` is odd. -/
theorem odd_d : Odd P.d := Nat.odd_iff.2 (by have := P.d_mod_eight; omega)

/-- `2 ^ (s + 1) ∣ q₁(s)`. -/
theorem two_pow_dvd_q₁ (s : ℕ) : 2 ^ (s + 1) ∣ P.q₁ s := by
  rw [pow_succ', q₁, towerDegree]
  exact mul_dvd_mul (P.dvd_q₀_of_dvd_18480 (by norm_num)) (dvd_mul_left _ _)

/-- Every prime `p` dividing `q₁(s)` divides `q₀`: the primes of `T(s)` are `2` and `3`. -/
theorem dvd_q₀_of_dvd_q₁ {p s : ℕ} (hp : p.Prime) (h : p ∣ P.q₁ s) : p ∣ P.q₀ := by
  rcases hp.dvd_mul.1 h with h | h
  · exact h
  rcases hp.dvd_mul.1 h with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)]
    exact P.dvd_q₀_of_dvd_18480 (by norm_num)
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)]
    exact P.dvd_q₀_of_dvd_18480 (by norm_num)

/-- Every prime `p` dividing `q₁(s)` divides `(d + 1)/4`, the norm of `(1 + √-d)/2`. -/
theorem dvd_d_add_one_div_four_of_dvd_q₁ {p s : ℕ} (hp : p.Prime) (h : p ∣ P.q₁ s) :
    p ∣ (P.d + 1) / 4 := by
  have h8 := P.d_mod_eight
  have h_dvd : p ∣ 2 ^ 3 * ((P.d + 1) / 4) := by
    rw [show 2 ^ 3 * ((P.d + 1) / 4) = 2 * (P.d + 1) by omega]
    exact (P.dvd_q₀_of_dvd_q₁ hp h).trans P.dvd_two_mul_succ
  rcases hp.dvd_mul.1 h_dvd with h2 | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)]
    omega
  · exact h

/-- Every prime `p` dividing `q₁(s)` splits in `K = ℚ(√-d)`: `(p/d) = 1`. Indeed `d ≡ -1 (mod 4p)`,
and the Jacobi symbol `(p/·)` depends only on its argument modulo `4p`. -/
theorem legendreSym_eq_one_of_dvd_q₁ {p s : ℕ} (hp : p.Prime) (h : p ∣ P.q₁ s) :
    legendreSym P.d p = 1 := by
  have hp0 := hp.pos
  have h8 := P.d_mod_eight
  have h_dvd : 4 * p ∣ P.d + 1 :=
    Nat.mul_dvd_of_dvd_div (by omega) (P.dvd_d_add_one_div_four_of_dvd_q₁ hp h)
  have h_mod : P.d % (4 * p) = 4 * p - 1 := (Nat.mod_eq_sub_iff one_pos (by omega)).2 h_dvd
  have h_four : J(4 * p | 4 * p - 1) = J(p | 4 * p - 1) := by
    simpa using (jacobiSym.div_four_left (a := 4 * p) (b := 4 * p - 1) (by omega) (by omega)).symm
  have h_cast : (4 * p : ℤ) = 1 + ((4 * p - 1 : ℕ) : ℤ) := by omega
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mod_right' p P.odd_d, h_mod, ← h_four,
    h_cast, jacobiSym.mod_left' (Int.add_emod_right 1 _), jacobiSym.one_left]

/-- A prime `p` that does not split in `K`, that is with `(p/d) ≠ 1`, is at least `13`: every
smaller prime divides `18480`, hence `q₁(0)`. -/
theorem thirteen_le_of_legendreSym_ne_one {p : ℕ} (hp : p.Prime)
    (h : legendreSym P.d p ≠ 1) : 13 ≤ p := by
  by_contra! h_lt
  have := hp.two_le
  have h_dvd : p ∣ 18480 := by
    interval_cases p <;> norm_num at hp <;> norm_num
  exact h (P.legendreSym_eq_one_of_dvd_q₁ (s := 0) hp
    ((P.dvd_q₀_of_dvd_18480 h_dvd).mul_right _))

/-- `q₁(s)` is prime to `d`: otherwise `(d/d) = 1`, but the symbol vanishes at `d`. -/
theorem coprime_q₁_d (s : ℕ) : (P.q₁ s).Coprime P.d := by
  refine (P.prime_d.coprime_iff_not_dvd.2 fun h ↦ ?_).symm
  have h_one := P.legendreSym_eq_one_of_dvd_q₁ P.prime_d h
  rw [(legendreSym.eq_zero_iff _ _).2 (by simp)] at h_one
  exact zero_ne_one h_one

/-- `q₁(s) d ∣ q₂(s) = (q₀ d) ^ (s + 6)`. -/
theorem q₁_mul_d_dvd_q₂ (s : ℕ) : P.q₁ s * P.d ∣ P.q₂ s := by
  have h6 : 3 * 2 ∣ P.q₀ * P.d := (P.dvd_q₀_of_dvd_18480 (by norm_num)).mul_right _
  calc P.q₁ s * P.d = P.q₀ * P.d * (3 ^ (Nat.log 3 s + 5) * 2 ^ s) := by
        rw [q₁, towerDegree]; ring
    _ ∣ P.q₀ * P.d * (3 ^ (s + 5) * 2 ^ (s + 5)) := by
        have := Nat.log_le_self 3 s
        exact mul_dvd_mul_left _ (mul_dvd_mul (pow_dvd_pow 3 (by omega)) (pow_dvd_pow 2 (by omega)))
    _ = P.q₀ * P.d * (3 * 2) ^ (s + 5) := by rw [mul_pow]
    _ ∣ P.q₀ * P.d * (P.q₀ * P.d) ^ (s + 5) := mul_dvd_mul_left _ (pow_dvd_pow_of_dvd h6 _)
    _ = P.q₂ s := by rw [q₂, ← pow_succ']

/-- No power of `d` is `-1` modulo `q₀`: as `d` is odd, `q₀ ∣ 2 (d + 1)` and `q₀ ∤ d + 1`, the
residue of `d` satisfies `d ^ 2 = 1`, and neither `1` nor `d` is `-1`. -/
theorem d_pow_ne_neg_one (n : ℕ) : (P.d : ZMod P.q₀) ^ n ≠ -1 := by
  obtain ⟨w, hw⟩ := P.odd_d
  have hd : (P.d : ZMod P.q₀) = 2 * w + 1 := by simp [hw]
  have h_zero : 2 * ((P.d : ZMod P.q₀) + 1) = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).2 P.dvd_two_mul_succ
  have h_ne : (P.d : ZMod P.q₀) + 1 ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).not.2 P.not_dvd_succ
  have h_sq : (P.d : ZMod P.q₀) ^ 2 = 1 := by linear_combination (↑P.d + 1) * hd + ↑w * h_zero
  induction n using Nat.twoStepInduction with
  | zero => exact fun h ↦ h_ne (by linear_combination hd + (↑w + 1) * h)
  | one => exact fun h ↦ h_ne (by linear_combination h)
  | more n ih _ => simpa [pow_add, h_sq] using ih

end Parameters

end TauCeti.ShortGRH
