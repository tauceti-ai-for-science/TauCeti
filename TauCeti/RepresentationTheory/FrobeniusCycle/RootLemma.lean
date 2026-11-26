/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
public import Mathlib.LinearAlgebra.Matrix.Swap
public import TauCeti.RepresentationTheory.FrobeniusCycle.Basic
public import TauCeti.RingTheory.LocalRing.StepanovCount
public import TauCeti.RingTheory.MvPolynomial.GaussFiltration
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Gauss filtrations and the root lemma

Let `T` be a Frobenius cycle (`TauCeti.FrobeniusCycle`): ring maps `ι_s : W → R` for the letters
`s ∈ ℤ/N`, alternately even and odd, with `ι_{s+1} ≡ ι_s ^ P` modulo a prime `p`, where `W` has
`q = P ^ N` residue classes, and a square root `w` of `p` in `R`. The group `GL_k(W)` acts on
polynomials over `R` in the variables `x_{s,b}` by the twisted action. This file shows which
monomials can carry the least `w`-adic order plus weight among all translates of a polynomial by
`SL₂(W)`, placed in two rows and columns `a`, `a'`: their exponents have defect at most `0`, which
is one of Pieri's inequalities.

## Main results

* `TauCeti.FrobeniusCycle.defect_nonpos_of_extreme_term` (the root lemma, (b) of the roadmap's
  section 1.3): for weights `c` with `c(u_s) - c(ū_s) ∈ [1 / 2, 1]`, if every translate of `f` by
  `SL₂^{a,a'}(W)` lies in Gauss level `l + c · α` and `w ^ (l + 1)` does not divide the coefficient
  of `x^α` in `f`, then the defect of `α` at any letter along `(a, a')` is at most `0`.
* `TauCeti.FrobeniusCycle.mem_gaussFiltration_sub_defect_div_three` ((c) of section 1.3): if the
  weights `δ` rise by `1` from `ū_s` to `u_s` and every translate of `f` lies in Gauss level `v₀`
  for `δ`, then `f` lies in Gauss level `v₀` for `δ` minus a third of the defect weights.
* `TauCeti.FrobeniusCycle.weight_defectWeight_nonpos_of_least` ((d) of section 1.3): over a field
  of characteristic `p`, a term of least `δ`-weight among all translates has defect at most `0`.

## Proof

Fix the root `(a, a')` and the letter `i` (`TauCeti.FrobeniusCycle.RootAt`). Write `X_s = ū_s` and
`Y_s = u_s` for the two variables of the root in the letter `s`. A substitution of polynomials in
one affine coordinate `t` for these variables turns the coefficient of a term of `f` into a
univariate polynomial `Φ` over `R / w ^ (l + 1)`. Its expansion at infinity bounds its degree by
`q ν'`, and its expansions at the `q` finite points `ι_i(r)`, which come from the translates of `f`
by the matrices `!![0, 1; -1, ±r]` together with the Frobenius congruences, give zeros of order at
least `ν` there, where `ν q - q ν'` is `q (q - 1)` times the defect. Stepanov's count
(`TauCeti.stepanov_count`) compares the two.

The statements and proofs are adapted from the file
`New/UpperBound/ElementaryDivisors/RootLemma.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC):
`New.FrobeniusCycle.RootAt` and its lemmas, `New.FrobeniusCycle.defect_nonpos_of_extreme_term`,
`New.FrobeniusCycle.totalDegree_polyAction_le`,
`New.FrobeniusCycle.mem_gaussFiltration_sub_defect_div_three` and
`New.FrobeniusCycle.weight_defectWeight_nonpos_of_least`.

## References

The comparison of zeros with degree is Stepanov's method; see
* E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*,
  Séminaire Bourbaki, exp. 430 (1973).

Weight inequalities for twisted actions on Frobenius twists of symmetric powers are in the spirit of
* E. Ghate, A. Jana, *Modular representations of `GL₂(F_q)` using calculus*, 2025;
* N. Imai, J.-S. Koskivirta, *Automorphic vector bundles on the stack of `G`-zips*, Forum Math.
  Sigma 9 (2021).
-/

@[expose] public section

namespace TauCeti

open MvPolynomial Matrix Finsupp SetLike Nat Ideal.Quotient

namespace FrobeniusCycle

variable {N k : ℕ} {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R]

/-- A root `(a, a')` of `GL_k` and a letter `i`, the data at which a defect is measured. -/
structure RootAt (T : FrobeniusCycle N W R) (k : ℕ) where
  /-- The letter `i`. -/
  letter : ZMod N
  /-- The index `a`. -/
  fst : Fin k
  /-- The index `a'`. -/
  snd : Fin k
  /-- The two indices differ. -/
  ne : fst ≠ snd

namespace RootAt

variable {T : FrobeniusCycle N W R} (D : T.RootAt k) {s : ZMod N} {z : ZMod N × Fin k}

/-- The variable `X_s = ū_s`: index `a` at even and `a'` at odd letters `s`. -/
def varX (s : ZMod N) : ZMod N × Fin k := T.rootVar D.snd D.fst s

/-- The variable `Y_s = u_s`: index `a'` at even and `a` at odd letters `s`. -/
def varY (s : ZMod N) : ZMod N × Fin k := T.rootVar D.fst D.snd s

/-- The variables whose index is neither `a` nor `a'`. -/
def IsFixed (z : ZMod N × Fin k) : Prop := z.2 ≠ D.fst ∧ z.2 ≠ D.snd

/-- The permutation of the variables that swaps `X_s` and `Y_s` in each letter. -/
def swapVar (z : ZMod N × Fin k) : ZMod N × Fin k := (z.1, Equiv.swap D.fst D.snd z.2)

/-- The map of variables that sends `Y_i` to `X_i` and fixes the others. -/
def merge (z : ZMod N × Fin k) : ZMod N × Fin k :=
  if z = D.varY D.letter then D.varX D.letter else z

/-- The sign at `Y_s`: `-1` if `s` has the parity of `i` and `1` otherwise; it is `0` at the other
variables. -/
def sign (z : ZMod N × Fin k) : ℤ :=
  if z = D.varY z.1 then if T.isEven z.1 = T.isEven D.letter then -1 else 1 else 0

/-- The number `q = P ^ N` of residue classes of `W`, as a constant whose casts `simp` keeps. -/
def card (_ : T.RootAt k) : ℕ := T.q

/-- The power `P_s = P ^ (s - i)`, with `s - i` read in `[0, N)`. -/
def frobPower (s : ZMod N) : ℕ := T.P ^ (s - D.letter).val

/-- The weights `q P_s` at `X_s` and `0` at the other variables: the weight of an exponent bounds
the degree in `t` of the auxiliary polynomial. -/
def poleOrder (z : ZMod N × Fin k) : ℕ := if z = D.varX z.1 then D.card * D.frobPower z.1 else 0

/-- The weights `q` at `Y_i`, `P_s` at `Y_s` for `s ≠ i`, and `0` at the other variables: the
weight of an exponent bounds from below the order of vanishing of the auxiliary polynomial at the
points `t = ι_i(r)`, `r ∈ W`. -/
def zeroOrder (z : ZMod N × Fin k) : ℕ :=
  if z = D.varY z.1 then if z.1 = D.letter then D.card else D.frobPower z.1 else 0

/-- The sign of `Y_s` at both `X_s` and `Y_s` for `s ≠ i`, and `0` at the other variables. -/
def crossSign (z : ZMod N × Fin k) : R :=
  if z.1 = D.letter then 0 else D.sign z + D.sign (D.swapVar z)

theorem cast_card_pos : (0 : ℝ) < D.card := by
  have := T.neZero
  simpa [card] using one_pos.trans T.one_lt_q

@[simp] theorem varX_fst : (D.varX s).1 = s := rfl

@[simp] theorem varY_fst : (D.varY s).1 = s := rfl

@[simp] theorem varX_ne_varY (s t : ZMod N) : D.varX s ≠ D.varY t := by
  have := D.ne
  grind [varX, varY, rootVar]

@[simp] theorem varY_ne_varX (s t : ZMod N) : D.varY s ≠ D.varX t := (D.varX_ne_varY t s).symm

@[simp] theorem varY_inj {t : ZMod N} : D.varY s = D.varY t ↔ s = t :=
  ⟨congrArg Prod.fst, congrArg D.varY⟩

@[simp] theorem swapVar_fst : (D.swapVar z).1 = z.1 := rfl

@[simp] theorem swapVar_varX : D.swapVar (D.varX s) = D.varY s := by
  grind [swapVar, varX, varY, rootVar]

@[simp] theorem swapVar_varY : D.swapVar (D.varY s) = D.varX s := by
  grind [swapVar, varX, varY, rootVar]

/-- Every variable is `Y_i`, `X_i`, some `Y_s` or `X_s` with `s ≠ i`, or lies off the root. -/
theorem var_cases (z : ZMod N × Fin k) : z = D.varY D.letter ∨ z = D.varX D.letter ∨
    (∃ s : ZMod N, s ≠ D.letter ∧ (z = D.varY s ∨ z = D.varX s)) ∨ D.IsFixed z := by
  have h_letter : z = D.varY z.1 ∨ z = D.varX z.1 ∨ D.IsFixed z := by
    grind [varX, varY, rootVar, IsFixed]
  grind

@[simp] theorem sign_varX : D.sign (D.varX s) = 0 := by simp [sign]

@[simp] theorem sign_varY_letter : D.sign (D.varY D.letter) = -1 := by simp [sign]

theorem sign_varY_eq_one_or_neg_one (s : ZMod N) :
    D.sign (D.varY s) = 1 ∨ D.sign (D.varY s) = -1 := by
  grind [sign, varY_fst]

@[simp] theorem frobPower_letter : D.frobPower D.letter = 1 := by simp [frobPower]

@[simp] theorem merge_varX : D.merge (D.varX s) = D.varX s := by simp [merge]

@[simp] theorem merge_varY :
    D.merge (D.varY s) = if s = D.letter then D.varX D.letter else D.varY s := by
  simp [merge]

@[simp] theorem poleOrder_varX : D.poleOrder (D.varX s) = D.card * D.frobPower s := by
  simp [poleOrder]

@[simp] theorem poleOrder_varY : D.poleOrder (D.varY s) = 0 := by simp [poleOrder]

@[simp] theorem zeroOrder_varX : D.zeroOrder (D.varX s) = 0 := by simp [zeroOrder]

@[simp] theorem zeroOrder_varY :
    D.zeroOrder (D.varY s) = if s = D.letter then D.card else D.frobPower s :=
  ite_eq_left rfl

@[simp] theorem crossSign_varX : D.crossSign (D.varX s) =
    if s = D.letter then 0 else (D.sign (D.varY s) : R) := by simp [crossSign]

@[simp] theorem crossSign_varY : D.crossSign (D.varY s) =
    if s = D.letter then 0 else (D.sign (D.varY s) : R) := by simp [crossSign]

namespace IsFixed

variable {D}

theorem ne_varX (hz : D.IsFixed z) (s : ZMod N) : z ≠ D.varX s := by
  grind [varX, rootVar, IsFixed]

theorem ne_varY (hz : D.IsFixed z) (s : ZMod N) : z ≠ D.varY s := by
  grind [varY, rootVar, IsFixed]

theorem swapVar_eq (hz : D.IsFixed z) : D.swapVar z = z := by grind [swapVar, IsFixed]

theorem merge_eq (hz : D.IsFixed z) : D.merge z = z := ite_eq_right (hz.ne_varY D.letter)

theorem sign_eq_zero (hz : D.IsFixed z) : D.sign z = 0 := ite_eq_right (hz.ne_varY z.1)

theorem poleOrder_eq_zero (hz : D.IsFixed z) : D.poleOrder z = 0 := ite_eq_right (hz.ne_varX z.1)

theorem zeroOrder_eq_zero (hz : D.IsFixed z) : D.zeroOrder z = 0 := ite_eq_right (hz.ne_varY z.1)

theorem crossSign_eq_zero (hz : D.IsFixed z) : D.crossSign z = 0 := by
  simp [crossSign, hz.swapVar_eq, hz.sign_eq_zero]

end IsFixed

/-- The defect weight of a variable `z` at the letter `i` along `(a, a')` is
`(D.zeroOrder z - D.poleOrder z / q) / (q - 1)`. -/
theorem defectWeight_eq (z : ZMod N × Fin k) :
    T.defectWeight D.letter D.fst D.snd z =
      (D.zeroOrder z - D.poleOrder z / D.card) / (D.card - 1) := by
  have := T.neZero
  change ((if z = D.varY z.1 then (T.P : ℝ) ^ (1 + (z.1 - 1 - D.letter).val) else 0) -
    if z = D.varX z.1 then (T.P : ℝ) ^ (z.1 - D.letter).val else 0) / (D.card - 1) = _
  rw [one_add_val_sub_one_sub, zeroOrder, poleOrder]
  congr 1
  split_ifs <;> simp [card, frobPower, T.prime.ne_zero]

/-- The diagonal signs `-1` at the index `a` and `1` at the other indices. -/
def signAt (D : T.RootAt k) : Fin k → Wˣ := Function.update 1 D.fst (-1)

/-- The matrix `!![0, 1; -1, x]` in the rows and columns `a`, `a'`, with `x = -r` if `i` is even
and `x = r` otherwise, written as a transposition times a transvection times the diagonal matrix
with `-1` at `a`. It relates the point at infinity of the projective line to the finite point with
the affine coordinate `ι_i(r)`. -/
def swapTransvection (r : W) : GL (Fin k) W :=
  permutationGL (Equiv.swap D.fst D.snd) *
    transvectionUnit D.ne (if T.isEven D.letter then -r else r) * diagGL D.signAt

/-- The sign `-1` at the variables with index `a`, and `1` at the other variables. -/
def moveSign (z : ZMod N × Fin k) : ℤ := if z.2 = D.fst then -1 else 1

theorem signAt_inv : D.signAt⁻¹ = D.signAt := by
  funext b
  by_cases hb : b = D.fst <;> simp [signAt, hb]

/-- `D.swapTransvection r` lies in `SL₂(W)` placed in the rows and columns `a`, `a'`. -/
theorem swapTransvection_mem_rootSL (r : W) : D.swapTransvection r ∈ rootSL W D.fst D.snd := by
  have := D.ne
  set P : Set (Fin k) := {D.fst, D.snd}ᶜ
  have hP {i : Fin k} : i ∈ P ↔ i ≠ D.fst ∧ i ≠ D.snd := by simp [P]
  have h_perm : permutationGL (Equiv.swap D.fst D.snd) ∈ columnRowFixingSubgroup W P P := by
    refine mem_columnRowFixingSubgroup_iff.2 ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩ <;>
      simp only [hP] at * <;>
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply,
        Equiv.swap_apply_def] <;> split_ifs <;> grind
  have h_tr (x : W) : transvectionUnit D.ne x ∈ columnRowFixingSubgroup W P P := by
    refine mem_columnRowFixingSubgroup_iff.2 ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩ <;>
      simp only [hP] at * <;> simp [transvection, Matrix.single_apply] <;> grind
  have h_sign : diagGL D.signAt ∈ columnRowFixingSubgroup W P P := by
    refine mem_columnRowFixingSubgroup_iff.2 ⟨fun j hj i ↦ ?_, fun i hi j ↦ ?_⟩ <;>
      simp only [hP] at * <;> by_cases h : i = j <;> simp_all [signAt, Matrix.one_apply]
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem h_perm (h_tr _)) h_sign, ?_⟩
  -- The three factors have determinants `-1`, `1` and `-1`.
  have h_diag : GeneralLinearGroup.det (diagGL D.signAt) = -1 := by
    ext
    simp [signAt, Finset.prod_update_of_mem]
  have h_perm : GeneralLinearGroup.det (permutationGL (k := W) (Equiv.swap D.fst D.snd)) = -1 := by
    ext
    simp [Equiv.Perm.sign_swap D.ne]
  rw [MonoidHom.mem_ker, swapTransvection, map_mul, map_mul, h_diag, h_perm,
    det_transvectionUnit]
  simp

end RootAt

/-- The action of `g` on a variable, through `g` at even and its inverse transpose at odd
letters. -/
theorem polyAction_X_eq (T : FrobeniusCycle N W R) (g : GL (Fin k) W) (z : ZMod N × Fin k) :
    T.polyAction g (X z) = ∑ b, C (T.embedding z.1
      ((if T.isEven z.1 then g else GeneralLinearGroup.inverseTranspose g : GL (Fin k) W) b z.2)) *
        X (z.1, b) := by
  rw [polyAction_X, coe_letterMatrix]
  by_cases h : T.isEven z.1 <;> simp [h]

namespace RootAt

variable {T : FrobeniusCycle N W R} (D : T.RootAt k)

/-- The diagonal factor of `D.swapTransvection r` is its own inverse transpose, and multiplies the
variables with index `a` by `-1`. -/
theorem polyAction_diagGL_signAt_X (z : ZMod N × Fin k) :
    T.polyAction (diagGL D.signAt) (X z) = D.moveSign z • X z := by
  have h_even : (if T.isEven z.1 then diagGL D.signAt
      else GeneralLinearGroup.inverseTranspose (diagGL D.signAt)) = diagGL D.signAt := by
    split_ifs <;> simp [← Pi.inv_def, signAt_inv]
  rw [polyAction_X_eq, h_even, Finset.sum_eq_single z.2 (fun b _ hb ↦ by simp [hb]) (by simp)]
  obtain ⟨s, b⟩ := z
  by_cases h : b = D.fst
  · subst h
    simp [signAt, moveSign]
  · simp [signAt, moveSign, h]

/-- The transposition of `a` and `a'` is its own inverse transpose, and exchanges `X_s` and
`Y_s`. -/
theorem polyAction_swap_X (z : ZMod N × Fin k) :
    T.polyAction (permutationGL (Equiv.swap D.fst D.snd)) (X z) = X (D.swapVar z) := by
  have h_even : (if T.isEven z.1 then permutationGL (Equiv.swap D.fst D.snd)
      else GeneralLinearGroup.inverseTranspose (permutationGL (Equiv.swap D.fst D.snd))) =
        permutationGL (k := W) (Equiv.swap D.fst D.snd) := by
    split_ifs <;> simp
  rw [polyAction_X_eq, h_even]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, swapVar, Equiv.swap_apply_eq_iff]

/-- The transvection by `x` at `(a, a')` adds `± ι_s(x) X_s` to `Y_s` and fixes the other
variables: the sign is `+` at even and `-` at odd letters. -/
theorem polyAction_transvectionUnit_X (x : W) (z : ZMod N × Fin k) :
    T.polyAction (transvectionUnit D.ne x) (X z) = X z + C (if z = D.varY z.1 then
      T.embedding z.1 (if T.isEven z.1 then x else -x) else 0) * X (D.varX z.1) := by
  rw [polyAction_X_eq]
  obtain ⟨s, b⟩ := z
  have := D.ne
  cases h : T.isEven s <;>
    simp [h, transvection, Matrix.single_apply, Matrix.one_apply, Finset.sum_add_distrib, add_mul,
      varX, varY, rootVar, apply_ite (T.embedding s), apply_ite C, ite_and] <;>
    grind

/-- The action of the matrix `D.swapTransvection r` on the variable `z`. Up to the sign
`D.moveSign z`, which is `-1` if `z` has index `a` and `1` otherwise, it sends `X_s` to `Y_s`,
sends `Y_s` to `X_s + ε_s ι_s(r) Y_s` and fixes the other variables. Here `ε_s = D.sign Y_s` is
`-1` if `s` has the parity of the letter `i` and `1` otherwise. -/
theorem polyAction_swapTransvection_X (r : W) (z : ZMod N × Fin k) :
    T.polyAction (D.swapTransvection r) (X z) =
      D.moveSign z • (X (D.swapVar z) + C (D.sign z * T.embedding z.1 r) * X (D.varY z.1)) := by
  rw [swapTransvection, map_mul, map_mul, AlgHom.mul_apply, AlgHom.mul_apply,
    polyAction_diagGL_signAt_X, map_zsmul, map_zsmul, polyAction_transvectionUnit_X, map_add,
    map_mul, algHom_C, algebraMap_eq, polyAction_swap_X, polyAction_swap_X, swapVar_varX]
  congr 3
  obtain ⟨s, b⟩ := z
  by_cases hz : (s, b) = D.varY s
  · rw [hz]
    cases h : T.isEven s <;> cases h' : T.isEven D.letter <;> simp [sign, h, h']
  · simp [hz, sign]

/-! ### Weights with bounded increments -/

/-- The weights `c` of the variables rise from `X_s` to `Y_s` by an amount in `[1 / 2, 1]`. -/
def HasBoundedIncrements (c : ZMod N × Fin k → ℝ) : Prop :=
  ∀ s : ZMod N, c (D.varY s) - c (D.varX s) ∈ Set.Icc 2⁻¹ 1

/-- The slope `ρ = (c Y_i - c X_i) / q` of weights `c` of the variables. The variable `t` of the
auxiliary polynomial weighs `-ρ` in the expansion at infinity and `ρ` in the expansion at a finite
point. -/
noncomputable def slope (c : ZMod N × Fin k → ℝ) : ℝ :=
  (c (D.varY D.letter) - c (D.varX D.letter)) / D.card

variable {D} {c : ZMod N × Fin k → ℝ}

theorem card_mul_slope :
    D.card * D.slope c = c (D.varY D.letter) - c (D.varX D.letter) := by
  have := T.neZero
  exact mul_div_cancel₀ _ D.cast_card_pos.ne'

theorem HasBoundedIncrements.slope_pos (hc : D.HasBoundedIncrements c) : 0 < D.slope c := by
  have := T.neZero
  exact div_pos (by linarith [(hc D.letter).1]) D.cast_card_pos

/-- If the steps of `c` lie in `[1 / 2, 1]`, then `P_s` times the slope is at most `1 / 5`, because
`5 P_s ≤ q`. -/
theorem HasBoundedIncrements.frobPower_mul_slope_le (hc : D.HasBoundedIncrements c)
    (s : ZMod N) : D.frobPower s * D.slope c ≤ 1 / 5 := by
  have := T.neZero
  have h_power : (5 * D.frobPower s : ℝ) ≤ D.card := mod_cast T.five_mul_P_pow_le_q (s - D.letter)
  have h_step : D.card * D.slope c ≤ 1 := card_mul_slope.trans_le (hc D.letter).2
  nlinarith [hc.slope_pos]

/-- If the steps of `c` lie in `[1 / 2, 1]` and `s ≠ i`, then `q P_s` times the slope is at least
`2`, because `P_s ≥ 5`. -/
theorem HasBoundedIncrements.two_le_card_mul_frobPower_mul_slope {s : ZMod N}
    (hc : D.HasBoundedIncrements c) (hs : s ≠ D.letter) :
    2 ≤ D.card * D.frobPower s * D.slope c := by
  have := T.neZero
  have h_power : (5 : ℝ) ≤ D.frobPower s :=
    mod_cast T.five_le_P.trans (le_self_pow (by simpa [sub_eq_zero]) _)
  have h_step : (2⁻¹ : ℝ) ≤ D.card * D.slope c := (hc D.letter).1.trans_eq card_mul_slope.symm
  nlinarith

/-! ### The auxiliary polynomial -/

variable (D) in
/-- The main part of the substitution, with a new variable `t = X ()`: `Y_i ↦ X_i`,
`X_s ↦ t ^ (q P_s) X_s`, and the other variables are fixed. -/
noncomputable def mainSubst (z : ZMod N × Fin k) :
    MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R) :=
  C (monomial (single () (D.poleOrder z)) 1) * X (D.merge z)

variable (D) in
/-- The cross terms: for `s ≠ i`, `Y_s ↦ ε_s X_s` and `X_s ↦ ε_s t ^ P_s Y_s`, where `ε_s` is the
sign `D.sign` at `Y_s`; the other variables go to `0`. The substitution that defines the auxiliary
polynomial is `D.mainSubst - D.crossSubst`. -/
noncomputable def crossSubst (z : ZMod N × Fin k) :
    MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R) :=
  C (monomial (single () (D.zeroOrder (D.swapVar z))) (D.crossSign z)) * X (D.swapVar z)

end RootAt

/-- The Gauss filtration on polynomials over `R[t]` in which `w` weighs `1`, `t` weighs `ρ` and
each variable `z` weighs `c z - v z * ρ`. -/
noncomputable abbrev iteratedGaussFiltration (T : FrobeniusCycle N W R)
    (c : ZMod N × Fin k → ℝ) (ρ : ℝ) (v : ZMod N × Fin k → ℕ) :
    ℝ → AddSubgroup (MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)) :=
  gaussFiltration (gaussFiltration (adicFiltration T.sqrtPrime) fun _ : Unit ↦ ρ)
    fun z ↦ c z - v z * ρ

theorem antitone_iteratedGaussFiltration (T : FrobeniusCycle N W R) (c : ZMod N × Fin k → ℝ)
    (ρ : ℝ) (v : ZMod N × Fin k → ℕ) : Antitone (T.iteratedGaussFiltration c ρ v) :=
  antitone_gaussFiltration (antitone_gaussFiltration (antitone_adicFiltration _))

variable {T : FrobeniusCycle N W R} {c : ZMod N × Fin k → ℝ} {ρ b : ℝ} {v : ZMod N × Fin k → ℕ}

theorem algebraMap_mem_iteratedGaussFiltration {r : R} (hr : r ∈ adicFiltration T.sqrtPrime b) :
    algebraMap R (MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)) r ∈
      T.iteratedGaussFiltration c ρ v b :=
  C_mem_gaussFiltration (C_mem_gaussFiltration hr)

/-- The term `r t ^ n` times the variable `X z` lies in `T.iteratedGaussFiltration c ρ v b` if
`r = 0` or `b ≤ c z - v z * ρ + n * ρ`, the weight of `t ^ n X z`. -/
theorem C_monomial_mul_X_mem_iteratedGaussFiltration {z : ZMod N × Fin k} {n : ℕ} {r : R}
    (hb : r ≠ 0 → b ≤ c z - v z * ρ + n * ρ) :
    C (monomial (single () n) r) * X z ∈ T.iteratedGaussFiltration c ρ v b := by
  rw [C_mul_X_eq_monomial]
  refine monomial_mem_gaussFiltration (monomial_mem_gaussFiltration ?_)
  exact mem_adicFiltration_of_nonpos (by simpa [weight_single, add_comm] using hb)

namespace RootAt

variable {D : T.RootAt k}

/-- **Expansion at infinity.** Let the weights `c` rise from `X_s` to `Y_s` by amounts in
`[1 / 2, 1]`, let each term of `f` have `w`-adic order plus `c`-weight at least `b`, and put
`ρ = D.slope c`. In the filtration on polynomials over `R[t]` in which `w` weighs `1`, `t` weighs
`-ρ` and `X_s` weighs `c X_s + q P_s ρ`, the substitution `D.mainSubst - D.crossSubst` sends `f` to
level `b`, and the cross terms change the image of `f` only in level `b + 1 / 20`. -/
theorem HasBoundedIncrements.aeval_mem_and_sub_mem_iteratedGaussFiltration
    (hc : D.HasBoundedIncrements c) {f : MvPolynomial (ZMod N × Fin k) R}
    (hf : f ∈ gaussFiltration (adicFiltration T.sqrtPrime) c b) :
    aeval (D.mainSubst - D.crossSubst) f ∈
        T.iteratedGaussFiltration c (-D.slope c) D.poleOrder b ∧
      aeval (D.mainSubst - D.crossSubst) f - aeval D.mainSubst f ∈
        T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (b + 20⁻¹) := by
  have := T.neZero
  have h_main (z : ZMod N × Fin k) :
      D.mainSubst z ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (c z) := by
    refine C_monomial_mul_X_mem_iteratedGaussFiltration fun _ ↦ ?_
    by_cases hz : z = D.varY D.letter
    · simp [hz, card_mul_slope]
    · simp [merge, hz]
  have h_cross (z : ZMod N × Fin k) :
      D.crossSubst z ∈ T.iteratedGaussFiltration c (-D.slope c) D.poleOrder (c z + 20⁻¹) := by
    refine C_monomial_mul_X_mem_iteratedGaussFiltration fun h_sign ↦ ?_
    rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
    · simp at h_sign
    · simp at h_sign
    · -- `X_s` weighs `c X_s + q P_s * D.slope c ≥ c X_s + 2 ≥ c Y_s + 1`
      suffices c (D.varY s) + 20⁻¹ ≤ c (D.varX s) + D.card * D.frobPower s * D.slope c by simpa
      linarith [(hc s).2, hc.two_le_card_mul_frobPower_mul_slope hs]
    · -- `t ^ P_s Y_s` weighs `c Y_s - P_s * D.slope c ≥ c X_s + 1 / 2 - 1 / 5`
      suffices c (D.varX s) + 20⁻¹ ≤ c (D.varY s) + -(D.frobPower s * D.slope c) by simpa [hs]
      linarith [(hc s).1, hc.frobPower_mul_slope_le s]
    · exact absurd hz.crossSign_eq_zero h_sign
  exact algHom_sub_mem_of_mem_gaussFiltration (aeval D.mainSubst) _
    (antitone_iteratedGaussFiltration ..) hf (by simpa using h_main) _ (by simpa using h_cross)
    algebraMap_mem_iteratedGaussFiltration

end RootAt

/-- The error in the rule `(t + ι_i(r)) ^ P ^ n = t ^ P ^ n + ι_{i + n}(r)`. -/
noncomputable def frobeniusError (T : FrobeniusCycle N W R) (i : ZMod N) (r : W) (n : ℕ) :
    MvPolynomial Unit R :=
  (X () + C (T.embedding i r)) ^ T.P ^ n - X () ^ T.P ^ n - C (T.embedding (i + n) r)

/-- The Frobenius error is divisible by `p = w ^ 2`, so for `ρ ≥ 0` its product with a variable `z`
has level `2` more than the weight of `z`. -/
theorem frobeniusError_mul_X_mem (hρ : 0 ≤ ρ) (v : ZMod N × Fin k → ℕ) (z : ZMod N × Fin k)
    (i : ZMod N) (r : W) (n : ℕ) :
    C (T.frobeniusError i r n) * X z ∈ T.iteratedGaussFiltration c ρ v (c z - v z * ρ + 2) := by
  have h_add : (T.p : MvPolynomial Unit R) ∣
      (X () + C (T.embedding i r)) ^ T.P ^ n - X () ^ T.P ^ n - C (T.embedding i r) ^ T.P ^ n := by
    simp [← pow_mul, add_pow_prime_pow_eq' T.prime, add_assoc]
  have h_shift : (T.p : MvPolynomial Unit R) ∣
      C (T.embedding (i + n) r) - C (T.embedding i r) ^ T.P ^ n := by
    simpa using map_dvd C (T.frobenius_pow_congr i n r)
  have h_dvd : C (T.sqrtPrime ^ 2) ∣ T.frobeniusError i r n := by
    simpa [frobeniusError, sqrtPrime_sq] using dvd_sub h_add h_shift
  rw [C_mul_X_eq_monomial]
  refine monomial_mem_gaussFiltration fun β ↦ ?_
  refine mem_adicFiltration_iff.2 ((pow_dvd_pow T.sqrtPrime ?_).trans
    ((C_dvd_iff_dvd_coeff _ _).1 h_dvd β))
  -- The order asked for is `2` minus the weight `β () * ρ ≥ 0` of the monomial `β` in `t`.
  simpa [weight_single, β.weight_eq_sum _] using mul_nonneg (β ()).cast_nonneg hρ

/-- The substitution `t ↦ t + x` in the coefficients. -/
noncomputable def shiftCoeff (σ : Type*) (x : R) :
    MvPolynomial σ (MvPolynomial Unit R) →ₐ[R] MvPolynomial σ (MvPolynomial Unit R) :=
  mapAlgHom (((uniqueAlgEquiv R Unit).arrowCongr (uniqueAlgEquiv R Unit)).symm
    (Polynomial.taylorAlgHom x))


namespace RootAt

variable {D : T.RootAt k}

/-- The shift of `t` undoes the transvection in `D.swapTransvection r` up to Frobenius errors. Act
on the variable `z` by `D.swapTransvection r`, substitute `D.mainSubst - D.crossSubst` and replace
`t` by `t + ι_i(r)`. Up to the sign `D.moveSign z` the result is the polynomial substituted for
`D.swapVar z`, plus errors `T.frobeniusError i r n` that occur only for `z = Y_s`: with
`d = (s - i) mod N`, the error for `n = N + d` multiplies `X_s`, and `-ε_s` times the error for
`n = d` multiplies `Y_s`. -/
theorem shiftCoeff_aeval_swapTransvection_X (r : W) (z : ZMod N × Fin k) :
    shiftCoeff (ZMod N × Fin k) (T.embedding D.letter r)
        (aeval (D.mainSubst - D.crossSubst) (T.polyAction (D.swapTransvection r) (X z))) -
      D.moveSign z • (D.mainSubst - D.crossSubst) (D.swapVar z) =
    D.moveSign z •
      (C (T.frobeniusError D.letter (|D.sign z| * r) (N + (z.1 - D.letter).val)) *
          X (D.swapVar z) -
        D.sign z • (C (T.frobeniusError D.letter r (z.1 - D.letter).val) * X z)) := by
  have := T.neZero
  rw [D.polyAction_swapTransvection_X, map_zsmul, map_zsmul, ← smul_sub]
  unfold shiftCoeff mainSubst crossSubst frobeniusError
  congr 1
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · -- `z = Y_i`
    simp [monomial_eq, card]
    ring
  · -- `z = X_i`
    simp [monomial_eq]
  · -- `z = Y_s` with `s ≠ i`, the same computation for both signs
    rcases D.sign_varY_eq_one_or_neg_one s with h_sign | h_sign
    all_goals
      simp [monomial_eq, card, frobPower, pow_add, hs, h_sign]
      ring
  · -- `z = X_s` with `s ≠ i`
    simp [monomial_eq, hs]
  · -- `z` lies off the root
    simp [monomial_eq, hz.swapVar_eq, hz.sign_eq_zero, hz.poleOrder_eq_zero, hz.crossSign_eq_zero]

/-- With `ρ = D.slope c`, filter polynomials over `R[t]` so that `w` weighs `1`, `t` weighs `ρ` and
a variable `y` weighs `c y - D.zeroOrder y * ρ`. If `c` rises from `X_s` to `Y_s` by amounts in
`[1 / 2, 1]`, the substitution `D.mainSubst - D.crossSubst` sends `D.swapVar z` to level `c z`. -/
theorem HasBoundedIncrements.subst_swapVar_mem_iteratedGaussFiltration
    (hc : D.HasBoundedIncrements c) (z : ZMod N × Fin k) :
    (D.mainSubst - D.crossSubst) (D.swapVar z) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z) := by
  have := T.neZero
  refine sub_mem (C_monomial_mul_X_mem_iteratedGaussFiltration fun _ ↦ ?_)
    (C_monomial_mul_X_mem_iteratedGaussFiltration (by simp [swapVar]))
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · simp [card_mul_slope]
  · simp
  · suffices c (D.varY s) ≤ c (D.varX s) + D.card * D.frobPower s * D.slope c by simpa
    linarith [(hc s).2, hc.two_le_card_mul_frobPower_mul_slope hs]
  · suffices c (D.varX s) + D.frobPower s * D.slope c ≤ c (D.varY s) by
      simpa [hs, le_sub_iff_add_le]
    linarith [(hc s).1, hc.frobPower_mul_slope_le s]
  · simp [hz.swapVar_eq, hz.merge_eq, hz.poleOrder_eq_zero, hz.zeroOrder_eq_zero]

/-- At a finite point a variable `y` weighs `c y - D.zeroOrder y * D.slope c`. If `c` rises from
`X_s` to `Y_s` by amounts in `[1 / 2, 1]`, then `c z + 1 / 20` is at most `2` plus the weight of
`y`, both for `y = z` and for `y = D.swapVar z`. -/
theorem HasBoundedIncrements.add_le_sub_zeroOrder_mul_slope_add_two
    (hc : D.HasBoundedIncrements c) (z : ZMod N × Fin k) :
    c z + 20⁻¹ ≤ c (D.swapVar z) - D.zeroOrder (D.swapVar z) * D.slope c + 2 ∧
      c z + 20⁻¹ ≤ c z - D.zeroOrder z * D.slope c + 2 := by
  have := T.neZero
  rcases D.var_cases z with rfl | rfl | ⟨s, hs, rfl | rfl⟩ | hz
  · suffices c (D.varY D.letter) + 20⁻¹ ≤ c (D.varX D.letter) + 2 by simpa [card_mul_slope]
    linarith [(hc D.letter).2]
  · norm_num [card_mul_slope]
  · suffices c (D.varY s) + 20⁻¹ ≤ c (D.varX s) + 2 ∧
        c (D.varY s) + 20⁻¹ ≤ c (D.varY s) - D.frobPower s * D.slope c + 2 by simpa [hs]
    constructor <;> linarith [(hc s).2, hc.frobPower_mul_slope_le s]
  · suffices c (D.varX s) + 20⁻¹ ≤ c (D.varY s) - D.frobPower s * D.slope c + 2 ∧
        (20⁻¹ : ℝ) ≤ 2 by simpa [hs]
    constructor <;> linarith [(hc s).1, hc.frobPower_mul_slope_le s]
  · norm_num [hz.swapVar_eq, hz.zeroOrder_eq_zero]

/-- **Expansion at the finite point `ι_i(r)`.** Let the weights `c` rise from `X_s` to `Y_s` by
amounts in `[1 / 2, 1]`, and let each term of the translate of `f` by `(D.swapTransvection r)⁻¹`
have `w`-adic order plus `c`-weight at least `b`. Substitute `D.mainSubst - D.crossSubst` in `f`,
then replace `t` by `t + ι_i(r)`. The result has level `b` when `w` weighs `1`, `t` weighs
`ρ = D.slope c` and a variable `z` weighs `c z - D.zeroOrder z * ρ`. -/
theorem HasBoundedIncrements.shiftCoeff_aeval_mem (hc : D.HasBoundedIncrements c)
    (r : W) {f : MvPolynomial (ZMod N × Fin k) R}
    (hf : T.polyAction (D.swapTransvection r)⁻¹ f ∈
      gaussFiltration (adicFiltration T.sqrtPrime) c b) :
    shiftCoeff (ZMod N × Fin k) (T.embedding D.letter r) (aeval (D.mainSubst - D.crossSubst) f) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder b := by
  have := T.neZero
  -- `ψ` (act, substitute, shift) is `θ` (signed swap, substitute) up to terms of more weight.
  let E := MvPolynomial (ZMod N × Fin k) R →ₐ[R]
    MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)
  let ψ : E := (shiftCoeff _ (T.embedding D.letter r)).comp
    (.comp (aeval (D.mainSubst - D.crossSubst)) (T.polyAction (D.swapTransvection r)))
  let θ : E := aeval fun z ↦ D.moveSign z • (D.mainSubst - D.crossSubst) (D.swapVar z)
  have h_main (z : ZMod N × Fin k) :
      θ (X z) ∈ T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z) := by
    rw [aeval_X]
    exact zsmul_mem (hc.subst_swapVar_mem_iteratedGaussFiltration z) _
  have h_error (z : ZMod N × Fin k) : ψ (X z) - θ (X z) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (c z + 20⁻¹) := by
    obtain ⟨h_exchange, h_self⟩ := hc.add_le_sub_zeroOrder_mul_slope_add_two z
    rw [aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, shiftCoeff_aeval_swapTransvection_X]
    refine zsmul_mem (sub_mem (antitone_iteratedGaussFiltration _ _ _ _ h_exchange ?_)
      (zsmul_mem (antitone_iteratedGaussFiltration _ _ _ _ h_self ?_) _)) _
    all_goals apply frobeniusError_mul_X_mem hc.slope_pos.le
  have h_level : ψ (T.polyAction (D.swapTransvection r)⁻¹ f) ∈
      T.iteratedGaussFiltration c (D.slope c) D.zeroOrder b :=
    (algHom_sub_mem_of_mem_gaussFiltration θ _ (antitone_iteratedGaussFiltration ..) hf h_main ψ
      h_error algebraMap_mem_iteratedGaussFiltration).left
  have h_cancel :
      T.polyAction (D.swapTransvection r) (T.polyAction (D.swapTransvection r)⁻¹ f) = f := by
    simp [← AlgHom.mul_apply, ← map_mul]
  rwa [AlgHom.comp_apply, AlgHom.comp_apply, h_cancel] at h_level

variable (D) in
/-- The coefficient, a polynomial in `t`, of the monomial obtained from `x ^ α` by writing `X_i`
for `Y_i`. -/
noncomputable def mergedCoeff (α : ZMod N × Fin k →₀ ℕ)
    (p : MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)) : Polynomial R :=
  uniqueAlgEquiv R Unit (p.coeff (mapDomain D.merge α))

theorem mergedCoeff_add (α : ZMod N × Fin k →₀ ℕ)
    (p p' : MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)) :
    D.mergedCoeff α (p + p') = D.mergedCoeff α p + D.mergedCoeff α p' := by
  simp [mergedCoeff]

theorem mergedCoeff_sub (α : ZMod N × Fin k →₀ ℕ)
    (p p' : MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)) :
    D.mergedCoeff α (p - p') = D.mergedCoeff α p - D.mergedCoeff α p' := by
  simp [mergedCoeff]

/-- Shifting `t` by `x` in the coefficients of `p` shifts the polynomial `D.mergedCoeff α p` by
`x`. -/
theorem mergedCoeff_shiftCoeff (α : ZMod N × Fin k →₀ ℕ) (x : R)
    (p : MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)) :
    D.mergedCoeff α (shiftCoeff (ZMod N × Fin k) x p) = (D.mergedCoeff α p).taylor x := by
  simpa [mergedCoeff, shiftCoeff, coeff_map] using
    (uniqueAlgEquiv R Unit).apply_symm_apply ((D.mergedCoeff α p).taylor x)

/-- Let `p` have level `b` in `T.iteratedGaussFiltration c ρ v`, and let `X_i` and `Y_i` have the
same weight there. The coefficient of `t ^ j` in `D.mergedCoeff α p` is divisible by `w ^ (l + 1)`
once `b` less the weight of `t ^ j x ^ α` exceeds `l`. -/
theorem pow_dvd_coeff_mergedCoeff {α : ZMod N × Fin k →₀ ℕ}
    {p : MvPolynomial (ZMod N × Fin k) (MvPolynomial Unit R)} {l : ℕ} (j : ℕ)
    (hp : p ∈ T.iteratedGaussFiltration c ρ v b)
    (h_merge_weight : c (D.varX D.letter) - v (D.varX D.letter) * ρ =
      c (D.varY D.letter) - v (D.varY D.letter) * ρ)
    (hj : l < b - (weight c α - weight v α * ρ) - j * ρ) :
    T.sqrtPrime ^ (l + 1) ∣ (D.mergedCoeff α p).coeff j := by
  have h_var (z : ZMod N × Fin k) : c (D.merge z) - v (D.merge z) * ρ = c z - v z * ρ := by
    grind [merge]
  have h_weight : weight (fun z ↦ c z - v z * ρ) (mapDomain D.merge α) =
      weight c α - weight v α * ρ := by
    rw [weight_apply, sum_mapDomain_index (by simp) (by simp [add_mul])]
    simp [h_var, weight_apply, mul_sub, Finsupp.sum_mul, mul_assoc]
  have h_coeff : T.sqrtPrime ^ ⌈b - (weight c α - weight v α * ρ) - j * ρ⌉₊ ∣
      (D.mergedCoeff α p).coeff j := by
    rw [mergedCoeff, coeff_uniqueAlgEquiv]
    simpa [h_weight, weight_single] using hp (mapDomain D.merge α) (single () j)
  exact (pow_dvd_pow T.sqrtPrime (lt_ceil.2 hj)).trans h_coeff

/-- An exponent is determined by its image under `D.merge` and its weight for `D.poleOrder`: the
first forgets only how the degree splits between `X_i` and `Y_i`, and the second recovers it. -/
theorem eq_of_mapDomain_merge_eq {α β : ZMod N × Fin k →₀ ℕ}
    (h_merge : mapDomain D.merge β = mapDomain D.merge α)
    (h_weight : weight D.poleOrder β = weight D.poleOrder α) : β = α := by
  have h_merge_add (γ : ZMod N × Fin k →₀ ℕ) :
      mapDomain D.merge γ + single (D.varY D.letter) (γ (D.varY D.letter)) =
        γ + single (D.varX D.letter) (γ (D.varY D.letter)) := by
    induction γ using induction_linear with
    | zero => simp
    | add γ γ' hγ hγ' => grind [mapDomain_add, Finsupp.add_apply, Finsupp.single_add]
    | single z n => by_cases hz : z = D.varY D.letter <;> simp [merge, hz, Ne.symm, add_comm]
  have h_pole_merge (γ : ZMod N × Fin k →₀ ℕ) : weight D.poleOrder (mapDomain D.merge γ) =
      weight D.poleOrder γ + γ (D.varY D.letter) * D.card := by
    simpa [weight_single] using congrArg (weight D.poleOrder) (h_merge_add γ)
  have h_sum : weight D.poleOrder α + β (D.varY D.letter) * D.card =
      weight D.poleOrder α + α (D.varY D.letter) * D.card := by
    rw [← h_pole_merge, ← h_merge, h_pole_merge, h_weight]
  have h_exponent : β (D.varY D.letter) = α (D.varY D.letter) := by
    simpa [card, T.prime.ne_zero] using h_sum
  refine add_right_cancel (b := single (D.varX D.letter) (α (D.varY D.letter))) ?_
  rw [← h_merge_add α, ← h_merge, ← h_exponent, h_merge_add β]

/-- In `f` substitute `D.mainSubst`. The coefficient of `t ^ d` in `D.mergedCoeff α` of the result,
with `d` the weight of `α` for `D.poleOrder`, is the coefficient of `x ^ α` in `f`: no other
monomial of `f` contributes to it. -/
theorem coeff_mergedCoeff_aeval_mainSubst (α : ZMod N × Fin k →₀ ℕ)
    (f : MvPolynomial (ZMod N × Fin k) R) :
    (D.mergedCoeff α (aeval D.mainSubst f)).coeff (weight D.poleOrder α) = f.coeff α := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial β r =>
    have h_image : aeval D.mainSubst (monomial β r) =
        monomial (mapDomain D.merge β) (monomial (single () (weight D.poleOrder β)) r) := by
      simp [mainSubst, aeval_monomial, X, C_mul_monomial, monomial_pow, Finsupp.prod,
        ← monomial_sum_prod, mapDomain, weight_apply, Finsupp.sum, single_finsetSum]
    have h_iff : mapDomain D.merge β = mapDomain D.merge α ∧
        weight D.poleOrder β = weight D.poleOrder α ↔ β = α :=
      ⟨fun h ↦ eq_of_mapDomain_merge_eq h.left h.right, fun h ↦ by simp [h]⟩
    rw [h_image, mergedCoeff, coeff_uniqueAlgEquiv, coeff_monomial, coeff_monomial]
    split_ifs <;> simp_all [coeff_monomial]
  | add p p' hp hp' => simp [mergedCoeff_add, ← hp, ← hp']

/-- **Zeros against degree.** Let the weights `c` rise from `X_s` to `Y_s` by amounts in
`[1 / 2, 1]`. Suppose that in all translates of `f` by `SL₂(W)` placed in the rows and columns
`a`, `a'` each term has `w`-adic order plus `c`-weight at least `l + c · α`, and that `w ^ (l + 1)`
does not divide the coefficient of `x ^ α` in `f`. Let `ν` be the weight of `α` for
`D.zeroOrder` and `q ν'` its weight for `D.poleOrder`. Then `ν q ≤ q ν'`. -/
theorem HasBoundedIncrements.weight_zeroOrder_mul_card_le
    (hc : D.HasBoundedIncrements c) {f : MvPolynomial (ZMod N × Fin k) R}
    {α : ZMod N × Fin k →₀ ℕ} {l : ℕ}
    (h_least : ∀ g ∈ rootSL W D.fst D.snd,
      T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) c (l + weight c α))
    (h_not_dvd : ¬T.sqrtPrime ^ (l + 1) ∣ f.coeff α) :
    weight D.zeroOrder α * D.card ≤ weight D.poleOrder α := by
  have := T.neZero
  -- `Φ` is the auxiliary binary form in the affine coordinate `t`, modulo `w ^ (l + 1)`. Its degree
  -- is at most `q ν'`, and it vanishes to order at least `ν` at the `q` finite rational points.
  let p := aeval (D.mainSubst - D.crossSubst) f
  let Φ : Polynomial (R ⧸ Ideal.span {T.sqrtPrime ^ (l + 1)}) :=
    (D.mergedCoeff α p).map (Ideal.Quotient.mk _)
  obtain ⟨h_infinity, h_cross⟩ := hc.aeval_mem_and_sub_mem_iteratedGaussFiltration
    (by simpa using h_least 1 (one_mem _))
  have h_merge_weight : c (D.varX D.letter) - D.poleOrder (D.varX D.letter) * -D.slope c =
      c (D.varY D.letter) - D.poleOrder (D.varY D.letter) * -D.slope c := by
    simp [card_mul_slope]
  -- Modulo `w ^ (l + 1)` the coefficient of `t ^ (q ν')` is the coefficient of `x ^ α` in `f`.
  have h_top : T.sqrtPrime ^ (l + 1) ∣
      (D.mergedCoeff α p).coeff (weight D.poleOrder α) - f.coeff α := by
    rw [← coeff_mergedCoeff_aeval_mainSubst (D := D), ← Polynomial.coeff_sub, ← mergedCoeff_sub]
    exact pow_dvd_coeff_mergedCoeff _ h_cross h_merge_weight (by linarith)
  have Φ_ne : Φ ≠ 0 := by
    refine fun hΦ ↦ h_not_dvd ((dvd_sub_right ?_).1 h_top)
    simpa [Φ, eq_zero_iff_dvd] using
      congrArg (fun P : Polynomial _ ↦ P.coeff (weight D.poleOrder α)) hΦ
  have Φ_deg : Φ.natDegree ≤ weight D.poleOrder α := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun j hj ↦ ?_
    have h_gap : weight D.poleOrder α * D.slope c < j * D.slope c := by
      gcongr
      exact hc.slope_pos
    rw [Polynomial.coeff_map, eq_zero_iff_dvd]
    exact pow_dvd_coeff_mergedCoeff j h_infinity h_merge_weight (by linarith)
  have Φ_zero (r : W) : Polynomial.X ^ weight D.zeroOrder α ∣
      Φ.comp (Polynomial.X +
        Polynomial.C (((Ideal.Quotient.mk _).comp (T.embedding D.letter)) r)) := by
    rw [← Polynomial.taylor_apply]
    refine Polynomial.X_pow_dvd_iff.2 fun j hj ↦ ?_
    have h_gap : j * D.slope c < weight D.zeroOrder α * D.slope c := by
      gcongr
      exact hc.slope_pos
    have h_shift : shiftCoeff _ (T.embedding D.letter r) p ∈
        T.iteratedGaussFiltration c (D.slope c) D.zeroOrder (l + weight c α) :=
      hc.shiftCoeff_aeval_mem r (h_least _ (inv_mem (D.swapTransvection_mem_rootSL r)))
    rw [RingHom.comp_apply, ← Polynomial.map_taylor, ← mergedCoeff_shiftCoeff,
      Polynomial.coeff_map, eq_zero_iff_dvd]
    exact pow_dvd_coeff_mergedCoeff j h_shift (by simp [card_mul_slope]) (by linarith)
  calc weight D.zeroOrder α * D.card
      = weight D.zeroOrder α * Nat.card (IsLocalRing.ResidueField W) := by
        rw [T.card_residueField, card]
    _ ≤ Φ.natDegree := stepanov_count _ _ Φ_ne Φ_zero
    _ ≤ weight D.poleOrder α := Φ_deg

end RootAt

/-- **The root lemma** ((b) of the roadmap's section 1.3). Let the weights `c` of the variables rise
from `ū_s = T.rootVar a' a s` to `u_s = T.rootVar a a' s` by amounts in `[1 / 2, 1]` (so that
`a ≠ a'`). Suppose that every translate `g • f`, `g ∈ SL₂^{a,a'}(W)`, lies in Gauss level
`l + c · α` for the `w`-adic filtration, and that `w ^ (l + 1)` does not divide the coefficient of
`x ^ α` in `f`. Then the defect of `α` at any letter `i` along `(a, a')` is at most `0`. These
bounds along the roots are Pieri's inequalities for the exponent of a term that is least among
all translates. -/
theorem defect_nonpos_of_extreme_term (T : FrobeniusCycle N W R) {a a' : Fin k} (i : ZMod N)
    {c : ZMod N × Fin k → ℝ}
    (hc : ∀ s : ZMod N, c (T.rootVar a a' s) - c (T.rootVar a' a s) ∈ Set.Icc 2⁻¹ 1)
    {f : MvPolynomial (ZMod N × Fin k) R} {α : ZMod N × Fin k →₀ ℕ} {l : ℕ}
    (h_least : ∀ g ∈ rootSL W a a',
      T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) c (l + weight c α))
    (h_not_dvd : ¬T.sqrtPrime ^ (l + 1) ∣ f.coeff α) :
    weight (T.defectWeight i a a') α ≤ 0 := by
  have := T.neZero
  -- For `a = a'` the weights would not rise from `ū_s = u_s` to `u_s`.
  have ha : a ≠ a' := by
    rintro rfl
    have := (hc i).1
    norm_num at this
  let D : T.RootAt k := ⟨i, a, a', ha⟩
  -- Stepanov's count gives `ν q ≤ q ν'`, and the defect is `(ν - ν') / (q - 1)`.
  have h_count : weight D.zeroOrder α * D.card ≤ weight D.poleOrder α :=
    RootAt.HasBoundedIncrements.weight_zeroOrder_mul_card_le (D := D) hc h_least h_not_dvd
  have h_card : (1 : ℝ) < D.card := by simpa [RootAt.card] using T.one_lt_q
  have h_defect : weight (T.defectWeight D.letter D.fst D.snd) α =
      (weight D.zeroOrder α - weight D.poleOrder α / D.card) / (D.card - 1) := by
    simp [weight_eq_sum, D.defectWeight_eq, mul_sub, mul_div, ← Finset.sum_div]
  refine h_defect.trans_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ?_) (by linarith))
  exact (le_div_iff₀ D.cast_card_pos).2 (mod_cast h_count)

/-- The twisted action does not raise the total degree. -/
theorem totalDegree_polyAction_le (T : FrobeniusCycle N W R) (g : GL (Fin k) W)
    (f : MvPolynomial (ZMod N × Fin k) R) : (T.polyAction g f).totalDegree ≤ f.totalDegree := by
  have h_linear (x : ZMod N × Fin k) : (T.polyAction g (X x)).IsHomogeneous 1 := by
    rw [polyAction_X]
    exact .sum _ _ 1 fun b _ ↦ isHomogeneous_C_mul_X _ (x.1, b)
  have h_term (α : ZMod N × Fin k →₀ ℕ) :
      (T.polyAction g (monomial α (f.coeff α))).IsHomogeneous (1 * α.degree) := by
    rw [aeval_unique (T.polyAction g)]
    exact (isHomogeneous_monomial _ rfl).aeval _ h_linear
  conv_lhs => rw [f.as_sum, map_sum]
  exact totalDegree_finsetSum_le fun α hα ↦
    (h_term α).totalDegree_le.trans ((one_mul _).trans_le (le_totalDegree hα))

/-- The weight of `α` for `depth - (defect weights) / 3` is its weight for `depth` minus a third of
its defect. -/
theorem weight_sub_defectWeight_div_three (T : FrobeniusCycle N W R) {a a' : Fin k} (i : ZMod N)
    (depth : ZMod N × Fin k → ℝ) (α : ZMod N × Fin k →₀ ℕ) :
    weight (fun x ↦ depth x - T.defectWeight i a a' x / 3) α =
      weight depth α - weight (T.defectWeight i a a') α / 3 := by
  have := T.neZero
  simp [weight_eq_sum, mul_sub, mul_div, ← Finset.sum_div]

/-- The weights `δ - (defect weights) / 3` rise by an amount in `[1 / 2, 1]` from `ū_s` to `u_s`
when the weights `δ` rise by `1`. -/
theorem sub_defectWeight_div_three_mem_Icc (T : FrobeniusCycle N W R) {a a' : Fin k} (i : ZMod N)
    {δ : ZMod N × Fin k → ℝ}
    (h_step : ∀ s : ZMod N, δ (T.rootVar a a' s) - δ (T.rootVar a' a s) = 1) (s : ZMod N) :
    (δ (T.rootVar a a' s) - T.defectWeight i a a' (T.rootVar a a' s) / 3) -
      (δ (T.rootVar a' a s) - T.defectWeight i a a' (T.rootVar a' a s) / 3) ∈
        Set.Icc (2⁻¹ : ℝ) 1 := by
  have h_rise := T.defectWeight_sub_mem_Icc s (i := i) (a := a) (a' := a')
  constructor <;> linarith [h_step s, h_rise.1, h_rise.2]

/-- Let `t ≤ v₀`, and suppose that whenever some translate of `f` by `SL₂^{a,a'}(W)` has a
coefficient at `x ^ α` not divisible by `w ^ (l + 1)` and `l + ω · α < v₀`, then
`t ≤ l + ω · α`. Then every such translate lies in Gauss level `t` for the weights `ω`. -/
private theorem polyAction_mem_of_forall_low (T : FrobeniusCycle N W R) {a a' : Fin k}
    {ω : ZMod N × Fin k → ℝ} {f : MvPolynomial (ZMod N × Fin k) R} {v₀ t : ℝ} (ht : t ≤ v₀)
    (h_low : ∀ (α : ZMod N × Fin k →₀ ℕ) (l : ℕ), l + weight ω α < v₀ →
      (∃ g ∈ rootSL W a a', ¬T.sqrtPrime ^ (l + 1) ∣ (T.polyAction g f).coeff α) →
        t ≤ l + weight ω α)
    {g : GL (Fin k) W} (hg : g ∈ rootSL W a a') :
    T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) ω t := by
  intro α
  by_contra h_not
  obtain ⟨l, hl⟩ : ∃ l : ℕ, ⌈t - weight ω α⌉₊ = l + 1 :=
    exists_eq_succ_of_ne_zero fun h_zero ↦ h_not (by simp [h_zero])
  have h_lt : l < t - weight ω α := lt_ceil.1 (by lia)
  linarith [h_low α l (by linarith) ⟨g, hg, by simpa [hl] using h_not⟩]

/-- **A large defect forces a divisible coefficient** ((c) of the roadmap's section 1.3). Let
the weights `δ` rise by `1` from `ū_s` to `u_s` in each letter (so that `a ≠ a'`). If every
translate of `f` by `SL₂^{a,a'}(W)` lies in Gauss level `v₀` for `δ`, then `f` lies in Gauss level
`v₀` for the weights `δ - (defect weights at i along (a, a')) / 3`: each term has order plus
`δ`-weight at least `v₀` plus a third of its defect. -/
theorem mem_gaussFiltration_sub_defect_div_three (T : FrobeniusCycle N W R) {a a' : Fin k}
    (i : ZMod N) {δ : ZMod N × Fin k → ℝ}
    (h_step : ∀ s : ZMod N, δ (T.rootVar a a' s) - δ (T.rootVar a' a s) = 1)
    {v₀ : ℝ} {f : MvPolynomial (ZMod N × Fin k) R}
    (hf : ∀ g ∈ rootSL W a a',
      T.polyAction g f ∈ gaussFiltration (adicFiltration T.sqrtPrime) δ v₀) :
    f ∈ gaussFiltration (adicFiltration T.sqrtPrime)
      (fun x ↦ δ x - T.defectWeight i a a' x / 3) v₀ := by
  have := T.neZero
  -- Let `ω` be `δ` minus a third of the defect weight. Suppose that some translate has a term
  -- whose order plus `ω`-weight is below `v₀`, and take a least such term. By
  -- `defect_nonpos_of_extreme_term` its defect is at most `0`, so its order plus `δ`-weight is
  -- below `v₀` as well, against the hypothesis.
  set ω : ZMod N × Fin k → ℝ := fun x ↦ δ x - T.defectWeight i a a' x / 3
  -- `(α, l) ∈ low`: in some translate the term at `α` has order at most `l`, and `l + ω · α < v₀`.
  let low : Set ((ZMod N × Fin k →₀ ℕ) × ℕ) := {x | x.2 + weight ω x.1 < v₀ ∧
    ∃ g ∈ rootSL W a a', ¬T.sqrtPrime ^ (x.2 + 1) ∣ (T.polyAction g f).coeff x.1}
  suffices h_empty : ¬low.Nonempty by
    simpa using T.polyAction_mem_of_forall_low le_rfl
      (fun α l h_lt h_g ↦ absurd ⟨(α, l), h_lt, h_g⟩ h_empty) (one_mem _)
  intro h_ne
  -- The degree of `f` bounds `α`, and `v₀` bounds `l`.
  have h_finite : low.Finite := by
    refine ((finite_of_degree_le f.totalDegree).biUnion fun α _ ↦
      (Set.finite_singleton α).prod (Set.finite_Iio ⌈v₀ - weight ω α⌉₊)).subset ?_
    rintro ⟨α, l⟩ ⟨h_lt, g, -, h_not⟩
    have h_degree : α.degree ≤ f.totalDegree :=
      (le_totalDegree (MvPolynomial.mem_support_iff.2 fun h_zero ↦ h_not (by simp [h_zero]))).trans
        (T.totalDegree_polyAction_le g f)
    exact Set.mem_biUnion h_degree ⟨rfl, lt_ceil.2 (by linarith)⟩
  obtain ⟨⟨α, l⟩, ⟨h_lt, g₀, hg₀, h_not⟩, h_min⟩ :
      ∃ x ∈ low, ∀ y ∈ low, x.2 + weight ω x.1 ≤ y.2 + weight ω y.1 :=
    Set.exists_min_image low _ h_finite h_ne
  have h_defect : weight (T.defectWeight i a a') α ≤ 0 :=
    T.defect_nonpos_of_extreme_term i (T.sub_defectWeight_div_three_mem_Icc i h_step)
      (fun g hg ↦ by
        simpa using T.polyAction_mem_of_forall_low h_lt.le
          (fun β m h_lt' h_g ↦ h_min (β, m) ⟨h_lt', h_g⟩) (mul_mem hg hg₀)) h_not
  have h_weight : weight ω α = weight δ α - weight (T.defectWeight i a a') α / 3 :=
    T.weight_sub_defectWeight_div_three i δ α
  have h_depth : l < v₀ - weight δ α := by linarith
  exact h_not ((pow_dvd_pow _ (lt_ceil.2 h_depth)).trans (hf g₀ hg₀ α))

/-- **The root lemma over a field of characteristic `p`** ((d) of the roadmap's section 1.3). Let
`R = K` be a field of characteristic `p`, so that `w = 0`, and let the weights `δ` rise by `1`
from `ū_s` to `u_s` in each letter (so that `a ≠ a'`). If `x ^ α` occurs in `f` and every term of
every translate of `f` by `SL₂^{a,a'}(W)` has `δ`-weight at least `δ · α`, then the defect of `α`
at any letter `i` along `(a, a')` is at most `0`. -/
theorem weight_defectWeight_nonpos_of_least {K : Type*} [Field K] (T : FrobeniusCycle N W K)
    [CharP K T.p] {a a' : Fin k} (i : ZMod N) {δ : ZMod N × Fin k → ℝ}
    (h_step : ∀ s : ZMod N, δ (T.rootVar a a' s) - δ (T.rootVar a' a s) = 1)
    {f : MvPolynomial (ZMod N × Fin k) K} {α : ZMod N × Fin k →₀ ℕ}
    (h_least : ∀ g ∈ rootSL W a a', ∀ β, (T.polyAction g f).coeff β ≠ 0 → weight δ α ≤ weight δ β)
    (hα : f.coeff α ≠ 0) : weight (T.defectWeight i a a') α ≤ 0 := by
  have w_zero : T.sqrtPrime = 0 :=
    (pow_eq_zero_iff two_ne_zero).1 (T.sqrtPrime_sq.trans (CharP.cast_eq_zero K _))
  refine T.defect_nonpos_of_extreme_term i (c := δ) (l := 0) (fun s ↦ by norm_num [h_step])
    (fun g hg β ↦ mem_adicFiltration_of_nonpos fun hβ ↦ ?_) (by simpa [w_zero] using hα)
  simpa using h_least g hg β hβ

end FrobeniusCycle

end TauCeti
