/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Parahoric
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.BlockSubst
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Frobenius cycles, the twisted action of `GL_k(W)`, depth and defect

Let `W` be a commutative local ring with finite residue field and `R` a commutative ring. A
*Frobenius cycle* with `N` letters is a circle of ring maps `ι_s : W → R`, `s ∈ ℤ/N`, each
congruent modulo a prime `p` to the `P`-th power of the one before, where `P = p ^ e ≥ 5` and the
residue field of `W` has `q = P ^ N` elements. The letters are alternately even and odd, and `R`
contains a square root `w` of `p`.

The group `GL_k(W)` acts on polynomials over `R` in the variables `x_{s,b}`, one block of `k`
variables `b ∈ Fin k` for each letter `s`, through `ι_s(g)` on an even letter and through
`ι_s((g⁻¹)ᵀ)` on an odd one. This *twisted action* preserves the degree in each letter. On the
forms of degree `n` in each letter, written as coefficient vectors indexed by the exponents of
their monomials, `g` acts by a matrix `ρ_n(g)`. The file then defines the *depth* and the *defect*
of a monomial, and the submodules of forms all of whose translates by a Levi subgroup have
prescribed coefficients in an ideal.

## Main definitions

* `TauCeti.FrobeniusCycle`: the data `p, e, ι_s`, the parities and `w`, with the Frobenius
  congruences `ι_{s+1}(y) ≡ ι_s(y) ^ P (mod p)` and `#(W/𝔪) = P ^ N`.
* `TauCeti.FrobeniusCycle.letterMatrix`, `TauCeti.FrobeniusCycle.polyAction`: the matrix
  `g_s` of `g` at the letter `s`, and the action of `GL_k(W)` on polynomials,
  `x_{s,c} ↦ ∑_b (g_s)_{bc} x_{s,b}`.
* `TauCeti.FrobeniusCycle.Exponents`, `TauCeti.FrobeniusCycle.formOf`,
  `TauCeti.FrobeniusCycle.letterRep`: the exponents `Exp(N, k, n)` of degree `n` in each letter,
  the form `∑_β F_β x^β` of a coefficient vector `F`, and the matrix `ρ_n(g)` of the action on
  such forms.
* `TauCeti.FrobeniusCycle.depth`: the degree of a monomial in the deep variables.
* `TauCeti.FrobeniusCycle.rootVar`, `TauCeti.FrobeniusCycle.defectWeight`: the variables
  `u_s, ū_s` of a root `(a, a')` and the weights whose weighted degree is the defect at a letter.
* `TauCeti.FrobeniusCycle.translatesIn`, `TauCeti.FrobeniusCycle.defectConditions`,
  `TauCeti.FrobeniusCycle.deepForms`: the conditions on translates `Tr_τ(I, B)`, the defect
  conditions `DC(a, a'; I; h)` and the deep forms `Deep(r, d)`.

## Main results

* `TauCeti.FrobeniusCycle.polyAction_formOf`: `ρ_n(g)` is the matrix of the action of `g` on forms
  of degree `n` in each letter.
* `TauCeti.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoric`: for `g` in a parahoric subgroup
  `P_τ(W)`, `p` divides `(g_s)_{ij}` if `s` is even and `τ i < τ j`, or `s` is odd and `τ j < τ i`.
* `TauCeti.FrobeniusCycle.defectWeight_sub_mem_Icc`: the weight of `u_s` minus that of `ū_s` lies in
  `[0, 3 / 2]`.
* `TauCeti.FrobeniusCycle.abs_weight_defectWeight_le`: an exponent of degree at most `d` in each
  letter has defect of absolute value at most `2 d`.

## Implementation notes

The variables are pairs `(s, b)` of a letter `s : ZMod N` and an index `b : Fin k`, so that the
letters are the blocks of `MvPolynomial.IsMultiHomogeneous` and the action is the block
substitution `MvPolynomial.blockLinearForm`. The matrix `ρ_n(g)` is defined by its entries, the
coefficients of the translates of monomials; it is the Kronecker product over the letters of the
`n`-th symmetric powers of the matrices `g_s`, but that description is not needed here.

The definitions and results are adapted from the file
`New/UpperBound/ElementaryDivisors/TwistingData.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC):
`New.FrobeniusCycle`, `New.FrobeniusCycle.letterMatrix`, `New.FrobeniusCycle.polyAction`,
`New.FrobeniusCycle.letterRep`, `New.FrobeniusCycle.polyAction_polyOfCoeffs`,
`New.FrobeniusCycle.depth`, `New.FrobeniusCycle.defectWeight`,
`New.FrobeniusCycle.translatesIn`, `New.FrobeniusCycle.defectConditions`,
`New.FrobeniusCycle.deepForms`, `New.FrobeniusCycle.p_dvd_letterMatrix_of_mem_parahoric`,
`New.FrobeniusCycle.defectWeight_sub_mem_Icc` and `New.FrobeniusCycle.abs_weight_defectWeight_le`.

## References

The twisted action of `GL₂` on Frobenius twists of symmetric powers, and the weight inequalities
for its invariants, are in the spirit of
* E. Ghate, A. Jana, *Modular representations of `GL₂(F_q)` using calculus*, 2025;
* N. Imai, J.-S. Koskivirta, *Automorphic vector bundles on the stack of `G`-zips*, Forum Math.
  Sigma 9 (2021).
-/

@[expose] public section

namespace TauCeti

open Finset Matrix MvPolynomial IsLocalRing

/-- A Frobenius cycle with `N` letters from a local ring `W` to a commutative ring `R`: a prime `p`
with `P = p ^ frobExp ≥ 5`, where the residue field of `W` has `P ^ N` elements; ring maps
`embedding s : W → R` for the letters `s ∈ ℤ/N`, alternately even and odd, with
`embedding (s + 1) ≡ embedding s ^ P` modulo `p`; and an element `sqrtPrime` of `R` with
`sqrtPrime ^ 2 = p`. When `N ≠ 0` the alternation forces `N` to be even. -/
structure FrobeniusCycle (N : ℕ) (W R : Type*) [CommRing W] [IsLocalRing W] [CommRing R] where
  /-- The prime `p`. -/
  p : ℕ
  /-- The exponent `e`, with `P = p ^ e`. -/
  frobExp : ℕ
  /-- The ring maps `ι_s : W → R`, one for each letter `s ∈ ℤ/N`. -/
  embedding : ZMod N → W →+* R
  /-- Whether the letter `s` is even (`true`) or odd (`false`). -/
  isEven : ZMod N → Bool
  /-- A square root `w` of `p` in `R`. -/
  sqrtPrime : R
  prime : p.Prime
  five_le_P : 5 ≤ p ^ frobExp
  sqrtPrime_sq : sqrtPrime ^ 2 = p
  frobenius_congr (s : ZMod N) (y : W) :
    (p : R) ∣ embedding (s + 1) y - embedding s y ^ p ^ frobExp
  isEven_succ (s : ZMod N) : isEven (s + 1) = !isEven s
  card_residueField : Nat.card (ResidueField W) = (p ^ frobExp) ^ N

namespace FrobeniusCycle

variable {N k : ℕ} {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R]
  (T : FrobeniusCycle N W R)

/-- The prime power `P = p ^ e` of a Frobenius cycle. -/
abbrev P : ℕ := T.p ^ T.frobExp

/-- The number `q = P ^ N` of elements of the residue field of `W`. -/
abbrev q : ℕ := T.P ^ N

/-! ### The twisted action -/

/-- The matrix `g_s` of `g ∈ GL_k(W)` at the letter `s`: `ι_s(g)` if `s` is even and
`ι_s((g⁻¹)ᵀ)` if `s` is odd. -/
def letterMatrix (s : ZMod N) : GL (Fin k) W →* GL (Fin k) R :=
  (GeneralLinearGroup.map (T.embedding s)).comp
    (if T.isEven s then MonoidHom.id _ else GeneralLinearGroup.inverseTranspose.toMonoidHom)

theorem coe_letterMatrix (s : ZMod N) (g : GL (Fin k) W) :
    (T.letterMatrix s g : Matrix (Fin k) (Fin k) R) =
      (if T.isEven s then (g : Matrix (Fin k) (Fin k) W) else (↑g⁻¹ : Matrix _ _ W)ᵀ).map
        (T.embedding s) := by
  by_cases h : T.isEven s <;> simp [letterMatrix, h]

/-- The twisted action of `GL_k(W)` on polynomials in the variables `x_{s,b}`: `g` sends `x_{s,c}`
to `∑_b (g_s)_{bc} x_{s,b}`, where `g_s = T.letterMatrix s g`. -/
noncomputable def polyAction :
    GL (Fin k) W →* MvPolynomial (ZMod N × Fin k) R →ₐ[R] MvPolynomial (ZMod N × Fin k) R where
  toFun g := aeval (blockLinearForm fun s c b ↦ (T.letterMatrix s g : Matrix (Fin k) (Fin k) R) b c)
  map_one' := by
    refine algHom_ext fun x ↦ ?_
    simp [blockLinearForm_apply, Units.val_one, Matrix.one_apply, apply_ite C, ite_mul]
  map_mul' g h := by
    refine algHom_ext fun x ↦ ?_
    simp only [map_mul, Units.val_mul, aeval_X, blockLinearForm_apply, Matrix.mul_apply,
      AlgHom.mul_apply, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Under `T.polyAction g` the variable `x_{s,c}` goes to `∑_b (g_s)_{bc} x_{s,b}`. -/
theorem polyAction_X (g : GL (Fin k) W) (x : ZMod N × Fin k) :
    T.polyAction g (X x) =
      ∑ b, C ((T.letterMatrix x.1 g : Matrix (Fin k) (Fin k) R) b x.2) * X (x.1, b) := by
  simp [polyAction, blockLinearForm_apply]

/-- The twisted action preserves the degree in each letter. -/
theorem isMultiHomogeneous_polyAction {d : ZMod N → ℕ} {f : MvPolynomial (ZMod N × Fin k) R}
    (hf : IsMultiHomogeneous d f) (g : GL (Fin k) W) : IsMultiHomogeneous d (T.polyAction g f) :=
  hf.aeval_blockLinearForm _

theorem polyAction_monomial (g : GL (Fin k) W) (γ : ZMod N × Fin k →₀ ℕ) (c : R) :
    T.polyAction g (monomial γ c) = C c * T.polyAction g (monomial γ 1) := by
  conv_lhs => rw [← mul_one c, ← C_mul_monomial]
  rw [map_mul, algHom_C, algebraMap_eq]

/-- A Frobenius cycle has at least one letter: the residue field of `W` has `P ^ N` elements, and
a field has more than one element. -/
theorem ne_zero (T : FrobeniusCycle N W R) : N ≠ 0 := by
  rintro rfl
  have h : Nat.card (ResidueField W) = 1 := by simpa using T.card_residueField
  exact not_subsingleton _ (Nat.card_eq_one_iff_unique.1 h).1

/-- The number of letters of a Frobenius cycle is non-zero, as an instance argument for `ZMod N`
to be finite. -/
theorem neZero (T : FrobeniusCycle N W R) : NeZero N :=
  ⟨T.ne_zero⟩

/-! ### Forms of degree `n` in each letter -/

variable [NeZero N]

variable (N k) in
/-- The exponents `Exp(N, k, n)` of the monomials of degree `n` in each letter, with `k` variables
in each letter. -/
abbrev Exponents (n : ℕ) : Type := ↥(multiMons (Fin k) fun _ : ZMod N ↦ n)

/-- The form `∑_β F_β x^β` of degree `n` in each letter with coefficient vector `F`. -/
noncomputable def formOf (n : ℕ) :
    (Exponents N k n → R) →ₗ[R] MvPolynomial (ZMod N × Fin k) R :=
  Fintype.linearCombination R fun β : Exponents N k n ↦ monomial (β : ZMod N × Fin k →₀ ℕ) 1

omit [IsLocalRing W] in
theorem formOf_apply {n : ℕ} (F : Exponents N k n → R) :
    formOf n F = ∑ β : Exponents N k n, monomial (β : ZMod N × Fin k →₀ ℕ) (F β) := by
  simp [formOf, Fintype.linearCombination_apply, smul_monomial]

omit [IsLocalRing W] in
@[simp]
theorem coeff_formOf {n : ℕ} (F : Exponents N k n → R) (β : Exponents N k n) :
    (formOf n F).coeff β = F β := by
  classical
  rw [formOf_apply, coeff_sum, Finset.sum_eq_single β (fun γ _ hγ ↦ by
    simp [coeff_monomial, Subtype.ext_iff.not.1 hγ]) (by simp)]
  simp

omit [IsLocalRing W] in
theorem isMultiHomogeneous_formOf {n : ℕ} (F : Exponents N k n → R) :
    IsMultiHomogeneous (fun _ ↦ n) (formOf n F) := by
  rw [formOf_apply]
  exact IsMultiHomogeneous.sum _ _ fun β _ ↦
    isMultiHomogeneous_monomial (mem_multiMons.1 β.property) _

omit [IsLocalRing W] in
/-- A form of degree `n` in each letter is the form of its coefficients at `Exp(N, k, n)`. -/
theorem formOf_coeff {n : ℕ} {f : MvPolynomial (ZMod N × Fin k) R}
    (hf : IsMultiHomogeneous (fun _ ↦ n) f) :
    formOf n (fun β : Exponents N k n ↦ f.coeff β) = f := by
  ext γ
  by_cases hγ : γ ∈ multiMons (Fin k) fun _ : ZMod N ↦ n
  · exact coeff_formOf (k := k) _ ⟨γ, hγ⟩
  · obtain ⟨s, hs⟩ : ∃ s, ∑ i, γ (s, i) ≠ n := by simpa using hγ
    rw [(isMultiHomogeneous_formOf _).coeff_eq_zero hs, hf.coeff_eq_zero hs]

/-- The matrix `ρ_n(g)` of `g ∈ GL_k(W)` on forms of degree `n` in each letter: its entry
`(β, α)` is the coefficient of `x^β` in the translate of `x^α`. -/
noncomputable def letterRep (n : ℕ) :
    GL (Fin k) W →* Matrix (Exponents N k n) (Exponents N k n) R where
  toFun g := Matrix.of fun β α ↦ (T.polyAction g (monomial (α : ZMod N × Fin k →₀ ℕ) 1)).coeff β
  map_one' := by
    ext β α
    rw [of_apply, map_one, AlgHom.one_apply, coeff_monomial, Matrix.one_apply]
    exact if_congr (by rw [eq_comm, Subtype.ext_iff]) rfl rfl
  map_mul' g h := by
    ext β α
    -- Expand the translate of `x^α` by `h` in the monomials of degree `n` in each letter.
    have h_expand := formOf_coeff (n := n) (T.isMultiHomogeneous_polyAction
      (isMultiHomogeneous_monomial (mem_multiMons.1 α.property) (1 : R)) h)
    rw [of_apply, map_mul, AlgHom.mul_apply, ← h_expand, formOf_apply, map_sum, coeff_sum,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [polyAction_monomial, coeff_C_mul, of_apply, of_apply, mul_comm]

theorem letterRep_apply (n : ℕ) (g : GL (Fin k) W) (β α : Exponents N k n) :
    T.letterRep n g β α = (T.polyAction g (monomial (α : ZMod N × Fin k →₀ ℕ) 1)).coeff β :=
  rfl

/-- The coefficient of `x^β` in the translate by `g` of the form of `F` is the entry `β` of
`ρ_n(g) F`. -/
theorem coeff_polyAction_formOf {n : ℕ} (g : GL (Fin k) W) (F : Exponents N k n → R)
    (β : Exponents N k n) :
    (T.polyAction g (formOf n F)).coeff β = (T.letterRep n g *ᵥ F) β := by
  simp only [formOf_apply, map_sum, coeff_sum, mulVec, dotProduct, letterRep_apply]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [polyAction_monomial, coeff_C_mul, mul_comm]

/-- `ρ_n(g)` is the matrix of the action of `g` on forms of degree `n` in each letter. -/
theorem polyAction_formOf {n : ℕ} (g : GL (Fin k) W) (F : Exponents N k n → R) :
    T.polyAction g (formOf n F) = formOf n (T.letterRep n g *ᵥ F) := by
  conv_lhs => rw [← formOf_coeff (T.isMultiHomogeneous_polyAction (isMultiHomogeneous_formOf F) g)]
  exact congrArg _ (funext fun β ↦ T.coeff_polyAction_formOf g F β)

/-! ### Depth, defect and the conditions on translates -/

/-- The indicator of the deep variables for `r`: the variable `(s, b)` is deep if `s` is even and
`r ≤ b`, or `s` is odd and `b < r`. -/
def deepIndicator (r : ℕ) (x : ZMod N × Fin k) : ℕ := if T.isEven x.1 ↔ r ≤ (x.2 : ℕ) then 1 else 0

/-- The depth `depth_r(β)` of an exponent of degree `n` in each letter: the degree of `x^β` in the
variables that are deep for `r` (`TauCeti.FrobeniusCycle.deepIndicator`). -/
noncomputable def depth (n r : ℕ) (β : Exponents N k n) : ℕ :=
  Finsupp.weight (T.deepIndicator r) (β : ZMod N × Fin k →₀ ℕ)

/-- For indices `a, a'` and a letter `s`, the variable `u_s`: `(s, a')` if `s` is even and `(s, a)`
if `s` is odd. The variable `ū_s` is `T.rootVar a' a s`. -/
def rootVar (a a' : Fin k) (s : ZMod N) : ZMod N × Fin k := (s, if T.isEven s then a' else a)

omit [NeZero N] in
@[simp]
theorem rootVar_fst (a a' : Fin k) (s : ZMod N) : (T.rootVar a a' s).1 = s :=
  rfl

/-- The weight of the variable `x` in the defect at the letter `i` along the root `(a, a')`. With
`u_s = T.rootVar a a' s` and `ū_s = T.rootVar a' a s`, the variable `u_s` weighs
`P ^ (1 + ((s - 1 - i) mod N)) / (q - 1)`, the variable `ū_s` weighs
`-P ^ ((s - i) mod N) / (q - 1)`, and the other variables weigh `0`. The defect of an exponent
is its weighted degree. -/
noncomputable def defectWeight (i : ZMod N) (a a' : Fin k) (x : ZMod N × Fin k) : ℝ :=
  ((if x = T.rootVar a a' x.1 then (T.P : ℝ) ^ (1 + (x.1 - 1 - i).val) else 0) -
    if x = T.rootVar a' a x.1 then (T.P : ℝ) ^ (x.1 - i).val else 0) / (T.q - 1)

variable (k) in
/-- The labelling `τ_r` of the indices `b : Fin k`: `0` if `b < r` and `1` otherwise. -/
def twoBlock (r : ℕ) (b : Fin k) : ℕ := if (b : ℕ) < r then 0 else 1

/-- The conditions on translates `Tr_τ(I, B)`: the coefficient vectors `F` with `(ρ_n(g) F)_β ∈ I`
for all `g` in the Levi subgroup `L_τ(W)` and all `β ∈ B`. -/
def translatesIn (n : ℕ) (τ : Fin k → ℕ) (I : Ideal R) (B : Set (Exponents N k n)) :
    Submodule R (Exponents N k n → R) where
  carrier := {F | ∀ g ∈ leviSubgroup W τ, ∀ β ∈ B, (T.letterRep n g *ᵥ F) β ∈ I}
  add_mem' hF hG g hg β hβ := by simpa [mulVec_add] using add_mem (hF g hg β hβ) (hG g hg β hβ)
  zero_mem' := by simp
  smul_mem' c F hF g hg β hβ := by
    simpa [mulVec_smul] using I.mul_mem_left c (hF g hg β hβ)

/-- The defect conditions `DC(a, a'; I; h)`: `Tr_{τ_{a'}}(I, B)` for `B` the exponents whose defect
along `(a, a')` exceeds `h` at some letter. -/
abbrev defectConditions (n : ℕ) (a a' : Fin k) (I : Ideal R) (h : ℝ) :
    Submodule R (Exponents N k n → R) :=
  T.translatesIn n (twoBlock k a') I
    {β | ∃ i : ZMod N, h < Finsupp.weight (T.defectWeight i a a') (β : ZMod N × Fin k →₀ ℕ)}

/-- The deep forms `Deep(r, d)`: the coefficient vectors `F` such that every translate of the form
of `F` by `GL_k(W)` has only monomials of depth at least `d`. -/
abbrev deepForms (n r d : ℕ) : Submodule R (Exponents N k n → R) :=
  T.translatesIn n 0 ⊥ {β | T.depth n r β < d}

/-! ### First properties -/

omit [NeZero N] in
theorem one_lt_P : (1 : ℝ) < T.P :=
  mod_cast Nat.one_lt_ofNat.trans_le T.five_le_P

omit [NeZero N] in
theorem one_lt_q : (1 : ℝ) < T.q := by
  have := T.neZero
  simpa using one_lt_pow₀ T.one_lt_P (NeZero.ne N)

omit [NeZero N] in
/-- The ring map of the letter `s + n` is the `P ^ n`-th power of that of the letter `s` modulo
`p`. -/
theorem frobenius_pow_congr (s : ZMod N) (n : ℕ) (y : W) :
    (T.p : R) ∣ T.embedding (s + n) y - T.embedding s y ^ T.P ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Raise the induction hypothesis to the power `P`, then take one step by `frobenius_congr`.
    have h_pow : (T.p : R) ∣ T.embedding (s + n) y ^ T.P - (T.embedding s y ^ T.P ^ n) ^ T.P :=
      ih.trans (sub_dvd_pow_sub_pow ..)
    simpa [← add_assoc, pow_succ, pow_mul] using (T.frobenius_congr (s + n) y).add h_pow

omit [NeZero N] in
/-- The ring map of a letter sends the maximal ideal of `W` into `p R`. -/
theorem p_dvd_embedding_of_mem_maximalIdeal (s : ZMod N) {y : W} (hy : y ∈ maximalIdeal W) :
    (T.p : R) ∣ T.embedding s y := by
  -- As `ι_s y ≡ (ι_s y) ^ q` modulo `p`, the prime `p` divides `ι_s y * ι_s (1 - y ^ (q - 1))`,
  -- whose last factor is a unit.
  have hq : 1 < T.q := mod_cast T.one_lt_q
  have h_unit : IsUnit (1 - y ^ (T.q - 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ (Ideal.pow_mem_of_mem _ hy _ (Nat.sub_pos_of_lt hq))
  have h_factor : T.embedding s y * T.embedding s (1 - y ^ (T.q - 1)) =
      T.embedding s y - T.embedding s y ^ T.q := by
    simp [mul_sub, mul_pow_sub_one, T.prime.ne_zero]
  rw [← (h_unit.map (T.embedding s)).dvd_mul_right, h_factor]
  simpa [ZMod.natCast_self] using T.frobenius_pow_congr s N y

omit [NeZero N] in
/-- **The parahoric congruences** (part of (a) of the roadmap's section 1.3). Let `g` lie in the
parahoric subgroup `P_τ(W)`. Then `p` divides the entry `(i, j)` of `g_s` if `s` is even and
`τ i < τ j`, or if `s` is odd and `τ j < τ i`. -/
theorem p_dvd_letterMatrix_of_mem_parahoric {τ : Fin k → ℕ} {g : GL (Fin k) W}
    (hg : g ∈ parahoricSubgroup W τ) (s : ZMod N) (i j : Fin k)
    (h_even : T.isEven s = true → τ i < τ j) (h_odd : T.isEven s = false → τ j < τ i) :
    (T.p : R) ∣ (T.letterMatrix s g : Matrix (Fin k) (Fin k) R) i j := by
  rw [coe_letterMatrix]
  cases hs : T.isEven s with
  | true =>
    simpa using T.p_dvd_embedding_of_mem_maximalIdeal s
      (mem_parahoricSubgroup_iff.1 hg i j (h_even hs))
  | false =>
    -- The entry comes from the entry `(j, i)` of `g⁻¹`, which is parahoric too.
    simpa using T.p_dvd_embedding_of_mem_maximalIdeal s
      (mem_parahoricSubgroup_iff.1 (inv_mem hg) j i (h_odd hs))

/-! ### Bounds on the defect weights -/

@[simp]
theorem one_add_val_sub_one_sub (s i : ZMod N) :
    1 + (s - 1 - i).val = if s = i then N else (s - i).val := by
  zify
  simp [sub_right_comm, ZMod.cast_sub_one, sub_eq_zero]

omit [NeZero N] in
/-- For every letter `s`, read in `{0, …, N - 1}`, one has `5 P ^ s ≤ q`. -/
theorem five_mul_P_pow_le_q (s : ZMod N) : 5 * T.P ^ s.val ≤ T.q := by
  have := T.neZero
  exact calc 5 * T.P ^ s.val ≤ T.P ^ (s.val + 1) := by grw [pow_succ', T.five_le_P]
      _ ≤ T.P ^ N := Nat.pow_le_pow_right (pow_pos T.prime.pos T.frobExp) s.val_lt

omit [NeZero N] in
theorem five_le_q : (5 : ℝ) ≤ T.q :=
  have := T.neZero
  mod_cast T.five_le_P.trans (Nat.le_self_pow (NeZero.ne N) T.P)

omit [NeZero N] in
/-- **The step of the defect weights** (part of (a) of the roadmap's section 1.3). The weight of
`u_s` minus that of `ū_s` in the defect at any letter lies in `[0, 3 / 2]` (for `a = a'` it is
`0`). -/
theorem defectWeight_sub_mem_Icc {i : ZMod N} {a a' : Fin k} (s : ZMod N) :
    T.defectWeight i a a' (T.rootVar a a' s) - T.defectWeight i a a' (T.rootVar a' a s) ∈
      Set.Icc 0 (3 / 2) := by
  rcases eq_or_ne a a' with rfl | ha
  · rw [sub_self]
    norm_num
  have := T.neZero
  have q_sub_one_pos : (0 : ℝ) < T.q - 1 := sub_pos.2 T.one_lt_q
  have h_ne : T.rootVar a a' s ≠ T.rootVar a' a s := by
    cases h : T.isEven s <;> simp [rootVar, h, ha, Ne.symm ha]
  have h_diff :
      T.defectWeight i a a' (T.rootVar a a' s) - T.defectWeight i a a' (T.rootVar a' a s) =
        (T.P ^ (1 + (s - 1 - i).val) + T.P ^ (s - i).val) / (T.q - 1) := by
    simp [defectWeight, h_ne, h_ne.symm]
    ring
  have h_first : (T.P : ℝ) ^ (1 + (s - 1 - i).val) ≤ T.q :=
    mod_cast Nat.pow_le_pow_right (pow_pos T.prime.pos _) (by linarith [(s - 1 - i).val_lt])
  have h_second : (5 * T.P ^ (s - i).val : ℝ) ≤ T.q := mod_cast T.five_mul_P_pow_le_q (s - i)
  rw [h_diff]
  exact ⟨by positivity, (div_le_iff₀ q_sub_one_pos).2 (by linarith [T.five_le_q])⟩

/-- As `s` runs over the letters, `1 + ((s - 1 - i) mod N)` runs over `1, …, N`, and
`P + P ^ 2 + ⋯ + P ^ N ≤ 2 (q - 1)`. -/
theorem sum_P_pow_le (i : ZMod N) :
    ∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val) ≤ 2 * (T.q - 1) := by
  -- With `S = 1 + P + ⋯ + P ^ (N - 1)` the sum is both `P S` and `S + (q - 1)`.
  set S : ℝ := ∑ s : ZMod N, (T.P : ℝ) ^ (s - i).val with hS
  have h_mul : ∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val) = T.P * S := by
    simp only [pow_add, pow_one, ← mul_sum]
    exact congrArg _ ((Equiv.subRight 1).sum_comp fun s : ZMod N ↦ (T.P : ℝ) ^ (s - i).val)
  have h_term (s : ZMod N) : (T.P : ℝ) ^ (1 + (s - 1 - i).val) =
      T.P ^ (s - i).val + if s = i then (T.q - 1 : ℝ) else 0 := by
    rw [one_add_val_sub_one_sub]
    split_ifs with hs <;> simp [hs]
  have h_add : ∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val) = S + (T.q - 1) := by
    simp only [h_term, sum_add_distrib, Fintype.sum_ite_eq', hS]
  have hP : 5 * S ≤ T.P * S := mul_le_mul_of_nonneg_right (mod_cast T.five_le_P) (by positivity)
  linarith [T.one_lt_q]

/-- **The defect is bounded by the degree** (part of (a) of the roadmap's section 1.3). If `α` has
degree at most `d` in each letter, then its defect at any letter along any root has absolute value
at most `2 d`. -/
theorem abs_weight_defectWeight_le {i : ZMod N} {a a' : Fin k} {α : ZMod N × Fin k →₀ ℕ} {d : ℝ}
    (hα : ∀ s : ZMod N, ∑ b : Fin k, (α (s, b) : ℝ) ≤ d) :
    |Finsupp.weight (T.defectWeight i a a') α| ≤ 2 * d := by
  have q_sub_one_pos : (0 : ℝ) < T.q - 1 := sub_pos.2 T.one_lt_q
  have hd : 0 ≤ d := le_trans (by positivity) (hα i)
  let bound (s : ZMod N) : ℝ := T.P ^ (1 + (s - 1 - i).val) / (T.q - 1)
  have h_var (x : ZMod N × Fin k) : |T.defectWeight i a a' x| ≤ bound x.1 := by
    have h_exp : (x.1 - i).val ≤ 1 + (x.1 - 1 - i).val := by
      rw [one_add_val_sub_one_sub]
      split_ifs
      exacts [(ZMod.val_lt (x.1 - i)).le, le_rfl]
    have h_pow_nonneg : 0 ≤ (T.P : ℝ) ^ (x.1 - i).val := by positivity
    have h_pow_le : (T.P : ℝ) ^ (x.1 - i).val ≤ (T.P : ℝ) ^ (1 + (x.1 - 1 - i).val) :=
      pow_le_pow_right₀ T.one_lt_P.le h_exp
    -- The numerator is a difference of two numbers in `[0, P ^ (1 + (s - 1 - i))]`.
    rw [defectWeight, abs_div, abs_of_pos q_sub_one_pos]
    refine div_le_div_of_nonneg_right (abs_sub_le_iff.2 ⟨?_, ?_⟩) q_sub_one_pos.le
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  calc |Finsupp.weight (T.defectWeight i a a') α|
      ≤ ∑ x : ZMod N × Fin k, α x * |T.defectWeight i a a' x| := by
        simpa [Finsupp.weight_eq_sum, abs_mul] using
          abs_sum_le_sum_abs (fun x ↦ α x * T.defectWeight i a a' x) univ
    _ ≤ ∑ x : ZMod N × Fin k, α x * bound x.1 := by grw [h_var]
    _ = ∑ s : ZMod N, (∑ b : Fin k, (α (s, b) : ℝ)) * bound s := by
        simp only [Fintype.sum_prod_type, sum_mul]
    _ ≤ ∑ s : ZMod N, d * bound s := by grw [hα]
    _ = (∑ s : ZMod N, (T.P : ℝ) ^ (1 + (s - 1 - i).val)) / (T.q - 1) * d := by
        rw [← mul_sum, Finset.sum_div, mul_comm]
    _ ≤ 2 * d := mul_le_mul_of_nonneg_right ((div_le_iff₀ q_sub_one_pos).2 (T.sum_P_pow_le i)) hd

end FrobeniusCycle

end TauCeti
