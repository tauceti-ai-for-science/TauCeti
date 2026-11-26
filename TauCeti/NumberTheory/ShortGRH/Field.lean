/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.GaloisEquiv
public import TauCeti.NumberTheory.ShortGRH.Parameters
public import TauCeti.NumberTheory.ShortGRH.PrimeRemainder
public import TauCeti.RingTheory.Cyclotomic.ComplexField
public import TauCeti.NumberTheory.NumberField.CMType.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Units.Basic
import TauCeti.NumberTheory.Cyclotomic.LinearDisjoint
import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.Conductor
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic

/-!
# The field `E = K(ζ_{q₁})` of the shorter route to GRH and its infinite places

Fix parameters `P = (q₀, d)` and `s : ℕ`, and write `q₁ = q₁(s)`. Let `K = ℚ(√-d) ⊆ ℂ`, with
`√-d = i √d`, and let `E = K(ζ)` be the cyclotomic extension of `K` of order `q₁`, with its chosen
primitive `q₁`-th root of unity `ζ`, and a fixed `K`-embedding `ι₀ : E → ℂ`.

The square root `√-d` lies in `ℚ(ζ_m) ⊆ ℂ` exactly when `d ∣ m`, since `-d` is a fundamental
discriminant (`TauCeti.Multiquadratic.mem_adjoin_simple_iff_natAbs_dvd`). As `d ∤ q₁`, the field `K`
meets `ℚ(ζ_{q₁})` in `ℚ`, so the cyclotomic polynomial of order `q₁` stays irreducible over `K`
(`TauCeti.Cyclotomic.irreducible_cyclotomic_of_inf_eq_bot`) and `Gal(E/K) ≅ (ℤ/q₁)ˣ`. As `d ∣ q₁ d`,
the image of `E` lies in `ℚ(ζ_{q₁ d})`: `E` is abelian over `ℚ`, totally complex, hence a CM field.

Since `K` is imaginary quadratic, it has one infinite place, which is complex, and
`g ↦ (place of ι₀ ∘ g)` is a bijection from `Gal(E/K)` onto the infinite places `Φ` of `E`
(`NumberField.InfinitePlace.galEquiv`). The group law of `Gal(E/K)` is transported to `Φ`, so
`Φ ≅ Gal(E/K) ≅ (ℤ/q₁)ˣ`; `g_v ∈ Gal(E/K)` is the automorphism of the place `v`, and
`Φ_v = ι₀ ∘ g_v` the embedding chosen at `v`. The place `[ν]` named by an integer `ν` is that of
the class of `ν` if `ν` is prime to `q₁`, and the identity place otherwise.

## Main definitions

* `TauCeti.ShortGRH.Parameters.K`, `TauCeti.ShortGRH.Parameters.E`, `TauCeti.ShortGRH.Parameters.ζ`,
  `TauCeti.ShortGRH.Parameters.ι₀`: the fields `K ⊆ ℂ` and `E`, the root `ζ`, and `ι₀`.
* `TauCeti.ShortGRH.Parameters.Φ`: the infinite places of `E`, a commutative group.
* `TauCeti.ShortGRH.Parameters.galOfPlace`, `TauCeti.ShortGRH.Parameters.placeMulEquiv`: the
  isomorphisms `Φ ≅ Gal(E/K)` and `Φ ≅ (ℤ/q₁)ˣ`.
* `TauCeti.ShortGRH.Parameters.phi`: the embedding `Φ_v = ι₀ ∘ g_v` chosen at `v`.
* `TauCeti.ShortGRH.Parameters.placeOfInt`, `TauCeti.ShortGRH.Parameters.placeClass`: the place
  `[ν]` named by an integer, and the class of a place modulo a divisor of `q₁`.
* `TauCeti.ShortGRH.Parameters.bigOmega`: `Ω = exp(γ - re (L'/L)(1, χ_K)) · 2π / rd_E`.

## Main results

* `TauCeti.ShortGRH.Parameters.irreducible_cyclotomic`, `TauCeti.ShortGRH.Parameters.toCyclotomic`:
  2.3 (a), with the instances that `E` is abelian over `ℚ` and over `K` and totally complex.
* `TauCeti.ShortGRH.Parameters.algHom_eq_of_mk_eq`: 2.3 (b).
* `TauCeti.ShortGRH.Parameters.card_Φ`, `TauCeti.ShortGRH.Parameters.card_placeClass_eq_one`:
  2.3 (c), `f = T(s) φ(q₀)` and exactly `T(s)` places have class `1` modulo `q₀`.
* `TauCeti.ShortGRH.Parameters.galOfPlace_zeta`,
  `TauCeti.ShortGRH.Parameters.galOfPlace_placeOfInt_zeta`,
  `TauCeti.ShortGRH.Parameters.placeClass_placeOfInt`, `TauCeti.ShortGRH.Parameters.placeOfInt_pow`,
  `TauCeti.ShortGRH.Parameters.phi_mul`,
  `TauCeti.ShortGRH.Parameters.placeClass_placeOfInt_eq_neg_one_iff`: 2.3 (d).
* `TauCeti.ShortGRH.Parameters.exists_zeta_pow_eq`, `TauCeti.ShortGRH.Parameters.star_zeta`,
  `TauCeti.ShortGRH.Parameters.norm_zeta`: 2.3 (e).
* `TauCeti.ShortGRH.Parameters.prod_phi_eq_norm`: 2.3 (f).

## References

The definitions and facts are those of OneSidedPrimeSumBoundsAndAdmissibleData §§2.2, 2.3 in the
`ShortGRH` family of the Tau Ceti roadmap. They are adapted from the shorter formal proof
https://github.com/lsernau/grh-lean (Apache 2.0, Copyright 2026 Anthropic, PBC), file
`grh/src/New/Reduction/Data/FieldsAndPlaces.lean` (`New.Parameters.E`, `New.Parameters.ζ`,
`New.Parameters.galOfPlace`, `New.Parameters.placeMulEquiv`, `New.Parameters.placeOfInt`,
`New.Parameters.placeClass`, `New.Parameters.bigOmega`, `New.Parameters.irreducible_cyclotomic`,
`New.Parameters.toCycloField`, `New.Parameters.algHom_eq_of_mk_eq`, `New.Parameters.numInfPlaces_E`,
`New.Parameters.card_placeClass_eq_one_eq_towerDeg`, `New.Parameters.galOfPlace_placeOfInt_zeta`,
`New.Parameters.placeClass_placeOfInt`, `New.Parameters.placeOfInt_pow`,
`New.Parameters.placeClass_placeOfInt_eq_neg_one_iff`, `New.Parameters.exists_zeta_pow_eq`,
`New.Parameters.star_zeta`, `New.Parameters.norm_zeta_eq_one`, `New.Parameters.prod_phi_eq_norm`).
There `K` is embedded in `ℚ(ζ_d)` by a Gauss sum and irreducibility is read off from degrees; here
both steps go through the conductor of `ℚ(√-d)` and linear disjointness. For cyclotomic extensions
of a quadratic field see L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer
GTM 83 (1997), Chapters 2 and 4.
-/

public section

noncomputable section

open NumberField Polynomial IntermediateField InfinitePlace TauCeti.Cyclotomic

namespace TauCeti.ShortGRH.Parameters

variable (P : Parameters) (s : ℕ)

/-! ### The field `K = ℚ(√-d)` -/

/-- The square root `√-d = i √d ∈ ℂ`. -/
def sqrtNegD : ℂ := Complex.I * (Real.sqrt P.d : ℂ)

/-- `(√-d) ^ 2 = -d`. -/
theorem sqrtNegD_sq : P.sqrtNegD ^ 2 = -(P.d : ℂ) := by
  rw [sqrtNegD, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  ring

/-- The imaginary quadratic field `K = ℚ(√-d) ⊆ ℂ`. -/
def K : IntermediateField ℚ ℂ := ℚ⟮P.sqrtNegD⟯

/-- `√-d ∈ K`. -/
theorem sqrtNegD_mem_K : P.sqrtNegD ∈ P.K := mem_adjoin_simple_self ℚ _

/-- The minimal polynomial of `√-d` over `ℚ` is `X ^ 2 + d`, which has no rational root. -/
theorem minpoly_sqrtNegD : minpoly ℚ P.sqrtNegD = X ^ 2 + C (P.d : ℚ) := by
  have h_deg : (X ^ 2 + C (P.d : ℚ)).natDegree = 2 := by compute_degree!
  refine (minpoly.eq_of_irreducible_of_monic ?_ (by simp [sqrtNegD_sq]) (by monicity!)).symm
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [h_deg]; decide) fun x hx ↦ ?_
  have h_pos : (0 : ℚ) < P.d := by exact_mod_cast P.prime_d.pos
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hx
  nlinarith [sq_nonneg x]

/-- `√-d` is integral over `ℚ`. -/
theorem isIntegral_sqrtNegD : IsIntegral ℚ P.sqrtNegD :=
  ⟨X ^ 2 + C (P.d : ℚ), monic_X_pow_add_C _ two_ne_zero, by simp [sqrtNegD_sq]⟩

/-- `[K : ℚ] = 2`. -/
theorem finrank_K : Module.finrank ℚ P.K = 2 := by
  rw [K, adjoin.finrank P.isIntegral_sqrtNegD, minpoly_sqrtNegD]
  compute_degree!

instance : FiniteDimensional ℚ P.K := Module.finite_of_finrank_eq_succ P.finrank_K

instance : NumberField P.K where

/-- `-d` is a fundamental discriminant: it is the odd prime discriminant of `d ≡ 3 (mod 4)`. -/
theorem isFundamentalDiscr_neg_d : Int.IsFundamentalDiscr (-(P.d : ℤ)) :=
  Multiquadratic.IsPrimeDiscriminant.isFundamentalDiscr <|
    Multiquadratic.isPrimeDiscriminant_iff.2 <| Or.inr ⟨P.d, P.prime_d, P.odd_d,
      (Multiquadratic.oddPrimeDiscriminant_of_mod_four_eq_three
        (by have := P.d_mod_eight; omega)).symm⟩

/-- **The conductor of `K`.** `√-d ∈ ℚ(ζ_m)` if and only if `d ∣ m`. -/
theorem sqrtNegD_mem_complexField_iff {m : ℕ} [NeZero m] :
    P.sqrtNegD ∈ complexField m ↔ P.d ∣ m := by
  rw [complexField_def, Multiquadratic.mem_adjoin_simple_iff_natAbs_dvd (NeZero.pos m)
    isPrimitiveRoot_complexRoot P.isFundamentalDiscr_neg_d (by simp [sqrtNegD_sq])]
  simp

/-- `K ⊆ ℚ(ζ_m)` when `d ∣ m`. -/
theorem K_le_complexField {m : ℕ} [NeZero m] (h : P.d ∣ m) : P.K ≤ complexField m :=
  adjoin_simple_le_iff.2 ((P.sqrtNegD_mem_complexField_iff).2 h)

/-- `K` meets `ℚ(ζ_m)` in `ℚ` when `d ∤ m`. -/
theorem K_inf_complexField {m : ℕ} [NeZero m] (h : ¬P.d ∣ m) : P.K ⊓ complexField m = ⊥ := by
  have h_dvd : Module.finrank ℚ ↥(P.K ⊓ complexField m) ∣ 2 :=
    P.finrank_K ▸ finrank_dvd_of_le_right inf_le_left
  rcases (Nat.dvd_prime Nat.prime_two).1 h_dvd with h1 | h2
  · exact finrank_eq_one_iff.1 h1
  · have h_eq : P.K ⊓ complexField m = P.K :=
      eq_of_le_of_finrank_eq inf_le_left (h2.trans P.finrank_K.symm)
    exact absurd ((P.sqrtNegD_mem_complexField_iff).1
      ((h_eq ▸ inf_le_right : P.K ≤ complexField m) P.sqrtNegD_mem_K)) h

/-- Every embedding of `K` in `ℚ` is complex: it sends `√-d` to a square root of `-d < 0`. -/
instance : IsTotallyComplex P.K where
  isComplex w := by
    rw [← not_isReal_iff_isComplex, ← mk_embedding w, isReal_mk_iff,
      ComplexEmbedding.isReal_iff]
    intro h
    set z := w.embedding ⟨P.sqrtNegD, P.sqrtNegD_mem_K⟩
    have hz : z ^ 2 = -(P.d : ℂ) := by
      rw [← map_pow, show (⟨P.sqrtNegD, P.sqrtNegD_mem_K⟩ : P.K) ^ 2 = -(P.d : P.K) from
        Subtype.ext (by simp [sqrtNegD_sq]), map_neg, map_natCast]
    have h_im : z.im = 0 := Complex.conj_eq_iff_im.1 (RingHom.congr_fun h _)
    have h_re := congrArg Complex.re hz
    simp only [sq, Complex.mul_re, h_im, mul_zero, sub_zero, Complex.neg_re,
      Complex.natCast_re] at h_re
    have h_pos : (0 : ℝ) < P.d := by exact_mod_cast P.prime_d.pos
    nlinarith [mul_self_nonneg z.re]

/-- `K` has a single infinite place: `2 = [K : ℚ] = 2 · #{complex places}`. -/
instance : Subsingleton (InfinitePlace P.K) := by
  rw [← Fintype.card_le_one_iff_subsingleton, card_eq_nrRealPlaces_add_nrComplexPlaces]
  have h := card_add_two_mul_card_eq_rank P.K
  rw [P.finrank_K, IsTotallyComplex.nrRealPlaces_eq_zero] at h
  rw [IsTotallyComplex.nrRealPlaces_eq_zero]
  omega

/-! ### The field `E = K(ζ)` -/

/-- The field `E = K(ζ)` obtained from `K = ℚ(√-d)` by adjoining a primitive root of unity `ζ` of
order `q₁(s)`. -/
def E : Type := CyclotomicField (P.q₁ s) P.K
  deriving Field, Algebra P.K, NumberField

instance : CharZero (P.E s) := inferInstanceAs (CharZero (CyclotomicField _ _))

instance : IsScalarTower ℚ P.K (P.E s) :=
  inferInstanceAs (IsScalarTower ℚ P.K (CyclotomicField _ _))

instance : IsCyclotomicExtension {P.q₁ s} P.K (P.E s) := CyclotomicField.isCyclotomicExtension ..

instance : IsAbelianGalois P.K (P.E s) := IsCyclotomicExtension.isAbelianGalois {P.q₁ s} ..

/-- The chosen primitive `q₁`-th root of unity `ζ ∈ E`. -/
def ζ : P.E s := IsCyclotomicExtension.zeta (P.q₁ s) P.K (P.E s)

/-- `ζ` is a primitive `q₁`-th root of unity. -/
theorem isPrimitiveRoot_ζ : IsPrimitiveRoot (P.ζ s) (P.q₁ s) :=
  IsCyclotomicExtension.zeta_spec (P.q₁ s) P.K (P.E s)

/-- The fixed `K`-embedding `ι₀ : E → ℂ`. -/
def ι₀ : P.E s →ₐ[P.K] ℂ := IsAlgClosed.lift

/-- **2.3 (a)**: the cyclotomic polynomial of order `q₁` is irreducible over `K`. -/
theorem irreducible_cyclotomic : Irreducible (cyclotomic (P.q₁ s) P.K) :=
  irreducible_cyclotomic_of_inf_eq_bot P.K (P.K_inf_complexField fun h ↦
    (Nat.not_coprime_of_dvd_of_dvd P.prime_d.one_lt dvd_rfl h) (P.coprime_q₁_d s).symm)

/-- `[E : K] = φ(q₁)`. -/
theorem finrank_E : Module.finrank P.K (P.E s) = (P.q₁ s).totient :=
  IsCyclotomicExtension.finrank _ (P.irreducible_cyclotomic s)

/-- `[E : ℚ] = 2 φ(q₁)`. -/
theorem finrank_rat_E : Module.finrank ℚ (P.E s) = 2 * (P.q₁ s).totient := by
  rw [← Module.finrank_mul_finrank ℚ P.K, P.finrank_K, finrank_E]

/-- The image of `E` under `ι₀` lies in `ℚ(ζ_{q₁ d})`. -/
theorem ι₀_mem_complexField (y : P.E s) : P.ι₀ s y ∈ complexField (P.q₁ s * P.d) := by
  have h_top := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := P.K)
    (P.isPrimitiveRoot_ζ s)
  have hy : y ∈ Algebra.adjoin P.K {P.ζ s} := h_top ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    have h_pow : (P.ι₀ s (P.ζ s)) ^ (P.q₁ s * P.d) = 1 := by
      rw [← map_pow, pow_mul, (P.isPrimitiveRoot_ζ s).pow_eq_one, one_pow, map_one]
    obtain ⟨i, -, hi⟩ :=
      (isPrimitiveRoot_complexRoot (e := P.q₁ s * P.d)).eq_pow_of_pow_eq_one h_pow
    exact hi ▸ pow_mem (complexRoot_mem_complexField _) i
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact P.K_le_complexField (dvd_mul_left _ _) r.property
  | add x y _ _ hx hy => exact map_add (P.ι₀ s) x y ▸ add_mem hx hy
  | mul x y _ _ hx hy => exact map_mul (P.ι₀ s) x y ▸ mul_mem hx hy

/-- **2.3 (a)**: `E` embeds in `ℚ(ζ_{q₁ d})`. -/
def toCyclotomic : P.E s →ₐ[ℚ] complexField (P.q₁ s * P.d) :=
  ((P.ι₀ s).restrictScalars ℚ).codRestrict (complexField _).toSubalgebra (P.ι₀_mem_complexField s)

/-- **2.3 (a)**: `E` is abelian over `ℚ`. -/
instance : IsAbelianGalois ℚ (P.E s) :=
  have := IsCyclotomicExtension.isAbelianGalois {P.q₁ s * P.d} ℚ (complexField (P.q₁ s * P.d))
  .of_algHom (P.toCyclotomic s)

/-- **2.3 (a)**: `E` is totally complex. -/
instance : IsTotallyComplex (P.E s) := isTotallyComplex_of_algebra P.K _

/-! ### The infinite places of `E` as a group -/

/-- **2.3 (b)**: two `K`-embeddings of `E` in `ℂ` that induce the same infinite place are equal. -/
theorem algHom_eq_of_mk_eq {φ ψ : P.E s →ₐ[P.K] ℂ}
    (h : InfinitePlace.mk φ.toRingHom = InfinitePlace.mk ψ.toRingHom) : φ = ψ := by
  refine AlgHom.toRingHom_injective (eq_of_mk_eq_of_comp_eq (K := P.K) ?_ ?_ h)
  · exact RingHom.ext fun x ↦ by simp
  · exact IsTotallyComplex.isComplex _

/-- The infinite places of `E`; they form a group isomorphic to `Gal(E/K)` (`galOfPlace`). -/
abbrev Φ : Type := InfinitePlace (P.E s)

/-- The bijection `g ↦ (place of ι₀ ∘ g)` from `Gal(E/K)` onto the infinite places of `E`. -/
def placeEquiv : Gal(P.E s/P.K) ≃ P.Φ s :=
  galEquiv (P.ι₀ s).toRingHom (IsTotallyComplex.isComplex _)

open IsMulCommutative in
/-- The group law on the infinite places of `E`, transported from `Gal(E/K)` along `placeEquiv`. -/
instance : CommGroup (P.Φ s) := (P.placeEquiv s).symm.commGroup

open IsMulCommutative in
/-- The isomorphism `v ↦ g_v` from the group of infinite places of `E` to `Gal(E/K)`. -/
def galOfPlace : P.Φ s ≃* Gal(P.E s/P.K) := (P.placeEquiv s).symm.mulEquiv

/-- The isomorphism `Φ ≅ Gal(E/K) ≅ (ℤ/q₁)ˣ`, the second map sending `g` to the class `a` with
`g(ζ) = ζ ^ a`. -/
def placeMulEquiv : P.Φ s ≃* (ZMod (P.q₁ s))ˣ :=
  (P.galOfPlace s).trans (IsCyclotomicExtension.autEquivPow (P.E s) (P.irreducible_cyclotomic s))

/-- The embedding `Φ_v = ι₀ ∘ g_v` of `E` in `ℂ` chosen at the place `v`. -/
def phi (v : P.Φ s) : P.E s →+* ℂ := ((P.ι₀ s).comp (P.galOfPlace s v).toAlgHom).toRingHom

/-- The embedding `Φ_v` chosen at `v` induces `v`. -/
theorem mk_phi (v : P.Φ s) : InfinitePlace.mk (P.phi s v) = v :=
  (P.placeEquiv s).apply_symm_apply v

/-- The embedding `Φ_v` restricts on `K` to the inclusion `K ⊆ ℂ`. -/
@[simp]
theorem phi_algebraMap (v : P.Φ s) (x : P.K) : P.phi s v (algebraMap P.K (P.E s) x) = x := by
  simp [phi]

/-- The place `[ν]` named by an integer `ν`: the place of the class of `ν` if `ν` is prime to `q₁`,
and the identity place otherwise. -/
def placeOfInt (ν : ℤ) : P.Φ s :=
  if h : IsUnit (ν : ZMod (P.q₁ s)) then (P.placeMulEquiv s).symm h.unit else 1

/-- For `m ∣ q₁`, the class modulo `m` of a place: its image in `(ℤ/m)ˣ`. -/
def placeClass {m : ℕ} (h : m ∣ P.q₁ s) : P.Φ s →* (ZMod m)ˣ :=
  (ZMod.unitsMap h).comp (P.placeMulEquiv s).toMonoidHom

/-- The root discriminant `rd_E` of `E`. -/
def rootDiscrE : ℝ := rootDiscr (P.E s)

/-- The number `Ω = exp(γ - re (L'/L)(1, χ_K)) · 2π / rd_E`, with `γ` Euler's constant. -/
def bigOmega : ℝ :=
  Real.exp (Real.eulerMascheroniConstant - (logDeriv (chiK P.d).LFunction 1).re) *
    (2 * Real.pi / P.rootDiscrE s)

/-! ### The CM type of the chosen embeddings -/

/-- An embedding of `E` in `ℂ` is one of the chosen embeddings `Φ_v` exactly when it restricts on
`K` to the inclusion `K ⊆ ℂ`. -/
theorem mem_range_phi_iff (φ : P.E s →+* ℂ) :
    φ ∈ Set.range (P.phi s) ↔ φ.comp (algebraMap P.K (P.E s)) = algebraMap P.K ℂ := by
  refine ⟨?_, fun h ↦ ⟨InfinitePlace.mk φ, ?_⟩⟩
  · rintro ⟨v, rfl⟩
    exact RingHom.ext fun x ↦ by simp
  · let ψ : P.E s →ₐ[P.K] ℂ := { φ with commutes' := fun r ↦ RingHom.congr_fun h r }
    have h_eq := P.algHom_eq_of_mk_eq s (φ := (P.ι₀ s).comp
      (P.galOfPlace s (InfinitePlace.mk φ)).toAlgHom) (ψ := ψ) (P.mk_phi s _)
    exact congrArg AlgHom.toRingHom h_eq

/-- The chosen embeddings `Φ_v`, one above each infinite place of `E`, form a CM type of `E`: an
embedding lies above the inclusion of `K` or above its conjugate, and exactly one of an embedding
and its conjugate lies above the inclusion. -/
def cmType : TauCeti.CMType (P.E s) where
  carrier := Set.range (P.phi s)
  star_mem_iff' φ := by
    have hK : ComplexEmbedding.conjugate (algebraMap P.K ℂ) ≠ algebraMap P.K ℂ := by
      simpa [ComplexEmbedding.isReal_iff] using
        IsTotallyComplex.complexEmbedding_not_isReal (algebraMap P.K ℂ)
    rw [mem_range_phi_iff, mem_range_phi_iff, ← ComplexEmbedding.conjugate,
      ComplexEmbedding.conjugate_comp]
    rcases mk_eq_iff.1 (Subsingleton.elim (InfinitePlace.mk (φ.comp (algebraMap P.K (P.E s))))
      (InfinitePlace.mk (algebraMap P.K ℂ))) with h | h
    · rw [h]
      exact iff_of_false hK (not_not.2 rfl)
    · rw [h]
      refine iff_of_true rfl fun h' ↦ hK ?_
      rwa [h'] at h

/-- The CM type `cmType` is the set of the chosen embeddings `Φ_v`. -/
theorem coe_cmType : (P.cmType s : Set (P.E s →+* ℂ)) = Set.range (P.phi s) := (rfl)

/-! ### 2.3 (c): the number of places -/

/-- `φ(p ^ a n) = p ^ a φ(n)` when `p ∣ n`. -/
private theorem totient_pow_mul_of_dvd {p n : ℕ} (h : p ∣ n) (a : ℕ) :
    (p ^ a * n).totient = p ^ a * n.totient := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', mul_assoc, Nat.totient_mul_of_dvd (h.trans (dvd_mul_left _ _)), ih, mul_assoc]

/-- `φ(q₁) = T φ(q₀)`, since the primes `2` and `3` of `T` divide `q₀`. -/
theorem totient_q₁ : (P.q₁ s).totient = towerDegree s * P.q₀.totient := by
  have h2 : 2 ∣ P.q₀ := P.dvd_q₀_of_dvd_18480 (by norm_num)
  have h3 : 3 ∣ 2 ^ s * P.q₀ := (P.dvd_q₀_of_dvd_18480 (by norm_num)).mul_left _
  rw [q₁, towerDegree, show P.q₀ * (3 ^ (Nat.log 3 s + 5) * 2 ^ s) =
      3 ^ (Nat.log 3 s + 5) * (2 ^ s * P.q₀) by ring, totient_pow_mul_of_dvd h3,
    totient_pow_mul_of_dvd h2, mul_assoc]

/-- **2.3 (c)**: `E` has `f = T φ(q₀)` infinite places. -/
theorem card_Φ : Fintype.card (P.Φ s) = towerDegree s * P.q₀.totient := by
  rw [Fintype.card_congr (P.placeMulEquiv s).toEquiv, ZMod.card_units_eq_totient, totient_q₁]

/-- **2.3 (c)**: exactly `T` infinite places of `E` have class `1` modulo `q₀`. -/
theorem card_placeClass_eq_one :
    (Finset.univ.filter fun v : P.Φ s ↦ P.placeClass s (P.q₀_dvd_q₁ s) v = 1).card =
      towerDegree s := by
  have h_surj : Function.Surjective (P.placeClass s (P.q₀_dvd_q₁ s)) :=
    (ZMod.unitsMap_surjective _).comp (P.placeMulEquiv s).surjective
  have h_index : (P.placeClass s (P.q₀_dvd_q₁ s)).ker.index = P.q₀.totient := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 h_surj, Subgroup.card_top,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have h := (P.placeClass s (P.q₀_dvd_q₁ s)).ker.card_mul_index
  simp only [h_index, Nat.card_eq_fintype_card, card_Φ] at h
  rw [← Fintype.card_subtype, ← Nat.mul_right_cancel (Nat.totient_pos.2 (NeZero.pos P.q₀)) h]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun v ↦ MonoidHom.mem_ker)

/-! ### 2.3 (d): the action of places on `ζ` and the places named by integers -/

/-- **2.3 (d)**: `g_v(ζ) = ζ ^ a` with `a` the class of `v` in `(ℤ/q₁)ˣ`. -/
theorem galOfPlace_zeta (v : P.Φ s) :
    P.galOfPlace s v (P.ζ s) = P.ζ s ^ (P.placeMulEquiv s v : ZMod (P.q₁ s)).val :=
  IsCyclotomicExtension.autEquivPow_spec (P.E s) (P.irreducible_cyclotomic s) _

/-- An integer prime to `q₀` is prime to `q₁ = q₀ T`, since the primes of `T` divide `q₀`. -/
theorem isUnit_intCast_of_isCoprime {ν : ℤ} (h : IsCoprime ν P.q₀) :
    IsUnit (ν : ZMod (P.q₁ s)) := by
  have h2 : IsCoprime (2 : ℤ) ν :=
    h.symm.of_isCoprime_of_dvd_left (by exact_mod_cast P.dvd_q₀_of_dvd_18480 (by norm_num))
  have h3 : IsCoprime (3 : ℤ) ν :=
    h.symm.of_isCoprime_of_dvd_left (by exact_mod_cast P.dvd_q₀_of_dvd_18480 (by norm_num))
  rw [ZMod.isUnit_intCast_iff_isCoprime, q₁, towerDegree]
  push_cast
  exact h.symm.mul_left ((h3.pow_left).mul_left h2.pow_left)

/-- For `ν` prime to `q₀`, the place `[ν]` corresponds to the class of `ν` in `(ℤ/q₁)ˣ`. -/
theorem placeMulEquiv_placeOfInt {ν : ℤ} (h : IsCoprime ν P.q₀) :
    (P.placeMulEquiv s (P.placeOfInt s ν) : ZMod (P.q₁ s)) = ν := by
  simp [placeOfInt, P.isUnit_intCast_of_isCoprime s h]

/-- **2.3 (d)**: for `ν` prime to `q₀`, the class of `[ν]` modulo every `m ∣ q₁` is `ν`. -/
theorem placeClass_placeOfInt {ν : ℤ} (h : IsCoprime ν P.q₀) {m : ℕ} (hm : m ∣ P.q₁ s) :
    (P.placeClass s hm (P.placeOfInt s ν) : ZMod m) = ν := by
  simp [placeClass, ZMod.unitsMap_val, P.placeMulEquiv_placeOfInt s h, ZMod.cast_intCast hm]

/-- **2.3 (d)**: for `ν` prime to `q₀`, `g_{[ν]}(ζ) = ζ ^ ν`. -/
theorem galOfPlace_placeOfInt_zeta {ν : ℤ} (h : IsCoprime ν P.q₀) :
    P.galOfPlace s (P.placeOfInt s ν) (P.ζ s) = P.ζ s ^ ν := by
  have hζ := P.isPrimitiveRoot_ζ s
  have h_ne : P.ζ s ≠ 0 := hζ.ne_zero (NeZero.ne _)
  rw [galOfPlace_zeta, P.placeMulEquiv_placeOfInt s h, ← zpow_natCast, ZMod.val_intCast]
  conv_rhs => rw [← Int.emod_add_mul_ediv ν (P.q₁ s)]
  rw [zpow_add₀ h_ne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]

/-- **2.3 (d)**: `[ν] ^ i = [ν ^ i]`; for `ν` not prime to `q₁` both sides are the identity. -/
theorem placeOfInt_pow (ν : ℤ) (i : ℕ) : P.placeOfInt s ν ^ i = P.placeOfInt s (ν ^ i) := by
  by_cases h : IsUnit (ν : ZMod (P.q₁ s))
  · have h_eq : (h.pow i).unit = h.unit ^ i := Units.ext (by simp)
    simp [placeOfInt, h, h.pow i, h_eq]
  · cases i <;> simp [placeOfInt, h]

/-- **2.3 (d)**: `Φ_{v v'} = Φ_v ∘ g_{v'}`. -/
theorem phi_mul (v v' : P.Φ s) (x : P.E s) :
    P.phi s (v * v') x = P.phi s v (P.galOfPlace s v' x) := by
  simp [phi, map_mul]

/-- **2.3 (d)**: the class of `[ν]` modulo `q₀` is `-1` exactly when `ν ≡ -1 (mod q₀)`. -/
theorem placeClass_placeOfInt_eq_neg_one_iff {ν : ℤ} :
    P.placeClass s (P.q₀_dvd_q₁ s) (P.placeOfInt s ν) = -1 ↔ (ν : ZMod P.q₀) = -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hν : IsUnit (ν : ZMod (P.q₁ s))
    · have := congrArg Units.val h
      simpa [placeClass, placeOfInt, hν, ZMod.unitsMap_val,
        ZMod.cast_intCast (P.q₀_dvd_q₁ s)] using this
    · simp only [placeOfInt, hν, dite_false, map_one] at h
      exact absurd (congrArg Units.val h) (by simpa using P.d_pow_ne_neg_one 0)
  · have h_cop : IsCoprime ν P.q₀ :=
      (ZMod.isUnit_intCast_iff_isCoprime ν P.q₀).1 (by simp [h]) |>.symm
    exact Units.ext (by simp [P.placeClass_placeOfInt s h_cop, h])

/-! ### 2.3 (e): roots of unity -/

/-- **2.3 (e)**: every root of unity of `E` is a power of `ζ`. -/
theorem exists_zeta_pow_eq {y : P.E s} (hy : IsOfFinOrder y) : ∃ k < P.q₁ s, P.ζ s ^ k = y := by
  refine (P.isPrimitiveRoot_ζ s).eq_pow_of_pow_eq_one ?_
  by_contra h_ne
  have : NeZero (orderOf y) := ⟨hy.orderOf_pos.ne'⟩
  -- In `ℚ(ζ_{q₁ d})` the roots of unity have order dividing `q₁ d`, as `q₁ d` is even.
  have h_even : Even (P.q₁ s * P.d) :=
    (even_iff_two_dvd.2 ((P.dvd_q₀_of_dvd_18480 (by norm_num)).trans (P.q₀_dvd_q₁ s))).mul_right _
  have h_dvd : orderOf y ∣ P.q₁ s * P.d := by
    have := NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
      ((IsPrimitiveRoot.orderOf y).map_of_injective (P.toCyclotomic s).injective)
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := P.q₁ s * P.d)] at this
    simpa [h_even] using this
  -- So `y ^ q₁` is a primitive `d`-th root of unity.
  have h_d : IsPrimitiveRoot (y ^ P.q₁ s) P.d := IsPrimitiveRoot.iff_orderOf.2 <|
    orderOf_eq_prime (by rwa [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]) h_ne
  -- Then `φ(q₁) (d - 1) = φ(q₁ d) ≤ [E : ℚ] = 2 φ(q₁)`, against `d > 64`.
  have h_le := (P.isPrimitiveRoot_ζ s).lcm_totient_le_finrank (K := ℚ) h_d
    (cyclotomic.irreducible_rat (Nat.lcm_pos (NeZero.pos _) P.prime_d.pos))
  rw [(P.coprime_q₁_d s).lcm_eq_mul, finrank_rat_E, Nat.totient_mul (P.coprime_q₁_d s),
    Nat.totient_prime P.prime_d, mul_comm 2] at h_le
  have := Nat.le_of_mul_le_mul_left h_le (Nat.totient_pos.2 (NeZero.pos _))
  have := P.sixty_four_lt_d
  omega

/-- **2.3 (e)**: complex conjugation on the CM field `E` inverts `ζ`. -/
theorem star_zeta : star (P.ζ s) = (P.ζ s)⁻¹ := by
  have h_norm : ‖P.phi s 1 (P.ζ s)‖ = 1 :=
    ((P.isPrimitiveRoot_ζ s).map_of_injective (P.phi s 1).injective).norm'_eq_one (NeZero.ne _)
  refine (P.phi s 1).injective ?_
  rw [map_inv₀, Complex.inv_eq_conj h_norm]
  exact IsCMField.complexEmbedding_complexConj (P.E s) (P.phi s 1) (P.ζ s)

/-- **2.3 (e)**: `N_{E/K}(ζ) = 1`. -/
theorem norm_zeta : Algebra.norm P.K (P.ζ s) = 1 := by
  have h_le : 18480 ≤ P.q₁ s :=
    Nat.le_of_dvd (NeZero.pos _) (P.dvd_q₀.trans (P.q₀_dvd_q₁ s))
  exact (P.isPrimitiveRoot_ζ s).norm_eq_one (by omega) (P.irreducible_cyclotomic s)

/-! ### 2.3 (f): norms to `K` -/

/-- **2.3 (f)**: `∏_{v ∈ Φ} Φ_v(y) = N_{E/K}(y)` for `y ∈ E`. -/
theorem prod_phi_eq_norm (y : P.E s) :
    ∏ v : P.Φ s, P.phi s v y = (Algebra.norm P.K y : ℂ) := by
  have h_conj (v : P.Φ s) : P.phi s v y = P.phi s 1 (P.galOfPlace s v y) := by
    simpa using P.phi_mul s 1 v y
  have h_norm : algebraMap P.K (P.E s) (Algebra.norm P.K y) = ∏ v, P.galOfPlace s v y := by
    rw [Algebra.norm_eq_prod_automorphisms]
    exact ((P.galOfPlace s).toEquiv.prod_comp (· y)).symm
  rw [← P.phi_algebraMap s 1 (Algebra.norm P.K y), h_norm, map_prod]
  exact Finset.prod_congr rfl fun v _ ↦ h_conj v

end TauCeti.ShortGRH.Parameters
