/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import TauCeti.Algebra.Homology.DerivedCategory.Coproduct
public import TauCeti.Algebra.Homology.DerivedCategory.Projective
public import TauCeti.Algebra.Homology.ModuleCat.KInjective
public import TauCeti.CategoryTheory.ObjectProperty.Orthogonal
public import TauCeti.CategoryTheory.Triangulated.Orthogonal
public import TauCeti.RingTheory.Localization.Away.MayerVietoris

/-!
# Derived completeness with respect to an ideal

Let `A` be a commutative ring and `I` an ideal of `A`. An object `M` of the derived category
`D(A)` of `A`-modules is *derived `I`-complete* (`TauCeti.derivedComplete`) if
`Hom_{D(A)}(A[1/f], M[n]) = 0` for every `f ∈ I` and every `n : ℤ`, that is, if
`RHom_A(A[1/f], M) = 0` for every `f ∈ I` (Stacks, Tag 091S). This is a homotopical condition and
not a separatedness condition: for instance it holds for every `A`-module annihilated by a power
of `I`, placed in any degree (`TauCeti.derivedComplete_singleFunctor_of_pow_le_annihilator`). The
derived `I`-complete objects form a triangulated subcategory, the right orthogonal of the shifts
of the localizations `A[1/f]`, `f ∈ I`.

The elements `f` with `RHom_A(A[1/f], M) = 0` form a radical ideal of `A`
(`TauCeti.derivedCompleteIdeal`, Stacks, Tag 091Q), and `M` is derived `I`-complete exactly when
`I` is contained in it (`TauCeti.derivedComplete_iff_le`). Consequently derived `I`-completeness
can be tested on any set of generators of `I` (`TauCeti.derivedComplete_span_iff`) and depends
only on the radical of `I` (`TauCeti.derivedComplete_radical_iff`); in particular no finiteness of
`I` is needed for these statements.

Derived completeness is detected by cohomology: `M` is derived `I`-complete if and only if every
cohomology module `Hⁿ(M)` is a derived `I`-complete module in the sense of
`TauCeti.IsDerivedComplete`, that is, the telescope map `(xₖ) ↦ (xₖ - f • xₖ₊₁)` is bijective on
sequences in `Hⁿ(M)` for every `f ∈ I`
(`TauCeti.derivedComplete_iff_isDerivedComplete_homology`). In particular an `A`-module placed in
any degree is derived `I`-complete exactly when it is a derived `I`-complete module
(`TauCeti.derivedComplete_singleFunctor_iff`).

## Main definitions and results

* `TauCeti.derivedComplete I`: the derived `I`-complete objects of `D(A)`, a triangulated
  subcategory.
* `TauCeti.derivedCompleteIdeal M`: the radical ideal of `f` with `RHom_A(A[1/f], M) = 0`.
* `TauCeti.derivedComplete_iff_le`: `M` is derived `I`-complete iff `I ≤ derivedCompleteIdeal M`.
* `TauCeti.derivedComplete_span_iff`: derived completeness can be tested on generators.
* `TauCeti.derivedComplete_radical_iff`: derived completeness depends only on the radical.
* `TauCeti.mem_derivedCompleteIdeal_iff_bijective_telescope`: `RHom_A(A[1/f], M) = 0` if and only
  if the telescope map of `f` is bijective on every cohomology module of `M`.
* `TauCeti.derivedComplete_iff_isDerivedComplete_homology`: `M` is derived `I`-complete if and
  only if every `Hⁿ(M)` is a derived `I`-complete module.

## Implementation notes

The proof that these elements form an ideal uses two short exact sequences of `A`-modules:

* for `c, f ∈ A`, with `S = A[1/f]` and `c` also denoting its image in `S`,
  `0 → S[X] → S[X] → A[1/(fc)] → 0`, where the first map is multiplication by `cX - 1`; the
  polynomial ring `S[X]` is a direct sum of copies of `S`, which is handled by the passage of
  orthogonality to coproducts (`DerivedCategory.singleFunctor_hom_eq_zero_of_isColimit`), and
  this shows that `f` in the ideal implies `cf` in the ideal;
* for `f, g ∈ A`, with `h = f + g` and `B = A[1/h]`, the Mayer–Vietoris sequence
  `0 → B → B[1/f] × B[1/g] → B[1/(fg)] → 0` (`IsLocalization.Away.mayerVietoris_exact`), exact
  since `f` and `g` generate the unit ideal of `B`, which shows that `f` and `g` in the ideal
  imply `f + g` in the ideal.

The comparison with cohomology uses the first of these sequences for `S = A` and `c = f`:
`0 → A[X] → A[X] → A[1/f] → 0`. Its distinguished triangle shows that `RHom_A(A[1/f], M) = 0`
exactly when precomposition with multiplication by `fX - 1` is bijective on maps from `A[X]`,
placed in degree zero, to every shift `M⟦n⟧`
(`CategoryTheory.ObjectProperty.leftOrthogonal_obj₃_iff_bijective`). Since `A[X]` is free, such
maps are the `A`-linear maps from `A[X]` to `H⁰(M⟦n⟧) = Hⁿ(M)`
(`DerivedCategory.fromSingleEquivOfProjective`), that is, sequences in `Hⁿ(M)` through the
monomial basis, and on sequences precomposition with `fX - 1` is the negative of the telescope map.

## References

* [Stacks Project, Section 15.93, *Derived completion*](https://stacks.math.columbia.edu/tag/091N),
  Lemma 15.93.1 (Tag 091Q) and Definition 15.93.4 (Tag 091S).
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory Polynomial

universe w u

namespace TauCeti

variable {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- An object `M` of the derived category of `A`-modules is **derived `I`-complete** if every map
from `A[1/f]` placed in degree zero to every shift `M⟦n⟧` vanishes, for every `f ∈ I`, that is,
`RHom_A(A[1/f], M) = 0` for every `f ∈ I` (Stacks, Tag 091S). It is defined as the right
orthogonal of the shifts of these localizations, a triangulated subcategory. -/
def derivedComplete (I : Ideal A) : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  ((ObjectProperty.ofObj fun f : I ↦
    (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away (f : A)))).shiftClosure
      ℤ).rightOrthogonal

instance (I : Ideal A) : (derivedComplete (A := A) I).IsTriangulated := by
  dsimp only [derivedComplete]
  infer_instance

instance (I : Ideal A) : (derivedComplete (A := A) I).IsClosedUnderIsomorphisms := by
  dsimp only [derivedComplete]
  infer_instance

/-! ### The ideal of elements with vanishing derived Hom -/

/-- The objects with no nonzero map to any shift of `M`. -/
private abbrev Orth (M : DerivedCategory (ModuleCat.{u} A)) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  ((ObjectProperty.singleton M).shiftClosure ℤ).leftOrthogonal

variable (A) in
/-- The `A`-module `X` placed in degree zero. -/
private abbrev deg0 (X : Type u) [AddCommGroup X] [Module A X] :
    DerivedCategory (ModuleCat.{u} A) :=
  (singleFunctor (ModuleCat.{u} A) 0).obj (.of A X)

variable {M : DerivedCategory (ModuleCat.{u} A)}

private lemma Orth.of_linearEquiv {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (e : X ≃ₗ[A] Y) (h : Orth M (deg0 A X)) : Orth M (deg0 A Y) :=
  ObjectProperty.prop_of_iso _ ((singleFunctor (ModuleCat.{u} A) 0).mapIso e.toModuleIso) h

private lemma Orth.of_subsingleton (X : Type u) [AddCommGroup X] [Module A X] [Subsingleton X] :
    Orth M (deg0 A X) := fun _ _ _ ↦
  ((singleFunctor (ModuleCat.{u} A) 0).map_isZero
    (ModuleCat.isZero_of_subsingleton _)).eq_of_src _ _

section ShortExact

variable {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
  [AddCommGroup X₃] [Module A X₃] {f : X₁ →ₗ[A] X₂} {g : X₂ →ₗ[A] X₃}
  (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
include hf hfg hg

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
private lemma shortExact :
    (ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero).ShortExact :=
  ModuleCat.shortComplex_shortExact _ hfg hf hg

private lemma Orth.of_shortExact₁ (h₂ : Orth M (deg0 A X₂)) (h₃ : Orth M (deg0 A X₃)) :
    Orth M (deg0 A X₁) :=
  ObjectProperty.ext_of_isTriangulatedClosed₁ _ _
    (shortExact hf hfg hg).singleTriangle_distinguished h₂ h₃

private lemma Orth.of_shortExact₂ (h₁ : Orth M (deg0 A X₁)) (h₃ : Orth M (deg0 A X₃)) :
    Orth M (deg0 A X₂) :=
  ObjectProperty.ext_of_isTriangulatedClosed₂ _ _
    (shortExact hf hfg hg).singleTriangle_distinguished h₁ h₃

private lemma Orth.of_shortExact₃ (h₁ : Orth M (deg0 A X₁)) (h₂ : Orth M (deg0 A X₂)) :
    Orth M (deg0 A X₃) :=
  ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (shortExact hf hfg hg).singleTriangle_distinguished h₁ h₂

end ShortExact

private lemma Orth.prod {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (hX : Orth M (deg0 A X)) (hY : Orth M (deg0 A Y)) : Orth M (deg0 A (X × Y)) :=
  Orth.of_shortExact₂ LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective hX hY

private lemma Orth.finsupp {X ι : Type u} [AddCommGroup X] [Module A X]
    (h : Orth M (deg0 A X)) : Orth M (deg0 A (ι →₀ X)) := by
  have h' := (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1 h
  exact (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 fun n ↦
    singleFunctor_hom_eq_zero_of_isColimit (ModuleCat.finsuppCoconeIsColimit A X ι) fun _ ↦ h' n

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
/-- For an `A`-algebra `S` and `c ∈ S`, multiplication by `cX - 1` on `S[X]` is injective, since
the constant coefficient `-1` is a unit. -/
private lemma mulLeft_C_mul_X_sub_one_injective {S : Type u} [CommRing S] [Algebra A S] (c : S) :
    Function.Injective (LinearMap.mulLeft A (C c * X - 1 : S[X])) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  exact mem_nonZeroDivisors_iff_left.1 <| Polynomial.mem_nonZeroDivisors_of_coeff_mem 0 <| by
    simpa using (isUnit_one.neg : IsUnit (-1 : S)).mem_nonZeroDivisors

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
/-- For an `A`-algebra `S` and `c ∈ S`, the cokernel of multiplication by `cX - 1` on `S[X]` is
the quotient `S[X] ⧸ (cX - 1)`. -/
private lemma exact_mulLeft_C_mul_X_sub_one {S : Type u} [CommRing S] [Algebra A S] (c : S) :
    Function.Exact (LinearMap.mulLeft A (C c * X - 1 : S[X]))
      (Ideal.Quotient.mkₐ A (Ideal.span {C c * X - 1})).toLinearMap := by
  intro p
  simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton', Set.mem_range, LinearMap.mulLeft_apply]
  exact exists_congr fun _ ↦ by rw [mul_comm]

/-- If `RHom(A[1/f], M) = 0` then `RHom(A[1/(cf)], M) = 0`, through the short exact sequence
`0 → S[X] → S[X] → A[1/(fc)] → 0`, with `S = A[1/f]` and first map multiplication by
`cX - 1`. -/
private lemma Orth.away_mul {f : A} (c : A) (hf : Orth M (deg0 A (Localization.Away f))) :
    Orth M (deg0 A (Localization.Away (c * f))) := by
  let S := Localization.Away f
  let q : S[X] := C (algebraMap A S c) * X - 1
  have hq := mulLeft_C_mul_X_sub_one_injective (A := A) (algebraMap A S c)
  have hexact := exact_mulLeft_C_mul_X_sub_one (A := A) (algebraMap A S c)
  have hpoly : Orth M (deg0 A S[X]) :=
    (Orth.finsupp (ι := ULift ℕ) hf).of_linearEquiv ((Finsupp.domLCongr Equiv.ulift).trans
      ((Polynomial.basisMonomials S).repr.restrictScalars A).symm)
  have hquot : Orth M (deg0 A (S[X] ⧸ Ideal.span {q})) :=
    Orth.of_shortExact₃ hq hexact (Ideal.Quotient.mkₐ_surjective A _) hpoly hpoly
  -- The quotient `S[X] ⧸ (cX - 1)` is the localization of `A` away from `f * c`.
  have : IsLocalization.Away (f * c) (AdjoinRoot q) :=
    have := IsLocalization.adjoin_inv (algebraMap A S c)
    IsLocalization.Away.mul' S (AdjoinRoot q) f c
  rw [mul_comm]
  exact hquot.of_linearEquiv
    (IsLocalization.algEquiv (Submonoid.powers (f * c)) (AdjoinRoot q)
      (Localization.Away (f * c))).toLinearEquiv

/-- If `RHom(A[1/f], M) = 0` and `RHom(A[1/g], M) = 0`, then `RHom(A[1/(f + g)], M) = 0`, through
the Mayer–Vietoris sequence of `B = A[1/(f + g)]`, in which `f` and `g` are coprime. -/
private lemma Orth.away_add {f g : A} (hf : Orth M (deg0 A (Localization.Away f)))
    (hg : Orth M (deg0 A (Localization.Away g))) : Orth M (deg0 A (Localization.Away (f + g))) := by
  let B := Localization.Away (f + g)
  have huv : IsCoprime (algebraMap A B f) (algebraMap A B g) :=
    ⟨IsLocalization.Away.invSelf (f + g), IsLocalization.Away.invSelf (f + g), by
      rw [← mul_add, ← map_add, mul_comm, IsLocalization.Away.mul_invSelf]⟩
  have : IsLocalization.Away (algebraMap A B f * algebraMap A B g)
      (Localization.Away (algebraMap A B (f * g))) := by
    rw [← map_mul]
    infer_instance
  let Bu := Localization.Away (algebraMap A B f)
  let Bv := Localization.Away (algebraMap A B g)
  let Buv := Localization.Away (algebraMap A B (f * g))
  have hu : IsUnit (algebraMap B Buv (algebraMap A B f)) := isUnit_of_mul_isUnit_left
    (y := algebraMap B Buv (algebraMap A B g)) (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Buv) (algebraMap A B (f * g)))
  have hv : IsUnit (algebraMap B Buv (algebraMap A B g)) := isUnit_of_mul_isUnit_right
    (x := algebraMap B Buv (algebraMap A B f)) (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Buv) (algebraMap A B (f * g)))
  let ρu : Bu →ₐ[A] Buv :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom A B Buv) _ hu
  let ρv : Bv →ₐ[A] Buv :=
    IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom A B Buv) _ hv
  have hρu (b : B) : ρu (algebraMap B Bu b) = algebraMap B Buv b :=
    IsLocalization.Away.lift_eq _ hu b
  have hρv (b : B) : ρv (algebraMap B Bv b) = algebraMap B Buv b :=
    IsLocalization.Away.lift_eq _ hv b
  let ι : B →ₗ[A] Bu × Bv :=
    (IsScalarTower.toAlgHom A B Bu).toLinearMap.prod (IsScalarTower.toAlgHom A B Bv).toLinearMap
  let δ : Bu × Bv →ₗ[A] Buv :=
    ρu.toLinearMap ∘ₗ LinearMap.fst A Bu Bv - ρv.toLinearMap ∘ₗ LinearMap.snd A Bu Bv
  have hι : Function.Injective ι :=
    IsLocalization.Away.mayerVietoris_injective (Bu := Bu) (Bv := Bv) huv
  have hιδ : Function.Exact ι δ :=
    IsLocalization.Away.mayerVietoris_exact (ρu := ρu.toRingHom) (ρv := ρv.toRingHom) huv hρu hρv
  have hδ : Function.Surjective δ :=
    IsLocalization.Away.mayerVietoris_surjective (ρu := ρu.toRingHom) (ρv := ρv.toRingHom) huv
      hρu hρv
  -- Each localization of `B` is a localization of `A` away from a multiple of `f` or of `g`.
  have e (x : A) : Localization.Away ((f + g) * x) ≃ₗ[A] Localization.Away (algebraMap A B x) :=
    (IsLocalization.algEquiv (Submonoid.powers ((f + g) * x)) _ _).toLinearEquiv
  have hfg := Orth.away_mul ((f + g) * g) hf
  have hfg_eq : (f + g) * g * f = (f + g) * (f * g) := by ring
  rw [hfg_eq] at hfg
  exact Orth.of_shortExact₁ hι hιδ hδ
    (((Orth.away_mul (f + g) hf).of_linearEquiv (e f)).prod
      ((Orth.away_mul (f + g) hg).of_linearEquiv (e g)))
    (hfg.of_linearEquiv (e (f * g)))

/-- The elements `f` of `A` such that every map from `A[1/f]`, placed in degree zero, to every
shift of `M` vanishes, that is, such that `RHom_A(A[1/f], M) = 0`. They form a radical ideal
(`TauCeti.isRadical_derivedCompleteIdeal`; Stacks, Tag 091Q), and `M` is derived `I`-complete
exactly when `I` is contained in it (`TauCeti.derivedComplete_iff_le`). -/
def derivedCompleteIdeal (M : DerivedCategory (ModuleCat.{u} A)) : Ideal A where
  carrier := {f | ∀ (n : ℤ)
    (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧), φ = 0}
  zero_mem' := by
    have : Subsingleton (Localization.Away (0 : A)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : A))
        (S := Localization.Away (0 : A)) ⟨1, pow_one _⟩
    exact (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
      (Orth.of_subsingleton _)
  add_mem' {f g} hf hg := (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
    (Orth.away_add ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hf)
      ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hg))
  smul_mem' c f hf := (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
    (Orth.away_mul c ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hf))

/-- `f` lies in `derivedCompleteIdeal M` if and only if every map from `A[1/f]`, placed in degree
zero, to every shift of `M` vanishes. -/
theorem mem_derivedCompleteIdeal {f : A} :
    f ∈ derivedCompleteIdeal M ↔ ∀ (n : ℤ)
      (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧), φ = 0 :=
  Iff.rfl

/-- The ideal of `f` with `RHom_A(A[1/f], M) = 0` is radical (Stacks, Tag 091Q): `A[1/gⁿ]` is
`A[1/g]` for `n > 0`. -/
theorem isRadical_derivedCompleteIdeal (M : DerivedCategory (ModuleCat.{u} A)) :
    (derivedCompleteIdeal M).IsRadical := by
  rintro g ⟨n, hn⟩
  cases n with
  | zero =>
    rw [pow_zero] at hn
    rw [(derivedCompleteIdeal M).eq_top_of_isUnit_mem hn isUnit_one]
    exact Submodule.mem_top
  | succ n =>
    have : IsLocalization.Away (g ^ (n + 1)) (Localization.Away g) := by
      rw [pow_succ]
      exact IsLocalization.Away.mul_of_isUnit' _ _
        (by simpa using IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away g) g n)
    exact (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).1
      (Orth.of_linearEquiv (IsLocalization.algEquiv (Submonoid.powers (g ^ (n + 1)))
        (Localization.Away (g ^ (n + 1))) (Localization.Away g)).toLinearEquiv
        ((ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).2 hn))

/-- `M` is derived `I`-complete if and only if `I` is contained in the ideal of `f` with
`RHom_A(A[1/f], M) = 0`. -/
theorem derivedComplete_iff_le {I : Ideal A} :
    derivedComplete I M ↔ I ≤ derivedCompleteIdeal M := by
  rw [derivedComplete, ObjectProperty.rightOrthogonal_shiftClosure_iff]
  constructor
  · intro h f hf
    exact h _ (ObjectProperty.ofObj_apply (fun g : I ↦
      (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away (g : A)))) ⟨f, hf⟩)
  · rintro h _ ⟨⟨f, hf⟩⟩
    exact h hf

/-- `M` is derived `I`-complete if and only if every map from `A[1/f]`, placed in degree zero, to
every shift of `M` vanishes, for every `f ∈ I`. -/
theorem derivedComplete_iff {I : Ideal A} :
    derivedComplete I M ↔ ∀ f ∈ I, ∀ (n : ℤ)
      (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧), φ = 0 :=
  derivedComplete_iff_le

/-- Derived completeness can be tested on generators (Stacks, Lemma 15.93.1): `M` is derived
complete with respect to the ideal generated by `s` if and only if `RHom_A(A[1/f], M) = 0` for every
`f ∈ s`. -/
theorem derivedComplete_span_iff (s : Set A) :
    derivedComplete (Ideal.span s) M ↔ ∀ f ∈ s, ∀ (n : ℤ)
      (φ : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ⟶ M⟦n⟧),
        φ = 0 := by
  rw [derivedComplete_iff_le, Ideal.span_le]
  rfl

/-- Derived completeness only depends on the radical of the ideal. -/
@[simp]
theorem derivedComplete_radical_iff {I : Ideal A} :
    derivedComplete I.radical M ↔ derivedComplete I M := by
  rw [derivedComplete_iff_le, derivedComplete_iff_le,
    (isRadical_derivedCompleteIdeal M).radical_le_iff]

/-- Ideals with the same radical have the same derived complete objects. -/
theorem derivedComplete_eq_of_radical_eq {I J : Ideal A} (h : I.radical = J.radical) :
    derivedComplete (A := A) I = derivedComplete J := by
  ext M
  rw [← derivedComplete_radical_iff, h, derivedComplete_radical_iff]

/-- A larger ideal has fewer derived complete objects. -/
theorem derivedComplete_antitone : Antitone (derivedComplete (A := A)) :=
  fun _ _ h _ hM ↦ derivedComplete_iff_le.2 (h.trans (derivedComplete_iff_le.1 hM))

/-- Every object is derived complete with respect to the zero ideal. -/
@[simp]
theorem derivedComplete_bot (M : DerivedCategory (ModuleCat.{u} A)) : derivedComplete ⊥ M :=
  derivedComplete_iff_le.2 bot_le

/-! ### Detection by cohomology -/

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] in
/-- Through the monomial basis of `A[X]`, precomposition with multiplication by `fX - 1` on maps
out of `A[X]` is the negative of the telescope map of `f`. -/
private lemma bijective_mulLeft_comp_iff (f : A) (N : ModuleCat.{u} A) :
    Function.Bijective (fun ψ : ModuleCat.of A A[X] ⟶ N ↦
      ModuleCat.ofHom (LinearMap.mulLeft A (C f * X - 1)) ≫ ψ) ↔
      Function.Bijective (telescope N f) := by
  let e : (ModuleCat.of A A[X] ⟶ N) ≃ (ℕ → N) :=
    ModuleCat.homEquiv.trans ((basisMonomials A).constr A).symm.toEquiv
  have he (ψ : ModuleCat.of A A[X] ⟶ N) :
      e (ModuleCat.ofHom (LinearMap.mulLeft A (C f * X - 1)) ≫ ψ) = -telescope N f (e ψ) := by
    ext k
    have hk : (C f * X - 1 : A[X]) * monomial k 1 = f • monomial (k + 1) 1 - monomial k 1 := by
      rw [sub_mul, one_mul, mul_assoc, X_mul_monomial, C_mul_monomial, smul_monomial, mul_one,
        smul_eq_mul, mul_one]
    simp [e, ModuleCat.homEquiv, hk]
  rw [← e.comp_bijective,
    show e ∘ _ = (Equiv.neg (ℕ → N)) ∘ telescope N f ∘ e from _root_.funext he,
    (Equiv.neg _).comp_bijective, e.bijective_comp]

/-- `f` lies in `derivedCompleteIdeal M`, that is `RHom_A(A[1/f], M) = 0`, if and only if the
telescope map `(xₖ) ↦ (xₖ - f • xₖ₊₁)` is bijective on sequences in every cohomology module
`Hⁿ(M)` (Stacks, Tag 091P). -/
theorem mem_derivedCompleteIdeal_iff_bijective_telescope {M : DerivedCategory (ModuleCat.{u} A)}
    {f : A} : f ∈ derivedCompleteIdeal M ↔
      ∀ n : ℤ, Function.Bijective (telescope ((homologyFunctor (ModuleCat.{u} A) n).obj M) f) := by
  -- The short exact sequence `0 → A[X] → A[X] → A[1/f] → 0`, with first map multiplication by
  -- `fX - 1`, gives a distinguished triangle in `D(A)`.
  have hS := shortExact (A := A) (mulLeft_C_mul_X_sub_one_injective f)
    (exact_mulLeft_C_mul_X_sub_one f) (Ideal.Quotient.mkₐ_surjective A _)
  let T := hS.singleTriangle
  let P := (ObjectProperty.singleton M).shiftClosure ℤ
  have e : (singleFunctor (ModuleCat.{u} A) 0).obj (.of A (Localization.Away f)) ≅ T.obj₃ :=
    (singleFunctor (ModuleCat.{u} A) 0).mapIso
      (Localization.awayEquivAdjoin f).toLinearEquiv.toModuleIso
  -- Maps from `A[X]` placed in degree zero are maps to the zeroth cohomology.
  have key (n : ℤ) : Function.Bijective (fun g : T.obj₂ ⟶ M⟦n⟧ ↦ T.mor₁ ≫ g) ↔
      Function.Bijective (telescope ((homologyFunctor (ModuleCat.{u} A) n).obj M) f) := by
    have : Projective (ModuleCat.of A A[X]) := ModuleCat.projective_of_free (basisMonomials A)
    let E := fromSingleEquivOfProjective 0 (ModuleCat.of A A[X]) (M⟦n⟧)
    have hE : E ∘ (fun g : T.obj₂ ⟶ M⟦n⟧ ↦ T.mor₁ ≫ g) =
        (fun ψ ↦ ModuleCat.ofHom (LinearMap.mulLeft A (C f * X - 1)) ≫ ψ) ∘ E :=
      _root_.funext fun g ↦ fromSingleEquivOfProjective_singleFunctor_map_comp 0 _ g
    rw [← Function.Bijective.of_comp_iff' E.bijective, hE,
      Function.Bijective.of_comp_iff _ E.bijective,
      bijective_mulLeft_comp_iff]
    exact bijective_telescope_congr
      (((homologyFunctor (ModuleCat.{u} A) 0).isoShift n).app M).toLinearEquiv f
  calc f ∈ derivedCompleteIdeal M ↔ P.leftOrthogonal ((singleFunctor (ModuleCat.{u} A) 0).obj
        (.of A (Localization.Away f))) :=
      (ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff _ M).symm
    _ ↔ P.leftOrthogonal T.obj₃ := ObjectProperty.prop_iff_of_iso _ e
    _ ↔ ∀ K, P K → Function.Bijective fun g : T.obj₂ ⟶ K ↦ T.mor₁ ≫ g :=
      ObjectProperty.leftOrthogonal_obj₃_iff_bijective _ _ hS.singleTriangle_distinguished
    _ ↔ ∀ n : ℤ,
        Function.Bijective (telescope ((homologyFunctor (ModuleCat.{u} A) n).obj M) f) := by
      refine ⟨fun h n ↦ (key n).1 (h _ ⟨M, n, Iso.refl _, by simp⟩), ?_⟩
      -- Bijectivity transfers along the isomorphism of an object of `P` with a shift of `M`.
      rintro h K ⟨_, n, e', ⟨⟩⟩
      convert! ((Iso.homCongr (Iso.refl _) e'.symm).bijective.comp ((key n).2 (h n))).comp
        (Iso.homCongr (Iso.refl _) e').bijective using 1
      ext g
      simp

/-- **Derived completeness is detected by cohomology** (Stacks, Section 15.93): an object `M` of
the derived category of `A`-modules is derived `I`-complete if and only if every cohomology module
`Hⁿ(M)` is a derived `I`-complete module. -/
theorem derivedComplete_iff_isDerivedComplete_homology {I : Ideal A}
    {M : DerivedCategory (ModuleCat.{u} A)} :
    derivedComplete I M ↔
      ∀ n : ℤ, IsDerivedComplete I ((homologyFunctor (ModuleCat.{u} A) n).obj M) := by
  simp only [derivedComplete_iff_le, isDerivedComplete_iff]
  exact ⟨fun h n f hf ↦ mem_derivedCompleteIdeal_iff_bijective_telescope.1 (h hf) n,
    fun h f hf ↦ mem_derivedCompleteIdeal_iff_bijective_telescope.2 fun n ↦ h n f hf⟩

/-- An `A`-module placed in any degree is derived `I`-complete if and only if it is a derived
`I`-complete module. -/
theorem derivedComplete_singleFunctor_iff {I : Ideal A} (N : ModuleCat.{u} A) (m : ℤ) :
    derivedComplete I ((singleFunctor (ModuleCat.{u} A) m).obj N) ↔ IsDerivedComplete I N := by
  rw [derivedComplete_iff_isDerivedComplete_homology]
  refine ⟨fun h ↦ (h m).of_linearEquiv
    ((singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) m).app N).toLinearEquiv,
    fun h n ↦ ?_⟩
  obtain rfl | hn := eq_or_ne n m
  · exact h.of_linearEquiv
      ((singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) n).app N).symm.toLinearEquiv
  · -- In the other degrees the cohomology vanishes.
    have hz : IsZero ((homologyFunctor (ModuleCat.{u} A) n).obj
        ((singleFunctor (ModuleCat.{u} A) m).obj N)) := by
      rcases hn.lt_or_gt with h | h
      · exact isZero_of_isGE _ m n h
      · exact isZero_of_isLE _ m n h
    have := ModuleCat.subsingleton_of_isZero hz
    exact (isDerivedComplete_top_iff.2 this).of_le le_top

/-- An `A`-module annihilated by a power of `I`, placed in any degree, is derived `I`-complete. -/
theorem derivedComplete_singleFunctor_of_pow_le_annihilator {I : Ideal A} {N : ModuleCat.{u} A}
    {k : ℕ} (hN : I ^ k ≤ Module.annihilator A N) (m : ℤ) :
    derivedComplete I ((singleFunctor (ModuleCat.{u} A) m).obj N) :=
  (derivedComplete_singleFunctor_iff N m).2 <| IsDerivedComplete.of_pow_smul_eq_bot (k := k) <|
    eq_bot_iff.2 <| Submodule.smul_le.2 fun r hr x _ ↦ by
      simpa using Module.mem_annihilator.1 (hN hr) x

end TauCeti
