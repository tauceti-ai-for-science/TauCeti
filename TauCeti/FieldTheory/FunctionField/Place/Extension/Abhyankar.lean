/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.TameInertia
public import TauCeti.FieldTheory.IntermediateField.ScalarTower
import Mathlib.FieldTheory.Normal.Closure
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.Extension.WildInertia
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index

/-!
# Abhyankar's lemma

Let `F' / F` be a finite separable extension of function fields which is the compositum
`F' = F₁ F₂` of two intermediate fields, let `P'` be a place of `F'` over the place `P` of `F`, and
let `Pᵢ = P' ∩ Fᵢ`. **Abhyankar's lemma** (Stichtenoth, Theorem 3.9.1) says that if one of
`P₁ ∣ P` and `P₂ ∣ P` is tame, then
`e(P' ∣ P) = lcm(e(P₁ ∣ P), e(P₂ ∣ P))`.

The proof is group-theoretic and takes place in a finite Galois extension `M / F` containing
`F'`. Fix a place `Q` of `M` over `P'`, and let `G₀ = G₀(Q)` be its inertia group, with residue
extension over `F` separable.

* For an intermediate field `E` of `M / F`, restriction of scalars identifies the inertia group of
  `Q` over `E` with `G₀ ∩ Gal(M / E)`, so the two have the same order
  (`TauCeti.Place.card_comap_fixingSubgroup`) and `e(Q ∩ E ∣ P) = [G₀ : G₀ ∩ Gal(M / E)]`
  (`TauCeti.Place.ramificationIdx_restrict_eq_index`).
* The wild inertia group `G₁` is a normal `p`-subgroup of `G₀` with cyclic quotient
  (`TauCeti.Place.isCyclic_quotient_ramificationGroup_one`), and in characteristic zero it is
  trivial. Tameness of `P₁ ∣ P` makes `[G₀ : G₀ ∩ Gal(M / F₁)]` prime to `|G₁|`, and
  `Gal(M / F₁ F₂) = Gal(M / F₁) ∩ Gal(M / F₂)`.
* The lcm formula then holds for the indices: this is `Subgroup.index_inf_eq_lcm`.

The theorem for an arbitrary finite separable `F' / F` follows by passing to a normal closure
and extending the place.

Stichtenoth assumes a perfect constant field. Here the Galois form only asks for a separable
residue extension at `Q`, and the general form asks for a perfect residue field at `P`. Tameness
of `P₁ ∣ P` enters only as the condition that `e(P₁ ∣ P)` is nonzero in the residue field of `P`;
with a separable residue extension this is `TauCeti.Place.IsTame`, by
`TauCeti.Place.isTame_iff_isSeparable_residueField`.

## Main results

* `TauCeti.Place.card_comap_fixingSubgroup`: the elements of the inertia group of `Q` over `F`
  which fix an intermediate field `E` are as many as the inertia group of `Q` over `E`.
* `TauCeti.Place.ramificationIdx_restrict_eq_index`: `e(Q ∩ E ∣ P)` is the index of
  `G₀ ∩ Gal(M / E)` in `G₀`.
* `TauCeti.Place.ramificationIdx_restrict_sup_eq_lcm_of_isGalois`: **Abhyankar's lemma** for
  intermediate fields of a finite Galois extension.
* `TauCeti.Place.ramificationIdx_restrict_sup_eq_lcm`: **Abhyankar's lemma** for intermediate
  fields of a finite separable extension of a function field (Stichtenoth, Theorem 3.9.1).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.9.1.
* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter IV, §1–§2, for inertia groups of
  subextensions and the structure of `G₀ / G₁`.
-/

public section

namespace TauCeti.Place

universe u v w w'

variable {k : Type u} {F : Type v} {M : Type w}
variable [Field k] [Field F] [Field M] [Algebra k F] [Algebra k M] [Algebra F M]
variable [IsScalarTower k F M]

section Inertia

variable (F) (Q : Place k M)

/-- **The order of the inertia group over an intermediate field** (Serre, *Local Fields*,
Chapter IV, §1): the inertia group of `Q` over an intermediate field `E` has as many elements as
the subgroup of the inertia group `G₀(Q)` over `F` fixing `E`, the bijection being restriction of
scalars from `E` to `F`. -/
theorem card_comap_fixingSubgroup (E : IntermediateField F M) :
    Nat.card (E.fixingSubgroup.comap ((Q.integers.decompositionSubgroup F).subtype.comp
      (ramificationGroup F Q 0).subtype)) = Nat.card (Q.integers.inertiaSubgroup E) := by
  -- Both groups consist of the automorphisms of `M` over `E` that fix `Q` and act trivially on
  -- its residue field; only the scalars over which they are read differ.
  have hres {g : Q.integers.decompositionSubgroup F} {h : Q.integers.decompositionSubgroup E}
      (hgh : ∀ x, (g : M ≃ₐ[F] M) x = (h : M ≃ₐ[E] M) x) :
      g ∈ Q.integers.inertiaSubgroup F ↔ h ∈ Q.integers.inertiaSubgroup E := by
    have hsmul (x : Q.integers) : g • x = h • x := Subtype.ext <| by
      rw [ValuationSubring.coe_decompositionSubgroup_smul,
        ValuationSubring.coe_decompositionSubgroup_smul, hgh]
    simp only [ValuationSubring.mem_inertiaSubgroup_iff, hsmul]
  -- The two maps are `IntermediateField.fixingSubgroupEquiv` and restriction of scalars, neither of
  -- which changes the underlying function (`IntermediateField.coe_fixingSubgroupEquiv_apply`,
  -- `AlgEquiv.restrictScalars_apply`), so the comparisons of functions below hold by `rfl`.
  refine Nat.card_congr
    { toFun x := ⟨⟨E.fixingSubgroupEquiv ⟨_, x.2⟩, ?_⟩, ?_⟩
      invFun y := ⟨⟨⟨(y : Q.integers.decompositionSubgroup E).1.restrictScalars F, ?_⟩, ?_⟩, ?_⟩
      left_inv x := ?_
      right_inv y := ?_ }
  · rw [← restrictScalars_mem_decompositionSubgroup_iff]
    convert (x.1.1 : Q.integers.decompositionSubgroup F).2
    ext
    rfl
  · refine (hres fun _ ↦ rfl).1 ?_
    rw [← ramificationGroup_zero]
    exact x.1.2
  · exact (restrictScalars_mem_decompositionSubgroup_iff Q E _).2 y.1.2
  · rw [ramificationGroup_zero]
    exact (hres fun _ ↦ rfl).2 y.2
  · exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz ↦
      (y : Q.integers.decompositionSubgroup E).1.commutes ⟨z, hz⟩
  · exact Subtype.ext (Subtype.ext (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)))
  · exact Subtype.ext (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl))

end Inertia

section Galois

variable (F) [FiniteDimensional F M] [IsGalois F M] (Q : Place k M)
variable [Algebra.IsSeparable (Q.restrict k F).ResidueField Q.ResidueField]

/-- **The ramification index below `Q` as an index of inertia groups**: for an intermediate field
`E` of a finite Galois extension `M / F` and a place `Q` of `M` with separable residue extension
over `F`, `e(Q ∩ E ∣ Q ∩ F)` is the index in `G₀(Q)` of the elements fixing `E`. In particular
`Q ∩ E` is unramified over `F` exactly when `G₀(Q)` fixes `E`. -/
theorem ramificationIdx_restrict_eq_index (E : IntermediateField F M) :
    ramificationIdx F (Q.restrict k E) =
      (E.fixingSubgroup.comap ((Q.integers.decompositionSubgroup F).subtype.comp
        (ramificationGroup F Q 0).subtype)).index := by
  have := isSeparable_residueField_restrict_top k F (k₁ := k) (F₁ := E) Q
  have hcard := (E.fixingSubgroup.comap ((Q.integers.decompositionSubgroup F).subtype.comp
    (ramificationGroup F Q 0).subtype)).card_mul_index
  have hG : Nat.card (ramificationGroup F Q 0) = ramificationIdx F Q := by
    rw [ramificationGroup_zero]
    exact card_inertiaSubgroup F Q
  rw [card_comap_fixingSubgroup, card_inertiaSubgroup, hG,
    ramificationIdx_restrict_mul (k₁ := k) (F₀ := F) (F₁ := E) Q] at hcard
  exact (Nat.eq_of_mul_eq_mul_left (ramificationIdx_pos E Q) hcard).symm

/-- **Abhyankar's lemma in a Galois extension** (Stichtenoth, Theorem 3.9.1): let `M / F` be
finite Galois, `Q` a place of `M` with separable residue extension over `F`, and `E₁`, `E₂`
intermediate fields. If `e(Q ∩ E₁ ∣ Q ∩ F)` is nonzero in the residue field of `Q ∩ F` (that is,
`Q ∩ E₁` is tame over `F`), then the ramification index of `Q` in the compositum is
`e(Q ∩ E₁E₂ ∣ Q ∩ F) = lcm(e(Q ∩ E₁ ∣ Q ∩ F), e(Q ∩ E₂ ∣ Q ∩ F))`. -/
theorem ramificationIdx_restrict_sup_eq_lcm_of_isGalois (E₁ E₂ : IntermediateField F M)
    (htame : ((ramificationIdx F (Q.restrict k E₁) : ℕ) : (Q.restrict k F).ResidueField) ≠ 0) :
    ramificationIdx F (Q.restrict k ↥(E₁ ⊔ E₂)) =
      Nat.lcm (ramificationIdx F (Q.restrict k E₁)) (ramificationIdx F (Q.restrict k E₂)) := by
  have : Finite (ramificationGroup F Q 0) := Finite.of_injective
    ((Q.integers.decompositionSubgroup F).subtype.comp (ramificationGroup F Q 0).subtype)
    fun _ _ h ↦ Subtype.ext (Subtype.ext h)
  have : Finite (ramificationGroup F Q 1) := Finite.of_injective
    (fun g : ramificationGroup F Q 1 ↦ (g : Q.integers.decompositionSubgroup F))
    fun _ _ h ↦ Subtype.ext h
  have := isCyclic_quotient_ramificationGroup_one F Q
  rw [ramificationIdx_restrict_eq_index, ramificationIdx_restrict_eq_index,
    ramificationIdx_restrict_eq_index, IntermediateField.fixingSubgroup_sup, Subgroup.comap_inf]
  refine Subgroup.index_inf_eq_lcm
    (V := (ramificationGroup F Q 1).subgroupOf (ramificationGroup F Q 0)) ?_ _
  rw [← ramificationIdx_restrict_eq_index]
  -- The wild inertia group is a `p`-group, and `p` does not divide `e(Q ∩ E₁ ∣ Q ∩ F)`; in
  -- characteristic zero it is trivial.
  have hinj := (algebraMap (Q.restrict k F).ResidueField Q.ResidueField).injective
  rcases CharP.char_is_prime_or_zero (Q.restrict k F).ResidueField
    (ringChar (Q.restrict k F).ResidueField) with hp | hp
  · have := ringChar.charP (Q.restrict k F).ResidueField
    have := charP_of_injective_algebraMap hinj (ringChar (Q.restrict k F).ResidueField)
    have : Fact (ringChar (Q.restrict k F).ResidueField).Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 <|
      (isPGroup_ramificationGroup_succ F Q (ringChar (Q.restrict k F).ResidueField) 0).comap_subtype
        (K := ramificationGroup F Q 0)
    rw [Subgroup.subgroupOf, hn]
    refine Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.2 fun h ↦ htame ?_)
    exact (CharP.cast_eq_zero_iff _ _ _).2 h
  · have := ringChar.of_eq hp
    have := CharP.charP_to_charZero (Q.restrict k F).ResidueField
    have := charZero_of_injective_algebraMap hinj
    rw [ramificationGroup_one_eq_bot, Subgroup.bot_subgroupOf, Subgroup.card_bot]
    exact Nat.coprime_one_left _

end Galois

section Separable

variable {N : Type w'} [Field N] [Algebra k N] [Algebra F N] [Algebra M N] [IsScalarTower k F N]
variable [IsScalarTower F M N] [IsScalarTower k M N]

/-- Restricting a place of `N` to the image in `N` of an intermediate field `E` of `M / F`, or
first to `M` and then to `E`, gives the same ramification index over `F`. -/
private theorem ramificationIdx_restrict_map [FiniteDimensional F M] [FiniteDimensional F N]
    [Algebra.IsIntegral M N] (Q : Place k N) (E : IntermediateField F M) :
    ramificationIdx F (Q.restrict k (E.map (IsScalarTower.toAlgHom F M N))) =
      ramificationIdx F ((Q.restrict k M).restrict k E) := by
  set E' := E.map (IsScalarTower.toAlgHom F M N)
  -- Read `E'` as an extension of `E` of degree one, through the isomorphism `E ≃ E'`.
  let ι := E.equivMap (IsScalarTower.toAlgHom F M N)
  let _ : Algebra E E' := ι.toRingHom.toAlgebra
  have : IsScalarTower F E E' := .of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : IsScalarTower k E E' := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply k F E, IsScalarTower.algebraMap_apply k F E']
    exact (ι.commutes (algebraMap k F x)).symm
  have : IsScalarTower E E' N := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k E N := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply E M N, ← IsScalarTower.algebraMap_apply k E M,
      ← IsScalarTower.algebraMap_apply k M N]
  have : Module.Finite E E' := .of_surjective (Algebra.linearMap E E') ι.surjective
  have hfinrank : Module.finrank E E' = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId E E') ι.bijective).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have he : ramificationIdx E (Q.restrict k E') = 1 :=
    le_antisymm (hfinrank ▸ ramificationIdx_le_finrank E _) (ramificationIdx_pos E _)
  have h := ramificationIdx_restrict_mul (k₁ := k) (F₀ := F) (F₁ := E) (F₂ := E')
    (Q.restrict k E')
  rw [restrict_restrict, he, one_mul] at h
  rw [h, restrict_restrict (k₁ := k) (F₁ := M)]

/-- Abhyankar's lemma for intermediate fields of `M`, read in a finite Galois extension `N` of `F`
containing `M`. -/
private theorem ramificationIdx_restrict_sup_eq_lcm_of_le [FiniteDimensional F M]
    [FiniteDimensional F N] [IsGalois F N] (hF : IsFunctionField k F) (Q : Place k M)
    [PerfectField (Q.restrict k F).ResidueField] (E₁ E₂ : IntermediateField F M)
    (htame : ((ramificationIdx F (Q.restrict k E₁) : ℕ) : (Q.restrict k F).ResidueField) ≠ 0) :
    ramificationIdx F (Q.restrict k ↥(E₁ ⊔ E₂)) =
      Nat.lcm (ramificationIdx F (Q.restrict k E₁)) (ramificationIdx F (Q.restrict k E₂)) := by
  have : FiniteDimensional M N := .of_restrictScalars_finite F M N
  obtain ⟨Q', rfl⟩ := restrict_surjective_of_finiteDimensional (hF.finite_extension (E := M))
    (hF.finite_extension (E := N)) Q
  have hP : (Q'.restrict k M).restrict k F = Q'.restrict k F := restrict_restrict Q'
  have : PerfectField (Q'.restrict k F).ResidueField := hP ▸ ‹_›
  rw [hP, ← ramificationIdx_restrict_map] at htame
  rw [← ramificationIdx_restrict_map, ← ramificationIdx_restrict_map,
    ← ramificationIdx_restrict_map, IntermediateField.map_sup]
  exact ramificationIdx_restrict_sup_eq_lcm_of_isGalois F Q' _ _ htame

/-- **Abhyankar's lemma** (Stichtenoth, Theorem 3.9.1): let `M / F` be a finite separable
extension of a function field `F / k`, `Q` a place of `M` whose restriction to `F` has perfect
residue field, and `E₁`, `E₂` intermediate fields. If `e(Q ∩ E₁ ∣ Q ∩ F)` is nonzero in the
residue field of `Q ∩ F` (that is, `Q ∩ E₁` is tame over `F`), then
`e(Q ∩ E₁E₂ ∣ Q ∩ F) = lcm(e(Q ∩ E₁ ∣ Q ∩ F), e(Q ∩ E₂ ∣ Q ∩ F))`.

Over a perfect constant field every residue field is perfect, as in Stichtenoth. The tameness
hypothesis cannot be dropped: over `k(x)` in characteristic `p`, the Artin–Schreier extensions
`y ^ p - y = x` and `y ^ p - y = x ^ (p + 1)` are both totally ramified of degree `p` at the pole
of `x`, while their compositum has ramification index `p²` there. -/
theorem ramificationIdx_restrict_sup_eq_lcm [FiniteDimensional F M] [Algebra.IsSeparable F M]
    (hF : IsFunctionField k F) (Q : Place k M) [PerfectField (Q.restrict k F).ResidueField]
    (E₁ E₂ : IntermediateField F M)
    (htame : ((ramificationIdx F (Q.restrict k E₁) : ℕ) : (Q.restrict k F).ResidueField) ≠ 0) :
    ramificationIdx F (Q.restrict k ↥(E₁ ⊔ E₂)) =
      Nat.lcm (ramificationIdx F (Q.restrict k E₁)) (ramificationIdx F (Q.restrict k E₂)) := by
  -- Embed `M` in its normal closure `N` inside an algebraic closure of `F`.
  let A := AlgebraicClosure F
  have : Algebra.IsSeparable F (IntermediateField.normalClosure F M A) := by
    have (f : M →ₐ[F] A) : Algebra.IsSeparable F f.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
    apply (le_separableClosure_iff F A _).mp
    rw [normalClosure_def]
    exact iSup_le fun f ↦ le_separableClosure F A f.fieldRange
  have : IsGalois F (IntermediateField.normalClosure F M A) := ⟨⟩
  let g : M →ₐ[F] IntermediateField.normalClosure F M A :=
    (IsAlgClosed.lift (R := F) (S := M) (M := A)).codRestrict
      (IntermediateField.normalClosure F M A).toSubalgebra
      fun x ↦ (IsAlgClosed.lift (R := F) (S := M) (M := A)).fieldRange_le_normalClosure ⟨x, rfl⟩
  let _ : Algebra M (IntermediateField.normalClosure F M A) := g.toRingHom.toAlgebra
  have : IsScalarTower F M (IntermediateField.normalClosure F M A) :=
    .of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : IsScalarTower k M (IntermediateField.normalClosure F M A) :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply k F M, IsScalarTower.algebraMap_apply k F,
        IsScalarTower.algebraMap_apply F M]
  exact ramificationIdx_restrict_sup_eq_lcm_of_le (N := IntermediateField.normalClosure F M A) hF
    Q E₁ E₂ htame

end Separable

end TauCeti.Place
