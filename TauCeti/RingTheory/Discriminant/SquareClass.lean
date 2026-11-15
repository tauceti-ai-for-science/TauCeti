/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Discriminant
public import TauCeti.FieldTheory.GaloisGroups.Discriminant.Field
public import TauCeti.FieldTheory.SquareClassGroup.Basic
import TauCeti.FieldTheory.IntermediateField.Quadratic
import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.FieldTheory.Trace
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The discriminant square class and the discriminant root field

Let `L/K` be a finite separable field extension. The discriminant `Algebra.discr K b` of a
`K`-basis `b` of `L` is nonzero, and a change of basis with matrix `P` multiplies it by
`(det P)²`. Its class in the square-class group `Kˣ ⧸ (Kˣ)²` is therefore an invariant of `L/K`,
the **discriminant square class** `TauCeti.discriminantClass K L`. The quadratic extension of `K`
cut out by a square root of the discriminant is the **discriminant root field**
`TauCeti.discriminantRootField K L`, an intermediate field of `AlgebraicClosure K / K`. It is `K`
when the discriminant square class is trivial and a quadratic extension of `K` otherwise.

For a power basis the algebra discriminant is the polynomial discriminant of the minimal polynomial
of the generator (`Algebra.discr_powerBasis_eq_minpoly_discr`), so the discriminant root field of
`L/K` is the discriminant field `TauCeti.discrField` of the minimal polynomial of any primitive
element, and the results on discriminant fields apply to it. Both invariants are displayed for
extensions of `p`-adic fields, where the LMFDB records the discriminant root field as `rf`.

## Main definitions

* `TauCeti.discriminantClass`: the square class of the discriminant of a basis of `L/K`.
* `TauCeti.discriminantRootField`: the subfield of `AlgebraicClosure K` generated over `K` by the
  square roots of the discriminant.

## Main results

* `Algebra.discr_eq_det_toMatrix_sq_mul`: a change of basis multiplies the discriminant by the
  square of its determinant.
* `TauCeti.discriminantClass_eq_squareClass`: the discriminant of every basis represents the
  discriminant square class.
* `TauCeti.discriminantClass_eq_zero_iff`: the class is trivial exactly when the discriminant of
  some, equivalently every, basis is a square.
* `TauCeti.discriminantClass_eq_squareClass_minpoly_discr`: the polynomial discriminant of the
  minimal polynomial of a power-basis generator represents the class.
* `TauCeti.discriminantClass_eq_of_algEquiv` and
  `TauCeti.discriminantRootField_eq_of_algEquiv`: invariance under `K`-algebra equivalence.
* `TauCeti.discriminantClass_eq_squareClass_of_sq_eq`: a separable quadratic extension `K(√a)`
  has discriminant square class that of `a`.
* `TauCeti.discriminantRootField_eq_adjoin_simple`: a square root of any representative of the
  class generates the discriminant root field.
* `TauCeti.discriminantRootField_eq_discrField`: the discriminant root field is the discriminant
  field of the minimal polynomial of a power-basis generator.
* `TauCeti.discriminantRootField_eq_bot_iff` and
  `TauCeti.finrank_discriminantRootField_eq_two_iff`: the root field is `K` exactly when the class
  is trivial, and quadratic otherwise.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §2.
* The LMFDB, *p-adic fields*: the discriminant root field `rf`.
-/

public section
noncomputable section

open Module Polynomial
open scoped IntermediateField

namespace Algebra

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι] [DecidableEq ι]

/-- **Change of basis for the discriminant.** For two bases `b` and `b'` of `B` over `A` with the
same index type, the discriminant of `b'` is that of `b` multiplied by the square of the
determinant of the change-of-basis matrix `b.toMatrix b'`. -/
theorem discr_eq_det_toMatrix_sq_mul (b b' : Basis ι A B) :
    discr A b' = (b.toMatrix b').det ^ 2 * discr A b := by
  conv_lhs => rw [← b.toMatrix_map_vecMul b']
  exact discr_of_matrix_vecMul _ _

end Algebra

namespace TauCeti

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- **The discriminant square class** of a finite separable extension `L/K`: the class in
`Kˣ ⧸ (Kˣ)²` of the discriminant of a `K`-basis of `L`, here the basis `Module.finBasis K L`.
By `TauCeti.discriminantClass_eq_squareClass` every basis of `L` gives the same class. -/
def discriminantClass : SquareClassGroup K :=
  squareClass (Units.mk0 _ (Algebra.discr_not_zero_of_basis K (Module.finBasis K L)))

/-- The discriminant square class is represented by the discriminant of `Module.finBasis K L`. -/
theorem discriminantClass_def :
    discriminantClass K L =
      squareClass (Units.mk0 _ (Algebra.discr_not_zero_of_basis K (Module.finBasis K L))) :=
  (rfl)

variable {K L}

/-- **Independence of the basis.** The discriminant of any `K`-basis `b` of `L` represents the
discriminant square class of `L/K`. -/
theorem discriminantClass_eq_squareClass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) :
    discriminantClass K L = squareClass (Units.mk0 _ (Algebra.discr_not_zero_of_basis K b)) := by
  set b₀ := (Module.finBasis K L).reindex ((Module.finBasis K L).indexEquiv b)
  have hb₀ : Algebra.discr K b₀ = Algebra.discr K (Module.finBasis K L) := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex]
  rw [discriminantClass_def, squareClass_eq_iff_isSquare_mul, ← Units.isSquare_coe_iff]
  refine ⟨(b₀.toMatrix b).det * Algebra.discr K b₀, ?_⟩
  simp only [Units.val_mul, Units.val_mk0]
  rw [Algebra.discr_eq_det_toMatrix_sq_mul b₀ b, ← hb₀]
  ring

/-- The discriminant square class is trivial exactly when the discriminant of a basis is a square
in `K`. -/
theorem discriminantClass_eq_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) : discriminantClass K L = 0 ↔ IsSquare (Algebra.discr K b) := by
  rw [discriminantClass_eq_squareClass b, squareClass_eq_zero_iff, ← Units.isSquare_coe_iff,
    Units.val_mk0]

/-- **The polynomial-discriminant form.** For a power basis of `L/K`, the discriminant square class
is represented by the polynomial discriminant of the minimal polynomial of its generator, which is
nonzero because the generator is separable. -/
theorem discriminantClass_eq_squareClass_minpoly_discr (pb : PowerBasis K L) :
    discriminantClass K L = squareClass (Units.mk0 _
      ((minpoly.monic pb.isIntegral_gen).discr_ne_zero_iff.mpr
        (Algebra.IsSeparable.isSeparable K pb.gen))) := by
  rw [discriminantClass_eq_squareClass pb.basis]
  congr 1
  ext
  exact Algebra.discr_powerBasis_eq_minpoly_discr pb

variable (K) in
/-- The trivial extension `K/K` has trivial discriminant square class: the basis `{1}` has
discriminant `1`. -/
@[simp]
theorem discriminantClass_self : discriminantClass K K = 0 := by
  rw [discriminantClass_eq_zero_iff (Basis.singleton (Fin 1) K), Algebra.discr_def,
    Matrix.det_unique]
  refine ⟨1, ?_⟩
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply]

/-- **Invariance under `K`-algebra equivalence.** Isomorphic extensions have the same discriminant
square class. -/
theorem discriminantClass_eq_of_algEquiv {L' : Type*} [Field L'] [Algebra K L']
    [FiniteDimensional K L'] [Algebra.IsSeparable K L'] (e : L ≃ₐ[K] L') :
    discriminantClass K L = discriminantClass K L' := by
  let b := Module.finBasis K L
  rw [discriminantClass_eq_squareClass b, discriminantClass_eq_squareClass (b.map e.toLinearEquiv)]
  congr 1
  ext
  rw [Units.val_mk0, Units.val_mk0, Basis.coe_map]
  exact Algebra.discr_eq_discr_of_algEquiv b e

/-- **The quadratic case.** If `L = K(x)` is a separable quadratic extension with `x² = a ∈ K`,
the discriminant square class of `L/K` is the square class of `a`: the basis `{1, x}` has
discriminant `4a`. (In characteristic two such an extension is inseparable, so there the
statement is vacuous.) -/
theorem discriminantClass_eq_squareClass_of_sq_eq (hL : finrank K L = 2)
    {x : L} {a : Kˣ} (hx : x ^ 2 = algebraMap K L a) (hxK : x ∉ Set.range (algebraMap K L)) :
    discriminantClass K L = squareClass a := by
  let b := quadraticExtensionBasis K L hxK hL
  have hb : ⇑b = ![1, x] := by
    ext i
    fin_cases i <;> simp [b]
  rw [discriminantClass_eq_squareClass b, squareClass_eq_iff_isSquare_mul,
    ← Units.isSquare_coe_iff]
  refine ⟨2 * a, ?_⟩
  have hxK' : x ∉ (algebraMap K L).range := by rwa [← SetLike.mem_coe, RingHom.coe_range]
  rw [Units.val_mul, Units.val_mk0, hb, Algebra.discr_one_elem_eq_of_sq_algebraMap hL hx hxK']
  ring

variable (K L)

/-- **The discriminant root field** of a finite separable extension `L/K`: the subfield of
`AlgebraicClosure K` generated over `K` by the square roots of the discriminant of a basis of
`L/K`, here `Module.finBasis K L`. By `TauCeti.discriminantRootField_eq_adjoin_simple` it is
`K(√d)` for any representative `d` of the discriminant square class and any choice of the square
root. -/
def discriminantRootField : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K
    ((X ^ 2 - C (Algebra.discr K (Module.finBasis K L))).rootSet (AlgebraicClosure K))

omit [Algebra.IsSeparable K L] in
/-- The discriminant root field is generated by the roots of `X ^ 2 - d`, for `d` the discriminant
of `Module.finBasis K L`. -/
theorem discriminantRootField_def :
    discriminantRootField K L = IntermediateField.adjoin K
      ((X ^ 2 - C (Algebra.discr K (Module.finBasis K L))).rootSet (AlgebraicClosure K)) :=
  (rfl)

variable {K L}

/-- **Independence of the representative and of the square root.** If `u` represents the
discriminant square class of `L/K` and `δ ∈ AlgebraicClosure K` is any square root of `u`, then the
discriminant root field is `K(δ)`. -/
theorem discriminantRootField_eq_adjoin_simple {u : Kˣ}
    (hu : squareClass u = discriminantClass K L) {δ : AlgebraicClosure K}
    (hδ : δ ^ 2 = algebraMap K (AlgebraicClosure K) u) :
    discriminantRootField K L = K⟮δ⟯ := by
  set d := Algebra.discr K (Module.finBasis K L)
  have hd : d ≠ 0 := Algebra.discr_not_zero_of_basis K _
  obtain ⟨δ₀, hδ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) d) two_pos
  rw [discriminantRootField_def, IntermediateField.adjoin_rootSet_X_pow_two_sub_C hδ₀]
  refine TauCeti.IntermediateField.adjoin_simple_eq_of_isSquare_mul hδ₀ hδ hd u.ne_zero ?_
  rw [discriminantClass_def, squareClass_eq_iff_isSquare_mul, ← Units.isSquare_coe_iff] at hu
  simpa [mul_comm] using hu

/-- **The discriminant root field as a discriminant field.** For a power basis of `L/K`, the
discriminant root field is the discriminant field `TauCeti.discrField` of the minimal polynomial of
the generator. -/
theorem discriminantRootField_eq_discrField (pb : PowerBasis K L) :
    discriminantRootField K L = discrField (minpoly K pb.gen) (AlgebraicClosure K) := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (minpoly K pb.gen).discr) two_pos
  rw [discrField_eq_adjoin_simple hδ, discriminantRootField_eq_adjoin_simple
    (discriminantClass_eq_squareClass_minpoly_discr pb).symm (by simpa using hδ)]

/-- **The trivial case.** The discriminant root field is `K` exactly when the discriminant square
class is trivial. -/
theorem discriminantRootField_eq_bot_iff :
    discriminantRootField K L = ⊥ ↔ discriminantClass K L = 0 := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (minpoly K pb.gen).discr) two_pos
  rw [discriminantRootField_eq_discrField pb, discrField_eq_bot_iff hδ,
    discriminantClass_eq_squareClass_minpoly_discr pb, squareClass_eq_zero_iff,
    ← Units.isSquare_coe_iff, Units.val_mk0]

/-- **The quadratic case.** The discriminant root field is a quadratic extension of `K` exactly
when the discriminant square class is nontrivial. -/
theorem finrank_discriminantRootField_eq_two_iff :
    finrank K (discriminantRootField K L) = 2 ↔ discriminantClass K L ≠ 0 := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (minpoly K pb.gen).discr) two_pos
  rw [discriminantRootField_eq_discrField pb, discriminantClass_eq_squareClass_minpoly_discr pb,
    Ne, squareClass_eq_zero_iff, ← Units.isSquare_coe_iff, Units.val_mk0]
  refine ⟨fun h hsq ↦ ?_, finrank_discrField_eq_two hδ⟩
  rw [← finrank_discrField_eq_one_iff hδ] at hsq
  omega

/-- The discriminant root field is either `K` or a quadratic extension of `K`. -/
theorem discriminantRootField_eq_bot_or_finrank_eq_two :
    discriminantRootField K L = ⊥ ∨ finrank K (discriminantRootField K L) = 2 := by
  rw [discriminantRootField_eq_bot_iff, finrank_discriminantRootField_eq_two_iff]
  exact em _

/-- **Invariance under `K`-algebra equivalence.** Isomorphic extensions have the same
discriminant root field. -/
theorem discriminantRootField_eq_of_algEquiv {L' : Type*} [Field L'] [Algebra K L']
    [FiniteDimensional K L'] [Algebra.IsSeparable K L'] (e : L ≃ₐ[K] L') :
    discriminantRootField K L = discriminantRootField K L' := by
  set d := Units.mk0 _ (Algebra.discr_not_zero_of_basis K (Module.finBasis K L))
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) d) two_pos
  rw [discriminantRootField_eq_adjoin_simple (discriminantClass_def K L).symm hδ,
    discriminantRootField_eq_adjoin_simple
      ((discriminantClass_def K L).symm.trans (discriminantClass_eq_of_algEquiv e)) hδ]

end TauCeti
