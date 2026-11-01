/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.HahnModule
public import TauCeti.RingTheory.HahnSeries.TensorProduct

/-!
# Lie algebra valued Hahn series as a scalar extension

Let `L` be a Lie algebra over a commutative ring `R`. The constant series give a homomorphism of
Lie algebras `HahnModule.constLieHom : L →ₗ⁅R⁆ HahnModule Γ R L`, and its extension of scalars
`HahnSeries Γ R ⊗[R] L →ₗ⁅HahnSeries Γ R⁆ HahnModule Γ R L`, sending `f ⊗ x` to `f • x`, has
`HahnModule.tensorProductToHahnModule` as its underlying linear map. So that canonical
comparison respects brackets: the bracket `⁅f ⊗ x, g ⊗ y⁆ = f g ⊗ ⁅x, y⁆` of the extended Lie
algebra goes to the coefficient convolution bracket of `L`-valued series.

When `L` is finite free over `R`, the comparison is bijective, so it is an isomorphism of Lie
algebras over `HahnSeries Γ R`. For `Γ = ℤ` and a finite-dimensional Lie algebra `L` over a
field `K`, this is the isomorphism `K((t)) ⊗[K] L ≃ L((t))` of Lie algebras over `K((t))`, where
`L((t))` carries the coefficientwise action of `K((t))` and the convolution bracket. The
file `TauCeti.Algebra.Lie.Current.HahnModule` compares it with the formal currents
`TauCeti.currentAlgebra`.

## Main definitions

* `HahnModule.constLieHom`: the constant series `L →ₗ⁅R⁆ HahnModule Γ R L`.
* `HahnModule.tensorProductLieEquiv`: for finite free `L`, the isomorphism of Lie algebras
  `HahnSeries Γ R ⊗[R] L ≃ₗ⁅HahnSeries Γ R⁆ HahnModule Γ R L`.

## Main results

* `HahnModule.liftBaseChange_constLieHom`: the extension of scalars of `constLieHom` is
  `tensorProductToHahnModule`.
* `HahnModule.tensorProductToHahnModule_lie`: so the comparison respects brackets, for every
  Lie algebra `L`.
* `HahnModule.isBaseChange_constLieHom`: for finite free `L`, the constant series exhibit
  `HahnModule Γ R L` as the base change of `L` along `R → HahnSeries Γ R`.
* `HahnModule.toLinearEquiv_tensorProductLieEquiv`: the Lie algebra isomorphism has underlying
  linear equivalence `HahnModule.tensorProductEquiv`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.
-/

public section

noncomputable section

open TensorProduct HahnSeries

namespace HahnModule

variable (Γ R L : Type*) [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The constant `L`-valued Hahn series, as a homomorphism of Lie algebras over `R`. -/
def constLieHom : L →ₗ⁅R⁆ HahnModule Γ R L where
  toFun x := of R (single 0 x)
  map_add' x y := by rw [single_add, of_add]
  map_smul' r x := (congrArg (of R) ((single.linearMap 0).map_smul r x)).trans (of_smul r _)
  map_lie' {x y} := by rw [single_lie_single, add_zero]

variable {Γ R L}

/-- The constant series of `x` is the monomial `x t ^ 0`. -/
@[simp]
theorem constLieHom_apply (x : L) : constLieHom Γ R L x = of R (single 0 x) :=
  (rfl)

/-- The extension of scalars of the constant series along `R → HahnSeries Γ R` is the canonical
comparison `f ⊗ x ↦ f • x`, without any finiteness assumption on `L`. -/
@[simp]
theorem liftBaseChange_constLieHom :
    (constLieHom Γ R L : L →ₗ[R] HahnModule Γ R L).liftBaseChange (HahnSeries Γ R) =
      tensorProductToHahnModule Γ R L := by
  ext x
  simp

/-- The canonical comparison `f ⊗ x ↦ f • x` respects brackets, for every Lie algebra `L`. -/
@[simp]
theorem tensorProductToHahnModule_lie (u v : HahnSeries Γ R ⊗[R] L) :
    tensorProductToHahnModule Γ R L ⁅u, v⁆ =
      ⁅tensorProductToHahnModule Γ R L u, tensorProductToHahnModule Γ R L v⁆ := by
  rw [← liftBaseChange_constLieHom, ← LieHom.coe_liftBaseChange]
  exact LieHom.map_lie _ u v

variable [Module.Free R L] [Module.Finite R L]

/-- For a finite free Lie algebra `L`, the constant series exhibit `L`-valued Hahn series as the
base change of `L` along `R → HahnSeries Γ R`. -/
theorem isBaseChange_constLieHom :
    IsBaseChange (HahnSeries Γ R) (constLieHom Γ R L : L →ₗ[R] HahnModule Γ R L) :=
  .of_equiv (tensorProductEquiv Γ R L) fun x ↦ by simp

variable (Γ R L) in
/-- **Formal loops are the scalar extension of a finite free Lie algebra.** The comparison
`f ⊗ x ↦ f • x` is an isomorphism of Lie algebras over `HahnSeries Γ R`, from the extension of
scalars of `L` to the `L`-valued Hahn series with the convolution bracket. For a
finite-dimensional Lie algebra `L` over a field `K`, this is `K((t)) ⊗[K] L ≃ L((t))` over
`K((t))`. -/
def tensorProductLieEquiv : HahnSeries Γ R ⊗[R] L ≃ₗ⁅HahnSeries Γ R⁆ HahnModule Γ R L :=
  (isBaseChange_constLieHom (Γ := Γ) (R := R) (L := L)).lieEquiv

/-- The Lie algebra isomorphism is the canonical comparison `f ⊗ x ↦ f • x`. -/
@[simp]
theorem tensorProductLieEquiv_apply (z : HahnSeries Γ R ⊗[R] L) :
    tensorProductLieEquiv Γ R L z = tensorProductToHahnModule Γ R L z := by
  induction z with
  | tmul f x => simp [tensorProductLieEquiv]
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- The Lie algebra isomorphism has underlying linear equivalence `tensorProductEquiv`. -/
@[simp]
theorem toLinearEquiv_tensorProductLieEquiv :
    (tensorProductLieEquiv Γ R L).toLinearEquiv = tensorProductEquiv Γ R L :=
  LinearEquiv.ext fun z ↦ by simp

/-- The inverse of the Lie algebra isomorphism is the inverse of `tensorProductEquiv`. -/
@[simp]
theorem tensorProductLieEquiv_symm_apply (x : HahnModule Γ R L) :
    (tensorProductLieEquiv Γ R L).symm x = (tensorProductEquiv Γ R L).symm x := by
  rw [LieEquiv.symm_apply_eq, tensorProductLieEquiv_apply, ← tensorProductEquiv_apply,
    LinearEquiv.apply_symm_apply]

end HahnModule
