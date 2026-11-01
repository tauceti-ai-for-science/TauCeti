/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Basic
public import TauCeti.Algebra.Lie.Loop.HahnModule
public import TauCeti.RingTheory.HahnSeries.TensorProduct

/-!
# Formal currents as Lie algebra valued Laurent series

Formal currents `currentAlgebra R L = R⸨X⸩ ⊗[R] L` are the scalar extension of a Lie algebra `L`
over a commutative ring `R` to Laurent series, with the coefficientwise `R`-algebra structure on
`R⸨X⸩`. The canonical comparison `HahnModule.tensorProductToHahnModule ℤ R L`, sending `f ⊗ x`
to `f • x`, takes them to the formal loop algebra `L((t)) = HahnModule ℤ R L` with its
coefficient convolution bracket and its coefficientwise action of `R⸨X⸩`.

This comparison preserves the coefficients of currents, and on polynomial currents it is the
polynomial loop embedding `LieAlgebra.LoopAlgebra.toHahnModule`. It respects brackets, and for a
finite free `L`, for instance a finite-dimensional Lie algebra over a field `K`, it is the
isomorphism of Lie algebras `HahnModule.tensorProductLieEquiv ℤ R L` over `R⸨X⸩` from
`TauCeti.Algebra.Lie.BaseChange.HahnModule`. With the coefficientwise algebra structure on
`R⸨X⸩` its domain is `currentAlgebra R L`, so this is `K((t)) ⊗[K] L ≃ L((t))` over `K((t))`.

## Main results

* `TauCeti.CurrentAlgebra.coeff_tensorProductToHahnModule`: the comparison preserves the
  coefficients of currents.
* `TauCeti.CurrentAlgebra.tensorProductToHahnModule_ofLoop`: on polynomial currents, the
  comparison is the polynomial loop embedding.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.2.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries

open HahnModule

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

-- Match the coefficientwise scalar action used to define formal currents.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- The comparison of formal currents with `L`-valued Laurent series preserves coefficients. -/
@[simp]
theorem coeff_tensorProductToHahnModule (u : currentAlgebra R L) (n : ℤ) :
    ((of R).symm (tensorProductToHahnModule ℤ R L u)).coeff n = coeff R L n u := by
  induction u using TensorProduct.inductionOn with
  | tmul f x => rw [tensorProductToHahnModule_tmul, coeff_smul_single_zero, coeff_tmul]
  | add u v hu hv => rw [map_add, of_symm_add, HahnSeries.coeff_add, hu, hv, map_add]

/-- On polynomial currents, the comparison of formal currents with `L`-valued Laurent series is
the polynomial loop embedding. -/
theorem tensorProductToHahnModule_ofLoop (p : LieAlgebra.loopAlgebra R ℤ L) :
    tensorProductToHahnModule ℤ R L (ofLoop R L p) =
      LieAlgebra.LoopAlgebra.toHahnModule R ℤ L p := by
  ext n
  rw [coeff_tensorProductToHahnModule, coeff_ofLoop, LieAlgebra.LoopAlgebra.coeff_toHahnModule]

end TauCeti.CurrentAlgebra
