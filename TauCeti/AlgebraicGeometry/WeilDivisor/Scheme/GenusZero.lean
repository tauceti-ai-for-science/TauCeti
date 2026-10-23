/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.DegreeZero

/-!
# The Picard group of a curve of genus zero

Let `X` be a proper integral curve over a field `k` whose codimension-one local rings are discrete
valuation rings, with `k` integrally closed in the function field `k(X)`, and suppose that `X` has
genus zero, `dim_k H¹(X, 𝒪_X) = 0`.

By Riemann's inequality every divisor of degree zero on `X` is principal, so **`Pic⁰ X` is
trivial**: a line bundle on `X` is determined up to isomorphism by its degree. If `X` moreover has
a codimension-one point `x₀` of residue degree one, for instance the image of a `k`-rational
point, the degree is onto `ℤ`, and **`Pic X ≅ ℤ`** by the degree, the class of `𝒪_X(x₀)` going to
`1`. This is the genus-zero counterpart of the description of `Pic⁰` of a curve of genus one by
its points (`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.degreeOneEquivPicZero`); in the language
of Jacobians, a curve of genus zero has trivial Jacobian.

The principality statement is transported from the function field, where it is
`TauCeti.Divisor.exists_principal_eq_of_genus_eq_zero`, along the identification of the
codimension-one points of `X` with the places of `k(X)`; the genus of `X` is the genus of `k(X)`
by `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.genus_eq_genus_functionField`.

## Main declarations

* `SchemeWeilDivisor.linearlyEquivalent_zero_of_genus_eq_zero`: in genus zero, a divisor of
  degree zero is principal;
* `SchemeWeilDivisor.picZero_eq_bot_of_genus_eq_zero`: in genus zero, `Pic⁰ X` is trivial;
* `SchemeWeilDivisor.eulerDegree_injective_of_genus_eq_zero`: in genus zero, line bundles with
  the same degree are isomorphic;
* `SchemeWeilDivisor.picAddEquivIntOfGenusEqZero`: in genus zero, at a point `x₀` of residue
  degree one, the degree `Pic X ≅ ℤ`, with inverse `n ↦ [𝒪_X(n x₀)]`
  (`SchemeWeilDivisor.picAddEquivIntOfGenusEqZero_symm_apply`).

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Example II.6.10.1 and
  Exercise IV.1.6.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.4.17 and Corollary 1.4.12(c).
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [hX : Fact (∀ y : X, coheight y ≤ 1)] [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **In genus zero, a divisor of degree zero is principal.** Here `X` is a proper integral curve
over `k` whose codimension-one local rings are discrete valuation rings, with `k` integrally closed
in `k(X)`. -/
theorem linearlyEquivalent_zero_of_genus_eq_zero (hk : IsIntegrallyClosedIn k X.functionField)
    (hg : X.genus k = 0) {D : SchemeWeilDivisor X} (hD : relativeDegree (X ↘ Spec (.of k)) D = 0) :
    (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D 0 := by
  rcases eq_or_ne D 0 with rfl | hD₀
  · exact WeilDivisor.OrderSystem.LinearlyEquivalent.refl _ _
  -- A nonzero divisor has a point in its support, so `X` has dimension one.
  obtain ⟨y, -⟩ : (Finsupp.support D).Nonempty := Finsupp.support_nonempty_iff.mpr hD₀
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)) :=
    (UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))).1
  have hF := isFunctionField_functionField_of_forall_coheight_le_one_of_coheight_eq_one
    k hX.out y.2
  obtain ⟨z, hz⟩ := Divisor.exists_principal_eq_of_genus_eq_zero hF
    ((genus_eq_genus_functionField hex hX.out hF hk).symm.trans hg)
    (D := equivFunctionFieldDivisor hex hX.out D) (by rw [degree_equivFunctionFieldDivisor, hD])
  rw [← linearlyEquivalent_equivFunctionFieldDivisor_iff hex hX.out hF, map_zero,
    Divisor.linearlyEquivalent_iff hF, sub_zero]
  exact ⟨z, hz⟩

variable (hk : IsIntegrallyClosedIn k X.functionField) (hg : X.genus k = 0)
include hk hg

/-- **`Pic⁰` of a curve of genus zero is trivial.** On a proper integral curve of genus zero over
`k` whose codimension-one local rings are discrete valuation rings, with `k` integrally closed in
`k(X)`, every line bundle of degree zero is trivial. -/
theorem picZero_eq_bot_of_genus_eq_zero : LineBundleClass.picZero k X = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun a ha ↦ ?_
  obtain ⟨c, rfl⟩ := (classGroupAddEquivLineBundleClass X).surjective a
  obtain ⟨D, rfl⟩ := (WeilDivisor.OrderSystem.ofScheme X).divisorClass_surjective c
  have hD : relativeDegree (X ↘ Spec (.of k)) D = 0 := by
    rwa [LineBundleClass.mem_picZero_iff, classGroupAddEquivLineBundleClass_apply, toMul_ofMul,
      eulerDegree_classGroupToLineBundleClass,
      WeilDivisor.OrderSystem.weightedDegreeClass_divisorClass, WeilDivisor.weightedDegree_apply,
      ← relativeDegree_apply] at ha
  rw [(WeilDivisor.OrderSystem.divisorClass_eq_iff _).mpr
      (linearlyEquivalent_zero_of_genus_eq_zero k hk hg hD), map_zero, map_zero]

/-- **On a curve of genus zero, a line bundle is determined by its degree.** Two line bundles on a
proper integral curve of genus zero over `k` whose codimension-one local rings are discrete
valuation rings, with `k` integrally closed in `k(X)`, are isomorphic exactly when their
Euler-characteristic degrees agree. -/
theorem eulerDegree_injective_of_genus_eq_zero :
    Function.Injective (LineBundleClass.eulerDegree k (X := X)) := fun a b hab ↦ by
  have h := (AddMonoidHom.ker_eq_bot_iff (LineBundleClass.eulerDegreeHom k X)).mp
    ((LineBundleClass.picZero_eq_ker k X).symm.trans (picZero_eq_bot_of_genus_eq_zero k hk hg))
    (a₁ := Additive.ofMul a) (a₂ := Additive.ofMul b) (by simpa using hab)
  exact Additive.ofMul.injective h

variable {x₀ : CodimensionOnePoint X} (hx₀ : (X ↘ Spec (.of k)).residueDegree x₀ = 1)

include hx₀ in
/-- In genus zero, at a point of residue degree one, the degree `Pic X →+ ℤ` is bijective. -/
private lemma bijective_eulerDegreeHom :
    Function.Bijective (LineBundleClass.eulerDegreeHom k X) :=
  ⟨fun a b hab ↦ Additive.toMul.injective (eulerDegree_injective_of_genus_eq_zero k hk hg
    (by simpa only [LineBundleClass.eulerDegreeHom_apply] using hab)),
    eulerDegreeHom_surjective k hx₀⟩

/-- **`Pic X ≅ ℤ` on a curve of genus zero with a point of residue degree one.** On a proper
integral curve of genus zero over `k` whose codimension-one local rings are discrete valuation
rings, with `k` integrally closed in `k(X)` and a codimension-one point `x₀` of residue degree one,
the Euler-characteristic degree is an isomorphism from the Picard group onto `ℤ`. -/
def picAddEquivIntOfGenusEqZero : Additive (LineBundleClass X) ≃+ ℤ :=
  AddEquiv.ofBijective (LineBundleClass.eulerDegreeHom k X) (bijective_eulerDegreeHom k hk hg hx₀)

/-- The isomorphism `Pic X ≅ ℤ` of a curve of genus zero sends the class of a line bundle to its
degree. -/
@[simp]
lemma picAddEquivIntOfGenusEqZero_apply (a : Additive (LineBundleClass X)) :
    picAddEquivIntOfGenusEqZero k hk hg hx₀ a = LineBundleClass.eulerDegree k a.toMul := by
  rw [picAddEquivIntOfGenusEqZero, AddEquiv.ofBijective_apply,
    LineBundleClass.eulerDegreeHom_apply]

/-- The inverse of the isomorphism `Pic X ≅ ℤ` of a curve of genus zero sends `n` to the class of
`𝒪_X(n x₀)`. -/
lemma picAddEquivIntOfGenusEqZero_symm_apply (n : ℤ) :
    (picAddEquivIntOfGenusEqZero k hk hg hx₀).symm n =
      Additive.ofMul (toLineBundleClass hX.out (n • WeilDivisor.ofPoint x₀)) := by
  rw [AddEquiv.symm_apply_eq, picAddEquivIntOfGenusEqZero_apply, toMul_ofMul,
    ← classGroupToLineBundleClass_divisorClass, eulerDegree_classGroupToLineBundleClass,
    WeilDivisor.OrderSystem.weightedDegreeClass_divisorClass, WeilDivisor.weightedDegree_apply,
    ← relativeDegree_apply, map_zsmul, relativeDegree_ofPoint, hx₀, Nat.cast_one, smul_eq_mul,
    mul_one]

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
