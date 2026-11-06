/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import TauCeti.CategoryTheory.ObjectProperty.Orthogonal

/-!
# Orthogonality of third vertices of triangles

Let `P` be a class of objects of a pretriangulated category, stable under shifts, and let
`T : X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` be a distinguished triangle. If every morphism from an object of `P`
to `X₂` factors uniquely through `X₁ ⟶ X₂`, then `X₃` is right orthogonal to `P`. This is the
long exact sequence of `Hom(K, -)` for objects `K` of `P`: surjectivity at `K` kills the image of
`Hom(K, X₂)` in `Hom(K, X₃)`, and injectivity at `K⟦-1⟧` kills the connecting map to
`Hom(K, X₁⟦1⟧)`.

Dually, `T.obj₃` is left orthogonal to `P` if and only if, for every object `K` of `P`, every
morphism `X₁ ⟶ K` extends uniquely along `X₁ ⟶ X₂`
(`CategoryTheory.ObjectProperty.leftOrthogonal_obj₃_iff_bijective`), by the long exact sequence
of `Hom(-, K)`.

This is how one shows that an object built as a cone is orthogonal to a class of objects
satisfying a lifting property, as for curved modules with projective underlying graded module
and totalizations of short exact sequences.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]

/-- Let `T` be a distinguished triangle such that, for every object `K` of a shift-stable class
`P`, composition with `T.mor₁` is a bijection from morphisms `K ⟶ T.obj₁` to morphisms
`K ⟶ T.obj₂`. Then `T.obj₃` is right orthogonal to `P`. -/
theorem rightOrthogonal_obj₃_of_bijective (T : Triangle C) (hT : T ∈ distTriang C)
    (H : ∀ K, P K → Function.Bijective fun f : K ⟶ T.obj₁ ↦ f ≫ T.mor₁) :
    P.rightOrthogonal T.obj₃ := by
  intro K φ hK
  -- The connecting morphism `φ ≫ T.mor₃` vanishes: its unshift by `-1` lands in `T.obj₁` and
  -- becomes zero after composing with `T.mor₁`, so it is zero by injectivity at `K⟦-1⟧`.
  have hφ : φ ≫ T.mor₃ = 0 := by
    let e := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
    have h₀ : ((φ ≫ T.mor₃)⟦(-1 : ℤ)⟧' ≫ e.hom.app T.obj₁) ≫ T.mor₁ = 0 ≫ T.mor₁ := by
      have hn := e.hom.naturality T.mor₁
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn
      rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, Category.assoc,
        comp_distTriang_mor_zero₃₁ T hT, comp_zero, Functor.map_zero, zero_comp, zero_comp]
    have h₁ := (H _ (P.le_shift (-1 : ℤ) K hK)).1 h₀
    rw [Preadditive.IsIso.comp_right_eq_zero] at h₁
    exact ((shiftFunctor C (-1 : ℤ)).map_eq_zero_iff).1 h₁
  obtain ⟨ψ, rfl⟩ := Triangle.coyoneda_exact₃ T hT φ hφ
  obtain ⟨χ, rfl⟩ := (H K hK).2 ψ
  rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

/-- Let `T` be a distinguished triangle and `P` a shift-stable class of objects. Then `T.obj₃` is
left orthogonal to `P` if and only if, for every object `K` of `P`, composition with `T.mor₁` is a
bijection from morphisms `T.obj₂ ⟶ K` to morphisms `T.obj₁ ⟶ K`. -/
theorem leftOrthogonal_obj₃_iff_bijective (T : Triangle C) (hT : T ∈ distTriang C) :
    P.leftOrthogonal T.obj₃ ↔
      ∀ K, P K → Function.Bijective fun f : T.obj₂ ⟶ K ↦ T.mor₁ ≫ f := by
  refine ⟨fun h K hK ↦ ⟨fun f₁ f₂ hf ↦ ?_, fun χ ↦ ?_⟩, fun H K φ hK ↦ ?_⟩
  · -- A map killed by `T.mor₁` factors through `T.obj₃`, so it vanishes.
    rw [← sub_eq_zero]
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT (f₁ - f₂) (by
      rw [Preadditive.comp_sub, sub_eq_zero]
      exact hf)
    rw [hg, h g hK, comp_zero]
  · -- A map `T.obj₁ ⟶ K` extends along `T.mor₁` once it vanishes on `T.obj₃⟦-1⟧`, which holds
    -- since `K⟦1⟧` lies in `P`.
    have h₀ : ∀ ψ : T.obj₃⟦(-1 : ℤ)⟧ ⟶ K, ψ = 0 :=
      (forall_shift_hom_eq_zero_iff T.obj₃ K (neg_add_cancel 1)).2 fun ψ ↦
        h ψ (P.le_shift 1 K hK)
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang T hT) χ (h₀ _)
    exact ⟨g, hg.symm⟩
  · -- A map out of `T.obj₃` vanishing on `T.obj₂` factors through the connecting map, and the
    -- surjectivity at `K⟦-1⟧` makes that factorization factor through `T.mor₁⟦1⟧'`.
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT φ ((H K hK).1 (by
      simp only [comp_distTriang_mor_zero₁₂_assoc T hT, comp_zero, zero_comp]))
    let adj := (shiftEquiv C (1 : ℤ)).toAdjunction
    obtain ⟨h, hh⟩ := (H _ (P.le_shift (-1) K hK)).2 (adj.homEquiv _ _ g)
    dsimp only at hh
    rw [← (adj.homEquiv _ _).symm_apply_apply g, ← hh]
    exact (congrArg (T.mor₃ ≫ ·) (adj.homEquiv_naturality_left_symm T.mor₁ h)).trans
      ((comp_distTriang_mor_zero₃₁_assoc T hT _).trans (zero_comp))

end CategoryTheory.ObjectProperty
