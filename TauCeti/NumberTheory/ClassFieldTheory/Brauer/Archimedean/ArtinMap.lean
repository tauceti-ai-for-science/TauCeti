/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ClassFormation
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
import TauCeti.RingTheory.Norm.Archimedean

/-!
# The archimedean Artin maps

Let `w` be an infinite place of a field `K`, with completion `K_w`. The archimedean class
formation `TauCeti.ClassFieldTheory.infiniteClassFormation w` lives on the formation of the units
of a separable closure of `K_w` over its absolute Galois group, and its ground level is `K_wˣ`. Its
absolute Artin map, read through these identifications, is the **archimedean Artin map**

```text
infiniteArtinAt w : K_wˣ →* G_{K_w}^ab,
```

with values in the topological abelianization of Mathlib's absolute Galois group
`Gal(AlgebraicClosure K_w/K_w)`, the target of the nonarchimedean absolute Artin map
`TauCeti.ClassFieldTheory.artinMap`. It is built from the formation machinery and the archimedean
Brauer invariant alone, with no reciprocity law.

On every finite layer `V ◁ G_{K_w}` it is the abstract Artin map of the archimedean class formation
(`infiniteArtinAt_layer`), so the character formula of a class formation becomes the archimedean
character formula `χ(Art_w x) = inv_w(x ∪ δχ)` (`character_infiniteArtinAt`), whose right-hand
side is the archimedean Brauer invariant `infiniteInvMap` of the inflated cup product. Its kernel is
the intersection of the norm subgroups of all finite layers (`ker_infiniteArtinAt_eq_iInf`). This
computes the map completely:

* at a complex place `G_{K_w}` is trivial, so `Art_w` is trivial
  (`infiniteArtinAt_eq_one_of_isComplex`);
* at a real place the only nontrivial layer is `ℂ/ℝ`, whose norms are the positive reals, so
  `Art_w(x)` is trivial exactly when `x` is positive (`infiniteArtinAt_eq_one_iff_of_isReal`); for
  negative `x` it is the other element of the two-element group `G_{K_w}^ab`, complex conjugation.

## Main definitions

* `TauCeti.ClassFieldTheory.infiniteArtinAt`: the archimedean Artin map `K_wˣ →* G_{K_w}^ab`.

## Main results

* `TauCeti.ClassFieldTheory.infiniteArtinAt_layer`: on each finite layer, the archimedean Artin
  map is the Artin map of the archimedean class formation.
* `TauCeti.ClassFieldTheory.character_infiniteArtinAt`: the archimedean character formula.
* `TauCeti.ClassFieldTheory.ker_infiniteArtinAt_eq_iInf`: the kernel is the intersection of all
  norm subgroups.
* `TauCeti.ClassFieldTheory.infiniteArtinAt_eq_one_of_isComplex`: `Art_ℂ` is trivial.
* `TauCeti.ClassFieldTheory.infiniteArtinAt_eq_one_iff_of_isReal`: `Art_ℝ` has kernel `ℝ_{>0}`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV.
* J. S. Milne, *Class Field Theory*, Chapter VII, §8.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable {K : Type} [Field K]

/-- The **archimedean Artin map** `K_wˣ →* G_{K_w}^ab` at an infinite place `w`, into the
topological abelianization of the absolute Galois group `Gal(AlgebraicClosure K_w/K_w)`. It is the
absolute Artin map of the archimedean class formation `infiniteClassFormation w`
(`infiniteArtinAt_apply`), so on each finite layer it is the Artin map of that class formation
(`infiniteArtinAt_layer`). -/
def infiniteArtinAt (w : InfinitePlace K) :
    (w.Completion)ˣ →* Field.absoluteGaloisGroupAbelianization w.Completion :=
  (absoluteGaloisGroupRestrictEquiv w.Completion).symm.topologicalAbelianizationCongr.toMonoidHom
    |>.comp <| MonoidHom.toAdditive.symm
      ((infiniteClassFormation w).absoluteArtinMap.comp
        (unitsLevelEquiv (Algebra.ofId w.Completion (SeparableClosure w.Completion))
          (fixedField_toSubgroup_top w.Completion)).toAddMonoidHom)

/-- **The archimedean Artin map is the absolute Artin map of the archimedean class formation**:
the absolute Artin symbol of `x ∈ K_wˣ`, regarded as an element of the ground level
`((K_wˢ)ˣ)^{G_{K_w}}`, carried from `Gal(K_wˢ/K_w)^ab` to `Gal(AlgebraicClosure K_w/K_w)^ab`. -/
theorem infiniteArtinAt_apply (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infiniteArtinAt w x =
      (absoluteGaloisGroupRestrictEquiv w.Completion).symm.topologicalAbelianizationCongr
        ((infiniteClassFormation w).absoluteArtinMap
          (unitsLevelEquiv (Algebra.ofId w.Completion (SeparableClosure w.Completion))
            (fixedField_toSubgroup_top w.Completion) (Additive.ofMul x))).toMul := by
  rw [infiniteArtinAt, MonoidHom.comp_apply, MonoidHom.toAdditive_symm_apply_apply]
  rfl

/-- **On every finite layer the archimedean Artin map is the abstract Artin map** of the
archimedean class formation. If `σ ∈ Gal(AlgebraicClosure K_w/K_w)` represents `Art_w(x)`, then
the Artin symbol of `x` for the layer `V ◁ G_{K_w}` is the class of the restriction of `σ` to the
separable closure, read in `(G_{K_w}/V)^ab`. -/
theorem infiniteArtinAt_layer (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) (x : (w.Completion)ˣ)
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w x) :
    (infiniteClassFormation w).artinMap (ofOpenNormal V)
        (localGroundEquiv w.Completion V (Additive.ofMul x)) =
      Additive.ofMul (Abelianization.of ((galOfOpenNormalEquiv V).symm
        (QuotientGroup.mk (absoluteGaloisGroupRestrictEquiv w.Completion σ)))) := by
  -- The absolute Artin symbol of `x` for the class formation is the class of the restriction of
  -- `σ` to the separable closure.
  have habs : (infiniteClassFormation w).absoluteArtinMap
      (unitsLevelEquiv (Algebra.ofId w.Completion (SeparableClosure w.Completion))
        (fixedField_toSubgroup_top w.Completion) (Additive.ofMul x)) =
      Additive.ofMul ((absoluteGaloisGroupRestrictEquiv w.Completion σ :
        AbsoluteGaloisGroup w.Completion) :
          TopologicalAbelianization (AbsoluteGaloisGroup w.Completion)) := by
    rw [← ContinuousMulEquiv.topologicalAbelianizationCongr_mk, hσ, infiniteArtinAt_apply,
      ← ContinuousMulEquiv.topologicalAbelianizationCongr_symm,
      ContinuousMulEquiv.apply_symm_apply, ofMul_toMul]
  have hmem : (absoluteGaloisGroupRestrictEquiv w.Completion σ :
      AbsoluteGaloisGroup w.Completion) ∈ (ofOpenNormal V).ground := by
    simp
  refine (congrArg _ (groundEquivOfOpenNormal_unitsLevelEquiv w.Completion V x).symm).trans ?_
  refine ((infiniteClassFormation w).abelianizationRestrict_absoluteArtinMap V _).symm.trans ?_
  rw [habs, abelianizationRestrict_mk V ⟨_, hmem⟩]
  exact congrArg (fun γ ↦ Additive.ofMul (Abelianization.of γ))
    ((galOfOpenNormalEquiv V).eq_symm_apply.mpr (galOfOpenNormalEquiv_mk V ⟨_, hmem⟩))

/-- **The archimedean character formula** `χ(Art_w x) = inv_w(x ∪ δχ)`. If `σ` represents
`Art_w(x)`, then for every character `χ` of the abelianized Galois group of a layer `V ◁ G_{K_w}`,
the value of `χ` at the class of `σ` is the archimedean Brauer invariant of the inflation of the
cup product `x₀ ∪ δχ` of the degree-zero Tate class of `x` with the connecting class of `χ`. -/
theorem character_infiniteArtinAt (w : InfinitePlace K)
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) (x : (w.Completion)ˣ)
    (σ : Field.absoluteGaloisGroup w.Completion)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization w.Completion) = infiniteArtinAt w x)
    (χ : Additive (Abelianization (ofOpenNormal V).Gal) →+ AddCircle (1 : ℚ)) :
    χ (Additive.ofMul (Abelianization.of ((galOfOpenNormalEquiv V).symm
        (QuotientGroup.mk (absoluteGaloisGroupRestrictEquiv w.Completion σ))))) =
      infiniteInvMap w (brInfl V ((ofOpenNormal V).artinCharacterCup (unitsFormation w.Completion)
        (localGroundEquiv w.Completion V (Additive.ofMul x)) χ)) :=
  (congrArg χ (infiniteArtinAt_layer w V x σ hσ)).symm.trans
    (((infiniteClassFormation w).character_artinMap (ofOpenNormal V) _ χ).symm.trans
      (infiniteClassFormation_inv w V _))

/-- **The kernel of the archimedean Artin map is the intersection of all norm subgroups**: `Art_w`
is trivial at `x ∈ K_wˣ` exactly when `x` is a norm from every finite Galois extension of `K_w`. -/
theorem ker_infiniteArtinAt_eq_iInf (w : InfinitePlace K) :
    (infiniteArtinAt w).ker = ⨅ V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion),
      localNormSubgroup w.Completion V := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_iInf, infiniteArtinAt_apply,
    map_eq_one_iff _ (ContinuousMulEquiv.injective _), toMul_eq_one,
    ClassFormation.absoluteArtinMap_eq_zero_iff]
  refine forall_congr' fun V ↦ ?_
  rw [groundEquivOfOpenNormal_unitsLevelEquiv, localGroundEquiv_mem_normSubgroup_iff]

/-- **`Art_ℂ` is trivial**: at a complex place the absolute Galois group of the completion is
trivial. -/
theorem infiniteArtinAt_eq_one_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex)
    (x : (w.Completion)ˣ) : infiniteArtinAt w x = 1 := by
  have := subsingleton_absoluteGaloisGroup_of_isComplex w hw
  have : Subsingleton (Field.absoluteGaloisGroup w.Completion) :=
    (absoluteGaloisGroupRestrictEquiv w.Completion).toEquiv.subsingleton
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (infiniteArtinAt w x)
  rw [← hσ, Subsingleton.elim σ 1, QuotientGroup.mk_one]

/-- **The kernel of `Art_ℝ` is `ℝ_{>0} = N_{ℂ/ℝ}(ℂˣ)`**: at a real place, `Art_w(x)` is trivial
exactly when `x` is positive. For negative `x` it is therefore complex conjugation, the nontrivial
element of the two-element group `G_{K_w}^ab`. -/
theorem infiniteArtinAt_eq_one_iff_of_isReal (w : InfinitePlace K) (hw : w.IsReal)
    (x : (w.Completion)ˣ) :
    infiniteArtinAt w x = 1 ↔ 0 < Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) := by
  -- The norm subgroup of a layer `V ◁ G_{K_w}` is all of `K_wˣ` if `V = G_{K_w}`, and the positive
  -- units otherwise.
  have hnorm (V : OpenNormalSubgroup (AbsoluteGaloisGroup w.Completion)) :
      x ∈ localNormSubgroup w.Completion V ↔ V.toSubgroup.index = 1 ∨
        0 < Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) := by
    rw [localNormSubgroup_def, normGroup_eq_of_ringEquiv_real (Completion.ringEquivRealOfIsReal hw),
      finrank_classField]
    split_ifs with h <;> simp [h]
  rw [← MonoidHom.mem_ker, ker_infiniteArtinAt_eq_iInf, Subgroup.mem_iInf]
  refine ⟨fun h ↦ ((hnorm _).mp (h (realOpenNormalSubgroup w hw))).resolve_left ?_,
    fun h V ↦ (hnorm V).mpr (Or.inr h)⟩
  rw [realOpenNormalSubgroup_toSubgroup, Subgroup.index_bot,
    natCard_absoluteGaloisGroup_of_isReal w hw]
  decide

end TauCeti.ClassFieldTheory
