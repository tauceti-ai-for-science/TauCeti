/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Bicollars from embedded collars

A bicollar (`TauCeti.IsBicollar`) of a map `f : N → M` is an *open* embedding `b : N × ℝ → M` with
zero slice `f`. In the statement of the generalized Schoenflies theorem, and whenever a collar is
written down in coordinates, one is instead given a topological embedding
`β : N × [-1, 1] → M` of a closed collar, with no openness asserted. When `N` and `M` are
topological manifolds without boundary of dimensions `m - 1` and `m`, invariance of domain supplies
the openness: `N × ℝ` is then an `m`-manifold without boundary, so a continuous injection
`N × ℝ → M` is an open embedding (`Continuous.isOpenEmbedding_of_injective`).

This file turns such collars into bicollars.

* A continuous injection `β : N × ℝ → M` is a bicollar of its zero slice
  (`Continuous.isBicollar_of_injective`).
* If `β : N × ℝ → M` is only continuous and injective on `N × (-1, 1)`, reparametrizing the line
  onto `(-1, 1)` by `Real.tanh` gives the bicollar `(x, t) ↦ β (x, tanh t)` of the zero slice
  (`ContinuousOn.isBicollar_tanh_of_injOn`). Its two sides `t > 0` and `t < 0` sweep out the
  images of `N × (0, 1)` and `N × (-1, 0)` under `β` (`TauCeti.image_univ_prod_tanh` with
  `Real.image_tanh_Ioi_zero` and `Real.image_tanh_Iio_zero`).
* For a closed collar `β : N × [-1, 1] → M` that is continuous and injective, the same
  reparametrization, composed with the projection `Set.projIcc` of `ℝ` onto `[-1, 1]`, is a
  bicollar of the zero slice `x ↦ β (x, 0)` (`Continuous.isBicollar_projIcc_tanh_of_injective`).

The dimension hypothesis cannot be dropped: `(x, t) ↦ (x, t, 0)` is a continuous injection
`ℝ × ℝ → ℝ³` whose image, a plane, is not open, so it is not a bicollar of the line
`ℝ × {0} × {0}`.

## Main results

* `Continuous.isBicollar_of_injective`: a continuous injection `N × ℝ → M` is a bicollar.
* `ContinuousOn.isBicollar_tanh_of_injOn`: a collar continuous and injective on `N × (-1, 1)`
  gives a bicollar after reparametrizing the line by `Real.tanh`.
* `Continuous.isBicollar_projIcc_tanh_of_injective`: the same for an embedded closed collar
  `N × [-1, 1] → M`.
* `TauCeti.image_univ_prod_tanh`: the images of the slabs `N × s` under the reparametrized
  collar.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 2B.3 (invariance
  of domain).
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, where the bicollar hypothesis is a closed collar `S^(m-1) × [-1, 1] → S^m`.
-/

public section

open Function Module Set Topology

namespace TauCeti

/-- The image of a slab `N × s` under the collar `(x, t) ↦ β (x, tanh t)` is the image under `β`
of the slab `N × tanh '' s`. With `Real.image_tanh_Ioi_zero` and `Real.image_tanh_Iio_zero`, the
two sides `t > 0` and `t < 0` of the collar sweep out `β (N × (0, 1))` and `β (N × (-1, 0))`. -/
theorem image_univ_prod_tanh {M N : Type*} (β : N × ℝ → M) (s : Set ℝ) :
    (fun p : N × ℝ ↦ β (p.1, Real.tanh p.2)) '' (univ ×ˢ s) = β '' (univ ×ˢ (Real.tanh '' s)) := by
  ext
  simp

end TauCeti

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

/-- **Invariance of domain for collars.** Let `N` and `M` be topological manifolds without
boundary, charted on finite-dimensional real normed spaces of dimensions `m - 1` and `m`. Then a
continuous injection `β : N × ℝ → M` is a bicollar of its zero slice `x ↦ β (x, 0)`: it is an open
embedding, since `N × ℝ` is an `m`-manifold without boundary. -/
theorem Continuous.isBicollar_of_injective {β : N × ℝ → M} (hβ : Continuous β)
    (hinj : Injective β) (hEF : finrank ℝ E = finrank ℝ F + 1) :
    TauCeti.IsBicollar (fun x ↦ β (x, 0)) β := by
  -- Mathlib's product charts are modelled on the type synonym `ModelProd F ℝ`, which carries no
  -- norm; read them on the normed space `F × ℝ` to apply invariance of domain.
  let : ChartedSpace (F × ℝ) (N × ℝ) := prodChartedSpace F N ℝ ℝ
  exact ⟨hβ.isOpenEmbedding_of_injective (E := F × ℝ) (F := E) hinj (by simp [hEF]),
    fun _ ↦ rfl⟩

/-- **A collar on `N × (-1, 1)` gives a bicollar.** Let `N` and `M` be topological manifolds
without boundary, charted on finite-dimensional real normed spaces of dimensions `m - 1` and `m`.
If `β : N × ℝ → M` is continuous and injective on `N × (-1, 1)`, then
`(x, t) ↦ β (x, tanh t)` is a bicollar of the zero slice `x ↦ β (x, 0)`. -/
theorem ContinuousOn.isBicollar_tanh_of_injOn {β : N × ℝ → M}
    (hβ : ContinuousOn β (univ ×ˢ Ioo (-1) 1)) (hinj : InjOn β (univ ×ˢ Ioo (-1) 1))
    (hEF : finrank ℝ E = finrank ℝ F + 1) :
    TauCeti.IsBicollar (fun x ↦ β (x, 0)) (fun p ↦ β (p.1, Real.tanh p.2)) := by
  have hmaps (p : N × ℝ) : (p.1, Real.tanh p.2) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 :=
    ⟨mem_univ _, Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  have hb := Continuous.isBicollar_of_injective (E := E) (F := F)
    (hβ.comp_continuous (by fun_prop) hmaps)
    (fun p q h ↦ Prod.ext (Prod.ext_iff.1 (hinj (hmaps p) (hmaps q) h)).1
      (Real.tanh_injective (Prod.ext_iff.1 (hinj (hmaps p) (hmaps q) h)).2)) hEF
  simpa only [Function.comp_def, Real.tanh_zero] using hb

/-- **A closed collar gives a bicollar.** Let `N` and `M` be topological manifolds without
boundary, charted on finite-dimensional real normed spaces of dimensions `m - 1` and `m`. If the
closed collar `β : N × [-1, 1] → M` is continuous and injective, then
`(x, t) ↦ β (x, tanh t)`, read through the projection `Set.projIcc` of `ℝ` onto `[-1, 1]`, is a
bicollar of the zero slice `x ↦ β (x, 0)`. -/
theorem Continuous.isBicollar_projIcc_tanh_of_injective {β : N × Icc (-1 : ℝ) 1 → M}
    (hβ : Continuous β) (hinj : Injective β) (hEF : finrank ℝ E = finrank ℝ F + 1) :
    TauCeti.IsBicollar (fun x ↦ β (x, ⟨0, by norm_num, by norm_num⟩))
      (fun p ↦ β (p.1, projIcc (-1) 1 (by norm_num) (Real.tanh p.2))) := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  have hb := ContinuousOn.isBicollar_tanh_of_injOn (E := E) (F := F)
    (β := fun p ↦ β (p.1, projIcc (-1) 1 hle p.2)) (by fun_prop)
    (fun p hp q hq h ↦ Prod.ext (Prod.ext_iff.1 (hinj h)).1
      ((strictMonoOn_projIcc hle).injOn (Ioo_subset_Icc_self hp.2) (Ioo_subset_Icc_self hq.2)
        (Prod.ext_iff.1 (hinj h)).2)) hEF
  simpa only [projIcc_of_mem hle (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)] using hb
