/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# The collar neighbourhood deforms onto the boundary

Let `c : N × [0, 1) → M` be a collar of `f : N → M` (`TauCeti.IsCollar f c`). Moving each point
`c (x, t)` to `c (x, (1 - s) * t)` deforms the collar neighbourhood `range c` within itself onto
the boundary `range f`, keeping the boundary inside itself. So the inclusion of the boundary into
its collar neighbourhood is a homotopy equivalence (`TauCeti.IsCollar.homotopyEquiv`), whose
homotopy inverse sends `c (x, t)` to `f x`. This is what makes homology relative to a collared
boundary computable by removing an open collar.

Every point of the collar neighbourhood off the boundary lies at a positive depth `t`, and the
thinner collar `(x, s) ↦ c (x, t * s)` of the same boundary misses it
(`TauCeti.IsCollar.exists_isCollar_range_subset_notMem`). So every point off the boundary is
avoided by some collar inside the given one.

## Main definitions

* `TauCeti.IsCollar.homotopyEquiv`: the inclusion of the boundary into its collar neighbourhood,
  as a homotopy equivalence.

## Main results

* `TauCeti.IsCollar.coe_homotopyEquiv_apply`: this homotopy equivalence is the inclusion.
* `TauCeti.IsCollar.exists_isCollar_range_subset_notMem`: a point off the boundary is missed by
  a thinner collar.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the collar neighbourhood of the boundary of a manifold (proof of Theorem 3.43).
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval ContinuousMap

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {N : Type*} [TopologicalSpace N] {f : N → X}
  {c : N × Ico (0 : ℝ) 1 → X}

namespace IsCollar

/-- The depth `t ∈ [0, 1)` of a collar, scaled by `1 - s` for `s ∈ [0, 1]`. -/
private def scaleDepth (p : I × Ico (0 : ℝ) 1) : Ico (0 : ℝ) 1 :=
  ⟨(1 - (p.1 : ℝ)) * p.2, mul_nonneg (sub_nonneg.2 p.1.2.2) p.2.2.1,
    (mul_le_of_le_one_left p.2.2.1 (sub_le_self _ p.1.2.1)).trans_lt p.2.2.2⟩

private theorem continuous_scaleDepth : Continuous scaleDepth :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private theorem scaleDepth_zero (t : Ico (0 : ℝ) 1) : scaleDepth (0, t) = t :=
  Subtype.ext (by simp [scaleDepth])

private theorem scaleDepth_one (t : Ico (0 : ℝ) 1) : scaleDepth (1, t) = ⟨0, by norm_num⟩ :=
  Subtype.ext (by simp [scaleDepth])

/-- The collar deformation of the collar neighbourhood `B = range c` onto the boundary
`range f`: at time `s` it moves the point `c (x, t)` to `c (x, (1 - s) * t)`. -/
private def deformation (hc : IsCollar f c) {B : Set X} (hB : B = range c) (p : I × B) : X :=
  c ((hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm (inclusion hB.subset p.2)).1,
    scaleDepth (p.1, (hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm
      (inclusion hB.subset p.2)).2))

private theorem continuous_deformation (hc : IsCollar f c) {B : Set X} (hB : B = range c) :
    Continuous (hc.deformation hB) := by
  have h : Continuous fun p : I × B ↦
      hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm (inclusion hB.subset p.2) :=
    hc.isOpenEmbedding.isEmbedding.toHomeomorph.symm.continuous.comp
      ((continuous_inclusion hB.subset).comp continuous_snd)
  exact hc.isOpenEmbedding.continuous.comp ((continuous_fst.comp h).prodMk
    (continuous_scaleDepth.comp (continuous_fst.prodMk (continuous_snd.comp h))))

private theorem deformation_mem (hc : IsCollar f c) {B : Set X} (hB : B = range c)
    (p : I × B) : hc.deformation hB p ∈ B :=
  (Set.ext_iff.1 hB _).2 (mem_range_self _)

private theorem deformation_zero (hc : IsCollar f c) {B : Set X} (hB : B = range c) (y : B) :
    hc.deformation hB (0, y) = y := by
  rw [deformation, scaleDepth_zero]
  exact congrArg Subtype.val
    (hc.isOpenEmbedding.isEmbedding.toHomeomorph.apply_symm_apply (inclusion hB.subset y))

private theorem deformation_one (hc : IsCollar f c) {B : Set X} (hB : B = range c) (y : B) :
    hc.deformation hB (1, y) ∈ range f := by
  rw [deformation, scaleDepth_one, hc.apply_zero]
  exact mem_range_self _

private theorem deformation_of_mem (hc : IsCollar f c) {B : Set X} (hB : B = range c)
    (p : I × B) (hp : (p.2 : X) ∈ range f) : hc.deformation hB p ∈ range f := by
  obtain ⟨x, hx⟩ := hp
  have hy : inclusion hB.subset p.2 = ⟨c (x, ⟨0, by norm_num⟩), mem_range_self _⟩ :=
    Subtype.ext (hx.symm.trans (hc.apply_zero x).symm)
  rw [deformation, hy, IsEmbedding.toHomeomorph_symm_apply]
  refine ⟨x, ?_⟩
  rw [← hc.apply_zero]
  exact congrArg c (Prod.ext rfl (Subtype.ext (by simp [scaleDepth])))

/-- **A collared boundary is a deformation retract of its collar neighbourhood.** For a collar
`c` of `f`, the inclusion of the boundary `range f` into the collar neighbourhood `range c` is a
homotopy equivalence, whose homotopy inverse sends `c (x, t)` to `f x`. It is stated for sets `A`
and `B` equal to these ranges, so that it applies to the subsets in which the ranges are
presented. -/
def homotopyEquiv (hc : IsCollar f c) {A B : Set X} (hA : A = range f) (hB : B = range c) :
    A ≃ₕ B :=
  ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction
    (by rw [hA, hB]; exact hc.range_subset_range) (hc.deformation hB)
    (hc.continuous_deformation hB) (hc.deformation_mem hB) (hc.deformation_zero hB)
    (fun y ↦ (Set.ext_iff.1 hA _).2 (hc.deformation_one hB y))
    (fun t y hy ↦ (Set.ext_iff.1 hA _).2
      (hc.deformation_of_mem hB (t, y) ((Set.ext_iff.1 hA _).1 hy)))

/-- The homotopy equivalence `TauCeti.IsCollar.homotopyEquiv` is the inclusion. -/
@[simp]
theorem coe_homotopyEquiv_apply (hc : IsCollar f c) {A B : Set X} (hA : A = range f)
    (hB : B = range c) (a : A) : (hc.homotopyEquiv hA hB a : X) = a := by
  unfold homotopyEquiv
  exact ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply ..

/-- **Every point off the boundary lies outside a thinner collar.** If `x` is not on the boundary
`range f`, some collar `c'` of `f` with `range c' ⊆ range c` misses `x`: if `x = c (y, t)`, then
`t > 0`, and the collar of depth `t` misses it. -/
theorem exists_isCollar_range_subset_notMem (hc : IsCollar f c) {x : X} (hx : x ∉ range f) :
    ∃ c' : N × Ico (0 : ℝ) 1 → X, IsCollar f c' ∧ range c' ⊆ range c ∧ x ∉ range c' := by
  by_cases h : x ∈ range c
  swap
  · exact ⟨c, hc, subset_rfl, h⟩
  obtain ⟨⟨y, t⟩, hyt⟩ := h
  have ht : 0 < (t : ℝ) := by
    refine t.2.1.lt_of_ne fun h0 ↦ hx ⟨y, ?_⟩
    rw [← hyt, ← hc.apply_zero]
    exact congrArg c (Prod.ext rfl (Subtype.ext h0))
  refine ⟨_, hc.scale t ⟨ht, t.2.2.le⟩, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact mem_range_self _
  · rintro ⟨⟨z, s⟩, hzs⟩
    have h := congrArg (fun p ↦ (p.2 : ℝ)) (hc.isOpenEmbedding.injective (hzs.trans hyt.symm))
    simp only [Prod.map_snd] at h
    nlinarith [s.2.2]

/-- The complement of a collar neighbourhood is contained in every set whose complement is the
boundary. -/
theorem compl_range_subset (hc : IsCollar f c) {S : Set X} (hS : Sᶜ = range f) :
    (range c)ᶜ ⊆ S :=
  compl_subset_comm.2 (hS ▸ hc.range_subset_range)

end IsCollar

end TauCeti
