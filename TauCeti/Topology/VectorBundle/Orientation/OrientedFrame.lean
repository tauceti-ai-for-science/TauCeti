/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SpecialOrthogonal
public import TauCeti.Topology.VectorBundle.Orientation.OrthonormalFrame

/-!
# The oriented orthonormal frame bundle

Let `E → B` be a continuous Riemannian vector bundle with model fibre `F` of rank `n`, oriented
by `ω`, and let `V` be an `n`-dimensional real inner product space with an orientation `o`. The
positively oriented orthonormal frames of `E` are the orthonormal frames `V ≃ₗᵢ[ℝ] E b` carrying
`o` to the orientation `ω b` of the fibre (`TauCeti.VectorBundleOrientation.orientedFrames`).
They are the frames whose image in the orientation double cover lies on the section given by `ω`
(`TauCeti.VectorBundleOrientation.mem_orientedFrames_iff_toOrientationCover`), so they form a
clopen subset of the orthonormal frame bundle
(`TauCeti.VectorBundleOrientation.isClopen_orientedFrames`). Reversing `ω` or `o` exchanges the
positively and negatively oriented frames (`TauCeti.VectorBundleOrientation.neg_orientedFrames`,
`TauCeti.VectorBundleOrientation.compl_orientedFrames`).

The orthogonal group of `V` acts on frames on the right. A positively oriented frame stays
positively oriented under an orthogonal transformation `g` exactly when `g` lies in the special
orthogonal group (`TauCeti.VectorBundleOrientation.smul_mem_orientedFrames_iff`), so the special
orthogonal group acts on the positively oriented frames. On each fibre the action is free
(`TauCeti.VectorBundleOrientation.smul_eq_self_iff`) and transitive
(`TauCeti.VectorBundleOrientation.exists_smul_eq_of_mem_orientedFrames`). When
`n ≥ 1`, every fibre contains a positively oriented frame
(`TauCeti.VectorBundleOrientation.exists_mem_orientedFrames`); in rank `0` the single frame of a
fibre is positively oriented or not according to the sign of `ω`.

The positively oriented frames are locally trivial with fibre the special orthogonal group, by
trivializations equivariant for the right action
(`TauCeti.VectorBundleOrientation.exists_trivialization_orientedFrames`). Near a point `x`, a
local section of the orthonormal frame bundle through a positively oriented frame over `x` stays
positively oriented nearby, because the positively oriented frames form an open set; dividing by
this section trivializes the positively oriented frames. So they form a principal bundle with
structure group `SO(n)`: the reduction of the structure group of the orthonormal frame bundle
from `O(n)` to `SO(n)` determined by the orientation. They recover `E` as their associated bundle
with fibre the standard representation of the special orthogonal group on `V`
(`TauCeti.VectorBundleOrientation.associatedHomeomorph`).

The action of the special orthogonal group on the subtype of positively oriented frames is an
instance under `Fact (Fintype.card ι = finrank ℝ V)`, the assumption that `ι` indexes
orientations of `V`, which an instance cannot take as an explicit hypothesis.

## Main definitions

* `TauCeti.VectorBundleOrientation.orientedFrames`: the positively oriented orthonormal frames.
* `TauCeti.VectorBundleOrientation.associatedRel`: the relation `(p, g w) ∼ (p • g, w)` for
  special orthogonal `g` on pairs of a positively oriented frame and a vector of `V`.
* `TauCeti.VectorBundleOrientation.associatedHomeomorph`: the homeomorphism from the quotient by
  `associatedRel` onto the total space of `E`.

## Main results

* `TauCeti.VectorBundleOrientation.smul_mem_orientedFrames_iff`: the orthogonal transformations
  preserving positively oriented frames are those of positive determinant.
* `TauCeti.VectorBundleOrientation.isClopen_orientedFrames`: the positively oriented frames form a
  clopen set.
* `TauCeti.VectorBundleOrientation.exists_trivialization_orientedFrames`: the positively oriented
  frames are locally trivial with fibre the special orthogonal group, equivariantly.
* `TauCeti.VectorBundleOrientation.isOpenQuotientMap_totalSpaceMk_frame_apply`: applying positively
  oriented frames to vectors is an open quotient map onto the total space.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §§9, 12 (oriented bundles and the structure group `SO(n)`).
* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 6, §2 (reduction of the structure group of the orthonormal frame bundle to
  `SO(n)` by an orientation).
-/

public section

noncomputable section

open Bundle Module Set MulOpposite TauCeti.OrthonormalFrameBundle
open scoped Topology

variable {B : Type*} {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
  [TopologicalSpace (TotalSpace F E)] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace B] [FiberBundle F E] [VectorBundle ℝ F E]

namespace TauCeti.VectorBundleOrientation

variable (ω : VectorBundleOrientation F E ι) (o : Orientation ℝ V ι)

/-- The positively oriented orthonormal frames of the oriented bundle `E`: the orthonormal frames
modelled on `V` that carry the orientation `o` of `V` to the orientation `ω` of the fibre. -/
def orientedFrames : Set (OrthonormalFrameBundle F E V) :=
  {p | Orientation.map ι p.frame.toLinearEquiv o = ω p.proj}

variable {ω o}

/-- A frame is positively oriented when it carries the orientation `o` of `V` to the orientation
of its fibre. -/
@[simp]
theorem mem_orientedFrames_iff {p : OrthonormalFrameBundle F E V} :
    p ∈ ω.orientedFrames o ↔ Orientation.map ι p.frame.toLinearEquiv o = ω p.proj :=
  Iff.rfl

/-- A frame is positively oriented exactly when its image in the orientation double cover lies
on the section given by the orientation of the bundle. -/
theorem mem_orientedFrames_iff_toOrientationCover {p : OrthonormalFrameBundle F E V} :
    p ∈ ω.orientedFrames o ↔ toOrientationCover o p = ⟨p.proj, ω p.proj⟩ := by
  rw [toOrientationCover_apply, VectorBundleOrientationCover.mk_eq_mk_iff, mem_orientedFrames_iff]

variable (ω o) in
/-- Reversing the orientation of the bundle amounts to reversing the orientation of `V`. -/
theorem neg_orientedFrames : (-ω).orientedFrames o = ω.orientedFrames (-o) := by
  ext p
  rw [mem_orientedFrames_iff, mem_orientedFrames_iff, neg_apply, Orientation.map_neg]
  -- `neg_neg` is applied by `exact`: `rw` does not match the negation of orientations reached
  -- through `neg_apply`.
  exact ⟨fun h ↦ by rw [h]; exact neg_neg (G := Orientation ℝ (E p.proj) ι) _,
    fun h ↦ by rw [← h]; exact (neg_neg (G := Orientation ℝ (E p.proj) ι) _).symm⟩

section LocalSection

variable [CompleteSpace V]
  (T : Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle F E V → B))
  (p₀ : ω.orientedFrames o)

/-- The local section of the orthonormal frame bundle over the base set of `T` through the
frame `p₀`. -/
private def localSection (y : B) : OrthonormalFrameBundle F E V :=
  T.toOpenPartialHomeomorph.symm (y, (T p₀).2)

private theorem continuousOn_localSection : ContinuousOn (localSection T p₀) T.baseSet :=
  T.toOpenPartialHomeomorph.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
    fun _ hy ↦ T.mem_target.2 hy

variable {T p₀}

private theorem proj_localSection {y : B} (hy : y ∈ T.baseSet) :
    (localSection T p₀ y).proj = y :=
  T.proj_symm_apply' hy

private theorem apply_localSection {y : B} (hy : y ∈ T.baseSet) :
    T (localSection T p₀ y) = (y, (T p₀).2) :=
  T.apply_symm_apply' hy

/-- A frame over the base set of `T` is the local section through `p₀` acted on by the quotient
of their readings in `T`. -/
private theorem smul_localSection
    (hT : ∀ (g : unitary (V →L[ℝ] V)) (p : OrthonormalFrameBundle F E V),
      T (op g • p) = ((T p).1, (T p).2 * g))
    {p : OrthonormalFrameBundle F E V} (hp : p.proj ∈ T.baseSet) :
    op ((T p₀).2⁻¹ * (T p).2) • localSection T p₀ p.proj = p := by
  refine T.toOpenPartialHomeomorph.injOn (T.mem_source.2 ?_) (T.mem_source.2 hp) ?_
  · rwa [proj_smul, proj_localSection hp]
  · simp only [Trivialization.coe_coe, hT, apply_localSection hp, mul_inv_cancel_left]
    exact T.mk_proj_snd' hp

end LocalSection

variable [Fintype ι] [FiniteDimensional ℝ V]

variable (ω o) in
/-- The frames that are not positively oriented for `ω` are the positively oriented frames for
the opposite orientation `-ω`. -/
theorem compl_orientedFrames (hι : Fintype.card ι = finrank ℝ V) :
    (ω.orientedFrames o)ᶜ = (-ω).orientedFrames o := by
  ext p
  have := p.frame.toLinearEquiv.finiteDimensional
  rw [mem_compl_iff, mem_orientedFrames_iff, mem_orientedFrames_iff, neg_apply]
  exact Orientation.ne_iff_eq_neg _ _ (hι.trans p.frame.toLinearEquiv.finrank_eq)

section Action

variable [CompleteSpace V]

/-- An orthogonal transformation `g` carries a positively oriented frame to a positively oriented
frame exactly when `g` lies in the special orthogonal group. -/
theorem smul_mem_orientedFrames_iff (hι : Fintype.card ι = finrank ℝ V)
    {p : OrthonormalFrameBundle F E V} (hp : p ∈ ω.orientedFrames o) {g : unitary (V →L[ℝ] V)} :
    op g • p ∈ ω.orientedFrames o ↔ g ∈ specialOrthogonalGroup V := by
  rw [mem_orientedFrames_iff_toOrientationCover] at hp ⊢
  by_cases hg : g ∈ specialOrthogonalGroup V
  · rw [toOrientationCover_smul_of_det_pos hι o (mem_specialOrthogonalGroup_iff.1 hg), hp]
    exact iff_of_true rfl hg
  · rw [toOrientationCover_smul_of_det_neg hι o (det_neg_of_notMem_specialOrthogonalGroup hg), hp]
    exact iff_of_false (VectorBundleOrientationCover.deck_ne_self _) hg

/-- The special orthogonal group acts transitively on the positively oriented frames over each
point of the base. -/
theorem exists_smul_eq_of_mem_orientedFrames (hι : Fintype.card ι = finrank ℝ V)
    {p q : OrthonormalFrameBundle F E V} (hp : p ∈ ω.orientedFrames o)
    (hq : q ∈ ω.orientedFrames o) (h : p.proj = q.proj) :
    ∃ g ∈ specialOrthogonalGroup V, op g • p = q := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_iff.2 h
  exact ⟨g, (smul_mem_orientedFrames_iff hι hp).1 hq, rfl⟩

variable [Fact (Fintype.card ι = finrank ℝ V)]

/-- The right action of the special orthogonal group on the positively oriented frames. -/
instance : MulAction (specialOrthogonalGroup V)ᵐᵒᵖ (ω.orientedFrames o) where
  smul g p := ⟨op (g.unop : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle F E V),
    (smul_mem_orientedFrames_iff Fact.out p.2).2 g.unop.2⟩
  one_smul p := Subtype.ext (one_smul _ (p : OrthonormalFrameBundle F E V))
  mul_smul g h p := Subtype.ext (mul_smul (op (g.unop : unitary (V →L[ℝ] V)))
    (op (h.unop : unitary (V →L[ℝ] V))) (p : OrthonormalFrameBundle F E V))

/-- The action of the special orthogonal group is the restriction of the action of the
orthogonal group. -/
@[simp]
theorem coe_smul (g : (specialOrthogonalGroup V)ᵐᵒᵖ) (p : ω.orientedFrames o) :
    ((g • p : ω.orientedFrames o) : OrthonormalFrameBundle F E V) =
      op (g.unop : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle F E V) :=
  (rfl)

/-- The action of the special orthogonal group on the positively oriented frames is free. -/
@[simp]
theorem smul_eq_self_iff {g : specialOrthogonalGroup V} {p : ω.orientedFrames o} :
    op g • p = p ↔ g = 1 := by
  rw [Subtype.ext_iff, coe_smul, unop_op, OrthonormalFrameBundle.smul_eq_self_iff,
    OneMemClass.coe_eq_one]

/-- The right action of the special orthogonal group on the positively oriented frames is
continuous. -/
instance : ContinuousSMul (specialOrthogonalGroup V)ᵐᵒᵖ (ω.orientedFrames o) where
  continuous_smul := Continuous.subtype_mk ((continuous_op.comp ((continuous_subtype_val.comp
    continuous_unop).comp continuous_fst)).smul (continuous_subtype_val.comp continuous_snd)) _

end Action

omit [FiniteDimensional ℝ V] in
/-- In positive rank, every fibre contains a positively oriented frame. -/
theorem exists_mem_orientedFrames [Nonempty ι] (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) (b : B) :
    ∃ p ∈ ω.orientedFrames o, p.proj = b := by
  obtain ⟨p, hp⟩ := surjective_toOrientationCover (F := F) (E := E) hι hF o ⟨b, ω b⟩
  obtain rfl : p.proj = b :=
    (proj_toOrientationCover o p).symm.trans (congrArg VectorBundleOrientationCover.proj hp)
  exact ⟨p, mem_orientedFrames_iff_toOrientationCover.2 hp, rfl⟩

section Topology

variable [FiniteDimensional ℝ F]

/-- The positively oriented frames form a clopen subset of the orthonormal frame bundle. -/
theorem isClopen_orientedFrames (hι : Fintype.card ι = finrank ℝ V)
    (hF : Fintype.card ι = finrank ℝ F) : IsClopen (ω.orientedFrames o) := by
  have h : ω.orientedFrames o = toOrientationCover o ⁻¹' {q | q.orientation = ω q.proj} := by
    ext p
    rw [mem_preimage, toOrientationCover_apply]
    rfl
  exact h ▸ (ω.isClopen_setOf_orientation_eq hF).preimage (continuous_toOrientationCover hι o)

section OrientedLocalSection

variable [CompleteSpace V] [Fact (Fintype.card ι = finrank ℝ V)]
  (T : Trivialization (unitary (V →L[ℝ] V)) (proj : OrthonormalFrameBundle F E V → B))
  (p₀ : ω.orientedFrames o)

/-- The points of the base set of `T` where the local section through `p₀` is positively
oriented. -/
private def orientedBaseSet : Set B :=
  T.baseSet ∩ localSection T p₀ ⁻¹' ω.orientedFrames o

private theorem isOpen_orientedBaseSet (hF : Fintype.card ι = finrank ℝ F) :
    IsOpen (orientedBaseSet T p₀) :=
  (continuousOn_localSection T p₀).isOpen_inter_preimage T.open_baseSet
    (isClopen_orientedFrames Fact.out hF).isOpen

variable {T p₀}

variable (hT : ∀ (g : unitary (V →L[ℝ] V)) (p : OrthonormalFrameBundle F E V),
  T (op g • p) = ((T p).1, (T p).2 * g))
include hT

omit [FiniteDimensional ℝ F] in
private theorem mem_specialOrthogonalGroup_of_mem_orientedBaseSet
    {p : OrthonormalFrameBundle F E V} (hp : p ∈ ω.orientedFrames o)
    (hU : p.proj ∈ orientedBaseSet T p₀) :
    (T p₀).2⁻¹ * (T p).2 ∈ specialOrthogonalGroup V := by
  rw [← smul_mem_orientedFrames_iff Fact.out hU.2, smul_localSection hT hU.1]
  exact hp

open scoped Classical in
/-- The trivialization of the positively oriented frames over the points of the base set of `T`
where the local section through `p₀` is positively oriented, given by dividing by this section. -/
private def orientedTrivialization (hF : Fintype.card ι = finrank ℝ F) :
    Trivialization (specialOrthogonalGroup V)
      (fun p : ω.orientedFrames o ↦ (p : OrthonormalFrameBundle F E V).proj) where
  toFun p := ((p : OrthonormalFrameBundle F E V).proj,
    if h : (p : OrthonormalFrameBundle F E V).proj ∈ orientedBaseSet T p₀ then
      ⟨_, mem_specialOrthogonalGroup_of_mem_orientedBaseSet hT p.2 h⟩ else 1)
  invFun q := if h : q.1 ∈ orientedBaseSet T p₀ then
      ⟨op (q.2 : unitary (V →L[ℝ] V)) • localSection T p₀ q.1,
        (smul_mem_orientedFrames_iff Fact.out h.2).2 q.2.2⟩
    else p₀
  source := (fun p : ω.orientedFrames o ↦ (p : OrthonormalFrameBundle F E V).proj) ⁻¹'
    orientedBaseSet T p₀
  target := orientedBaseSet T p₀ ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q hq := by
    simp only [mem_preimage, hq.1, ↓reduceDIte, proj_smul, proj_localSection hq.1.1]
  left_inv' p hp := by
    refine Subtype.ext ?_
    have hp' : (p : OrthonormalFrameBundle F E V).proj ∈ orientedBaseSet T p₀ := hp
    simp only [hp', ↓reduceDIte]
    exact smul_localSection hT hp.1
  right_inv' q hq := by
    obtain ⟨y, g⟩ := q
    have hy : y ∈ orientedBaseSet T p₀ := hq.1
    simp only [hy, ↓reduceDIte, proj_smul, proj_localSection hy.1, Prod.mk.injEq, true_and]
    refine Subtype.ext ?_
    simp only [hT, apply_localSection hy.1, inv_mul_cancel_left]
  open_source := (isOpen_orientedBaseSet T p₀ hF).preimage
    (continuous_proj.comp continuous_subtype_val)
  open_target := (isOpen_orientedBaseSet T p₀ hF).prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_proj.comp continuous_subtype_val).continuousOn.prodMk ?_
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun p : ω.orientedFrames o ↦
      (T p₀).2⁻¹ * (T (p : OrthonormalFrameBundle F E V)).2) ?_ fun p hp ↦ ?_
    · have hT' : ContinuousOn (fun p : ω.orientedFrames o ↦
            T.toOpenPartialHomeomorph (p : OrthonormalFrameBundle F E V))
          ((fun p : ω.orientedFrames o ↦ (p : OrthonormalFrameBundle F E V).proj) ⁻¹'
            orientedBaseSet T p₀) :=
        T.toOpenPartialHomeomorph.continuousOn.comp continuous_subtype_val.continuousOn
          fun _ hp ↦ T.mem_source.2 (mem_preimage.1 hp).1
      exact continuousOn_const.mul (continuous_snd.comp_continuousOn hT')
    · have hp' : (p : OrthonormalFrameBundle F E V).proj ∈ orientedBaseSet T p₀ := hp
      simp only [Function.comp_apply, hp', ↓reduceDIte]
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr (f := fun q : B × specialOrthogonalGroup V ↦
      op (q.2 : unitary (V →L[ℝ] V)) • localSection T p₀ q.1) ?_ fun q hq ↦ ?_
    · exact (continuous_op.comp (continuous_subtype_val.comp continuous_snd)).continuousOn.smul
        ((continuousOn_localSection T p₀).comp continuousOn_fst fun q hq ↦ hq.1.1)
    · simp only [Function.comp_apply, hq.1, ↓reduceDIte]
  baseSet := orientedBaseSet T p₀
  open_baseSet := isOpen_orientedBaseSet T p₀ hF
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

open scoped Classical in
/-- Over its base set, the trivialization reads a positively oriented frame as its quotient by
the local section through `p₀`. -/
private theorem coe_orientedTrivialization_snd (hF : Fintype.card ι = finrank ℝ F)
    {p : ω.orientedFrames o} (hp : (p : OrthonormalFrameBundle F E V).proj ∈ orientedBaseSet T p₀) :
    ((orientedTrivialization hT (p₀ := p₀) hF p).2 : unitary (V →L[ℝ] V)) =
      (T p₀).2⁻¹ * (T (p : OrthonormalFrameBundle F E V)).2 := by
  -- `simp` does not unfold the coercion of the structure instance `orientedTrivialization` to a
  -- function, so `change` exposes the second component of its defining formula.
  change ((if h : _ then ⟨_, _⟩ else 1 : specialOrthogonalGroup V) : unitary (V →L[ℝ] V)) = _
  simp only [hp, ↓reduceDIte]

end OrientedLocalSection

/-- In positive rank `n`, the positively oriented frames are locally trivial with fibre the
special orthogonal group of `V`, by trivializations equivariant for the right action: they form
a principal bundle with structure group `SO(n)`. -/
theorem exists_trivialization_orientedFrames [Nonempty ι] [CompleteSpace V]
    [Fact (Fintype.card ι = finrank ℝ V)] [IsContinuousRiemannianBundle F E]
    (hF : Fintype.card ι = finrank ℝ F) (x : B) :
    ∃ t : Trivialization (specialOrthogonalGroup V)
        (fun p : ω.orientedFrames o ↦ (p : OrthonormalFrameBundle F E V).proj),
      x ∈ t.baseSet ∧ ∀ (g : specialOrthogonalGroup V) (p : ω.orientedFrames o),
        (p : OrthonormalFrameBundle F E V).proj ∈ t.baseSet →
          t (op g • p) = ((t p).1, (t p).2 * g) := by
  have hι : Fintype.card ι = finrank ℝ V := Fact.out
  obtain ⟨p₀, hp₀, rfl⟩ := exists_mem_orientedFrames (ω := ω) (o := o) hι hF x
  obtain ⟨T, hx, hT⟩ :=
    OrthonormalFrameBundle.exists_trivialization (E := E) (hι.symm.trans hF) p₀.proj
  refine ⟨orientedTrivialization hT (p₀ := ⟨p₀, hp₀⟩) hF, ⟨hx, ?_⟩, fun g p hp ↦ ?_⟩
  · -- The local section through `p₀` passes through `p₀` over its base point.
    rw [mem_preimage, localSection, T.symm_apply_mk_proj (T.mem_source.2 hx)]
    exact hp₀
  · have hp' : (op (g : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle F E V)).proj ∈
        orientedBaseSet T ⟨p₀, hp₀⟩ := hp
    refine Prod.ext rfl (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, coe_orientedTrivialization_snd hT hF hp,
      coe_orientedTrivialization_snd hT hF (p := op g • p) hp', coe_smul, hT, unop_op, mul_assoc]

section Associated

variable [CompleteSpace V] [Fact (Fintype.card ι = finrank ℝ V)]

omit [FiniteDimensional ℝ F] in
/-- Two positively oriented frames applied to two vectors give the same point of the total space
exactly when the pairs differ by a special orthogonal transformation, as `(p, g w)` and
`(p • g, w)` do. -/
theorem totalSpaceMk_frame_apply_eq_iff {p q : ω.orientedFrames o} {v w : V} :
    (⟨(p : OrthonormalFrameBundle F E V).proj, (p : OrthonormalFrameBundle F E V).frame v⟩ :
        TotalSpace F E) =
      ⟨(q : OrthonormalFrameBundle F E V).proj, (q : OrthonormalFrameBundle F E V).frame w⟩ ↔
      ∃ g : specialOrthogonalGroup V, q = op g • p ∧ v = (g : V →L[ℝ] V) w := by
  rw [OrthonormalFrameBundle.totalSpaceMk_frame_apply_eq_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgS : g ∈ specialOrthogonalGroup V :=
      (smul_mem_orientedFrames_iff Fact.out p.2).1 (hg ▸ q.2)
    exact ⟨⟨g, hgS⟩, Subtype.ext hg, rfl⟩
  · rintro ⟨g, rfl, rfl⟩
    exact ⟨g, rfl, rfl⟩

variable (ω o) in
/-- The relation on pairs of a positively oriented frame and a vector of `V` whose quotient is the
vector bundle associated to the positively oriented frames and the standard representation of
the special orthogonal group on `V`: the pair `(p, g w)` is related to `(p • g, w)`. -/
def associatedRel : Setoid (ω.orientedFrames o × V) where
  r x y := ∃ g : specialOrthogonalGroup V, y.1 = op g • x.1 ∧ x.2 = (g : V →L[ℝ] V) y.2
  -- By `totalSpaceMk_frame_apply_eq_iff`, the relation says that the two pairs give the same
  -- point of the total space.
  iseqv.refl _ := totalSpaceMk_frame_apply_eq_iff.1 rfl
  iseqv.symm h := totalSpaceMk_frame_apply_eq_iff.1 (totalSpaceMk_frame_apply_eq_iff.2 h).symm
  iseqv.trans h h' := totalSpaceMk_frame_apply_eq_iff.1
    ((totalSpaceMk_frame_apply_eq_iff.2 h).trans (totalSpaceMk_frame_apply_eq_iff.2 h'))

omit [FiniteDimensional ℝ F] in
/-- Unfolds `associatedRel`: two pairs are related when they differ by a special orthogonal
transformation. -/
theorem associatedRel_iff {x y : ω.orientedFrames o × V} :
    associatedRel ω o x y ↔
      ∃ g : specialOrthogonalGroup V, y.1 = op g • x.1 ∧ x.2 = (g : V →L[ℝ] V) y.2 :=
  Iff.rfl

omit [FiniteDimensional ℝ F] in
/-- The relation `associatedRel` is the kernel of applying positively oriented frames to
vectors. -/
theorem associatedRel_eq_ker :
    associatedRel ω o = Setoid.ker fun x : ω.orientedFrames o × V ↦
      (⟨(x.1 : OrthonormalFrameBundle F E V).proj, (x.1 : OrthonormalFrameBundle F E V).frame x.2⟩ :
        TotalSpace F E) :=
  Setoid.ext fun _ _ ↦ totalSpaceMk_frame_apply_eq_iff.symm

variable [Nonempty ι] [IsContinuousRiemannianBundle F E]

omit [CompleteSpace V] in
/-- In positive rank, applying positively oriented frames to vectors is an open quotient map onto
the total space of `E`. -/
theorem isOpenQuotientMap_totalSpaceMk_frame_apply (hF : Fintype.card ι = finrank ℝ F) :
    IsOpenQuotientMap fun x : ω.orientedFrames o × V ↦
      (⟨(x.1 : OrthonormalFrameBundle F E V).proj, (x.1 : OrthonormalFrameBundle F E V).frame x.2⟩ :
        TotalSpace F E) where
  surjective x := by
    obtain ⟨p, hp, hpx⟩ := exists_mem_orientedFrames (ω := ω) (o := o) Fact.out hF x.proj
    obtain ⟨b, v⟩ := x
    obtain rfl : p.proj = b := hpx
    exact ⟨(⟨p, hp⟩, p.frame.symm v), by simp⟩
  continuous := continuous_totalSpaceMk_frame_apply.comp
    (continuous_subtype_val.prodMap continuous_id)
  isOpenMap := isOpenMap_totalSpaceMk_frame_apply.comp
    ((isClopen_orientedFrames Fact.out hF).isOpen.isOpenEmbedding_subtypeVal.prodMap
      .id).isOpenMap

/-- In positive rank, the positively oriented frames reconstruct `E` as their associated bundle
with fibre the standard representation of the special orthogonal group on `V`: applying frames to
vectors descends to a homeomorphism from the quotient by `(p, g w) ∼ (p • g, w)` onto the total
space of `E`. It sends the class of `(p, v)` to `p v` in the fibre over `p.proj`
(`TauCeti.VectorBundleOrientation.associatedHomeomorph_mk`). -/
def associatedHomeomorph (hF : Fintype.card ι = finrank ℝ F) :
    Quotient (associatedRel ω o) ≃ₜ TotalSpace F E :=
  (Homeomorph.Quotient.congrRight (Setoid.ext_iff.1 associatedRel_eq_ker)).trans
    (Topology.IsQuotientMap.homeomorph
      (f := ⟨_, (isOpenQuotientMap_totalSpaceMk_frame_apply hF).continuous⟩)
      (isOpenQuotientMap_totalSpaceMk_frame_apply hF).isQuotientMap)

/-- The homeomorphism `associatedHomeomorph` sends the class of `(p, v)` to the vector `p v` of
the fibre over `p.proj`. -/
@[simp]
theorem associatedHomeomorph_mk (hF : Fintype.card ι = finrank ℝ F) (p : ω.orientedFrames o)
    (v : V) :
    associatedHomeomorph hF (Quotient.mk _ (p, v)) =
      ⟨(p : OrthonormalFrameBundle F E V).proj, (p : OrthonormalFrameBundle F E V).frame v⟩ :=
  (rfl)

/-- The inverse of `associatedHomeomorph` reads a vector of the fibre over `p.proj` in the
positively oriented frame `p`. -/
theorem associatedHomeomorph_symm_apply (hF : Fintype.card ι = finrank ℝ F)
    (p : ω.orientedFrames o) (x : E (p : OrthonormalFrameBundle F E V).proj) :
    (associatedHomeomorph hF).symm ⟨(p : OrthonormalFrameBundle F E V).proj, x⟩ =
      Quotient.mk _ (p, (p : OrthonormalFrameBundle F E V).frame.symm x) := by
  rw [Homeomorph.symm_apply_eq, associatedHomeomorph_mk, LinearIsometryEquiv.apply_symm_apply]

end Associated

end Topology

end TauCeti.VectorBundleOrientation
