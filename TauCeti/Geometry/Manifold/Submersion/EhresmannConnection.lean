/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Orthogonal
public import TauCeti.Geometry.Manifold.Distribution.Submersion
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Existence

/-!
# Ehresmann connections

An **Ehresmann connection** of class `C^n` on a map `f : P → B` is a `C^n` distribution `H` on
`P`, of rank the dimension of the model space of `B`, which is complementary at every point to
the vertical space `ker (df_p)` (`TauCeti.EhresmannConnection`). Every tangent vector of `P` then
splits uniquely into a horizontal and a vertical part (`TauCeti.EhresmannConnection.horizontalProj`
and `TauCeti.EhresmannConnection.verticalProj`). When `B` is finite-dimensional, the differential
`df_p` maps `H p` isomorphically onto `T_(f p) B`. In particular `df_p` is surjective at every
point, and every tangent vector of `B` has a unique horizontal lift at each point `p` over its
base point (`TauCeti.EhresmannConnection.horizontalLift`). These lifts are the infinitesimal form
of the horizontal lifts of curves.

Conversely, a `C^m` submersion between real manifolds modelled on finite-dimensional spaces has
an Ehresmann connection of class `C^n` whenever `n + 1 ≤ m`: for a `C^n` Riemannian metric on `P`,
the orthogonal complements of the vertical spaces
(`Manifold.IsSubmersion.orthogonalEhresmannConnection`). The vertical spaces form a `C^n`
distribution by `Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`, so their orthogonal
complements do too, by `TauCeti.IsContMDiffDistribution.orthogonal`. A Riemannian metric exists on
a Hausdorff σ-compact manifold, so then every such submersion has an Ehresmann connection
(`Manifold.IsSubmersion.nonempty_ehresmannConnection`). Unlike the horizontal spaces of a
Riemannian submersion (`TauCeti.IsRiemannianSubmersion`), these involve no metric on `B`.

## Main definitions

* `TauCeti.EhresmannConnection I J n f`: the `C^n` Ehresmann connections on `f : P → B`.
* `TauCeti.EhresmannConnection.horizontalProj`, `TauCeti.EhresmannConnection.verticalProj`: the
  projections of `T_p P` onto the horizontal and vertical spaces along each other.
* `TauCeti.EhresmannConnection.horizontalLift`: the horizontal lift `T_(f p) B → T_p P`.
* `Manifold.IsSubmersion.orthogonalEhresmannConnection`: the orthogonal complement of the
  vertical distribution of a submersion, for a Riemannian metric on its source.

## Main results

* `TauCeti.EhresmannConnection.horizontalProj_add_verticalProj`: the horizontal and vertical
  projections sum to the identity.
* `TauCeti.EhresmannConnection.surjective_mfderiv`: a map with an Ehresmann connection has
  surjective differential at every point.
* `TauCeti.EhresmannConnection.eq_horizontalLift_iff`: the horizontal lift of `w` is the unique
  horizontal vector mapped to `w` by the differential.
* `Manifold.IsSubmersion.nonempty_ehresmannConnection`: a submersion with Hausdorff σ-compact
  source has an Ehresmann connection.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer
  (1993), §9.3 (connections on fibre bundles).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 13
  (existence of Riemannian metrics) and Chapter 19 (distributions).
-/

public section

noncomputable section

open Bundle Function Module Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I 1 P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {J : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {n : ℕ∞ω}

variable (I J n) in
/-- A `C^n` **Ehresmann connection** on a map `f : P → B`: a `C^n` distribution on `P`, the
horizontal distribution, whose rank is the dimension of the model space of `B` and which is
complementary at every point `p` to the vertical space `ker (df_p)`. -/
@[ext]
structure EhresmannConnection (f : P → B) where
  /-- The horizontal subspace of the tangent space at each point. -/
  horizontal : Π p : P, Submodule 𝕜 (TangentSpace I p)
  /-- The horizontal subspaces form a `C^n` distribution whose rank is the dimension of the
  model space of the base. -/
  isContMDiffDistribution : IsContMDiffDistribution I n (finrank 𝕜 EB) horizontal
  /-- At every point the horizontal subspace is complementary to the vertical subspace, the
  kernel of the differential of `f`. -/
  isCompl (p : P) : IsCompl (horizontal p) (mfderiv I J f p).ker

namespace EhresmannConnection

variable {f : P → B} (Γ : EhresmannConnection I J n f) (p : P)

/-- The projection of `T_p P` onto the horizontal space along the vertical space. -/
def horizontalProj : TangentSpace I p →ₗ[𝕜] TangentSpace I p :=
  (Γ.horizontal p).projection (mfderiv I J f p).ker (Γ.isCompl p)

/-- The projection of `T_p P` onto the vertical space `ker (df_p)` along the horizontal space. -/
def verticalProj : TangentSpace I p →ₗ[𝕜] TangentSpace I p :=
  (mfderiv I J f p).ker.projection (Γ.horizontal p) (Γ.isCompl p).symm

/-- Every tangent vector is the sum of its horizontal and vertical parts. -/
@[simp]
theorem horizontalProj_add_verticalProj (v : TangentSpace I p) :
    Γ.horizontalProj p v + Γ.verticalProj p v = v :=
  Submodule.projection_add_projection_eq_self (Γ.isCompl p) v

@[simp]
theorem horizontalProj_apply_mem (v : TangentSpace I p) :
    Γ.horizontalProj p v ∈ Γ.horizontal p :=
  Submodule.projection_apply_mem _ v

/-- The vertical part of a tangent vector lies in the kernel of the differential. -/
@[simp]
theorem mfderiv_verticalProj (v : TangentSpace I p) :
    mfderiv I J f p (Γ.verticalProj p v) = 0 :=
  Submodule.projection_apply_mem (Γ.isCompl p).symm v

@[simp]
theorem horizontalProj_eq_self_iff {v : TangentSpace I p} :
    Γ.horizontalProj p v = v ↔ v ∈ Γ.horizontal p :=
  Submodule.projection_eq_self_iff _ v

@[simp]
theorem verticalProj_eq_self_iff {v : TangentSpace I p} :
    Γ.verticalProj p v = v ↔ mfderiv I J f p v = 0 :=
  Submodule.projection_eq_self_iff _ v

@[simp]
theorem horizontalProj_eq_zero_iff {v : TangentSpace I p} :
    Γ.horizontalProj p v = 0 ↔ mfderiv I J f p v = 0 :=
  Submodule.projection_apply_eq_zero_iff _

@[simp]
theorem verticalProj_eq_zero_iff {v : TangentSpace I p} :
    Γ.verticalProj p v = 0 ↔ v ∈ Γ.horizontal p :=
  Submodule.projection_apply_eq_zero_iff _

/-- Horizontal projection does not change the differential. -/
@[simp]
theorem mfderiv_horizontalProj (v : TangentSpace I p) :
    mfderiv I J f p (Γ.horizontalProj p v) = mfderiv I J f p v := by
  conv_rhs => rw [← Γ.horizontalProj_add_verticalProj p v]
  rw [map_add, mfderiv_verticalProj, add_zero]

/-- The differential of `f` is injective on horizontal vectors. -/
theorem injOn_mfderiv : Set.InjOn (mfderiv I J f p) (Γ.horizontal p) := by
  intro v hv w hw hvw
  have : v - w ∈ Γ.horizontal p ⊓ (mfderiv I J f p).ker :=
    ⟨sub_mem hv hw, by simp [LinearMap.mem_ker, map_sub, hvw]⟩
  rwa [(Γ.isCompl p).inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at this

variable [FiniteDimensional 𝕜 EB]

/-- The differential of `f` restricted to the horizontal space is bijective onto the tangent space
of the base, since both have the dimension of the model space of the base. -/
private theorem bijective_domRestrict_mfderiv :
    Bijective ((mfderiv I J f p : TangentSpace I p →ₗ[𝕜] TangentSpace J (f p)).domRestrict
      (Γ.horizontal p)) := by
  have hinj : Injective ((mfderiv I J f p : TangentSpace I p →ₗ[𝕜] TangentSpace J (f p)).domRestrict
      (Γ.horizontal p)) := fun v w h ↦ Subtype.ext (Γ.injOn_mfderiv p v.2 w.2 h)
  have : FiniteDimensional 𝕜 (TangentSpace J (f p)) := inferInstanceAs (FiniteDimensional 𝕜 EB)
  have : FiniteDimensional 𝕜 (Γ.horizontal p) := Module.Finite.of_injective _ hinj
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [Γ.isContMDiffDistribution.finrank_eq p, finrank_tangentSpace]

include Γ in
/-- **A map with an Ehresmann connection has surjective differential** at every point: already
its restriction to the horizontal space is onto. -/
theorem surjective_mfderiv : Surjective (mfderiv I J f p) := fun w ↦ by
  obtain ⟨v, hv⟩ := (bijective_domRestrict_mfderiv Γ p).2 w
  exact ⟨v, hv⟩

/-- The **horizontal lift** `T_(f p) B → T_p P`: the inverse of the differential of `f` on the
horizontal space at `p`. -/
def horizontalLift : TangentSpace J (f p) →ₗ[𝕜] TangentSpace I p :=
  (Γ.horizontal p).subtype ∘ₗ
    (LinearEquiv.ofBijective _ (bijective_domRestrict_mfderiv Γ p)).symm.toLinearMap

@[simp]
theorem horizontalLift_mem (w : TangentSpace J (f p)) :
    Γ.horizontalLift p w ∈ Γ.horizontal p :=
  Submodule.coe_mem _

/-- The horizontal lift of `w` lies over `w`. -/
@[simp]
theorem mfderiv_horizontalLift (w : TangentSpace J (f p)) :
    mfderiv I J f p (Γ.horizontalLift p w) = w :=
  (LinearEquiv.ofBijective _ (bijective_domRestrict_mfderiv Γ p)).apply_symm_apply w

/-- **Characterization of the horizontal lift**: the horizontal lift of `w` is the unique
horizontal vector mapped to `w` by the differential. -/
theorem eq_horizontalLift_iff {v : TangentSpace I p} {w : TangentSpace J (f p)} :
    v = Γ.horizontalLift p w ↔ v ∈ Γ.horizontal p ∧ mfderiv I J f p v = w := by
  refine ⟨?_, fun ⟨hv, hvw⟩ ↦ Γ.injOn_mfderiv p hv (Γ.horizontalLift_mem p w) ?_⟩
  · rintro rfl
    exact ⟨Γ.horizontalLift_mem p w, Γ.mfderiv_horizontalLift p w⟩
  · rw [hvw, mfderiv_horizontalLift]

/-- Lifting the differential of a vector gives its horizontal part. -/
@[simp]
theorem horizontalLift_mfderiv (v : TangentSpace I p) :
    Γ.horizontalLift p (mfderiv I J f p v) = Γ.horizontalProj p v :=
  ((Γ.eq_horizontalLift_iff p).mpr
    ⟨Γ.horizontalProj_apply_mem p v, Γ.mfderiv_horizontalProj p v⟩).symm

/-- The horizontal space is the range of the horizontal lift. -/
theorem range_horizontalLift : LinearMap.range (Γ.horizontalLift p) = Γ.horizontal p := by
  refine le_antisymm (LinearMap.range_le_iff_comap.mpr ?_) fun v hv ↦ ⟨mfderiv I J f p v, ?_⟩
  · exact Submodule.eq_top_iff'.mpr fun w ↦ Γ.horizontalLift_mem p w
  · rw [horizontalLift_mfderiv, horizontalProj_eq_self_iff]
    exact hv

end EhresmannConnection

end TauCeti

open TauCeti

section Orthogonal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H P]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {J : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {n m : ℕ∞ω} {f : P → B}

namespace Manifold.IsSubmersion

section Metric

variable [IsManifold I 1 P] [IsManifold I (n + 1) P]
  [RiemannianBundle (fun p : P ↦ TangentSpace I p)]
  [IsContMDiffRiemannianBundle I n E (fun p : P ↦ TangentSpace I p)]

/-- The **orthogonal Ehresmann connection** of a `C^m` submersion `f`, for a `C^n` Riemannian
metric on its source with `n + 1 ≤ m`: the horizontal space at `p` is the orthogonal complement of
the vertical space `ker (df_p)`. -/
def orthogonalEhresmannConnection (hf : IsSubmersion I J m f) (hnm : n + 1 ≤ m) :
    EhresmannConnection I J n f where
  horizontal p := (mfderiv I J f p).kerᗮ
  isContMDiffDistribution := by
    cases isEmpty_or_nonempty P with
    | inl _ => exact isContMDiffDistribution_iff.mpr fun p ↦ isEmptyElim p
    | inr h =>
      -- The vertical distribution has rank `dim E - dim EB`, and `dim EB ≤ dim E` since `df` is
      -- surjective, so its orthogonal complements have rank `dim EB`.
      have hm : m ≠ 0 := fun h ↦ by simp [h] at hnm
      have hle := LinearMap.finrank_range_le
        (mfderiv I J f h.some : TangentSpace I h.some →ₗ[ℝ] TangentSpace J (f h.some))
      rw [LinearMap.range_eq_top.mpr (hf.surjective_mfderiv hm h.some), finrank_top,
        finrank_tangentSpace, finrank_tangentSpace] at hle
      rw [show finrank ℝ EB = finrank ℝ E - (finrank ℝ E - finrank ℝ EB) by omega]
      exact (hf.isContMDiffDistribution_ker_mfderiv hnm).orthogonal
  isCompl p := (Submodule.isCompl_orthogonal _).symm

@[simp]
theorem orthogonalEhresmannConnection_horizontal (hf : IsSubmersion I J m f) (hnm : n + 1 ≤ m)
    (p : P) : (hf.orthogonalEhresmannConnection hnm).horizontal p = (mfderiv I J f p).kerᗮ :=
  (rfl)

end Metric

/-- **Existence of Ehresmann connections.** A `C^m` submersion from a smooth Hausdorff σ-compact
manifold has an Ehresmann connection of class `C^n` for every `n ≤ ∞` with `n + 1 ≤ m`, the
orthogonal one for a smooth Riemannian metric on its source. -/
theorem nonempty_ehresmannConnection [T2Space P] [SigmaCompactSpace P] [IsManifold I ∞ P]
    (hf : IsSubmersion I J m f) (hnm : n + 1 ≤ m) (hn : n ≤ ∞) :
    Nonempty (EhresmannConnection I J n f) := by
  obtain ⟨g⟩ := nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := E)
    (E := fun p : P ↦ TangentSpace I p)
  let : RiemannianBundle (fun p : P ↦ TangentSpace I p) := ⟨g.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun p : P ↦ TangentSpace I p) :=
    Bundle.instIsContMDiffRiemannianBundle g
  have : IsContMDiffRiemannianBundle I n E (fun p : P ↦ TangentSpace I p) := .of_le hn
  have h1 (k : ℕ∞ω) (hk : k ≤ ∞) : k + 1 ≤ ∞ := by
    lift k to ℕ∞ using ne_top_of_le_ne_top (by simp) hk
    exact_mod_cast le_top
  have : IsManifold I (n + 1) P := .of_le (h1 n hn)
  exact ⟨hf.orthogonalEhresmannConnection hnm⟩

end Manifold.IsSubmersion

end Orthogonal
