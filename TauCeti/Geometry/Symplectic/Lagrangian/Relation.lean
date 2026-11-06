/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions
public import TauCeti.LinearAlgebra.Submodule.Relation

/-!
# Composition of linear Lagrangian relations

A linear canonical relation from `(V, ω₁)` to `(W, ω₂)` is a Lagrangian subspace
of `V × W` for `ω₁ ⊖ ω₂`. Composition is ordinary relational composition of
submodules, with the intermediate vector eliminated. In finite dimension it is
again Lagrangian, even when the matching intersection is not transverse and the
projection is not injective. The diagonal and symplectic graphs are the identity
and invertible examples from `TauCeti.Geometry.Symplectic.Lagrangian.Constructions`.

This is the tangent-space calculation for geometric composition of smooth
Lagrangian correspondences. It does not supply smoothness or embeddedness of a
set-theoretic geometric composite.

The **excess** of the composition consists of the middle vectors `y` with `(0, y) ∈ L` and
`(y, 0) ∈ K`: the matched pairs `((0, y), (y, 0))` are exactly the matched pairs with zero image
in `L.relComp K`. For Lagrangian relations the excess is the symplectic complement of the sum of
the projections of `L` and `K` to the middle space
(`TauCeti.SymplecticForm.IsLagrangian.comap_inr_inf_comap_inl`). In finite dimension it is
therefore zero exactly when `L` and `K` are transverse over the middle space
(`TauCeti.SymplecticForm.IsLagrangian.comap_inr_inf_comap_inl_eq_bot_iff`); this is why a
transverse composite of Lagrangian immersions is again an immersion.

The proof intersects the product relation with the matching subspace, then
eliminates its characteristic directions. Orthogonal complementation exchanges
intersection and sum, so no transversality or dimension-of-intersection assumption
is needed in this linear calculation.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

namespace TauCeti.SymplecticForm

variable {V W U : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup U] [Module ℝ U]
  {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {ω₃ : SymplecticForm U}
  {L : Submodule ℝ (V × W)} {K : Submodule ℝ (W × U)}

/-- Composition of isotropic linear relations is isotropic. No finite-dimensionality
or transversality hypothesis is needed. -/
theorem IsIsotropic.relComp (hL : (ω₁.twistedProd ω₂).IsIsotropic L)
    (hK : (ω₂.twistedProd ω₃).IsIsotropic K) :
    (ω₁.twistedProd ω₃).IsIsotropic (L.relComp K) := by
  rw [isIsotropic_iff] at hL hK ⊢
  simp only [Submodule.mem_relComp]
  rintro x ⟨y, hxy, hyx⟩ z ⟨w, hzw, hwz⟩
  have h₁ := hL (x.1, y) hxy (z.1, w) hzw
  have h₂ := hK (y, x.2) hyx (w, z.2) hwz
  simp only [twistedProd_apply] at h₁ h₂ ⊢
  linarith

variable (V W U) in
/-- The matching subspace of `(V × W) × (W × U)`: pairs of pairs whose middle coordinates
agree. Intersecting a product relation with it is the first step of relational composition. -/
private def matching : Submodule ℝ ((V × W) × (W × U)) :=
  LinearMap.ker ((LinearMap.snd ℝ V W).comp (LinearMap.fst ℝ (V × W) (W × U)) -
    (LinearMap.fst ℝ W U).comp (LinearMap.snd ℝ (V × W) (W × U)))

private lemma mem_matching {z : (V × W) × (W × U)} : z ∈ matching V W U ↔ z.1.2 = z.2.1 := by
  simp [matching, sub_eq_zero]

/-- The characteristic directions of the matching subspace have zero outer coordinates and
equal middle coordinates. -/
private lemma eq_of_mem_orthogonal_matching {z : (V × W) × (W × U)}
    (hz : z ∈ ((ω₁.twistedProd ω₂).prod (ω₂.twistedProd ω₃)).orthogonal (matching V W U)) :
    z.1.1 = 0 ∧ z.1.2 = z.2.1 ∧ z.2.2 = 0 := by
  rw [mem_orthogonal_iff] at hz
  have h (y : (V × W) × (W × U)) (hy : y.1.2 = y.2.1) :
      ω₁ y.1.1 z.1.1 - ω₂ y.1.2 z.1.2 + (ω₂ y.2.1 z.2.1 - ω₃ y.2.2 z.2.2) = 0 :=
    by simpa only [prod_apply, twistedProd_apply] using hz y (mem_matching.mpr hy)
  refine ⟨ω₁.separatingRight _ fun v ↦ ?_, sub_eq_zero.mp <| ω₂.separatingRight _ fun w ↦ ?_,
    ω₃.separatingRight _ fun u ↦ ?_⟩
  · simpa using h ((v, 0), (0, 0)) rfl
  · have := h ((0, w), (w, 0)) rfl
    simp only [map_zero, LinearMap.zero_apply, zero_sub, sub_zero, map_sub] at this ⊢
    linarith
  · simpa using h ((0, 0), (0, u)) rfl

/-- Composition of finite-dimensional linear Lagrangian relations is Lagrangian,
including compositions with excess matching directions. -/
theorem IsLagrangian.relComp [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ U] (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    (ω₁.twistedProd ω₃).IsLagrangian (L.relComp K) := by
  let Ω := (ω₁.twistedProd ω₂).prod (ω₂.twistedProd ω₃)
  rw [isLagrangian_iff]
  refine ⟨hL.isIsotropic.relComp hK.isIsotropic, ?_⟩
  rw [isCoisotropic_iff]
  intro x hx
  let z : (V × W) × (W × U) := ((x.1, 0), (0, x.2))
  have hz : z ∈ Ω.orthogonal (L.prod K ⊓ matching V W U) := by
    rw [mem_orthogonal_iff]
    intro y hy
    have hmatch := mem_matching.mp hy.2
    have hcomp : (y.1.1, y.2.2) ∈ L.relComp K :=
      Submodule.mem_relComp.mpr ⟨y.1.2, hy.1.1, hmatch ▸ hy.1.2⟩
    have hzero := (mem_orthogonal_iff.mp hx) _ hcomp
    simpa [Ω, z, sub_eq_add_neg] using hzero
  -- Orthogonality puts the lift in the product relation plus a characteristic direction.
  have hprod : Ω.orthogonal (L.prod K) = L.prod K :=
    le_antisymm (isCoisotropic_iff_le.mp (hL.prod hK).isCoisotropic)
      (isIsotropic_iff_le.mp (hL.prod hK).isIsotropic)
  rw [Ω.orthogonal_inf, hprod] at hz
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
  obtain ⟨hbv, hbw, hbu⟩ := eq_of_mem_orthogonal_matching hb
  have hav : a.1.1 = x.1 := by
    simpa [z, hbv] using congrArg (fun p : (V × W) × (W × U) ↦ p.1.1) hab
  have hau : a.2.2 = x.2 := by
    simpa [z, hbu] using congrArg (fun p : (V × W) × (W × U) ↦ p.2.2) hab
  have haw : a.1.2 = a.2.1 := by
    have h₁ := congrArg (fun p : (V × W) × (W × U) ↦ p.1.2) hab
    have h₂ := congrArg (fun p : (V × W) × (W × U) ↦ p.2.1) hab
    dsimp [z] at h₁ h₂
    rw [← hbw] at h₂
    exact add_right_cancel (h₁.trans h₂.symm)
  apply Submodule.mem_relComp.mpr
  exact ⟨a.1.2, hav ▸ ha.1, hau ▸ haw ▸ ha.2⟩

/-! ### The excess of a composition -/

/-- For a Lagrangian relation `L ⊆ V × W`, the vectors `y` with `(0, y) ∈ L` form the
`ω₂`-complement of the projection of `L` to `W`. -/
theorem IsLagrangian.comap_inr_eq_orthogonal_map_snd
    (hL : (ω₁.twistedProd ω₂).IsLagrangian L) :
    L.comap (LinearMap.inr ℝ V W) = ω₂.orthogonal (L.map (LinearMap.snd ℝ V W)) := by
  ext y
  simp only [Submodule.mem_comap, LinearMap.inr_apply, mem_orthogonal_iff, Submodule.mem_map,
    LinearMap.snd_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine ⟨fun hy p hp ↦ ?_, fun hy ↦ isCoisotropic_iff.mp hL.isCoisotropic _ ?_⟩
  · simpa using hL.symplecticForm_apply_eq_zero hp hy
  · rw [mem_orthogonal_iff]
    intro p hp
    simp [hy p hp]

/-- For a Lagrangian relation `K ⊆ W × U`, the vectors `y` with `(y, 0) ∈ K` form the
`ω₂`-complement of the projection of `K` to `W`. -/
theorem IsLagrangian.comap_inl_eq_orthogonal_map_fst
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    K.comap (LinearMap.inl ℝ W U) = ω₂.orthogonal (K.map (LinearMap.fst ℝ W U)) := by
  ext y
  simp only [Submodule.mem_comap, LinearMap.inl_apply, mem_orthogonal_iff, Submodule.mem_map,
    LinearMap.fst_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine ⟨fun hy p hp ↦ ?_, fun hy ↦ isCoisotropic_iff.mp hK.isCoisotropic _ ?_⟩
  · simpa using hK.symplecticForm_apply_eq_zero hp hy
  · rw [mem_orthogonal_iff]
    intro p hp
    simp [hy p hp]

/-- **The excess of a composition of Lagrangian relations.** The middle vectors `y` with
`(0, y) ∈ L` and `(y, 0) ∈ K` are the matched pairs `((0, y), (y, 0))` lost when the middle
coordinate is eliminated, that is, the kernel of the projection from the matched pairs onto
`L.relComp K`. They form the `ω₂`-complement of the sum of the projections of `L` and `K` to the
middle space `W`. -/
theorem IsLagrangian.comap_inr_inf_comap_inl (hL : (ω₁.twistedProd ω₂).IsLagrangian L)
    (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    L.comap (LinearMap.inr ℝ V W) ⊓ K.comap (LinearMap.inl ℝ W U) =
      ω₂.orthogonal (L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U)) := by
  rw [hL.comap_inr_eq_orthogonal_map_snd, hK.comap_inl_eq_orthogonal_map_fst, orthogonal_sup]

/-- **Transverse composition has no excess.** In finite dimension, the composition of two
Lagrangian relations has no excess directions exactly when the relations are transverse over the
middle space, that is, when their projections to `W` span `W`. -/
theorem IsLagrangian.comap_inr_inf_comap_inl_eq_bot_iff [FiniteDimensional ℝ W]
    (hL : (ω₁.twistedProd ω₂).IsLagrangian L) (hK : (ω₂.twistedProd ω₃).IsLagrangian K) :
    L.comap (LinearMap.inr ℝ V W) ⊓ K.comap (LinearMap.inl ℝ W U) = ⊥ ↔
      L.map (LinearMap.snd ℝ V W) ⊔ K.map (LinearMap.fst ℝ W U) = ⊤ := by
  rw [hL.comap_inr_inf_comap_inl hK]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, orthogonal_top]⟩
  rw [← ω₂.orthogonal_orthogonal (_ ⊔ _), h, orthogonal_bot]

end TauCeti.SymplecticForm
