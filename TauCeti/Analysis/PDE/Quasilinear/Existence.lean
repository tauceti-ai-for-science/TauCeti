/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem.ContinuousDependence
import TauCeti.Analysis.Convex.SchauderFixedPoint
import TauCeti.Analysis.Sobolev.RellichKondrachov
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory

/-!
# Existence for the quasilinear Dirichlet problem

Let `Ω ⊆ ℝⁿ⁺¹` be a bounded open set and let `A(x, z)` be a matrix coefficient which is a
Carathéodory function, measurable in `x` and continuous in `z`, and uniformly elliptic with the
same constants `λ ≤ Λ` for every `z`. This file proves that the quasilinear Dirichlet problem

`-div(A(x, u) ∇u) = ℓ` in `Ω`, `u = g` on `∂Ω`,

has a weak solution `u ∈ H¹(Ω)` for every `ℓ ∈ H⁻¹(Ω)` and every `g ∈ H¹(Ω)`: `u - g ∈ H¹₀(Ω)`
and `∫_Ω A(x, u) ∇u · ∇w = ℓ(w)` for every `w ∈ H¹₀(Ω)`
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_forall_energyFormH1_apply_value_eq_of_subset_ball`).
The forcing `ℓ` covers right-hand sides `f + div F` with `f, F ∈ L²(Ω)`. No regularity of `∂Ω` is
assumed and uniqueness is not claimed.

## The compact map

Freezing the coefficient at `v ∈ L²(Ω)` gives the linear problem `-div(A(x, v(x)) ∇u) = ℓ`,
`u - g ∈ H¹₀(Ω)`, which Lax--Milgram solves. Its solutions are bounded in `H¹(Ω)` uniformly in `v`,
by the energy estimate with the coercivity constant `λ / (2 (4R² + 1))` of a domain in a ball of
radius `R`. The map `T(v) = u` is

* continuous from `L²(Ω)` to `H¹(Ω)` (`TauCeti.PDE.continuous_of_forall_energyFormH1_apply_eq`):
  along a subsequence `vₖ → v` almost everywhere, so the frozen coefficients converge almost
  everywhere, and the solutions converge by
  `TauCeti.PDE.tendsto_of_forall_energyFormH1_eq_of_tendsto_ae`;
* compact into `L²(Ω)`
  (`TauCeti.PDE.isCompact_closure_range_value_of_forall_energyFormH1_apply_eq`), by the
  Rellich--Kondrachov theorem for `H¹₀(Ω)`.

Schauder's theorem (`TauCeti.schauderFixedPoint_isCompact_closure_range`) then gives a fixed
point `u = T(u)`, which is a solution. The compactness comes from Rellich--Kondrachov rather than
from a Hölder estimate up to the boundary, so neither a boundary De Giorgi estimate nor any
regularity of `∂Ω` enters.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 11 (fixed-point methods for quasilinear equations).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 9.2 (fixed-point methods).
-/

public section

open MeasureTheory TopologicalSpace Filter
open scoped Matrix Topology

namespace TauCeti.PDE

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {A : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {lam Lam : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
-- The shortcut instances of the energy-form file, so that the operator norm of the bundled
-- energy form `TauCeti.PDE.energyFormH1L` is found by instance search.
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

/-- Freezing the second variable of a Carathéodory coefficient at a measurable function gives a
measurable coefficient field. -/
private theorem aestronglyMeasurable_apply
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    AEStronglyMeasurable (fun x => A x (v x))
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
  -- The matrices are seen as `Fin (n + 1) → Fin (n + 1) → ℝ`, whose metrizable topology is found
  -- by instance search.
  (Lp.aestronglyMeasurable v).apply_of_forall_of_continuousAt
    (G := Fin (n + 1) → Fin (n + 1) → ℝ) hAm (hAc.mono fun _ hx => hx.continuousAt)

/-- Freezing the second variable keeps uniform ellipticity with the same constants. -/
private theorem uniformlyEllipticOn_apply
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam) (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :
    UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) (fun x => A x (v x))
      lam Lam :=
  uniformlyEllipticOn_iff.2 ⟨(hA 0).pos, (uniformlyEllipticOn_iff.1 (hA 0)).2.1,
    fun x hx => (uniformlyEllipticOn_iff.1 (hA (v x))).2.2 hx⟩

/-- The uniform coercivity constant `λ / (2 (4R² + 1))` of the frozen energy forms on a domain in
a ball of radius `R`. -/
private theorem mul_norm_sq_le_energyFormH1_apply
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    {z₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z₀ R)
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (w : W1p0 volume Omega 2) :
    lam / (2 * ((2 * R) ^ 2 + 1)) * ‖w‖ ^ 2 ≤
      energyFormH1 (fun x => A x (v x)) 0 0 (w : W1p volume Omega 2) (w : W1p volume Omega 2) := by
  have h := (uniformlyEllipticOn_apply hA v).mul_norm_sq_le_energyFormH1_self_of_subset_ball
    (aestronglyMeasurable_apply hAm hAc v)
    (b := 0) (c := 0) aestronglyMeasurable_const aestronglyMeasurable_const (beta := 0) (gamma := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl) hball w.2
  have hlam := (hA 0).pos
  rw [Submodule.norm_coe] at h
  convert h using 2
  field_simp
  ring

/-- Frozen-coefficient solutions along data converging almost everywhere converge in `H¹(Ω)`. -/
private theorem tendsto_of_tendsto_ae
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    {z₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z₀ R)
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)}
    {v : ℕ → Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {v₀ : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hv : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Tendsto (fun k => v k x) atTop (𝓝 (v₀ x)))
    {u : ℕ → W1p volume Omega 2} {u₀ : W1p volume Omega 2}
    (hsub : ∀ k, u k - u₀ ∈ w1p0Submodule volume Omega 2)
    (hu₀ : ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (v₀ x)) 0 0 u₀ (w : W1p volume Omega 2) = ℓ w)
    (hu : ∀ k, ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (v k x)) 0 0 (u k) (w : W1p volume Omega 2) = ℓ w) :
    Tendsto u atTop (𝓝 u₀) := by
  have hlam := (hA 0).pos
  refine tendsto_of_forall_energyFormH1_eq_of_tendsto_ae (b := 0) (c := 0)
    (a' := fun k x => A x (v k x)) (b' := fun _ => 0) (c' := fun _ => 0) (K := Lam)
    (C := lam / (2 * ((2 * R) ^ 2 + 1)))
    (fun k => aestronglyMeasurable_energyIntegrand
      (aestronglyMeasurable_apply hAm hAc _)
      aestronglyMeasurable_const aestronglyMeasurable_const) (fun k => ?_) ?_ (by positivity)
    (fun k => mul_norm_sq_le_energyFormH1_apply hA hAm hAc hball _) hsub hu₀ hu
  · -- The frozen energy densities are bounded by the upper ellipticity constant.
    filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
    simpa using opNorm_energyIntegrand_le_of_bounds (hA 0).upper_nonneg
      (fun η ξ => (hA (v k x)).upper_bound hx η ξ)
      (b₀ := 0) (c₀ := 0) (le_refl _) (le_refl _)
  · -- The coefficient is continuous in the frozen value.
    filter_upwards [hv, hAc] with x hx hcx
    have hc : Continuous fun z => energyIntegrand (A x z) (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (0 : ℝ) :=
      hcx.energyIntegrand continuous_const continuous_const
    simpa only [Pi.zero_apply, Function.comp_def] using (hc.tendsto _).comp hx

/-- The frozen energy density is essentially bounded. -/
private theorem memLp_energyIntegrand_apply
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    MemLp (fun x => energyIntegrand (A x (v x))
      ((0 : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x)
      ((0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) ⊤
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
  memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) (hA 0).upper_nonneg
    (aestronglyMeasurable_apply hAm hAc v)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx η ξ => (hA (v x)).upper_bound hx η ξ) (fun _ _ => by simp) (fun _ _ => by simp)

/-- The frozen energy form is bounded by the upper ellipticity constant. -/
private theorem norm_energyFormH1L_apply_le
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ‖energyFormH1L (memLp_energyIntegrand_apply hA hAm hAc v)‖ ≤ Lam := by
  have h := norm_energyFormH1L_le_of_bounds (memLp_energyIntegrand_apply hA hAm hAc v)
    (hA 0).upper_nonneg ((ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx η ξ =>
      (hA (v x)).upper_bound hx η ξ) le_rfl le_rfl
    (Filter.Eventually.of_forall fun x => by simp) (Filter.Eventually.of_forall fun x => by simp)
  simpa only [add_zero] using h

/-- Arithmetic of the a priori bound: `(l + N g) / (λ / D) ≤ D (l + Λ g) / λ` when `N ≤ Λ`. -/
private theorem div_le_mul_div_of_le {l N Lam g lam D : ℝ} (hlam : 0 < lam) (hD : 0 < D)
    (hg : 0 ≤ g) (hN : N ≤ Lam) : (l + N * g) / (lam / D) ≤ D * (l + Lam * g) / lam := by
  rw [div_div_eq_mul_div, mul_comm _ D]
  gcongr

/-- The a priori bound `‖u - g‖ ≤ 2 (4R² + 1) (‖ℓ‖ + Λ ‖g‖) / λ` for a solution of a frozen
problem, uniform in the frozen function. -/
private theorem norm_sub_le_of_forall_energyFormH1_apply_eq
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    {z₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z₀ R)
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {g : W1p volume Omega 2}
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {u : W1p volume Omega 2} (hug : u - g ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (v x)) 0 0 u (w : W1p volume Omega 2) = ℓ w) :
    ‖u - g‖ ≤ 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam := by
  have hlam := (hA 0).pos
  have hb := norm_sub_le_of_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq
    (memLp_energyIntegrand_apply hA hAm hAc v) (by positivity)
    (mul_norm_sq_le_energyFormH1_apply hA hAm hAc hball v) hug hu
  exact hb.trans (div_le_mul_div_of_le hlam (by positivity) (norm_nonneg g)
    (norm_energyFormH1L_apply_le hA hAm hAc v))

/-- The value of a frozen solution is the value of `g` plus the value of an element of a fixed
ball of `H¹₀(Ω)`. -/
private theorem value_mem_image_closedBall
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    {z₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z₀ R)
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {g : W1p volume Omega 2}
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {u : W1p volume Omega 2} (hug : u - g ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (v x)) 0 0 u (w : W1p volume Omega 2) = ℓ w) :
    W1p.value u ∈ (W1p.value g + ·) '' (W1p0.valueL '' Metric.closedBall 0
      (2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam)) := by
  let w : W1p0 volume Omega 2 := ⟨u - g, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hug⟩
  have hw : ‖w‖ ≤ 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam :=
    (Submodule.norm_coe w).trans_le
      (norm_sub_le_of_forall_energyFormH1_apply_eq hA hAm hAc hball v hug hu)
  refine ⟨W1p0.valueL w, ⟨w, mem_closedBall_zero_iff.2 hw, rfl⟩, ?_⟩
  rw [W1p0.valueL_apply, ← W1p.valueL_apply, ← W1p.valueL_apply, ← W1p.valueL_apply]
  exact (congrArg _ (map_sub W1p.valueL u g)).trans (add_sub_cancel _ _)

/-- **Continuity of the frozen-coefficient solution map.** Let `Ω` be bounded and, for every
`v ∈ L²(Ω)`, let `S v ∈ H¹(Ω)` be a weak solution of the linear Dirichlet problem
`-div(A(x, v(x)) ∇(S v)) = ℓ` in `Ω` with `S v - g ∈ H¹₀(Ω)`. Then `S` is continuous from
`L²(Ω)` to `H¹(Ω)`. -/
theorem continuous_of_forall_energyFormH1_apply_eq
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    (hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {g : W1p volume Omega 2}
    {S : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
      W1p volume Omega 2}
    (hSg : ∀ v, S v - g ∈ w1p0Submodule volume Omega 2)
    (hS : ∀ v, ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (v x)) 0 0 (S v) (w : W1p volume Omega 2) = ℓ w) :
    Continuous S := by
  obtain ⟨R, -, hball⟩ := hOmega.subset_ball_lt 0 0
  rw [continuous_iff_seqContinuous]
  intro v v₀ hv
  -- Every subsequence has a further subsequence converging almost everywhere.
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (hv.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, tendsto_of_tendsto_ae hA hAm hAc hball hae (fun k => ?_) (hS v₀) fun k => hS _⟩
  have h := Submodule.sub_mem _ (hSg (v (ns (ms k)))) (hSg v₀)
  rw [sub_sub_sub_cancel_right] at h
  exact (ClosedSubmodule.mem_toSubmodule_iff _ _).1 h

/-- **Compactness of the frozen-coefficient solution map.** Under the hypotheses of
`TauCeti.PDE.continuous_of_forall_energyFormH1_apply_eq`, the values `v ↦ S v` of the frozen
solutions form a relatively compact subset of `L²(Ω)`: they lie in a fixed ball of `g + H¹₀(Ω)`,
which the Rellich--Kondrachov theorem maps to a relatively compact subset of `L²(Ω)`. -/
theorem isCompact_closure_range_value_of_forall_energyFormH1_apply_eq
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    (hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {g : W1p volume Omega 2}
    {S : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
      W1p volume Omega 2}
    (hSg : ∀ v, S v - g ∈ w1p0Submodule volume Omega 2)
    (hS : ∀ v, ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (v x)) 0 0 (S v) (w : W1p volume Omega 2) = ℓ w) :
    IsCompact (closure (Set.range fun v => W1p.value (S v))) := by
  obtain ⟨R, -, hball⟩ := hOmega.subset_ball_lt 0 0
  -- Rellich--Kondrachov: the values of a ball of `H¹₀(Ω)` are relatively compact in `L²(Ω)`.
  have hK := ((W1p0.isCompactOperator_valueL (mu := volume) (Omega := Omega) (p := 2)
    (by norm_num) hOmega).isCompact_closure_image_closedBall
      (2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam)).image
        (continuous_const_add (W1p.value g))
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨v, rfl⟩
  exact Set.image_mono subset_closure
    (value_mem_image_closedBall hA hAm hAc hball v (hSg v) (hS v))

/-- The frozen linear problem `-div(A(x, v(x)) ∇u) = ℓ`, `u - g ∈ H¹₀(Ω)`, has a solution. -/
private theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_apply_eq
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    {z₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z₀ R)
    (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) (g : W1p volume Omega 2)
    (v : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃ u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ w : W1p0 volume Omega 2,
        energyFormH1 (fun x => A x (v x)) 0 0 u (w : W1p volume Omega 2) = ℓ w :=
  (UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
    (uniformlyEllipticOn_apply hA v) (aestronglyMeasurable_apply hAm hAc v)
    (b := 0) (c := 0) aestronglyMeasurable_const aestronglyMeasurable_const (beta := 0)
    (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl) hball
    (by simpa using (hA 0).pos) ℓ g).exists

/-- **The fixed point of the frozen-coefficient map.** Under the hypotheses of
`TauCeti.PDE.continuous_of_forall_energyFormH1_apply_eq`, Schauder's theorem gives `v ∈ L²(Ω)`
whose frozen solution `S v` has value `v`. -/
private theorem exists_value_eq_of_forall_energyFormH1_apply_eq
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    (hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {ℓ : StrongDual ℝ (W1p0 volume Omega 2)} {g : W1p volume Omega 2}
    {S : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) →
      W1p volume Omega 2}
    (hSg : ∀ v, S v - g ∈ w1p0Submodule volume Omega 2)
    (hS : ∀ v, ∀ w : W1p0 volume Omega 2,
      energyFormH1 (fun x => A x (v x)) 0 0 (S v) (w : W1p volume Omega 2) = ℓ w) :
    ∃ v, W1p.value (S v) = v := by
  have hT : Continuous fun v => W1p.value (S v) := by
    simpa only [Function.comp_def, W1p.valueL_apply] using W1p.valueL.continuous.comp
      (continuous_of_forall_energyFormH1_apply_eq hA hAm hAc hOmega hSg hS)
  obtain ⟨v, hv⟩ := schauderFixedPoint_isCompact_closure_range hT
    (isCompact_closure_range_value_of_forall_energyFormH1_apply_eq hA hAm hAc hOmega hSg hS)
  exact ⟨v, hv⟩

/-- **Existence for the quasilinear Dirichlet problem.** Let `Ω ⊆ ℝⁿ⁺¹` be an open set contained
in a ball of radius `R`. Let `A(x, z)` be a matrix coefficient that is measurable in `x ∈ Ω` for
every `z`, continuous in `z` for almost every `x ∈ Ω`, and uniformly elliptic on `Ω` with the same
constants `λ ≤ Λ` for every `z`. Then for every `ℓ ∈ H⁻¹(Ω)` and every `g ∈ H¹(Ω)` there is
`u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` solving

`∫_Ω A(x, u(x)) ∇u · ∇w = ℓ(w)` for every `w ∈ H¹₀(Ω)`,

that is, `-div(A(x, u) ∇u) = ℓ` in `Ω` with `u = g` on `∂Ω` in the weak sense, and
`‖u - g‖ ≤ 2 (4R² + 1) (‖ℓ‖ + Λ ‖g‖) / λ`.

No regularity of `∂Ω` and no Lipschitz condition in `z` is assumed, and uniqueness is not
claimed. -/
theorem exists_sub_mem_w1p0Submodule_forall_energyFormH1_apply_value_eq_of_subset_ball
    (hA : ∀ z, UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
      (fun x => A x z) lam Lam)
    (hAm : ∀ z, AEStronglyMeasurable (fun x => A x z)
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hAc : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      Continuous (A x))
    {z₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z₀ R)
    (ℓ : StrongDual ℝ (W1p0 volume Omega 2)) (g : W1p volume Omega 2) :
    ∃ u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
      (∀ w : W1p0 volume Omega 2,
        energyFormH1 (fun x => A x (W1p.value u x)) 0 0 u (w : W1p volume Omega 2) = ℓ w) ∧
      ‖u - g‖ ≤ 2 * ((2 * R) ^ 2 + 1) * (‖ℓ‖ + Lam * ‖g‖) / lam := by
  have hOmega : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    Metric.isBounded_ball.subset hball
  -- Freeze the coefficient at `v ∈ L²(Ω)` and solve the linear problem by Lax--Milgram.
  choose S hSg hS using
    exists_sub_mem_w1p0Submodule_forall_energyFormH1_apply_eq (A := A) hA hAm hAc hball ℓ g
  have hfix := exists_value_eq_of_forall_energyFormH1_apply_eq (n := n) (Omega := Omega)
    (A := A) (lam := lam) (Lam := Lam) (ℓ := ℓ) (g := g) (S := S) hA hAm hAc hOmega hSg hS
  obtain ⟨v, hv⟩ := hfix
  refine ⟨S v, hSg v, fun w => ?_,
    norm_sub_le_of_forall_energyFormH1_apply_eq (A := A) hA hAm hAc hball v (hSg v) (hS v)⟩
  -- At the fixed point the frozen coefficient is the coefficient of the solution itself.
  have hcoef : (fun x => A x (W1p.value (S v) x)) = fun x => A x (v x) :=
    congrArg (fun f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) =>
      fun x => A x (f x)) hv
  exact (congrArg (fun a => energyFormH1 a 0 0 (S v) (w : W1p volume Omega 2)) hcoef).trans
    (hS v w)

end TauCeti.PDE
