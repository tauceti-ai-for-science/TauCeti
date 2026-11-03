/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.DeRham.Period
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.ContMDiff.Curve
import TauCeti.Geometry.Manifold.DeRham.PathIntegral
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Logarithmic derivatives of circle-valued maps

A differentiable map `u : M → S¹` into the unit circle `S¹ ⊆ ℂ` has the logarithmic derivative
`u⁻¹ du`, a `1`-form with values in `iℝ`. Writing `u⁻¹ du = i a`, the real `1`-form `a` is the
pullback `u^* dθ` of the angular form of the circle; this real form is
`TauCeti.circleLogDeriv u`, so that the de Rham and period theory of real forms applies to it. In
coordinates `a(w) = Im (conj u · du(w))`, while `Re (conj u · du(w)) = 0` because `|u|² = 1`.

The logarithmic derivative takes pointwise products of circle-valued maps to sums of forms,
inverses to negatives and constants to zero, and it takes `exp (i f)` to `df` for a real function
`f`. It is closed, and its periods are integer multiples of `2π`: the integral of `u^* dθ` along a
loop is the integral of `dθ` along the image loop in `S¹`, which lifts along `t ↦ exp (t i)` to a
path in `ℝ` whose endpoints differ by a multiple of `2π`.

Conversely, on a connected manifold every closed smooth real `1`-form `α` whose periods lie in
`2πℤ` is `u^* dθ` for a smooth map `u : M → S¹`, namely `u(y) = exp (i ∫_γ α)` along a smooth curve
`γ` from a base point to `y`, and such a `u` is unique up to a constant phase.

These are the facts about abelian gauge transformations `u : X → U(1)` behind the structure of the
gauge group: such a `u` changes a `U(1)` connection by a multiple of `u⁻¹ du`, a closed imaginary
form with periods in `2πiℤ`, and the constants are exactly the gauge transformations with
`u⁻¹ du = 0` on a connected manifold.

## Main declarations

* `TauCeti.circleLogDeriv u`: the real form `u^* dθ`, with `u⁻¹ du = i · circleLogDeriv u`
  (`TauCeti.mvfderiv_coe_eq_circleLogDeriv_mul`).
* `TauCeti.circleLogDeriv_apply`: `(u^* dθ)(w) = Im (conj u · du(w))`.
* `TauCeti.mextDeriv_circleLogDeriv`: the logarithmic derivative is closed.
* `TauCeti.circleLogDeriv_mul`, `TauCeti.circleLogDeriv_inv`, `TauCeti.circleLogDeriv_const`,
  `TauCeti.circleLogDeriv_circleExp_comp`: products, inverses, constants and `exp (i f)`.
* `TauCeti.periodHom_circleAngularForm_mem_zmultiples`: the periods of `dθ` lie in `2πℤ`.
* `TauCeti.periodHom_circleLogDeriv_mem_zmultiples`: the periods of `u^* dθ` lie in `2πℤ`.
* `TauCeti.exists_circleLogDeriv_eq_iff`: on a connected manifold, a closed smooth real `1`-form is
  a logarithmic derivative exactly when its periods lie in `2πℤ`.
* `TauCeti.circleLogDeriv_eq_zero_iff`, `TauCeti.exists_eq_mul_of_circleLogDeriv_eq`: on a
  connected manifold, the logarithmic derivative determines the map up to a constant phase.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (the angular form, line
  integrals and closed covector fields).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (the gauge group).
-/

public section

noncomputable section

open Set Filter ComplexConjugate
open scoped Manifold ContDiff Topology Real

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {u v : M → Circle}

/-- The **logarithmic derivative** of a circle-valued map `u : M → S¹`, as a real `1`-form: the
pullback `u^* dθ` of the angular form. For differentiable `u` it is the real form `a` with
`du = i a u`, that is `u⁻¹ du = i a` (`TauCeti.mvfderiv_coe_eq_circleLogDeriv_mul`). -/
def circleLogDeriv (u : M → Circle) : RoughForm I M ℝ 1 :=
  mpullback I (𝓡 1) u circleAngularForm

/-- The logarithmic derivative of `u` is the pullback of the angular form along `u`. -/
theorem circleLogDeriv_def (u : M → Circle) :
    circleLogDeriv (I := I) u = mpullback I (𝓡 1) u circleAngularForm :=
  (rfl)

/-- The inclusion of the circle into `ℂ` is differentiable. -/
private theorem mdifferentiableAt_coe_circle (z : Circle) :
    MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) z :=
  (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero

/-- At a point where `u` is differentiable, `u^* dθ` is the pullback of the plane angular form
`x dy − y dx` along `u`, viewed as a map to `ℂ`. -/
theorem circleLogDeriv_apply_eq_mpullback {x : M} (hu : MDifferentiableAt I (𝓡 1) u x) :
    circleLogDeriv u x = mpullback I 𝓘(ℝ, ℂ) (fun y ↦ (u y : ℂ)) planeAngularForm x := by
  rw [circleLogDeriv_def, circleAngularForm_def]
  exact (mpullback_comp_at hu (mdifferentiableAt_coe_circle _) planeAngularForm).symm

/-- **The logarithmic derivative in coordinates.** At a point where `u` is differentiable,
`(u^* dθ)(v) = Im (conj (u x) · du(v))` for `u` viewed as a map to `ℂ`. -/
theorem circleLogDeriv_apply {x : M} (hu : MDifferentiableAt I (𝓡 1) u x)
    (w : Fin 1 → TangentSpace I x) :
    circleLogDeriv u x w = (conj (u x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x (w 0)).im := by
  rw [circleLogDeriv_apply_eq_mpullback hu, mpullback_apply]
  refine (planeAngularForm_apply _ _).trans ?_
  simp only [← mvfderiv_apply_eq_mfderiv_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The derivative of a circle-valued map is tangent to the circle: `Re (conj (u x) · du(w)) = 0`,
the derivative of `|u|² = 1`. -/
theorem re_conj_mul_mvfderiv_coe {x : M} (hu : MDifferentiableAt I (𝓡 1) u x)
    (w : TangentSpace I x) :
    (conj (u x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x w).re = 0 := by
  -- The range of the derivative of the inclusion `S¹ → ℂ` at `z` is the orthogonal of `z`.
  let z : Metric.sphere (0 : ℂ) 1 := u x
  have hmem := LinearMap.mem_range_self
    (mvfderiv (𝓡 1) (Subtype.val : Metric.sphere (0 : ℂ) 1 → ℂ) z).toLinearMap
    (mfderiv I (𝓡 1) u x w)
  rw [range_mvfderiv_subtypeVal (n := 1) z] at hmem
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, Complex.inner, mul_comm] at hmem
  have hcomp := mvfderiv_comp_apply x (mdifferentiableAt_coe_circle _) hu w
  rw [Function.comp_def] at hcomp
  rw [hcomp]
  -- `z` is `u x`, read as a point of the sphere.
  exact hmem

/-- **`du = i a u`.** At a point where `u` is differentiable, the derivative of `u`, viewed as a map
to `ℂ`, is `du(w) = u x · (a(w) i)` for the logarithmic derivative `a = circleLogDeriv u`. -/
theorem mvfderiv_coe_eq_circleLogDeriv_mul {x : M} (hu : MDifferentiableAt I (𝓡 1) u x)
    (w : TangentSpace I x) :
    mvfderiv I (fun y ↦ (u y : ℂ)) x w =
      (u x : ℂ) * (circleLogDeriv u x (fun _ ↦ w) * Complex.I) := by
  have hu1 : (u x : ℂ) * conj (u x : ℂ) = 1 := by
    rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hlog : conj (u x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x w =
      circleLogDeriv u x (fun _ ↦ w) * Complex.I := by
    apply Complex.ext
    · simpa using re_conj_mul_mvfderiv_coe hu w
    · simp [circleLogDeriv_apply hu]
  rw [← hlog, ← mul_assoc, hu1, one_mul]

/-- Maps that agree near `x` have the same logarithmic derivative at `x`. -/
theorem _root_.Filter.EventuallyEq.circleLogDeriv_eq {x : M} (h : u =ᶠ[𝓝 x] v) :
    circleLogDeriv (I := I) u x = circleLogDeriv v x :=
  h.mpullback_eq _

/-- A constant map has zero logarithmic derivative. -/
@[simp]
theorem circleLogDeriv_const (c : Circle) : circleLogDeriv (I := I) (fun _ : M ↦ c) = 0 := by
  funext x
  ext w
  simp only [circleLogDeriv_def, mpullback_apply, mfderiv_const, zero_apply]
  exact (circleAngularForm c).map_zero

/-- The constant map `1` has zero logarithmic derivative. -/
@[simp]
theorem circleLogDeriv_one : circleLogDeriv (I := I) (1 : M → Circle) = 0 :=
  circleLogDeriv_const 1

/-- The logarithmic derivative of a `C^(n+1)` circle-valued map is a `C^n` form. -/
theorem isSmoothForm_circleLogDeriv [IsManifold I 1 M] {n : ℕ∞}
    (hu : ContMDiff I (𝓡 1) (n + 1) u) :
    IsSmoothForm I n (circleLogDeriv u) :=
  (isSmoothForm_circleAngularForm.of_le (by exact_mod_cast le_top)).mpullback hu

/-- **The logarithmic derivative is closed**: `d (u^* dθ) = u^* (d dθ) = 0` for a `C²` map `u`. -/
theorem mextDeriv_circleLogDeriv [IsManifold I 2 M] (hu : ContMDiff I (𝓡 1) 2 u) :
    mextDeriv (circleLogDeriv (I := I) u) = 0 := by
  rw [circleLogDeriv_def, ← mpullback_mextDeriv hu ((isSmoothBundleForm_def _ _).mpr
    (isSmoothForm_circleAngularForm.of_le (by exact_mod_cast le_top)).contMDiff),
    mextDeriv_circleAngularForm, mpullback_zero]

/-- **The logarithmic derivative is a homomorphism**: `d log (u v) = d log u + d log v`. -/
theorem circleLogDeriv_mul (hu : ContMDiff I (𝓡 1) 1 u) (hv : ContMDiff I (𝓡 1) 1 v) :
    circleLogDeriv (I := I) (u * v) = circleLogDeriv u + circleLogDeriv v := by
  funext x
  ext w
  have hu' := hu.mdifferentiableAt (x := x) one_ne_zero
  have hv' := hv.mdifferentiableAt (x := x) one_ne_zero
  have huv' := (hu.mul hv).mdifferentiableAt (x := x) one_ne_zero
  have hcu : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (u y : ℂ)) x :=
    (mdifferentiableAt_coe_circle _).comp x hu'
  have hcv : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (v y : ℂ)) x :=
    (mdifferentiableAt_coe_circle _).comp x hv'
  -- the product rule for `u v` viewed as a map to `ℂ`
  have hd : mvfderiv I (fun y ↦ ((u * v) y : ℂ)) x (w 0) =
      (u x : ℂ) * mvfderiv I (fun y ↦ (v y : ℂ)) x (w 0) +
        (v x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x (w 0) := by
    have h := (hcu.hasMFDerivAt.mul hcv.hasMFDerivAt).mfderiv
    simp only [mvfderiv_apply_eq_mfderiv_apply]
    exact congrArg (· (w 0)) h
  have hu1 : conj (u x : ℂ) * u x = 1 := by
    rw [mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hv1 : conj (v x : ℂ) * v x = 1 := by
    rw [mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, circleLogDeriv_apply huv',
    circleLogDeriv_apply hu', circleLogDeriv_apply hv', hd, ← Complex.add_im]
  congr 1
  simp only [Pi.mul_apply, Circle.coe_mul, map_mul]
  linear_combination (conj (v x : ℂ) * mvfderiv I (fun y ↦ (v y : ℂ)) x (w 0)) * hu1 +
    (conj (u x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x (w 0)) * hv1

/-- The logarithmic derivative of `u⁻¹` is minus that of `u`. -/
theorem circleLogDeriv_inv (hu : ContMDiff I (𝓡 1) 1 u) :
    circleLogDeriv (I := I) u⁻¹ = -circleLogDeriv u := by
  have h := circleLogDeriv_mul (v := u⁻¹) hu hu.inv
  rw [mul_inv_cancel, circleLogDeriv_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- **The logarithmic derivative of `exp (i t)`**: on the real line, `(exp (i ·))^* dθ = dt`. -/
theorem circleLogDeriv_circleExp :
    circleLogDeriv (I := 𝓘(ℝ)) Circle.exp = mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id) := by
  funext t
  refine ContinuousAlternatingMap.ext fun w ↦ ?_
  have hd : HasDerivAt (fun s : ℝ ↦ (Circle.exp s : ℂ)) (Circle.exp t * Complex.I) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
  have he : conj (Circle.exp t : ℂ) * Circle.exp t = 1 := by
    rw [mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  rw [circleLogDeriv_apply ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero),
    mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_eq_fderiv,
    mvfderiv_eq_fderiv, hd.hasFDerivAt.fderiv, fderiv_id]
  have key (r : ℝ) : (conj (Circle.exp t : ℂ) * (r • ((Circle.exp t : ℂ) * Complex.I))).im = r := by
    rw [Complex.real_smul, show conj (Circle.exp t : ℂ) * (r * ((Circle.exp t : ℂ) * Complex.I)) =
      r * Complex.I by linear_combination (r * Complex.I) * he]
    simp
  exact key _

/-- **The logarithmic derivative of `exp (i f)`** is `df`: for a differentiable real function `f`,
`(exp (i f))^* dθ = df`. -/
theorem circleLogDeriv_circleExp_comp {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ) f) :
    circleLogDeriv (fun x ↦ Circle.exp (f x)) = mextDeriv (RoughForm.ofFunction I f) := by
  funext x
  rw [show (fun x ↦ Circle.exp (f x)) = Circle.exp ∘ f from rfl, circleLogDeriv_def,
    mpullback_comp_at (hf x) ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero),
    ← circleLogDeriv_def, circleLogDeriv_circleExp,
    mpullback_mextDeriv_ofFunction_apply (hf x) mdifferentiableAt_id]
  rfl

section Periods

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- **The periods of the angular form are multiples of `2π`.** -/
theorem periodHom_circleAngularForm_mem_zmultiples (z : Circle)
    (γ : Additive (FundamentalGroup Circle z)) :
    periodHom circleAngularForm z γ ∈ AddSubgroup.zmultiples (2 * π) := by
  obtain ⟨t₀, rfl⟩ := Circle.exp_surjective z
  rw [periodHom_apply]
  generalize (Additive.toMul γ).toPath = q
  induction q with | mk p =>
  -- Lift the loop `p` along `t ↦ exp (t i)` to a path `Γ` in `ℝ` starting at `t₀`. As `dθ` pulls
  -- back to `dt`, the period is `Γ 1 - t₀`, a multiple of `2π` since `exp (Γ 1 i) = exp (t₀ i)`.
  obtain ⟨Γ, hΓp, hΓ0⟩ :=
    Circle.isCoveringMap_exp.exists_path_lifts p.toContinuousMap t₀ p.source
  have hΓ (t : unitInterval) : Circle.exp (Γ t) = p t := congrFun hΓp t
  let Γ' : Path t₀ (Γ 1) := ⟨Γ, hΓ0, rfl⟩
  have hs : Circle.exp t₀ = Circle.exp (Γ 1) := by rw [hΓ 1, p.target]
  have hpΓ : p = (Γ'.map (contMDiff_circleExp (m := 2)).continuous).cast rfl hs :=
    Path.ext (funext fun t ↦ (hΓ t).symm)
  rw [hpΓ, Path.Homotopic.Quotient.mk_cast, pathClassIntegral_cast,
    Path.Homotopic.Quotient.mk_map (f := ⟨_, (contMDiff_circleExp (m := 2)).continuous⟩),
    ← pathClassIntegral_mpullback contMDiff_circleExp
      (isSmoothForm_circleAngularForm.of_le (by exact_mod_cast le_top)) mextDeriv_circleAngularForm,
    ← circleLogDeriv_def, circleLogDeriv_circleExp,
    pathClassIntegral_mextDeriv_ofFunction contMDiff_id]
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hs.symm
  exact ⟨m, by simp [hm]⟩

/-- **The periods of a logarithmic derivative are multiples of `2π`**: for a `C²` map
`u : M → S¹`, the integral of `u^* dθ` around every loop is `2π` times an integer, the degree of
`u` along the loop. -/
theorem periodHom_circleLogDeriv_mem_zmultiples (hu : ContMDiff I (𝓡 1) 2 u) (x : M)
    (γ : Additive (FundamentalGroup M x)) :
    periodHom (circleLogDeriv (I := I) u) x γ ∈ AddSubgroup.zmultiples (2 * π) := by
  rw [circleLogDeriv_def, periodHom_mpullback hu
    (isSmoothForm_circleAngularForm.of_le (by exact_mod_cast le_top)) mextDeriv_circleAngularForm]
  exact periodHom_circleAngularForm_mem_zmultiples _ _

/-- **Closed forms with periods in `2πℤ` are logarithmic derivatives.** On a connected manifold, a
closed smooth real `1`-form `α` is `u^* dθ` for a smooth map `u : M → S¹` exactly when all its
periods at a base point `x₀` are multiples of `2π`. -/
theorem exists_circleLogDeriv_eq_iff [PreconnectedSpace M] {α : RoughForm I M ℝ 1}
    (hα : IsSmoothForm I ∞ α) (hclosed : mextDeriv α = 0) (x₀ : M) :
    (∃ u : M → Circle, ContMDiff I (𝓡 1) ∞ u ∧ circleLogDeriv u = α) ↔
      ∀ γ : Additive (FundamentalGroup M x₀),
        periodHom α x₀ γ ∈ AddSubgroup.zmultiples (2 * π) := by
  refine ⟨fun ⟨u, hu, hα⟩ ↦ hα ▸ periodHom_circleLogDeriv_mem_zmultiples
    (hu.of_le (by norm_num)) x₀, fun hper ↦ ?_⟩
  -- The map is `u y = exp (i ∫_γ α)` along a smooth curve `γ` from `x₀` to `y`. It does not
  -- depend on `γ`, since loop integrals lie in `2πℤ`, and near each point it is `exp (i g)` for a
  -- local primitive `g` of `α`.
  have hα₀ : IsSmoothForm I 0 α := hα.of_le (by simp)
  -- the integral of `α` along every smooth loop at `x₀` is a multiple of `2π`
  have hloop (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (hc₀ : c 0 = x₀) (hc₁ : c 1 = x₀) :
      pathIntegral α c 0 1 ∈ AddSubgroup.zmultiples (2 * π) := by
    let γ : Path x₀ x₀ := ⟨⟨fun t ↦ c t, hc.continuous.comp continuous_subtype_val⟩, hc₀, hc₁⟩
    rw [← periodHom_ofMul_eq_pathIntegral (hα.of_le (by simp)) hclosed (hc.of_le (by simp))
      (γ := γ) fun _ ↦ rfl]
    exact hper _
  -- `f y` is the integral of `α` along a chosen smooth curve from `x₀` to `y`
  choose γ hγ hγ₀ hγ₁ using fun y : M ↦ exists_contMDiff_curve (I := I) (n := ⊤) x₀ y
  set f : M → ℝ := fun y ↦ pathIntegral α (γ y) 0 1 with hf_def
  -- near each point, `exp (i f)` is `exp (i g)` for a local primitive `g` of `α`
  have hloc (x : M) : ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ g ∧
      mextDeriv (RoughForm.ofFunction I g) x = α x ∧
      (fun y ↦ Circle.exp (f y)) =ᶠ[𝓝 x] fun y ↦ Circle.exp (g y) := by
    obtain ⟨U, hU, ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_nhds (r := ⊤) le_top hα (x := x)
      (Eventually.of_forall fun y ↦ congrFun hclosed y)
    have hψ' := hψ
    rw [RoughForm.eq_ofFunction ψ, isSmoothForm_ofFunction_iff] at hψ'
    refine ⟨fun y ↦ ψ y 0 + (f x - ψ x 0), hψ'.add contMDiff_const, ?_, ?_⟩
    · rw [mextDeriv_ofFunction_eq_of_eventuallyEq_add_const (hψ'.mdifferentiableAt (by simp))
        (Eventually.of_forall fun _ ↦ rfl), ← RoughForm.eq_ofFunction]
      exact hdψ x (mem_of_mem_nhds hU)
    · filter_upwards [eventually_exists_contMDiff_curve (I := I) (n := ⊤) hU] with y hy
      obtain ⟨c, hc, hc₀, hc₁, hcU⟩ := hy
      have hc' : ContMDiff 𝓘(ℝ, ℝ) I 1 c := hc.of_le (by simp)
      -- compare the chosen curve to `y` with the chosen curve to `x` followed by `c`
      have hcat := pathIntegral_sub_mem_of_forall_pathIntegral_mem hα₀ hloop (hγ y) (hγ₀ y)
        (hγ₁ y) ((hγ x).curveConcat hc (hγ₁ x) hc₀)
        (fun t ht ↦ by rw [curveConcat_of_le (by linarith), hγ₀ x _ (by linarith)])
        (fun t ht ↦ by rw [curveConcat_of_lt (by linarith), hc₁ _ (by linarith)])
      rw [pathIntegral_curveConcat hα₀ ((hγ x).of_le (by simp)) hc' (hγ₁ x) hc₀,
        pathIntegral_congr (ψ := mextDeriv ψ) fun t _ ↦ (hdψ _ (hcU t)).symm,
        pathIntegral_mextDeriv (hψ.of_le (by simp)) hc', hc₁ 1 le_rfl, hc₀ 0 le_rfl] at hcat
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hcat
      refine Circle.exp_eq_exp.mpr ⟨m, ?_⟩
      rw [zsmul_eq_mul] at hm
      linarith
  refine ⟨fun y ↦ Circle.exp (f y), fun x ↦ ?_, funext fun x ↦ ?_⟩
  · obtain ⟨g, hg, -, hev⟩ := hloc x
    exact ((contMDiff_circleExp.comp hg) x).congr_of_eventuallyEq hev
  · obtain ⟨g, hg, hdg, hev⟩ := hloc x
    rw [hev.circleLogDeriv_eq, circleLogDeriv_circleExp_comp (hg.mdifferentiable (by simp)), hdg]

end Periods

/-- **Uniqueness up to a constant.** On a connected manifold, a differentiable map `u : M → S¹`
has zero logarithmic derivative exactly when it is constant. -/
theorem circleLogDeriv_eq_zero_iff [IsManifold I 1 M] [PreconnectedSpace M]
    (hu : MDifferentiable I (𝓡 1) u) : circleLogDeriv (I := I) u = 0 ↔ ∃ c, u = fun _ ↦ c := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ hc ▸ circleLogDeriv_const c⟩
  have hcu : MDifferentiable I 𝓘(ℝ, ℂ) (fun y ↦ (u y : ℂ)) :=
    fun x ↦ (mdifferentiableAt_coe_circle _).comp x (hu x)
  -- `du = i (d log u) u` vanishes
  have hzero (x : M) : mfderiv I 𝓘(ℝ, ℂ) (fun y ↦ (u y : ℂ)) x = 0 := by
    refine ContinuousLinearMap.ext fun w ↦ ?_
    have hw := mvfderiv_coe_eq_circleLogDeriv_mul (hu x) w
    rw [h, mvfderiv_apply_eq_mfderiv_apply] at hw
    rw [hw, zero_apply]
    simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Complex.ofReal_zero, zero_mul,
      mul_zero]
    -- the zero of `TangentSpace 𝓘(ℝ, ℂ) (u x)` is the zero of `ℂ`
    rfl
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, funext fun x ↦ (IsEmpty.false x).elim⟩
  · exact ⟨u x₀, funext fun y ↦ Circle.ext (hcu.apply_eq_of_mfderiv_eq_zero hzero y x₀)⟩

/-- **Uniqueness up to a constant.** On a connected manifold, two `C¹` maps `u v : M → S¹` with the
same logarithmic derivative differ by a constant phase: `u = c v`. -/
theorem exists_eq_mul_of_circleLogDeriv_eq [IsManifold I 1 M] [PreconnectedSpace M]
    (hu : ContMDiff I (𝓡 1) 1 u) (hv : ContMDiff I (𝓡 1) 1 v)
    (h : circleLogDeriv (I := I) u = circleLogDeriv v) : ∃ c : Circle, ∀ x, u x = c * v x := by
  have hw : circleLogDeriv (I := I) (u * v⁻¹) = 0 := by
    rw [circleLogDeriv_mul (v := v⁻¹) hu hv.inv, circleLogDeriv_inv hv, h, add_neg_cancel]
  obtain ⟨c, hc⟩ :=
    (circleLogDeriv_eq_zero_iff ((hu.mul hv.inv).mdifferentiable one_ne_zero)).mp hw
  refine ⟨c, fun x ↦ ?_⟩
  rw [← congrFun hc x, Pi.mul_apply, inv_mul_cancel_right]

end TauCeti
