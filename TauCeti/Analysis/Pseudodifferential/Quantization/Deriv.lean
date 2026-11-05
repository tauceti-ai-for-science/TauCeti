/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import TauCeti.Analysis.Pseudodifferential.Quantization.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol

/-!
# Derivatives of the Kohn–Nirenberg quantization

For a symbol `a ∈ S^m_{1,0}` on `ℝⁿ` and a Schwartz function `u`, the quantization

`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ`

(`TauCeti.quantizeSchwartzValue`) is a smooth function of `x`. Differentiating under the integral
sign gives the Leibniz rule

`∂_j (Op(a) u) = Op(∂_{x_j} a) u + Op(a) (∂_j u)`:

the derivative falls either on the position variable of the symbol or, through the phase
`exp(2πi ⟪ζ, x⟫)` and the identity `𝓕 (∂_j u) ζ = 2πi ζ_j 𝓕 u ζ`, on the input. Equivalently, the
commutator `[∂_j, Op(a)]` is the quantization `Op(∂_{x_j} a)` of the spatial derivative. Since
`∂_{x_j} a` is again a symbol of order `m` (`TauCeti.Symbol.spatialDeriv`) and `∂_j u` is again a
Schwartz function, induction on the order of differentiability shows that `Op(a) u` is smooth.

The domination needed to differentiate under the integral sign uses only the local estimates of
`a` and of its first spatial derivatives, so no uniformity in `x` is required for smoothness. For
a uniform symbol the same induction also bounds every derivative of `Op(a) u` on all of `ℝⁿ`.

## Main results

* `TauCeti.differentiable_quantizeSchwartzValue`: `Op(a) u` is differentiable.
* `TauCeti.fderiv_quantizeSchwartzValue_single` and `TauCeti.coordinateDeriv_quantizeSchwartzValue`:
  the Leibniz rule `∂_j (Op(a) u) = Op(∂_{x_j} a) u + Op(a) (∂_j u)`.
* `TauCeti.contDiff_quantizeSchwartzValue`: `Op(a) u` is smooth.
* `TauCeti.Symbol.IsUniform.exists_norm_coordinateDeriv_quantizeSchwartzValue_le`: for a uniform
  symbol, every coordinate derivative of `Op(a) u` is bounded on `ℝⁿ`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ContDiff
open MeasureTheory Real FourierTransform Metric

noncomputable section

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The weight `⟨ξ⟩^t = (1 + ‖ξ‖²)^(t/2)` grows when the exponent grows by one. -/
private theorem rpow_weight_le_add_one (ξ : CoordinateSpace n) (m : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ (m / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ ((m + 1) / 2) :=
  Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)

/-- Multiplying the weight `⟨ξ⟩^m` by `‖ξ‖ ≤ ⟨ξ⟩` raises its exponent by at most one. -/
private theorem norm_mul_rpow_weight_le (ξ : CoordinateSpace n) (m : ℝ) :
    ‖ξ‖ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) ≤ (1 + ‖ξ‖ ^ 2) ^ ((m + 1) / 2) := by
  rw [add_div, Real.rpow_add (by positivity), mul_comm]
  gcongr
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le (by linarith)

namespace Symbol

/-- On a compact set of positions, a symbol of order `m` is bounded by `C ⟨ξ⟩ ^ m`. -/
private theorem exists_norm_coefficient_le (a : Symbol n V W m) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC, h⟩ := a.exists_bound K hK [] []
  exact ⟨C, hC, fun x hx ξ => by simpa using h x hx ξ⟩

/-- On a compact set of positions, the spatial derivative of a symbol of order `m` is bounded by
`C ⟨ξ⟩ ^ m` in operator norm. -/
private theorem exists_norm_fderiv_coefficient_le (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖fderiv ℝ (fun y => a.coefficient (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨D, hD, hDu⟩ :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.exists_opNorm_le (F := V →L[ℂ] W)
  choose C hC h using fun j => (spatialDeriv j a).exists_norm_coefficient_le hK
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => hC j
  refine ⟨D * ∑ j, C j, mul_nonneg hD.le hsum, fun x hx ξ => ?_⟩
  rw [mul_assoc]
  refine hDu (mul_nonneg hsum (by positivity)) fun j => ?_
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have hj : ‖fderiv ℝ (fun y => a.coefficient (y, ξ)) x (EuclideanSpace.single j 1)‖ ≤
      C j * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
    simpa [coordinateDeriv_cons] using h j x hx ξ
  refine hj.trans ?_
  gcongr
  exact Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)

end Symbol

section Derivative

variable (a : Symbol n V W m) (f : 𝓢(CoordinateSpace n, V))

/-- The quantization integrand `x ↦ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (f ζ)` at the frequency `ζ`. -/
private abbrev integrand (x ζ : CoordinateSpace n) : W :=
  𝐞 ⟪ζ, x⟫ • a.coefficient (x, (2 * π) • ζ) (f ζ)

/-- The derivative in the position `x` of the quantization integrand at the frequency `ζ`. -/
private def integrandFDeriv (x ζ : CoordinateSpace n) : CoordinateSpace n →L[ℝ] W :=
  (𝐞 ⟪ζ, x⟫ : ℂ) • ((ContinuousLinearMap.apply ℂ W (f ζ)).restrictScalars ℝ ∘L
      fderiv ℝ (fun y => a.coefficient (y, (2 * π) • ζ)) x) +
    (ContinuousLinearMap.toSpanSingleton ℝ (2 * π * Complex.I * 𝐞 ⟪ζ, x⟫) ∘L
      innerSL ℝ ζ).smulRight (a.coefficient (x, (2 * π) • ζ) (f ζ))

private theorem integrandFDeriv_apply (x ζ y : CoordinateSpace n) :
    integrandFDeriv a f x ζ y =
      𝐞 ⟪ζ, x⟫ • fderiv ℝ (fun y => a.coefficient (y, (2 * π) • ζ)) x y (f ζ) +
        𝐞 ⟪ζ, x⟫ • a.coefficient (x, (2 * π) • ζ) ((2 * π * Complex.I * ⟪ζ, y⟫) • f ζ) := by
  simp only [integrandFDeriv, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    innerSL_apply_apply, Circle.smul_def, map_smul, smul_smul, Complex.real_smul]
  congr 2
  ring

private theorem contDiff_coefficient_left (ξ : CoordinateSpace n) :
    ContDiff ℝ ∞ fun y => a.coefficient (y, ξ) :=
  a.contDiff_coefficient.comp (contDiff_prodMk_left ξ)

private theorem hasFDerivAt_integrand (x ζ : CoordinateSpace n) :
    HasFDerivAt (integrand a f · ζ) (integrandFDeriv a f x ζ) x := by
  have he := (Real.hasDerivAt_fourierChar ⟪ζ, x⟫).hasFDerivAt.comp x (innerSL ℝ ζ).hasFDerivAt
  have ha : HasFDerivAt (fun y => a.coefficient (y, (2 * π) • ζ) (f ζ))
      ((ContinuousLinearMap.apply ℂ W (f ζ)).restrictScalars ℝ ∘L
        fderiv ℝ (fun y => a.coefficient (y, (2 * π) • ζ)) x) x :=
    ((ContinuousLinearMap.apply ℂ W (f ζ)).restrictScalars ℝ).hasFDerivAt.comp x
      ((contDiff_coefficient_left a _).differentiable (by simp) x).hasFDerivAt
  exact (he.smul ha).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => (Circle.smul_def _ _).symm)

private theorem continuous_integrand (x : CoordinateSpace n) : Continuous (integrand a f x) :=
  (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
    ((a.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk (continuous_const_smul _))).clm_apply f.continuous)

private theorem continuous_integrandFDeriv (x : CoordinateSpace n) :
    Continuous (integrandFDeriv a f x) := by
  refine continuous_clm_apply.2 fun y => ?_
  simp only [integrandFDeriv_apply]
  have hphase : Continuous fun ζ : CoordinateSpace n => 𝐞 ⟪ζ, x⟫ :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  have hderiv : Continuous fun ζ : CoordinateSpace n =>
      fderiv ℝ (fun y => a.coefficient (y, (2 * π) • ζ)) x y :=
    ((ContDiff.fderiv (f := fun ζ y => a.coefficient (y, (2 * π) • ζ))
      (a.contDiff_coefficient.comp (contDiff_snd.prodMk (contDiff_fst.const_smul _)))
      contDiff_const (n := 0) (by simp)).continuous).clm_apply continuous_const
  exact (hphase.smul (hderiv.clm_apply f.continuous)).add (hphase.smul
    ((a.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk (continuous_const_smul _))).clm_apply
        ((continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_id.inner continuous_const))).smul f.continuous)))

private theorem norm_integrandFDeriv_le (x ζ : CoordinateSpace n) :
    ‖integrandFDeriv a f x ζ‖ ≤
      (‖fderiv ℝ (fun y => a.coefficient (y, (2 * π) • ζ)) x‖ +
        ‖(2 * π) • ζ‖ * ‖a.coefficient (x, (2 * π) • ζ)‖) * ‖f ζ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [integrandFDeriv_apply]
  refine (norm_add_le _ _).trans ?_
  rw [Circle.norm_smul, Circle.norm_smul]
  have h₁ := ((fderiv ℝ (fun y => a.coefficient (y, (2 * π) • ζ)) x y).le_opNorm (f ζ)).trans
    (mul_le_mul_of_nonneg_right
      ((fderiv ℝ (fun y => a.coefficient (y, (2 * π) • ζ)) x).le_opNorm y) (norm_nonneg _))
  have h₂ : ‖a.coefficient (x, (2 * π) • ζ) ((2 * π * Complex.I * ⟪ζ, y⟫) • f ζ)‖ ≤
      ‖a.coefficient (x, (2 * π) • ζ)‖ * (‖(2 * π) • ζ‖ * ‖y‖ * ‖f ζ‖) := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have hinner : ‖(2 * π * Complex.I * ⟪ζ, y⟫ : ℂ)‖ ≤ ‖(2 * π) • ζ‖ * ‖y‖ := by
      have h := abs_real_inner_le_norm ζ y
      rw [norm_smul, Real.norm_of_nonneg two_pi_pos.le]
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat,
        Real.norm_eq_abs, abs_of_pos pi_pos, mul_one]
      nlinarith [pi_pos]
    rw [norm_smul]
    gcongr
  nlinarith [h₁, h₂, norm_nonneg y, norm_nonneg (f ζ),
    norm_nonneg (a.coefficient (x, (2 * π) • ζ)), norm_nonneg ((2 * π) • ζ)]

/-- Near every point the derivative of the quantization integrand is dominated by an integrable
function of the frequency. -/
private theorem exists_integrable_bound (x₀ : CoordinateSpace n) :
    ∃ b : CoordinateSpace n → ℝ, Integrable b ∧
      ∀ x ∈ closedBall x₀ 1, ∀ ζ, ‖integrandFDeriv a f x ζ‖ ≤ b ζ := by
  obtain ⟨C₀, hC₀, h₀⟩ := a.exists_norm_coefficient_le (isCompact_closedBall x₀ 1)
  obtain ⟨C₁, hC₁, h₁⟩ := a.exists_norm_fderiv_coefficient_le (isCompact_closedBall x₀ 1)
  refine ⟨fun ζ => (C₁ + C₀) * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) * ‖f ζ‖),
    (f.integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) (m + 1)).const_mul _,
    fun x hx ζ => (norm_integrandFDeriv_le a f x ζ).trans ?_⟩
  dsimp only
  rw [← mul_assoc]
  gcongr
  have hw := rpow_weight_le_add_one ((2 * π) • ζ) m
  have hw' := norm_mul_rpow_weight_le ((2 * π) • ζ) m
  have := h₁ x hx ((2 * π) • ζ)
  have := h₀ x hx ((2 * π) • ζ)
  nlinarith [norm_nonneg ((2 * π) • ζ), Real.rpow_nonneg (by positivity :
    (0 : ℝ) ≤ 1 + ‖(2 * π) • ζ‖ ^ 2) (m / 2)]

private theorem integrable_integrandFDeriv (x : CoordinateSpace n) :
    Integrable (integrandFDeriv a f x) := by
  obtain ⟨b, hb, hbound⟩ := exists_integrable_bound a f x
  exact hb.mono' (continuous_integrandFDeriv a f x).aestronglyMeasurable
    (ae_of_all _ (hbound x (mem_closedBall_self zero_le_one)))

private theorem hasFDerivAt_quantizeSchwartzValue (u : 𝓢(CoordinateSpace n, V))
    (x₀ : CoordinateSpace n) :
    HasFDerivAt (quantizeSchwartzValue a.coefficient u)
      (∫ ζ, integrandFDeriv a (𝓕 u) x₀ ζ) x₀ := by
  obtain ⟨b, hb, hbound⟩ := exists_integrable_bound a (𝓕 u) x₀
  obtain ⟨C, -, hC⟩ := a.exists_norm_coefficient_le (isCompact_closedBall x₀ 1)
  have hint : Integrable (integrand a (𝓕 u) x₀) :=
    integrable_quantizeSchwartzValue_integrand
      (a.contDiff_coefficient.continuous.comp (continuous_const.prodMk continuous_id)
        ).aestronglyMeasurable
      (hC x₀ (mem_closedBall_self zero_le_one)) (𝓕 u)
  have hfun : quantizeSchwartzValue a.coefficient u = fun x => ∫ ζ, integrand a (𝓕 u) x ζ :=
    funext (quantizeSchwartzValue_def a.coefficient u)
  rw [hfun]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (closedBall_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (continuous_integrand a (𝓕 u) x).aestronglyMeasurable)
    hint (continuous_integrandFDeriv a (𝓕 u) x₀).aestronglyMeasurable
    (ae_of_all _ fun ζ x hx => hbound x hx ζ) hb
    (ae_of_all _ fun ζ x _ => hasFDerivAt_integrand a (𝓕 u) x ζ)

/-- The quantization `Op(a) u` of a Schwartz function by a symbol is differentiable. -/
theorem differentiable_quantizeSchwartzValue (u : 𝓢(CoordinateSpace n, V)) :
    Differentiable ℝ (quantizeSchwartzValue a.coefficient u) :=
  fun x => (hasFDerivAt_quantizeSchwartzValue a u x).differentiableAt

/-- **Leibniz rule.** The derivative of `Op(a) u` along the `j`-th coordinate is
`Op(∂_{x_j} a) u + Op(a) (∂_j u)`. -/
theorem fderiv_quantizeSchwartzValue_single (u : 𝓢(CoordinateSpace n, V)) (j : Fin n)
    (x : CoordinateSpace n) :
    fderiv ℝ (quantizeSchwartzValue a.coefficient u) x (EuclideanSpace.single j 1) =
      quantizeSchwartzValue (Symbol.spatialDeriv j a).coefficient u x +
        quantizeSchwartzValue a.coefficient (∂_{EuclideanSpace.single j (1 : ℝ)} u) x := by
  obtain ⟨C, -, hC⟩ := a.exists_norm_coefficient_le (isCompact_closedBall x 1)
  obtain ⟨C', -, hC'⟩ :=
    (Symbol.spatialDeriv j a).exists_norm_coefficient_le (isCompact_closedBall x 1)
  have hmeas (b : Symbol n V W m) :
      AEStronglyMeasurable fun ξ => b.coefficient (x, ξ) :=
    (b.contDiff_coefficient.continuous.comp (continuous_const.prodMk continuous_id)
      ).aestronglyMeasurable
  rw [(hasFDerivAt_quantizeSchwartzValue a u x).fderiv,
    ContinuousLinearMap.integral_apply (integrable_integrandFDeriv a (𝓕 u) x),
    quantizeSchwartzValue_def, quantizeSchwartzValue_def,
    ← integral_add
      (integrable_quantizeSchwartzValue_integrand (hmeas _)
        (hC' x (mem_closedBall_self zero_le_one)) (𝓕 u))
      (integrable_quantizeSchwartzValue_integrand (hmeas _)
        (hC x (mem_closedBall_self zero_le_one)) _)]
  congr 1 with ζ
  rw [integrandFDeriv_apply, SchwartzMap.fourier_lineDerivOp_apply]
  simp [coordinateDeriv_cons]

/-- **Leibniz rule.** The `j`-th coordinate derivative of `Op(a) u` is
`Op(∂_{x_j} a) u + Op(a) (∂_j u)`: the commutator `[∂_j, Op(a)]` is `Op(∂_{x_j} a)`. -/
theorem coordinateDeriv_quantizeSchwartzValue (u : 𝓢(CoordinateSpace n, V)) (j : Fin n) :
    coordinateDeriv [j] (quantizeSchwartzValue a.coefficient u) =
      quantizeSchwartzValue (Symbol.spatialDeriv j a).coefficient u +
        quantizeSchwartzValue a.coefficient (∂_{EuclideanSpace.single j (1 : ℝ)} u) :=
  funext fun x => by
    rw [coordinateDeriv_cons, coordinateDeriv_nil, Pi.add_apply,
      fderiv_quantizeSchwartzValue_single]

/-- **Smoothness.** The quantization `Op(a) u` of a Schwartz function by a symbol is smooth. -/
theorem contDiff_quantizeSchwartzValue (u : 𝓢(CoordinateSpace n, V)) :
    ContDiff ℝ ∞ (quantizeSchwartzValue a.coefficient u) := by
  suffices h : ∀ k : ℕ, ∀ (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)),
      ContDiff ℝ k (quantizeSchwartzValue a.coefficient u) from
    contDiff_infty.2 fun k => h k a u
  intro k
  induction k with
  | zero => exact fun a u => contDiff_zero.2 (differentiable_quantizeSchwartzValue a u).continuous
  | succ k ih =>
    intro a u
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨differentiable_quantizeSchwartzValue a u, by simp, fun y => ?_⟩
    have hy : (fun x => fderiv ℝ (quantizeSchwartzValue a.coefficient u) x y) = fun x =>
        ∑ j, y j • (quantizeSchwartzValue (Symbol.spatialDeriv j a).coefficient u x +
          quantizeSchwartzValue a.coefficient (∂_{EuclideanSpace.single j (1 : ℝ)} u) x) := by
      funext x
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y]
      simp [fderiv_quantizeSchwartzValue_single]
    rw [hy]
    exact ContDiff.sum fun j _ => ((ih _ u).add (ih a _)).const_smul (y j)

end Derivative

/-- For a uniform symbol, every coordinate derivative of `Op(a) u` is bounded on `ℝⁿ`. -/
theorem Symbol.IsUniform.exists_norm_coordinateDeriv_quantizeSchwartzValue_le
    {a : Symbol n V W m} (ha : a.IsUniform) (u : 𝓢(CoordinateSpace n, V)) (α : List (Fin n)) :
    ∃ C, ∀ x, ‖coordinateDeriv α (quantizeSchwartzValue a.coefficient u) x‖ ≤ C := by
  induction α using List.reverseRecOn generalizing a u with
  | nil =>
    obtain ⟨C, -, hC⟩ := Symbol.isUniform_iff.1 ha [] []
    exact ⟨_, fun x => by
      simpa using norm_quantizeSchwartzValue_le (fun ξ => by simpa using hC x ξ) u⟩
  | append_singleton α j ih =>
    obtain ⟨C₁, h₁⟩ := ih (ha.spatialDeriv j) u
    obtain ⟨C₂, h₂⟩ := ih ha (∂_{EuclideanSpace.single j (1 : ℝ)} u)
    refine ⟨C₁ + C₂, fun x => ?_⟩
    rw [coordinateDeriv_append, coordinateDeriv_quantizeSchwartzValue,
      coordinateDeriv_add α (contDiff_infty.1 (contDiff_quantizeSchwartzValue _ _) _)
        (contDiff_infty.1 (contDiff_quantizeSchwartzValue _ _) _)]
    exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))

end TauCeti
