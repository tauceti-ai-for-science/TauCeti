/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.Order
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import TauCeti.Analysis.Fourier.Convolution
import TauCeti.Analysis.PositiveDefinite.FourierAtom
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Localizing the cutoff of a microlocally smooth distribution

A complex distribution `T` is microlocally smooth at `(x, ξ)` if, for *some* cutoff `φ` with
`φ x ≠ 0`, the localized Fourier transform `localFourier T φ`, the Fourier transform of `φ T`,
decays rapidly in an open cone around `ξ`. This file shows that the cutoff can be changed: the
decay survives multiplying `φ` by any Schwartz function, at the price of shrinking the cone
(Hörmander, Lemma 8.1.1). This is what makes the wave front set a local, additive notion.

The mechanism is the identity `𝓕 (ψ u) = 𝓕 ψ ⋆ 𝓕 u` for the compactly supported distribution
`u = φ T`. The localized Fourier transform grows at most polynomially, by the finite order of `T`
on the support of `φ`. Near a frequency `η` deep inside the cone, the convolution sees only
frequencies `η - ζ` still in the cone, where `localFourier T φ` decays; the remaining frequencies
`ζ` are large compared to `η`, where `𝓕 ψ ζ` decays faster than any polynomial.

## Main results

* `Distribution.exists_norm_localFourier_le`: `localFourier T φ` grows at most polynomially.
* `Distribution.localFourier_mul_eq_integral`: for a Schwartz function `ψ`,
  `localFourier T (φ ψ) η = ∫ ζ, 𝓕 ψ ζ * localFourier T φ (η - ζ)`.
* `Distribution.exists_isOpen_cone_decay_localFourier_mul`: rapid decay of `localFourier T φ` in
  an open cone `Γ` gives rapid decay of `localFourier T (φ ψ)` in an open cone `Γ' ⊆ Γ` around
  any given direction of `Γ`.
* `Distribution.IsMicrolocallySmoothAt.exists_tsupport_subset`: microlocal smoothness is witnessed
  by cutoffs supported in any neighbourhood of the point.
* `Distribution.IsMicrolocallySmoothAt.add`, `Distribution.waveFrontSet_add_subset`: the wave front
  set of a sum lies in the union of the wave front sets.

## Implementation notes

The convolution identity is proved by regularization. For a normalized bump `ρ`, the integral of
a complex test function `F` against the regularization `y ↦ T (ρ (· - y))` is the pairing of `T`
with the mollification of `F` (`Distribution.apply_eq_integral_smul_translatePairing`). For the
regularizations the identity is the convolution theorem
`Real.fourier_fourierInv_smul_eq_convolution`, and shrinking bumps recover `T`
(`TestFunction.tendsto_mollify`). The limit is taken by dominated convergence, using a bound on
the regularized transforms which is polynomial in the frequency and uniform in the bump.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.1: Lemma 8.1.1
  and its proof, and Definition 8.1.2.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction MeasureTheory Metric
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff Convolution
  Pointwise SchwartzMap

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-! ### Polynomial growth of the localized Fourier transform -/

/-- The derivatives of the modulated cutoff `x ↦ φ x * 𝐞 (-⟪x, η⟫)` of order at most `N` grow at
most like `(1 + ‖η‖) ^ N`. -/
private theorem exists_norm_iteratedFDeriv_mul_fourierAtom_le (φ : 𝓓(Ω, ℂ)) (N : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ η, ∀ i ≤ N, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => φ y * TauCeti.fourierAtom η y) x‖ ≤
        A * (1 + ‖η‖) ^ N := by
  obtain ⟨B, hB, hφ⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff N
  refine ⟨2 ^ N * B * (2 * Real.pi) ^ N, by positivity, fun η i hi x => ?_⟩
  -- Each derivative of the Fourier atom of order at most `N` is at most `a ^ N`.
  set a := 2 * Real.pi * (1 + ‖η‖)
  have ha : 1 ≤ a := by
    have : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    nlinarith [norm_nonneg η]
  have hatom (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j (TauCeti.fourierAtom η) x‖ ≤ a ^ N :=
    (TauCeti.norm_iteratedFDeriv_fourierAtom_le η x j).trans <|
      (pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) j).trans
        (pow_le_pow_right₀ ha hj)
  calc ‖iteratedFDeriv ℝ i (fun y => φ y * TauCeti.fourierAtom η y) x‖
      ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
          ‖iteratedFDeriv ℝ k φ x‖ * ‖iteratedFDeriv ℝ (i - k) (TauCeti.fourierAtom η) x‖ :=
        norm_iteratedFDeriv_mul_le φ.contDiff (TauCeti.contDiff_fourierAtom η) x
          (by exact_mod_cast le_top)
    _ ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * B * a ^ N := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        gcongr
        · exact hφ k (hk'.trans hi) x
        · exact hatom (i - k) ((Nat.sub_le i k).trans hi)
    _ = 2 ^ i * B * a ^ N := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ) * B * a ^ N) (Nat.sum_range_choose i)
    _ ≤ 2 ^ N * B * a ^ N := by
        gcongr
        · norm_num
    _ = 2 ^ N * B * (2 * Real.pi) ^ N * (1 + ‖η‖) ^ N := by
        rw [mul_pow]
        ring

/-- **The localized Fourier transform grows at most polynomially.** For a complex distribution
`T` and a cutoff `φ` there are an exponent `N` and a constant `C` with
`‖localFourier T φ η‖ ≤ C (1 + ‖η‖) ^ N` for every frequency `η`: the order of `T` on the support
of `φ` bounds the growth. -/
theorem exists_norm_localFourier_le (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ η, ‖T.localFourier φ η‖ ≤ C * (1 + ‖η‖) ^ N := by
  let K : Compacts E := ⟨tsupport φ, φ.hasCompactSupport.isCompact⟩
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_complexPairing_le (K := K) φ.tsupport_subset
  obtain ⟨A, hA, hφ⟩ := exists_norm_iteratedFDeriv_mul_fourierAtom_le φ N
  refine ⟨N, C * A, by positivity, fun η => ?_⟩
  rw [T.localFourier_eq φ (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (TauCeti.contDiff_fourierAtom η) φ) fun x => ?_, mul_assoc]
  swap
  · simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]
  refine hT _ ?_ _ (by positivity) fun i hi x => ?_
  · rw [bilinLeftCLM_apply]
    exact tsupport_mul_subset_left (f := φ)
  · simpa [bilinLeftCLM_apply] using hφ η i hi x

/-! ### Shrinking the cone -/

/-- Inside an open cone `Γ` containing `ξ` there are a smaller open cone `Γ'` containing `ξ` and
a constant `0 < c ≤ 1/2` such that `η - ζ ∈ Γ` whenever `η ∈ Γ'` and `‖ζ‖ ≤ c ‖η‖`. -/
private theorem exists_cone_sub_mem {Γ : Set E} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {ξ : E} (hξ : ξ ∈ Γ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∃ Γ' ⊆ Γ, IsOpen Γ' ∧ ξ ∈ Γ' ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') ∧
      ∀ η ∈ Γ', ∀ ζ : E, ‖ζ‖ ≤ c * ‖η‖ → η - ζ ∈ Γ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hΓ ξ hξ
  have hden : 0 < 4 * ‖ξ‖ + 2 * δ := by positivity
  set c := δ / (4 * ‖ξ‖ + 2 * δ)
  have hc : 0 < c := div_pos hδ hden
  have hc2 : c ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [norm_nonneg ξ]
  have hcξ : c * (‖ξ‖ + δ / 2) = δ / 4 := by
    simp only [c]
    field_simp
    ring
  -- `Γ'` is the union of the positive multiples of the ball of radius `δ / 2` around `ξ`.
  let Γ' : Set E := ⋃ s : Ioi (0 : ℝ), (fun η => (s : ℝ) • η) ⁻¹' ball ξ (δ / 2)
  have hmem {η : E} : η ∈ Γ' ↔ ∃ s : ℝ, 0 < s ∧ s • η ∈ ball ξ (δ / 2) := by
    simp [Γ']
  have hback {s : ℝ} (hs : 0 < s) {η : E} (h : s • η ∈ Γ) : η ∈ Γ := by
    simpa [smul_smul, inv_mul_cancel₀ hs.ne'] using hcone s⁻¹ (inv_pos.2 hs) _ h
  refine ⟨c, hc, hc2, Γ', fun η hη => ?_,
    isOpen_iUnion fun s => isOpen_ball.preimage (continuous_const_smul _),
    hmem.2 ⟨1, one_pos, by simpa using half_pos hδ⟩, fun t ht η hη => ?_, fun η hη ζ hζ => ?_⟩
  · obtain ⟨s, hs, hsη⟩ := hmem.1 hη
    exact hback hs (hball (ball_subset_ball (half_le_self hδ.le) hsη))
  · obtain ⟨s, hs, hsη⟩ := hmem.1 hη
    exact hmem.2 ⟨s / t, div_pos hs ht, by rwa [smul_smul, div_mul_cancel₀ s ht.ne']⟩
  · obtain ⟨s, hs, hsη⟩ := hmem.1 hη
    rw [mem_ball, dist_eq_norm] at hsη
    refine hback hs (hball ?_)
    have hy : ‖s • η‖ ≤ ‖ξ‖ + δ / 2 := by
      have := norm_le_insert' (s • η) ξ
      linarith [norm_sub_rev (s • η) ξ]
    have hsζ : ‖s • ζ‖ ≤ δ / 4 := by
      calc ‖s • ζ‖ = s * ‖ζ‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
        _ ≤ s * (c * ‖η‖) := by gcongr
        _ = c * ‖s • η‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]; ring
        _ ≤ c * (‖ξ‖ + δ / 2) := by gcongr
        _ = δ / 4 := hcξ
    rw [mem_ball, dist_eq_norm]
    calc ‖s • (η - ζ) - ξ‖ = ‖(s • η - ξ) - s • ζ‖ := by rw [smul_sub]; congr 1; abel
      _ ≤ ‖s • η - ξ‖ + ‖s • ζ‖ := norm_sub_le _ _
      _ < δ := by linarith

omit [InnerProductSpace ℝ E] in
/-- The pointwise estimate behind `exists_isOpen_cone_decay_localFourier_mul`. Let `v` grow at
most like `C₀ (1 + ‖θ‖) ^ M` and satisfy `(1 + ‖θ‖) ^ N ‖v θ‖ ≤ C₁` on `Γ`, and let `η - ζ ∈ Γ`
whenever `η ∈ Γ'` and `‖ζ‖ ≤ c ‖η‖`. Then for `η ∈ Γ'` the weight `(1 + ‖η‖) ^ N` is transferred
from `v (η - ζ)` to a polynomial in `‖ζ‖`. -/
private theorem one_add_norm_pow_mul_norm_le {v : E → ℂ} {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) (hsub : ∀ η ∈ Γ', ∀ ζ : E, ‖ζ‖ ≤ c * ‖η‖ → η - ζ ∈ Γ) {N M : ℕ}
    {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hpoly : ∀ θ, ‖v θ‖ ≤ C₀ * (1 + ‖θ‖) ^ M)
    (hdecay : ∀ θ ∈ Γ, (1 + ‖θ‖) ^ N * ‖v θ‖ ≤ C₁) {η : E} (hη : η ∈ Γ') (ζ : E) :
    (1 + ‖η‖) ^ N * ‖v (η - ζ)‖ ≤
      2 ^ N * max C₁ 0 + C₀ * c⁻¹ ^ (N + M) * (1 + ‖ζ‖) ^ (N + 2 * M) := by
  by_cases hζ : ‖ζ‖ ≤ c * ‖η‖
  · -- For small `ζ` the frequency `η - ζ` lies in `Γ`, and `1 + ‖η‖ ≤ 2 (1 + ‖η - ζ‖)`.
    have h1 : 1 + ‖η‖ ≤ 2 * (1 + ‖η - ζ‖) := by
      have := norm_sub_norm_le η ζ
      nlinarith [norm_nonneg ζ, norm_nonneg η]
    calc (1 + ‖η‖) ^ N * ‖v (η - ζ)‖ ≤ (2 * (1 + ‖η - ζ‖)) ^ N * ‖v (η - ζ)‖ := by gcongr
      _ = 2 ^ N * ((1 + ‖η - ζ‖) ^ N * ‖v (η - ζ)‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ N * max C₁ 0 := by
          gcongr
          exact (hdecay _ (hsub η hη ζ hζ)).trans (le_max_left _ _)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · -- For large `ζ`, `1 + ‖η‖ ≤ c⁻¹ (1 + ‖ζ‖)` absorbs the weight and the growth of `v`.
    replace hζ := not_le.1 hζ
    have h1 : 1 + ‖η‖ ≤ c⁻¹ * (1 + ‖ζ‖) := by
      rw [le_inv_mul_iff₀ hc]
      nlinarith
    have hw : 1 + ‖η - ζ‖ ≤ (1 + ‖η‖) * (1 + ‖ζ‖) := by
      simpa [sub_eq_add_neg] using TauCeti.one_add_norm_add_le η (-ζ)
    calc (1 + ‖η‖) ^ N * ‖v (η - ζ)‖
        ≤ (1 + ‖η‖) ^ N * (C₀ * ((1 + ‖η‖) * (1 + ‖ζ‖)) ^ M) := by
          gcongr
          exact (hpoly _).trans (by gcongr)
      _ = C₀ * (1 + ‖η‖) ^ (N + M) * (1 + ‖ζ‖) ^ M := by rw [mul_pow, pow_add]; ring
      _ ≤ C₀ * (c⁻¹ * (1 + ‖ζ‖)) ^ (N + M) * (1 + ‖ζ‖) ^ M := by gcongr
      _ = C₀ * c⁻¹ ^ (N + M) * (1 + ‖ζ‖) ^ (N + 2 * M) := by
          rw [mul_pow, show N + 2 * M = N + M + M by ring, pow_add (1 + ‖ζ‖) (N + M) M]
          ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

variable [FiniteDimensional ℝ E]

/-! ### Approximation by regularizations

The pairing of `T` with a complex test function `F` is approximated by the integrals of `F`
against the smooth regularizations `y ↦ T (ρ (· - y))` of `T` by shrinking normalized bumps `ρ`.
On the regularizations, Fourier analysis is ordinary integration. -/

section Regularization

variable [MeasurableSpace E] [BorelSpace E]

/-- A normalized bump, as a test function on the whole space. -/
private def normedBump (b : ContDiffBump (0 : E)) : 𝓓((⊤ : Opens E), ℝ) :=
  ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, by simp⟩

private theorem coe_normedBump (b : ContDiffBump (0 : E)) :
    ⇑(normedBump b) = b.normed volume :=
  rfl

/-- A regularization of `T` by a normalized bump is continuous on every set whose enlargement by
the support of the bump stays in `Ω`. -/
private theorem continuousOn_translatePairing_normedBump (T : 𝓓'(Ω, ℂ)) {S : Set E}
    (b : ContDiffBump (0 : E)) (hb : closedBall (0 : E) b.rOut + S ⊆ Ω) :
    ContinuousOn (T.translatePairing (normedBump b)) S :=
  (T.contDiffOn_translatePairing _).continuousOn.mono fun y hy z hz =>
    hb ⟨z, by simpa [coe_normedBump, b.tsupport_normed_eq] using hz, y, hy, rfl⟩

/-- A continuous function vanishing outside a compact set `S` is integrable against a
regularization of `T` which is continuous on `S`. -/
private theorem integrable_mul_translatePairing (T : 𝓓'(Ω, ℂ)) {S : Set E} (hS : IsCompact S)
    (b : ContDiffBump (0 : E)) (hb : closedBall (0 : E) b.rOut + S ⊆ Ω) {k : E → ℂ}
    (hk : Continuous k) (hkS : ∀ y ∉ S, k y = 0) :
    Integrable (fun y => k y * T.translatePairing (normedBump b) y) :=
  ((hk.continuousOn.mul (continuousOn_translatePairing_normedBump T b hb)).integrableOn_compact
    hS).integrable_of_forall_notMem_eq_zero fun y hy => by simp [hkS y hy]

/-- Pairing a distribution with a mollified test function is integrating the test function
against the regularization of the distribution. -/
private theorem apply_mollify_eq_integral (T : 𝓓'(Ω, ℂ)) (f : 𝓓(Ω, ℝ)) (b : ContDiffBump (0 : E))
    (hb : closedBall (0 : E) b.rOut + tsupport f ⊆ Ω) :
    T (mollify f volume b hb) = ∫ y, f y • T.translatePairing (normedBump b) y := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext
    simp
  refine T.apply_eq_integral_smul_translatePairing (normedBump b)
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) f.hasCompactSupport
    (fun y hy z hz => hb ⟨z, by simpa [coe_normedBump, b.tsupport_normed_eq] using hz, y, hy, rfl⟩)
    ?_
  rw [coe_mollify, coe_normedBump]
  conv_lhs => rw [← hflip]
  exact convolution_flip _

/-- The pairings of `T` with the mollified real and imaginary parts of `F` combine to the integral
of `F` against the regularization of `T`. -/
private theorem apply_mollify_re_add_im_eq_integral (T : 𝓓'(Ω, ℂ)) (F : 𝓓(Ω, ℂ))
    (b : ContDiffBump (0 : E)) (hb : closedBall (0 : E) b.rOut + tsupport F ⊆ Ω) :
    T (mollify (postcompCLM (𝕜 := ℝ) reCLM F) volume b
        ((add_subset_add_left (tsupport_postcompCLM_subset _ F)).trans hb)) +
      I * T (mollify (postcompCLM (𝕜 := ℝ) imCLM F) volume b
        ((add_subset_add_left (tsupport_postcompCLM_subset _ F)).trans hb)) =
      ∫ y, F y * T.translatePairing (normedBump b) y := by
  have hint (L : ℂ →L[ℝ] ℝ) :
      Integrable fun y => postcompCLM (𝕜 := ℝ) L F y • T.translatePairing (normedBump b) y := by
    refine (integrable_mul_translatePairing T F.hasCompactSupport.isCompact b hb
      (k := fun y => ((L (F y) : ℝ) : ℂ)) (by fun_prop) fun y hy => ?_).congr
      (Eventually.of_forall fun y => ?_)
    · simp [image_eq_zero_of_notMem_tsupport hy]
    · simp [Complex.real_smul]
  rw [apply_mollify_eq_integral, apply_mollify_eq_integral, ← integral_const_mul,
    ← integral_add (hint reCLM) ((hint imCLM).const_mul I)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [postcompCLM_apply, Function.comp_apply, reCLM_apply, imCLM_apply, Complex.real_smul]
  conv_rhs => rw [← re_add_im (F y)]
  ring

/-- Along shrinking normalized bumps, the integrals of `F` against the regularizations of `T`
converge to the pairing of `T` with `F`. -/
private theorem tendsto_integral_mul_translatePairing (T : 𝓓'(Ω, ℂ)) (F : 𝓓(Ω, ℂ))
    {b : ℕ → ContDiffBump (0 : E)} (hb0 : Tendsto (fun n => (b n).rOut) atTop (𝓝 0))
    (hb : ∀ n, closedBall (0 : E) (b n).rOut + tsupport F ⊆ Ω) :
    Tendsto (fun n => ∫ y, F y * T.translatePairing (normedBump (b n)) y) atTop
      (𝓝 (T.complexPairing F)) := by
  refine Tendsto.congr (fun n => apply_mollify_re_add_im_eq_integral T F (b n) (hb n)) ?_
  rw [complexPairing_apply]
  exact ((T.continuous.tendsto _).comp (tendsto_mollify _ volume hb0 _)).add
    (((T.continuous.tendsto _).comp (tendsto_mollify _ volume hb0 _)).const_mul I)

/-- **Uniform finite order of the regularized pairings.** For a compact `S` whose closed
`δ`-enlargement lies in `Ω`, the integrals of complex test functions `F` supported in `S` against
the regularizations of `T` by bumps of radius at most `δ` are bounded by a fixed multiple of a
bound on the derivatives of `F` up to a fixed order. -/
private theorem exists_norm_integral_mul_translatePairing_le (T : 𝓓'(Ω, ℂ)) {S : Set E}
    (hS : IsCompact S) {δ : ℝ} (hSδ : closedBall (0 : E) δ + S ⊆ Ω) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ F : 𝓓(Ω, ℂ), tsupport F ⊆ S → ∀ b : ContDiffBump (0 : E),
      b.rOut ≤ δ → ∀ M, 0 ≤ M → (∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i F x‖ ≤ M) →
        ‖∫ y, F y * T.translatePairing (normedBump b) y‖ ≤ C * M := by
  let K : Compacts E := ⟨closedBall (0 : E) δ + S, (isCompact_closedBall _ _).add hS⟩
  obtain ⟨N, C, hC, hT⟩ := T.exists_norm_apply_le (K := K) hSδ
  refine ⟨N, 2 * C, by positivity, fun F hF b hbδ M hM hFM => ?_⟩
  have hb : closedBall (0 : E) b.rOut + tsupport F ⊆ Ω :=
    (add_subset_add (closedBall_subset_closedBall hbδ) hF).trans hSδ
  -- The mollified real and imaginary parts are supported in `K` and obey the same bounds.
  have hpart (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
      ‖T (mollify (postcompCLM (𝕜 := ℝ) L F) volume b
        ((add_subset_add_left (tsupport_postcompCLM_subset _ F)).trans hb))‖ ≤ C * M := by
    refine hT _ ?_ M hM fun i hi x => norm_iteratedFDeriv_mollify_le _ volume b _ (fun y => ?_) x
    · rw [coe_mollify]
      exact b.tsupport_normed_convolution_subset.trans
        (add_subset_add (closedBall_subset_closedBall hbδ)
          ((tsupport_postcompCLM_subset L F).trans hF))
    · rw [postcompCLM_apply]
      calc ‖iteratedFDeriv ℝ i (L ∘ F) y‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i F y‖ :=
            L.norm_iteratedFDeriv_comp_left F.contDiff.contDiffAt (by exact_mod_cast le_top)
        _ ≤ 1 * M := mul_le_mul hL (hFM i hi y) (norm_nonneg _) zero_le_one
        _ = M := one_mul M
  rw [← apply_mollify_re_add_im_eq_integral T F b hb]
  calc _ ≤ C * M + ‖I‖ * (C * M) := (norm_add_le _ _).trans (by
        rw [norm_mul]
        exact add_le_add (hpart _ Complex.reCLM_norm.le)
          (mul_le_mul_of_nonneg_left (hpart _ Complex.imCLM_norm.le) (norm_nonneg _)))
    _ = 2 * C * M := by rw [norm_I]; ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Normalized bumps of radius at most `δ`, with radii tending to zero. -/
private theorem exists_seq_contDiffBump {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ → ContDiffBump (0 : E), (∀ n, (b n).rOut ≤ δ) ∧
      Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := by
  refine ⟨fun n => ⟨δ / (2 * (n + 1)), δ / (n + 1), by positivity, by
    rw [mul_comm, ← div_div]
    exact half_lt_self (by positivity)⟩, fun n => div_le_self hδ.le (by
      linarith [n.cast_nonneg (α := ℝ)]), ?_⟩
  simpa [div_eq_mul_one_div δ] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ

/-- Dominated convergence for a convolution against a Schwartz function: if continuous functions
`v n` converge pointwise to `w`, with a bound `C (1 + ‖θ‖) ^ N` uniform in `n`, then
`∫ ζ, G ζ * v n (η - ζ)` converges to `∫ ζ, G ζ * w (η - ζ)`. -/
private theorem tendsto_integral_mul_sub (G : 𝓢(E, ℂ)) {v : ℕ → E → ℂ} {w : E → ℂ}
    (hv : ∀ n, Continuous (v n)) (hlim : ∀ θ, Tendsto (fun n => v n θ) atTop (𝓝 (w θ)))
    {C : ℝ} {N : ℕ} (hbound : ∀ n θ, ‖v n θ‖ ≤ C * (1 + ‖θ‖) ^ N) (η : E) :
    Tendsto (fun n => ∫ ζ, G ζ * v n (η - ζ)) atTop (𝓝 (∫ ζ, G ζ * w (η - ζ))) := by
  refine tendsto_integral_of_dominated_convergence
    (fun ζ => C * (1 + ‖η‖) ^ N * ((1 + ‖ζ‖) ^ N * ‖G ζ‖))
    (fun n => (G.continuous.mul ((hv n).comp (continuous_sub_left η))).aestronglyMeasurable)
    ((SchwartzMap.integrable_one_add_norm_pow_mul_norm N G).const_mul _)
    (fun n => Eventually.of_forall fun ζ => ?_)
    (Eventually.of_forall fun ζ => (hlim (η - ζ)).const_mul _)
  have hw : 1 + ‖η - ζ‖ ≤ (1 + ‖η‖) * (1 + ‖ζ‖) := by
    simpa [sub_eq_add_neg] using TauCeti.one_add_norm_add_le η (-ζ)
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hbound 0 0)) (by simp)
  rw [norm_mul]
  calc ‖G ζ‖ * ‖v n (η - ζ)‖ ≤ ‖G ζ‖ * (C * ((1 + ‖η‖) * (1 + ‖ζ‖)) ^ N) := by
        gcongr
        exact (hbound n _).trans (by gcongr)
    _ = _ := by rw [mul_pow]; ring

/-! ### Cutting off by a Schwartz function -/

/-- **The localized Fourier transform of a product cutoff is a convolution.** For a Schwartz
function `ψ`, the localized Fourier transform of `T` with the cutoff `φ ψ` is the convolution of
the Fourier transform of `ψ` with the localized Fourier transform with the cutoff `φ`:

`localFourier T (φ ψ) η = ∫ ζ, 𝓕 ψ ζ * localFourier T φ (η - ζ)`.

This is the identity `𝓕 (ψ u) = 𝓕 ψ ⋆ 𝓕 u` for the compactly supported distribution `u = φ T`. -/
theorem localFourier_mul_eq_integral (T : 𝓓'(Ω, ℂ)) (ψ : 𝓢(E, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    T.localFourier (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (ψ.smooth ⊤) φ) η =
      ∫ ζ, 𝓕 ψ ζ * T.localFourier φ (η - ζ) := by
  -- Strategy: replace `T` by its regularizations `g n` along shrinking bumps `b n`. With
  -- `h n = φ g n`, the two sides become `𝓕 (ψ h n) η` and `∫ ζ, 𝓕 ψ ζ * 𝓕 (h n) (η - ζ)`, equal
  -- by `SchwartzMap.fourier_smul_eq_convolution`. Then pass to the limit `n → ∞`.
  set S := tsupport φ
  have hS : IsCompact S := φ.hasCompactSupport.isCompact
  obtain ⟨δ, hδ, hδΩ⟩ := hS.exists_cthickening_subset_open Ω.isOpen φ.tsupport_subset
  have hSδ : closedBall (0 : E) δ + S ⊆ Ω := by
    simpa only [hS.closedBall_add hδ.le, zero_vadd] using hδΩ
  obtain ⟨b, hbδ, hb0⟩ := exists_seq_contDiffBump (E := E) hδ
  have hbF {F : 𝓓(Ω, ℂ)} (hF : tsupport F ⊆ S) (n : ℕ) :
      closedBall (0 : E) (b n).rOut + tsupport F ⊆ Ω :=
    (add_subset_add (closedBall_subset_closedBall (hbδ n)) hF).trans hSδ
  set g := fun n => T.translatePairing (normedBump (b n))
  set h := fun n y => φ y * g n y
  have hh (n : ℕ) : Integrable (h n) :=
    integrable_mul_translatePairing T hS (b n) (hbF subset_rfl n) φ.continuous
      fun y hy => image_eq_zero_of_notMem_tsupport hy
  -- The cutoff `φ`, modulated at `θ`, gives the regularized transforms `𝓕 (h n) θ`.
  let A (θ : E) : 𝓓(Ω, ℂ) :=
    bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom θ) φ
  have hA (θ : E) : tsupport (A θ) ⊆ S := by
    simpa [A, bilinLeftCLM_apply] using tsupport_mul_subset_left (f := φ)
  have hAg (n : ℕ) (θ : E) : ∫ y, A θ y * g n y = 𝓕 (h n) θ := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [A, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', h, Circle.smul_def,
      smul_eq_mul, TauCeti.fourierAtom_eq_fourierChar]
    ring
  have hlimA (θ : E) : Tendsto (fun n => 𝓕 (h n) θ) atTop (𝓝 (T.localFourier φ θ)) := by
    rw [T.localFourier_eq φ (ψ := A θ) fun x => by
      simp [A, bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar,
        -TauCeti.fourierAtom_apply]]
    exact (tendsto_integral_mul_translatePairing T (A θ) hb0 (hbF (hA θ))).congr (hAg · θ)
  obtain ⟨N, C, hC, hT⟩ := exists_norm_integral_mul_translatePairing_le T hS hSδ
  obtain ⟨B, hB, hφB⟩ := exists_norm_iteratedFDeriv_mul_fourierAtom_le φ N
  have hbound (n : ℕ) (θ : E) : ‖𝓕 (h n) θ‖ ≤ C * B * (1 + ‖θ‖) ^ N := by
    rw [← hAg, mul_assoc]
    exact hT (A θ) (hA θ) (b n) (hbδ n) _ (by positivity) fun i hi x => by
      simpa [A, bilinLeftCLM_apply] using hφB θ i hi x
  -- The cutoff `φ ψ`, modulated at `η`, gives the convolutions.
  set P := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (ψ.smooth ⊤) φ
  let Q : 𝓓(Ω, ℂ) :=
    bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) P
  have hQ : tsupport Q ⊆ S := by
    simpa [Q, P, bilinLeftCLM_apply, mul_assoc] using
      tsupport_mul_subset_left (f := φ) (g := fun y => ψ y * TauCeti.fourierAtom η y)
  have hQg (n : ℕ) : ∫ y, Q y * g n y = ∫ ζ, 𝓕 ψ ζ * 𝓕 (h n) (η - ζ) := by
    have hconv := SchwartzMap.fourier_smul_eq_convolution ψ (hh n) η
    rw [Real.fourier_eq, convolution_def] at hconv
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] at hconv
    rw [← hconv]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Q, P, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', h, Circle.smul_def,
      smul_eq_mul, TauCeti.fourierAtom_eq_fourierChar]
    ring
  have hlimQ : Tendsto (fun n => ∫ ζ, 𝓕 ψ ζ * 𝓕 (h n) (η - ζ)) atTop
      (𝓝 (T.localFourier P η)) := by
    rw [T.localFourier_eq P (ψ := Q) fun x => by
      simp [Q, bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar,
        -TauCeti.fourierAtom_apply]]
    exact (tendsto_integral_mul_translatePairing T Q hb0 (hbF hQ)).congr hQg
  exact tendsto_nhds_unique hlimQ <| tendsto_integral_mul_sub (𝓕 ψ)
    (fun n => VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) (hh n)) hlimA hbound η

end Regularization

/-- **Localizing the cutoff** (Hörmander, Lemma 8.1.1). If the localized Fourier transform of `T`
with cutoff `φ` decays rapidly in an open cone `Γ`, then for every Schwartz function `ψ` and every
`ξ ∈ Γ`, the localized Fourier transform with cutoff `φ ψ` decays rapidly in an open cone
`Γ' ⊆ Γ` containing `ξ`.

Microlocal smoothness is therefore insensitive to the choice of cutoff: shrinking the support of
the cutoff, or multiplying it by a smooth function, keeps the rapid decay near every direction in
which it held. -/
theorem exists_isOpen_cone_decay_localFourier_mul {T : 𝓓'(Ω, ℂ)} {φ : 𝓓(Ω, ℂ)} {Γ : Set E}
    (hΓ : IsOpen Γ) (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ)
    (hdecay : ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C)
    (ψ : 𝓢(E, ℂ)) {ξ : E} (hξ : ξ ∈ Γ) :
    ∃ Γ' ⊆ Γ, IsOpen Γ' ∧ ξ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') ∧
      ∀ N : ℕ, ∃ C, ∀ η ∈ Γ', (1 + ‖η‖) ^ N *
        ‖T.localFourier (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (ψ.smooth ⊤) φ) η‖ ≤ C := by
  borelize E
  obtain ⟨c, hc, hc2, Γ', hΓ'Γ, hΓ', hξ', hcone', hsub⟩ := exists_cone_sub_mem hΓ hcone hξ
  refine ⟨Γ', hΓ'Γ, hΓ', hξ', hcone', fun N => ?_⟩
  obtain ⟨M, C₀, hC₀, hpoly⟩ := exists_norm_localFourier_le T φ
  obtain ⟨C₁, hC₁⟩ := hdecay N
  set D := 2 ^ N * max C₁ 0
  set D' := C₀ * c⁻¹ ^ (N + M)
  -- Write the transform as the convolution `∫ ζ, 𝓕 ψ ζ * localFourier T φ (η - ζ)` and bound the
  -- weighted integrand by `‖𝓕 ψ ζ‖` times a polynomial in `‖ζ‖`.
  refine ⟨∫ ζ, (D * ‖𝓕 ψ ζ‖ + D' * ((1 + ‖ζ‖) ^ (N + 2 * M) * ‖𝓕 ψ ζ‖)), fun η hη => ?_⟩
  rw [localFourier_mul_eq_integral]
  calc (1 + ‖η‖) ^ N * ‖∫ ζ, 𝓕 ψ ζ * T.localFourier φ (η - ζ)‖
      ≤ (1 + ‖η‖) ^ N * ∫ ζ, ‖𝓕 ψ ζ * T.localFourier φ (η - ζ)‖ := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ = ∫ ζ, (1 + ‖η‖) ^ N * ‖𝓕 ψ ζ * T.localFourier φ (η - ζ)‖ :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ ζ, (D * ‖𝓕 ψ ζ‖ + D' * ((1 + ‖ζ‖) ^ (N + 2 * M) * ‖𝓕 ψ ζ‖)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ζ => by positivity)
          (((𝓕 ψ).integrable.norm.const_mul D).add
            ((SchwartzMap.integrable_one_add_norm_pow_mul_norm _ (𝓕 ψ)).const_mul D'))
          (Eventually.of_forall fun ζ => ?_)
        dsimp only
        rw [norm_mul, mul_left_comm]
        calc ‖𝓕 ψ ζ‖ * ((1 + ‖η‖) ^ N * ‖T.localFourier φ (η - ζ)‖)
            ≤ ‖𝓕 ψ ζ‖ * (D + D' * (1 + ‖ζ‖) ^ (N + 2 * M)) := by
              gcongr
              exact one_add_norm_pow_mul_norm_le hc hc2 hsub hC₀ hpoly hC₁ hη ζ
          _ = D * ‖𝓕 ψ ζ‖ + D' * ((1 + ‖ζ‖) ^ (N + 2 * M) * ‖𝓕 ψ ζ‖) := by ring

/-! ### Consequences for the wave front set -/

/-- **Microlocal smoothness is witnessed by arbitrarily small cutoffs.** If `T` is microlocally
smooth at `(x, ξ)`, then for every neighbourhood `U` of `x` there is a cutoff supported in `U`,
not vanishing at `x`, whose localized Fourier transform decays rapidly in an open cone containing
`ξ`. -/
theorem IsMicrolocallySmoothAt.exists_tsupport_subset {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (h : T.IsMicrolocallySmoothAt x ξ) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U ∧ φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
      (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 h
  have hx : x ∈ Ω := φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨θ, hθ, hθx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  -- Multiply the cutoff by `θ`, which is supported in `U` and equals `1` at `x`.
  obtain ⟨Γ', -, hΓ', hξ', hcone', hdecay'⟩ := exists_isOpen_cone_decay_localFourier_mul hΓ hcone
    hdecay (θ.hasCompactSupport.toSchwartzMap θ.contDiff) hξ
  refine ⟨_, ?_, ?_, Γ', hΓ', hξ', hcone', hdecay'⟩
  · rw [bilinLeftCLM_apply]
    exact (tsupport_mul_subset_right (f := φ) (g := θ)).trans (hθ.trans inter_subset_left)
  · simpa [bilinLeftCLM_apply, hθx] using hφ

/-- The sum of two distributions microlocally smooth at `(x, ξ)` is microlocally smooth there. -/
theorem IsMicrolocallySmoothAt.add {S T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hS : S.IsMicrolocallySmoothAt x ξ) (hT : T.IsMicrolocallySmoothAt x ξ) :
    (S + T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφ, Γ₁, hΓ₁, hξ₁, hcone₁, hdecay₁⟩ := isMicrolocallySmoothAt_iff.1 hS
  obtain ⟨θ, hθ, Γ₂, hΓ₂, hξ₂, hcone₂, hdecay₂⟩ := isMicrolocallySmoothAt_iff.1 hT
  -- Both decay estimates survive passing to the common cutoff `φ θ`.
  set ψφ := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  set ψθ := θ.hasCompactSupport.toSchwartzMap θ.contDiff
  obtain ⟨Γ₁', -, hΓ₁', hξ₁', hcone₁', hdecay₁'⟩ :=
    exists_isOpen_cone_decay_localFourier_mul hΓ₁ hcone₁ hdecay₁ ψθ hξ₁
  obtain ⟨Γ₂', -, hΓ₂', hξ₂', hcone₂', hdecay₂'⟩ :=
    exists_isOpen_cone_decay_localFourier_mul hΓ₂ hcone₂ hdecay₂ ψφ hξ₂
  have hcomm : bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (ψφ.smooth ⊤) θ =
      bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (ψθ.smooth ⊤) φ := by
    ext y
    simp [ψφ, ψθ, bilinLeftCLM_apply, mul_comm]
  rw [hcomm] at hdecay₂'
  refine isMicrolocallySmoothAt_iff.2
    ⟨bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (ψθ.smooth ⊤) φ, by
      simpa [ψθ, bilinLeftCLM_apply] using mul_ne_zero hφ hθ, Γ₁' ∩ Γ₂', hΓ₁'.inter hΓ₂',
      ⟨hξ₁', hξ₂'⟩, fun t ht η hη => ⟨hcone₁' t ht η hη.1, hcone₂' t ht η hη.2⟩, fun N => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hdecay₁' N
  obtain ⟨C₂, hC₂⟩ := hdecay₂' N
  refine ⟨C₁ + C₂, fun η hη => ?_⟩
  rw [localFourier_add]
  calc _ ≤ (1 + ‖η‖) ^ N * (‖S.localFourier _ η‖ + ‖T.localFourier _ η‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ C₁ + C₂ := by rw [mul_add]; exact add_le_add (hC₁ η hη.1) (hC₂ η hη.2)

/-- The wave front set of a sum lies in the union of the wave front sets. -/
theorem waveFrontSet_add_subset (S T : 𝓓'(Ω, ℂ)) :
    (S + T).waveFrontSet ⊆ S.waveFrontSet ∪ T.waveFrontSet := by
  rintro ⟨x, ξ⟩ hxξ
  obtain ⟨hx, hξ, hST⟩ := mem_waveFrontSet_iff.1 hxξ
  by_contra h
  simp only [mem_union, mem_waveFrontSet_iff, not_or, not_and, not_not] at h
  exact hST ((h.1 hx hξ).add (h.2 hx hξ))

/-- The wave front set of a difference lies in the union of the wave front sets. -/
theorem waveFrontSet_sub_subset (S T : 𝓓'(Ω, ℂ)) :
    (S - T).waveFrontSet ⊆ S.waveFrontSet ∪ T.waveFrontSet := by
  simpa [sub_eq_add_neg] using waveFrontSet_add_subset S (-T)

end Distribution
