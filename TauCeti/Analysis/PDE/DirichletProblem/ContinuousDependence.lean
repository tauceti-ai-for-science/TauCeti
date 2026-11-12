/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem

/-!
# Continuous dependence of the Dirichlet problem on its coefficients

For a divergence-form operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` on an open set `Ω ⊆ ℝⁿ`, the
weak solution `u ∈ H¹₀(Ω)` of `L u = ℓ` depends Lipschitz continuously on the coefficients
`a, b, c` in `L^∞(Ω)` and on the forcing `ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*`, with constants governed by the
coercivity constant of the energy form. If `u` solves the problem for `(a, b, c, ℓ)`, whose energy
form `B` satisfies `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)`, and `u'` solves it for `(a', b', c', ℓ')`, then
testing both equations against `w = u - u'` gives

`C ‖u - u'‖² ≤ B(w, w) = (ℓ - ℓ')(w) - (B - B')(u', w)`,

and the difference of the energy forms is the energy form of the difference of the coefficients,
bounded by the `L^∞` bounds `Λ, β, γ` of `a - a'`, `b - b'` and `c - c'`. Hence
`‖u - u'‖ ≤ (‖ℓ - ℓ'‖ + (Λ + β + γ) ‖u'‖) / C`. Only the first energy form needs to be coercive.

## Main declarations

* `TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_eq`: the stability estimate for data in
  `H⁻¹(Ω)`.
* `TauCeti.PDE.norm_sub_le_of_isWeakSolutionDirichlet`: for a common right-hand side
  `f ∈ L²(Ω)` and coercivity constants `C, C'`, `‖u - u'‖ ≤ (Λ + β + γ) ‖f‖ / (C C')`.
* `TauCeti.PDE.tendsto_of_isWeakSolutionDirichlet`: weak solutions for coefficients converging in
  `L^∞(Ω)` to coefficients with a coercive energy form converge in `H¹₀(Ω)`.
* `TauCeti.PDE.sq_mul_norm_sub_sq_le_integral_of_forall_energyFormH1_eq`: the stability estimate
  with the coefficient difference measured in `L²` along the jet of one solution.
* `TauCeti.PDE.tendsto_of_forall_energyFormH1_eq_of_tendsto_ae`: solutions for uniformly bounded,
  uniformly coercive coefficients converging almost everywhere converge in `H¹(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.2.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, Theorem 4.1.1 (the first
  Strang lemma, the same perturbation argument for approximate forms).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped Matrix

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b b' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c c' : EuclideanSpace ℝ ι → ℝ} {C C' Lam beta gamma : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **Stability of the Dirichlet problem under perturbation of the coefficients and the data.**
Let `u ∈ H¹₀(Ω)` satisfy `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, where `B` is the energy form of
the coefficients `(a, b, c)` and satisfies `C ‖w‖² ≤ B(w, w)` on `H¹₀(Ω)` with `0 < C`, and let
`u' ∈ H¹₀(Ω)` satisfy `B'(u', v) = ℓ'(v)` for the energy form `B'` of `(a', b', c')`. Suppose both
coefficient fields are essentially bounded and that almost everywhere on `Ω`
`|ηᵀ (a - a') ξ| ≤ Λ ‖η‖ ‖ξ‖`, `‖b - b'‖ ≤ β` and `|c - c'| ≤ γ`. Then
`‖u - u'‖ ≤ (‖ℓ - ℓ'‖ + (Λ + β + γ) ‖u'‖) / C`.

The second energy form need not be coercive. -/
theorem norm_sub_le_of_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b' x) (c' x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hLam : 0 ≤ Lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' x) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hbeta : 0 ≤ beta) (hb : ∀ᵐ x ∂mu.restrict Omega, ‖b x - b' x‖ ≤ beta)
    (hgamma : 0 ≤ gamma) (hc : ∀ᵐ x ∂mu.restrict Omega, ‖c x - c' x‖ ≤ gamma)
    {ℓ ℓ' : StrongDual ℝ (W1p0 mu Omega 2)} {u u' : W1p0 mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c (u : W1p mu Omega 2) v = ℓ v)
    (hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a' b' c' (u' : W1p mu Omega 2) v = ℓ' v) :
    ‖u - u'‖ ≤ (‖ℓ - ℓ'‖ + (Lam + beta + gamma) * ‖u'‖) / C := by
  set w := u - u'
  -- Test both equations against `w = u - u'` and compare the two energy forms at `u'`.
  have hdiff := norm_energyFormH1_le_of_bounds (a := a - a') (b := b - b') (c := c - c') hLam
    ha hb hc (u' : W1p mu Omega 2) w
  have hnorm (v : W1p0 mu Omega 2) : ‖(v : W1p mu Omega 2)‖ = ‖v‖ := Submodule.norm_coe v
  rw [energyFormH1_sub hcoeff hcoeff', hnorm, hnorm] at hdiff
  have hw : energyFormH1 a b c (w : W1p mu Omega 2) w =
      (ℓ - ℓ') w - (energyFormH1 a b c (u' : W1p mu Omega 2) w -
        energyFormH1 a' b' c' (u' : W1p mu Omega 2) w) := by
    -- The coercion of `w = u - u'` to `H¹(Ω)` is `↑u - ↑u'` by `rfl` (`Submodule.coe_sub`).
    have hsplit : energyFormH1 a b c (w : W1p mu Omega 2) w =
        energyFormH1 a b c (u : W1p mu Omega 2) w - energyFormH1 a b c (u' : W1p mu Omega 2) w :=
      energyFormH1_sub_left hcoeff (u : W1p mu Omega 2) w u'
    have hℓ : (ℓ - ℓ') w = ℓ w - ℓ' w := _root_.sub_apply ℓ ℓ' w
    linarith [hu w, hu' w]
  have hkey : C * ‖w‖ ^ 2 ≤ (‖ℓ - ℓ'‖ + (Lam + beta + gamma) * ‖u'‖) * ‖w‖ := by
    have hℓ := (le_abs_self _).trans ((ℓ - ℓ').le_opNorm w)
    have hd := (neg_le_abs _).trans hdiff
    calc C * ‖w‖ ^ 2 ≤ _ := hlower w
      _ = _ := hw
      _ ≤ ‖ℓ - ℓ'‖ * ‖w‖ + (Lam + beta + gamma) * (‖u'‖ * ‖w‖) := by linarith
      _ = _ := by ring
  rcases eq_or_lt_of_le (norm_nonneg w) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hC.le
  · rw [le_div_iff₀ hC]
    nlinarith [hkey, hpos]

/-- **Dependence of the weak solution on the coefficients.** Let `u` and `u'` be weak solutions
in `H¹₀(Ω)` of the Dirichlet problems for the two coefficient triples `(a, b, c)` and
`(a', b', c')` with the same right-hand side `f ∈ L²(Ω)`, whose energy forms are coercive on
`H¹₀(Ω)` with constants `C` and `C'`. If almost everywhere on `Ω` the differences of the
coefficients are bounded by `Λ`, `β` and `γ`, in the sense of the hypotheses of
`norm_sub_le_of_forall_energyFormH1_eq`, then `‖u - u'‖ ≤ (Λ + β + γ) ‖f‖ / (C C')`. -/
theorem norm_sub_le_of_isWeakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b' x) (c' x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hC' : 0 < C')
    (hlower' : ∀ w : W1p0 mu Omega 2,
      C' * ‖w‖ ^ 2 ≤ energyFormH1 a' b' c' (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hLam : 0 ≤ Lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' x) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hbeta : 0 ≤ beta) (hb : ∀ᵐ x ∂mu.restrict Omega, ‖b x - b' x‖ ≤ beta)
    (hgamma : 0 ≤ gamma) (hc : ∀ᵐ x ∂mu.restrict Omega, ‖c x - c' x‖ ≤ gamma)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u u' : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) (hu' : IsWeakSolutionDirichlet a' b' c' f u') :
    ‖u - u'‖ ≤ (Lam + beta + gamma) * ‖f‖ / (C * C') := by
  have h := norm_sub_le_of_forall_energyFormH1_eq hcoeff hcoeff' hC hlower hLam ha hbeta hb
    hgamma hc hu.energyFormH1_eq_dirichletForcing hu'.energyFormH1_eq_dirichletForcing
  rw [sub_self (dirichletForcing f), ContinuousLinearMap.opNorm_zero, zero_add] at h
  have hu'f := norm_le_of_isWeakSolutionDirichlet hC' hlower' hu'
  calc ‖u - u'‖ ≤ (Lam + beta + gamma) * ‖u'‖ / C := h
    _ ≤ (Lam + beta + gamma) * (‖f‖ / C') / C := by gcongr
    _ = _ := by ring

/-- **Continuous dependence of the weak solution on the coefficients.** Let `u` be a weak
solution in `H¹₀(Ω)` of the Dirichlet problem for `(a, b, c)` with right-hand side `f ∈ L²(Ω)`,
whose energy form is coercive on `H¹₀(Ω)` with constant `C`, and let `u' i` be weak solutions for
a family of coefficient triples `(a' i, b' i, c' i)` with the same `f`. If the bounds `Λ i`, `β i`
and `γ i` on the differences `a - a' i`, `b - b' i` and `c - c' i` almost everywhere on `Ω`, in
the sense of the hypotheses of `norm_sub_le_of_forall_energyFormH1_eq`, tend to `0` along a
filter, then `u' i` tends to `u` in `H¹₀(Ω)`. The perturbed energy forms need not be coercive. -/
theorem tendsto_of_isWeakSolutionDirichlet {α : Type*} {l : Filter α}
    {a' : α → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b' : α → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c' : α → EuclideanSpace ℝ ι → ℝ} {Lam beta gamma : α → ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : ∀ i,
      MemLp (fun x => energyIntegrand (a' i x) (b' i x) (c' i x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hLam : ∀ i, 0 ≤ Lam i)
    (ha : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ ((a x - a' i x) *ᵥ ξ)| ≤ Lam i * ‖η‖ * ‖ξ‖)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hb : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ‖b x - b' i x‖ ≤ beta i)
    (hgamma : ∀ i, 0 ≤ gamma i)
    (hc : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ‖c x - c' i x‖ ≤ gamma i)
    (hlim : Filter.Tendsto (fun i => Lam i + beta i + gamma i) l (nhds 0))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2} {u' : α → W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u)
    (hu' : ∀ i, IsWeakSolutionDirichlet (a' i) (b' i) (c' i) f (u' i)) :
    Filter.Tendsto u' l (nhds u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- `‖u - u' i‖ ≤ (Λ i + β i + γ i) ‖u' i‖ / C`, so once `Λ i + β i + γ i ≤ C / 2` we get
  -- `‖u' i - u‖ ≤ 2 (Λ i + β i + γ i) ‖u‖ / C`, and these bounds tend to `0`.
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (((hlim.const_mul 2).mul_const ‖u‖).div_const C |>.trans
      (by rw [mul_zero, zero_mul, zero_div]))
  filter_upwards [hlim.eventually (ge_mem_nhds (half_pos hC))] with i hi
  have h := norm_sub_le_of_forall_energyFormH1_eq hcoeff (hcoeff' i) hC hlower (hLam i)
    (ha i) (hbeta i) (hb i) (hgamma i) (hc i) hu.energyFormH1_eq_dirichletForcing
    (hu' i).energyFormH1_eq_dirichletForcing
  rw [sub_self (dirichletForcing f), ContinuousLinearMap.opNorm_zero, zero_add,
    le_div_iff₀ hC] at h
  have htri := norm_le_norm_add_norm_sub u (u' i)
  have hδ : 0 ≤ Lam i + beta i + gamma i := by linarith [hLam i, hbeta i, hgamma i]
  rw [norm_sub_rev, le_div_iff₀ hC]
  nlinarith [mul_le_mul_of_nonneg_right hi (norm_nonneg (u - u' i)),
    mul_le_mul_of_nonneg_left htri hδ]

/-- **Stability measured along the solution.** Let `u ∈ H¹(Ω)` satisfy `B(u, v) = ℓ(v)` and
`u' ∈ H¹(Ω)` satisfy `B'(u', v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, with the same right-hand side
`ℓ ∈ H⁻¹(Ω)` and `u' - u ∈ H¹₀(Ω)`, where `B` and `B'` are the energy forms of two coefficient
triples with essentially bounded pointwise energy densities `E` and `E'`. If `B'` satisfies
`C ‖w‖² ≤ B'(w, w)` on `H¹₀(Ω)`, then

`C² ‖u' - u‖² ≤ ∫_Ω ‖(E(x) - E'(x)) (u(x), ∇u(x))‖² dx`.

Only the second energy form needs to be coercive. Unlike
`TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_eq`, the difference of the coefficients is
measured along the jet of `u` rather than in `L^∞(Ω)`. -/
theorem sq_mul_norm_sub_sq_le_integral_of_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b' x) (c' x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower' : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a' b' c' (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} {u u' : W1p mu Omega 2}
    (hsub : u' - u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v)
    (hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a' b' c' u' v = ℓ v) :
    C ^ 2 * ‖u' - u‖ ^ 2 ≤ ∫ x in Omega, ‖(energyIntegrand (a x) (b x) (c x) -
      energyIntegrand (a' x) (b' x) (c' x)) (jetField u x)‖ ^ 2 ∂mu := by
  let : NormedAddCommGroup
      ((ℝ × EuclideanSpace ℝ ι) →L[ℝ] (ℝ × EuclideanSpace ℝ ι) →L[ℝ] ℝ) := inferInstance
  have hD : MemLp (fun x => energyIntegrand (a x) (b x) (c x) -
      energyIntegrand (a' x) (b' x) (c' x)) ⊤ (mu.restrict Omega) := hcoeff.sub hcoeff'
  have hcont : Continuous (fun p : ((ℝ × EuclideanSpace ℝ ι) →L[ℝ]
      (ℝ × EuclideanSpace ℝ ι) →L[ℝ] ℝ) × (ℝ × EuclideanSpace ℝ ι) => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hGm : AEStronglyMeasurable (fun x => (energyIntegrand (a x) (b x) (c x) -
      energyIntegrand (a' x) (b' x) (c' x)) (jetField u x)) (mu.restrict Omega) :=
    hcont.comp_aestronglyMeasurable
      (hD.aestronglyMeasurable.prodMk (memLp_jetField u).aestronglyMeasurable)
  -- The jet of `u` is in `L²` and the coefficient difference is in `L^∞`.
  have hG : MemLp (fun x => (energyIntegrand (a x) (b x) (c x) -
      energyIntegrand (a' x) (b' x) (c' x)) (jetField u x)) 2 (mu.restrict Omega) := by
    refine (memLp_jetField u).of_le_mul' (c := (eLpNormEssSup (fun x =>
      energyIntegrand (a x) (b x) (c x) - energyIntegrand (a' x) (b' x) (c' x))
        (mu.restrict Omega)).toNNReal) hGm ?_
    have hfin := hD.eLpNorm_lt_top
    rw [eLpNorm_exponent_top hD.aestronglyMeasurable] at hfin
    filter_upwards [ae_le_eLpNormEssSup (f := fun x =>
      energyIntegrand (a x) (b x) (c x) - energyIntegrand (a' x) (b' x) (c' x))
        (μ := mu.restrict Omega)] with x hx
    refine ((ContinuousLinearMap.le_opENorm _ _)).trans ?_
    gcongr
    rwa [ENNReal.coe_toNNReal hfin.ne]
  have hG2 := (memLp_two_iff_integrable_sq_norm hGm).1 hG
  have hJ2 (w : W1p mu Omega 2) : Integrable (fun x => ‖jetField w x‖ ^ 2) (mu.restrict Omega) :=
    (memLp_two_iff_integrable_sq_norm (memLp_jetField w).aestronglyMeasurable).1
      (memLp_jetField w)
  let w : W1p0 mu Omega 2 := ⟨u' - u, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hsub⟩
  have hnorm : ‖w‖ = ‖u' - u‖ := Submodule.norm_coe w
  -- Testing both equations against `w = u' - u` expresses `B'(w, w)` through the coefficient
  -- difference applied to the jet of `u`.
  have hww : energyFormH1 a' b' c' (w : W1p mu Omega 2) (w : W1p mu Omega 2) =
      ∫ x in Omega, (energyIntegrand (a x) (b x) (c x) -
        energyIntegrand (a' x) (b' x) (c' x)) (jetField u x)
          (jetField (w : W1p mu Omega 2) x) ∂mu := by
    have h1 := energyFormH1_sub_left hcoeff' u' (w : W1p mu Omega 2) u
    rw [hu' w, ← hu w] at h1
    refine h1.trans ?_
    rw [energyFormH1_def, energyFormH1_def, ← integral_sub
      (integrable_energyIntegrand_jetField hcoeff u _)
      (integrable_energyIntegrand_jetField hcoeff' u _)]
    simp only [sub_apply]
  -- Young's inequality `‖G‖ ‖J‖ ≤ ‖G‖² / (2C) + (C / 2) ‖J‖²` under the integral.
  have hbound : ∫ x in Omega, (energyIntegrand (a x) (b x) (c x) -
        energyIntegrand (a' x) (b' x) (c' x)) (jetField u x)
          (jetField (w : W1p mu Omega 2) x) ∂mu ≤
      (∫ x in Omega, ‖(energyIntegrand (a x) (b x) (c x) -
        energyIntegrand (a' x) (b' x) (c' x)) (jetField u x)‖ ^ 2 ∂mu) / (2 * C) +
        C / 2 * ‖w‖ ^ 2 := by
    refine (le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le ?_)
    refine (norm_integral_le_of_norm_le ((hG2.div_const (2 * C)).add
      ((hJ2 (w : W1p mu Omega 2)).const_mul (C / 2)))
        (Filter.Eventually.of_forall fun x => ?_)).trans ?_
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [Pi.add_apply, div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖(energyIntegrand (a x) (b x) (c x) -
        energyIntegrand (a' x) (b' x) (c' x)) (jetField u x)‖ -
          C * ‖jetField (w : W1p mu Omega 2) x‖)]
    · simp only [Pi.add_apply]
      rw [integral_add (hG2.div_const _) ((hJ2 _).const_mul _), integral_div,
        integral_const_mul]
      gcongr
      exact (integral_norm_jetField_sq_le _).trans_eq (by rw [Submodule.norm_coe])
  have hkey := (hlower' w).trans (hww.trans_le hbound)
  rw [← hnorm]
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)] at hkey
  nlinarith [sq_nonneg ‖w‖]

/-- **Continuous dependence on coefficients converging almost everywhere.** Let `u ∈ H¹(Ω)`
satisfy `B(u, v) = ℓ(v)` for every `v ∈ H¹₀(Ω)`, and let `u' i ∈ H¹(Ω)`, with
`u' i - u ∈ H¹₀(Ω)`, satisfy the same equation for the energy forms `B'ᵢ` of a sequence of
coefficient triples. Suppose that the pointwise energy densities of the `i`-th triple are
a.e. strongly measurable and bounded by `K` almost everywhere on `Ω`, that they converge
almost everywhere on `Ω` to the energy density of `B`, and that the forms `B'ᵢ` are coercive on
`H¹₀(Ω)` with a common constant `C`. Then `u' i → u` in `H¹(Ω)`.

The coefficients need not converge in `L^∞(Ω)`, as in
`TauCeti.PDE.tendsto_of_isWeakSolutionDirichlet`; dominated convergence controls the coefficient
error along the jet of `u`. -/
theorem tendsto_of_forall_energyFormH1_eq_of_tendsto_ae
    {a' : ℕ → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b' : ℕ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c' : ℕ → EuclideanSpace ℝ ι → ℝ} {K : ℝ}
    (hmeas : ∀ i, AEStronglyMeasurable (fun x => energyIntegrand (a' i x) (b' i x) (c' i x))
      (mu.restrict Omega))
    (hK : ∀ i, ∀ᵐ x ∂mu.restrict Omega, ‖energyIntegrand (a' i x) (b' i x) (c' i x)‖ ≤ K)
    (hlim : ∀ᵐ x ∂mu.restrict Omega, Filter.Tendsto
      (fun i => energyIntegrand (a' i x) (b' i x) (c' i x)) Filter.atTop
      (nhds (energyIntegrand (a x) (b x) (c x))))
    (hC : 0 < C)
    (hlower : ∀ i, ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 (a' i) (b' i) (c' i) (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} {u : W1p mu Omega 2} {u' : ℕ → W1p mu Omega 2}
    (hsub : ∀ i, u' i - u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v)
    (hu' : ∀ i, ∀ v : W1p0 mu Omega 2, energyFormH1 (a' i) (b' i) (c' i) (u' i) v = ℓ v) :
    Filter.Tendsto u' Filter.atTop (nhds u) := by
  let : NormedAddCommGroup
      ((ℝ × EuclideanSpace ℝ ι) →L[ℝ] (ℝ × EuclideanSpace ℝ ι) →L[ℝ] ℝ) := inferInstance
  -- The limit density is measurable and bounded by `K`, as an almost everywhere limit.
  have hEK : ∀ᵐ x ∂mu.restrict Omega, ‖energyIntegrand (a x) (b x) (c x)‖ ≤ K := by
    filter_upwards [hlim, ae_all_iff.2 hK] with x hx hxK
    exact le_of_tendsto' hx.norm hxK
  have hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega) :=
    memLp_top_of_bound (aestronglyMeasurable_of_tendsto_ae _ hmeas hlim) K hEK
  have hcont : Continuous (fun p : ((ℝ × EuclideanSpace ℝ ι) →L[ℝ]
      (ℝ × EuclideanSpace ℝ ι) →L[ℝ] ℝ) × (ℝ × EuclideanSpace ℝ ι) => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  -- Dominated convergence: the coefficient error along the jet of `u` tends to `0` in `L²`.
  have hδ : Filter.Tendsto (fun i => ∫ x in Omega, ‖(energyIntegrand (a x) (b x) (c x) -
      energyIntegrand (a' i x) (b' i x) (c' i x)) (jetField u x)‖ ^ 2 ∂mu) Filter.atTop
      (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := mu.restrict Omega)
      (F := fun i x => ‖(energyIntegrand (a x) (b x) (c x) -
        energyIntegrand (a' i x) (b' i x) (c' i x)) (jetField u x)‖ ^ 2) (f := 0)
      (fun x => (2 * K) ^ 2 * ‖jetField u x‖ ^ 2)
      (fun i => (hcont.comp_aestronglyMeasurable ((hcoeff.aestronglyMeasurable.sub
        (hmeas i)).prodMk (memLp_jetField u).aestronglyMeasurable)).norm.pow 2)
      (((memLp_two_iff_integrable_sq_norm (memLp_jetField u).aestronglyMeasurable).1
        (memLp_jetField u)).const_mul _) (fun i => ?_) ?_
    · simpa using h
    · filter_upwards [hK i, hEK] with x hx hE
      have hle : ‖(energyIntegrand (a x) (b x) (c x) -
          energyIntegrand (a' i x) (b' i x) (c' i x)) (jetField u x)‖ ≤
            2 * K * ‖jetField u x‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans_eq (by ring)
    · filter_upwards [hlim] with x hx
      have h0 := (tendsto_const_nhds (x := energyIntegrand (a x) (b x) (c x))).sub hx
      rw [sub_self] at h0
      simpa using (((hcont.tendsto _).comp (h0.prodMk_nhds tendsto_const_nhds)).norm.pow 2)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    ((hδ.sqrt.div_const C).trans (by rw [Real.sqrt_zero, zero_div]))
  have h := sq_mul_norm_sub_sq_le_integral_of_forall_energyFormH1_eq hcoeff
    (memLp_top_of_bound (hmeas i) K (hK i)) hC (hlower i) (hsub i) hu (hu' i)
  rw [le_div_iff₀ hC, ← Real.sqrt_sq (mul_nonneg (norm_nonneg _) hC.le)]
  exact Real.sqrt_le_sqrt (by rw [mul_pow, mul_comm]; exact h)

end PDE

end TauCeti
