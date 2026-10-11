/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Existence
public import TauCeti.Data.EReal.Operations
public import TauCeti.Topology.EMetricSpace.Ascoli

/-!
# Generalized minimizing movements

Let `φ : X → EReal` be an energy on an extended metric space. The *minimizing movement scheme* of
De Giorgi approximates the gradient flow of `φ` by implicit Euler steps: for a time step `τ > 0`, a
*minimizing movement sequence* `u` has each `u (n + 1)` in the resolvent `J_τ (u n)`, minimizing
`y ↦ φ y + d(u n, y)² / (2τ)`. Its *piecewise constant interpolant* `ū_τ` is the curve with value
`u (n + 1)` on `(n τ, (n + 1) τ]`. A *generalized minimizing movement* starting from `x` is a
pointwise limit of such interpolants along time steps `τ k → 0`. Following
Ambrosio–Gigli–Savaré, the limit is taken for an auxiliary convergence `y_n ⇀ y` on `X`, given by
filters `l y`, which may be weaker than that of the metric: the narrow topology on the Wasserstein
space `P₂(X)` is the motivating case. Generalized minimizing movements are the candidate solutions
of the gradient flow; under further hypotheses they are curves of maximal slope.

The main result is the compactness theorem of the scheme
(`TauCeti.exists_strictMono_tendsto_piecewiseConstantInterpolant`) and its consequence that
generalized minimizing movements exist (`TauCeti.exists_isGeneralizedMinimizingMovement`). The
hypotheses are those of Ambrosio–Gigli–Savaré, Assumption 2.1, under which resolvent steps exist
(`TauCeti.moreauYosidaResolvent_nonempty`): the energy is coercive, `φ_{τ₀}(x₀) > -∞` for a
time step `τ₀ > 0`, bounded sublevels of `φ` are relatively sequentially compact for `⇀`, and the
distance is jointly lower semicontinuous for `⇀`. The energy need not be bounded below. The
proof rests on a priori estimates uniform in the time step, which make the interpolants
equicontinuous up to an error of the order of `√τ`, followed by the pointwise Arzelà–Ascoli
theorem `TauCeti.exists_strictMono_forall_tendsto_of_limsup_edist`.

The a priori estimates hold for `4τ ≤ τ₀` and a real lower bound `m ≤ φ_{τ₀}(x₀)`. The quantity
`H(y) = φ y - m + d(y, x₀)² / τ₀`, which coercivity makes nonnegative, grows by a factor at most
`1 + 8τ/τ₀` along each resolvent step. Hence, starting from `φ (u 0) ≤ c` and `d(u 0, x₀) ≤ r`,
the sequence stays in a ball about `x₀` and the squared step lengths have bounded sums, with
bounds growing exponentially in the elapsed time `n τ`.

## Main definitions

* `TauCeti.piecewiseConstantInterpolant τ u`: the piecewise constant interpolant of `u` with time
  step `τ`.
* `TauCeti.IsGeneralizedMinimizingMovement l φ x u`: `u` is a generalized minimizing movement for
  `φ` starting from `x`, for the convergence given by `l`.

## Main results

* `TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent` and
  `TauCeti.sum_edist_sq_le_of_forall_mem_moreauYosidaResolvent`: the a priori estimates along a
  minimizing movement sequence for a coercive energy.
* `TauCeti.edist_piecewiseConstantInterpolant_le`: the interpolant is `1/2`-Hölder up to the time
  step, `d(ū s, ū t)² ≤ C (|t - s| + τ)` on `(-∞, T]`, with `C` independent of `τ`.
* `TauCeti.exists_strictMono_tendsto_piecewiseConstantInterpolant`: **compactness**: interpolants
  of minimizing movement sequences with time steps `τ k → 0` and admissible initial points have a
  subsequence converging at every time to a curve that is `1/2`-Hölder on bounded intervals.
* `TauCeti.exists_isGeneralizedMinimizingMovement`: **existence** of a generalized minimizing
  movement from every point of finite energy at finite distance from `x₀`, and
  `TauCeti.exists_isGeneralizedMinimizingMovement_of_lowerSemicontinuous` for a lower
  semicontinuous energy on a proper metric space.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 2 (Assumption 2.1 and
  Proposition 2.2.3) and Chapter 3, Section 3.3.
* E. De Giorgi, *New problems on minimizing movements*, in *Boundary Value Problems for PDE and
  Applications*, Masson 1993, 81–98.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section Interpolant

variable {X : Type*} {τ : ℝ≥0} {u : ℕ → X}

/-- The *piecewise constant interpolant* of a sequence `u` with time step `τ`: the curve equal to
`u 0` at times `t ≤ 0` and to `u (n + 1)` on the interval `(n τ, (n + 1) τ]`. Its value at `t` is
`u ⌈t / τ⌉₊`. -/
def piecewiseConstantInterpolant (τ : ℝ≥0) (u : ℕ → X) (t : ℝ) : X :=
  u ⌈t / τ⌉₊

/-- The defining formula of the piecewise constant interpolant. -/
theorem piecewiseConstantInterpolant_def (τ : ℝ≥0) (u : ℕ → X) (t : ℝ) :
    piecewiseConstantInterpolant τ u t = u ⌈t / τ⌉₊ :=
  (rfl)

/-- At times `t ≤ 0` the piecewise constant interpolant is the initial point. -/
theorem piecewiseConstantInterpolant_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    piecewiseConstantInterpolant τ u t = u 0 := by
  rw [piecewiseConstantInterpolant_def,
    Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg ht (NNReal.coe_nonneg τ))]

/-- At time `0` the piecewise constant interpolant is the initial point. -/
@[simp]
theorem piecewiseConstantInterpolant_zero (τ : ℝ≥0) (u : ℕ → X) :
    piecewiseConstantInterpolant τ u 0 = u 0 :=
  piecewiseConstantInterpolant_of_nonpos le_rfl

/-- On the interval `(n τ, (n + 1) τ]` the piecewise constant interpolant is `u (n + 1)`. -/
theorem piecewiseConstantInterpolant_of_mem_Ioc (hτ : 0 < τ) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ioc ((n : ℝ) * τ) ((n + 1) * τ)) :
    piecewiseConstantInterpolant τ u t = u (n + 1) := by
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  rw [piecewiseConstantInterpolant_def, (Nat.ceil_eq_iff n.succ_ne_zero).2]
  rw [Nat.succ_sub_one, Nat.cast_succ, lt_div_iff₀ hτ', div_le_iff₀ hτ']
  exact ht

/-- At the time `n τ` of the `n`-th step the piecewise constant interpolant is `u n`. -/
@[simp]
theorem piecewiseConstantInterpolant_natCast_mul (hτ : 0 < τ) (n : ℕ) :
    piecewiseConstantInterpolant τ u (n * τ) = u n := by
  rw [piecewiseConstantInterpolant_def, mul_div_cancel_right₀ _ (NNReal.coe_pos.2 hτ).ne',
    Nat.ceil_natCast]

end Interpolant

section Estimates

/-- The real inequality behind one step of the a priori estimate. With `t` the time step, `s` the
coercivity time step, `A` and `B` the energies before and after the step, `d` its length and `D`,
`D'` the distances to the base point before and after it, the quantity
`H = energy - m + distance² / s` grows by a factor at most `1 + 8t/s`. -/
private theorem sub_add_sq_div_le_mul {t s D D' d A B m : ℝ} (ht : 0 < t) (hts : 4 * t ≤ s)
    (hD'₀ : 0 ≤ D') (hD' : D' ≤ D + d) (hB : B + d ^ 2 / (2 * t) ≤ A)
    (hm : m ≤ A + D ^ 2 / (2 * s)) :
    B - m + D' ^ 2 / s ≤ (1 + 8 * t / s) * (A - m + D ^ 2 / s) := by
  have hs : 0 < s := by linarith
  -- `D'² ≤ (1 + 4t/s) D² + s d² / (2t)`, the triangle inequality and Young's inequality.
  have key : 2 * t * s * D' ^ 2 ≤ 2 * t * (s + 4 * t) * D ^ 2 + s ^ 2 * d ^ 2 := by
    have h1 : D' ^ 2 ≤ (D + d) ^ 2 := pow_le_pow_left₀ hD'₀ hD' 2
    have h2 : 0 ≤ (4 * t * D - s * d) ^ 2 := sq_nonneg _
    have h3 : 2 * t * s * d ^ 2 ≤ s ^ 2 * d ^ 2 / 2 := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg d) hs.le) (sub_nonneg.2 hts)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * t * s)]
  have h4 : D' ^ 2 / s ≤ D ^ 2 / s + 4 * t * D ^ 2 / s ^ 2 + d ^ 2 / (2 * t) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity)
      (by positivity), div_le_div_iff₀ hs (by positivity)]
    nlinarith [key]
  -- `A - m + D² / s ≥ D² / (2s)`, so the extra term `4t D² / s²` is at most `8t/s` times it.
  have h5 : 4 * t * D ^ 2 / s ^ 2 ≤ 8 * t / s * (A - m + D ^ 2 / s) := by
    have : D ^ 2 / (2 * s) ≤ A - m + D ^ 2 / s := by
      have : D ^ 2 / (2 * s) = D ^ 2 / s - D ^ 2 / (2 * s) := by field_simp; ring
      linarith
    calc 4 * t * D ^ 2 / s ^ 2 = 8 * t / s * (D ^ 2 / (2 * s)) := by field_simp; ring
      _ ≤ 8 * t / s * (A - m + D ^ 2 / s) := by gcongr
  nlinarith [h4, h5]

variable {X : Type*} [PseudoEMetricSpace X] {φ : X → EReal} {τ τ₀ : ℝ≥0} {x₀ : X} {m : ℝ}
  {u : ℕ → X}

/-- A real lower bound `m ≤ φ_{τ₀}(x₀)` for the Moreau–Yosida approximation bounds the energy
below at every point `z` at finite distance from `x₀`: `m ≤ φ z + d(z, x₀)² / (2τ₀)`. -/
private theorem ne_bot_and_le_toReal_add (hτ₀ : 0 < τ₀) (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    {z : X} (hz : edist z x₀ ≠ ⊤) (hφz : φ z ≠ ⊤) :
    φ z ≠ ⊥ ∧ m ≤ (φ z).toReal + (edist z x₀).toReal ^ 2 / (2 * τ₀) := by
  have hz' : edist x₀ z ≠ ⊤ := edist_comm z x₀ ▸ hz
  have hP : edist x₀ z ^ 2 / (2 * τ₀) ≠ ⊤ :=
    ENNReal.div_ne_top (by finiteness) (by simp [hτ₀.ne'])
  have h := hm.trans (moreauYosida_le φ τ₀ hz')
  have hbot : φ z ≠ ⊥ := by
    rintro hb
    rw [hb, EReal.bot_add, le_bot_iff] at h
    exact EReal.coe_ne_bot _ h
  refine ⟨hbot, ?_⟩
  rw [← EReal.coe_toReal hφz hbot, EReal.coe_le_coe_add_coe_ennreal_iff hP] at h
  simpa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, edist_comm] using h

/-- The a priori estimates along a minimizing movement sequence, in real numbers: the energy stays
finite, the sequence stays at finite distance from `x₀`, the energy plus the accumulated penalties
is at most the initial energy, and `H n = φ (u n) - m + d(u n, x₀)² / τ₀` grows at most
geometrically. -/
private theorem forall_toReal_le (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀)
    (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) (h0 : φ (u 0) ≠ ⊤)
    (hx : edist (u 0) x₀ ≠ ⊤) (n : ℕ) :
    φ (u n) ≠ ⊤ ∧ φ (u n) ≠ ⊥ ∧ edist (u n) x₀ ≠ ⊤ ∧
      (φ (u n)).toReal + ∑ k ∈ Finset.range n, (edist (u k) (u (k + 1))).toReal ^ 2 / (2 * τ) ≤
        (φ (u 0)).toReal ∧
      (φ (u n)).toReal - m + (edist (u n) x₀).toReal ^ 2 / τ₀ ≤
        (1 + 8 * τ / τ₀) ^ n * ((φ (u 0)).toReal - m + (edist (u 0) x₀).toReal ^ 2 / τ₀) := by
  have hτ₀ : 0 < τ₀ := lt_of_lt_of_le (by positivity) h4
  induction n with
  | zero =>
    exact ⟨h0, (ne_bot_and_le_toReal_add hτ₀ hm hx h0).1, hx, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨htop, hbot, hdist, hsum, hH⟩ := ih
    have hstep := edist_ne_top_of_mem_moreauYosidaResolvent (hu n)
    have htri := edist_triangle_left (u (n + 1)) x₀ (u n)
    have hdist' : edist (u (n + 1)) x₀ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hstep, hdist⟩) htri
    have htop' : φ (u (n + 1)) ≠ ⊤ :=
      ne_top_of_le_ne_top htop (apply_le_of_mem_moreauYosidaResolvent (hu n))
    have hbot' := (ne_bot_and_le_toReal_add hτ₀ hm hdist' htop').1
    have hB := add_toReal_sq_div_le_of_mem_moreauYosidaResolvent hτ (hu n) (z := u n) (by simp)
      (EReal.coe_toReal htop' hbot').symm (EReal.coe_toReal htop hbot).symm
    rw [edist_self, ENNReal.toReal_zero, zero_pow two_ne_zero, zero_div, add_zero] at hB
    refine ⟨htop', hbot', hdist', ?_, ?_⟩
    · rw [Finset.sum_range_succ]
      linarith
    · have hD' := ENNReal.toReal_le_add htri hstep hdist
      calc _ ≤ (1 + 8 * τ / τ₀) * ((φ (u n)).toReal - m + (edist (u n) x₀).toReal ^ 2 / τ₀) :=
            sub_add_sq_div_le_mul (NNReal.coe_pos.2 hτ) (by exact_mod_cast h4)
              ENNReal.toReal_nonneg (by linarith) hB
              (ne_bot_and_le_toReal_add hτ₀ hm hdist htop).2
        _ ≤ (1 + 8 * τ / τ₀) * ((1 + 8 * τ / τ₀) ^ n *
              ((φ (u 0)).toReal - m + (edist (u 0) x₀).toReal ^ 2 / τ₀)) := by gcongr
        _ = _ := by ring

/-- The a priori estimates along a minimizing movement sequence in terms of a bound `c` on the
initial energy and a bound `r` on the initial distance to `x₀`. -/
private theorem toReal_sq_le_and_sum_le (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀)
    (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) {c : ℝ} (hc : φ (u 0) ≤ c)
    {r : ℝ≥0} (hr : edist (u 0) x₀ ≤ r) (n : ℕ) :
    edist (u n) x₀ ≠ ⊤ ∧
      (edist (u n) x₀).toReal ^ 2 ≤ 2 * τ₀ * Real.exp (8 * n * τ / τ₀) * (c - m + r ^ 2 / τ₀) ∧
      ∑ k ∈ Finset.range n, (edist (u k) (u (k + 1))).toReal ^ 2 ≤
        2 * τ * (1 + Real.exp (8 * n * τ / τ₀)) * (c - m + r ^ 2 / τ₀) := by
  have hτ₀ : 0 < τ₀ := lt_of_lt_of_le (by positivity) h4
  have hτ₀' : (0 : ℝ) < τ₀ := NNReal.coe_pos.2 hτ₀
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have h0 : φ (u 0) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top c) hc
  have hx : edist (u 0) x₀ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hr
  obtain ⟨htop₀, hbot₀, -, -, -⟩ := forall_toReal_le hτ h4 hm hu h0 hx 0
  obtain ⟨htop, hbot, hdist, hsum, hH⟩ := forall_toReal_le hτ h4 hm hu h0 hx n
  have hm₀ := (ne_bot_and_le_toReal_add hτ₀ hm hx h0).2
  have hmn := (ne_bot_and_le_toReal_add hτ₀ hm hdist htop).2
  -- The initial value of `H` is at most `c - m + r² / τ₀`.
  have hc' : (φ (u 0)).toReal ≤ c := by
    simpa using EReal.toReal_le_toReal hc hbot₀ (EReal.coe_ne_top c)
  have hr' : (edist (u 0) x₀).toReal ≤ r := by
    simpa using (ENNReal.toReal_le_toReal hx ENNReal.coe_ne_top).2 hr
  have hH₀ : (φ (u 0)).toReal - m + (edist (u 0) x₀).toReal ^ 2 / τ₀ ≤ c - m + r ^ 2 / τ₀ := by
    gcongr
  have hH₀' : 0 ≤ (φ (u 0)).toReal - m + (edist (u 0) x₀).toReal ^ 2 / τ₀ := by
    have : (edist (u 0) x₀).toReal ^ 2 / (2 * τ₀) ≤ (edist (u 0) x₀).toReal ^ 2 / τ₀ := by
      gcongr; linarith
    linarith
  -- The geometric growth factor is at most an exponential.
  have hexp : (1 + 8 * τ / τ₀ : ℝ) ^ n ≤ Real.exp (8 * n * τ / τ₀) := by
    calc (1 + 8 * τ / τ₀ : ℝ) ^ n ≤ Real.exp (8 * τ / τ₀) ^ n := by
          gcongr
          linarith [Real.add_one_le_exp (8 * τ / τ₀ : ℝ)]
      _ = Real.exp (8 * n * τ / τ₀) := by rw [← Real.exp_nat_mul]; ring_nf
  have hHn : (φ (u n)).toReal - m + (edist (u n) x₀).toReal ^ 2 / τ₀ ≤
      Real.exp (8 * n * τ / τ₀) * (c - m + r ^ 2 / τ₀) :=
    hH.trans (mul_le_mul hexp hH₀ hH₀' (Real.exp_pos _).le)
  -- `H n` dominates `d(u n, x₀)² / (2τ₀)`.
  have hhalf : (edist (u n) x₀).toReal ^ 2 / (2 * τ₀) ≤
      (φ (u n)).toReal - m + (edist (u n) x₀).toReal ^ 2 / τ₀ := by
    have : (edist (u n) x₀).toReal ^ 2 / τ₀ =
        (edist (u n) x₀).toReal ^ 2 / (2 * τ₀) + (edist (u n) x₀).toReal ^ 2 / (2 * τ₀) := by
      field_simp; ring
    linarith
  refine ⟨hdist, ?_, ?_⟩
  · have := hhalf.trans hHn
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  · rw [← Finset.sum_div] at hsum
    have : (∑ k ∈ Finset.range n, (edist (u k) (u (k + 1))).toReal ^ 2) / (2 * τ) ≤
        (1 + Real.exp (8 * n * τ / τ₀)) * (c - m + r ^ 2 / τ₀) := by
      have : (edist (u 0) x₀).toReal ^ 2 / τ₀ ≥ 0 := by positivity
      nlinarith [hhalf.trans hHn]
    rw [div_le_iff₀ (by positivity)] at this
    linarith

/-- **A priori estimate for the distance** along a minimizing movement sequence. Let `u` be a
minimizing movement sequence with time step `τ > 0`, each `u (n + 1)` a resolvent step from
`u n`, and suppose the energy is coercive, with `m ≤ φ_{τ₀}(x₀)` for some `τ₀ ≥ 4τ`. If
`φ (u 0) ≤ c` and `d(u 0, x₀) ≤ r`, then the sequence stays in a ball about `x₀` whose squared
radius grows at most exponentially in the elapsed time `n τ`:
`d(u n, x₀)² ≤ 2τ₀ e^{8nτ/τ₀} (c - m + r² / τ₀)`. -/
theorem edist_sq_le_of_forall_mem_moreauYosidaResolvent (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀)
    (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) {c : ℝ} (hc : φ (u 0) ≤ c)
    {r : ℝ≥0} (hr : edist (u 0) x₀ ≤ r) (n : ℕ) :
    edist (u n) x₀ ^ 2 ≤
      ENNReal.ofReal (2 * τ₀ * Real.exp (8 * n * τ / τ₀) * (c - m + r ^ 2 / τ₀)) := by
  obtain ⟨hdist, h, -⟩ := toReal_sq_le_and_sum_le hτ h4 hm hu hc hr n
  rw [← ENNReal.ofReal_toReal hdist, ← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal h

/-- **A priori estimate for the accumulated penalties** along a minimizing movement sequence.
Under the hypotheses of `TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent`, the squared
lengths of the first `n` steps sum to at most `2τ (1 + e^{8nτ/τ₀}) (c - m + r² / τ₀)`. When `φ`
is bounded below the discrete energy estimate gives such a bound directly; here only coercivity
is assumed, and the exponential accounts for the possible decrease of `φ` far from `x₀`. -/
theorem sum_edist_sq_le_of_forall_mem_moreauYosidaResolvent (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀)
    (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) {c : ℝ} (hc : φ (u 0) ≤ c)
    {r : ℝ≥0} (hr : edist (u 0) x₀ ≤ r) (n : ℕ) :
    ∑ k ∈ Finset.range n, edist (u k) (u (k + 1)) ^ 2 ≤
      ENNReal.ofReal (2 * τ * (1 + Real.exp (8 * n * τ / τ₀)) * (c - m + r ^ 2 / τ₀)) := by
  obtain ⟨-, -, h⟩ := toReal_sq_le_and_sum_le hτ h4 hm hu hc hr n
  have hstep : ∀ k, edist (u k) (u (k + 1)) ^ 2 =
      ENNReal.ofReal ((edist (u k) (u (k + 1))).toReal ^ 2) := fun k ↦ by
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (edist_ne_top_of_mem_moreauYosidaResolvent (hu k))]
  simp_rw [hstep]
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
  exact ENNReal.ofReal_le_ofReal h

/-- The bound `c - m + r² / τ₀` of the a priori estimates is nonnegative. -/
private theorem sub_add_sq_div_nonneg (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀)
    (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) {c : ℝ} (hc : φ (u 0) ≤ c)
    {r : ℝ≥0} (hr : edist (u 0) x₀ ≤ r) : 0 ≤ c - m + r ^ 2 / τ₀ := by
  have h := (toReal_sq_le_and_sum_le hτ h4 hm hu hc hr 0).2.1
  have hpos : (0 : ℝ) < 2 * τ₀ * Real.exp (8 * (0 : ℕ) * τ / τ₀) :=
    mul_pos (mul_pos two_pos (NNReal.coe_pos.2 (lt_of_lt_of_le (by positivity) h4)))
      (Real.exp_pos _)
  exact (mul_nonneg_iff_of_pos_left hpos).1 ((sq_nonneg _).trans h)

/-- Along a sequence with steps of finite length,
`d(u i, u j)² ≤ (j - i) ∑_{k < N} d(u k, u (k + 1))²` for `i ≤ j ≤ N`, by the triangle and
Cauchy–Schwarz inequalities. -/
private theorem toReal_edist_sq_le_mul_sum (hfin : ∀ k, edist (u k) (u (k + 1)) ≠ ⊤) {i j N : ℕ}
    (hij : i ≤ j) (hjN : j ≤ N) :
    (edist (u i) (u j)).toReal ^ 2 ≤
      ((j - i : ℕ) : ℝ) * ∑ k ∈ Finset.range N, (edist (u k) (u (k + 1))).toReal ^ 2 := by
  have h1 : (edist (u i) (u j)).toReal ≤
      ∑ k ∈ Finset.Ico i j, (edist (u k) (u (k + 1))).toReal := by
    rw [← ENNReal.toReal_sum fun k _ ↦ hfin k]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun k _ ↦ hfin k) (edist_le_Ico_sum_edist u hij)
  calc (edist (u i) (u j)).toReal ^ 2
      ≤ (∑ k ∈ Finset.Ico i j, (edist (u k) (u (k + 1))).toReal) ^ 2 := by gcongr
    _ ≤ (Finset.Ico i j).card * ∑ k ∈ Finset.Ico i j, (edist (u k) (u (k + 1))).toReal ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ ((j - i : ℕ) : ℝ) * ∑ k ∈ Finset.range N, (edist (u k) (u (k + 1))).toReal ^ 2 := by
        rw [Nat.card_Ico]
        gcongr
        exact fun k hk ↦ Finset.mem_range.2 ((Finset.mem_Ico.1 hk).2.trans_le hjN)

/-- Between times `s ≤ t`, the index `⌈t / τ⌉₊` of the piecewise constant interpolant advances by
at most `(t - s) / τ + 1`. -/
private theorem natCast_ceil_sub_ceil_mul_le (hτ : 0 < τ) {s t : ℝ} (hst : s ≤ t) :
    ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : ℝ) * τ ≤ t - s + τ := by
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  rcases le_total ⌈t / τ⌉₊ ⌈s / τ⌉₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_mul]
    linarith
  rcases lt_or_ge t 0 with ht | ht
  · have : ⌈t / τ⌉₊ = 0 := Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg ht.le hτ'.le)
    rw [this, Nat.zero_sub, Nat.cast_zero, zero_mul]
    linarith
  have h1 := Nat.ceil_lt_add_one (div_nonneg ht hτ'.le)
  have h2 := Nat.le_ceil (s / τ)
  rw [Nat.cast_sub h, sub_mul]
  have e1 : (⌈t / τ⌉₊ : ℝ) * τ ≤ t + τ := by
    have := (mul_lt_mul_of_pos_right h1 hτ').le
    rwa [add_mul, div_mul_cancel₀ _ hτ'.ne', one_mul] at this
  have e2 : s ≤ (⌈s / τ⌉₊ : ℝ) * τ := by
    have := mul_le_mul_of_nonneg_right h2 hτ'.le
    rwa [div_mul_cancel₀ _ hτ'.ne'] at this
  linarith

/-- The elapsed time `⌈T / τ⌉₊ τ` up to a time `T ≥ 0` is less than `T + τ`. -/
private theorem natCast_ceil_mul_lt (hτ : 0 < τ) {T : ℝ} (hT : 0 ≤ T) :
    (⌈T / τ⌉₊ : ℝ) * τ < T + τ := by
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hT hτ'.le)) hτ'
  rwa [add_mul, div_mul_cancel₀ _ hτ'.ne', one_mul] at this

/-- Up to a time `T ≥ 0`, the exponential growth factor of the a priori estimates is at most
`e^{8T/τ₀ + 2}`, uniformly in the time step `τ ≤ τ₀ / 4`. -/
private theorem exp_le_exp_add_two (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (hn : n ≤ ⌈T / τ⌉₊) :
    Real.exp (8 * n * τ / τ₀) ≤ Real.exp (8 * T / τ₀ + 2) := by
  have hτ₀ : (0 : ℝ) < τ₀ := NNReal.coe_pos.2 (lt_of_lt_of_le (by positivity) h4)
  have h4' : (4 * τ : ℝ) ≤ τ₀ := by exact_mod_cast h4
  have hnτ : (n : ℝ) * τ < T + τ :=
    lt_of_le_of_lt (by gcongr) (natCast_ceil_mul_lt hτ hT)
  gcongr
  rw [div_add' _ _ _ hτ₀.ne', div_le_div_iff_of_pos_right hτ₀]
  nlinarith

/-- **Uniform estimate for the piecewise constant interpolant.** Under the hypotheses of
`TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent`, the piecewise constant interpolant of a
minimizing movement sequence is `1/2`-Hölder continuous up to an error of the order of the time
step: for times `s, t ≤ T` with `T ≥ 0`,
`d(ū s, ū t)² ≤ (|t - s| + τ) · 2 (1 + e^{8T/τ₀ + 2}) (c - m + r² / τ₀)`.
The constant does not depend on `τ ≤ τ₀ / 4`. -/
theorem edist_piecewiseConstantInterpolant_le (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀)
    (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) {c : ℝ} (hc : φ (u 0) ≤ c)
    {r : ℝ≥0} (hr : edist (u 0) x₀ ≤ r) {T s t : ℝ} (hT : 0 ≤ T) (hs : s ≤ T) (ht : t ≤ T) :
    edist (piecewiseConstantInterpolant τ u s) (piecewiseConstantInterpolant τ u t) ≤
      ENNReal.ofReal √((|t - s| + τ) *
        (2 * (1 + Real.exp (8 * T / τ₀ + 2)) * (c - m + r ^ 2 / τ₀))) := by
  wlog hst : s ≤ t generalizing s t
  · rw [edist_comm, abs_sub_comm]
    exact this ht hs (le_of_not_ge hst)
  have hτ' : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hfin : ∀ k, edist (u k) (u (k + 1)) ≠ ⊤ :=
    fun k ↦ edist_ne_top_of_mem_moreauYosidaResolvent (hu k)
  set N := ⌈T / τ⌉₊
  set H := c - m + r ^ 2 / τ₀
  have hij : ⌈s / τ⌉₊ ≤ ⌈t / τ⌉₊ := Nat.ceil_mono (by gcongr)
  have hjN : ⌈t / τ⌉₊ ≤ N := Nat.ceil_mono (by gcongr)
  have hH : 0 ≤ H := sub_add_sq_div_nonneg hτ h4 hm hu hc hr
  have hsum := (toReal_sq_le_and_sum_le hτ h4 hm hu hc hr N).2.2
  have hexp := exp_le_exp_add_two hτ h4 hT le_rfl
  have hidx := natCast_ceil_sub_ceil_mul_le hτ hst
  have key : (edist (u ⌈s / τ⌉₊) (u ⌈t / τ⌉₊)).toReal ^ 2 ≤
      (|t - s| + τ) * (2 * (1 + Real.exp (8 * T / τ₀ + 2)) * H) := by
    rw [abs_of_nonneg (sub_nonneg.2 hst)]
    calc (edist (u ⌈s / τ⌉₊) (u ⌈t / τ⌉₊)).toReal ^ 2
        ≤ ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : ℝ) *
            (2 * τ * (1 + Real.exp (8 * N * τ / τ₀)) * H) :=
          (toReal_edist_sq_le_mul_sum hfin hij hjN).trans (by gcongr)
      _ = ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : ℝ) * τ * (2 * (1 + Real.exp (8 * N * τ / τ₀)) * H) := by
          ring
      _ ≤ (t - s + τ) * (2 * (1 + Real.exp (8 * T / τ₀ + 2)) * H) := by gcongr
  have hfin' : edist (u ⌈s / τ⌉₊) (u ⌈t / τ⌉₊) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨(toReal_sq_le_and_sum_le hτ h4 hm hu hc hr _).1,
      (toReal_sq_le_and_sum_le hτ h4 hm hu hc hr _).1⟩) (edist_triangle_right _ _ x₀)
  rw [piecewiseConstantInterpolant_def, piecewiseConstantInterpolant_def,
    ← ENNReal.ofReal_toReal hfin']
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.abs_le_sqrt key))

/-- **Uniform bound for the piecewise constant interpolant.** Under the hypotheses of
`TauCeti.edist_sq_le_of_forall_mem_moreauYosidaResolvent`, up to a time `T ≥ 0` the piecewise
constant interpolant of a minimizing movement sequence stays within distance
`√(2τ₀ e^{8T/τ₀ + 2} (c - m + r² / τ₀))` of `x₀`, uniformly in the time step `τ ≤ τ₀ / 4`. -/
theorem edist_piecewiseConstantInterpolant_le_of_le (hτ : 0 < τ) (h4 : 4 * τ ≤ τ₀)
    (hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀)
    (hu : ∀ n, u (n + 1) ∈ moreauYosidaResolvent φ τ (u n)) {c : ℝ} (hc : φ (u 0) ≤ c)
    {r : ℝ≥0} (hr : edist (u 0) x₀ ≤ r) {T t : ℝ} (hT : 0 ≤ T) (ht : t ≤ T) :
    edist (piecewiseConstantInterpolant τ u t) x₀ ≤
      ENNReal.ofReal √(2 * τ₀ * Real.exp (8 * T / τ₀ + 2) * (c - m + r ^ 2 / τ₀)) := by
  obtain ⟨hdist, h, -⟩ := toReal_sq_le_and_sum_le hτ h4 hm hu hc hr ⌈t / τ⌉₊
  have hH := sub_add_sq_div_nonneg hτ h4 hm hu hc hr
  have hexp := exp_le_exp_add_two hτ h4 hT (Nat.ceil_mono (by gcongr) : ⌈t / τ⌉₊ ≤ ⌈T / τ⌉₊)
  rw [piecewiseConstantInterpolant_def, ← ENNReal.ofReal_toReal hdist]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.abs_le_sqrt (h.trans (by gcongr))))

end Estimates

section GeneralizedMinimizingMovement

variable {X : Type*} [PseudoEMetricSpace X] {φ : X → EReal}

/-- A curve `u` is a *generalized minimizing movement* for the energy `φ` starting from `x`, with
respect to an auxiliary convergence `y_n ⇀ y` given by the filters `l y`, if it is a pointwise
limit of piecewise constant interpolants of minimizing movement sequences with time steps
tending to `0`. Precisely, there are time steps `τ k > 0` with `τ k → 0` and sequences `U k`, each
term `U k (n + 1)` a resolvent step of time `τ k` from `U k n`, whose initial points have energy
bounded above and stay at bounded distance from `x`, such that `u 0 = x` and the interpolants
converge, `ū_k(t) ⇀ u t`, at every time `t ≥ 0`. In particular the initial points converge,
`U k 0 ⇀ x`. Only the values of `u` on `[0, ∞)` matter. -/
def IsGeneralizedMinimizingMovement (l : X → Filter X) (φ : X → EReal) (x : X) (u : ℝ → X) :
    Prop :=
  ∃ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X), (∀ k, 0 < τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
    (∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n)) ∧
    (∃ c : ℝ, ∀ k, φ (U k 0) ≤ c) ∧ (∃ R : ℝ≥0, ∀ k, edist (U k 0) x ≤ R) ∧
    u 0 = x ∧ ∀ t, 0 ≤ t →
      Tendsto (fun k ↦ piecewiseConstantInterpolant (τ k) (U k) t) atTop (l (u t))

/-- The defining property of a generalized minimizing movement. -/
theorem isGeneralizedMinimizingMovement_iff {l : X → Filter X} {x : X} {u : ℝ → X} :
    IsGeneralizedMinimizingMovement l φ x u ↔
      ∃ (τ : ℕ → ℝ≥0) (U : ℕ → ℕ → X), (∀ k, 0 < τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
        (∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n)) ∧
        (∃ c : ℝ, ∀ k, φ (U k 0) ≤ c) ∧ (∃ R : ℝ≥0, ∀ k, edist (U k 0) x ≤ R) ∧
        u 0 = x ∧ ∀ t, 0 ≤ t →
          Tendsto (fun k ↦ piecewiseConstantInterpolant (τ k) (U k) t) atTop (l (u t)) :=
  Iff.rfl

/-- A generalized minimizing movement starting from `x` is at `x` at time `0`. -/
theorem IsGeneralizedMinimizingMovement.apply_zero {l : X → Filter X} {x : X} {u : ℝ → X}
    (h : IsGeneralizedMinimizingMovement l φ x u) : u 0 = x :=
  let ⟨_, _, _, _, _, _, _, h0, _⟩ := h
  h0

end GeneralizedMinimizingMovement

section EMetricSpace

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {τ₀ : ℝ≥0} {x₀ : X} {l : X → Filter X}

/-- `√(a K) = √K · a ^ (1/2)` in the form used by `HolderOnWith`. -/
private theorem ofReal_sqrt_mul_eq {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) :
    ENNReal.ofReal √(a * K) =
      ((Real.toNNReal √K : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal a ^ (((1 / 2 : ℝ≥0)) : ℝ) := by
  rw [ENNReal.ofReal_rpow_of_nonneg ha (by positivity), ENNReal.ofReal_coe_nnreal.symm.trans
    (by rw [Real.coe_toNNReal _ (Real.sqrt_nonneg K)]), ← ENNReal.ofReal_mul (Real.sqrt_nonneg K),
    mul_comm a, Real.sqrt_mul hK, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    Real.sqrt_eq_rpow a]

/-- **Compactness of the minimizing movement scheme** (Ambrosio–Gigli–Savaré, Proposition 2.2.3).
Let `l y` be the filter of an auxiliary convergence `y_n ⇀ y` on `X` such that

* the distance is jointly sequentially lower semicontinuous for `⇀`;
* every sequence of finite diameter along which `φ` is bounded above by a real number has a
  `⇀`-convergent subsequence;

and let `φ` be coercive: `φ_{τ₀}(x₀) > -∞` for a time step `τ₀ > 0`. Let `U k` be minimizing
movement sequences with time steps `τ k → 0`, whose initial points `U k 0 ⇀ x` have energy at most
`c` and stay at distance at most `R` from a point `x` at finite distance from `x₀`. Then a
subsequence of the piecewise constant interpolants converges at every time to a curve `u` with
`u 0 = x`, and `u` is `1/2`-Hölder continuous on every interval `[0, T]`. -/
theorem exists_strictMono_tendsto_piecewiseConstantInterpolant
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    (hcpt : ∀ (c : ℝ) ⦃v : ℕ → X⦄, Metric.ediam (range v) ≠ ⊤ → (∀ n, φ (v n) ≤ c) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (l y))
    (hτ₀ : 0 < τ₀) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) {τ : ℕ → ℝ≥0} (hτ : ∀ k, 0 < τ k)
    (hτ0 : Tendsto τ atTop (𝓝 0)) {U : ℕ → ℕ → X}
    (hU : ∀ k n, U k (n + 1) ∈ moreauYosidaResolvent φ (τ k) (U k n)) {c : ℝ}
    (hc : ∀ k, φ (U k 0) ≤ c) {x : X} {R : ℝ≥0} (hR : ∀ k, edist (U k 0) x ≤ R)
    (hx₀ : edist x x₀ ≠ ⊤) (hx : Tendsto (fun k ↦ U k 0) atTop (l x)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ u : ℝ → X, u 0 = x ∧
      (∀ t, Tendsto (fun k ↦ piecewiseConstantInterpolant (τ (ψ k)) (U (ψ k)) t) atTop
        (l (u t))) ∧
      ∀ T, ∃ C : ℝ≥0, HolderOnWith C (1 / 2) u (Icc 0 T) := by
  -- A real lower bound `m` for `φ_{τ₀}(x₀)`, and an index `K` past which `4 τ k ≤ τ₀`.
  set m := (moreauYosida φ τ₀ x₀).toReal
  have hm : (m : EReal) ≤ moreauYosida φ τ₀ x₀ := EReal.coe_toReal_le h₀
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hτ0.eventually (Iic_mem_nhds (by positivity :
    (0 : ℝ≥0) < τ₀ / 4)))
  have h4 : ∀ k, 4 * τ (k + K) ≤ τ₀ := fun k ↦ by
    have := hK (k + K) (Nat.le_add_left K k)
    rw [le_div_iff₀' (by norm_num : (0 : ℝ≥0) < 4)] at this
    exact this
  -- The initial points stay within `r = R + d(x, x₀)` of `x₀`.
  set r : ℝ≥0 := R + (edist x x₀).toNNReal
  have hr : ∀ k, edist (U k 0) x₀ ≤ r := fun k ↦ by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hx₀]
    exact (edist_triangle _ x _).trans (add_le_add_left (hR k) _)
  set H := c - m + r ^ 2 / τ₀
  -- The interpolants of the shifted sequences, and the constants of the uniform estimates.
  set v : ℕ → ℝ → X := fun k ↦ piecewiseConstantInterpolant (τ (k + K)) (U (k + K))
  set C : ℝ → ℝ := fun T ↦ 2 * (1 + Real.exp (8 * T / τ₀ + 2)) * H
  have hH : 0 ≤ H := sub_add_sq_div_nonneg (hτ _) (h4 0) hm (hU _) (hc _) (hr _)
  have hC : ∀ T, 0 ≤ C T := fun T ↦ by positivity
  have hest : ∀ k {T s t : ℝ}, 0 ≤ T → s ≤ T → t ≤ T →
      edist (v k s) (v k t) ≤ ENNReal.ofReal √((|t - s| + τ (k + K)) * C T) :=
    fun k _ _ _ hT hs ht ↦ edist_piecewiseConstantInterpolant_le (hτ _) (h4 k) hm (hU _) (hc _)
      (hr _) hT hs ht
  have hlim : ∀ (T s t : ℝ) {ψ : ℕ → ℕ}, Tendsto ψ atTop atTop →
      Tendsto (fun k ↦ ENNReal.ofReal √((|t - s| + τ (ψ k + K)) * C T)) atTop
        (𝓝 (ENNReal.ofReal √(|t - s| * C T))) := fun T s t ψ hψ ↦ by
    have hτψ : Tendsto (fun k ↦ (τ (ψ k + K) : ℝ)) atTop (𝓝 0) :=
      NNReal.tendsto_coe.2 (hτ0.comp (tendsto_atTop_mono (fun k ↦ Nat.le_add_right (ψ k) K) hψ))
    simpa using ENNReal.tendsto_ofReal (((hτψ.const_add |t - s|).mul_const (C T)).sqrt)
  -- At a fixed time the interpolants are bounded and have energy at most `c`.
  have hcpt' : ∀ t (ψ : ℕ → ℕ), StrictMono ψ → ∃ y, ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
      Tendsto (fun k ↦ v (ψ (ψ' k)) t) atTop (l y) := by
    intro t ψ hψ
    set T := max t 0
    have hball : ∀ k, edist (v (ψ k) t) x₀ ≤
        ENNReal.ofReal √(2 * τ₀ * Real.exp (8 * T / τ₀ + 2) * H) := fun k ↦
      edist_piecewiseConstantInterpolant_le_of_le (hτ _) (h4 _) hm (hU _) (hc _) (hr _)
        (le_max_right t 0) (le_max_left t 0)
    have hdiam : Metric.ediam (range fun k ↦ v (ψ k) t) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := 2 * ENNReal.ofReal √(2 * τ₀ *
        Real.exp (8 * T / τ₀ + 2) * H)) (by finiteness) (Metric.ediam_le ?_)
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [two_mul]
      exact (edist_triangle_right _ _ x₀).trans (add_le_add (hball i) (hball j))
    obtain ⟨y, ψ', hψ', hy⟩ := hcpt c hdiam fun k ↦
      (antitone_comp_of_forall_mem_moreauYosidaResolvent (hU _) (Nat.zero_le _)).trans (hc _)
    exact ⟨y, ψ', hψ', hy⟩
  -- Asymptotic equicontinuity: `limsup_k d(v k s, v k t) ≤ √(|t - s| C)` near `t`.
  have hequi : ∀ t, Tendsto (fun s ↦ limsup (fun k ↦ edist (v k s) (v k t)) atTop) (𝓝 t)
      (𝓝 0) := by
    intro t
    set T := |t| + 1
    have hbd : ∀ᶠ s in 𝓝 t, limsup (fun k ↦ edist (v k s) (v k t)) atTop ≤
        ENNReal.ofReal √(|t - s| * C T) := by
      filter_upwards [Ioo_mem_nhds (sub_one_lt t) (lt_add_one t)] with s hs
      have hsT : s ≤ T := by linarith [hs.2, le_abs_self t]
      have htT : t ≤ T := by linarith [le_abs_self t]
      calc limsup (fun k ↦ edist (v k s) (v k t)) atTop
          ≤ limsup (fun k ↦ ENNReal.ofReal √((|t - s| + τ (id k + K)) * C T)) atTop :=
            limsup_le_limsup (Eventually.of_forall fun k ↦
              hest k (by positivity) hsT htT)
        _ = ENNReal.ofReal √(|t - s| * C T) := (hlim T s t tendsto_id).limsup_eq
    have hg : Tendsto (fun s ↦ ENNReal.ofReal √(|t - s| * C T)) (𝓝 t) (𝓝 0) := by
      have : Continuous fun s ↦ ENNReal.ofReal √(|t - s| * C T) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      simpa using this.tendsto t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall fun _ ↦ zero_le) hbd
  -- The pointwise Arzelà–Ascoli theorem applies to the interpolants.
  obtain ⟨ψ, hψ, u, -, hconv⟩ := exists_strictMono_forall_tendsto_of_limsup_edist hd
    (v := v) hcpt' hequi
  refine ⟨fun k ↦ ψ k + K, hψ.add_const K, u, ?_, hconv, fun T ↦ ?_⟩
  · -- The limit at time `0` is the limit `x` of the initial points.
    have h := hd (hconv 0) (hx.comp (tendsto_atTop_mono (fun k ↦ Nat.le_add_right (ψ k) K)
      hψ.tendsto_atTop))
    simp only [v, piecewiseConstantInterpolant_zero, Function.comp_apply,
      edist_self, liminf_const] at h
    exact edist_le_zero.1 h
  · -- The uniform estimate passes to the limit.
    refine ⟨Real.toNNReal √(C T), fun s hs t ht ↦ ?_⟩
    have hT : 0 ≤ T := hs.1.trans hs.2
    calc edist (u s) (u t) ≤ liminf (fun k ↦ edist (v (ψ k) s) (v (ψ k) t)) atTop :=
          hd (hconv s) (hconv t)
      _ ≤ liminf (fun k ↦ ENNReal.ofReal √((|t - s| + τ (ψ k + K)) * C T)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k ↦ hest _ hT hs.2 ht.2)
      _ = ENNReal.ofReal √(|t - s| * C T) := (hlim T s t hψ.tendsto_atTop).liminf_eq
      _ = _ := by rw [ofReal_sqrt_mul_eq (abs_nonneg _) (hC T), edist_dist, Real.dist_eq,
          abs_sub_comm]

/-- **Existence of generalized minimizing movements** (Ambrosio–Gigli–Savaré, Proposition 2.2.3).
Let `l y` be the filter of an auxiliary convergence `y_n ⇀ y` on `X`, under which constant
sequences converge, such that

* the distance is jointly sequentially lower semicontinuous for `⇀`;
* `φ` is sequentially lower semicontinuous for `⇀` along sequences of finite diameter;
* every sequence of finite diameter along which `φ` is bounded above by a real number has a
  `⇀`-convergent subsequence;

and let `φ` be coercive: `φ_{τ₀}(x₀) > -∞` for a time step `τ₀ > 0`. Then from every point `x` of
finite energy at finite distance from `x₀` starts a generalized minimizing movement, and it can be
chosen `1/2`-Hölder continuous on every interval `[0, T]`. For `l = 𝓝` the hypotheses on `l` hold
for a lower semicontinuous energy on a proper metric space. -/
theorem exists_isGeneralizedMinimizingMovement (hl : ∀ y, pure y ≤ l y)
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    (hφ : ∀ ⦃v : ℕ → X⦄ ⦃y : X⦄, Metric.ediam (range v) ≠ ⊤ → Tendsto v atTop (l y) →
      φ y ≤ liminf (fun n ↦ φ (v n)) atTop)
    (hcpt : ∀ (c : ℝ) ⦃v : ℕ → X⦄, Metric.ediam (range v) ≠ ⊤ → (∀ n, φ (v n) ≤ c) →
      ∃ y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (v ∘ ψ) atTop (l y))
    (hτ₀ : 0 < τ₀) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) {x : X} (hx₀ : edist x x₀ ≠ ⊤)
    (hφx : φ x ≠ ⊤) :
    ∃ u : ℝ → X, IsGeneralizedMinimizingMovement l φ x u ∧
      ∀ T, ∃ C : ℝ≥0, HolderOnWith C (1 / 2) u (Icc 0 T) := by
  -- Time steps `τ k = τ₀ / (k + 2)`, all smaller than `τ₀`, and minimizing movement sequences
  -- `U k` from `x` with these time steps.
  set τ : ℕ → ℝ≥0 := fun k ↦ τ₀ / ((k + 2 : ℕ) : ℝ≥0)
  have hτ : ∀ k, 0 < τ k := fun k ↦ div_pos hτ₀ (by positivity)
  have hττ₀ : ∀ k, τ k < τ₀ := fun k ↦ div_lt_self hτ₀ (by norm_cast; omega)
  have hτ0 : Tendsto τ atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat τ₀).comp (tendsto_add_atTop_nat 2)
  have hd' : ∀ (z : X) ⦃v : ℕ → X⦄ ⦃y : X⦄, Tendsto v atTop (l y) →
      edist z y ≤ liminf (fun n ↦ edist z (v n)) atTop := fun z _ _ hv ↦
    hd (tendsto_const_pure.mono_right (hl z)) hv
  choose U hU0 hU using fun k ↦
    exists_forall_mem_moreauYosidaResolvent hd' hφ hcpt (hτ k) (hττ₀ k) hx₀ h₀
  have hc : ∀ k, φ (U k 0) ≤ (φ x).toReal := fun k ↦ by
    rw [hU0 k]
    exact EReal.le_coe_toReal hφx
  have hR : ∀ k, edist (U k 0) x ≤ (0 : ℝ≥0) := fun k ↦ by simp [hU0 k]
  have hx : Tendsto (fun k ↦ U k 0) atTop (l x) := by
    simpa only [hU0] using tendsto_const_pure.mono_right (hl x)
  obtain ⟨ψ, hψ, u, hu0, hconv, hhol⟩ := exists_strictMono_tendsto_piecewiseConstantInterpolant
    hd hcpt hτ₀ h₀ hτ hτ0 hU hc hR hx₀ hx
  exact ⟨u, isGeneralizedMinimizingMovement_iff.2 ⟨τ ∘ ψ, U ∘ ψ, fun k ↦ hτ _,
    hτ0.comp hψ.tendsto_atTop, fun k ↦ hU _, ⟨_, fun k ↦ hc _⟩, ⟨0, fun k ↦ hR _⟩, hu0,
    fun t _ ↦ hconv t⟩, hhol⟩

end EMetricSpace

/-- **Existence of generalized minimizing movements in a proper space.** In a proper metric space,
from every point of finite energy starts a generalized minimizing movement of a lower
semicontinuous energy with `φ_{τ₀}(x₀) > -∞` for some `τ₀ > 0`, for the convergence of the metric,
and it is `1/2`-Hölder continuous on every interval `[0, T]`. This is
`TauCeti.exists_isGeneralizedMinimizingMovement` with `l = 𝓝`. -/
theorem exists_isGeneralizedMinimizingMovement_of_lowerSemicontinuous {X : Type*} [MetricSpace X]
    [ProperSpace X] {φ : X → EReal} {τ₀ : ℝ≥0} {x₀ x : X} (hφ : LowerSemicontinuous φ)
    (hτ₀ : 0 < τ₀) (h₀ : moreauYosida φ τ₀ x₀ ≠ ⊥) (hφx : φ x ≠ ⊤) :
    ∃ u : ℝ → X, IsGeneralizedMinimizingMovement 𝓝 φ x u ∧
      ∀ T, ∃ C : ℝ≥0, HolderOnWith C (1 / 2) u (Icc 0 T) :=
  exists_isGeneralizedMinimizingMovement pure_le_nhds
    (fun _ _ _ _ hv hw ↦ (hv.edist hw).liminf_eq.ge)
    (fun _ y _ hv ↦ (hφ.le_liminf y).trans hv.liminf_le_liminf_comp)
    (fun _ _ hv _ ↦
      let ⟨a, _, ψ, hψ, h⟩ := tendsto_subseq_of_bounded (Metric.isBounded_iff_ediam_ne_top.2 hv)
        fun n ↦ mem_range_self n
      ⟨a, ψ, hψ, h⟩)
    hτ₀ h₀ (edist_ne_top x x₀) hφx

end TauCeti
