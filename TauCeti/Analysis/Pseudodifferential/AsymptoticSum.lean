/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.FrequencyCutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Borel asymptotic summation of symbols

Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and let `aⱼ` be symbols of order `mⱼ`
(`TauCeti.Symbol n V W (m j)`). Borel's construction produces a single symbol `b` of order `m₀`
with `b - ∑_{j < N} aⱼ` of order `m_N` for every `N`: an *asymptotic sum* `b ∼ ∑ⱼ aⱼ`. This is
how a formal series of symbols, for example the full symbol of a composition or of a parametrix,
is realised by an actual symbol.

The sum is `b(x, ξ) = ∑ⱼ χ(ξ / tⱼ) aⱼ(x, ξ)` for a frequency cutoff `χ` and radii `tⱼ → ∞`.
Each truncation `χ(ξ / t) a(x, ξ)` of a symbol `a` of order `m` vanishes for `‖ξ‖ ≤ t` and is
bounded in every symbol seminorm of an order `m' ≥ m` by a constant times `t ^ (m - m')`, uniformly
in `t ≥ 1` (`TauCeti.Symbol.exists_norm_mixedDeriv_cutoff_smul_le`). For `m < m'` it is therefore
arbitrarily small in each of these seminorms once `t` is large
(`TauCeti.Symbol.eventually_norm_mixedDeriv_cutoff_smul_le`). Choosing `tⱼ` large enough for the
finitely many seminorms indexed by `j` makes the tail of the series small in every seminorm, while
the series is locally finite in `ξ`, so its sum is smooth.

## Main results

* `TauCeti.Symbol.exists_norm_mixedDeriv_cutoff_smul_le`: the seminorm estimate for the
  high-frequency truncations `χ(ξ / t) a(x, ξ)`, uniform in `t ≥ 1`.
* `TauCeti.Symbol.eventually_norm_mixedDeriv_cutoff_smul_le`: for `m < m'` these truncations
  become arbitrarily small in the seminorms of order `m'` as `t → ∞`.
* `TauCeti.exists_norm_mixedDeriv_le_of_lt_norm`: for a smooth function, symbol estimates at large
  frequencies imply symbol estimates at all frequencies.
* `TauCeti.Symbol.exists_asymptoticSum`: Borel asymptotic summation.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3.
* R. Melrose, *Introduction to Microlocal Analysis*, Chapter 2, Proposition 2.3.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I.
-/

public section

noncomputable section

open Filter Metric Set Finset
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

section Weight

/-- At frequencies `‖ξ‖ ≥ t > 0` the weight of order `m ≤ m'` is at most `t ^ (m - m')` times the
weight of order `m'`. -/
private theorem rpow_weight_le_of_le_norm {t : ℝ} (ht : 0 < t) {ξ : CoordinateSpace n}
    (hξ : t ≤ ‖ξ‖) {m m' : ℝ} (hm : m ≤ m') (s : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ ((m - s) / 2) ≤ t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - s) / 2) := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [show (m - s) / 2 = (m - m') / 2 + (m' - s) / 2 by ring, Real.rpow_add hpos]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hpos.le _)
  have ht2 : t ^ (m - m') = (t ^ 2) ^ ((m - m') / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  rw [ht2]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)

/-- Raising the order of the weight by a natural number `i` multiplies it by `⟨ξ⟩ ^ i`. -/
private theorem rpow_weight_sub_natCast_sub {k i : ℕ} (hik : i ≤ k) (ξ : CoordinateSpace n)
    (m : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ ((m - ((k - i : ℕ) : ℝ)) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2) * √(1 + ‖ξ‖ ^ 2) ^ i := by
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [Nat.cast_sub hik, show (m - (k - i)) / 2 = (m - k) / 2 + 1 / 2 * (i : ℝ) by ring,
    Real.rpow_add hpos, Real.sqrt_eq_rpow, Real.rpow_mul_natCast hpos.le]

end Weight

section Large

/-- For a smooth function of a position and a frequency, symbol estimates on the frequencies
`‖ξ‖ > R` give symbol estimates on all frequencies, with a larger constant: on the compact set of
positions in `K` and frequencies in the closed ball of radius `R` the mixed derivative is
bounded and the weight is bounded below. -/
theorem exists_norm_mixedDeriv_le_of_lt_norm {f : CoordinateSpace n × CoordinateSpace n → A}
    (hf : ContDiff ℝ ∞ f) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n))
    {s R C : ℝ}
    (h : ∀ x ∈ K, ∀ ξ, R < ‖ξ‖ → ‖mixedDeriv α β f x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (s / 2)) :
    ∃ C', 0 ≤ C' ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β f x ξ‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (hK.prod (isCompact_closedBall (0 : CoordinateSpace n) R))
    (hf.mixedDeriv α β).continuous.continuousOn
  have hR0 : 0 ≤ (1 + R ^ 2) ^ (|s| / 2) := by positivity
  refine ⟨max C 0 + max M 0 * (1 + R ^ 2) ^ (|s| / 2),
    add_nonneg (le_max_right _ _) (mul_nonneg (le_max_right _ _) hR0), fun x hx ξ => ?_⟩
  have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (s / 2) := Real.rpow_nonneg hpos.le _
  rcases lt_or_ge R ‖ξ‖ with hξ | hξ
  · refine (h x hx ξ hξ).trans (mul_le_mul_of_nonneg_right ?_ hw)
    exact (le_max_left _ _).trans (le_add_of_nonneg_right (mul_nonneg (le_max_right _ _) hR0))
  · have hR : 1 + ‖ξ‖ ^ 2 ≤ 1 + R ^ 2 := by nlinarith [norm_nonneg ξ]
    have h1 : 1 ≤ (1 + R ^ 2) ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) :=
      calc (1 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ (|s| / 2 + s / 2) :=
            Real.one_le_rpow (by nlinarith [norm_nonneg ξ]) (by linarith [neg_abs_le s])
        _ = (1 + ‖ξ‖ ^ 2) ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) := Real.rpow_add hpos _ _
        _ ≤ (1 + R ^ 2) ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hpos.le hR (by positivity)) hw
    calc ‖mixedDeriv α β f x ξ‖ ≤ max M 0 :=
          (hM (x, ξ) (Set.mk_mem_prod hx (mem_closedBall_zero_iff.2 hξ))).trans (le_max_left _ _)
      _ ≤ max M 0 * ((1 + R ^ 2) ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2)) :=
          le_mul_of_one_le_right (le_max_right _ _) h1
      _ ≤ (max C 0 + max M 0 * (1 + R ^ 2) ^ (|s| / 2)) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (le_max_right _ _)) hw

end Large

namespace Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

section Cutoff

variable (χ : FrequencyCutoff (CoordinateSpace n))

/-- The iterated derivatives of the dilated cutoff `ξ ↦ χ(ξ / t)` are those of `χ` at `ξ / t`,
scaled by `t⁻ⁱ`. -/
private theorem iteratedFDeriv_cutoff_dilate (t : ℝ) (i : ℕ) (ξ : CoordinateSpace n) :
    iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ = t⁻¹ ^ i • iteratedFDeriv ℝ i χ (t⁻¹ • ξ) :=
  congrFun (iteratedFDeriv_comp_const_smul _ ((χ.contDiff (n := ⊤)).of_le
    (by exact_mod_cast le_top))) ξ

private theorem norm_iteratedFDeriv_cutoff_dilate {t : ℝ} (ht : 0 < t) (i : ℕ)
    (ξ : CoordinateSpace n) :
    ‖iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ‖ = ‖iteratedFDeriv ℝ i χ (t⁻¹ • ξ)‖ * t⁻¹ ^ i := by
  rw [iteratedFDeriv_cutoff_dilate, norm_smul, norm_pow, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
    mul_comm]

private theorem iteratedFDeriv_cutoff_dilate_eq_zero_of_norm_le {t : ℝ} (ht : 0 < t) (i : ℕ)
    {ξ : CoordinateSpace n} (hξ : ‖ξ‖ ≤ t) :
    iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ = 0 := by
  have h : ‖t⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht, mul_one]
    exact hξ
  rw [iteratedFDeriv_cutoff_dilate, χ.iteratedFDeriv_eq_zero_of_norm_le_one i h, smul_zero]

private theorem iteratedFDeriv_cutoff_dilate_eq_zero_of_le_norm {t : ℝ} (ht : 0 < t) {i : ℕ}
    (hi : i ≠ 0) {ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ = 0 := by
  have h : 2 ≤ ‖t⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
    linarith
  rw [iteratedFDeriv_cutoff_dilate, χ.iteratedFDeriv_eq_zero_of_two_le_norm hi h, smul_zero]

/-- The Fréchet derivatives in the frequency of the position derivatives `∂_x^α a(x, ξ)` of a
symbol of order `m` satisfy the estimates of order `m` lowered by their order. -/
private theorem exists_norm_iteratedFDeriv_coordinateDeriv_le {m : ℝ} (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α : List (Fin n)) (l : ℕ) :
    ∃ G, 0 ≤ G ∧ ∀ x ∈ K, ∀ ξ,
      ‖iteratedFDeriv ℝ l (fun η => coordinateDeriv α (fun y => a.coefficient (y, η)) x) ξ‖ ≤
        G * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by
  choose C hC0 hC using fun w : Fin l → Fin n => a.exists_bound K hK α (List.ofFn w)
  refine ⟨∑ w, C w, Finset.sum_nonneg fun w _ => hC0 w, fun x hx ξ => ?_⟩
  have hg : ContDiff ℝ ∞ fun η => coordinateDeriv α (fun y => a.coefficient (y, η)) x :=
    (a.contDiff_coefficient.coordinateDeriv_fst α).comp (contDiff_prodMk_right x)
  refine (norm_iteratedFDeriv_le_sum_coordinateDeriv (contDiff_infty.1 hg l) ξ).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [← mixedDeriv_eq_coordinateDeriv_snd a.contDiff_coefficient]
  simpa using hC w x hx ξ

/-- **High-frequency truncations of a symbol.** For a symbol `a` of order `m`, a frequency
cutoff `χ` and an order `m' ≥ m`, the truncations `χ(ξ / t) a(x, ξ)` satisfy the symbol estimates
of order `m'` with constants `C t ^ (m - m')`, uniformly in `t ≥ 1`. -/
theorem exists_norm_mixedDeriv_cutoff_smul_le {m m' : ℝ} (a : Symbol n V W m) (hm : m ≤ m')
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ t, 1 ≤ t → ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
        C * t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  -- After commuting the position derivatives past the cutoff, the Leibniz rule bounds the
  -- frequency derivatives by a sum over `i ≤ |β|` of `‖∂ⁱ(χ(·/t))‖ ‖∂^(|β|-i) ∂_x^α a‖`. The `i`-th
  -- term vanishes for `‖ξ‖ ≤ t`, and for `i ≠ 0` also for `‖ξ‖ ≥ 2t`; on the remaining
  -- frequencies the factor `t⁻ⁱ` from the dilation absorbs the growth `⟨ξ⟩ⁱ ≤ (3t)ⁱ`.
  choose G hG0 hG using exists_norm_iteratedFDeriv_coordinateDeriv_le a hK α
  choose B hB using fun i => χ.exists_bound_iteratedFDeriv i
  set k := β.length
  have hc0 : ∀ i, 0 ≤ (k.choose i : ℝ) * (max (B i) 0 * (3 ^ i * G (k - i))) := fun i =>
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_max_right _ _) (mul_nonneg (by positivity)
      (hG0 _)))
  refine ⟨∑ i ∈ range (k + 1), (k.choose i : ℝ) * (max (B i) 0 * (3 ^ i * G (k - i))),
    Finset.sum_nonneg fun i _ => hc0 i, fun t ht x hx ξ => ?_⟩
  have ht0 : 0 < t := by linarith
  have hφ : ContDiff ℝ ∞ fun η : CoordinateSpace n => χ (t⁻¹ • η) :=
    χ.contDiff.comp (contDiff_const_smul _)
  have hg : ContDiff ℝ ∞ fun η => coordinateDeriv α (fun y => a.coefficient (y, η)) x :=
    (a.contDiff_coefficient.coordinateDeriv_fst α).comp (contDiff_prodMk_right x)
  have hF : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n =>
      χ (t⁻¹ • p.2) • a.coefficient p :=
    (hφ.comp contDiff_snd).smul a.contDiff_coefficient
  -- The cutoff only depends on the frequency, so it commutes with the position derivatives.
  have heq : mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ =
      coordinateDeriv β (fun η => χ (t⁻¹ • η) •
        coordinateDeriv α (fun y => a.coefficient (y, η)) x) ξ := by
    rw [mixedDeriv_eq_coordinateDeriv_snd hF]
    congr 1
    funext η
    exact congrFun (coordinateDeriv_const_smul α
      (contDiff_infty.1 (a.contDiff_coefficient.comp (contDiff_prodMk_left η)) _)
      (χ (t⁻¹ • η))) x
  rw [heq]
  refine (norm_coordinateDeriv_le β (contDiff_infty.1 (hφ.smul hg) _) ξ).trans ?_
  refine (norm_iteratedFDeriv_smul_le hφ hg ξ (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hRHS : 0 ≤ (k.choose i : ℝ) * (max (B i) 0 * (3 ^ i * G (k - i))) * t ^ (m - m') *
      (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2) :=
    mul_nonneg (mul_nonneg (hc0 i) (Real.rpow_nonneg ht0.le _)) (by positivity)
  -- The derivatives of the dilated cutoff vanish for `‖ξ‖ ≤ t`, and for `‖ξ‖ ≥ 2t` unless
  -- `i = 0`.
  by_cases hξt : ‖ξ‖ ≤ t
  · rw [iteratedFDeriv_cutoff_dilate_eq_zero_of_norm_le χ ht0 i hξt, norm_zero, mul_zero,
      zero_mul]
    exact hRHS
  by_cases h2 : i ≠ 0 ∧ 2 * t ≤ ‖ξ‖
  · rw [iteratedFDeriv_cutoff_dilate_eq_zero_of_le_norm χ ht0 h2.1 h2.2, norm_zero, mul_zero,
      zero_mul]
    exact hRHS
  have hsq : √(1 + ‖ξ‖ ^ 2) ^ i ≤ (3 * t) ^ i := by
    rcases not_and_or.1 h2 with hi0 | hlt
    · rw [not_not.1 hi0, pow_zero, pow_zero]
    · refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ i
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [norm_nonneg ξ]
  have hφb : ‖iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ‖ ≤ max (B i) 0 * t⁻¹ ^ i :=
    (norm_iteratedFDeriv_cutoff_dilate χ ht0 i ξ).trans_le
      (mul_le_mul_of_nonneg_right ((hB i _).trans (le_max_left _ _)) (by positivity))
  have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - ((k - i : ℕ) : ℝ)) / 2) ≤
      t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2) * (3 * t) ^ i := by
    rw [rpow_weight_sub_natCast_sub hik]
    exact mul_le_mul (rpow_weight_le_of_le_norm ht0 (not_le.1 hξt).le hm _) hsq
      (by positivity) (mul_nonneg (Real.rpow_nonneg ht0.le _) (by positivity))
  have hgb := (hG (k - i) x hx ξ).trans (mul_le_mul_of_nonneg_left hw (hG0 _))
  have h3 : t⁻¹ ^ i * (3 * t) ^ i = 3 ^ i := by
    rw [← mul_pow, inv_mul_eq_div, mul_div_assoc, div_self ht0.ne', mul_one]
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun η => χ (t⁻¹ • η)) ξ‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun η => coordinateDeriv α (fun y => a.coefficient (y, η)) x)
          ξ‖ ≤ (k.choose i : ℝ) * (max (B i) 0 * t⁻¹ ^ i) *
        (G (k - i) * (t ^ (m - m') * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2) * (3 * t) ^ i)) := by
        gcongr
    _ = (k.choose i : ℝ) * (max (B i) 0 * (3 ^ i * G (k - i))) * t ^ (m - m') *
        (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2) := by
        rw [← h3]
        ring

/-- For `m < m'`, the high-frequency truncations `χ(ξ / t) a(x, ξ)` of a symbol `a` of order `m`
become arbitrarily small in each symbol seminorm of order `m'` as `t → ∞`. -/
theorem eventually_norm_mixedDeriv_cutoff_smul_le {m m' : ℝ} (a : Symbol n V W m) (hm : m < m')
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • a.coefficient p) x ξ‖ ≤
        ε * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  obtain ⟨C, -, hC⟩ := exists_norm_mixedDeriv_cutoff_smul_le χ a hm.le hK α β
  have hlim : Tendsto (fun t : ℝ => C * t ^ (m - m')) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (sub_pos.2 hm)).const_mul C
    simpa only [neg_sub, mul_zero] using this
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with t hCt ht x hx ξ
  exact (hC t ht x hx ξ).trans (mul_le_mul_of_nonneg_right hCt.le (by positivity))

end Cutoff

section Sum

variable {f : ℕ → CoordinateSpace n × CoordinateSpace n → A}

omit [NormedSpace ℝ A] in
/-- A series of functions whose `j`-th term vanishes for `‖ξ‖ ≤ j` is, near every point, a finite
sum. -/
private theorem tsum_eventuallyEq (hvan : ∀ (j : ℕ) (p : CoordinateSpace n × CoordinateSpace n),
    ‖p.2‖ ≤ j → f j p = 0) (J : ℕ) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    (fun p => ∑' i, f (i + J) p) =ᶠ[𝓝 p₀]
      fun p => ∑ i ∈ range (⌈‖p₀.2‖⌉₊ + 1), f (i + J) p := by
  have hU : {p : CoordinateSpace n × CoordinateSpace n | ‖p.2‖ < ‖p₀.2‖ + 1} ∈ 𝓝 p₀ :=
    (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const).mem_nhds (by simp)
  filter_upwards [hU] with p hp
  refine tsum_eq_sum fun i hi => hvan (i + J) p ?_
  have hi' : (⌈‖p₀.2‖⌉₊ + 1 : ℝ) ≤ i := by
    exact_mod_cast not_lt.1 (Finset.mem_range.not.1 hi)
  have hceil := Nat.le_ceil ‖p₀.2‖
  have hp' : ‖p.2‖ < ‖p₀.2‖ + 1 := hp
  push_cast
  linarith [(J.cast_nonneg : (0 : ℝ) ≤ J)]

private theorem contDiff_tsum (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hvan : ∀ (j : ℕ) (p : CoordinateSpace n × CoordinateSpace n), ‖p.2‖ ≤ j → f j p = 0) (J : ℕ) :
    ContDiff ℝ ∞ fun p => ∑' i, f (i + J) p :=
  contDiff_iff_contDiffAt.2 fun p₀ =>
    (ContDiff.sum fun i _ => hf (i + J)).contDiffAt.congr_of_eventuallyEq
      (tsum_eventuallyEq hvan J p₀)

private theorem mixedDeriv_tsum (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hvan : ∀ (j : ℕ) (p : CoordinateSpace n × CoordinateSpace n), ‖p.2‖ ≤ j → f j p = 0) (J : ℕ)
    (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p => ∑' i, f (i + J) p) x ξ =
      ∑ i ∈ range (⌈‖ξ‖⌉₊ + 1), mixedDeriv α β (f (i + J)) x ξ :=
  ((tsum_eventuallyEq hvan J (x, ξ)).mixedDeriv α β).trans
    (mixedDeriv_sum _ (fun i _ => hf (i + J)) α β x ξ)

end Sum

/-- The tails `∑ᵢ χ(ξ / t_{i+J}) a_{i+J}(x, ξ)` of the Borel series satisfy the symbol estimates of
order `m J`, provided the `j`-th truncation is smaller than `2⁻ʲ` in the seminorms of every order
`m_N > mⱼ` with `N ≤ j`, over `‖x‖ ≤ j` and words of length at most `j`. -/
private theorem exists_norm_mixedDeriv_tsum_le (χ : FrequencyCutoff (CoordinateSpace n))
    {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot) (a : ∀ j, Symbol n V W (m j))
    {t : ℕ → ℝ} (ht1 : ∀ j, 1 ≤ t j) {f : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hfdef : ∀ j, f j = fun p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p)
    (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (hvan : ∀ (j : ℕ) (p : CoordinateSpace n × CoordinateSpace n), ‖p.2‖ ≤ j → f j p = 0)
    (hsmall : ∀ j : ℕ, ∀ α ∈ {l : List (Fin n) | l.length ≤ j},
      ∀ β ∈ {l : List (Fin n) | l.length ≤ j}, ∀ N ∈ {N | N ≤ j ∧ m j < m N},
        ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ, ‖mixedDeriv α β (f j) x ξ‖ ≤
          (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2))
    (J : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖mixedDeriv α β (fun p => ∑' i, f (i + J) p) x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m J - β.length) / 2) := by
  obtain ⟨r₀, hr₀⟩ := hK.isBounded.subset_closedBall (0 : CoordinateSpace n)
  obtain ⟨j₂, hj₂⟩ := (hm'.eventually (eventually_lt_atBot (m J))).exists
  set j₁ := max (max J j₂) (max (max α.length β.length) ⌈r₀⌉₊)
  choose C hC0 hC using fun i =>
    exists_norm_mixedDeriv_cutoff_smul_le χ (a (i + J)) (hm (Nat.le_add_left J i)) hK α β
  refine ⟨∑ i ∈ range j₁, C i + 2,
    add_nonneg (Finset.sum_nonneg fun i _ => hC0 i) zero_le_two, fun x hx ξ => ?_⟩
  have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ ((m J - β.length) / 2) := by positivity
  -- Terms beyond `j₁` are bounded by `2⁻ⁱ`, the finitely many others by their own estimates.
  have hterm : ∀ i, ‖mixedDeriv α β (f (i + J)) x ξ‖ ≤
      ((if i < j₁ then C i else 0) + (1 / 2) ^ i) * (1 + ‖ξ‖ ^ 2) ^ ((m J - β.length) / 2) := by
    intro i
    by_cases hi : j₁ ≤ i + J
    · have hx' : x ∈ closedBall (0 : CoordinateSpace n) ((i + J : ℕ) : ℝ) := by
        refine closedBall_subset_closedBall ?_ (hr₀ hx)
        have hr : ⌈r₀⌉₊ ≤ i + J := (le_max_right _ _).trans ((le_max_right _ _).trans hi)
        calc r₀ ≤ ⌈r₀⌉₊ := Nat.le_ceil r₀
          _ ≤ ((i + J : ℕ) : ℝ) := by exact_mod_cast hr
      have hj₁ : max J j₂ ≤ i + J := (le_max_left _ _).trans hi
      have hαβ : max α.length β.length ≤ i + J :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans hi
      refine (hsmall (i + J) α ((le_max_left _ _).trans hαβ) β ((le_max_right _ _).trans hαβ) J
        ⟨Nat.le_add_left J i, (hm ((le_max_right _ _).trans hj₁)).trans_lt hj₂⟩ x hx' ξ).trans
        (mul_le_mul_of_nonneg_right ?_ hw)
      refine (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right i J)).trans ?_
      refine le_add_of_nonneg_left ?_
      split_ifs
      exacts [hC0 i, le_rfl]
    · have hi' : i < j₁ := by omega
      rw [hfdef (i + J)]
      refine (hC i (t (i + J)) (ht1 _) x hx ξ).trans ?_
      simp only [hi', ↓reduceIte, add_mul]
      refine le_add_of_le_of_nonneg ?_ (mul_nonneg (by positivity) hw)
      refine mul_le_mul_of_nonneg_right ?_ hw
      exact mul_le_of_le_one_right (hC0 i) (Real.rpow_le_one_of_one_le_of_nonpos (ht1 _)
        (sub_nonpos.2 (hm (Nat.le_add_left J i))))
  rw [mixedDeriv_tsum hf hvan J α β x ξ]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans ?_)
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_right (add_le_add ?_ (sum_geometric_two_le _)) hw
  rw [← Finset.sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => Finset.mem_range.2
    (Finset.mem_filter.1 hi).2) fun i _ _ => hC0 i

/-- **Borel asymptotic summation.** Let `m₀ ≥ m₁ ≥ ⋯` be real orders tending to `-∞` and `aⱼ` a
symbol of order `mⱼ` for every `j`. Then there is a symbol `b` of order `m₀` such that for every
`N` the difference `b - ∑_{j < N} aⱼ` is a symbol of order `m_N`. -/
theorem exists_asymptoticSum {m : ℕ → ℝ} (hm : Antitone m) (hm' : Tendsto m atTop atBot)
    (a : ∀ j, Symbol n V W (m j)) :
    ∃ b : Symbol n V W (m 0), ∀ N, ∃ r : Symbol n V W (m N),
      ∀ p, b.coefficient p - ∑ j ∈ range N, (a j).coefficient p = r.coefficient p := by
  classical
  let χ : FrequencyCutoff (CoordinateSpace n) :=
    FrequencyCutoff.ofContDiffBump ⟨1, 2, one_pos, one_lt_two⟩ le_rfl le_rfl
  -- The radius `tⱼ` is at least `j + 1`, and makes the `j`-th truncation smaller than `2⁻ʲ` in the
  -- seminorms of every order `m_N > mⱼ` with `N ≤ j`, over `‖x‖ ≤ j` and words of length `≤ j`.
  have hP : ∀ j : ℕ, ∀ᶠ t in atTop, (j : ℝ) + 1 ≤ t ∧
      ∀ α ∈ {l : List (Fin n) | l.length ≤ j}, ∀ β ∈ {l : List (Fin n) | l.length ≤ j},
        ∀ N ∈ {N | N ≤ j ∧ m j < m N}, ∀ x ∈ closedBall (0 : CoordinateSpace n) j, ∀ ξ,
          ‖mixedDeriv α β (fun p => χ (t⁻¹ • p.2) • (a j).coefficient p) x ξ‖ ≤
            (1 / 2) ^ j * (1 + ‖ξ‖ ^ 2) ^ ((m N - β.length) / 2) := by
    intro j
    refine (eventually_ge_atTop _).and ?_
    rw [eventually_all_finite (List.finite_length_le _ _)]
    intro α _
    rw [eventually_all_finite (List.finite_length_le _ _)]
    intro β _
    rw [eventually_all_finite ((Set.finite_le_nat j).subset
      (t := {N | N ≤ j ∧ m j < m N}) fun N hN => hN.1)]
    intro N hN
    exact eventually_norm_mixedDeriv_cutoff_smul_le χ (a j) hN.2 (isCompact_closedBall _ _) α β
      (by positivity)
  choose t ht using fun j => (hP j).exists
  have ht1 : ∀ j, 1 ≤ t j := fun j => le_trans (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    (ht j).1
  set f : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun j p => χ ((t j)⁻¹ • p.2) • (a j).coefficient p with hfdef
  have hf : ∀ j, ContDiff ℝ ∞ (f j) := fun j =>
    ((χ.contDiff.comp (contDiff_const_smul _)).comp contDiff_snd).smul (a j).contDiff_coefficient
  have hvan : ∀ (j : ℕ) (p : CoordinateSpace n × CoordinateSpace n), ‖p.2‖ ≤ j → f j p = 0 := by
    intro j p hp
    have h : ‖(t j)⁻¹ • p.2‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by linarith [ht1 j])),
        inv_mul_le_iff₀ (by linarith [ht1 j]), mul_one]
      linarith [(ht j).1]
    simp [hfdef, χ.apply_eq_zero_of_norm_le_one h]
  -- The tails `∑_{i} f (i + J)` are symbols of order `m J`.
  have htail J (K : Set (CoordinateSpace n)) (hK : IsCompact K) (α β : List (Fin n)) :=
    exists_norm_mixedDeriv_tsum_le χ hm hm' a ht1 (fun j => rfl) hf hvan (fun j => (ht j).2) J hK
      α β
  let T : ∀ J, Symbol n V W (m J) := fun J =>
    ⟨fun p => ∑' i, f (i + J) p, contDiff_tsum hf hvan J, htail J⟩
  have hT : ∀ J p, (T J).coefficient p = ∑' i, f (i + J) p := fun _ _ => rfl
  refine ⟨T 0, fun N => ?_⟩
  have hsplit : ∀ p, (T 0).coefficient p - ∑ j ∈ range N, (a j).coefficient p =
      ∑ j ∈ range N, (f j p - (a j).coefficient p) + (T N).coefficient p := by
    intro p
    have hs : Summable fun j => f j p :=
      summable_of_ne_finset_zero (s := range (⌈‖p.2‖⌉₊ + 1)) fun j hj => hvan j p (by
        have hj' : ((⌈‖p.2‖⌉₊ + 1 : ℕ) : ℝ) ≤ j := by
          exact_mod_cast not_lt.1 (Finset.mem_range.not.1 hj)
        push_cast at hj'
        linarith [Nat.le_ceil ‖p.2‖])
    rw [hT, hT]
    simp only [add_zero, ← hs.sum_add_tsum_nat_add N, Finset.sum_sub_distrib]
    abel
  have hr : ContDiff ℝ ∞ fun p => (T 0).coefficient p - ∑ j ∈ range N, (a j).coefficient p :=
    (T 0).contDiff_coefficient.sub (ContDiff.sum fun j _ => (a j).contDiff_coefficient)
  refine ⟨⟨fun p => (T 0).coefficient p - ∑ j ∈ range N, (a j).coefficient p, hr,
    fun K hK α β => ?_⟩, fun p => rfl⟩
  -- At frequencies beyond `2 tⱼ` for all `j < N` the remainder agrees with the tail `T N`.
  obtain ⟨C, -, hC⟩ := (T N).exists_bound K hK α β
  refine exists_norm_mixedDeriv_le_of_lt_norm hr hK α β (R := 2 * ∑ j ∈ range N, t j) (C := C)
    fun x hx ξ hξ => ?_
  have hU : {p : CoordinateSpace n × CoordinateSpace n | 2 * ∑ j ∈ range N, t j < ‖p.2‖} ∈
      𝓝 (x, ξ) :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds hξ
  have heq : (fun p => (T 0).coefficient p - ∑ j ∈ range N, (a j).coefficient p) =ᶠ[𝓝 (x, ξ)]
      (T N).coefficient := by
    filter_upwards [hU] with p hp
    rw [hsplit, Finset.sum_eq_zero, zero_add]
    intro j hj
    have htj : t j ≤ ∑ j ∈ range N, t j :=
      Finset.single_le_sum (fun i _ => (zero_le_one.trans (ht1 i))) hj
    have h : 2 ≤ ‖(t j)⁻¹ • p.2‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by linarith [ht1 j])),
        le_inv_mul_iff₀ (by linarith [ht1 j])]
      have hp' : 2 * ∑ j ∈ range N, t j < ‖p.2‖ := hp
      linarith
    simp [hfdef, χ.apply_eq_one_of_two_le_norm h]
  rw [heq.mixedDeriv α β]
  exact hC x hx ξ

end Symbol

end TauCeti
