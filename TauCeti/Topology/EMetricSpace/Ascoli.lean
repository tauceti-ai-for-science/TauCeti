/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import TauCeti.Order.Filter.AtTopBot

/-!
# A pointwise Arzelà–Ascoli theorem for an auxiliary convergence

Let `v k : T → X` be a sequence of maps from a separable topological space `T` into an extended
metric space `X`, typically curves with `T` an interval of times. The maps need not be continuous;
instead they are *asymptotically equicontinuous*: for every `t`,

`limsup_k d(v k s, v k t) → 0` as `s → t`.

Suppose moreover that at every `t`, every subsequence of `(v k t)` has a further subsequence
converging for an auxiliary notion of convergence `y_n ⇀ y` on `X`, along which the distance is
jointly lower semicontinuous: `y_n ⇀ y` and `z_n ⇀ z` imply `d(y, z) ≤ liminf d(y_n, z_n)`. Then
some subsequence converges at every `t` to a continuous limit `u : T → X`
(`TauCeti.exists_strictMono_forall_tendsto_of_limsup_edist`).

The auxiliary convergence can be weaker than that of the metric, such as the weak topology of a
Hilbert space or the narrow topology on a Wasserstein space, whose bounded sets are not relatively
compact for the metric; the limit is nevertheless continuous for the metric. This is the
compactness theorem behind the convergence of the minimizing movement scheme for gradient flows,
where `v k` are the piecewise constant interpolants of discrete solutions with time steps tending
to `0`: these are discontinuous, but equicontinuous up to an error that vanishes with the time
step.

The auxiliary convergence is a map `l : X → Filter X`, a sequence `w` converging to `y` when
`Tendsto w atTop (l y)`; for a topology `σ` on `X` take `l = @nhds X σ`. No property of `l` is
used beyond the joint lower semicontinuity of the distance.

## Main results

* `TauCeti.exists_strictMono_forall_tendsto_of_limsup_edist`: the pointwise Arzelà–Ascoli
  theorem.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 3, Proposition 3.3.1.
-/

public section

open Filter Topology
open scoped ENNReal

namespace TauCeti

variable {T X : Type*} [EMetricSpace X] {l : X → Filter X}

/-- Along subsequences of a sequence of maps that converges at the points `q n`, a limit `z` at
`t` lies within `limsup_k d(v k (q n), v k t)` of the limit `y n` at `q n`. -/
private theorem edist_le_limsup_of_tendsto
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    {v : ℕ → T → X} {s t : T} {θ χ : ℕ → ℕ} (hθ : StrictMono θ) (hχ : StrictMono χ) {y z : X}
    (hy : Tendsto (fun k ↦ v (θ k) s) atTop (l y))
    (hz : Tendsto (fun k ↦ v (θ (χ k)) t) atTop (l z)) :
    edist y z ≤ limsup (fun k ↦ edist (v k s) (v k t)) atTop :=
  calc edist y z
      ≤ liminf (fun k ↦ edist (v (θ (χ k)) s) (v (θ (χ k)) t)) atTop :=
        hd (hy.comp hχ.tendsto_atTop) hz
    _ ≤ limsup (fun k ↦ edist (v (θ (χ k)) s) (v (θ (χ k)) t)) atTop := liminf_le_limsup
    _ ≤ limsup (fun k ↦ edist (v k s) (v k t)) atTop :=
        (hθ.comp hχ).tendsto_atTop.limsup_comp_le_limsup (u := fun k ↦ edist (v k s) (v k t))

/-- **A pointwise Arzelà–Ascoli theorem** (Ambrosio–Gigli–Savaré, Proposition 3.3.1). Let
`v k : T → X` be maps from a separable space into an extended metric space, and `l y` the filter
of an auxiliary convergence `y_n ⇀ y` on `X` for which the distance is jointly lower
semicontinuous. If at every `t` every subsequence of `(v k t)` has a `⇀`-convergent subsequence,
and `limsup_k d(v k s, v k t) → 0` as `s → t`, then some subsequence `v (ψ k)` converges at every
`t` to `u t`, for a continuous `u : T → X`. -/
theorem exists_strictMono_forall_tendsto_of_limsup_edist [TopologicalSpace T]
    [TopologicalSpace.SeparableSpace T]
    (hd : ∀ ⦃v w : ℕ → X⦄ ⦃y z : X⦄, Tendsto v atTop (l y) → Tendsto w atTop (l z) →
      edist y z ≤ liminf (fun n ↦ edist (v n) (w n)) atTop)
    {v : ℕ → T → X}
    (hcpt : ∀ t (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ y, ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ Tendsto (fun k ↦ v (ψ (ψ' k)) t) atTop (l y))
    (hequi : ∀ t, Tendsto (fun s ↦ limsup (fun k ↦ edist (v k s) (v k t)) atTop) (𝓝 t) (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ u : T → X, Continuous u ∧
      ∀ t, Tendsto (fun k ↦ v (ψ k) t) atTop (l (u t)) := by
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨id, strictMono_id, isEmptyElim, continuous_of_discreteTopology, isEmptyElim⟩
  -- A diagonal subsequence `θ` converges at the points of a dense sequence `q`.
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq T
  obtain ⟨θ, hθ, y, hy⟩ := exists_strictMono_forall_tendsto (x := fun n k ↦ v k (q n)) (l := l)
    fun n ψ hψ ↦ hcpt (q n) ψ hψ
  -- Two limits at `t` along subsequences of `θ` coincide: both lie within
  -- `limsup_k d(v k (q n), v k t)` of `y n`, which is small for `q n` near `t`.
  have huniq : ∀ t {χ χ' : ℕ → ℕ}, StrictMono χ → StrictMono χ' → ∀ {z z' : X},
      Tendsto (fun k ↦ v (θ (χ k)) t) atTop (l z) →
      Tendsto (fun k ↦ v (θ (χ' k)) t) atTop (l z') → z = z' := by
    intro t χ χ' hχ hχ' z z' hz hz'
    refine edist_eq_zero.1 (le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
      zero_le)
    have hε' : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.half_pos (ENNReal.coe_pos.2 hε).ne'
    obtain ⟨n, hn⟩ := hq.mem_nhds ((hequi t).eventually (gt_mem_nhds hε'))
    rw [zero_add]
    calc edist z z' ≤ edist (y n) z + edist (y n) z' := edist_triangle_left _ _ _
      _ ≤ (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 := by
        gcongr
        · exact (edist_le_limsup_of_tendsto hd hθ hχ (hy n) hz).trans hn.le
        · exact (edist_le_limsup_of_tendsto hd hθ hχ' (hy n) hz').trans hn.le
      _ = ε := ENNReal.add_halves _
  -- At every `t` some subsequence of `θ` converges, to `u t`, and then all of `θ` does.
  choose u ψ hψ hu using fun t ↦ hcpt t θ hθ
  have hconv : ∀ t, Tendsto (fun k ↦ v (θ k) t) atTop (l (u t)) := fun t ↦
    tendsto_of_subseq_tendsto fun ns hns ↦ by
      obtain ⟨φ, hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
      obtain ⟨z, ψ', hψ', hz⟩ := hcpt t (θ ∘ ns ∘ φ) (hθ.comp hnsφ)
      exact ⟨φ ∘ ψ', huniq t (hnsφ.comp hψ') (hψ t) hz (hu t) ▸ hz⟩
  refine ⟨θ, hθ, u, continuous_iff_continuousAt.2 fun t ↦ ?_, hconv⟩
  -- Continuity: `d(u s, u t) ≤ limsup_k d(v k s, v k t) → 0` as `s → t`.
  refine tendsto_iff_edist_tendsto_0.2 <| tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (hequi t) (fun _ ↦ zero_le) fun s ↦ ?_
  simpa using edist_le_limsup_of_tendsto hd hθ strictMono_id (hconv s) (hconv t)

end TauCeti
