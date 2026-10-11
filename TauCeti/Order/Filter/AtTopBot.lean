/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Diagonal indices along `atTop`

If for every `k` a property `P k n` holds for all large `n`, then an index `κ n` tending to
infinity can be chosen so slowly that `P (κ n) n` holds for all large `n`
(`TauCeti.exists_tendsto_atTop_of_forall_eventually`). This is the diagonal step of constructions
that must meet countably many eventual requirements at once with a single sequence, such as a
recovery sequence built from a countable neighbourhood basis. It complements Mathlib's
`Filter.extraction_forall_of_eventually`, which meets the requirements along a subsequence
instead.

The second result is the diagonal extraction of a subsequence: if each of countably many sequences
`x n` has, along every subsequence, a further subsequence converging to some limit, then one
subsequence makes all of them converge at once (`TauCeti.exists_strictMono_forall_tendsto`). This
is the diagonal step of compactness arguments for countably many coordinates, such as the
Arzelà–Ascoli theorem.
-/

public section

open Filter

namespace TauCeti

/-- If for every `k` the property `P k n` holds for all large `n`, then there is an index `κ n`
tending to infinity with `P (κ n) n` for all large `n`. -/
theorem exists_tendsto_atTop_of_forall_eventually {P : ℕ → ℕ → Prop}
    (h : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧ ∀ᶠ n in atTop, P (κ n) n := by
  classical
  choose N hN using fun k ↦ eventually_atTop.1 (h k)
  -- `κ n` is the largest `k ≤ n` such that `N j ≤ n` for every `j ≤ k`.
  refine ⟨fun n ↦ Nat.findGreatest (fun k ↦ ∀ j ≤ k, N j ≤ n) n, tendsto_atTop.2 fun k ↦ ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop k, (eventually_all_finset (Finset.range (k + 1))).2
      fun j _ ↦ eventually_ge_atTop (N j)] with n hkn hn
    exact Nat.le_findGreatest hkn fun j hj ↦ hn j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    refine hN _ _ (Nat.findGreatest_spec (P := fun k ↦ ∀ j ≤ k, N j ≤ n) (Nat.zero_le n)
      (fun j hj ↦ ?_) _ le_rfl)
    rwa [Nat.le_zero.1 hj]

/-- **Diagonal extraction of a subsequence.** Let `x n` be countably many sequences in `α`, each of
which has, along every subsequence, a further subsequence converging to `l y` for some `y`. Then a
single subsequence `θ` makes all of them converge: `x n (θ k) → l (y n)` for every `n`. The
filters `l y` are arbitrary, so the convergence need not be that of a topology. -/
theorem exists_strictMono_forall_tendsto {α : Type*} {x : ℕ → ℕ → α} {l : α → Filter α}
    (h : ∀ n (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ y, ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ Tendsto (fun k ↦ x n (ψ (ψ' k))) atTop (l y)) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ y : ℕ → α, ∀ n, Tendsto (fun k ↦ x n (θ k)) atTop (l (y n)) := by
  -- `next n ψ` is a further subsequence of `ψ` along which `x n` converges, to `y n ψ`.
  have h' : ∀ n (ψ : {ψ : ℕ → ℕ // StrictMono ψ}), ∃ ψ' : {ψ : ℕ → ℕ // StrictMono ψ}, ∃ y,
      Tendsto (fun k ↦ x n (ψ.1 (ψ'.1 k))) atTop (l y) := fun n ψ ↦
    let ⟨y, ψ', hψ', hy⟩ := h n ψ.1 ψ.2
    ⟨⟨ψ', hψ'⟩, y, hy⟩
  choose next y hy using h'
  -- `Ψ n` is the subsequence obtained after the first `n` extractions.
  let Ψ : ℕ → {ψ : ℕ → ℕ // StrictMono ψ} := fun n ↦ Nat.rec ⟨id, strictMono_id⟩
    (fun n ψ ↦ ⟨ψ.1 ∘ (next n ψ).1, ψ.2.comp (next n ψ).2⟩) n
  have hΨ : ∀ n, (Ψ (n + 1)).1 = (Ψ n).1 ∘ (next n (Ψ n)).1 := fun n ↦ rfl
  -- Each later subsequence is a subsequence of every earlier one.
  have hsub : ∀ n j, ∃ σ : ℕ → ℕ, StrictMono σ ∧ (Ψ (n + j)).1 = (Ψ n).1 ∘ σ := by
    intro n j
    induction j with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ j ih =>
      obtain ⟨σ, hσ, he⟩ := ih
      exact ⟨σ ∘ (next (n + j) (Ψ (n + j))).1, hσ.comp (next _ _).2, by
        rw [← add_assoc, hΨ, he, Function.comp_assoc]⟩
  choose σ hσ hΨσ using hsub
  -- The diagonal subsequence `θ k = Ψ (k + 1) k`.
  refine ⟨fun k ↦ (Ψ (k + 1)).1 k, strictMono_nat_of_lt_succ fun k ↦ ?_,
    fun n ↦ y n (Ψ n), fun n ↦ ?_⟩
  · rw [congrFun (hΨσ (k + 1) 1) (k + 1), Function.comp_apply]
    exact (Ψ (k + 1)).2 ((Nat.lt_succ_self k).trans_le ((hσ (k + 1) 1).id_le _))
  · -- For `k ≥ n`, `θ k = Ψ (n + 1) (σ (n + 1) (k - n) k)`, and `σ (n + 1) (k - n) k ≥ k`.
    have hm : Tendsto (fun k ↦ σ (n + 1) (k - n) k) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ (hσ _ _).id_le k) tendsto_id
    refine ((hy n (Ψ n)).comp hm).congr' ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    have := congrFun (hΨσ (n + 1) (k - n)) k
    rw [show n + 1 + (k - n) = k + 1 by omega] at this
    simp only [Function.comp_apply, this, hΨ]

end TauCeti
