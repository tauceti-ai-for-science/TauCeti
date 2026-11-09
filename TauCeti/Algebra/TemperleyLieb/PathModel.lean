/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.QuantumGroups.QuantumInteger.Real
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Path models of the Temperley–Lieb algebras

The path model realises the Temperley–Lieb algebra `TemperleyLieb 𝕜 δ n` on the span of the
`n`-step paths on a weighted graph with vertices in `ℤ`. The weights are encoded by an amplitude
`c : ℤ → 𝕜`, the square root of the vertex weight. It is a *path amplitude* for `δ`
(`TauCeti.TemperleyLieb.IsPathAmplitude`) when at every vertex `a` of its support
`c (a - 1) ^ 2 + c (a + 1) ^ 2 = δ * c a ^ 2`, so the squared amplitudes form an eigenvector of
eigenvalue `δ` of the adjacency matrix of the support. The paths
(`TauCeti.TemperleyLieb.AmplitudePath c n`) start at `0`, move by `±1` at each step and stay in
the support of `c`.

The generator `e i` acts at the vertex `i + 1` of the paths. It kills a path whose vertices `i`
and `i + 2` differ. On the paths whose vertices `i` and `i + 2` both equal `a`, which differ only
in their vertex `i + 1 ∈ {a - 1, a + 1}`, it acts by the rank-one matrix `c a⁻² • v vᵀ` with
`v = (c (a - 1), c (a + 1))`. The neighbour condition gives `e i * e i = δ • e i`, and the zigzag
and distant commutation relations hold for every amplitude. So the matrices define an algebra map
`TauCeti.TemperleyLieb.pathRep` by the universal property `TauCeti.TemperleyLieb.lift`. For a
self-adjoint amplitude the generator matrices are Hermitian, so the path representation carries
the analytic adjoint to the conjugate transpose.

The basic amplitude is `√[t + 1]`, with `[k]` the quantum integer `TauCeti.qInt ℝ δ k`, on the
vertices `0 ≤ t < L` (`TauCeti.TemperleyLieb.qIntAmplitude`). The recurrence of the quantum
integers is the neighbour condition, provided `[1], …, [L]` are positive and `[L + 1] = 0`. This
covers the two families of positive loop values of Jones's theorem: the half-line for `δ ≥ 2`, and
the Dynkin graph `A_(m - 1)`, with vertices `0, …, m - 2`, for `δ = 2 cos (π / m)`.

## Main definitions

* `TauCeti.TemperleyLieb.IsPathAmplitude`: the neighbour condition on an amplitude.
* `TauCeti.TemperleyLieb.AmplitudePath`: the paths through the support of an amplitude.
* `TauCeti.TemperleyLieb.pathGenerator`: the matrix of a generator in the path model.
* `TauCeti.TemperleyLieb.pathRep`: the path representation.
* `TauCeti.TemperleyLieb.qIntAmplitude`: the amplitude `√[t + 1]` on the vertices `0 ≤ t < L`.

## Main results

* `TauCeti.TemperleyLieb.pathGenerator_mul_self`,
  `TauCeti.TemperleyLieb.pathGenerator_zigzag_left`,
  `TauCeti.TemperleyLieb.pathGenerator_zigzag_right`,
  `TauCeti.TemperleyLieb.pathGenerator_mul_pathGenerator_comm`: the Temperley–Lieb relations.
* `TauCeti.TemperleyLieb.pathRep_star`: the path representation of a self-adjoint amplitude
  carries the analytic adjoint to the conjugate transpose.
* `TauCeti.TemperleyLieb.isPathAmplitude_qIntAmplitude_top`,
  `TauCeti.TemperleyLieb.isPathAmplitude_qIntAmplitude_two_mul_cos`: the amplitudes `√[t + 1]`
  on the half-line for `δ ≥ 2` and on `A_(m - 1)` for `δ = 2 cos (π / m)`.

## References

* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.4–4.5, for the path
  weights `[t + 1]` on the half-line and on `A_(m - 1)`.
* H. Wenzl, *Hecke algebras of type `A_n` and subfactors*, Invent. Math. 92 (1988), 349–383.
-/

public section

open Function Matrix

namespace TauCeti.TemperleyLieb

variable {𝕜 : Type*} [Field 𝕜]

/-- A *path amplitude* for the loop value `δ` is a function `c : ℤ → 𝕜` such that at every
vertex `a` with `c a ≠ 0` the squared amplitudes of the two neighbours `a - 1` and `a + 1` add
up to `δ` times the squared amplitude of `a`. -/
def IsPathAmplitude (δ : 𝕜) (c : ℤ → 𝕜) : Prop :=
  ∀ a, c a ≠ 0 → c (a - 1) ^ 2 + c (a + 1) ^ 2 = δ * c a ^ 2

/-- A function `p : Fin (n + 1) → ℤ` is an `n`-step path through the support of `c` when it
starts at `0`, moves by `±1` at every step, and only visits vertices with nonzero amplitude. -/
structure IsAmplitudePath (c : ℤ → 𝕜) {n : ℕ} (p : Fin (n + 1) → ℤ) : Prop where
  map_zero : p 0 = 0
  abs_sub_eq_one : ∀ j k : Fin (n + 1), (j : ℕ) + 1 = k → |p k - p j| = 1
  ne_zero : ∀ j, c (p j) ≠ 0

/-- The `n`-step paths from `0` through the vertices of nonzero amplitude. -/
abbrev AmplitudePath (c : ℤ → 𝕜) (n : ℕ) : Type := {p : Fin (n + 1) → ℤ // IsAmplitudePath c p}

variable {c : ℤ → 𝕜} {n : ℕ}

/-- A path has moved at most `j` away from `0` after `j` steps. -/
private theorem IsAmplitudePath.abs_apply_le {p : Fin (n + 1) → ℤ} (hp : IsAmplitudePath c p)
    (j : Fin (n + 1)) : |p j| ≤ j := by
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero => simp [show (⟨0, hj⟩ : Fin (n + 1)) = 0 from rfl, hp.map_zero]
  | succ j ih =>
    have h := hp.abs_sub_eq_one ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    have h' := ih (by omega)
    rw [abs_le] at h' ⊢
    rw [abs_eq zero_le_one] at h
    push_cast at h' ⊢
    omega

instance : Finite (AmplitudePath c n) := by
  have : {p : Fin (n + 1) → ℤ | IsAmplitudePath c p}.Finite :=
    (Set.Finite.pi (t := fun _ ↦ Set.Icc (-(n : ℤ)) n) fun _ ↦ Set.finite_Icc _ _).subset
      fun p hp j _ ↦ by
        have hj : ((j : ℕ) : ℤ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp j.is_lt
        exact abs_le.mp ((IsAmplitudePath.abs_apply_le hp j).trans hj)
  exact this.to_subtype

noncomputable instance : Fintype (AmplitudePath c n) := Fintype.ofFinite _

/-- The two neighbours of a vertex `a` of `ℤ`. -/
private theorem mem_pair_of_abs_sub_eq_one {x a : ℤ} (h : |x - a| = 1) :
    x ∈ ({a - 1, a + 1} : Finset ℤ) := by
  rw [abs_eq zero_le_one] at h
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Resetting the vertex `k` of a path to a neighbour of the common value of its neighbours `j`
and `l`, with nonzero amplitude, gives a path again. -/
private theorem IsAmplitudePath.update {p : Fin (n + 1) → ℤ} (hp : IsAmplitudePath c p)
    {j k l : Fin (n + 1)} (hjk : (j : ℕ) + 1 = k) (hkl : (k : ℕ) + 1 = l) (hjl : p j = p l)
    {x : ℤ} (hx : x ∈ ({p j - 1, p j + 1} : Finset ℤ)) (hcx : c x ≠ 0) :
    IsAmplitudePath c (update p k x) where
  map_zero := by
    rw [update_of_ne (fun h ↦ by simp [← h] at hjk), hp.map_zero]
  abs_sub_eq_one a b hab := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    by_cases hbk : b = k
    · subst hbk
      have hak : a = j := Fin.ext (by omega)
      subst hak
      rw [update_self, update_of_ne (fun h ↦ by simp [h] at hjk)]
      rw [abs_eq zero_le_one]
      omega
    by_cases hak : a = k
    · subst hak
      have hbl : b = l := Fin.ext (by omega)
      subst hbl
      rw [update_self, update_of_ne hbk, ← hjl, abs_eq zero_le_one]
      omega
    rw [update_of_ne hbk, update_of_ne hak]
    exact hp.abs_sub_eq_one a b hab
  ne_zero a := by
    by_cases hak : a = k
    · subst hak
      rwa [update_self]
    · rw [update_of_ne hak]
      exact hp.ne_zero a

/-- The coefficient of the generator at the vertex `k`, with neighbours `j` and `l`, between two
vertex functions: nonzero only when they agree away from `k` and take the same value `a` at `j`
and `l`, in which case it is `c (q k) * c (q' k) / c a ^ 2`. -/
private def pathCoeff (c : ℤ → 𝕜) (j k l : Fin (n + 1)) (q q' : Fin (n + 1) → ℤ) : 𝕜 :=
  if (∀ m, m ≠ k → q m = q' m) ∧ q j = q l then c (q k) * c (q' k) / c (q j) ^ 2 else 0

variable (c) in
/-- The matrix of a Temperley–Lieb generator in the path model, acting at the vertex `k` of the
paths, with neighbours `j` and `l`. Its entry at the paths `p` and `p'` is nonzero only when `p`
and `p'` agree away from `k` and `p` takes the same value `a` at `j` and `l`; it is then
`c (p k) * c (p' k) / c a ^ 2`. On the two-dimensional block of paths through `a` at `j` and `l`
this is the rank-one matrix `c a⁻² • v vᵀ` with `v = (c (a - 1), c (a + 1))`. -/
def pathGenerator (j k l : Fin (n + 1)) : Matrix (AmplitudePath c n) (AmplitudePath c n) 𝕜 :=
  Matrix.of fun p p' ↦ pathCoeff c j k l p.1 p'.1

theorem pathGenerator_apply (j k l : Fin (n + 1)) (p p' : AmplitudePath c n) :
    pathGenerator c j k l p p' = if (∀ m, m ≠ k → p.1 m = p'.1 m) ∧ p.1 j = p.1 l then
      c (p.1 k) * c (p'.1 k) / c (p.1 j) ^ 2 else 0 := (rfl)

/-- Paths joined by a nonzero entry of a generator matrix agree away from its vertex. -/
private theorem forall_ne_eq_of_pathGenerator_mul_ne_zero {j k l : Fin (n + 1)}
    {p p' : AmplitudePath c n} {z : 𝕜} (h : pathGenerator c j k l p p' * z ≠ 0) :
    ∀ m, m ≠ k → p.1 m = p'.1 m := by
  by_contra hag
  simp [pathGenerator_apply, hag] at h

/-- Left multiplication by a generator matrix: the row `p` of the product is a combination of the
rows of `X` at the paths obtained from `p` by resetting the vertex `k` to one of the two
neighbours of `a = p j = p l`. The rows of `X` are given by a function `F` of the underlying vertex
functions, which is evaluated also at the vertex functions that leave the support of `c`; their
coefficient `c x` vanishes. -/
theorem pathGenerator_mul_apply {j k l : Fin (n + 1)} (hjk : (j : ℕ) + 1 = k)
    (hkl : (k : ℕ) + 1 = l) {X : Matrix (AmplitudePath c n) (AmplitudePath c n) 𝕜}
    {u : AmplitudePath c n} (F : (Fin (n + 1) → ℤ) → 𝕜) (hX : ∀ p', X p' u = F p'.1)
    (p : AmplitudePath c n) :
    (pathGenerator c j k l * X) p u = if p.1 j = p.1 l then
      c (p.1 k) / c (p.1 j) ^ 2 * ∑ x ∈ ({p.1 j - 1, p.1 j + 1} : Finset ℤ),
        c x * F (update p.1 k x) else 0 := by
  have hjk' : j ≠ k := fun h ↦ by simp [h] at hjk
  have hlk : l ≠ k := fun h ↦ by simp [h] at hkl
  rw [Matrix.mul_apply]
  simp_rw [hX]
  split_ifs with hjl
  · rw [Finset.mul_sum]
    refine Finset.sum_bij_ne_zero (fun p' _ _ ↦ p'.1 k) ?_ ?_ ?_ ?_
    · intro p' _ h
      have hag := forall_ne_eq_of_pathGenerator_mul_ne_zero h
      rw [hag j hjk']
      exact mem_pair_of_abs_sub_eq_one (p'.2.abs_sub_eq_one j k hjk)
    · intro p' _ h p'' _ h' hk
      have hag := forall_ne_eq_of_pathGenerator_mul_ne_zero h
      have hag' := forall_ne_eq_of_pathGenerator_mul_ne_zero h'
      refine Subtype.ext (funext fun m ↦ ?_)
      by_cases hm : m = k
      · subst hm; exact hk
      · rw [← hag m hm, ← hag' m hm]
    · intro x hx h
      have hcx : c x ≠ 0 := fun h0 ↦ h (by simp [h0])
      refine ⟨⟨update p.1 k x, p.2.update hjk hkl hjl hx hcx⟩, Finset.mem_univ _, ?_, ?_⟩
      · intro h0
        apply h
        rw [pathGenerator_apply, ite_eq_left ⟨fun m hm ↦ (update_of_ne hm _ _).symm, hjl⟩] at h0
        simpa [mul_assoc, mul_div_right_comm] using h0
      · simp
    · intro p' _ h
      have hag := forall_ne_eq_of_pathGenerator_mul_ne_zero h
      have hp' : p'.1 = update p.1 k (p'.1 k) :=
        eq_update_iff.mpr ⟨rfl, fun m hm ↦ (hag m hm).symm⟩
      rw [pathGenerator_apply, ite_eq_left ⟨hag, hjl⟩, ← hp']
      ring
  · refine Finset.sum_eq_zero fun p' _ ↦ ?_
    simp [pathGenerator_apply, hjl]

/-- Agreement away from `k` does not see the value at `k`. -/
private theorem forall_ne_update_eq_iff {k : Fin (n + 1)} (q q' : Fin (n + 1) → ℤ) (x : ℤ) :
    (∀ m, m ≠ k → update q k x m = q' m) ↔ ∀ m, m ≠ k → q m = q' m :=
  forall₂_congr fun m hm ↦ by rw [update_of_ne hm]

/-- Agreement away from `k` after resetting the vertex `k' ≠ k`. -/
private theorem forall_ne_update_eq_iff_of_ne {k k' : Fin (n + 1)} (h : k' ≠ k)
    (q q' : Fin (n + 1) → ℤ) (x : ℤ) :
    (∀ m, m ≠ k → update q k' x m = q' m) ↔ x = q' k' ∧ ∀ m, m ≠ k' → m ≠ k → q m = q' m := by
  rw [forall_update_iff q (fun m v ↦ m ≠ k → v = q' m)]
  simp [h]

variable {δ : 𝕜}

/-- Closing a loop multiplies a generator matrix by the loop value. -/
theorem pathGenerator_mul_self (hc : IsPathAmplitude δ c) {j k l : Fin (n + 1)}
    (hjk : (j : ℕ) + 1 = k) (hkl : (k : ℕ) + 1 = l) :
    pathGenerator c j k l * pathGenerator c j k l = δ • pathGenerator c j k l := by
  have hjk' : j ≠ k := fun h ↦ by simp [h] at hjk
  have hlk : l ≠ k := fun h ↦ by simp [h] at hkl
  ext p u
  rw [pathGenerator_mul_apply hjk hkl (fun q ↦ pathCoeff c j k l q u.1) (fun _ ↦ rfl),
    Matrix.smul_apply, pathGenerator_apply, smul_eq_mul]
  simp only [pathCoeff, update_self, update_of_ne hjk', update_of_ne hlk,
    forall_ne_update_eq_iff]
  by_cases hjl : p.1 j = p.1 l
  · by_cases hag : ∀ m, m ≠ k → p.1 m = u.1 m
    · have ha := p.2.ne_zero j
      have hcond : (∀ m, m ≠ k → p.1 m = u.1 m) ∧ p.1 j = p.1 l := ⟨hag, hjl⟩
      simp only [ite_eq_left hcond, ite_eq_left hjl]
      rw [Finset.sum_pair (by omega)]
      have h := hc _ ha
      field_simp
      linear_combination c (p.1 k) * c (u.1 k) * h
    · simp [hag]
  · simp [hjl]

/-- The coefficient at a vertex function reset at `k`. -/
private theorem pathCoeff_update_self {j k l : Fin (n + 1)} (hjk : j ≠ k) (hlk : l ≠ k)
    (q q' : Fin (n + 1) → ℤ) (x : ℤ) :
    pathCoeff c j k l (update q k x) q' = if (∀ m, m ≠ k → q m = q' m) ∧ q j = q l then
      c x * c (q' k) / c (q j) ^ 2 else 0 := by
  simp only [pathCoeff, update_self, update_of_ne hjk, update_of_ne hlk, forall_ne_update_eq_iff]

/-- The zigzag relation for the generator matrices at two adjacent vertices, with the earlier
vertex on the outside. -/
theorem pathGenerator_zigzag_left {j k l m : Fin (n + 1)} (hjk : (j : ℕ) + 1 = k)
    (hkl : (k : ℕ) + 1 = l) (hlm : (l : ℕ) + 1 = m) :
    pathGenerator c j k l * pathGenerator c k l m * pathGenerator c j k l =
      pathGenerator c j k l := by
  have hjk' : j ≠ k := fun h ↦ by simp [h] at hjk
  have hlk : l ≠ k := fun h ↦ by simp [h] at hkl
  have hmk : m ≠ k := fun h ↦ by rw [h] at hlm; omega
  have hjl : j ≠ l := fun h ↦ by rw [h] at hjk; omega
  ext p u
  rw [mul_assoc, pathGenerator_mul_apply hjk hkl (fun q ↦ if q k = q m then
      c (q l) / c (q k) ^ 2 * ∑ y ∈ ({q k - 1, q k + 1} : Finset ℤ),
        c y * pathCoeff c j k l (update q l y) u.1 else 0)
      (fun p' ↦ pathGenerator_mul_apply hkl hlm (fun q ↦ pathCoeff c j k l q u.1)
        (fun _ ↦ rfl) p'),
    pathGenerator_apply]
  by_cases ha : p.1 j = p.1 l
  swap
  · simp [ha]
  simp only [ite_eq_left ha, update_self, update_of_ne hmk, update_of_ne hlk]
  have hm : p.1 m ∈ ({p.1 j - 1, p.1 j + 1} : Finset ℤ) :=
    ha ▸ mem_pair_of_abs_sub_eq_one (p.2.abs_sub_eq_one l m hlm)
  rw [Finset.sum_eq_single_of_mem _ hm (fun x _ hx ↦ by simp [hx])]
  have hl : p.1 l ∈ ({p.1 m - 1, p.1 m + 1} : Finset ℤ) :=
    mem_pair_of_abs_sub_eq_one (by rw [abs_sub_comm]; exact p.2.abs_sub_eq_one l m hlm)
  rw [ite_eq_left rfl, Finset.sum_eq_single_of_mem _ hl (fun y _ hy ↦ ?_)]
  · rw [update_eq_self_iff.mpr (by rw [update_of_ne hlk]), pathCoeff_update_self hjk' hlk]
    have hcm := p.2.ne_zero m
    have hcl := p.2.ne_zero l
    split_ifs
    · rw [ha]
      field_simp
    · simp
  · simp [pathCoeff, update_of_ne hjl, update_of_ne hjk', ha, Ne.symm hy]

/-- The zigzag relation for the generator matrices at two adjacent vertices, with the later
vertex on the outside. -/
theorem pathGenerator_zigzag_right {j k l m : Fin (n + 1)} (hjk : (j : ℕ) + 1 = k)
    (hkl : (k : ℕ) + 1 = l) (hlm : (l : ℕ) + 1 = m) :
    pathGenerator c k l m * pathGenerator c j k l * pathGenerator c k l m =
      pathGenerator c k l m := by
  have hjk' : j ≠ k := fun h ↦ by simp [h] at hjk
  have hkl' : k ≠ l := fun h ↦ by simp [h] at hkl
  have hml : m ≠ l := fun h ↦ by simp [h] at hlm
  have hjl : j ≠ l := fun h ↦ by rw [h] at hjk; omega
  have hmk : m ≠ k := fun h ↦ by rw [h] at hlm; omega
  ext p u
  rw [mul_assoc, pathGenerator_mul_apply hkl hlm (fun q ↦ if q j = q l then
      c (q k) / c (q j) ^ 2 * ∑ x ∈ ({q j - 1, q j + 1} : Finset ℤ),
        c x * pathCoeff c k l m (update q k x) u.1 else 0)
      (fun p' ↦ pathGenerator_mul_apply hjk hkl (fun q ↦ pathCoeff c k l m q u.1)
        (fun _ ↦ rfl) p'),
    pathGenerator_apply]
  by_cases ha : p.1 k = p.1 m
  swap
  · simp [ha]
  simp only [ite_eq_left ha, update_self, update_of_ne hjl, update_of_ne hkl']
  have hj : p.1 j ∈ ({p.1 k - 1, p.1 k + 1} : Finset ℤ) :=
    mem_pair_of_abs_sub_eq_one (by rw [abs_sub_comm]; exact p.2.abs_sub_eq_one j k hjk)
  rw [Finset.sum_eq_single_of_mem _ hj (fun y _ hy ↦ by simp [Ne.symm hy])]
  have hk : p.1 k ∈ ({p.1 j - 1, p.1 j + 1} : Finset ℤ) :=
    mem_pair_of_abs_sub_eq_one (p.2.abs_sub_eq_one j k hjk)
  rw [ite_eq_left rfl, Finset.sum_eq_single_of_mem _ hk (fun x _ hx ↦ ?_)]
  · rw [update_eq_self_iff.mpr (by rw [update_of_ne hkl']), pathCoeff_update_self hkl' hml]
    have hcj := p.2.ne_zero j
    have hck := p.2.ne_zero k
    split_ifs
    · field_simp
    · simp
  · simp [pathCoeff, update_of_ne hmk, update_of_ne hml, ← ha, hx]

/-- Generator matrices at vertices at distance at least two commute. -/
theorem pathGenerator_mul_pathGenerator_comm {j k l j' k' l' : Fin (n + 1)}
    (hjk : (j : ℕ) + 1 = k) (hkl : (k : ℕ) + 1 = l) (hjk₂ : (j' : ℕ) + 1 = k')
    (hkl₂ : (k' : ℕ) + 1 = l') (hkk : (k : ℕ) + 2 ≤ k' ∨ (k' : ℕ) + 2 ≤ k) :
    pathGenerator c j k l * pathGenerator c j' k' l' =
      pathGenerator c j' k' l' * pathGenerator c j k l := by
  have hjk' : j ≠ k := fun h ↦ by simp [h] at hjk
  have hlk : l ≠ k := fun h ↦ by simp [h] at hkl
  have hjk₂' : j' ≠ k' := fun h ↦ by simp [h] at hjk₂
  have hlk₂ : l' ≠ k' := fun h ↦ by simp [h] at hkl₂
  have hkk' : k ≠ k' := fun h ↦ by rw [h] at hkk; omega
  have hjk₃ : j ≠ k' := fun h ↦ by rw [h] at hjk; omega
  have hlk₃ : l ≠ k' := fun h ↦ by rw [h] at hkl; omega
  have hjk₄ : j' ≠ k := fun h ↦ by rw [h] at hjk₂; omega
  have hlk₄ : l' ≠ k := fun h ↦ by rw [h] at hkl₂; omega
  ext p u
  rw [pathGenerator_mul_apply hjk hkl (fun q ↦ pathCoeff c j' k' l' q u.1) (fun _ ↦ rfl),
    pathGenerator_mul_apply hjk₂ hkl₂ (fun q ↦ pathCoeff c j k l q u.1) (fun _ ↦ rfl)]
  simp only [pathCoeff, update_of_ne hjk₃, update_of_ne hlk₃, update_of_ne hkk',
    update_of_ne hjk₄, update_of_ne hlk₄, update_of_ne hkk'.symm,
    forall_ne_update_eq_iff_of_ne hkk', forall_ne_update_eq_iff_of_ne hkk'.symm]
  have hswap : (∀ m, m ≠ k' → m ≠ k → p.1 m = u.1 m) ↔ ∀ m, m ≠ k → m ≠ k' → p.1 m = u.1 m :=
    forall_congr' fun _ ↦ ⟨fun h h₁ h₂ ↦ h h₂ h₁, fun h h₁ h₂ ↦ h h₂ h₁⟩
  simp only [hswap]
  by_cases ha : p.1 j = p.1 l
  swap
  · simp [ha]
  by_cases hb : p.1 j' = p.1 l'
  swap
  · simp [hb]
  by_cases hag : ∀ m, m ≠ k → m ≠ k' → p.1 m = u.1 m
  · have hu : u.1 k ∈ ({p.1 j - 1, p.1 j + 1} : Finset ℤ) := by
      rw [hag j hjk' hjk₃]
      exact mem_pair_of_abs_sub_eq_one (u.2.abs_sub_eq_one j k hjk)
    have hu' : u.1 k' ∈ ({p.1 j' - 1, p.1 j' + 1} : Finset ℤ) := by
      rw [hag j' hjk₄ hjk₂']
      exact mem_pair_of_abs_sub_eq_one (u.2.abs_sub_eq_one j' k' hjk₂)
    simp only [eq_true hag, eq_true ha, eq_true hb, and_true, ite_true, mul_ite, mul_zero,
      Finset.sum_ite_eq', hu, hu']
    ring
  · simp [eq_false hag]

section Rep

variable (c) in
/-- The path representation of the Temperley–Lieb algebra on `n` strands, for a path amplitude
`c` of the loop value `δ`: the generator `e i` acts by the generator matrix at the vertex `i + 1`
of the `n`-step paths, with neighbours `i` and `i + 2`. -/
noncomputable def pathRep (hc : IsPathAmplitude δ c) :
    TemperleyLieb 𝕜 δ n →ₐ[𝕜] Matrix (AmplitudePath c n) (AmplitudePath c n) 𝕜 :=
  lift (fun i ↦ pathGenerator c ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩)
    (fun _ ↦ pathGenerator_mul_self hc rfl rfl)
    (fun {i j} h ↦ by
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      simp only at h ⊢
      rcases h with rfl | rfl
      · exact pathGenerator_zigzag_left rfl rfl rfl
      · exact pathGenerator_zigzag_right rfl rfl rfl)
    (fun h ↦ pathGenerator_mul_pathGenerator_comm rfl rfl rfl rfl (by simpa using h))

/-- The path representation sends the generator `e i` to the generator matrix at the vertex
`i + 1`. -/
@[simp]
theorem pathRep_e (hc : IsPathAmplitude δ c) (i : Fin (n - 1)) :
    pathRep c hc (e δ i) = pathGenerator c ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ :=
  lift_e _ _ _ _ i

end Rep

section Star

variable [StarRing 𝕜]

/-- For a self-adjoint path amplitude, every generator matrix is Hermitian. -/
theorem isHermitian_pathGenerator (hstar : ∀ t, IsSelfAdjoint (c t)) {j k l : Fin (n + 1)}
    (hjk : j ≠ k) (hlk : l ≠ k) : Matrix.IsHermitian (pathGenerator c j k l) := by
  ext p p'
  rw [conjTranspose_apply, pathGenerator_apply, pathGenerator_apply]
  by_cases hag : ∀ m, m ≠ k → p.1 m = p'.1 m
  · have hag' : ∀ m, m ≠ k → p'.1 m = p.1 m := fun m hm ↦ (hag m hm).symm
    simp only [eq_true hag, eq_true hag', true_and, hag j hjk, hag l hlk]
    split_ifs
    · simp only [star_div₀, star_mul, star_pow, (hstar _).star_eq]
    · exact star_zero _
  · have hag' : ¬∀ m, m ≠ k → p'.1 m = p.1 m := fun h ↦ hag fun m hm ↦ (h m hm).symm
    simp [eq_false hag, eq_false hag']

variable [Fact (IsSelfAdjoint δ)]

/-- For a self-adjoint path amplitude, the path representation carries the analytic adjoint of
the Temperley–Lieb algebra to the conjugate transpose. -/
theorem pathRep_star (hc : IsPathAmplitude δ c) (hstar : ∀ t, IsSelfAdjoint (c t))
    (x : TemperleyLieb 𝕜 δ n) : pathRep c hc (star x) = (pathRep c hc x)ᴴ := by
  rw [← star_eq_conjTranspose]
  refine map_star_iff.mpr (fun i ↦ ?_) x
  rw [pathRep_e, IsSelfAdjoint, star_eq_conjTranspose]
  exact isHermitian_pathGenerator hstar (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

end Star

/-- Path amplitudes are preserved by ring homomorphisms of fields. -/
theorem IsPathAmplitude.map {𝕜' : Type*} [Field 𝕜'] (hc : IsPathAmplitude δ c) (f : 𝕜 →+* 𝕜') :
    IsPathAmplitude (f δ) (fun t ↦ f (c t)) := fun a ha ↦ by
  rw [map_ne_zero] at ha
  simpa using congrArg f (hc a ha)

section QInt

open Real

/-- The amplitude `√[t + 1]` on the vertices `0 ≤ t < L` of `ℤ` and `0` elsewhere, where `[k]` is
the quantum integer `TauCeti.qInt ℝ δ k`. For `δ ≥ 2` and `L = ⊤` its support is the half-line;
for `δ = 2 cos (π / m)` and `L = m - 1` it is the Dynkin graph `A_(m - 1)`. -/
noncomputable def qIntAmplitude (δ : ℝ) (L : ℕ∞) (t : ℤ) : ℝ :=
  if 0 ≤ t ∧ (t.toNat : ℕ∞) < L then √(qInt ℝ δ (t.toNat + 1)) else 0

/-- The square of the amplitude at a vertex `t < L` of the half-line is the quantum integer
`[t + 1]`, provided it is nonnegative. -/
theorem qIntAmplitude_natCast_sq {δ : ℝ} {L : ℕ∞} {t : ℕ} (htL : (t : ℕ∞) < L)
    (ht : 0 ≤ qInt ℝ δ (t + 1)) : qIntAmplitude δ L t ^ 2 = qInt ℝ δ (t + 1) := by
  simp [qIntAmplitude, htL, ht]

/-- If the quantum integers `[1], …, [L]` are positive and `[L + 1] = 0` (when `L` is finite),
then `qIntAmplitude δ L` is a path amplitude: the recurrence `[t] + [t + 2] = δ [t + 1]` is the
neighbour condition, with the missing vertices `-1` and `L` contributing `[0] = 0` and
`[L + 1] = 0`. -/
theorem isPathAmplitude_qIntAmplitude {δ : ℝ} {L : ℕ∞}
    (hpos : ∀ j : ℕ, 0 < j → (j : ℕ∞) ≤ L → 0 < qInt ℝ δ j)
    (hend : ∀ N : ℕ, L = N → qInt ℝ δ (N + 1) = 0) :
    IsPathAmplitude δ (qIntAmplitude δ L) := by
  intro a ha
  have hsupp : 0 ≤ a ∧ (a.toNat : ℕ∞) < L := by
    by_contra h
    exact ha (by simp [qIntAmplitude, h])
  obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hsupp.1
  have htL : (t : ℕ∞) < L := by simpa using hsupp.2
  have hlt : ∀ s : ℕ, (s : ℕ∞) < L → 0 ≤ qInt ℝ δ (s + 1) := fun s hs ↦
    (hpos (s + 1) (by omega) ((ENat.add_one_le_iff (ENat.natCast_ne_top s)).mpr hs)).le
  have h0 : qIntAmplitude δ L ((t : ℤ) - 1) ^ 2 = qInt ℝ δ t := by
    rcases t with _ | s
    · simp [qIntAmplitude]
    · rw [show ((s + 1 : ℕ) : ℤ) - 1 = s by push_cast; ring]
      exact qIntAmplitude_natCast_sq ((ENat.natCast_lt_natCast.mpr (by omega)).trans htL)
        (hlt s ((ENat.natCast_lt_natCast.mpr (by omega)).trans htL))
  have h2 : qIntAmplitude δ L ((t : ℤ) + 1) ^ 2 = qInt ℝ δ (t + 2) := by
    rw [show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by push_cast; ring]
    by_cases hL : ((t + 1 : ℕ) : ℕ∞) < L
    · exact qIntAmplitude_natCast_sq hL (hlt (t + 1) hL)
    · have hLt : L = ((t + 1 : ℕ) : ℕ∞) := le_antisymm (not_lt.mp hL)
        (by simpa using (ENat.add_one_le_iff (ENat.natCast_ne_top t)).mpr htL)
      simp [qIntAmplitude, hLt, hend (t + 1) hLt]
  rw [h0, h2, qIntAmplitude_natCast_sq htL (hlt t htL), qInt_add_two]
  ring

/-- For `δ ≥ 2` the amplitude `√[t + 1]` on the half-line is a path amplitude. -/
theorem isPathAmplitude_qIntAmplitude_top {δ : ℝ} (hδ : 2 ≤ δ) :
    IsPathAmplitude δ (qIntAmplitude δ ⊤) :=
  isPathAmplitude_qIntAmplitude (fun _ hj _ ↦ qInt_pos_of_two_le hδ hj) (fun _ h ↦ by simp at h)

/-- For `δ = 2 cos (π / m)` the amplitude `√[t + 1]` on the vertices `0, …, m - 2` of the Dynkin
graph `A_(m - 1)` is a path amplitude. -/
theorem isPathAmplitude_qIntAmplitude_two_mul_cos {m : ℕ} (hm : 2 ≤ m) :
    IsPathAmplitude (2 * cos (π / m)) (qIntAmplitude (2 * cos (π / m)) (m - 1 : ℕ)) := by
  refine isPathAmplitude_qIntAmplitude (fun j hj hjm ↦ ?_) (fun N hN ↦ ?_)
  · exact qInt_two_mul_cos_pi_div_pos hj (by have := ENat.natCast_le_natCast.mp hjm; omega)
  · obtain rfl : m - 1 = N := ENat.natCast_inj.mp hN
    rw [show m - 1 + 1 = m by omega]
    exact qInt_two_mul_cos_pi_div_eq_zero hm

end QInt

end TauCeti.TemperleyLieb
