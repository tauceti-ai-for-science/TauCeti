/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Basic

/-!
# Colength dividing an element

Let `O` be a commutative ring and `M`, `N` submodules of an `O`-module `V`. Say that *the colength
of `N` in `M` divides `z`*, written `M ⊸_z N`, if every finite family `Φ₁, …, Φₙ` in `M` is carried
into `N` by a square matrix whose determinant divides `z`: some `m ∈ Mₙ(O)` has `det m ∣ z` and
`∑ₖ m i k • Φ k ∈ N` for every `i`. Over a valuation ring this says that `N` has colength at most
`v(z)` in `M`. It needs no bases and no inclusion `N ≤ M`, so it makes sense for the integral
vectors of a lattice in a module that is not finitely generated, such as a complex vector space
over the non-noetherian valuation ring `{z : |ι z| ≤ 1}` of a field isomorphism
`ι : ℂ ≃ PadicAlgCl ℓ`. Over a discrete valuation ring it bounds a length
(`TauCeti.RingTheory.Length.ColengthDvd`).

## Main definitions

* `Submodule.ColengthDvd M N z`: the colength of `N` in `M` divides `z`.
* `Submodule.IsOntoUpToColength p M n y c`: the endomorphism `y` keeps `M` and is onto `M`
  modulo `p ^ n` up to a colength dividing `p ^ l` for some natural number `l ≤ c`.

## Main results

* `Submodule.ColengthDvd.of_le`, `Submodule.ColengthDvd.of_dvd`, `Submodule.ColengthDvd.trans`:
  inclusions have colength dividing `1`, the divisor may be enlarged, and divisors multiply along
  chains.
* `Submodule.ColengthDvd.comap`, `Submodule.ColengthDvd.map`: colength bounds pass along linear
  maps in both directions.
* `Submodule.ColengthDvd.comp`, `Submodule.IsOntoUpToColength.prod`: images under an endomorphism
  modulo `a`, and products of endomorphisms that are onto up to a colength.
* `Submodule.ColengthDvd.of_det_dvd`: over a valuation domain, a submodule of `O ^ ι` that contains
  the image of a square matrix `A` has colength dividing `det A`. This rests on the Smith normal
  form over a valuation domain, `Matrix.exists_mul_mul_eq_diagonal_of_valuationRing`.
* `Submodule.colengthDvd_inf_comap_span`, `Submodule.colengthDvd_top_smul_top`,
  `Submodule.colengthDvd_sup_span`: one coordinate condition costs `a`, `a • O ^ ι` has colength
  dividing `a ^ #ι`, and `N + z • V` has colength dividing `z ^ #S` in `N + span S`.

## References

These statements are adapted from the formal proof of the Riemann hypothesis for Dirichlet
L-functions in grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic PBC), file `New/Reduction/Lattices/Colength.lean` (`New.ColengthDvd` and the lemmas
named after it, `New.IsOntoUpToColength`, `New.IsOntoUpToColength.prod`,
`New.colengthDvd_inf_comap_span`, `New.colengthDvd_top_smul_top`, `New.colengthDvd_sup_span`).
-/

public section

open Matrix Finset Pointwise

namespace Submodule

variable {O U V ι : Type*} [CommRing O] [AddCommGroup U] [Module O U] [AddCommGroup V] [Module O V]
  {M N P : Submodule O V} {M' N' : Submodule O U} {z z' a : O}

variable (M N z) in
/-- The colength of `N` in `M` divides `z`, written `M ⊸_z N`: every finite family `Φ k`
(`k : Fin n`) of vectors of `M` is carried into `N` by a square matrix `m` with `det m ∣ z`, that
is, `∑ k, m i k • Φ k ∈ N` for every `i`. Over a valuation ring read it as "`N` has colength at most
`v(z)` in `M`". Neither `N ≤ M` nor any finiteness is assumed. -/
@[expose] def ColengthDvd : Prop :=
  ∀ (n : ℕ) (Φ : Fin n → V), (∀ k, Φ k ∈ M) →
    ∃ m : Matrix (Fin n) (Fin n) O, m.det ∣ z ∧ ∀ i, ∑ k, m i k • Φ k ∈ N

namespace ColengthDvd

/-- An inclusion `M ≤ N` has colength dividing every element. -/
theorem of_le (hMN : M ≤ N) : ColengthDvd M N z := fun _ _ hΦ ↦
  ⟨1, by simp, fun i ↦ by simpa [Matrix.one_apply] using hMN (hΦ i)⟩

/-- A colength dividing `z` divides every multiple of `z`. -/
theorem of_dvd (hMN : ColengthDvd M N z) (hz : z ∣ z') : ColengthDvd M N z' :=
  fun n Φ hΦ ↦ (hMN n Φ hΦ).imp fun _ ⟨h_det, h_mem⟩ ↦ ⟨h_det.trans hz, h_mem⟩

/-- Colength bounds multiply along chains: `M ⊸_z N` and `N ⊸_a P` give `M ⊸_{z a} P`. No
inclusion between the three submodules is assumed. -/
theorem trans (hMN : ColengthDvd M N z) (hNP : ColengthDvd N P a) : ColengthDvd M P (z * a) := by
  intro n Φ hΦ
  -- combine `Φ` by `m` into `N`, then combine the results by `m'` into `P`
  obtain ⟨m, hm_det, hm_mem⟩ := hMN n Φ hΦ
  obtain ⟨m', hm'_det, hm'_mem⟩ := hNP n (fun i ↦ ∑ k, m i k • Φ k) hm_mem
  have h_assoc (i : Fin n) : ∑ k, (m' * m) i k • Φ k = ∑ j, m' i j • ∑ k, m j k • Φ k := by
    simpa [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul] using Finset.sum_comm
  refine ⟨m' * m, ?_, fun i ↦ by simpa only [h_assoc] using hm'_mem i⟩
  simpa [mul_comm z] using mul_dvd_mul hm'_det hm_det

/-- Colength bounds pull back along a linear map `f : U → V`: if `f (M') ⊆ M` and every `x ∈ M'`
with `f x ∈ N` lies in `N'`, then `M ⊸_z N` gives `M' ⊸_z N'`. -/
theorem comap (hMN : ColengthDvd M N z) (f : U →ₗ[O] V) (hM : M' ≤ M.comap f)
    (hN : ∀ x ∈ M', f x ∈ N → x ∈ N') : ColengthDvd M' N' z := by
  intro n Φ hΦ
  obtain ⟨m, hm_det, hm_mem⟩ := hMN n (f ∘ Φ) fun k ↦ hM (hΦ k)
  exact ⟨m, hm_det, fun i ↦ hN _ (sum_smul_mem M' _ fun k _ ↦ hΦ k) (by simpa using hm_mem i)⟩

/-- Colength bounds push forward along a linear map `f : V → U`: if `M' ⊆ f (M) + N'` and
`f (N) ⊆ N'`, then `M ⊸_z N` gives `M' ⊸_z N'`. -/
theorem map (hMN : ColengthDvd M N z) (f : V →ₗ[O] U) (hM' : M' ≤ M.map f ⊔ N')
    (hN : N.map f ≤ N') : ColengthDvd M' N' z := by
  intro n Φ hΦ
  -- write `Φ k = f (x k) + y k` with `x k ∈ M` and `y k ∈ N'`
  have h_split (k : Fin n) : ∃ x ∈ M, ∃ y ∈ N', f x + y = Φ k := by
    simpa using mem_sup.1 (hM' (hΦ k))
  choose x hx y hy hxy using h_split
  obtain ⟨m, hm_det, hm_mem⟩ := hMN n x hx
  refine ⟨m, hm_det, fun i ↦ ?_⟩
  simpa [← hxy, sum_add_distrib] using
    add_mem (hN (mem_map_of_mem (hm_mem i))) (sum_smul_mem N' (m i) fun k _ ↦ hy k)

/-- Let the endomorphism `f` keep `M`. If `M ⊸_z (f (M) + a • M)` and `M ⊸_{z'} (N + a • M)`, then
`M ⊸_{z z'} (f (N) + a • M)`. -/
theorem comp {f : V →ₗ[O] V} (hf_keep : M.map f ≤ M)
    (hf_onto : ColengthDvd M (M.map f ⊔ a • M) z) (hMN : ColengthDvd M (N ⊔ a • M) z') :
    ColengthDvd M (N.map f ⊔ a • M) (z * z') := by
  -- push `hMN` forward by `f`, using `f (a • M) ≤ a • M`, and chain it after `hf_onto`
  refine hf_onto.trans (hMN.map f (sup_le_sup_left le_sup_right _) ?_)
  rw [Submodule.map_sup, map_pointwise_smul]
  exact sup_le_sup_left (smul_mono_right a hf_keep) _

end ColengthDvd

/-! ### Endomorphisms that are onto up to a bounded colength -/

/-- The endomorphism `y` of `V` keeps `M` and is onto `M` modulo `p ^ n` up to colength `c`: for
some natural number `l ≤ c`, the colength of `y (M) + p ^ n • M` in `M` divides `p ^ l`. -/
@[expose] def IsOntoUpToColength (p : O) (M : Submodule O V) (n : ℕ) (y : Module.End O V) (c : ℝ) :
    Prop :=
  M.map y ≤ M ∧ ∃ l : ℕ, l ≤ c ∧ ColengthDvd M (M.map y ⊔ p ^ n • M) (p ^ l)

/-- If each endomorphism `T l` of a list `L` is onto `M` modulo `p ^ s` up to colength `t l`, then
their product is onto `M` modulo `p ^ s` up to colength `∑ t l`. -/
theorem IsOntoUpToColength.prod {s : ℕ} {T : ι → Module.End O V} {t : ι → ℝ} (L : List ι)
    (hT : ∀ l ∈ L, IsOntoUpToColength z M s (T l) (t l)) :
    IsOntoUpToColength z M s (L.map T).prod (L.map t).sum := by
  induction L with
  | nil =>
    simpa [IsOntoUpToColength, Module.End.one_eq_id] using
      ColengthDvd.of_le (M := M) (z := (1 : O)) le_rfl
  | cons a L ih =>
    -- the product `T a * ∏ L` keeps `M`, and the bounds multiply by `ColengthDvd.comp`
    obtain ⟨ha_map, i, hi, ha⟩ := hT a List.mem_cons_self
    obtain ⟨hL_map, j, hj, hL⟩ := ih fun l hl ↦ hT l (List.mem_cons_of_mem a hl)
    rw [IsOntoUpToColength, List.map_cons, List.prod_cons, Module.End.mul_eq_comp, map_comp]
    refine ⟨(map_mono hL_map).trans ha_map, i + j, by simpa using add_le_add hi hj, ?_⟩
    simpa [pow_add] using ColengthDvd.comp ha_map ha hL

/-! ### Colength bounds over a valuation domain -/

section ValuationRing

variable [IsDomain O] [ValuationRing O]

/-- Over a valuation domain, the vectors of `M` on which a linear form `f` is divisible by `a` have
colength dividing `a` in `M`. -/
theorem colengthDvd_inf_comap_span (M : Submodule O V) (f : V →ₗ[O] O) (a : O) :
    ColengthDvd M (M ⊓ Submodule.comap f (Ideal.span {a})) a := by
  intro n Φ hΦ
  obtain rfl | hn := n.eq_zero_or_pos
  · exact ⟨1, by simp, finZeroElim⟩
  -- take a member `Φ p` whose value divides the others, subtract multiples of it from them to
  -- clear their values, and multiply it by `a`
  classical
  obtain ⟨p, -, hp⟩ := exists_max_image univ (fun k ↦ Ideal.span {f (Φ k)}) ⟨⟨0, hn⟩, mem_univ _⟩
  replace hp (k : Fin n) : f (Φ p) ∣ f (Φ k) :=
    Ideal.span_singleton_le_span_singleton.1 (hp k (mem_univ k))
  choose c hc using hp
  let m : Matrix (Fin n) (Fin n) O := updateCol 1 p fun i ↦ if i = p then a else -c i
  have h_det : m.det = a := by simp [m, ← cramer_apply, cramer_one]
  have h_comb (i : Fin n) : ∑ k, m i k • Φ k = if i = p then a • Φ p else Φ i - c i • Φ p := by
    obtain rfl | hip := eq_or_ne i p
    · rw [Fintype.sum_eq_single i] <;> simp +contextual [m, eq_comm]
    · rw [Fintype.sum_eq_add i p hip] <;>
        simp +contextual [m, hip, Ne.symm hip, sub_eq_add_neg, eq_comm]
  refine ⟨m, h_det.dvd, fun i ↦ ⟨sum_smul_mem M _ fun k _ ↦ hΦ k, ?_⟩⟩
  rw [SetLike.mem_coe, mem_comap, h_comb]
  split_ifs <;> simp [Ideal.mem_span_singleton, hc i, mul_comm]

/-- **The image of a square matrix.** Over a valuation domain, if a square matrix `A` has
`det A ∣ z` and the submodule `L` of `ι → O` contains its image, then `O ^ ι ⊸_z L`.

The proof writes `A` in diagonal form `L₀ * A * Q₀ = diagonal d` and imposes the conditions
`d j ∣ (L₀ x) j` one coordinate at a time, each of colength dividing `d j`. -/
theorem ColengthDvd.of_det_dvd [Fintype ι] [DecidableEq ι] {A : Matrix ι ι O}
    {L : Submodule O (ι → O)} (h_dvd : A.det ∣ z) (h_le : LinearMap.range A.mulVecLin ≤ L) :
    ColengthDvd ⊤ L z := by
  obtain ⟨L₀, Q₀, d, hL₀, hQ₀, h⟩ := exists_mul_mul_eq_diagonal_of_valuationRing A
  let f (j : ι) : (ι → O) →ₗ[O] O := .proj j ∘ₗ L₀.mulVecLin
  let S (s : Finset ι) : Submodule O (ι → O) := ⨅ j ∈ s, Submodule.comap (f j) (Ideal.span {d j})
  -- each further coordinate condition costs `d j`
  have h_chain (s : Finset ι) : ColengthDvd ⊤ (S s) (∏ j ∈ s, d j) := by
    induction s using Finset.induction with
    | empty => exact .of_le (by simp [S])
    | insert j s hj ih =>
      simpa only [S, Finset.iInf_insert, inf_comm, prod_insert hj, mul_comm] using
        ih.trans (colengthDvd_inf_comap_span _ (f j) (d j))
  -- the last submodule lies in the image of `A = L₀⁻¹ * diagonal d * Q₀⁻¹`
  have h_image : S univ ≤ LinearMap.range A.mulVecLin := by
    intro x hx
    simp only [S, mem_iInf, mem_univ, forall_const] at hx
    choose w hw using fun j ↦ Ideal.mem_span_singleton.1 (hx j)
    have hA : A = L₀⁻¹ * diagonal d * Q₀⁻¹ := by
      rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hL₀, Matrix.one_mul,
        Matrix.mul_assoc, mul_nonsing_inv _ hQ₀, Matrix.mul_one]
    refine ⟨Q₀ *ᵥ w, ?_⟩
    have h_diag : diagonal d *ᵥ w = L₀ *ᵥ x :=
      funext fun j ↦ by simpa [f, mulVec_diagonal] using (hw j).symm
    rw [hA, mulVecLin_apply, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec w,
      nonsing_inv_mul _ hQ₀, one_mulVec,
      h_diag, mulVec_mulVec, nonsing_inv_mul _ hL₀, one_mulVec]
  have h_assoc : Associated A.det (∏ j, d j) := by
    rw [← det_diagonal, ← h, det_mul, det_mul, mul_comm L₀.det, mul_assoc]
    exact associated_mul_unit_right _ _ (hL₀.mul hQ₀)
  have h_prod : ∏ j, d j ∣ z := h_assoc.symm.dvd.trans h_dvd
  simpa using ((h_chain univ).of_dvd h_prod).trans (.of_le (z := 1) (h_image.trans h_le))

/-- Over a valuation domain, `a • O ^ ι` has colength dividing `a ^ #ι` in `O ^ ι`. -/
theorem colengthDvd_top_smul_top [Fintype ι] (a : O) :
    ColengthDvd (⊤ : Submodule O (ι → O)) (a • ⊤) (a ^ Fintype.card ι) := by
  classical
  refine .of_det_dvd (A := a • (1 : Matrix ι ι O)) (by simp) ?_
  rintro _ ⟨v, rfl⟩
  simpa [smul_mulVec] using smul_mem_pointwise_smul v a ⊤ mem_top

/-- Over a valuation domain, for a submodule `N` and a finite set `s` of vectors, the colength of
`N + z • V` in `N + span s` divides `z ^ #s`. -/
theorem colengthDvd_sup_span (N : Submodule O V) (s : Finset V) (z : O) :
    ColengthDvd (N ⊔ span O (s : Set V)) (N ⊔ z • ⊤) (z ^ #s) := by
  -- push the bound for `z • O ^ s` in `O ^ s` forward along the map to linear combinations
  classical
  let comb : (s → O) →ₗ[O] V := Fintype.linearCombination O fun v : s ↦ (v : V)
  have h_range : (⊤ : Submodule O (s → O)).map comb = span O s := by
    simp [comb, Fintype.range_linearCombination]
  have h_free : ColengthDvd (⊤ : Submodule O (s → O)) (z • ⊤) (z ^ #s) := by
    simpa using colengthDvd_top_smul_top (ι := s) z
  refine h_free.map comb (by rw [h_range, sup_comm]; exact sup_le_sup_left le_sup_left _) ?_
  rw [map_pointwise_smul]
  exact le_sup_of_le_right (smul_mono_right z le_top)

end ValuationRing

end Submodule
