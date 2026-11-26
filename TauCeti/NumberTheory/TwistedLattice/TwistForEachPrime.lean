/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.TwistedLattice.Basic
public import TauCeti.NumberTheory.Height.PrimePadicIso
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A twist for each prime

Let `V` be a finite-dimensional complex inner product space with a twisted lattice
(`TauCeti.TwistedLattice`) whose maps `Θ_ξ` are all injective, let `y₁, …, yₙ, z₁, …, z_{n'}` be
a basis of `V`, and choose for each pair `ι` a twist `ξ_ι` allowed at the prime of `ι`. The theorem
`TauCeti.TwistedLattice.covolume_add_index_nonneg` bounds the covolume of `y` from below by its
index, the height of `Z(1) / Z(ξ_ι)` (`TauCeti.HeightLe`) and the sizes and denominators of the
vectors `z` completing it to a basis: sizes are read for the trivial twist, valuations for the twist
`ξ_ι` allowed at each prime.

Write `Gram(ξ)` for the Gram determinant of the images under `Θ_ξ` of the basis `y ∪ z`. Then
`Gram(ξ) = Z(ξ) · det ⟨y_i, z_k⟩` (`TauCeti.TwistedLattice.det_gram_comp`), so for every pair
`Gram(1) = |γ(ξ_ι)|^{2n'} Gram(ξ_ι) · |γ(ξ_ι)|^{-2n'} · Z(1) / Z(ξ_ι)`. At `ι` and at `ι.conj` the
matrices of the index together with the scalar `γ(ξ_ι)` carry the images under `Θ_{ξ_ι}` into the
integral vectors, so the integrality of inner products bounds `|ι (|γ(ξ_ι)|^{2n'} Gram(ξ_ι))|` by
`ℓ^{2δ_ℓ}`: that family has height at most `2δ`. Adding the heights of the three factors
(`TauCeti.HeightLe.mul`) bounds the height of the constant family `Gram(1)`, whose conjugates are at
most `e^{c + n' b_short}` by Fischer's inequality and the Cauchy–Schwarz inequality for
determinants; the product formula (`TauCeti.HeightLe.neg_le_of_norm_map_le`) gives the inequality.

## Main results

* `TauCeti.TwistedLattice.det_gram_comp`: `det ⟨u x_i, u x_k⟩ = (normDet u)² det ⟨x_i, x_k⟩` for a
  family `x` of `dim V` vectors.
* `TauCeti.TwistedLattice.norm_pow_mul_det_gram_le`,
  `TauCeti.TwistedLattice.heightLe_pow_mul_det_gram`: the valuations of `|γ|^{2n'} Gram(ξ)`.
* `TauCeti.TwistedLattice.covolume_add_index_nonneg`: `0 ≤ c + 2δ + n'(b_short + b_denom) + b_vol`.

## References

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `New/Reduction/Lattices/TwistedLattice.lean`
(`New.TwistedLattice.covolume_add_index_nonneg`, `New.TwistedLattice.heightLe_pow_mul_det_gram`,
`New.TwistedLattice.norm_pow_mul_det_gram_le`), and
`New.det_gram_comp` in `Lib/General/LinearAlgebra/GramDeterminant.lean`. Related work on
size-versus-divisibility bounds for determinants: J.-B. Bost, *Algebraic leaves of algebraic
foliations over number fields*, Publ. Math. IHÉS 93 (2001); M. Laurent, *Linear forms in two
logarithms and interpolation determinants*, Acta Arith. 66 (1994).
-/

public section

noncomputable section

open Finset Matrix Real Module
open scoped InnerProductSpace

namespace TauCeti

namespace TwistedLattice

/-- For a linear map `u` and a family `x` of `dim W` vectors of `W`, the Gram determinant of
`u ∘ x` is that of `x` times `(normDet u)² = det (u^* u)`. -/
theorem det_gram_comp {W H S : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype S]
    [DecidableEq S] (u : W →ₗ[ℂ] H) (x : S → W) (h_card : finrank ℂ W = Fintype.card S) :
    (gram ℂ (u ∘ x)).det = u.normDet ^ 2 * (gram ℂ x).det := by
  -- with `X` sending the standard basis to `x`, both sides are squared volumes
  let e : OrthonormalBasis S ℂ (EuclideanSpace ℂ S) := EuclideanSpace.basisFun S ℂ
  let X : EuclideanSpace ℂ S →ₗ[ℂ] W := e.toBasis.constr ℂ x
  have hX (i : S) : X (e i) = x i := e.toBasis.constr_basis ℂ x i
  have h_comp : (gram ℂ (u ∘ x)).det = ((u ∘ₗ X).normDet ^ 2 : ℝ) := by
    simpa [hX, Function.comp_def] using ((u ∘ₗ X).normDet_sq_eq_det_gram e).symm
  have h_id : (gram ℂ x).det = (X.normDet ^ 2 : ℝ) := by
    simpa [hX] using (X.normDet_sq_eq_det_gram e).symm
  rw [h_comp, h_id, LinearMap.normDet_comp_of_finrank_eq X u (by simp [h_card])]
  push_cast
  ring

/-- A square matrix whose entries are integral at the pair `ι` has an integral determinant. -/
private theorem norm_iso_det_le_one {S : Type} [Fintype S] [DecidableEq S] {ι : PrimePadicIso}
    {M : Matrix S S ℂ} (h : ∀ a b, ‖ι.iso (M a b)‖ ≤ 1) : ‖ι.iso M.det‖ ≤ 1 := by
  let M' : Matrix S S ι.integers := of fun a b ↦ ⟨M a b, (ι.mem_integers).2 (h a b)⟩
  have : M.det = (M'.det : ℂ) := by
    rw [show ((M'.det : ι.integers) : ℂ) = ι.integers.subtype M'.det from rfl, RingHom.map_det]
    rfl
  exact this ▸ (ι.mem_integers).1 M'.det.property

variable {V T : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [One T]
  {L : TwistedLattice V T}

/-- **Gram determinants and valuations.** Let `ξ` be allowed at the prime of the pair `ι`. If `u`
carries the vectors `Θ_ξ w_i` into the vectors integral at `ι` and `u'` carries them into those
integral at `ι.conj`, then `|ι.conj (det u')| · |ι Gram(ξ)| · |ι (det u)| ≤ 1`, with
`Gram(ξ) = det ⟨Θ_ξ w_i, Θ_ξ w_k⟩`. -/
theorem norm_det_mul_det_gram_le_one {ι : PrimePadicIso} {ξ : T} (hξ : L.IsAllowed ι.prime ξ)
    {S : Type} [Fintype S] [DecidableEq S] {w : S → V} {u u' : Matrix S S ℂ}
    (hu : ∀ i, ∑ k, u i k • L.lift ξ (w k) ∈ L.lattice ξ ι)
    (hu' : ∀ i, ∑ k, u' i k • L.lift ξ (w k) ∈ L.lattice ξ ι.conj) :
    ‖ι.conj.iso u'.det‖ * ‖ι.iso (gram ℂ (L.lift ξ ∘ w)).det‖ * ‖ι.iso u.det‖ ≤ 1 := by
  -- the matrix of the inner products of the two transformed families
  set N := u'.map (starRingEnd ℂ) * gram ℂ (L.lift ξ ∘ w) * uᵀ
  have h_entry (a b : S) :
      N a b = ⟪∑ k, u' a k • L.lift ξ (w k), ∑ k, u b k • L.lift ξ (w k)⟫_ℂ := by
    simp [N, Matrix.mul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      gram_apply, mul_comm]
  have h_det : N.det = starRingEnd ℂ u'.det * (gram ℂ (L.lift ξ ∘ w)).det * u.det := by
    rw [det_mul, det_mul, det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have h_int := norm_iso_det_le_one (ι := ι) (M := N) fun a b ↦
    h_entry a b ▸ L.norm_inner_le_one ι hξ _ (hu' a) _ (hu b)
  rwa [h_det, map_mul, map_mul, norm_mul, norm_mul, ← ι.conj_iso_apply] at h_int

/-- Let `ξ` be allowed at the prime of the pair `ι`, let `u` carry `y` into the vectors integral at
`ι`, and let the vectors `γ Θ_ξ z_i` be integral at `ι`. Then a matrix `v` with
`det v = det u · γ ^ n'` carries `Θ_ξ y_1, …, Θ_ξ y_n, Θ_ξ z_1, …, Θ_ξ z_n'` into the vectors of
`S_ξ` integral at `ι`. -/
theorem exists_matrix_elim_mem_lattice {n n' : ℕ} {y : Fin n → V} {z : Fin n' → V}
    {ι : PrimePadicIso} {ξ : T} (hξ : L.IsAllowed ι.prime ξ)
    {u : Matrix (Fin n) (Fin n) ι.integers}
    (hu : ∀ i, ∑ k, u i k • y k ∈ L.integralVectors ι) {γ : ℂ}
    (hz : ∀ i, γ • L.lift ξ (z i) ∈ L.lattice ξ ι) :
    ∃ v : Matrix (Fin n ⊕ Fin n') (Fin n ⊕ Fin n') ℂ, v.det = u.det * γ ^ n' ∧
      ∀ i, ∑ k, v i k • L.lift ξ (Sum.elim y z k) ∈ L.lattice ξ ι := by
  -- the block diagonal matrix with blocks `u` and `γ`
  have hu_coe : (u.map (↑) : Matrix (Fin n) (Fin n) ℂ).det = u.det :=
    (RingHom.map_det ι.integers.subtype u).symm
  refine ⟨fromBlocks (u.map (↑)) 0 0 (γ • 1), by simp [hu_coe], ?_⟩
  rintro (i | i)
  · have h_lift : L.lift ξ (∑ k, u i k • y k) ∈ L.lattice ξ ι :=
      mem_integralVectors.1 (hu i) ξ hξ
    convert h_lift using 1
    simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Sum.elim_inl,
      Sum.elim_inr, map_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
      map_sum, LinearMap.map_smul_of_tower]
    rfl
  · simpa [Matrix.one_apply] using hz i

/-- Let `ξ` be allowed at the prime `ℓ` of the pair `ι`, let `u` and `u'` carry `y` into the
vectors integral at `ι` and at `ι.conj`, both with `|ι (det u)|, |ι.conj (det u')| ≥ ℓ ^ (-a)`,
and let the vectors `γ Θ_ξ z_i` be integral at `ι` and at `ι.conj`. Then
`|ι (|γ| ^ (2 n') Gram(ξ))| ≤ ℓ ^ (2 a)`, where `Gram(ξ)` is the Gram determinant of
`Θ_ξ y_1, …, Θ_ξ y_n, Θ_ξ z_1, …, Θ_ξ z_n'`. -/
theorem norm_pow_mul_det_gram_le {n n' : ℕ} {y : Fin n → V} {z : Fin n' → V}
    {ι : PrimePadicIso} {ξ : T} (hξ : L.IsAllowed ι.prime ξ) {a : ℝ}
    {u : Matrix (Fin n) (Fin n) ι.integers} {u' : Matrix (Fin n) (Fin n) ι.conj.integers}
    (hu_det : (ι.prime : ℝ) ^ (-a) ≤ ‖ι.iso u.det‖)
    (hu : ∀ i, ∑ k, u i k • y k ∈ L.integralVectors ι)
    (hu'_det : (ι.prime : ℝ) ^ (-a) ≤ ‖ι.conj.iso u'.det‖)
    (hu' : ∀ i, ∑ k, u' i k • y k ∈ L.integralVectors ι.conj) {γ : ℂ}
    (hz : ∀ i, γ • L.lift ξ (z i) ∈ L.lattice ξ ι)
    (hz' : ∀ i, γ • L.lift ξ (z i) ∈ L.lattice ξ ι.conj) :
    ‖ι.iso (((‖γ‖ : ℂ) ^ 2) ^ n' * (gram ℂ (L.lift ξ ∘ Sum.elim y z)).det)‖ ≤
      exp (2 * (a * log ι.prime)) := by
  obtain ⟨v, hv_det, hv_mem⟩ := exists_matrix_elim_mem_lattice hξ hu hz
  obtain ⟨v', hv'_det, hv'_mem⟩ := exists_matrix_elim_mem_lattice (ι := ι.conj) hξ hu' hz'
  set G : ℂ := (gram ℂ (L.lift ξ ∘ Sum.elim y z)).det
  have h_int : ‖ι.conj.iso v'.det‖ * ‖ι.iso G‖ * ‖ι.iso v.det‖ ≤ 1 :=
    norm_det_mul_det_gram_le_one hξ hv_mem hv'_mem
  set β : ℝ := a * log ι.prime
  have h_exp : exp (-β) = (ι.prime : ℝ) ^ (-a) := by
    rw [rpow_def_of_pos (mod_cast (Fact.out : ι.prime.Prime).pos), mul_neg, mul_comm]
  calc ‖ι.iso (((‖γ‖ : ℂ) ^ 2) ^ n' * G)‖
      = ‖ι.conj.iso γ‖ ^ n' * ‖ι.iso G‖ * ‖ι.iso γ‖ ^ n' := by
        rw [ι.conj_iso_apply, ← Complex.conj_mul', mul_pow, map_mul, map_mul, map_pow, map_pow,
          norm_mul, norm_mul, norm_pow, norm_pow]
        exact mul_right_comm (G := ℝ) _ _ _
    _ = exp (2 * β) *
          (exp (-β) * ‖ι.conj.iso γ‖ ^ n' * ‖ι.iso G‖ * (exp (-β) * ‖ι.iso γ‖ ^ n')) := by
        rw [two_mul, Real.exp_add, Real.exp_neg]
        field_simp
    _ ≤ exp (2 * β) * (‖ι.conj.iso v'.det‖ * ‖ι.iso G‖ * ‖ι.iso v.det‖) := by
        simp only [hv_det, hv'_det, map_mul, map_pow, norm_mul, norm_pow]
        gcongr
        · exact h_exp ▸ hu'_det
        · exact h_exp ▸ hu_det
    _ ≤ exp (2 * β) := mul_le_of_le_one_right (exp_nonneg _) h_int

/-- Let `y` have index at most `δ`, let the twist `ξ_ι = θ ι` be allowed at the prime of `ι`, and
let the vectors `γ_ι Θ_{ξ_ι} z_i` be integral at `ι` and at `ι.conj`. Then the family
`ι ↦ |γ_ι| ^ (2 n') Gram(ξ_ι)` has height at most `2 δ`, where `Gram(ξ)` is the Gram determinant of
the images of `y_1, …, y_n, z_1, …, z_n'` under `Θ_ξ`. -/
theorem heightLe_pow_mul_det_gram {n n' : ℕ} {y : Fin n → V} {z : Fin n' → V} {δ : ℝ}
    (hδ : L.IndexLe y δ) {θ : PrimePadicIso → T} (hθ : ∀ ι, L.IsAllowed ι.prime (θ ι))
    {γ : PrimePadicIso → ℂ} (hz : ∀ ι i, γ ι • L.lift (θ ι) (z i) ∈ L.lattice (θ ι) ι)
    (hz' : ∀ ι i, γ ι • L.lift (θ ι) (z i) ∈ L.lattice (θ ι) ι.conj) :
    HeightLe (2 * δ) fun ι ↦
      ((‖γ ι‖ : ℂ) ^ 2) ^ n' * (gram ℂ (L.lift (θ ι) ∘ Sum.elim y z)).det := by
  obtain ⟨e, -, he_sum, h_carries⟩ := hδ
  refine .of_le (e := fun ℓ ↦ 2 * (e ℓ * log ℓ)) (fun U hU ↦ ?_) fun ι ↦ ?_
  · simpa [← mul_sum] using he_sum U hU
  -- the matrices of the index at `ι` and at `ι.conj`, which have the same prime, serve for `θ ι`
  obtain ⟨⟨u, hu_det, hu⟩, ⟨u', hu'_det, hu'⟩⟩ := And.intro (h_carries ι) (h_carries ι.conj)
  exact norm_pow_mul_det_gram_le (hθ ι) hu_det hu hu'_det hu' (hz ι) (hz' ι)

variable [FiniteDimensional ℂ V]

/-- **A twist for each prime.** Let `L` be a twisted lattice on `V` whose maps `Θ_ξ` are all
injective, let `y_1, …, y_n, z_1, …, z_n'` be a basis of `V`, and let `ξ_ι = θ ι` be allowed at
the prime of `ι`. Suppose that `y` has covolume at most `c` and index at most `δ`; that
`γ(ξ) ≠ 0` and `γ(ξ) Θ_ξ z_i` is integral at every pair `ι` for `ξ` allowed at the prime of `ι`;
that `‖z_i‖²_σ ≤ e^{b_short}` for all automorphisms `σ` of `ℂ`; and that the families
`ι ↦ |γ(ξ_ι)|⁻²` and `ι ↦ Z(1) / Z(ξ_ι)` have heights at most `b_denom` and `b_vol`. Then
`0 ≤ c + 2 δ + n' (b_short + b_denom) + b_vol`. -/
theorem covolume_add_index_nonneg {n n' : ℕ} {y : Fin n → V} {z : Fin n' → V}
    (h_inj : ∀ ξ, Function.Injective (L.lift ξ))
    (h_indep : LinearIndependent ℂ (Sum.elim y z)) (h_card : finrank ℂ V = n + n')
    {θ : PrimePadicIso → T} (hθ : ∀ ι, L.IsAllowed ι.prime (θ ι))
    {c δ b_vol b_short b_denom : ℝ} (hc : L.CovolumeLe y c) (hδ : L.IndexLe y δ)
    {γ : T → ℂ} (hγ_ne : ∀ ξ, γ ξ ≠ 0)
    (hz_int : ∀ i (ι : PrimePadicIso) ξ, L.IsAllowed ι.prime ξ →
      γ ξ • L.lift ξ (z i) ∈ L.lattice ξ ι)
    (hz_short : ∀ i σ, L.normSqAt (z i) σ ≤ exp b_short)
    (hγ : HeightLe b_denom fun ι ↦ ((‖γ (θ ι)‖ : ℂ) ^ 2)⁻¹)
    (hZ : HeightLe b_vol fun ι ↦ L.volume 1 / L.volume (θ ι)) :
    0 ≤ c + 2 * δ + n' * (b_short + b_denom) + b_vol := by
  -- write `Gram(1)` as a product of three factors and add their heights
  let G (ξ : T) : ℂ := (gram ℂ (L.lift ξ ∘ Sum.elim y z)).det
  have h_gram (ξ : T) : G ξ = L.volume ξ * (gram ℂ (Sum.elim y z)).det :=
    (det_gram_comp (L.lift ξ) (Sum.elim y z) (by simp [h_card])).trans (by simp [volume])
  have h_factor (ι : PrimePadicIso) : G 1 = ((‖γ (θ ι)‖ : ℂ) ^ 2) ^ n' * G (θ ι) *
      ((‖γ (θ ι)‖ : ℂ) ^ 2)⁻¹ ^ n' * (L.volume 1 / L.volume (θ ι)) := by
    have hγ_norm : (‖γ (θ ι)‖ : ℂ) ≠ 0 := by simpa using hγ_ne (θ ι)
    have hZ_ne : L.volume (θ ι) ≠ 0 := volume_ne_zero (h_inj (θ ι))
    simp [h_gram, field]
  have h_index : HeightLe (2 * δ) fun ι ↦ ((‖γ (θ ι)‖ : ℂ) ^ 2) ^ n' * G (θ ι) :=
    heightLe_pow_mul_det_gram hδ hθ (fun ι i ↦ hz_int i ι (θ ι) (hθ ι))
      fun ι i ↦ hz_int i ι.conj (θ ι) (hθ ι)
  have h_height : HeightLe (2 * δ + n' * b_denom + b_vol) fun _ ↦ G 1 := by
    simpa only [← h_factor, Pi.mul_def, Pi.pow_def] using (h_index.mul (hγ.pow n')).mul hZ
  -- compare with the conjugates of `Gram(1)` by the product formula
  have h_ne : G 1 ≠ 0 :=
    det_gram_ne_zero_iff_linearIndependent.2 (h_indep.map_injOn _ (h_inj 1).injOn)
  have h_conj (σ : ℂ ≃+* ℂ) : ‖σ (G 1)‖ ≤ exp (c + n' * b_short) :=
    (hc.sumElim hz_short).norm_map_det_gram_le σ
  linarith [h_height.neg_le_of_norm_map_le h_ne h_conj]

end TwistedLattice

end TauCeti
