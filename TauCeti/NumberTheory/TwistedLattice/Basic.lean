/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.PrimePadicIso
public import TauCeti.LinearAlgebra.Submodule.ColengthDvd
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Gram.Fischer
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.Matrix.GramFactorization

/-!
# Twisted lattices, index and covolume

Let `V` be a complex vector space and `T` a set of *twists* with a trivial twist `1`. A *twisted
lattice* on `V` (`TauCeti.TwistedLattice V T`) consists of

* for each twist `ξ` a complex inner product space `S_ξ` and a linear map `Θ_ξ : V → S_ξ`;
* a relation "`ξ` is allowed at `ℓ`" between twists and primes;
* for each `ξ` and each pair `ι` (a prime `ℓ` with an isomorphism `ℂ ≃+* PadicAlgCl ℓ`,
  `TauCeti.PrimePadicIso`) an `𝒪_ι`-submodule `Λ_{ξ,ι} ⊆ S_ξ`, such that `|ι ⟨φ, φ'⟩| ≤ 1`
  whenever `ξ` is allowed at `ℓ`, `φ ∈ Λ_{ξ,ι.conj}` and `φ' ∈ Λ_{ξ,ι}`;
* a finite set `C`, a linear map `coord : S_1 → ℂ^C` and a rational matrix `G`, positive definite
  as a complex matrix, with `⟨φ, φ'⟩ = coord(φ)^* G coord(φ')`.

A vector `v ∈ V` is integral at `ι` if `Θ_ξ v ∈ Λ_{ξ,ι}` for every twist `ξ` allowed at `ℓ`.
Integrality at `ι` is read through all twists allowed at its prime, while sizes are read through
the trivial twist alone: for an automorphism `σ` of `ℂ`, `σ Θ₁ v ∈ ℂ^C` is `coord (Θ₁ v)` with `σ`
applied to each coordinate, and `‖v‖²_σ = (σ Θ₁ v)^* G (σ Θ₁ v)`.

A finite family `y` has *index at most `δ`* if for numbers `δ_ℓ ≥ 0` with
`∑_{ℓ ∈ S} δ_ℓ log ℓ ≤ δ` over every finite set `S` of primes, every pair `ι` has a matrix
`u` over `𝒪_ι` with `|ι (det u)| ≥ ℓ ^ (-δ_ℓ)` carrying `y` into the vectors integral at `ι`; the
matrix is the same for all twists. It has *covolume at most `c`* if
`|det ((σ Θ₁ y_i)^* G (σ Θ₁ y_k))| ≤ e^c` for every `σ`. If `V` is a finite-dimensional inner
product space, `Z(ξ) = det (Θ_ξ^* Θ_ξ)` is the Gram determinant of the images of an orthonormal
basis.

The bounds for the covolume are Hadamard's and Fischer's inequalities for the Gram matrices taken
with `G`, and, since `G` is rational, the conjugate of a Gram determinant by `σ` pairs the
conjugates by `σ` and by `z ↦ conj (σ (conj z))`, which the Cauchy–Schwarz inequality for
determinants bounds (`Matrix.norm_det_inner_sq_le`).

## Main definitions

* `TauCeti.TwistedLattice`, `TauCeti.TwistedLattice.integralVectors`: twisted lattices and their
  integral vectors.
* `TauCeti.TwistedLattice.IndexLe`, `TauCeti.TwistedLattice.normSqAt`,
  `TauCeti.TwistedLattice.CovolumeLe`, `TauCeti.TwistedLattice.volume`: index and covolume of a
  family, the squared norms `‖v‖²_σ`, and `Z(ξ)`.

## Main results

* `TauCeti.TwistedLattice.IndexLe.mono`, `TauCeti.TwistedLattice.IndexLe.of_comp_equiv`,
  `TauCeti.TwistedLattice.IndexLe.sumElim`, `TauCeti.TwistedLattice.indexLe_of_colengthDvd`,
  `TauCeti.TwistedLattice.indexLe_card_mul`: the calculus of the index, and the index from
  colength bounds (`Submodule.ColengthDvd`).
* `TauCeti.TwistedLattice.covolumeLe_of_normSqAt_le`, `TauCeti.TwistedLattice.CovolumeLe.sumElim`,
  `TauCeti.TwistedLattice.CovolumeLe.norm_map_det_gram_le`: Hadamard's and Fischer's
  inequalities, and the conjugates of the Gram determinant for the trivial twist.
* `TauCeti.TwistedLattice.volume_ne_zero`, `TauCeti.TwistedLattice.volume_eq_det`: `Z(ξ) ≠ 0` for
  an injective `Θ_ξ`, and `Z(ξ) = det (Θ_ξ^* Θ_ξ)`.

## References

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `New/Reduction/Lattices/TwistedLattice.lean` (`New.TwistedLattice` and the
declarations named after it listed above), with the Gram determinant inequalities of
`Lib/General/LinearAlgebra/GramDeterminant.lean`.
-/

@[expose] public section

noncomputable section

open Finset Matrix Real Submodule
open scoped InnerProductSpace ComplexOrder

namespace TauCeti

/-- A *twisted lattice* on the complex vector space `V`, with twists `ξ : T` and trivial twist
`1`: linear maps `Θ_ξ = lift ξ` to inner product spaces, and in each of them a module of vectors
integral at each pair `ι`, such that, for `ξ` allowed at the prime of `ι`, the products of vectors
integral at `ι.conj` with vectors integral at `ι` are integral at `ι`; and coordinates on the space
for the trivial twist in which the inner product has a rational matrix. -/
structure TwistedLattice (V T : Type) [AddCommGroup V] [Module ℂ V] [One T] where
  /-- The inner product space `S_ξ` of the twist `ξ`. -/
  Space : T → Type
  [normedAddCommGroup (ξ : T) : NormedAddCommGroup (Space ξ)]
  [innerProductSpace (ξ : T) : InnerProductSpace ℂ (Space ξ)]
  /-- The map `Θ_ξ`. -/
  lift (ξ : T) : V →ₗ[ℂ] Space ξ
  /-- The twist `ξ` is allowed at the prime `ℓ`. -/
  IsAllowed : ℕ → T → Prop
  /-- The vectors of `S_ξ` integral at the pair `ι`. -/
  lattice (ξ : T) (ι : PrimePadicIso) : Submodule ι.integers (Space ξ)
  /-- For `ξ` allowed at the prime of `ι`, the product of a vector integral at `ι.conj` and a vector
  integral at `ι` is integral at `ι`. -/
  norm_inner_le_one {ξ : T} (ι : PrimePadicIso) (hξ : IsAllowed ι.prime ξ) :
    ∀ φ ∈ lattice ξ ι.conj, ∀ φ' ∈ lattice ξ ι, ‖ι.iso ⟪φ, φ'⟫_ℂ‖ ≤ 1
  /-- The finite set `C` of coordinates on `S_1`. -/
  Coord : Type
  [fintypeCoord : Fintype Coord]
  /-- The coordinates of a vector of `S_1`. -/
  coord : Space 1 →ₗ[ℂ] Coord → ℂ
  /-- The rational matrix `G` of the inner product in these coordinates. -/
  gramMatrix : Matrix Coord Coord ℚ
  /-- `G` is positive definite as a complex matrix. -/
  posDef_gramMatrix : (gramMatrix.map (↑) : Matrix Coord Coord ℂ).PosDef
  /-- The inner product is `coord(φ)^* G coord(φ')`. -/
  inner_eq (φ φ' : Space 1) : ⟪φ, φ'⟫_ℂ = star (coord φ) ⬝ᵥ gramMatrix.map (↑) *ᵥ coord φ'

namespace TwistedLattice

attribute [instance] normedAddCommGroup innerProductSpace fintypeCoord

section Index

variable {V T : Type} [AddCommGroup V] [Module ℂ V] [One T] (L : TwistedLattice V T)

/-- The vectors of `V` integral at the pair `ι`: those `v` with `Θ_ξ v` integral at `ι` for every
twist `ξ` allowed at the prime of `ι`. -/
def integralVectors (ι : PrimePadicIso) : Submodule ι.integers V :=
  ⨅ (ξ : T) (_ : L.IsAllowed ι.prime ξ), (L.lattice ξ ι).comap ((L.lift ξ).restrictScalars _)

variable {L} in
theorem mem_integralVectors {ι : PrimePadicIso} {v : V} :
    v ∈ L.integralVectors ι ↔ ∀ ξ, L.IsAllowed ι.prime ξ → L.lift ξ v ∈ L.lattice ξ ι := by
  simp [integralVectors]

variable {S S' : Type} [Fintype S] [Fintype S'] [DecidableEq S] [DecidableEq S']

/-- The family `y` has *index at most `δ`*: there are numbers `e ℓ ≥ 0` with `∑ e ℓ log ℓ ≤ δ`
over every finite set of primes, such that every pair `ι` has a matrix `u` over `𝒪_ι` with
`|ι (det u)| ≥ ℓ ^ (-e ℓ)` carrying `y` into the vectors integral at `ι`. The matrix does not
depend on the twist. -/
def IndexLe (y : S → V) (δ : ℝ) : Prop :=
  ∃ e : ℕ → ℝ, (∀ ℓ, 0 ≤ e ℓ) ∧ (∀ U : Finset ℕ, (∀ ℓ ∈ U, ℓ.Prime) → ∑ ℓ ∈ U, e ℓ * log ℓ ≤ δ) ∧
    ∀ ι : PrimePadicIso, ∃ u : Matrix S S ι.integers,
      (ι.prime : ℝ) ^ (-e ι.prime) ≤ ‖ι.iso u.det‖ ∧
        ∀ i, ∑ k, u i k • y k ∈ L.integralVectors ι

variable {L}

/-- Index bounds increase with `δ`. -/
theorem IndexLe.mono {y : S → V} {δ δ' : ℝ} (hy : L.IndexLe y δ) (hδ : δ ≤ δ') :
    L.IndexLe y δ' := by
  obtain ⟨e, he_nonneg, he_sum, hu⟩ := hy
  exact ⟨e, he_nonneg, fun U hU ↦ (he_sum U hU).trans hδ, hu⟩

/-- The index does not depend on the numbering of the family: if `y ∘ f` has index at most `δ` for
a bijection `f`, then so has `y`. -/
theorem IndexLe.of_comp_equiv {y : S → V} {δ : ℝ} (f : S' ≃ S) (hy : L.IndexLe (y ∘ f) δ) :
    L.IndexLe y δ := by
  obtain ⟨e, he_nonneg, he_sum, h_carries⟩ := hy
  refine ⟨e, he_nonneg, he_sum, fun ι ↦ ?_⟩
  obtain ⟨u, hu_det, hu_mem⟩ := h_carries ι
  refine ⟨u.submatrix f.symm f.symm, by simpa using hu_det, fun i ↦ ?_⟩
  simpa [← f.sum_comp] using hu_mem (f.symm i)

/-- **The index from colength bounds.** Let `e ℓ ≥ 0` with `∑ e ℓ log ℓ ≤ δ` over every finite set
of primes. If for every pair `ι` the family `y` lies in an `𝒪_ι`-module `M` in which the vectors
integral at `ι` have colength dividing `ℓ ^ j` (`Submodule.ColengthDvd`) for an integer
`j ≤ e ℓ`, then `y` has index at most `δ`. -/
theorem indexLe_of_colengthDvd {n : ℕ} {y : Fin n → V} {δ : ℝ} {e : ℕ → ℝ}
    (he_nonneg : ∀ ℓ, 0 ≤ e ℓ)
    (he_sum : ∀ U : Finset ℕ, (∀ ℓ ∈ U, ℓ.Prime) → ∑ ℓ ∈ U, e ℓ * log ℓ ≤ δ)
    (h_local : ∀ ι : PrimePadicIso, ∃ (j : ℕ) (M : Submodule ι.integers V),
      j ≤ e ι.prime ∧ (∀ i, y i ∈ M) ∧ M.ColengthDvd (L.integralVectors ι) ((ι.prime : _) ^ j)) :
    L.IndexLe y δ := by
  refine ⟨e, he_nonneg, he_sum, fun ι ↦ ?_⟩
  obtain ⟨j, M, hj, hy, h_colength⟩ := h_local ι
  obtain ⟨u, hu_dvd, hu_mem⟩ := h_colength n y hy
  refine ⟨u, ?_, hu_mem⟩
  have hℓ : (1 : ℝ) ≤ ι.prime := mod_cast (Fact.out : ι.prime.Prime).one_le
  calc (ι.prime : ℝ) ^ (-e ι.prime) ≤ (ι.prime : ℝ) ^ (-(j : ℝ)) :=
        rpow_le_rpow_of_exponent_le hℓ (neg_le_neg hj)
    _ = ((ι.prime : ℝ) ^ j)⁻¹ := by rw [rpow_neg (by positivity), rpow_natCast]
    _ ≤ ‖ι.iso u.det‖ := ι.inv_pow_le_norm_of_dvd hu_dvd

/-- If two families have index at most `δ` and `δ'`, their union has index at most `δ + δ'`. -/
theorem IndexLe.sumElim {y : S → V} {y' : S' → V} {δ δ' : ℝ} (hy : L.IndexLe y δ)
    (hy' : L.IndexLe y' δ') : L.IndexLe (Sum.elim y y') (δ + δ') := by
  -- add the numbers `e ℓ` and put the two matrices in diagonal blocks
  obtain ⟨e, he_nonneg, he_sum, h_carries⟩ := hy
  obtain ⟨e', he'_nonneg, he'_sum, h_carries'⟩ := hy'
  refine ⟨e + e', fun ℓ ↦ add_nonneg (he_nonneg ℓ) (he'_nonneg ℓ), fun U hU ↦ ?_, fun ι ↦ ?_⟩
  · simpa [add_mul, sum_add_distrib] using add_le_add (he_sum U hU) (he'_sum U hU)
  obtain ⟨⟨u, hu_det, hu_mem⟩, ⟨u', hu'_det, hu'_mem⟩⟩ := And.intro (h_carries ι) (h_carries' ι)
  refine ⟨fromBlocks u 0 0 u', ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, Pi.add_apply, neg_add,
      rpow_add (mod_cast (Fact.out : ι.prime.Prime).pos), MulMemClass.coe_mul, map_mul, norm_mul]
    exact mul_le_mul hu_det hu'_det (by positivity) (norm_nonneg _)
  · rintro (i | i)
    · simpa using hu_mem i
    · simpa using hu'_mem i

/-- Let `t` be a finite set and `A s ⊆ V` (`s ∈ t`) sets such that every finite family in `A s`
has index at most `δ`. Then every finite family with members in `⋃_{s ∈ t} A s` has index at
most `#t δ`. -/
theorem indexLe_card_mul {y : S → V} {δ : ℝ} {κ : Type} {A : κ → Set V} (t : Finset κ)
    (hA : ∀ s ∈ t, ∀ (n : ℕ) (z : Fin n → V), (∀ i, z i ∈ A s) → L.IndexLe z δ)
    (hy : ∀ i, ∃ s ∈ t, y i ∈ A s) : L.IndexLe y (#t * δ) := by
  induction t using Finset.cons_induction generalizing S with
  | empty =>
    have : IsEmpty S := ⟨fun i ↦ by simpa using hy i⟩
    exact ⟨0, fun _ ↦ le_rfl, by simp, fun ι ↦ ⟨1, by simp, isEmptyElim⟩⟩
  | cons s t hs ih =>
    -- split the family into the members of `A s` and the rest
    classical
    let p (i : S) : Prop := y i ∈ A s
    let f : Fin (Fintype.card {i // p i}) ≃ {i // p i} := (Fintype.equivFin _).symm
    have h_mem : L.IndexLe (fun i : {i // p i} ↦ y i) δ :=
      .of_comp_equiv f (hA s (mem_cons_self s t) _ _ fun i ↦ (f i).prop)
    have h_rest : L.IndexLe (fun i : {i // ¬p i} ↦ y i) (#t * δ) := by
      refine ih (fun s' hs' ↦ hA s' (mem_cons_of_mem hs')) fun i ↦ ?_
      simpa [i.prop, p] using hy i
    refine .of_comp_equiv (Equiv.sumCompl p) ?_
    rw [card_cons, Nat.cast_succ, add_one_mul, add_comm,
      ← Sum.elim_comp_inl_inr (y ∘ Equiv.sumCompl p)]
    exact h_mem.sumElim h_rest

end Index

section Covolume

variable {V T : Type} [AddCommGroup V] [Module ℂ V] [One T] (L : TwistedLattice V T)

/-- The coordinates `σ Θ₁ v` of `Θ₁ v`, with the automorphism `σ` of `ℂ` applied to each. -/
def conjCoord (σ : ℂ ≃+* ℂ) (v : V) : L.Coord → ℂ := σ ∘ L.coord (L.lift 1 v)

/-- The squared norm `‖v‖²_σ = (σ Θ₁ v)^* G (σ Θ₁ v)`. -/
def normSqAt (v : V) (σ : ℂ ≃+* ℂ) : ℝ :=
  (star (L.conjCoord σ v) ⬝ᵥ L.gramMatrix.map (↑) *ᵥ L.conjCoord σ v).re

/-- The Gram matrix `((σ Θ₁ y_i)^* G (σ Θ₁ y_k))_{i,k}` of the family `y` at the automorphism `σ`
of `ℂ`. -/
def gramAt {S : Type} (σ : ℂ ≃+* ℂ) (y : S → V) : Matrix S S ℂ :=
  of fun i k ↦ star (L.conjCoord σ (y i)) ⬝ᵥ L.gramMatrix.map (↑) *ᵥ L.conjCoord σ (y k)

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The family `y` has *covolume at most `c`*: `|det ((σ Θ₁ y_i)^* G (σ Θ₁ y_k))| ≤ e^c` for every
automorphism `σ` of `ℂ`. -/
def CovolumeLe (y : S → V) (c : ℝ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, ‖(L.gramAt σ y).det‖ ≤ exp c

variable {L}

/-- The positive definite matrix `G` is the Gram matrix of a linear map into a Euclidean space:
`a^* G b = ⟪e a, e b⟫`. -/
private theorem exists_linearMap_inner_eq :
    ∃ e : (L.Coord → ℂ) →ₗ[ℂ] EuclideanSpace ℂ L.Coord,
      ∀ a b, star a ⬝ᵥ L.gramMatrix.map (↑) *ᵥ b = ⟪e a, e b⟫_ℂ := by
  obtain ⟨B, hB⟩ := posSemidef_iff_eq_conjTranspose_mul_self.1 L.posDef_gramMatrix.posSemidef
  let e : (L.Coord → ℂ) →ₗ[ℂ] EuclideanSpace ℂ L.Coord :=
    { toFun a := WithLp.toLp 2 (B *ᵥ a)
      map_add' a b := by simp [mulVec_add]
      map_smul' c a := by simp [mulVec_smul] }
  refine ⟨e, fun a b ↦ ?_⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [e, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, star_mulVec, hB,
    ← mulVec_mulVec, dotProduct_mulVec]
  rw [dotProduct_comm (B *ᵥ b), dotProduct_mulVec, dotProduct_comm]

/-- The Gram matrix at `σ` is the Gram matrix of a family in a Euclidean space, whose squared norms
are the `‖y i‖²_σ`. -/
private theorem exists_gramAt_eq_gram :
    ∃ e : (L.Coord → ℂ) →ₗ[ℂ] EuclideanSpace ℂ L.Coord,
      (∀ a b, star a ⬝ᵥ L.gramMatrix.map (↑) *ᵥ b = ⟪e a, e b⟫_ℂ) ∧
      (∀ {S : Type} (σ : ℂ ≃+* ℂ) (y : S → V), L.gramAt σ y = gram ℂ (e ∘ L.conjCoord σ ∘ y)) ∧
      ∀ σ v, L.normSqAt v σ = ‖e (L.conjCoord σ v)‖ ^ 2 := by
  obtain ⟨e, he⟩ := exists_linearMap_inner_eq (L := L)
  refine ⟨e, he, fun σ y ↦ ?_, fun σ v ↦ ?_⟩
  · ext i k
    simp [gramAt, he]
  · rw [normSqAt, he]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- **Hadamard's inequality.** If `‖z_i‖²_σ ≤ e^h` for `i = 1, …, n` and every automorphism `σ` of
`ℂ`, then `z_1, …, z_n` has covolume at most `n h`. -/
theorem covolumeLe_of_normSqAt_le {n : ℕ} {z : Fin n → V} {h : ℝ}
    (hz : ∀ i σ, L.normSqAt (z i) σ ≤ exp h) : L.CovolumeLe z (n * h) := by
  obtain ⟨e, -, he_gram, he_norm⟩ := exists_gramAt_eq_gram (L := L)
  intro σ
  rw [he_gram, (posSemidef_gram ℂ _).norm_det_eq_re_det]
  calc RCLike.re (gram ℂ (e ∘ L.conjCoord σ ∘ z)).det
      ≤ ∏ i, ‖e (L.conjCoord σ (z i))‖ ^ 2 := re_det_gram_le_prod_norm_sq _
    _ ≤ ∏ _i : Fin n, exp h :=
        Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ he_norm σ (z i) ▸ hz i σ
    _ = exp (n * h) := by rw [Fin.prod_const, ← exp_natCast_mul]

/-- **Fischer's inequality.** If `y` has covolume at most `c` and `‖z_i‖²_σ ≤ e^h` for
`i = 1, …, n` and every automorphism `σ` of `ℂ`, then `y` together with `z_1, …, z_n` has
covolume at most `c + n h`. -/
theorem CovolumeLe.sumElim {y : S → V} {n : ℕ} {z : Fin n → V} {c h : ℝ} (hy : L.CovolumeLe y c)
    (hz : ∀ i σ, L.normSqAt (z i) σ ≤ exp h) : L.CovolumeLe (Sum.elim y z) (c + n * h) := by
  obtain ⟨e, -, he_gram, -⟩ := exists_gramAt_eq_gram (L := L)
  intro σ
  have hy' := hy σ
  have hz' := covolumeLe_of_normSqAt_le hz σ
  rw [he_gram] at hy' hz' ⊢
  rw [Sum.comp_elim, Sum.comp_elim, exp_add]
  exact (norm_det_gram_sumElim_le _ _).trans
    (mul_le_mul hy' hz' (norm_nonneg _) (exp_nonneg c))

/-- Since `G` is rational, `σ ⟪Θ₁ v, Θ₁ w⟫ = (σ' Θ₁ v)^* G (σ Θ₁ w)` with
`σ' z = conj (σ (conj z))`. -/
private theorem map_inner_lift_one (σ : ℂ ≃+* ℂ) (v w : V) :
    σ ⟪L.lift 1 v, L.lift 1 w⟫_ℂ = star (L.conjCoord ((starRingAut.trans σ).trans starRingAut) v) ⬝ᵥ
      L.gramMatrix.map (↑) *ᵥ L.conjCoord σ w := by
  simp [conjCoord, inner_eq, dotProduct, mulVec]

/-- **Conjugates of the Gram determinant.** If `y` has covolume at most `c`, then
`|σ (det ⟨Θ₁ y_i, Θ₁ y_k⟩)| ≤ e^c` for every automorphism `σ` of `ℂ`. -/
theorem CovolumeLe.norm_map_det_gram_le {y : S → V} {c : ℝ} (hy : L.CovolumeLe y c)
    (σ : ℂ ≃+* ℂ) : ‖σ (gram ℂ (L.lift 1 ∘ y)).det‖ ≤ exp c := by
  -- `σ Gram(1)` pairs the conjugates by `σ'` and by `σ`
  obtain ⟨e, he', he_gram, -⟩ := exists_gramAt_eq_gram (L := L)
  set σ' : ℂ ≃+* ℂ := (starRingAut.trans σ).trans starRingAut
  have h_pair : σ (gram ℂ (L.lift 1 ∘ y)).det =
      (of fun i k ↦ ⟪e (L.conjCoord σ' (y i)), e (L.conjCoord σ (y k))⟫_ℂ).det := by
    rw [show σ (gram ℂ (L.lift 1 ∘ y)).det = (σ : ℂ →+* ℂ) (gram ℂ (L.lift 1 ∘ y)).det from rfl,
      RingHom.map_det]
    congr 1
    ext i k
    simp [← he', ← map_inner_lift_one, σ']
  have h1 := hy σ'
  have h2 := hy σ
  rw [he_gram] at h1 h2
  refine le_of_sq_le_sq ?_ (exp_nonneg c)
  rw [h_pair]
  calc _ ≤ ‖(gram ℂ (e ∘ L.conjCoord σ' ∘ y)).det‖ * ‖(gram ℂ (e ∘ L.conjCoord σ ∘ y)).det‖ :=
        norm_det_inner_sq_le _ _
    _ ≤ exp c * exp c := mul_le_mul h1 h2 (norm_nonneg _) (exp_nonneg c)
    _ = exp c ^ 2 := (sq _).symm

end Covolume

section Volume

variable {V T : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [One T] (L : TwistedLattice V T)

/-- The number `Z(ξ) = det (Θ_ξ^* Θ_ξ)`, the Gram determinant of the images under `Θ_ξ` of an
orthonormal basis of `V`, written through Mathlib's `LinearMap.normDet`. -/
def volume (ξ : T) : ℂ := ((L.lift ξ).normDet ^ 2 : ℝ)

variable {L}

/-- If `Θ_ξ` is injective, then `Z(ξ) ≠ 0`. -/
theorem volume_ne_zero {ξ : T} (h_inj : Function.Injective (L.lift ξ)) :
    L.volume ξ ≠ 0 := by
  simp [volume, LinearMap.normDet_eq_zero_iff_ker_ne_bot, LinearMap.ker_eq_bot.2 h_inj]

/-- If `S_ξ` is finite-dimensional, then `Z(ξ) = det (Θ_ξ^* Θ_ξ)`. -/
theorem volume_eq_det (ξ : T) [FiniteDimensional ℂ (L.Space ξ)] :
    L.volume ξ = (LinearMap.adjoint (L.lift ξ) ∘ₗ L.lift ξ).det := by
  simp [volume, ← LinearMap.normDet_sq]

end Volume

end TwistedLattice

end TauCeti
