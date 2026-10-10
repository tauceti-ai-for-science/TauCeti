/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.FanDominance
public import TauCeti.Data.Set.Card

/-!
# Orthogonal block sums of linear maps

For linear maps `A : E₁ →ₗ F₁` and `B : E₂ →ₗ F₂`, the orthogonal block sum `A ⊕ B` is the
block-diagonal map `(x, y) ↦ (A x, B y)` between the `L²` products `WithLp 2 (E₁ × E₂)` and
`WithLp 2 (F₁ × F₂)`. When the factors are inner product spaces, these products are the orthogonal
direct sums, so `A ⊕ B` acts on two mutually orthogonal blocks independently.

This file defines `LinearMap.orthogonalBlockSum` and computes the data that unitarily invariant
norms see. The adjoint and the Gram operator are formed blockwise, so the eigenspaces of the Gram
operator of `A ⊕ B` are products of those of `A` and `B`: every positive singular value of `A ⊕ B`
occurs as often as in `A` and `B` together. In particular doubling `A ⊕ A` repeats each singular
value of `A` twice, and its Ky Fan sums are `K₂ₖ(A ⊕ A) = 2 Kₖ(A)`.

On the norm side, block sums preserve the convex hulls of two-sided unitary orbits: if `A` lies in
the orbit hull of `C` and `B` in that of `D`, then `A ⊕ B` lies in that of `C ⊕ D`. Combined with
the orbit-hull characterization of Ky Fan domination, two separate Ky Fan majorizations
`Kₖ(A) ≤ Kₖ(C)` and `Kₖ(B) ≤ Kₖ(D)` give `N(A ⊕ B) ≤ N(C ⊕ D)` for every unitarily invariant
seminorm `N` on the block sums, with no loss of constant.

## Main declarations

* `LinearMap.orthogonalBlockSum`: the orthogonal block sum `A ⊕ B`.
* `LinearMap.orthogonalBlockSum_apply`: `(A ⊕ B)(x, y) = (A x, B y)`.
* `LinearMap.orthogonalBlockSum_comp`: `(A₁ ⊕ B₁)(A₂ ⊕ B₂) = A₁A₂ ⊕ B₁B₂`.
* `LinearMap.adjoint_orthogonalBlockSum`: `(A ⊕ B)† = A† ⊕ B†`.
* `LinearMap.finrank_eigenspace_orthogonalBlockSum`: the eigenspaces of `T₁ ⊕ T₂` have dimension
  `dim ker(T₁ - μ) + dim ker(T₂ - μ)`.
* `LinearMap.ncard_ofPred_singularValues_orthogonalBlockSum`: a positive value occurs among the
  singular values of `A ⊕ B` as often as among those of `A` and `B` together.
* `LinearMap.singularValues_orthogonalBlockSum_self`: `σᵢ(A ⊕ A) = σ_{⌊i/2⌋}(A)`.
* `LinearMap.kyFanSum_orthogonalBlockSum_self`: `K₂ₖ(A ⊕ A) = 2 Kₖ(A)`.
* `LinearMap.orthogonalBlockSum_mem_twoSidedUnitaryOrbitHull`: block sums preserve orbit hulls.
* `TauCeti.UnitarilyInvariantSeminorm.map_orthogonalBlockSum_le_of_kyFanSum_le`: the sharp
  block-sum comparison under Ky Fan domination.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Sections III.1
  and IV.2 (singular values of direct sums, Ky Fan norms and unitarily invariant norms).
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
-/

public section

open Module Module.End WithLp

namespace LinearMap

section Module

variable {R E₁ E₂ F₁ F₂ G₁ G₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]
  [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₂] [Module R F₂]
  [AddCommGroup G₁] [Module R G₁] [AddCommGroup G₂] [Module R G₂]

/-- The **orthogonal block sum** `A ⊕ B : (x, y) ↦ (A x, B y)` of two linear maps, between the
`L²` products `WithLp 2 (E₁ × E₂)` and `WithLp 2 (F₁ × F₂)`. -/
def orthogonalBlockSum (A : E₁ →ₗ[R] F₁) (B : E₂ →ₗ[R] F₂) :
    WithLp 2 (E₁ × E₂) →ₗ[R] WithLp 2 (F₁ × F₂) :=
  withLpMap 2 (A.prodMap B)

/-- **Componentwise action.** `(A ⊕ B)(x, y) = (A x, B y)`. -/
@[simp]
theorem orthogonalBlockSum_apply (A : E₁ →ₗ[R] F₁) (B : E₂ →ₗ[R] F₂) (x : WithLp 2 (E₁ × E₂)) :
    A.orthogonalBlockSum B x = toLp 2 (A x.fst, B x.snd) := by
  simp [orthogonalBlockSum, WithLp.map]

/-- **Composition of block sums.** `(A₁ ⊕ B₁)(A₂ ⊕ B₂) = A₁A₂ ⊕ B₁B₂`. -/
theorem orthogonalBlockSum_comp (A₁ : F₁ →ₗ[R] G₁) (B₁ : F₂ →ₗ[R] G₂) (A₂ : E₁ →ₗ[R] F₁)
    (B₂ : E₂ →ₗ[R] F₂) :
    A₁.orthogonalBlockSum B₁ ∘ₗ A₂.orthogonalBlockSum B₂ =
      (A₁ ∘ₗ A₂).orthogonalBlockSum (B₁ ∘ₗ B₂) := by
  ext x : 1
  simp

@[simp]
theorem orthogonalBlockSum_id :
    (id : E₁ →ₗ[R] E₁).orthogonalBlockSum (id : E₂ →ₗ[R] E₂) = id := by
  ext x : 1
  simp [WithLp.ext_iff, Prod.ext_iff]

@[simp]
theorem orthogonalBlockSum_zero :
    (0 : E₁ →ₗ[R] F₁).orthogonalBlockSum (0 : E₂ →ₗ[R] F₂) = 0 := by
  ext x : 1
  simp

theorem orthogonalBlockSum_add (A₁ A₂ : E₁ →ₗ[R] F₁) (B₁ B₂ : E₂ →ₗ[R] F₂) :
    (A₁ + A₂).orthogonalBlockSum (B₁ + B₂) =
      A₁.orthogonalBlockSum B₁ + A₂.orthogonalBlockSum B₂ := by
  ext x : 1
  simp [WithLp.ext_iff]

@[simp]
theorem orthogonalBlockSum_smul {S : Type*} [Monoid S] [DistribMulAction S F₁]
    [DistribMulAction S F₂] [SMulCommClass R S F₁] [SMulCommClass R S F₂] (c : S)
    (A : E₁ →ₗ[R] F₁) (B : E₂ →ₗ[R] F₂) :
    (c • A).orthogonalBlockSum (c • B) = c • A.orthogonalBlockSum B := by
  ext x : 1
  simp [WithLp.ext_iff]

end Module

section Field

variable {K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]

/-- The eigenspace of a block sum of endomorphisms is the product of the eigenspaces of the
blocks, so its dimension is the sum of their dimensions. -/
theorem finrank_eigenspace_orthogonalBlockSum (T₁ : V₁ →ₗ[K] V₁) (T₂ : V₂ →ₗ[K] V₂) (μ : K) :
    finrank K (eigenspace (T₁.orthogonalBlockSum T₂) μ) =
      finrank K (eigenspace T₁ μ) + finrank K (eigenspace T₂ μ) := by
  have hmem {x : WithLp 2 (V₁ × V₂)} :
      x ∈ eigenspace (T₁.orthogonalBlockSum T₂) μ ↔
        x.fst ∈ eigenspace T₁ μ ∧ x.snd ∈ eigenspace T₂ μ := by
    simp only [mem_eigenspace_iff, orthogonalBlockSum_apply]
    constructor
    · intro h
      exact ⟨by simpa using congrArg WithLp.fst h, by simpa using congrArg WithLp.snd h⟩
    · rintro ⟨h₁, h₂⟩
      simp [WithLp.ext_iff, Prod.ext_iff, h₁, h₂]
  let e : eigenspace (T₁.orthogonalBlockSum T₂) μ ≃ₗ[K] eigenspace T₁ μ × eigenspace T₂ μ :=
    { toFun x := (⟨x.1.fst, (hmem.mp x.2).1⟩, ⟨x.1.snd, (hmem.mp x.2).2⟩)
      invFun y := ⟨toLp 2 (y.1.1, y.2.1), hmem.mpr ⟨by simp, by simp⟩⟩
      map_add' x y := rfl
      map_smul' c x := rfl
      left_inv x := Subtype.ext (toLp_ofLp 2 x.1)
      right_inv y := rfl }
  rw [e.finrank_eq, finrank_prod]

end Field

section InnerProductSpace

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-! ### Orbit hulls -/

/-- The block sum of two linear isometric equivalences is the linear map underlying their `L²`
product `LinearIsometryEquiv.withLpProdCongr`. -/
theorem orthogonalBlockSum_linearIsometryEquiv (U : E₁ ≃ₗᵢ[𝕜] F₁) (V : E₂ ≃ₗᵢ[𝕜] F₂) :
    (U : E₁ →ₗ[𝕜] F₁).orthogonalBlockSum (V : E₂ →ₗ[𝕜] F₂) =
      (U.withLpProdCongr 2 V : WithLp 2 (E₁ × E₂) →ₗ[𝕜] WithLp 2 (F₁ × F₂)) := by
  ext x : 1
  simp

/-- Block sums of points of two-sided unitary orbits lie in the two-sided unitary orbit of the
block sum. -/
theorem orthogonalBlockSum_mem_twoSidedUnitaryOrbit {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : A ∈ C.twoSidedUnitaryOrbit) (hB : B ∈ D.twoSidedUnitaryOrbit) :
    A.orthogonalBlockSum B ∈ (C.orthogonalBlockSum D).twoSidedUnitaryOrbit := by
  obtain ⟨U₁, V₁, rfl⟩ := mem_twoSidedUnitaryOrbit.mp hA
  obtain ⟨U₂, V₂, rfl⟩ := mem_twoSidedUnitaryOrbit.mp hB
  refine mem_twoSidedUnitaryOrbit.mpr ⟨U₁.withLpProdCongr 2 U₂, V₁.withLpProdCongr 2 V₂, ?_⟩
  rw [← orthogonalBlockSum_linearIsometryEquiv, ← orthogonalBlockSum_linearIsometryEquiv,
    orthogonalBlockSum_comp, orthogonalBlockSum_comp]

/-- **Block sums preserve orbit hulls.** If `A` lies in the convex hull of the two-sided unitary
orbit of `C` and `B` in that of `D`, then `A ⊕ B` lies in the convex hull of the two-sided unitary
orbit of `C ⊕ D`. -/
theorem orthogonalBlockSum_mem_twoSidedUnitaryOrbitHull {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂}
    (hA : A ∈ C.twoSidedUnitaryOrbitHull) (hB : B ∈ D.twoSidedUnitaryOrbitHull) :
    A.orthogonalBlockSum B ∈ (C.orthogonalBlockSum D).twoSidedUnitaryOrbitHull := by
  -- First let `A` range over the orbit hull of `C` with `B` in the orbit of `D`, then let `B`
  -- range over the orbit hull of `D`; in each step the admissible blocks form a convex set.
  have hleft {Y : E₂ →ₗ[𝕜] F₂} (hY : Y ∈ D.twoSidedUnitaryOrbit) :
      A.orthogonalBlockSum Y ∈ (C.orthogonalBlockSum D).twoSidedUnitaryOrbitHull := by
    refine twoSidedUnitaryOrbitHull_subset
      (S := {X | X.orthogonalBlockSum Y ∈ (C.orthogonalBlockSum D).twoSidedUnitaryOrbitHull})
      (fun X hX ↦ twoSidedUnitaryOrbit_subset_twoSidedUnitaryOrbitHull _
        (orthogonalBlockSum_mem_twoSidedUnitaryOrbit hX hY))
      (fun X hX X' hX' a b ha hb hab ↦ ?_) hA
    have h := smul_add_smul_mem_twoSidedUnitaryOrbitHull hX hX' ha hb hab
    rwa [← orthogonalBlockSum_smul, ← orthogonalBlockSum_smul, ← orthogonalBlockSum_add,
      Convex.combo_self (by exact_mod_cast hab)] at h
  refine twoSidedUnitaryOrbitHull_subset
    (S := {Y | A.orthogonalBlockSum Y ∈ (C.orthogonalBlockSum D).twoSidedUnitaryOrbitHull})
    (fun Y hY ↦ hleft hY) (fun Y hY Y' hY' a b ha hb hab ↦ ?_) hB
  have h := smul_add_smul_mem_twoSidedUnitaryOrbitHull hY hY' ha hb hab
  rwa [← orthogonalBlockSum_smul, ← orthogonalBlockSum_smul, ← orthogonalBlockSum_add,
    Convex.combo_self (by exact_mod_cast hab)] at h

/-! ### Adjoints, Gram operators and singular values -/

variable [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂] [FiniteDimensional 𝕜 F₁]
  [FiniteDimensional 𝕜 F₂]

/-- **Adjoint of a block sum.** `(A ⊕ B)† = A† ⊕ B†`. -/
@[simp]
theorem adjoint_orthogonalBlockSum (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂) :
    adjoint (A.orthogonalBlockSum B) = (adjoint A).orthogonalBlockSum (adjoint B) := by
  refine ((eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply, adjoint_inner_left]

/-- A positive value `s` occurs among the singular values of `A ⊕ B` as often as among those of
`A` and of `B` together. -/
theorem ncard_ofPred_singularValues_orthogonalBlockSum (A : E₁ →ₗ[𝕜] F₁) (B : E₂ →ₗ[𝕜] F₂)
    {s : ℝ} (hs : 0 < s) :
    {i | (A.orthogonalBlockSum B).singularValues i = s}.ncard =
      {i | A.singularValues i = s}.ncard + {i | B.singularValues i = s}.ncard := by
  rw [ncard_ofPred_singularValues_eq _ hs, ncard_ofPred_singularValues_eq _ hs,
    ncard_ofPred_singularValues_eq _ hs, adjoint_orthogonalBlockSum, orthogonalBlockSum_comp,
    finrank_eigenspace_orthogonalBlockSum]

/-- **Singular values of a doubled block.** The singular values of `A ⊕ A` are those of `A`, each
repeated twice: `σᵢ(A ⊕ A) = σ_{⌊i/2⌋}(A)`. -/
theorem singularValues_orthogonalBlockSum_self (A : E₁ →ₗ[𝕜] F₁) (i : ℕ) :
    (A.orthogonalBlockSum A).singularValues i = A.singularValues (i / 2) := by
  -- The sequence `i ↦ σ_{⌊i/2⌋}(A)` lists every singular value of `A` twice; it vanishes from
  -- `2 * dim E₁` on.
  let d : ℕ →₀ ℝ :=
    Finsupp.ofSupportFinite (fun i ↦ A.singularValues (i / 2))
      ((Set.finite_Iio (2 * finrank 𝕜 E₁)).subset fun i hi ↦ Set.mem_Iio.mpr <| by
        by_contra h
        exact hi (A.singularValues_of_finrank_le (by omega)))
  have hd (i : ℕ) : d i = A.singularValues (i / 2) := congrFun Finsupp.ofSupportFinite_coe i
  suffices (A.orthogonalBlockSum A).singularValues = d by rw [this, hd]
  refine Finsupp.eq_of_antitone_of_ncard_eq (singularValues_antitone _)
    (fun i j hij ↦ by simpa only [hd] using A.singularValues_antitone (Nat.div_le_div_right hij))
    fun s hs ↦ ?_
  rcases (lt_or_gt_of_ne hs) with hs | hs
  · have hempty (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) : {i | f i = s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun i hi ↦ (hf i).not_gt (hi ▸ hs)
    rw [hempty _ (singularValues_nonneg _), hempty d fun i ↦ by
      simpa only [hd] using A.singularValues_nonneg _]
  · rw [ncard_ofPred_singularValues_orthogonalBlockSum A A hs, ← mul_two,
      ← Set.ncard_preimage_div]
    simp only [hd, Set.preimage_ofPred_eq]

/-- **Ky Fan sums of a doubled block.** `K₂ₖ(A ⊕ A) = 2 Kₖ(A)`. -/
theorem kyFanSum_orthogonalBlockSum_self (A : E₁ →ₗ[𝕜] F₁) (k : ℕ) :
    (A.orthogonalBlockSum A).kyFanSum (2 * k) = 2 * A.kyFanSum k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, kyFanSum_succ, kyFanSum_succ, ih,
      singularValues_orthogonalBlockSum_self, singularValues_orthogonalBlockSum_self,
      show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega, kyFanSum_succ]
    ring

end InnerProductSpace

end LinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [FiniteDimensional 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

/-- **Sharp block-sum comparison.** If every Ky Fan sum of `A` is at most the corresponding one of
`C`, and likewise for `B` and `D`, then `N (A ⊕ B) ≤ N (C ⊕ D)` for every unitarily invariant
seminorm `N` on the block sums. -/
theorem map_orthogonalBlockSum_le_of_kyFanSum_le
    (N : UnitarilyInvariantSeminorm 𝕜 (WithLp 2 (E₁ × E₂)) (WithLp 2 (F₁ × F₂)))
    {A C : E₁ →ₗ[𝕜] F₁} {B D : E₂ →ₗ[𝕜] F₂} (hA : ∀ k, A.kyFanSum k ≤ C.kyFanSum k)
    (hB : ∀ k, B.kyFanSum k ≤ D.kyFanSum k) :
    N (A.orthogonalBlockSum B) ≤ N (C.orthogonalBlockSum D) :=
  N.map_le_of_mem_twoSidedUnitaryOrbitHull
    (LinearMap.orthogonalBlockSum_mem_twoSidedUnitaryOrbitHull
      (LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr hA)
      (LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr hB))

end TauCeti.UnitarilyInvariantSeminorm
