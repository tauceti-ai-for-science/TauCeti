/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import TauCeti.Analysis.Matrix.PosSemidef.Basic
public import TauCeti.Analysis.Matrix.PosSemidef.Determinant

/-!
# The overlapping-family Gram determinant inequality

For three finite families `u`, `v`, `w`, the product of the Gram determinants
of `u` and `(u,v,w)` is at most the product for `(u,v)` and `(u,w)`.
Taking `u` to be a basis of an intersection and completing it to bases of two
subspaces gives the archimedean determinant estimate for subspace-height
submodularity. No independence or finite-dimensional ambient-space hypothesis
is needed; empty and dependent families are included.

For two families `u` and `w` of the same size, Fischer's inequality bounds the Gram
determinant of `(u,w)` by the product of those of `u` and `w`, and the Cauchy–Schwarz
inequality for determinants bounds the determinant of the products `⟪u i, w k⟫`:
`|det ⟪u i, w k⟫|² ≤ det ⟪u i, u k⟫ · det ⟪w i, w k⟫`, the Cauchy–Schwarz inequality for
`u₁ ∧ ⋯ ∧ uₙ` and `w₁ ∧ ⋯ ∧ wₙ` in the exterior power. For an independent `u` it is the
monotonicity of the determinant applied to the Schur complement of `⟪u i, u k⟫`; for a
dependent `u` both sides vanish.

## Main results

* `Matrix.det_gram_mul_det_gram_sumElim_le`: Koteljanskii's inequality.
* `Matrix.norm_det_gram_sumElim_le`: Fischer's inequality for Gram determinants.
* `Matrix.norm_det_inner_sq_le`: the Cauchy–Schwarz inequality for determinants.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative
  Subspace Theorem*, §6.1, (6.12).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, §7.8.
-/

public section

open scoped InnerProductSpace ComplexOrder

namespace Matrix

variable {𝕜 E ι κ η : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Gram matrix of a concatenated family, in block form. -/
theorem gram_sumElim (u : ι → E) (v : κ → E) :
    gram 𝕜 (Sum.elim u v) = fromBlocks (gram 𝕜 u)
      (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, v j⟫_𝕜)ᴴ (gram 𝕜 v) := by
  ext i j
  cases i <;> cases j <;> simp [gram_apply, conjTranspose_apply, inner_conj_symm]

/-- The Gram matrix of three concatenated families, with the two complementary families
split into separate blocks. -/
theorem gram_sumElim_sumElim (u : ι → E) (v : κ → E) (w : η → E) :
    gram 𝕜 (Sum.elim u (Sum.elim v w)) =
      fromBlocks (gram 𝕜 u)
        (fromCols (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, w j⟫_𝕜))
        (fromCols (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, w j⟫_𝕜))ᴴ
        (fromBlocks (gram 𝕜 v) (of fun i j ↦ ⟪v i, w j⟫_𝕜)
          (of fun i j ↦ ⟪v i, w j⟫_𝕜)ᴴ (gram 𝕜 w)) := by
  have hcols : (of fun i j ↦ ⟪u i, Sum.elim v w j⟫_𝕜) =
      fromCols (of fun i j ↦ ⟪u i, v j⟫_𝕜) (of fun i j ↦ ⟪u i, w j⟫_𝕜) := by
    ext i j
    cases j <;> simp
  simp only [gram_sumElim, hcols]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype η] [DecidableEq η]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η] in
/-- The determinant of a positive-semidefinite matrix is a nonnegative real number, so its norm is
its real part. -/
theorem PosSemidef.norm_det_eq_re_det {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n 𝕜} (h : M.PosSemidef) : ‖M.det‖ = RCLike.re M.det := by
  rw [← h.isHermitian.ofReal_re_det, RCLike.norm_ofReal, RCLike.ofReal_re,
    abs_of_nonneg h.re_det_nonneg]

/-- Gram determinants satisfy Koteljanskii's overlapping-family inequality over
real or complex scalars, including empty and dependent families. -/
theorem det_gram_mul_det_gram_sumElim_le (u : ι → E) (v : κ → E) (w : η → E) :
    (gram 𝕜 u).det * (gram 𝕜 (Sum.elim u (Sum.elim v w))).det ≤
      (gram 𝕜 (Sum.elim u v)).det * (gram 𝕜 (Sum.elim u w)).det := by
  have h := posSemidef_gram 𝕜 (Sum.elim u (Sum.elim v w))
  rw [gram_sumElim_sumElim] at h
  rw [gram_sumElim_sumElim u v w, gram_sumElim u v, gram_sumElim u w]
  exact h.det_mul_det_fromBlocks_le

/-- The real parts of Gram determinants satisfy the overlapping-family
Hadamard--Fischer inequality, also called Koteljanskii's inequality. -/
theorem re_det_gram_mul_re_det_gram_sumElim_le (u : ι → E) (v : κ → E) (w : η → E) :
    RCLike.re (gram 𝕜 u).det * RCLike.re (gram 𝕜 (Sum.elim u (Sum.elim v w))).det ≤
      RCLike.re (gram 𝕜 (Sum.elim u v)).det *
        RCLike.re (gram 𝕜 (Sum.elim u w)).det := by
  have hbound := det_gram_mul_det_gram_sumElim_le (𝕜 := 𝕜) u v w
  rw [← (isHermitian_gram 𝕜 u).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u (Sum.elim v w))).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u v)).ofReal_re_det,
    ← (isHermitian_gram 𝕜 (Sum.elim u w)).ofReal_re_det] at hbound
  exact_mod_cast hbound

omit [DecidableEq η] [Fintype η] in
/-- **Fischer's inequality for Gram determinants**: the Gram determinant of a concatenated family
is at most the product of the Gram determinants of its two parts. -/
theorem norm_det_gram_sumElim_le (u : ι → E) (v : κ → E) :
    ‖(gram 𝕜 (Sum.elim u v)).det‖ ≤ ‖(gram 𝕜 u).det‖ * ‖(gram 𝕜 v).det‖ := by
  have h := posSemidef_gram 𝕜 (Sum.elim u v)
  have hle := (gram_sumElim (𝕜 := 𝕜) u v ▸ h).det_fromBlocks_le
  rw [← gram_sumElim, ← h.isHermitian.ofReal_re_det,
    ← (posSemidef_gram 𝕜 u).isHermitian.ofReal_re_det,
    ← (posSemidef_gram 𝕜 v).isHermitian.ofReal_re_det] at hle
  rw [h.norm_det_eq_re_det, (posSemidef_gram 𝕜 u).norm_det_eq_re_det,
    (posSemidef_gram 𝕜 v).norm_det_eq_re_det]
  exact_mod_cast hle

end Matrix

namespace Matrix

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι]

/-- **The Cauchy–Schwarz inequality for determinants.** For two families `u`, `w` of the same
size, `|det ⟪u i, w k⟫|² ≤ |det ⟪u i, u k⟫| · |det ⟪w i, w k⟫|`. -/
theorem norm_det_inner_sq_le (u w : ι → E) :
    ‖(of fun i k ↦ ⟪u i, w k⟫_𝕜).det‖ ^ 2 ≤ ‖(gram 𝕜 u).det‖ * ‖(gram 𝕜 w).det‖ := by
  set P : Matrix ι ι 𝕜 := of fun i k ↦ ⟪u i, w k⟫_𝕜
  by_cases hA : (gram 𝕜 u).det = 0
  · -- a dependent family `u`: a combination `∑ g i • u i = 0` kills the rows of `P`
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1
      (mt det_gram_ne_zero_iff_linearIndependent.2 (not_not.2 hA))
    have : P.det = 0 := by
      refine exists_vecMul_eq_zero_iff.1 ⟨star g, fun h ↦ hi (by simpa using congrFun h i), ?_⟩
      ext k
      simpa [P, vecMul, dotProduct, sum_inner, inner_smul_left] using congrArg (⟪·, w k⟫_𝕜) hg
    rw [this, norm_zero, zero_pow two_ne_zero]
    positivity
  -- an independent family `u`: the Schur complement of its Gram matrix is positive semidefinite
  set A := gram 𝕜 u
  have hApd : A.PosDef := (posSemidef_gram 𝕜 u).posDef_iff_det_ne_zero.2 hA
  have h := posSemidef_gram 𝕜 (Sum.elim u w)
  rw [gram_sumElim] at h
  have hS := h.schur_complement₁₁ (P := A⁻¹) hApd.inv.isHermitian (by
    change A⁻¹ * A * A⁻¹ = A⁻¹
    rw [nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA), Matrix.one_mul])
  have hle := (hApd.inv.posSemidef.conjTranspose_mul_mul_same P).det_le_det (Matrix.le_iff.2 hS)
  rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv] at hle
  have ha : 0 < RCLike.re A.det := (RCLike.pos_iff.1 hApd.det_pos).1
  rw [← hApd.isHermitian.ofReal_re_det, ← (posSemidef_gram 𝕜 w).isHermitian.ofReal_re_det,
    Ring.inverse_eq_inv', mul_comm (star _), mul_assoc, RCLike.star_def, RCLike.conj_mul] at hle
  norm_cast at hle
  rw [hApd.posSemidef.norm_det_eq_re_det, (posSemidef_gram 𝕜 w).norm_det_eq_re_det]
  exact (inv_mul_le_iff₀ ha).1 hle

end Matrix
