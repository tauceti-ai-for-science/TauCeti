/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Composition
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Transverse composition of Lagrangian correspondences

Let `f : L₁ → M₁ × M₂` be Lagrangian for `pr₁*σ₁ - pr₂*σ₂` and `g : L₂ → M₂ × M₃` Lagrangian for
`pr₁*σ₂ - pr₂*σ₃`, both smooth maps from boundaryless finite-dimensional manifolds. Suppose that
the middle coordinates `x ↦ (f x).2` and `y ↦ (g y).1` are transverse maps into `M₂`. Then the
fibre product

`L₁ ×_{M₂} L₂ = {p : L₁ × L₂ // (f p.1).2 = (g p.2).1}`

is an embedded submanifold of `L₁ × L₂`, with the atlas
`TauCeti.transverseFiberProductChartedSpace`, and its tangent vectors are the pairs of tangent
vectors with equal images in `T M₂` (`TauCeti.mem_range_mfderiv_coe_transverseFiberProduct_iff`).
This is exactly the tangent hypothesis of `IsLagrangianMap.relComp`, so the composite

`h : L₁ ×_{M₂} L₂ → M₁ × M₃`, `h p = ((f p.1).1, (g p.2).2)`

is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.transverseRelComp`).

If `f` and `g` are moreover immersions, then so is `h`: transversality leaves the composition no
excess directions
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.injective_mfderiv_relComp`).
Hence the transverse composite of two Lagrangian immersions is a Lagrangian immersion
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersion.transverseRelComp`), and the
transverse composite of two Lagrangian embeddings is a Lagrangian correspondence `M₁ ⇝ M₃` as
soon as `h` is a topological embedding
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.transverseRelComp`). That last
hypothesis cannot be dropped: two different points of the fibre product can have the same image
under `h`.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [FiniteDimensional ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [K₁.Boundaryless]
  [TopologicalSpace L₁] [ChartedSpace HL₁ L₁] [IsManifold K₁ ∞ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [FiniteDimensional ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [K₂.Boundaryless]
  [TopologicalSpace L₂] [ChartedSpace HL₂ L₂] [IsManifold K₂ ∞ L₂]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃}

variable (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g)
  (htrans : ∀ p : L₁ × L₂, (f p.1).2 = (g p.2).1 →
    (mfderiv K₁ I₂ (fun x ↦ (f x).2) p.1).range ⊔
      (((tangentSpaceCast I₂ (g p.2).1 (f p.1).2).toContinuousLinearMap).comp
        (mfderiv K₂ I₂ (fun y ↦ (g y).1) p.2)).range = ⊤)

omit [FiniteDimensional ℝ E₁] [IsManifold I₁ ∞ M₁] [FiniteDimensional ℝ E₃]
  [IsManifold I₃ ∞ M₃] in
include hf hg htrans in
/-- The transverse fibre product `L₁ ×_{M₂} L₂` is a manifold, and its inclusion into `L₁ × L₂`
is smooth with injective differential. These are the facts about the fibre product used below. -/
private theorem isManifold_and_contMDiff_val_and_injective_mfderiv_val :
    letI := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
      (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
    IsManifold 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ) ∞
        {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ∧
      ContMDiff 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ) (K₁.prod K₂) ∞
        (Subtype.val : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} → L₁ × L₂) ∧
      ∀ (p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1}) ξ,
        mfderiv 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ) (K₁.prod K₂)
          (Subtype.val : _ → L₁ × L₂) p ξ = 0 → ξ = 0 := by
  let := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
    (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct (n := ∞) (f := fun x ↦ (f x).2)
    (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
  refine ⟨isManifold_transverseFiberProduct (n := ∞) (f := fun x ↦ (f x).2)
    (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans,
    hemb.isImmersion.contMDiff, fun p ξ hξ ↦ ?_⟩
  exact (injective_iff_map_eq_zero _).mp (hemb.isImmersion.mfderiv_injective (by simp) p) ξ hξ

include hf hg htrans in
/-- **Composition of Lagrangian correspondences along a transverse fibre product.** If the
middle coordinates of the Lagrangian maps `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` are
transverse, the composite `p ↦ ((f p.1).1, (g p.2).2)` on the fibre-product manifold
`L₁ ×_{M₂} L₂` is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`. -/
theorem IsLagrangianMap.transverseRelComp (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) :
    letI := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
      (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianMap
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
    (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
  obtain ⟨-, hval, -⟩ := isManifold_and_contMDiff_val_and_injective_mfderiv_val hf hg htrans
  have hval' := hval.mdifferentiable (by simp)
  refine hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL
    (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)) hval'.fst hval'.snd
    (fun p ↦ p.2) fun p u w huw ↦ ?_
  -- The pair `(u, w)` is tangent to the fibre product, by its tangent-space characterization.
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_transverseFiberProduct_iff (n := ∞)
    (f := fun x ↦ (f x).2) (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf)
    (contMDiff_fst.comp hg) htrans p (u, w)).mpr (by
      rw [(hf.mdifferentiable (by simp) _).mfderiv_snd_apply,
        (hg.mdifferentiable (by simp) _).mfderiv_fst_apply]
      exact huw)
  rw [ContinuousLinearMap.coe_coe] at hξ
  refine ⟨ξ, ?_, ?_⟩
  · rw [(hval' p).mfderiv_fst_apply, hξ]
  · rw [(hval' p).mfderiv_snd_apply, hξ]

variable [I₁.Boundaryless] [I₃.Boundaryless]

include hf hg htrans in
/-- **Transverse composites of immersed correspondences are immersions.** If the Lagrangian maps
`f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` have injective differentials and transverse middle
coordinates, the composite `p ↦ ((f p.1).1, (g p.2).2)` on the fibre-product manifold
`L₁ ×_{M₂} L₂` has injective differentials, hence is an immersion. -/
theorem IsLagrangianMap.isImmersion_transverseRelComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g)
    (hfi : ∀ x, Function.Injective (mfderiv K₁ (I₁.prod I₂) f x))
    (hgi : ∀ y, Function.Injective (mfderiv K₂ (I₂.prod I₃) g y)) :
    letI := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
      (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
    Manifold.IsImmersion 𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (I₁.prod I₃) ∞
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
    (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
  obtain ⟨_, hval, hvali⟩ :=
    isManifold_and_contMDiff_val_and_injective_mfderiv_val hf hg htrans
  have hval' := hval.mdifferentiable (by simp)
  refine ContMDiff.isImmersion_of_injective_mfderiv
    (((contMDiff_fst.comp hf).comp (contMDiff_fst.comp hval)).prodMk
      ((contMDiff_snd.comp hg).comp (contMDiff_snd.comp hval))) (by simp) fun p ↦ ?_
  refine hfL.injective_mfderiv_relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL
    (hf.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)) hval'.fst hval'.snd
    (fun p ↦ p.2) (hfi _) (hgi _) (fun ξ hu hw ↦ hvali p ξ ?_) (htrans p.1 p.2)
  rw [(hval' p).mfderiv_fst_apply] at hu
  rw [(hval' p).mfderiv_snd_apply] at hw
  exact Prod.ext hu hw

include hf hg htrans in
/-- **Transverse composition of Lagrangian immersions.** The composite of two Lagrangian
immersions `L₁ → M₁ × M₂` and `L₂ → M₂ × M₃` with transverse middle coordinates, on the
fibre-product manifold `L₁ ×_{M₂} L₂`, is a Lagrangian immersion into `M₁ × M₃`. -/
theorem IsLagrangianImmersion.transverseRelComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianImmersion K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianImmersion K₂ g) :
    letI := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
      (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianImmersion
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
    (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
  refine ⟨hfL.isLagrangianMap.isImmersion_transverseRelComp (hσ₁ := hσ₁) (hσ₂ := hσ₂)
    (hσ₃ := hσ₃) hf hg htrans hgL.isLagrangianMap
    (fun x ↦ hfL.isImmersion.mfderiv_injective (by simp) x)
    (fun y ↦ hgL.isImmersion.mfderiv_injective (by simp) y),
    (hfL.isLagrangianMap.transverseRelComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hf hg htrans
      hgL.isLagrangianMap).isIsotropicMap, ?_⟩
  -- `2 dim L₁ = dim M₁ + dim M₂` and `2 dim L₂ = dim M₂ + dim M₃`.
  have h₁ := hfL.two_mul_finrank
  have h₂ := hgL.two_mul_finrank
  simp only [finrank_prod, finrank_fin_fun] at h₁ h₂ ⊢
  omega

include hf hg htrans in
/-- **Transverse composition of Lagrangian correspondences, embedded case.** Let
`f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be Lagrangian correspondences `M₁ ⇝ M₂` and `M₂ ⇝ M₃`
with transverse middle coordinates. If the composite `p ↦ ((f p.1).1, (g p.2).2)` on the
fibre-product manifold `L₁ ×_{M₂} L₂` is a topological embedding, it is a Lagrangian
correspondence `M₁ ⇝ M₃`. -/
theorem IsLagrangianEmbedding.transverseRelComp
    (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianEmbedding K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianEmbedding K₂ g)
    (hemb : Topology.IsEmbedding
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2))) :
    letI := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
      (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding
      𝓘(ℝ, Fin (finrank ℝ EL₁ + finrank ℝ EL₂ - finrank ℝ E₂) → ℝ)
      (fun p : {p : L₁ × L₂ // (f p.1).2 = (g p.2).1} ↦ ((f p.1.1).1, (g p.1.2).2)) := by
  let := transverseFiberProductChartedSpace (n := ∞) (f := fun x ↦ (f x).2)
    (g := fun y ↦ (g y).1) (by simp) (contMDiff_snd.comp hf) (contMDiff_fst.comp hg) htrans
  exact ⟨hfL.isLagrangianMap.isImmersion_transverseRelComp (hσ₁ := hσ₁) (hσ₂ := hσ₂)
    (hσ₃ := hσ₃) hf hg htrans hgL.isLagrangianMap
    (fun x ↦ hfL.isImmersion.mfderiv_injective (by simp) x)
    (fun y ↦ hgL.isImmersion.mfderiv_injective (by simp) y), hemb,
    hfL.isLagrangianMap.transverseRelComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hf hg htrans
      hgL.isLagrangianMap⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
