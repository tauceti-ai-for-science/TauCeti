/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthogonalComplement

/-!
# Orthogonal complements of distributions

On a real manifold modelled on a finite-dimensional space `E`, with a `C^n` Riemannian metric, the
orthogonal complements `(D x)ᗮ` of a `C^n` distribution `D` of rank `k` form a `C^n` distribution
of rank `dim E - k` (`TauCeti.IsContMDiffDistribution.orthogonal`). This is the case of the tangent
bundle of `TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal`. It produces smooth complements of
distributions, such as horizontal complements of the kernel distribution of a submersion.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (orthogonal complements of subbundles) and Chapter 19 (distributions).
-/

public section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} [IsManifold I (n + 1) M] {k : ℕ}
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- **Orthogonal complements of distributions.** For a `C^n` Riemannian metric on a manifold of
dimension `dim E`, the orthogonal complements of a `C^n` distribution of rank `k` form a `C^n`
distribution of rank `dim E - k`. -/
theorem IsContMDiffDistribution.orthogonal {D : Π x : M, Submodule ℝ (TangentSpace I x)}
    (hD : IsContMDiffDistribution I n k D) :
    IsContMDiffDistribution I n (finrank ℝ E - k) fun x ↦ (D x)ᗮ := by
  have := TangentBundle.contMDiffVectorBundle (n := n) (I := I) (M := M)
  exact (HasLocalContMDiffSubbundleFrames.orthogonal (IB := I) (F := E)
    (V := fun x : M ↦ TangentSpace I x) hD.hasLocalContMDiffSubbundleFrames).isContMDiffDistribution

end TauCeti
