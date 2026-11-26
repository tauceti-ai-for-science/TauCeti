/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Infinite places of a Galois extension of a field with one complex place

Let `E / K` be a Galois extension and `φ : E → ℂ` an embedding whose restriction to `K` induces a
complex place. Two automorphisms `g, g'` of `E / K` for which `φ ∘ g` and `φ ∘ g'` induce the same
infinite place are equal: otherwise `φ ∘ g'` would be the conjugate of `φ ∘ g`, and restricting to
`K` would make `φ|_K` real. If moreover `K` has a single infinite place, every infinite place of
`E` lies above it, so it is `σ • mk φ = mk (φ ∘ σ⁻¹)` for some `σ`. Then `g ↦ mk (φ ∘ g)` is a
bijection from `Gal(E/K)` onto the infinite places of `E`. This applies to every Galois extension
of an imaginary quadratic field.

## Main results

* `NumberField.InfinitePlace.eq_of_mk_eq_of_comp_eq`: two embeddings agreeing on `K`, where they
  induce a complex place, and inducing the same place of `E`, are equal.
* `NumberField.InfinitePlace.mk_comp_algEquiv_injective`: `g ↦ mk (φ ∘ g)` is injective when
  `φ|_K` induces a complex place.
* `NumberField.InfinitePlace.mk_comp_algEquiv_surjective`: it is surjective when `E / K` is Galois
  and `K` has one infinite place.
* `NumberField.InfinitePlace.galEquiv`: the resulting bijection `Gal(E/K) ≃ InfinitePlace E`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer Grundlehren 322 (1999), Chapter II, §8
  (extensions of archimedean valuations and the action of the Galois group on them).
-/

public section

namespace NumberField.InfinitePlace

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Two embeddings `φ, ψ : E → ℂ` that agree on `K`, where they induce a complex place, and that
induce the same infinite place of `E`, are equal. -/
theorem eq_of_mk_eq_of_comp_eq {φ ψ : E →+* ℂ}
    (hK : φ.comp (algebraMap K E) = ψ.comp (algebraMap K E))
    (hφ : (mk (φ.comp (algebraMap K E))).IsComplex) (h : mk φ = mk ψ) : φ = ψ := by
  rcases mk_eq_iff.1 h with h | h
  · exact h
  · refine absurd ?_ (not_isReal_iff_isComplex.2 hφ)
    rw [isReal_mk_iff, ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x ↦ ?_
    have hx : φ (algebraMap K E x) = ψ (algebraMap K E x) := RingHom.congr_fun hK x
    simpa [hx] using RingHom.congr_fun h (algebraMap K E x)

/-- If the restriction of `φ : E → ℂ` to `K` induces a complex place, then automorphisms `g` of
`E / K` are determined by the infinite place induced by `φ ∘ g`. -/
theorem mk_comp_algEquiv_injective {φ : E →+* ℂ}
    (hφ : (mk (φ.comp (algebraMap K E))).IsComplex) :
    Function.Injective fun g : Gal(E/K) ↦ mk (φ.comp (g : E →+* E)) := by
  intro g g' h
  have hK (g : Gal(E/K)) : (φ.comp (g : E →+* E)).comp (algebraMap K E) =
      φ.comp (algebraMap K E) := RingHom.ext fun x ↦ by simp
  refine AlgEquiv.ext fun x ↦ φ.injective (RingHom.congr_fun
    (eq_of_mk_eq_of_comp_eq ((hK g).trans (hK g').symm) ?_ h) x)
  rwa [hK]

/-- If `E / K` is Galois and `K` has a single infinite place, then every infinite place of `E` is
induced by `φ ∘ g` for some automorphism `g` of `E / K`. -/
theorem mk_comp_algEquiv_surjective [IsGalois K E] [Subsingleton (InfinitePlace K)]
    (φ : E →+* ℂ) :
    Function.Surjective fun g : Gal(E/K) ↦ mk (φ.comp (g : E →+* E)) := by
  intro w
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_comap_eq (k := K) (w := mk φ) (w' := w)
    (Subsingleton.elim _ _)
  exact ⟨σ.symm, by rw [← hσ, smul_mk]⟩

/-- For a Galois extension `E / K` where `K` has a single infinite place, which is complex, and an
embedding `φ : E → ℂ`, the bijection `g ↦ mk (φ ∘ g)` from `Gal(E/K)` onto the infinite places of
`E`. -/
@[expose] noncomputable def galEquiv [IsGalois K E] [Subsingleton (InfinitePlace K)]
    (φ : E →+* ℂ) (hφ : (mk (φ.comp (algebraMap K E))).IsComplex) : Gal(E/K) ≃ InfinitePlace E :=
  .ofBijective _ ⟨mk_comp_algEquiv_injective hφ, mk_comp_algEquiv_surjective φ⟩

@[simp]
theorem galEquiv_apply [IsGalois K E] [Subsingleton (InfinitePlace K)] (φ : E →+* ℂ)
    (hφ : (mk (φ.comp (algebraMap K E))).IsComplex) (g : Gal(E/K)) :
    galEquiv φ hφ g = mk (φ.comp (g : E →+* E)) :=
  rfl

end NumberField.InfinitePlace
