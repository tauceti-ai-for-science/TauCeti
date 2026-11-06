/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution

/-!
# The Fourier transform of convolutions and of products

Mathlib's convolution theorem `Real.fourier_mul_convolution_eq` says that the Fourier transform of
the convolution of two integrable functions is the product of their Fourier transforms. Since the
inverse Fourier transform is the Fourier transform evaluated at `-x`
(`Real.fourierInv_eq_fourier_neg`), the same holds for the inverse Fourier transform:

`𝓕⁻ (f₁ ⋆ f₂) = 𝓕⁻ f₁ * 𝓕⁻ f₂`

(`Real.fourierInv_mul_convolution_eq`). Read backwards, this writes the pointwise product of two
functions with integrable Fourier transforms as the inverse Fourier transform of an integrable
function, which is how products are handled in Fourier-side Sobolev estimates.

Dually, the Fourier transform of a product is the convolution of the Fourier transforms. In the
form `𝓕 (𝓕⁻ g • h) = g ⋆ 𝓕 h` (`Real.fourier_fourierInv_smul_eq_convolution`) only `g` and `h`
need to be integrable: the proof is Fubini's theorem, with no inversion formula. For a Schwartz
function `ψ`, taking `g = 𝓕 ψ` gives `𝓕 (ψ • h) = 𝓕 ψ ⋆ 𝓕 h`
(`SchwartzMap.fourier_smul_eq_convolution`); this is how a smooth cutoff acts on Fourier
transforms in microlocal analysis.
-/

public section

open MeasureTheory ContinuousLinearMap
open scoped Convolution FourierTransform RealInnerProductSpace SchwartzMap

namespace Real

variable {E R : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedRing R] [NormedSpace ℂ R] [IsScalarTower ℂ R R]
  [SMulCommClass ℂ R R] [CompleteSpace R]

/-- **The convolution theorem for the inverse Fourier transform.** The inverse Fourier transform
of the convolution of two integrable functions is the product of their inverse Fourier
transforms. -/
theorem fourierInv_mul_convolution_eq {f₁ f₂ : E → R} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂)
    (x : E) : 𝓕⁻ (f₁ ⋆[mul ℂ R] f₂) x = 𝓕⁻ f₁ x * 𝓕⁻ f₂ x := by
  simp only [fourierInv_eq_fourier_neg, fourier_mul_convolution_eq hf₁ hf₂]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **The Fourier transform of a product is the convolution of the Fourier transforms.** For
integrable `g` and `h`, the Fourier transform of `𝓕⁻ g • h` at `η` is
`∫ ζ, g ζ • 𝓕 h (η - ζ)`. -/
theorem fourier_fourierInv_smul_eq_convolution {g : E → ℂ} {h : E → F} (hg : Integrable g)
    (hh : Integrable h) (η : E) :
    𝓕 (fun x => 𝓕⁻ g x • h x) η = (g ⋆[lsmul ℂ ℂ] 𝓕 h) η := by
  -- Both sides are the double integral of `𝐞 (-⟪x, η - ζ⟫) g ζ h x`, in the two orders.
  have hchar (x ζ : E) : (𝐞 (-⟪x, η⟫) : ℂ) * 𝐞 ⟪ζ, x⟫ = 𝐞 (-⟪x, η - ζ⟫) := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_sub_right, real_inner_comm ζ x]
    ring_nf
  have hint : Integrable (Function.uncurry fun x ζ => 𝐞 (-⟪x, η - ζ⟫) • g ζ • h x)
      (volume.prod volume) := by
    refine (hg.smul_prod hh).swap.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have hg' := hg.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure E)))
      have hh' := hh.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure E)))
      exact (continuous_fourierChar.comp (f := fun z : E × E => -⟪z.1, η - z.2⟫)
        (by fun_prop)).aestronglyMeasurable.smul (hg'.smul hh')
    · simp [Function.uncurry, norm_smul]
  calc 𝓕 (fun x => 𝓕⁻ g x • h x) η
      = ∫ x, ∫ ζ, 𝐞 (-⟪x, η - ζ⟫) • g ζ • h x := by
        rw [fourier_eq]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [fourierInv_eq, Circle.smul_def, smul_eq_mul, ← hchar, smul_smul, mul_assoc,
          integral_smul_const, integral_const_mul]
    _ = ∫ ζ, ∫ x, 𝐞 (-⟪x, η - ζ⟫) • g ζ • h x := integral_integral_swap hint
    _ = (g ⋆[lsmul ℂ ℂ] 𝓕 h) η := by
        rw [convolution_def]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        simp only [lsmul_apply, fourier_eq, Circle.smul_def, ← integral_smul, smul_smul,
          mul_comm]

/-- **The Fourier transform of a product with a Schwartz function.** For a Schwartz function `ψ`
and an integrable `h`, the Fourier transform of `ψ • h` is the convolution `𝓕 ψ ⋆ 𝓕 h`. -/
theorem _root_.SchwartzMap.fourier_smul_eq_convolution (ψ : 𝓢(E, ℂ)) {h : E → F}
    (hh : Integrable h) (η : E) :
    𝓕 (fun x => ψ x • h x) η = (⇑(𝓕 ψ : 𝓢(E, ℂ)) ⋆[lsmul ℂ ℂ] 𝓕 h) η := by
  have hinv : 𝓕⁻ (𝓕 (ψ : E → ℂ)) = ψ :=
    ψ.continuous.fourierInv_fourier_eq ψ.integrable (by
      rw [← SchwartzMap.fourier_coe]
      exact (𝓕 ψ).integrable)
  rw [← fourier_fourierInv_smul_eq_convolution (𝓕 ψ).integrable hh, SchwartzMap.fourier_coe, hinv]

end Real
