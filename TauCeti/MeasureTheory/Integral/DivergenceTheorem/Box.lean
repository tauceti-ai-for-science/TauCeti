/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Boundary flux on boxes

`boxBoundarySum` is the front-minus-back face sum in Mathlib's Bochner divergence theorem.
The face parametrizations insert the omitted coordinate, in increasing coordinate order.
The codomain may be any real normed space, so quaternion-valued fluxes need no separate
integration theory.

`boxBoundarySum_eq_integral_of_hasFDerivAt` identifies the boundary flux of a continuous field
with the integral of a function agreeing with its divergence in the open box, and
`boxBoundarySum_eq_zero_of_hasFDerivAt` is the case of zero divergence. The fields need only
pointwise derivatives in the open box; no continuity of the derivatives is required.
Degenerate boxes are included.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The oriented boundary flux of a family of fields on a box: the integral on each front
face minus the integral on the corresponding back face. -/
noncomputable def boxBoundarySum (a b : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) : E :=
  ∑ i, ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
    ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x))

/-- The defining front-minus-back expansion of the boundary flux. -/
theorem boxBoundarySum_def (a b : Fin (n + 1) → ℝ)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum a b F =
      ∑ i, ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F i (i.insertNth (a i) x)) := (rfl)

/-- On the unit cube, the boundary flux is the sum of front-minus-back integrals over
unit cubes of one lower dimension. -/
theorem boxBoundarySum_zero_one (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) :
    boxBoundarySum 0 1 F =
      ∑ i, ((∫ x in Icc (0 : Fin n → ℝ) 1, F i (i.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin n → ℝ) 1, F i (i.insertNth 0 x)) := by
  simp only [boxBoundarySum_def, Function.comp_def, Pi.zero_def, Pi.one_def]

@[simp]
theorem boxBoundarySum_zero (a b : Fin (n + 1) → ℝ) :
    boxBoundarySum a b (fun _ _ ↦ (0 : E)) = 0 := by
  simp [boxBoundarySum_def]

/-- The divergence theorem on a box, with the divergence identified only in the open box: if a
continuous field has pointwise derivatives in the open box whose divergence agrees there with a
function `φ` integrable on the closed box, the boundary flux is the integral of `φ`. Continuity
of the derivatives is not assumed, and degenerate boxes are included. -/
theorem boxBoundarySum_eq_integral_of_hasFDerivAt {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {D : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    {φ : (Fin (n + 1) → ℝ) → E}
    (hc : ∀ i, ContinuousOn (F i) (Icc a b))
    (hd : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∀ i, HasFDerivAt (F i) (D i x) x)
    (hdiv : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∑ i, D i x (Pi.single i 1) = φ x)
    (hφ : IntegrableOn φ (Icc a b)) :
    boxBoundarySum a b F = ∫ x in Icc a b, φ x := by
  have hae : (fun x ↦ ∑ i, D i x (Pi.single i 1)) =ᵐ[volume.restrict (Icc a b)] φ := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo).measurableSet).mono
      fun x hx ↦ hdiv x hx
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab F D ∅ countable_empty hc
    (fun x hx ↦ hd x hx.1) (hφ.congr hae.symm)
  rw [integral_congr_ae hae] at h
  simpa only [boxBoundarySum_def] using h.symm

/-- A continuous field with pointwise derivatives of zero divergence in the open box has
zero boundary flux. Continuity of the derivatives is not assumed. -/
theorem boxBoundarySum_eq_zero_of_hasFDerivAt {a b : Fin (n + 1) → ℝ} (hab : a ≤ b)
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {D : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] E}
    (hc : ∀ i, ContinuousOn (F i) (Icc a b))
    (hd : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∀ i, HasFDerivAt (F i) (D i x) x)
    (hzero : ∀ x ∈ pi univ (fun i ↦ Ioo (a i) (b i)), ∑ i, D i x (Pi.single i 1) = 0) :
    boxBoundarySum a b F = 0 := by
  simpa using boxBoundarySum_eq_integral_of_hasFDerivAt (φ := fun _ ↦ 0) hab hc hd hzero
    integrableOn_zero

end TauCeti
