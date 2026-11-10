/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cauchy.Concentration
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box

/-!
# The cut-off fluxes and the box Cauchy–Fueter formulas

Multiplying the ordered field `G(q - q₀) * eᵢ * f q` by the radial cutoff removes its
singularity at the pole. The resulting field is continuous on a closed box when `f` is,
and differentiable wherever `f` is left Fueter regular away from the pole. Its divergence
is exactly `cauchyFueterCutoffDensity ε q q₀ • f q`. Neither differentiability of `f` at
the pole nor continuity of its derivative is needed. The mirrored field
`f q * eᵢ * G(q - q₀)`, cut off in the same way, has the same divergence when `f` is right
Fueter regular away from the pole.

The integral identities apply the Bochner divergence theorem to these fields. Concentration
of the cutoff density and eventual agreement with the uncut fields on every boundary face
then give `left_cauchyFueter_box` and `right_cauchyFueter_box`, the left and right box
representations with normalization `1 / (2π²)`. All products retain the orders
`G * eᵢ * f` and `f * eᵢ * G`; these are not product-closure theorems for regular functions.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open MeasureTheory Set Filter
open scoped Quaternion Topology

namespace TauCeti

open TauCeti.Quaternion _root_.Quaternion

/-- Fields that agree with `H` at distance at least `ε` from a pole inside the open box have,
for every sufficiently small `ε > 0`, the same box boundary flux as `H`: the boundary faces stay
at a positive distance from the pole. No regularity of the fields is needed. -/
theorem eventually_boxBoundarySum_eq_of_le_norm_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b x₀ : Fin 4 → ℝ}
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i)
    {F : ℝ → Fin 4 → ℍ → E} {H : Fin 4 → ℍ → E}
    (hF : ∀ ε > 0, ∀ i q, ε ≤ ‖q - dq x₀‖ → F ε i q = H i q) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      boxBoundarySum a b (fun i x ↦ F ε i (dq x)) = boxBoundarySum a b (fun i x ↦ H i (dq x)) := by
  let e := (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv
  have he (x : Fin 4 → ℝ) : dq x = e x := congrFun coe_dq x
  let U := pi univ (fun i ↦ Ioo (a i) (b i))
  have hU : IsOpen U := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo
  have hx₀ : x₀ ∈ U := Set.mem_pi.mpr (fun i _ ↦ ⟨ha i, hb i⟩)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (e.isOpenMap U hU) (e x₀)
    (mem_image_of_mem e hx₀)
  have hdist (i : Fin 4) (c : ℝ) (hc : c = a i ∨ c = b i) (x : Fin 3 → ℝ) :
      δ ≤ ‖dq (i.insertNth c x) - dq x₀‖ := by
    by_contra hn
    have hm := hball (by simpa only [Metric.mem_ball, dist_eq_norm, he] using lt_of_not_ge hn)
    obtain ⟨y, hy, heq⟩ := hm
    have hy' : y = i.insertNth c x := e.injective heq
    have hi := (Set.mem_pi.mp hy) i (mem_univ i)
    rw [hy', Fin.insertNth_apply_same] at hi
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hi.1
    · exact lt_irrefl _ hi.2
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
  simp only [boxBoundarySum_def]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  · apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    exact hF ε hε i _ (hεδ.le.trans (hdist i (b i) (Or.inr rfl) x))
  · apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    exact hF ε hε i _ (hεδ.le.trans (hdist i (a i) (Or.inl rfl) x))

/-! ### The left formula -/

/-- The left Cauchy–Fueter flux with its pole removed by a radial cutoff. The basis
coefficient lies between the kernel and the function. -/
noncomputable def cauchyFueterCutoffField (ε : ℝ) (q₀ : ℍ) (f : ℍ → ℍ)
    (i : Fin 4) (q : ℍ) : ℍ :=
  cauchyFueterCutoff (‖q - q₀‖ / ε) •
    (cauchyFueterKernel q q₀ * dq (Pi.single i 1) * f q)

/-- Evaluation of the cut-off ordered flux. -/
theorem cauchyFueterCutoffField_apply (ε : ℝ) (q₀ : ℍ) (f : ℍ → ℍ)
    (i : Fin 4) (q : ℍ) :
    cauchyFueterCutoffField ε q₀ f i q = cauchyFueterCutoff (‖q - q₀‖ / ε) •
      (cauchyFueterKernel q q₀ * dq (Pi.single i 1) * f q) := (rfl)

/-- Inside the excised ball the field vanishes, regardless of the coefficient. -/
theorem cauchyFueterCutoffField_eq_zero {ε : ℝ} (hε : 0 < ε) {q q₀ : ℍ}
    (hq : ‖q - q₀‖ ≤ ε / 2) (f : ℍ → ℍ) (i : Fin 4) :
    cauchyFueterCutoffField ε q₀ f i q = 0 := by
  rw [cauchyFueterCutoffField_apply, cauchyFueterCutoff_of_le, zero_smul]
  rw [div_le_iff₀ hε]
  linarith

@[simp]
theorem cauchyFueterCutoffField_self (ε : ℝ) (q₀ : ℍ) (f : ℍ → ℍ) (i : Fin 4) :
    cauchyFueterCutoffField ε q₀ f i q₀ = 0 := by
  simp [cauchyFueterCutoffField_apply]

/-- Outside the cutoff radius the flux is the original kernel-weighted flux. -/
theorem cauchyFueterCutoffField_of_le {ε : ℝ} (hε : 0 < ε) {q q₀ : ℍ}
    (hq : ε ≤ ‖q - q₀‖) (f : ℍ → ℍ) (i : Fin 4) :
    cauchyFueterCutoffField ε q₀ f i q =
      cauchyFueterKernel q q₀ * dq (Pi.single i 1) * f q := by
  rw [cauchyFueterCutoffField_apply, cauchyFueterCutoff_of_one_le, one_smul]
  exact (le_div_iff₀ hε).2 (by simpa using hq)

/-- Near its pole the cut-off field is identically zero, even for an arbitrary `f`. -/
theorem cauchyFueterCutoffField_eventuallyEq_zero {ε : ℝ} (hε : 0 < ε)
    (q₀ : ℍ) (f : ℍ → ℍ) (i : Fin 4) :
    cauchyFueterCutoffField ε q₀ f i =ᶠ[𝓝 q₀] 0 := by
  filter_upwards [Metric.ball_mem_nhds q₀ (half_pos hε)] with q hq
  exact cauchyFueterCutoffField_eq_zero hε
    (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hq).le) f i

/-- The cutoff removes the kernel singularity without requiring continuity of `f`
at the pole. Away from the pole only continuity within the given set is used. -/
theorem continuousOn_cauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {q₀ : ℍ} {f : ℍ → ℍ} {s : Set ℍ} (hf : ContinuousOn f (s \ {q₀})) (i : Fin 4) :
    ContinuousOn (cauchyFueterCutoffField ε q₀ f i) s := by
  intro q hq
  by_cases hp : q = q₀
  · subst q
    exact ((continuousAt_const.congr
      (cauchyFueterCutoffField_eventuallyEq_zero hε q₀ f i).symm)).continuousWithinAt
  · have hfs : ContinuousWithinAt f s q :=
      continuousWithinAt_sdiff_singleton.mp (hf q ⟨hq, hp⟩)
    have hψ := (hasFDerivAt_cauchyFueterCutoff_norm_sub_div q q₀ ε).continuousAt
    exact hψ.continuousWithinAt.smul
      ((((contDiffAt_cauchyFueterKernel (n := 1) hp).continuousAt).continuousWithinAt.mul
        continuousWithinAt_const).mul hfs)

/-- Pointwise differentiability of the cut-off flux. No differentiability of the
coefficient is needed at the pole. -/
theorem differentiableAt_cauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {q q₀ : ℍ} {f : ℍ → ℍ} (hf : q ≠ q₀ → DifferentiableAt ℝ f q) (i : Fin 4) :
    DifferentiableAt ℝ (cauchyFueterCutoffField ε q₀ f i) q := by
  by_cases hp : q = q₀
  · subst q
    exact ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℍ) q₀).congr_of_eventuallyEq
      (cauchyFueterCutoffField_eventuallyEq_zero hε q₀ f i)).differentiableAt
  · exact (hasFDerivAt_cauchyFueterCutoff_norm_sub_div q q₀ ε).differentiableAt.smul
      (((contDiffAt_cauchyFueterKernel (n := 1) hp).differentiableAt one_ne_zero).mul_const
        (dq (Pi.single i 1)) |>.mul (hf hp))

/-- The divergence of the cut-off kernel-weighted field is the radial density times
the coefficient. Only pointwise left Fueter regularity away from the pole is assumed. -/
theorem sum_fderiv_cauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {q q₀ : ℍ} {f : ℍ → ℍ} (hf : q ≠ q₀ → LeftFueterAt f q) :
    ∑ i : Fin 4, fderiv ℝ (cauchyFueterCutoffField ε q₀ f i) q (dq (Pi.single i 1)) =
      cauchyFueterCutoffDensity ε q q₀ • f q := by
  by_cases hp : q = q₀
  · subst q
    have hz (i : Fin 4) := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℍ) q₀).congr_of_eventuallyEq
      (cauchyFueterCutoffField_eventuallyEq_zero hε q₀ f i)).fderiv
    simp [hz]
  · have hG := (contDiffAt_cauchyFueterKernel (n := 1) hp).differentiableAt one_ne_zero
    have hd (i : Fin 4) :
        fderiv ℝ (cauchyFueterCutoffField ε q₀ f i) q =
          cauchyFueterCutoff (‖q - q₀‖ / ε) •
            fderiv ℝ (fun p ↦ cauchyFueterKernel p q₀ * dq (Pi.single i 1) * f p) q +
          (fderiv ℝ (fun p ↦ cauchyFueterCutoff (‖p - q₀‖ / ε)) q).smulRight
            (cauchyFueterKernel q q₀ * dq (Pi.single i 1) * f q) :=
      fderiv_fun_smul (hasFDerivAt_cauchyFueterCutoff_norm_sub_div q q₀ ε).differentiableAt
        ((hG.mul_const _).mul (hf hp).differentiableAt)
    have hzero := (rightFueterAt_cauchyFueterKernel hp).sum_fderiv_mul_leftFueterAt (hf hp)
    have he (i : Fin 4) : dq (Pi.single i 1) =
        QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by simp
    simp only [← he] at hzero
    simp only [hd, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Finset.sum_add_distrib, ← Finset.smul_sum, hzero,
      smul_zero, zero_add]
    rw [← Quaternion.coe_mul_eq_smul,
      ← Quaternion.cauchyFueterKernel_mul_sum_fderiv_cauchyFueterCutoff q q₀ ε]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

/-- The divergence theorem for the cut-off Cauchy–Fueter field on a coordinate box.
The right side is the radial-density integral whose limit gives `2π² • f q₀` when
`q₀` lies strictly inside the box; see `tendsto_boxBoundarySum_cauchyFueterCutoffField`.
Regularity is required only in the punctured open box, not at the pole. -/
theorem boxBoundarySum_cauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {q₀ : ℍ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {q₀})) :
    boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε q₀ f i (dq x)) =
      ∫ x in Icc a b, cauchyFueterCutoffDensity ε (dq x) q₀ • f (dq x) := by
  have hf := leftFueterOn_iff.mp hf
  have hcd := hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)
  exact boxBoundarySum_eq_integral_of_hasFDerivAt hab
    (fun i ↦ (continuousOn_cauchyFueterCutoffField hε (hc.mono sdiff_subset) i).comp
      dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx))
    (fun x hx i ↦
      (differentiableAt_cauchyFueterCutoffField hε
        (fun hp ↦ (hf _ ⟨mem_image_of_mem _ hx, hp⟩).differentiableAt) i).hasFDerivAt.comp x
        dq.hasFDerivAt)
    (fun x hx ↦
      sum_fderiv_cauchyFueterCutoffField hε (fun hp ↦ hf _ ⟨mem_image_of_mem _ hx, hp⟩))
    ((integrable_cauchyFueterCutoffDensity hε q₀).integrableOn.smul_continuousOn hcd
      isCompact_Icc)

/-- As the excised ball shrinks to an interior pole, the boundary flux of the cut-off
field tends to `2π²` times the value of the coefficient at that pole. -/
theorem tendsto_boxBoundarySum_cauchyFueterCutoffField
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    Tendsto (fun ε : ℝ ↦ boxBoundarySum a b
      (fun i x ↦ cauchyFueterCutoffField ε (dq x₀) f i (dq x)))
      (𝓝[>] 0) (𝓝 ((2 * Real.pi ^ 2) • f (dq x₀))) := by
  have h := tendsto_integral_Icc_cauchyFueterCutoff_density
    (hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)) ha hb
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (boxBoundarySum_cauchyFueterCutoffField hε
    (fun i ↦ (ha i).le.trans (hb i).le) hc hf).symm

/-- For an interior pole, sufficiently small cutoffs leave every boundary coefficient
unchanged. No regularity or continuity of the coefficient is needed for this fact. -/
theorem eventually_boxBoundarySum_cauchyFueterCutoffField
    {a b x₀ : Fin 4 → ℝ} (f : ℍ → ℍ)
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      boxBoundarySum a b (fun i x ↦ cauchyFueterCutoffField ε (dq x₀) f i (dq x)) =
        boxBoundarySum a b
          (fun i x ↦ cauchyFueterKernel (dq x) (dq x₀) * dq (Pi.single i 1) * f (dq x)) :=
  eventually_boxBoundarySum_eq_of_le_norm_sub ha hb
    (F := fun ε ↦ cauchyFueterCutoffField ε (dq x₀) f)
    (H := fun i q ↦ cauchyFueterKernel q (dq x₀) * dq (Pi.single i 1) * f q)
    fun _ hε i _ hq ↦ cauchyFueterCutoffField_of_le hε hq f i

/-- The left Cauchy–Fueter representation on a box, normalized by `1 / (2π²)`.
Continuity on the closed box and pointwise left regularity in its punctured interior
suffice; in particular no continuity of the derivative is assumed. -/
theorem left_cauchyFueter_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ cauchyFueterKernel (dq x) (dq x₀) * dq (Pi.single i 1) * f (dq x)) := by
  have h := tendsto_boxBoundarySum_cauchyFueterCutoffField hc hf ha hb
  have heq := tendsto_nhds_unique
    (h.congr' (eventually_boxBoundarySum_cauchyFueterCutoffField f ha hb)) tendsto_const_nhds
  have hm : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← heq, smul_smul, one_div, inv_mul_cancel₀ hm, one_smul]

/-! ### The right formula -/

/-- The right Cauchy–Fueter flux with its pole removed by a radial cutoff. The basis
coefficient lies between the function and the kernel. -/
noncomputable def rightCauchyFueterCutoffField (ε : ℝ) (q₀ : ℍ) (f : ℍ → ℍ)
    (i : Fin 4) (q : ℍ) : ℍ :=
  cauchyFueterCutoff (‖q - q₀‖ / ε) •
    (f q * dq (Pi.single i 1) * cauchyFueterKernel q q₀)

/-- Evaluation of the cut-off right flux. -/
theorem rightCauchyFueterCutoffField_apply (ε : ℝ) (q₀ : ℍ) (f : ℍ → ℍ)
    (i : Fin 4) (q : ℍ) :
    rightCauchyFueterCutoffField ε q₀ f i q = cauchyFueterCutoff (‖q - q₀‖ / ε) •
      (f q * dq (Pi.single i 1) * cauchyFueterKernel q q₀) := (rfl)

/-- Inside the excised ball the right field vanishes, regardless of the coefficient. -/
theorem rightCauchyFueterCutoffField_eq_zero {ε : ℝ} (hε : 0 < ε) {q q₀ : ℍ}
    (hq : ‖q - q₀‖ ≤ ε / 2) (f : ℍ → ℍ) (i : Fin 4) :
    rightCauchyFueterCutoffField ε q₀ f i q = 0 := by
  rw [rightCauchyFueterCutoffField_apply, cauchyFueterCutoff_of_le, zero_smul]
  rw [div_le_iff₀ hε]
  linarith

@[simp]
theorem rightCauchyFueterCutoffField_self (ε : ℝ) (q₀ : ℍ) (f : ℍ → ℍ) (i : Fin 4) :
    rightCauchyFueterCutoffField ε q₀ f i q₀ = 0 := by
  simp [rightCauchyFueterCutoffField_apply]

/-- Outside the cutoff radius the right field is the original kernel-weighted flux. -/
theorem rightCauchyFueterCutoffField_of_le {ε : ℝ} (hε : 0 < ε) {q q₀ : ℍ}
    (hq : ε ≤ ‖q - q₀‖) (f : ℍ → ℍ) (i : Fin 4) :
    rightCauchyFueterCutoffField ε q₀ f i q =
      f q * dq (Pi.single i 1) * cauchyFueterKernel q q₀ := by
  rw [rightCauchyFueterCutoffField_apply, cauchyFueterCutoff_of_one_le, one_smul]
  exact (le_div_iff₀ hε).2 (by simpa using hq)

/-- Near its pole the cut-off right field is identically zero, even for an arbitrary `f`. -/
theorem rightCauchyFueterCutoffField_eventuallyEq_zero {ε : ℝ} (hε : 0 < ε)
    (q₀ : ℍ) (f : ℍ → ℍ) (i : Fin 4) :
    rightCauchyFueterCutoffField ε q₀ f i =ᶠ[𝓝 q₀] 0 := by
  filter_upwards [Metric.ball_mem_nhds q₀ (half_pos hε)] with q hq
  exact rightCauchyFueterCutoffField_eq_zero hε
    (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hq).le) f i

/-- The cutoff removes the kernel singularity of the right field without requiring
continuity of `f` at the pole. Away from the pole only continuity within the given set
is used. -/
theorem continuousOn_rightCauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {q₀ : ℍ} {f : ℍ → ℍ} {s : Set ℍ} (hf : ContinuousOn f (s \ {q₀})) (i : Fin 4) :
    ContinuousOn (rightCauchyFueterCutoffField ε q₀ f i) s := by
  intro q hq
  by_cases hp : q = q₀
  · subst q
    exact ((continuousAt_const.congr
      (rightCauchyFueterCutoffField_eventuallyEq_zero hε q₀ f i).symm)).continuousWithinAt
  · have hfs : ContinuousWithinAt f s q :=
      continuousWithinAt_sdiff_singleton.mp (hf q ⟨hq, hp⟩)
    have hψ := (hasFDerivAt_cauchyFueterCutoff_norm_sub_div q q₀ ε).continuousAt
    exact hψ.continuousWithinAt.smul ((hfs.mul continuousWithinAt_const).mul
      ((contDiffAt_cauchyFueterKernel (n := 1) hp).continuousAt).continuousWithinAt)

/-- Pointwise differentiability of the cut-off right flux. No differentiability of the
coefficient is needed at the pole. -/
theorem differentiableAt_rightCauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {q q₀ : ℍ} {f : ℍ → ℍ} (hf : q ≠ q₀ → DifferentiableAt ℝ f q) (i : Fin 4) :
    DifferentiableAt ℝ (rightCauchyFueterCutoffField ε q₀ f i) q := by
  by_cases hp : q = q₀
  · subst q
    exact ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℍ) q₀).congr_of_eventuallyEq
      (rightCauchyFueterCutoffField_eventuallyEq_zero hε q₀ f i)).differentiableAt
  · exact (hasFDerivAt_cauchyFueterCutoff_norm_sub_div q q₀ ε).differentiableAt.smul
      (((hf hp).mul_const (dq (Pi.single i 1))).mul
        ((contDiffAt_cauchyFueterKernel (n := 1) hp).differentiableAt one_ne_zero))

/-- The divergence of the cut-off right field is the same radial density times the
coefficient. Only pointwise right Fueter regularity away from the pole is assumed. -/
theorem sum_fderiv_rightCauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {q q₀ : ℍ} {f : ℍ → ℍ} (hf : q ≠ q₀ → RightFueterAt f q) :
    ∑ i : Fin 4, fderiv ℝ (rightCauchyFueterCutoffField ε q₀ f i) q (dq (Pi.single i 1)) =
      cauchyFueterCutoffDensity ε q q₀ • f q := by
  by_cases hp : q = q₀
  · subst q
    have hz (i : Fin 4) := ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℍ) q₀).congr_of_eventuallyEq
      (rightCauchyFueterCutoffField_eventuallyEq_zero hε q₀ f i)).fderiv
    simp [hz]
  · have hG := (contDiffAt_cauchyFueterKernel (n := 1) hp).differentiableAt one_ne_zero
    have hd (i : Fin 4) :
        fderiv ℝ (rightCauchyFueterCutoffField ε q₀ f i) q =
          cauchyFueterCutoff (‖q - q₀‖ / ε) •
            fderiv ℝ (fun p ↦ f p * dq (Pi.single i 1) * cauchyFueterKernel p q₀) q +
          (fderiv ℝ (fun p ↦ cauchyFueterCutoff (‖p - q₀‖ / ε)) q).smulRight
            (f q * dq (Pi.single i 1) * cauchyFueterKernel q q₀) :=
      fderiv_fun_smul (hasFDerivAt_cauchyFueterCutoff_norm_sub_div q q₀ ε).differentiableAt
        (((hf hp).differentiableAt.mul_const _).mul hG)
    have hzero := (hf hp).sum_fderiv_mul_leftFueterAt (leftFueterAt_cauchyFueterKernel hp)
    have he (i : Fin 4) : dq (Pi.single i 1) =
        QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by simp
    simp only [← he] at hzero
    simp only [hd, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Finset.sum_add_distrib, ← Finset.smul_sum, hzero,
      smul_zero, zero_add]
    rw [← _root_.Quaternion.mul_coe_eq_smul,
      ← _root_.Quaternion.sum_fderiv_cauchyFueterCutoff_mul_cauchyFueterKernel q q₀ ε]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]

/-- The divergence theorem for the cut-off right Cauchy–Fueter field on a coordinate box.
Its right side is the same radial-density integral as for the left field. Regularity is
required only in the punctured open box, not at the pole. -/
theorem boxBoundarySum_rightCauchyFueterCutoffField {ε : ℝ} (hε : 0 < ε)
    {a b : Fin 4 → ℝ} (hab : a ≤ b) {q₀ : ℍ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {q₀})) :
    boxBoundarySum a b (fun i x ↦ rightCauchyFueterCutoffField ε q₀ f i (dq x)) =
      ∫ x in Icc a b, cauchyFueterCutoffDensity ε (dq x) q₀ • f (dq x) := by
  have hf := rightFueterOn_iff.mp hf
  have hcd := hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)
  exact boxBoundarySum_eq_integral_of_hasFDerivAt hab
    (fun i ↦ (continuousOn_rightCauchyFueterCutoffField hε (hc.mono sdiff_subset) i).comp
      dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx))
    (fun x hx i ↦
      (differentiableAt_rightCauchyFueterCutoffField hε
        (fun hp ↦ (hf _ ⟨mem_image_of_mem _ hx, hp⟩).differentiableAt) i).hasFDerivAt.comp x
        dq.hasFDerivAt)
    (fun x hx ↦
      sum_fderiv_rightCauchyFueterCutoffField hε (fun hp ↦ hf _ ⟨mem_image_of_mem _ hx, hp⟩))
    ((integrable_cauchyFueterCutoffDensity hε q₀).integrableOn.smul_continuousOn hcd
      isCompact_Icc)

/-- As the excised ball shrinks to an interior pole, the boundary flux of the cut-off
right field tends to `2π²` times the value of the coefficient at that pole. -/
theorem tendsto_boxBoundarySum_rightCauchyFueterCutoffField
    {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    Tendsto (fun ε : ℝ ↦ boxBoundarySum a b
      (fun i x ↦ rightCauchyFueterCutoffField ε (dq x₀) f i (dq x)))
      (𝓝[>] 0) (𝓝 ((2 * Real.pi ^ 2) • f (dq x₀))) := by
  have h := tendsto_integral_Icc_cauchyFueterCutoff_density
    (hc.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)) ha hb
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (boxBoundarySum_rightCauchyFueterCutoffField hε
    (fun i ↦ (ha i).le.trans (hb i).le) hc hf).symm

/-- For an interior pole, sufficiently small cutoffs leave every boundary coefficient of
the right field unchanged. No regularity or continuity of the coefficient is needed. -/
theorem eventually_boxBoundarySum_rightCauchyFueterCutoffField
    {a b x₀ : Fin 4 → ℝ} (f : ℍ → ℍ)
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      boxBoundarySum a b (fun i x ↦ rightCauchyFueterCutoffField ε (dq x₀) f i (dq x)) =
        boxBoundarySum a b
          (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) (dq x₀)) :=
  eventually_boxBoundarySum_eq_of_le_norm_sub ha hb
    (F := fun ε ↦ rightCauchyFueterCutoffField ε (dq x₀) f)
    (H := fun i q ↦ f q * dq (Pi.single i 1) * cauchyFueterKernel q (dq x₀))
    fun _ hε i _ hq ↦ rightCauchyFueterCutoffField_of_le hε hq f i

/-- The right Cauchy–Fueter representation on a box, normalized by `1 / (2π²)`. The
coefficients are ordered `f * eᵢ * G`, with `f` to the left of the basis coefficient and the
kernel to its right. Continuity on the closed box and pointwise right regularity in its
punctured interior suffice; no continuity of the derivative is assumed. -/
theorem right_cauchyFueter_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f ((dq '' pi univ (fun i ↦ Ioo (a i) (b i))) \ {dq x₀}))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) (dq x₀)) := by
  have h := tendsto_boxBoundarySum_rightCauchyFueterCutoffField hc hf ha hb
  have heq := tendsto_nhds_unique
    (h.congr' (eventually_boxBoundarySum_rightCauchyFueterCutoffField f ha hb))
    tendsto_const_nhds
  have hm : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← heq, smul_smul, one_div, inv_mul_cancel₀ hm, one_smul]

end TauCeti
