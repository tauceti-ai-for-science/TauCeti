/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.Data.ENNReal.Inv
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's embedding for local Sobolev classes on planar domains

Let `Ω ⊆ ℂ` be open, let `F` be a finite-dimensional real normed space and let `2 < p ≤ ∞`.
This file proves that a map `u ∈ MemWkpLoc p Ω (k + 1)` has a `C^{k,α}` representative on `Ω`,
with `α = 1 - 2 / p`: the precise representative `preciseRepresentative volume u`, the limit of
the averages of `u` over shrinking discs, agrees with `u` almost everywhere on `Ω`, is `C^k` on
`Ω`, and its `k`-th derivative is `α`-Hölder continuous on every compact subset of `Ω`. For
`p = ∞` the exponent is `1`, so that derivative is Lipschitz on compact subsets.

At order one this is the interior Morrey embedding for `W^{1,p}` of
`TauCeti.Analysis.Sobolev.W1p.InteriorMorrey`. That result concerns real functions in the scalar
space `W1p`. A first-order local Sobolev function is represented by an element of `W1p` on every
open set with compact closure in `Ω` (`TauCeti.MemWkpLoc.exists_w1p`); vector-valued maps are
handled coordinatewise in a basis of `F`. Higher orders follow by induction: the weak derivative
of `u` has a `C^k` representative, so the continuous representative of `u` is `C^{k+1}`, with
that representative as its classical derivative (`TauCeti.HasWeakFDerivOn.contDiffOn_succ`).

In dimension two, `p > 2` is exactly the range in which first-order Sobolev maps are continuous,
which is what nonlinear Cauchy–Riemann equations require of their solutions.

## Main declarations

* `TauCeti.MemWkpLoc.exists_w1p`: a real first-order local Sobolev function is represented by an
  element of `W1p` on every open set with compact closure in `Ω`.
* `TauCeti.MemLpLoc.ae_eq_preciseRepresentative`: a locally `Lᵖ` map, `1 ≤ p`, agrees almost
  everywhere on `Ω` with its precise representative.
* `TauCeti.MemWkpLoc.exists_holderOnWith_preciseRepresentative`: at order one the precise
  representative is `α`-Hölder continuous on every compact subset of `Ω`.
* `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`: at order one it is continuous on `Ω`.
* `TauCeti.MemWkpLoc.contDiffOn_preciseRepresentative`: at order `k + 1` it is `C^k` on `Ω`.
* `TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_preciseRepresentative`: at order `k + 1`
  its `k`-th derivative is `α`-Hölder continuous on every compact subset of `Ω`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (the Sobolev embedding theorem).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Metric Set Filter Topology Module
open TauCeti.MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} {Ω : Opens ℂ} {k : ℕ} {u : ℂ → F}

/-- **First-order local Sobolev functions are `W^{1,p}` on relatively compact subdomains.** If a
real function `u` lies in `MemWkpLoc p Ω 1`, then on every open `W` whose closure is compact and
contained in `Ω`, `u` is represented by an element of `W1p volume W p`. -/
theorem MemWkpLoc.exists_w1p [Fact (1 ≤ p)] {u : ℂ → ℝ} (hu : MemWkpLoc p Ω 1 u)
    {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ w : W1p volume W p, W1p.value w =ᵐ[volume.restrict W] u := by
  obtain ⟨hup, D, hD, hDp⟩ := memWkpLoc_succ_iff_of_isOpen.1 hu
  have hWle : W ≤ Ω := SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)
  have huW : MemLp u p (volume.restrict W) := hup.memLp_restrict_of_isCompact_closure hWc hWΩ
  -- The weak gradient is the Riesz representative of the weak derivative.
  set G : ℂ → ℂ := fun z => (InnerProductSpace.toDual ℝ ℂ).symm (D z)
  have hG : MemLp G p (volume.restrict W) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
      ((memWkpLoc_zero_iff.1 hDp).memLp_restrict_of_isCompact_closure hWc hWΩ)
  have hGD : ∀ z, innerSL ℝ (G z) = D z := fun z => by
    ext y
    simp only [G, innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
  have hmk : HasWeakFDerivOn volume W (huW.toLp u) (fun z => innerSL ℝ (hG.toLp G z)) := by
    refine ((hD.mono hWle).congr_ae huW.coeFn_toLp.symm).congr_ae_deriv ?_
    filter_upwards [hG.coeFn_toLp] with z hz
    rw [hz, hGD]
  exact ⟨W1p.mk _ _ hmk, by rw [W1p.value_mk]; exact huW.coeFn_toLp⟩

/-- A locally `Lᵖ` map on an open planar set, `1 ≤ p`, agrees almost everywhere there with its
precise representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative [CompleteSpace F] (hp : 1 ≤ p)
    (hu : MemLpLoc p Ω u) : u =ᵐ[volume.restrict Ω] preciseRepresentative volume u :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

/-- The real case of `TauCeti.MemWkpLoc.exists_holderOnWith_preciseRepresentative`, obtained from
the interior Morrey embedding for `W1p` on a thickening of the compact set. -/
private theorem MemWkpLoc.exists_holderOnWith_preciseRepresentative_real {u : ℂ → ℝ}
    (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (preciseRepresentative volume u) K := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  let W : Opens ℂ := ⟨thickening δ K, isOpen_thickening⟩
  have hWcl : closure (W : Set ℂ) ⊆ cthickening δ K := closure_thickening_subset_cthickening δ K
  have hKW : K ⊆ W := self_subset_thickening hδ K
  obtain ⟨w, hw⟩ := hu.exists_w1p (hK.cthickening.of_isClosed_subset isClosed_closure hWcl)
    (hWcl.trans hδΩ)
  have hp' : (finrank ℝ ℂ : ℝ≥0∞) < p := by rwa [Complex.finrank_real_complex, Nat.cast_ofNat]
  obtain ⟨C, hC⟩ := W1p.exists_holderOnWith_preciseRepresentative_of_isCompact hp' w hK hKW
  rw [Complex.finrank_real_complex, Nat.cast_ofNat] at hC
  -- Near `K` the precise representatives of `u` and of its `W1p` representative coincide.
  have heq : EqOn (preciseRepresentative volume (W1p.value w)) (preciseRepresentative volume u) K :=
    fun z hz => preciseRepresentative_congr_ae_nhds (W.isOpen.mem_nhds (hKW hz)) hw
  exact ⟨C, fun x hx y hy => by simpa only [heq hx, heq hy] using hC x hx y hy⟩

/-- The real case of `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`. -/
private theorem MemWkpLoc.continuousOn_preciseRepresentative_real {u : ℂ → ℝ} (hp : 2 < p)
    (hu : MemWkpLoc p Ω 1 u) : ContinuousOn (preciseRepresentative volume u) Ω := fun x hx => by
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hx)
  obtain ⟨C, hC⟩ := hu.exists_holderOnWith_preciseRepresentative_real hp (isCompact_closedBall x r)
    hrΩ
  exact ((hC.continuousOn (ENNReal.toNNReal_one_sub_div_pos hp)).continuousAt
    (closedBall_mem_nhds x hr)).continuousWithinAt

/-- In a basis `b` of `F`, the precise representative of a first-order local Sobolev map agrees
on `Ω` with the combination of the precise representatives of its coordinates. -/
private theorem MemWkpLoc.eqOn_preciseRepresentative_sum [FiniteDimensional ℝ F] {ι : Type*}
    [Fintype ι] (b : Basis ι ℝ F) (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) :
    EqOn (preciseRepresentative volume u)
      (fun z => ∑ i, preciseRepresentative volume (fun w => b.repr (u w) i) z • b i) Ω := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hui := (b.memWkpLoc_iff (p := p) (U := Ω) (k := 1)).1 hu
  have hae : u =ᵐ[volume.restrict Ω]
      fun z => ∑ i, preciseRepresentative volume (fun w => b.repr (u w) i) z • b i := by
    filter_upwards [ae_all_iff.2 fun i => (hui i).memLpLoc.ae_eq_preciseRepresentative hp1]
      with z hz
    calc u z = ∑ i, b.repr (u z) i • b i := (b.sum_repr _).symm
      _ = _ := Finset.sum_congr rfl fun i _ => by rw [hz i]
  exact eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hu.memLpLoc.locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed) hae
    (continuousOn_finsetSum _ fun i _ =>
      ((hui i).continuousOn_preciseRepresentative_real hp).smul continuousOn_const)

/-- **Morrey's embedding for first-order local Sobolev maps.** If `2 < p` and
`u ∈ MemWkpLoc p Ω 1` takes values in a finite-dimensional space, then its precise representative
is Hölder continuous with exponent `1 - 2 / p` on every compact subset of `Ω`. -/
theorem MemWkpLoc.exists_holderOnWith_preciseRepresentative [FiniteDimensional ℝ F] (hp : 2 < p)
    (hu : MemWkpLoc p Ω 1 u) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (preciseRepresentative volume u) K := by
  set α := ((1 : ℝ≥0∞) - 2 / p).toNNReal
  let b := Module.finBasis ℝ F
  have hui := (b.memWkpLoc_iff (p := p) (U := Ω) (k := 1)).1 hu
  -- Each coordinate term is Hölder on `K`, hence so is their sum.
  have hterm : ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
      (fun z => preciseRepresentative volume (fun w => b.repr (u w) i) z • b i) K := fun i => by
    obtain ⟨C, hC⟩ := (hui i).exists_holderOnWith_preciseRepresentative_real hp hK hKΩ
    refine ⟨‖b i‖₊ * C, HolderOnWith.of_dist_le fun x hx y hy => ?_⟩
    rw [dist_eq_norm, ← sub_smul, norm_smul, ← dist_eq_norm, NNReal.coe_mul, coe_nnnorm,
      mul_assoc, mul_comm]
    gcongr
    exact hC.dist_le hx hy
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0, HolderOnWith C α
      (∑ i, fun z => preciseRepresentative volume (fun w => b.repr (u w) i) z • b i) K :=
    Finset.sum_induction _ (fun f => ∃ C : ℝ≥0, HolderOnWith C α f K)
      (fun _ _ ⟨C, hf⟩ ⟨C', hg⟩ => ⟨C + C', hf.add hg⟩) ⟨0, HolderWith.zero.holderOnWith K⟩
      fun i _ => hterm i
  rw [Finset.sum_fn] at hC
  have heq := hu.eqOn_preciseRepresentative_sum b hp
  exact ⟨C, fun x hx y hy => by simpa only [heq (hKΩ hx), heq (hKΩ hy)] using hC x hx y hy⟩

/-- **First-order local Sobolev maps are continuous.** If `2 < p` and `u ∈ MemWkpLoc p Ω 1`
takes values in a finite-dimensional space, then its precise representative, which agrees with `u`
almost everywhere on `Ω`, is continuous on `Ω`. -/
theorem MemWkpLoc.continuousOn_preciseRepresentative [FiniteDimensional ℝ F] (hp : 2 < p)
    (hu : MemWkpLoc p Ω 1 u) : ContinuousOn (preciseRepresentative volume u) Ω := by
  let b := Module.finBasis ℝ F
  have hui := (b.memWkpLoc_iff (p := p) (U := Ω) (k := 1)).1 hu
  exact (continuousOn_finsetSum _ fun i _ =>
    ((hui i).continuousOn_preciseRepresentative_real hp).smul continuousOn_const).congr
      (hu.eqOn_preciseRepresentative_sum b hp)

/-- The induction behind `TauCeti.MemWkpLoc.contDiffOn_preciseRepresentative` and
`TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_preciseRepresentative`, carried out for all
finite-dimensional codomains at once, since the weak derivative takes values in `ℂ →L[ℝ] F`. -/
private theorem MemWkpLoc.contDiffOn_and_holderOnWith (hp : 2 < p) (k : ℕ) :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {u : ℂ → F},
      MemWkpLoc p Ω (k + 1) u → ContDiffOn ℝ k (preciseRepresentative volume u) Ω ∧
        ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal
          (iteratedFDeriv ℝ k (preciseRepresentative volume u)) K := by
  induction k with
  | zero =>
    intro F _ _ _ u hu
    refine ⟨contDiffOn_zero.2 (hu.continuousOn_preciseRepresentative hp), fun K hK hKΩ => ?_⟩
    obtain ⟨C, hC⟩ := hu.exists_holderOnWith_preciseRepresentative hp hK hKΩ
    rw [iteratedFDeriv_zero_eq_comp]
    exact ⟨C, (continuousMultilinearCurryFin0 ℝ ℂ F).symm.isometry.comp_holderOnWith hC⟩
  | succ k ih =>
    intro F _ _ _ u hu
    have hp1 : 1 ≤ p := one_le_two.trans hp.le
    obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
    obtain ⟨hDc, hDh⟩ := ih hDk
    set g := preciseRepresentative volume u
    set G := preciseRepresentative volume D
    have hgc : ContinuousOn g Ω := (hu.of_le (by omega)).continuousOn_preciseRepresentative hp
    -- The continuous representative of `u` has the `C^k` representative of `D` as its weak
    -- derivative, hence as its classical derivative on `Ω`.
    have hgG : HasWeakFDerivOn volume Ω g G :=
      (hD.congr_ae (hu.memLpLoc.ae_eq_preciseRepresentative hp1)).congr_ae_deriv
        (hDk.memLpLoc.ae_eq_preciseRepresentative hp1)
    have hfd : ∀ x ∈ Ω, fderiv ℝ g =ᶠ[𝓝 x] G := fun x hx =>
      eventually_of_mem (Ω.isOpen.mem_nhds hx) fun y hy =>
        hgG.fderiv_eq_of_continuousOn hgc hDc.continuousOn hy
    refine ⟨by exact_mod_cast hgG.contDiffOn_succ hgc (n := k) (by exact_mod_cast hDc),
      fun K hK hKΩ => ?_⟩
    obtain ⟨C, hC⟩ := hDh K hK hKΩ
    have key : ∀ z ∈ K, iteratedFDeriv ℝ (k + 1) g z =
        (continuousMultilinearCurryRightEquiv' ℝ k ℂ F).symm (iteratedFDeriv ℝ k G z) :=
      fun z hz => by
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
          ((hfd z (hKΩ hz)).iteratedFDeriv ℝ k).eq_of_nhds]
    refine ⟨C, fun x hx y hy => ?_⟩
    rw [key x hx, key y hy, LinearIsometryEquiv.edist_map]
    exact hC x hx y hy

/-- **Higher-order Morrey embedding for local Sobolev maps.** If `2 < p` and
`u ∈ MemWkpLoc p Ω (k + 1)` takes values in a finite-dimensional space, then its precise
representative, which agrees with `u` almost everywhere on `Ω`, is `C^k` on `Ω`. -/
theorem MemWkpLoc.contDiffOn_preciseRepresentative [FiniteDimensional ℝ F] (hp : 2 < p)
    (hu : MemWkpLoc p Ω (k + 1) u) : ContDiffOn ℝ k (preciseRepresentative volume u) Ω :=
  (contDiffOn_and_holderOnWith hp k hu).1

/-- **Hölder continuity of the top derivative.** If `2 < p` and `u ∈ MemWkpLoc p Ω (k + 1)` takes
values in a finite-dimensional space, then the `k`-th derivative of its precise representative is
Hölder continuous with exponent `1 - 2 / p` on every compact subset of `Ω`. Together with
`TauCeti.MemWkpLoc.contDiffOn_preciseRepresentative`, the precise representative is `C^{k,1-2/p}`
on compact subsets of `Ω`. -/
theorem MemWkpLoc.exists_holderOnWith_iteratedFDeriv_preciseRepresentative
    [FiniteDimensional ℝ F] (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u) {K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal
      (iteratedFDeriv ℝ k (preciseRepresentative volume u)) K :=
  (contDiffOn_and_holderOnWith hp k hu).2 K hK hKΩ

end TauCeti
