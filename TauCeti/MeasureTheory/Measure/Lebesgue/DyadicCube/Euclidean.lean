/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Measure.Lebesgue.DyadicCube
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Dyadic cubes and Euclidean balls

Dyadic cubes live in `ι → ℝ` with the sup norm (`TauCeti.dyadicCube`). This file compares them
with the balls of the Euclidean space `EuclideanSpace ℝ ι`, through `WithLp.ofLp`, which preserves
volume. The Euclidean ball about the centre of a cube whose radius is half the side lies in the
cube, and is a fixed fraction of its volume; two points of a cube of level `k` are at Euclidean
distance less than `n 2ᵏ`; and a Euclidean ball of radius `r` is covered by `2ⁿ` dyadic cubes of
a level of side between `2 r` and `4 r`, of total volume a bounded multiple of the volume of the
ball. These comparisons pass estimates on Euclidean balls to dyadic cubes and back, as in the
Krylov–Safonov covering arguments.

## Main declarations

* `TauCeti.volume_preimage_ofLp_dyadicCube`: a dyadic cube has the same volume in `ι → ℝ` and in
  `EuclideanSpace ℝ ι`.
* `TauCeti.dist_lt_of_ofLp_mem_dyadicCube`: two points of a dyadic cube of level `k` are at
  Euclidean distance less than `n 2ᵏ`.
* `TauCeti.ball_dyadicCenter_subset_preimage_dyadicCube`,
  `TauCeti.volume_ball_dyadicCenter`: the Euclidean ball about the centre of a cube whose radius
  is half the side lies in the cube, and its volume is the fraction `ωₙ / 2ⁿ` of that of the cube.
* `TauCeti.exists_card_eq_ball_subset_biUnion`, `TauCeti.two_pow_mul_volume_dyadicCube_le`: a
  Euclidean ball is covered by `2ⁿ` dyadic cubes of comparable total volume.
-/

public section

noncomputable section

open Metric MeasureTheory Set WithLp
open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A dyadic cube has the same volume in `ι → ℝ` and in `EuclideanSpace ℝ ι`. -/
@[simp]
theorem volume_preimage_ofLp_dyadicCube (k : ℤ) (m : ι → ℤ) :
    volume (ofLp ⁻¹' dyadicCube k m : Set (EuclideanSpace ℝ ι)) = volume (dyadicCube k m) :=
  (PiLp.volume_preserving_ofLp ι).measure_preimage (measurableSet_dyadicCube k m).nullMeasurableSet

/-- Two points of `EuclideanSpace ℝ ι` lying in a common dyadic cube of level `k` are at Euclidean
distance less than `n 2ᵏ`, where `n` is the dimension. -/
theorem dist_lt_of_ofLp_mem_dyadicCube [Nonempty ι] {k : ℤ} {m : ι → ℤ}
    {x y : EuclideanSpace ℝ ι} (hx : ofLp x ∈ dyadicCube k m) (hy : ofLp y ∈ dyadicCube k m) :
    dist x y < Fintype.card ι * 2 ^ k := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  exact (PiLp.dist_le_sqrt_card_mul_dist_ofLp x y).trans_lt
    ((mul_lt_mul_of_pos_left (dist_lt_of_mem_dyadicCube hx hy) (by positivity)).trans_le
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.2 (Or.inr hn)) (by positivity)))

/-- The Euclidean ball about the centre of a dyadic cube whose radius is half its side lies in the
cube. -/
theorem ball_dyadicCenter_subset_preimage_dyadicCube (k : ℤ) (m : ι → ℤ) :
    ball (toLp 2 (dyadicCenter k m)) (2 ^ k / 2) ⊆ ofLp ⁻¹' dyadicCube k m := by
  intro y hy
  rw [mem_preimage, dyadicCube_eq_pi]
  intro i _
  have h := (PiLp.norm_apply_le (y - toLp 2 (dyadicCenter k m)) i).trans_lt
    (mem_ball_iff_norm.1 hy)
  simp only [PiLp.sub_apply, dyadicCenter_apply, Real.norm_eq_abs, abs_sub_lt_iff] at h
  constructor <;> linarith

/-- The volume of the Euclidean ball about the centre of a dyadic cube whose radius is half its
side is the fraction `ωₙ / 2ⁿ` of the volume of the cube, where `ωₙ` is the volume of the unit
ball. -/
theorem volume_ball_dyadicCenter (k : ℤ) (m : ι → ℤ) :
    volume (ball (toLp 2 (dyadicCenter k m)) (2 ^ k / 2)) =
      ENNReal.ofReal (volume.real (ball (0 : EuclideanSpace ℝ ι) 1) / 2 ^ Fintype.card ι) *
        volume (dyadicCube k m) := by
  rw [Measure.addHaar_ball_of_pos _ _ (by positivity), finrank_euclideanSpace,
    ← ofReal_measureReal (μ := volume) (s := ball (0 : EuclideanSpace ℝ ι) 1)
      measure_ball_lt_top.ne, volume_dyadicCube, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_pow]
  field_simp

/-- A Euclidean ball of radius `r` is covered by `2ⁿ` dyadic cubes of a level of side `2ᴷ > 2 r`,
whose corners `m 2ᴷ` lie within `n (r + 2ᴷ)` of the centre of the ball. -/
theorem exists_card_eq_ball_subset_biUnion [Nonempty ι]
    (c : EuclideanSpace ℝ ι) {r : ℝ} {K : ℤ} (hr : 0 < r) (hK : 2 * r < 2 ^ K) :
    ∃ S : Finset (ι → ℤ), S.card = 2 ^ Fintype.card ι ∧
      ball c r ⊆ ⋃ m ∈ S, ofLp ⁻¹' dyadicCube K m ∧
      ∀ m ∈ S, dist (toLp 2 fun i ↦ (m i : ℝ) * 2 ^ K) c ≤ Fintype.card ι * (r + 2 ^ K) := by
  classical
  have hK0 : (0 : ℝ) < 2 ^ K := zpow_pos two_pos K
  have hn : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.2 Fintype.card_pos
  set b : ι → ℤ := fun i ↦ ⌊(c i - r) / 2 ^ K⌋
  refine ⟨Fintype.piFinset fun i ↦ ({b i, b i + 1} : Finset ℤ), ?_, fun x hx ↦ ?_, fun m hm ↦ ?_⟩
  · rw [Fintype.card_piFinset, Finset.prod_congr rfl fun i _ ↦
      Finset.card_pair (by omega : b i ≠ b i + 1), Finset.prod_const, Finset.card_univ]
  · refine mem_biUnion (x := dyadicIndex K (ofLp x)) (Fintype.mem_piFinset.2 fun i ↦ ?_)
      (mem_dyadicCube_dyadicIndex K _)
    have := (PiLp.norm_apply_le (x - c) i).trans_lt (mem_ball_iff_norm.1 hx)
    rw [PiLp.sub_apply, Real.norm_eq_abs] at this
    rw [dyadicIndex_apply]
    exact floor_div_mem_pair hK0 hK this
  · refine (PiLp.dist_le_sqrt_card_mul_dist_ofLp _ _).trans ((mul_le_mul_of_nonneg_left
      ((dist_pi_le_iff (by positivity)).2 fun i ↦ ?_) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.2 (Or.inr hn)) (by positivity)))
    have hb1 := Int.floor_le ((c i - r) / 2 ^ K)
    have hb2 := Int.lt_floor_add_one ((c i - r) / 2 ^ K)
    rw [le_div_iff₀ hK0] at hb1
    rw [div_lt_iff₀ hK0] at hb2
    have hmi := Fintype.mem_piFinset.1 hm i
    rw [Finset.mem_insert, Finset.mem_singleton] at hmi
    rw [ofLp_toLp, Real.dist_eq, abs_le]
    rcases hmi with h | h <;> rw [h] <;> push_cast <;> constructor <;> nlinarith

/-- `2ⁿ` dyadic cubes of side `2ᴷ ≤ 4 r` have total volume at most `8ⁿ / ωₙ` times the volume of
a Euclidean ball of radius `r`, where `ωₙ` is the volume of the unit ball. -/
theorem two_pow_mul_volume_dyadicCube_le (c : EuclideanSpace ℝ ι) {r : ℝ} {K : ℤ} (m : ι → ℤ)
    (hr : 0 < r) (hK : (2 : ℝ) ^ K ≤ 4 * r) :
    2 ^ Fintype.card ι * volume (dyadicCube K m) ≤
      ENNReal.ofReal (8 ^ Fintype.card ι / volume.real (ball (0 : EuclideanSpace ℝ ι) 1)) *
        volume (ball c r) := by
  set N := Fintype.card ι
  set ω := volume.real (ball (0 : EuclideanSpace ℝ ι) 1)
  have hω : 0 < ω := measureReal_ball_pos volume _ one_pos
  have hK0 : (0 : ℝ) < 2 ^ K := zpow_pos two_pos K
  have h2N : (2 : ℝ≥0∞) ^ N = ENNReal.ofReal (2 ^ N) := by
    rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  rw [h2N, volume_dyadicCube, Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace,
    ← ofReal_measureReal (μ := volume) (s := ball (0 : EuclideanSpace ℝ ι) 1)
      measure_ball_lt_top.ne, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc 2 ^ N * (2 ^ K) ^ N ≤ 2 ^ N * (4 * r) ^ N := by gcongr
    _ = 8 ^ N / ω * (r ^ N * ω) := by
        rw [show (8 : ℝ) ^ N = 2 ^ N * 4 ^ N by rw [← mul_pow]; norm_num, mul_pow]
        field_simp

end TauCeti
