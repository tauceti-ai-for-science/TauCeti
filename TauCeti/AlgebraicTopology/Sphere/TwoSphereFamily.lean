/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.AlgebraicTopology.Sphere.TangentCircle
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.PathSpace.Loop

/-!
# A family of 2-spheres in a sphere representing a generator of `H_{n-2}(Ω²Sⁿ)`

Let `V` be a real inner product space, `u` a unit vector of `V`, `v` a unit vector of the
hyperplane `W = u^⊥` and `p` a unit vector of `W` orthogonal to `v`. For a unit vector `q` of
`W` orthogonal to `v`, `TauCeti.tangentCircleLoopMap` gives the loop of `S_W` at `p` running along
the circle through `p` and `q` tangent to `v`. Seen in `S_V`, every point of this loop is a unit
vector orthogonal to `u`, through which runs the circle through `p` tangent to `u`. Sweeping these
circles along the first loop gives a double loop of `S_V` at `p`, that is a map of the 2-sphere to
`S_V` (`TauCeti.tangentCircleDoubleLoopMap`):

`σ_p : Σ_p → Ω (Ω S_V p) (refl p)`, `σ_p q s t = c_u (c_v q (2π s)) (2π t)`,

where `Σ_p` is the sphere of the vectors of `W` orthogonal to `v`, of dimension `dim V - 3`, and
`c_u r θ` is the point at angle `θ` of the circle through `p` and `r` tangent to `u`.

When `dim V = n + 1` with `n ≥ 4`, the map `σ_p` induces an isomorphism
`H_{n-2}(Σ_p; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`
(`TauCeti.isIso_singularHomologyMap_tangentCircleDoubleLoopMap`). Since `Σ_p` is an
`(n - 2)`-sphere, this says that `σ_p` sends the fundamental class of `Σ_p` to a generator of
`H_{n-2}(Ω²Sⁿ; ℤ) ≅ ℤ`. The proof follows the paper's. Compose `σ_p` with a degree-one map
`c : I^{n-2} → Σ_p`. Under the loop-space shifts `π_{n-2}(Ω²Sⁿ) ≅ πₙ(Sⁿ)`, the class of `σ_p ∘ c`
becomes that of the circles swept along the circles through the points of `c`, read on the cube
`Iⁿ` with its coordinates reordered. This map is onto and identifies only points of the boundary
of the cube, so it generates `πₙ(Sⁿ)` (`TauCeti.isIso_hurewicz_tangentCircleGenLoop`). The
Hurewicz theorem for the `(n - 3)`-connected space `Ω²Sⁿ` and the `(n - 1)`-connected space `Sⁿ`
turns this into the statement on homology. The case `n = 3`, where `Ω²S³` is only connected and
the degree is one, is not treated here.

This is Example 6.20 and Proposition 6.21 of Barraud–Damian–Humilière–Oancea, for a fixed point
`p` of `Sⁿ` and fixed vectors `u(p)`, `v(p)`. There `n = 4k - 1`, and `u`, `v` are two pointwise
orthonormal vector fields on `Sⁿ`, which exist in those dimensions and let `p` vary, so that the
maps `σ_p` form a family over `Sⁿ`; for a single point no such restriction on `n` is needed.

## Main declarations

* `TauCeti.tangentCircleLoopMap`: the loops `φ_{V,u}` of circles through the points of the
  equator, tangent to `u`.
* `TauCeti.tangentCircleDoubleLoopMap`: the double loops `σ_p`.
* `TauCeti.isIso_singularHomologyMap_tangentCircleDoubleLoopMap`: `σ_p` induces an isomorphism
  `H_{n-2}(Σ_p; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)` for `n ≥ 4`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Example 6.20 and Proposition 6.21.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Metric Module Real
open scoped RealInnerProductSpace unitInterval Topology.Homotopy

namespace TauCeti

/-! ### The loops of circles tangent to a direction -/

section Loop

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V}

/-- **The loops of circles tangent to `u`** (the map `φ_{V,u}` of
Barraud–Damian–Humilière–Oancea, Example 6.20). A point `q` of the equator orthogonal to the unit
vector `u` is sent to the loop of the unit sphere at the point `p₀` of the equator running along
the circle through `p₀` and `q` tangent to `u`, proportionally to arc length. -/
def tangentCircleLoopMap (hu : ‖u‖ = 1) (p₀ : sphereEquator u) :
    C(sphereEquator u, Ω (sphere (0 : V) 1) (p₀ : sphere (0 : V) 1)) where
  toFun q :=
    { toFun t := ⟨tangentCircle ((p₀ : sphere (0 : V) 1) : V) u ((q : sphere (0 : V) 1) : V)
          (2 * π * t),
        mem_sphere_zero_iff_norm.2 (norm_tangentCircle (mem_sphere_zero_iff_norm.1 p₀.1.2) hu
          (mem_sphereEquator.1 p₀.2) (mem_sphere_zero_iff_norm.1 q.1.2)
          (mem_sphereEquator.1 q.2) _)⟩
      continuous_toFun := Continuous.subtype_mk ((continuous_tangentCircle _ u).comp
        (continuous_const.prodMk (continuous_const.mul continuous_subtype_val))) _
      source' := Subtype.ext (by simp)
      target' := Subtype.ext (by simpa using tangentCircle_add_two_pi _ u _ 0) }
  continuous_toFun := by
    refine Path.continuous_uncurry_iff.1 (Continuous.subtype_mk ?_ _)
    exact (continuous_tangentCircle _ u).comp (Continuous.prodMk
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))

@[simp]
theorem coe_tangentCircleLoopMap_apply_apply (hu : ‖u‖ = 1) (p₀ q : sphereEquator u) (t : I) :
    (tangentCircleLoopMap hu p₀ q t : V) = tangentCircle ((p₀ : sphere (0 : V) 1) : V) u
      ((q : sphere (0 : V) 1) : V) (2 * π * t) :=
  (rfl)

/-- The loop of circles at the base point itself is the constant loop. -/
@[simp]
theorem tangentCircleLoopMap_self (hu : ‖u‖ = 1) (p₀ : sphereEquator u) :
    tangentCircleLoopMap hu p₀ p₀ = Path.refl _ :=
  Path.ext (funext fun _ ↦ Subtype.ext (tangentCircle_self _ u _))

end Loop

/-! ### The double loops of circles swept along circles -/

section DoubleLoop

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V}
  {v : (ℝ ∙ u)ᗮ}

/-- **The double loops of circles swept along circles** (the map `σ_p` of
Barraud–Damian–Humilière–Oancea, Example 6.20). Let `u` be a unit vector of `V`, `v` a unit vector
of `W = u^⊥` and `p` a unit vector of `W` orthogonal to `v`. A unit vector `q` of `W` orthogonal to
`v` is sent to the double loop of the unit sphere `S_V` at `p` whose loop at time `s` runs along
the circle through `p` tangent to `u` and through the point at time `s` of the circle of `S_W`
through `p` and `q` tangent to `v`. The second circle is `TauCeti.tangentCircleLoopMap` for `W`,
seen in the equator `S_V ∩ u^⊥`, and the first is the loop map of `TauCeti.tangentCircleLoopMap`
for `V`. -/
def tangentCircleDoubleLoopMap (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p : sphereEquator v) :
    C(sphereEquator v, Ω (Ω (sphere (0 : V) 1)
      ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator p : sphere (0 : V) 1))
        (Path.refl _)) :=
  ((tangentCircleLoopMap hu _).loopMap (tangentCircleLoopMap_self hu _)).comp
    (((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator.loopMap rfl).comp
      (tangentCircleLoopMap hv p))

@[simp]
theorem coe_tangentCircleDoubleLoopMap_apply_apply_apply (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (p q : sphereEquator v) (s t : I) :
    (tangentCircleDoubleLoopMap hu hv p q s t : V) =
      tangentCircle (((p : sphere (0 : (ℝ ∙ u)ᗮ) 1) : (ℝ ∙ u)ᗮ) : V) u
        ((tangentCircle ((p : sphere (0 : (ℝ ∙ u)ᗮ) 1) : (ℝ ∙ u)ᗮ) v
          ((q : sphere (0 : (ℝ ∙ u)ᗮ) 1) : (ℝ ∙ u)ᗮ) (2 * π * s) : (ℝ ∙ u)ᗮ) : V)
        (2 * π * t) := by
  simp [tangentCircleDoubleLoopMap]

/-- The double loop at the base point is the constant double loop. -/
@[simp]
theorem tangentCircleDoubleLoopMap_self (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p : sphereEquator v) :
    tangentCircleDoubleLoopMap hu hv p p = Path.refl _ := by
  simp [tangentCircleDoubleLoopMap]

end DoubleLoop

/-! ### The double loops represent a generator -/

section Generator

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {u : V}
  {v : (ℝ ∙ u)ᗮ} {m : ℕ}

/-- The reordering `(z₀, …, z_{m+3}) ↦ (z_{m+3}, z_{m+2}, z₀, …, z_{m+1})` of the coordinates of
the cube `I^{m+4}`, which moves the two loop coordinates of a family of double loops to the front,
where `TauCeti.tangentCircleGenLoop` puts its circle coordinate. -/
private def frontPerm (m : ℕ) : Fin (m + 4) → Fin (m + 4) :=
  Fin.cons (Fin.last _) (Fin.cons (Fin.last _).castSucc fun i ↦ i.castSucc.castSucc)

private theorem bijective_frontPerm (m : ℕ) : Function.Bijective (frontPerm m) := by
  refine Finite.injective_iff_bijective.1 (Fin.cons_injective_iff.2 ⟨?_,
    Fin.cons_injective_iff.2 ⟨?_, (Fin.castSucc_injective _).comp (Fin.castSucc_injective _)⟩⟩)
  · rintro ⟨i, hi⟩
    induction i using Fin.cases <;> simp [Fin.ext_iff] at hi
    omega
  · rintro ⟨i, hi⟩
    simp [Fin.ext_iff] at hi
    omega

/-- The loop-space shifts `π_{m+2}(Ω²X) ≅ π_{m+3}(ΩX) ≅ π_{m+4}(X)` send the class of a family
`f ∘ c` of double loops to the class of the generalized loop
`z ↦ f (c (z₀, …, z_{m+1})) z_{m+2} z_{m+3}`. -/
private theorem pathLoopSpaceMulEquiv_pathLoopSpaceMulEquiv_map_mk {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(Y, Ω (Ω X x) (Path.refl x))) (hf : f y = Path.refl _) (c : Ω^ (Fin (m + 2)) Y y) :
    ∃ G : Ω^ (Fin (m + 4)) X x,
      (∀ z, G z = f (c fun i ↦ z i.castSucc.castSucc) (z (Fin.last _).castSucc) (z (Fin.last _))) ∧
      HomotopyGroup.pathLoopSpaceMulEquiv (m + 2) (HomotopyGroup.pathLoopSpaceMulEquiv (m + 1)
        (HomotopyGroup.map f hf ⟦c⟧)) = ⟦G⟧ := by
  rw [HomotopyGroup.map_mk, HomotopyGroup.pathLoopSpaceMulEquiv_mk,
    HomotopyGroup.pathLoopSpaceMulEquiv_mk]
  refine ⟨_, fun z ↦ ?_, rfl⟩
  simp [GenLoop.congr, GenLoop.genLoopGenLoopEquiv]
  -- The remaining goal only reindexes coordinates: `Fin.castAdd`, `Fin.natAdd` and
  -- `finSumFinEquiv` of the shifts compute the same `Fin` values as `castSucc` and `last`.
  rfl

/-- **The double loops of circles represent a generator** (Barraud–Damian–Humilière–Oancea,
Proposition 6.21, for a fixed point `p`). If `V` has dimension `n + 1` with `n = m + 4 ≥ 4`, the
double loops of circles swept along circles, `σ_p : Σ_p → Ω²Sⁿ`, induce an isomorphism
`H_{n-2}(Σ_p; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)` on integral singular homology. As `Σ_p` is a sphere of
dimension `n - 2`, the class `σ_{p*}[Σ_p]` generates `H_{n-2}(Ω²Sⁿ; ℤ) ≅ ℤ`. -/
theorem isIso_singularHomologyMap_tangentCircleDoubleLoopMap (hV : finrank ℝ V = m + 5)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (p : sphereEquator v) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2)).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom (tangentCircleDoubleLoopMap hu hv p))) := by
  let ι := (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).sphereToEquator
  let Φ := tangentCircleDoubleLoopMap hu hv p
  let R := ModuleCat.of ℤ ℤ
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have : Fact (finrank ℝ V = (m + 4) + 1) := ⟨hV⟩
  -- A degree-one map `c : I^{m+2} → Σ_p` onto the `(m + 2)`-sphere `Σ_p`.
  obtain ⟨c, hcs, hci⟩ := exists_genLoop_sphereEquator hv0
    (Submodule.finrank_orthogonal_span_singleton (n := m + 4) hu0) p
  have hc : IsIso (GenLoop.hurewicz R c) :=
    GenLoop.isIso_hurewicz_of_bijective_toSphere R
      ⟨(GenLoop.injective_toSphere_iff c).2 hci, (GenLoop.surjective_toSphere_iff c).2 fun q ↦ by
        by_cases hq : q = p
        · exact ⟨0, by rw [hq, GenLoop.boundary c 0 ⟨0, Or.inl rfl⟩]⟩
        · exact hcs q hq⟩
  -- The circles of `S_V` swept along the circles of `S_W` through the points of `c`.
  let c₁ := tangentCircleGenLoop hv c
  let c₂ := GenLoop.map ι rfl c₁
  let T := tangentCircleGenLoop hu c₂
  have hc₂s : ∀ q, q ≠ ι p → ∃ y, c₂ y = q := by
    intro q hq
    obtain ⟨w, rfl⟩ := (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).surjective_sphereToEquator q
    obtain ⟨y, hy⟩ := surjective_tangentCircleGenLoop hv c hcs w
    refine ⟨y, by rw [GenLoop.map_apply, hy]⟩
  have hc₂i : ∀ y z, c₂ y = c₂ z → y = z ∨ y ∈ Cube.boundary (Fin (m + 3)) ∧
      z ∈ Cube.boundary (Fin (m + 3)) := fun y z h ↦
    eq_or_of_tangentCircleGenLoop_eq hv c hcs hci
      ((LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).injective_sphereToEquator
        (by rwa [GenLoop.map_apply, GenLoop.map_apply] at h))
  -- Through the loop-space shifts, the class of `σ_p ∘ c` is that of `T`, up to reordering the
  -- coordinates of the cube.
  obtain ⟨G, hG, hDG⟩ := pathLoopSpaceMulEquiv_pathLoopSpaceMulEquiv_map_mk Φ
    (tangentCircleDoubleLoopMap_self hu hv p) c
  have hGT : ∀ z, G z = T (z ∘ frontPerm m) := by
    intro z
    refine Subtype.ext ?_
    rw [hG, coe_tangentCircleDoubleLoopMap_apply_apply_apply, coe_tangentCircleGenLoop_apply]
    simp [c₂, c₁, ι, frontPerm, Fin.comp_cons]
    rfl
  have hGs : Function.Bijective (GenLoop.toSphere G) :=
    (GenLoop.bijective_toSphere_iff_of_apply_eq_comp (bijective_frontPerm m) hGT).2
      ⟨(GenLoop.injective_toSphere_iff T).2 fun _ _ h ↦
          eq_or_of_tangentCircleGenLoop_eq hu c₂ hc₂s hc₂i h,
        (GenLoop.surjective_toSphere_iff T).2 (surjective_tangentCircleGenLoop hu c₂ hc₂s)⟩
  -- `Sⁿ` and `Ω²Sⁿ` are `(m + 3)`- and `(m + 1)`-connected.
  have hS : ∀ k < m + 4, Subsingleton (HomotopyGroup (Fin k) (sphere (0 : V) 1) (ι p)) :=
    fun k hk ↦ subsingleton_homotopyGroup_sphere_of_lt hV (by simpa using hk) _
  have hΩ : ∀ k < m + 2, Subsingleton (HomotopyGroup (Fin k)
      (Ω (Ω (sphere (0 : V) 1) (ι p)) (Path.refl _)) (Path.refl _)) := fun k hk ↦
    (subsingleton_homotopyGroup_loopSpace_iff _ k).2
      ((subsingleton_homotopyGroup_loopSpace_iff _ (k + 1)).2 (hS (k + 2) (by omega)))
  -- The class of `G` generates `π_{m+4}(Sⁿ)` freely, hence so does that of `σ_p ∘ c` in
  -- `π_{m+2}(Ω²Sⁿ)`, and its Hurewicz class generates `H_{m+2}(Ω²Sⁿ; ℤ)`.
  have hG' : Function.Bijective fun z : ℤ ↦
      z • Additive.ofMul (α := HomotopyGroup (Fin (m + 4)) (sphere (0 : V) 1) _) ⟦G⟧ :=
    (HomotopyGroup.isIso_hurewicz_iff_bijective_zsmul hS _).1 <| by
      rw [HomotopyGroup.hurewicz_mk]
      exact GenLoop.isIso_hurewicz_of_bijective_toSphere R hGs
  let D := (HomotopyGroup.pathLoopSpaceMulEquiv (m + 1)).trans
    (HomotopyGroup.pathLoopSpaceMulEquiv (X := sphere (0 : V) 1)
    (x := ι p) (m + 2))
  have hσc : IsIso (GenLoop.hurewicz R (GenLoop.map Φ (tangentCircleDoubleLoopMap_self hu hv p)
      c)) := by
    rw [← HomotopyGroup.hurewicz_mk, ← HomotopyGroup.map_mk,
      HomotopyGroup.isIso_hurewicz_iff_bijective_zsmul hΩ]
    have h : (fun z : ℤ ↦
        z • Additive.ofMul (α := HomotopyGroup (Fin (m + 4)) (sphere (0 : V) 1) _) ⟦G⟧) =
        D.toAdditive ∘ fun z : ℤ ↦ z • Additive.ofMul
          (HomotopyGroup.map Φ (tangentCircleDoubleLoopMap_self hu hv p) ⟦c⟧) := by
      funext z
      rw [Function.comp_apply, map_zsmul]
      exact congrArg (z • Additive.ofMul ·) hDG.symm
    rw [h, EquivLike.comp_bijective] at hG'
    exact hG'
  -- Finally `σ_{p*} ∘ hur(c) = hur(σ_p ∘ c)` with both Hurewicz classes isomorphisms.
  rw [GenLoop.hurewicz_map] at hσc
  exact IsIso.of_isIso_comp_left (GenLoop.hurewicz R c) _

end Generator

end TauCeti
