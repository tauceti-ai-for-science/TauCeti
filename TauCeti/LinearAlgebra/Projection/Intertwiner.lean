/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection

/-!
# When the intertwining operator of two idempotents is bijective

An idempotent endomorphism `p` of a module `E` splits `E` as `range p ⊕ ker p`
(`LinearMap.IsIdempotentElem.isCompl`). For a second idempotent `q`, the intertwining operator

`U = q * p + (1 - q) * (1 - p)`

acts as `q` on the range of `p` and as `1 - q` on the kernel of `p`, so it sends `range p` into
`range q` and `ker p` into `ker q`. For continuous idempotents,
`ContinuousLinearMap.IsIdempotentElem.rangeEquiv` restricts `U` to an isomorphism of the ranges
whenever `U` is invertible. This file gives a purely algebraic criterion in terms of the two
splittings, which needs no topology.

When the range of `p` is a complement of the kernel of `q`, the operator `U` carries the range of
`p` onto the range of `q`; when the kernel of `p` is a complement of the range of `q`, it carries
the kernel of `p` onto the kernel of `q`; and when both hold, `U` is bijective. So two splittings of
`E` whose parts are complementary in this crossed sense are carried onto each other by a single
automorphism of `E`, built from the two idempotents alone. This applies, for instance, to the
negative and positive spectral subspaces of a nondegenerate symmetric form relative to two
different inner products.

## Main results

* `LinearMap.IsIdempotentElem.map_range_mul_add_one_sub_mul_one_sub`: `U` carries the range of
  `p` onto the range of `q`.
* `LinearMap.IsIdempotentElem.map_ker_mul_add_one_sub_mul_one_sub`: `U` carries the kernel of `p`
  onto the kernel of `q`.
* `LinearMap.IsIdempotentElem.bijective_mul_add_one_sub_mul_one_sub`: `U` is bijective.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6, for the
  intertwining operator of a pair of projections.
-/

public section

open LinearMap

namespace LinearMap.IsIdempotentElem

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {p q : Module.End R E}

/-- On the range of `p`, the operator `q * p + (1 - q) * (1 - p)` agrees with `q`. -/
private theorem mul_add_one_sub_mul_one_sub_apply_of_mem_range (hp : IsIdempotentElem p) {x : E}
    (hx : x ∈ range p) : (q * p + (1 - q) * (1 - p)) x = q x := by
  have hpx : p x = x := hp.mem_range_iff.mp hx
  simp [hpx]

/-- On the kernel of `p`, the operator `q * p + (1 - q) * (1 - p)` agrees with `1 - q`. -/
private theorem mul_add_one_sub_mul_one_sub_apply_of_mem_ker {x : E} (hx : x ∈ ker p) :
    (q * p + (1 - q) * (1 - p)) x = x - q x := by
  simp [mem_ker.mp hx]

/-- **The intertwining operator `q * p + (1 - q) * (1 - p)` carries the range of `p` onto the
range of `q`**, when the range of `p` is a complement of the kernel of `q`. -/
theorem map_range_mul_add_one_sub_mul_one_sub (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : IsCompl (range p) (ker q)) :
    (range p).map (q * p + (1 - q) * (1 - p)) = range q := by
  refine le_antisymm ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [mul_add_one_sub_mul_one_sub_apply_of_mem_range hp hx]
    exact mem_range_self q x
  · -- Split `y = a + b` with `a` in the range of `p` and `b` in the kernel of `q`; then
    -- `U a = q a = q y = y`.
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h.codisjoint.eq_top ▸ Submodule.mem_top :
      y ∈ range p ⊔ ker q)
    refine ⟨a, ha, ?_⟩
    rw [mul_add_one_sub_mul_one_sub_apply_of_mem_range hp ha]
    have hy' : q (a + b) = a + b := hq.mem_range_iff.mp hy
    rwa [map_add, mem_ker.mp hb, add_zero] at hy'

/-- **The intertwining operator `q * p + (1 - q) * (1 - p)` carries the kernel of `p` onto the
kernel of `q`**, when the kernel of `p` is a complement of the range of `q`. -/
theorem map_ker_mul_add_one_sub_mul_one_sub (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h : IsCompl (ker p) (range q)) :
    (ker p).map (q * p + (1 - q) * (1 - p)) = ker q := by
  -- This is the statement for the complementary idempotents `1 - p` and `1 - q`, whose
  -- intertwining operator is the same.
  have h' : IsCompl (range (1 - p)) (ker (1 - q)) := by
    rwa [← hp.ker_eq_range_one_sub, ← hq.range_eq_ker_one_sub]
  have := map_range_mul_add_one_sub_mul_one_sub hp.one_sub hq.one_sub h'
  rwa [sub_sub_cancel, sub_sub_cancel, add_comm, ← hp.ker_eq_range_one_sub,
    ← hq.ker_eq_range_one_sub] at this

/-- **The intertwining operator `q * p + (1 - q) * (1 - p)` of two idempotents is bijective** when
the range of each is a complement of the kernel of the other. -/
theorem bijective_mul_add_one_sub_mul_one_sub (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (h₁ : IsCompl (range p) (ker q)) (h₂ : IsCompl (ker p) (range q)) :
    Function.Bijective ⇑(q * p + (1 - q) * (1 - p)) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, ?_⟩
  · -- Split `x = a + b` along `p`. Then `U x = q a + (b - q b)`, whose two terms lie in the range
    -- and in the kernel of `q`, so both vanish, and then so do `a` and `b`.
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
      (hp.isCompl.codisjoint.eq_top ▸ Submodule.mem_top : x ∈ range p ⊔ ker p)
    rw [map_add, mul_add_one_sub_mul_one_sub_apply_of_mem_range hp ha,
      mul_add_one_sub_mul_one_sub_apply_of_mem_ker hb] at hx
    have hqb : b - q b ∈ ker q := by
      rw [mem_ker, map_sub, hq.mem_range_iff.mp (mem_range_self q b), sub_self]
    have hqa : q a ∈ ker q := by
      rw [eq_neg_of_add_eq_zero_left hx]
      exact Submodule.neg_mem _ hqb
    have hqa0 : q a = 0 := Submodule.disjoint_def.mp hq.isCompl.disjoint _ (mem_range_self q a) hqa
    rw [hqa0, zero_add, sub_eq_zero] at hx
    have ha0 : a = 0 := Submodule.disjoint_def.mp h₁.disjoint _ ha hqa0
    have hb0 : b = 0 := Submodule.disjoint_def.mp h₂.disjoint _ hb (hx ▸ mem_range_self q b)
    rw [ha0, hb0, add_zero]
  · -- The image contains the range and the kernel of `q`, which together span `E`.
    rw [← range_eq_top, eq_top_iff, ← hq.isCompl.codisjoint.eq_top,
      ← map_range_mul_add_one_sub_mul_one_sub hp hq h₁,
      ← map_ker_mul_add_one_sub_mul_one_sub hp hq h₂]
    exact sup_le LinearMap.map_le_range LinearMap.map_le_range

end LinearMap.IsIdempotentElem
