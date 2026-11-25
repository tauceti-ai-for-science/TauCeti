/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.Perfectoid.Untilt
public import TauCeti.RingTheory.Teichmuller
public import TauCeti.RingTheory.WittVector.Teichmuller.Coeff

import Mathlib.NumberTheory.Basic
import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# Functoriality of the tilt, the sharp map and Fontaine's map

A ring homomorphism `f : A →+* B` sends `p A` into `p B`, so it induces a ring homomorphism
`ModP.map p f : A ⧸ p → B ⧸ p` and, coordinatewise on compatible systems of `p`-th roots, a ring
homomorphism of tilts `PreTilt.map p f : A♭ → B♭`. When `A` and `B` are `p`-adically complete,
the sharp map `x ↦ x♯` (Mathlib's `PreTilt.untilt`) and Fontaine's map
`θ : W(A♭) → A` (Mathlib's `WittVector.fontaineTheta`) are natural in `f`:

* `f (x♯) = (PreTilt.map p f x)♯`;
* `f (θ_A w) = θ_B (W(PreTilt.map p f) w)`.

The first identity is the case `I = (p)` of the naturality of the Teichmüller map
(`Perfection.teichmuller₀_map`): `x♯` is the `p`-adic limit of the `p ^ n`-th powers of lifts of
the coordinates of `x`, and `f` preserves these congruences. The second follows from the first,
since a ring homomorphism out of `W(A♭)` into a `p`-adically separated ring is determined by its
values on Teichmüller representatives (`WittVector.ringHom_ext_teichmuller`), and
`θ [x] = x♯`.

These identities let constructions on tilts (products, quotients, base change) be compared with
the corresponding constructions on the rings themselves.

## Main definitions

* `ModP.map p f : ModP A p →+* ModP B p`: reduction modulo `p` of a ring homomorphism.
* `PreTilt.map p f : PreTilt A p →+* PreTilt B p`: the induced homomorphism of tilts.

## Main results

* `PreTilt.coeff_map`: the coordinates of `PreTilt.map p f x` are the reductions of those of `x`.
* `PreTilt.map_id`, `PreTilt.map_comp`: functoriality.
* `PreTilt.untilt_natural`: naturality of the sharp map, `(PreTilt.map p f x)♯ = f (x♯)`.
* `PreTilt.map_untilt_eq_of_map_eq`: if `f : A →+* C` and `g : B →+* C` identify `a ∈ A♭` and
  `b ∈ B♭` in `C♭`, and `C` is `p`-adically separated, then `f (a♯) = g (b♯)`.
* `WittVector.theta_natural`: naturality of Fontaine's map.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.2.
* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1.
-/

public section

open Ideal

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

namespace ModP

variable (p : ℕ)

/-- The reduction modulo `p` of a ring homomorphism `f : A →+* B`, as a ring homomorphism
`A ⧸ p → B ⧸ p`; it is well defined because `f` maps `p A` into `p B`. -/
noncomputable def map (f : A →+* B) : ModP A p →+* ModP B p :=
  quotientMap _ f <| span_le.mpr <| Set.singleton_subset_iff.mpr <| by
    rw [SetLike.mem_coe, mem_comap, map_natCast]
    exact mem_span_singleton_self _

@[simp]
theorem map_mk (f : A →+* B) (a : A) :
    map p f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) :=
  quotientMap_mk ..

@[simp]
theorem map_id : map p (RingHom.id A) = RingHom.id (ModP A p) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun a ↦ by simp

theorem map_comp (g : B →+* C) (f : A →+* B) : map p (g.comp f) = (map p g).comp (map p f) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun a ↦ by simp

end ModP

namespace PreTilt

variable (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : A)] [Fact ¬IsUnit (p : B)]
  [Fact ¬IsUnit (p : C)]

/-- The ring homomorphism of tilts `A♭ → B♭` induced by a ring homomorphism `f : A →+* B`: it
reduces every coordinate of a compatible system of `p`-th roots in `A ⧸ p` along `f`. -/
noncomputable def map (f : A →+* B) : PreTilt A p →+* PreTilt B p :=
  Perfection.map p (ModP.map p f)

variable {p}

@[simp]
theorem coeff_map (f : A →+* B) (x : PreTilt A p) (n : ℕ) :
    coeff n (map p f x) = ModP.map p f (coeff n x) := by
  rw [coeff_def, coeff_def]
  -- `PreTilt A p` is by definition `Perfection (ModP A p) p`, and `map p f` is `Perfection.map`
  exact Perfection.coeff_map p (ModP.map p f) x n

variable (p) in
@[simp]
theorem map_id : map p (RingHom.id A) = RingHom.id (PreTilt A p) :=
  RingHom.ext fun x ↦ ext fun n ↦ by simp

variable (p) in
theorem map_comp (g : B →+* C) (f : A →+* B) :
    map p (g.comp f) = (map p g).comp (map p f) :=
  RingHom.ext fun x ↦ ext fun n ↦ by simp [ModP.map_comp]

/-- **Naturality of the sharp map**: for `p`-adically complete `A` and `B`, a ring homomorphism
`f : A →+* B` satisfies `(PreTilt.map p f x)♯ = f (x♯)`. -/
@[simp]
theorem untilt_natural [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]
    (f : A →+* B) (x : PreTilt A p) : (map p f x).untilt = f x.untilt := by
  rw [← teichmuller₀_equivPerfection, ← teichmuller₀_equivPerfection]
  refine Eq.trans ?_ (Perfection.teichmuller₀_map (J := span {(p : B)}) f ?_ (equivPerfection x))
  · -- `PreTilt.map p f` is `Perfection.map` of `ModP.map p f`, an `Ideal.quotientMap`
    congr 1
    ext n
    simp [ModP.map]
  · rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton, map_natCast]

/-- If `a ∈ A♭` and `b ∈ B♭` have the same image in `C♭` under ring homomorphisms
`f : A →+* C` and `g : B →+* C`, and `C` is only `p`-adically separated, then
`f (a♯) = g (b♯)`: the images of the sharps of their `p ^ m`-th roots agree modulo `p`, so
`f (a♯)` and `g (b♯)` agree modulo `p ^ (m + 1)` for every `m`. When `C` is `p`-adically
complete this also follows from `PreTilt.untilt_natural`. -/
theorem map_untilt_eq_of_map_eq [IsAdicComplete (span {(p : A)}) A]
    [IsAdicComplete (span {(p : B)}) B] [IsHausdorff (span {(p : C)}) C] {f : A →+* C}
    {g : B →+* C} {a : PreTilt A p} {b : PreTilt B p} (hab : map p f a = map p g b) :
    f a.untilt = g b.untilt := by
  refine sub_eq_zero.mp <| IsHausdorff.haus (I := span {(p : C)}) inferInstance _ fun m ↦ ?_
  rw [TauCeti.sModEq_span_singleton_pow_iff, sub_zero]
  have hm : (p : C) ∣ f (untilt ((frobeniusEquiv (PreTilt A p) p).symm^[m] a)) -
      g (untilt ((frobeniusEquiv (PreTilt B p) p).symm^[m] b)) := by
    rw [← mem_span_singleton, ← Ideal.Quotient.eq, ← ModP.map_mk, ← ModP.map_mk,
      ← coeff_eq_mk_untilt_iterate, ← coeff_eq_mk_untilt_iterate, ← coeff_map, ← coeff_map, hab]
  have h := dvd_sub_pow_of_dvd_sub hm m
  rw [← map_pow f, ← map_pow g, untilt_iterate_frobeniusEquiv_symm_pow,
    untilt_iterate_frobeniusEquiv_symm_pow] at h
  exact (pow_dvd_pow _ m.le_succ).trans h

end PreTilt

namespace WittVector

variable {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : A)] [Fact ¬IsUnit (p : B)]
  [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]

/-- **Naturality of Fontaine's map**: for `p`-adically complete `A` and `B` and a ring
homomorphism `f : A →+* B`, `θ_B ∘ W(PreTilt.map p f) = f ∘ θ_A`. -/
theorem theta_natural_comp (f : A →+* B) :
    (fontaineTheta B p).comp (map (PreTilt.map p f)) = f.comp (fontaineTheta A p) :=
  ringHom_ext_teichmuller fun x ↦ by
    simp [map_teichmuller, fontaineTheta_teichmuller]

/-- **Naturality of Fontaine's map**, elementwise: `θ_B (W(PreTilt.map p f) w) = f (θ_A w)`. -/
@[simp]
theorem theta_natural (f : A →+* B) (w : WittVector p (PreTilt A p)) :
    fontaineTheta B p (map (PreTilt.map p f) w) = f (fontaineTheta A p w) :=
  congr($(theta_natural_comp f) w)

end WittVector
