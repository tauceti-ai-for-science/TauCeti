/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# The completion action on ideal-power-torsion modules

An `R`-module in which every element is killed by a power of `I` has a canonical action of
`AdicCompletion I R`. On an element killed by `I ^ n`, a completed scalar acts through its
residue modulo `I ^ n`. The hypothesis is membership of every element in
`Ideal.primaryComponent M I`. No finite generation or Noetherian hypothesis is needed.

`TauCeti.AdicCompletion.torsionModule` constructs this module structure. The residue formula
`AdicCompletion.torsion_smul_eq` characterizes its action. Every `R`-linear map
between such modules is linear for these completion actions, and restriction of scalars recovers
the original action of `R`.

For a finite `R`-module `N` and an ideal-power-torsion module `E`,
`TauCeti.AdicCompletion.torsionHomEquiv` identifies completion-linear maps
`AdicCompletion I N → E` with `R`-linear maps `N → E`, by restriction along `AdicCompletion.of`.
An `R`-linear map `f : N → E` has finitely generated image, hence is killed by a single power
`I ^ n`, and extends through `N ⧸ I ^ n • ⊤`; uniqueness holds because the completion of `N` is
spanned over the completion of `R` by the image of `N`. No Noetherian hypothesis is needed. For the
injective hull `E` of the residue field of a Noetherian local ring this is the completion
adjunction `Hom(N̂, E) ≅ Hom(N, E)` of Matlis duality, with completion-linear maps on the left.

The construction uses the compatible residues of Mathlib's `AdicCompletion`, formalized by
Judith Ludwig and Christian Merten, and the quotient actions on `Submodule.torsionBySet`.
For its role in Matlis duality, see the Stacks Project,
Section 47.7, Tag 08Z1.
-/

public section

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private def torsionActionAt (a : AdicCompletion I R) {n : ℕ} {x : M}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n)) : M :=
  ↑(evalₐ I n a • (⟨x, hx⟩ : Submodule.torsionBySet R M ↑(I ^ n)))

private theorem torsionActionAt_eq {a : AdicCompletion I R} {x : M} {n : ℕ} {r : R}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (ha : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r) :
    torsionActionAt a hx = r • x := by
  simp only [torsionActionAt, ha, Submodule.torsionBySet.mk_smul, Submodule.coe_smul_of_tower]

private theorem torsionActionAt_mono (a : AdicCompletion I R) {x : M} {n m : ℕ}
    (h : n ≤ m) (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (hy : x ∈ Submodule.torsionBySet R M ↑(I ^ m)) :
    torsionActionAt a hx = torsionActionAt a hy := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I m a)
  have hn : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r := by
    rw [← factor_evalₐ h a, ← hr, Ideal.Quotient.factor_mk]
  rw [torsionActionAt_eq hx hn, torsionActionAt_eq hy hr.symm]

variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

private def torsionAction (a : AdicCompletion I R) (x : M) : M :=
  torsionActionAt a ((Ideal.primaryComponent_mem M I x).mp (hM x)).choose_spec

private theorem torsionAction_eq (a : AdicCompletion I R) {x : M} {n : ℕ}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n)) :
    torsionAction hM a x = torsionActionAt a hx := by
  let h := (Ideal.primaryComponent_mem M I x).mp (hM x)
  let k := max n h.choose
  have hk : x ∈ Submodule.torsionBySet R M ↑(I ^ k) :=
    Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_left _ _) I hx
  have hchosen : x ∈ Submodule.torsionBySet R M ↑(I ^ h.choose) := h.choose_spec
  exact (torsionActionAt_mono a (Nat.le_max_right _ _) hchosen hk).trans
    (torsionActionAt_mono a (Nat.le_max_left _ _) hx hk).symm

end AdicCompletion

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

/-- The canonical module structure over the completion on a module whose elements are each
annihilated by a power of `I`. Use it with `letI := TauCeti.AdicCompletion.torsionModule hM`. -/
@[instance_reducible]
def torsionModule : Module (AdicCompletion I R) M where
  smul := torsionAction hM
  one_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 1 x = x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM 1 hn]
    simp [torsionActionAt]
  mul_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a * b) x = torsionAction hM a (torsionAction hM b x)
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    have hb : torsionAction hM b x ∈ Submodule.torsionBySet R M ↑(I ^ n) := by
      rw [torsionAction_eq hM b hn]
      exact (evalₐ I n b • (⟨x, hn⟩ : Submodule.torsionBySet R M ↑(I ^ n))).property
    rw [torsionAction_eq hM (a * b) hn, torsionAction_eq hM a hb]
    have hinner : (⟨torsionAction hM b x, hb⟩ : Submodule.torsionBySet R M ↑(I ^ n)) =
        evalₐ I n b • (⟨x, hn⟩ : Submodule.torsionBySet R M ↑(I ^ n)) :=
      Subtype.ext (torsionAction_eq hM b hn)
    simp only [torsionActionAt, map_mul, mul_smul, hinner]
  smul_zero a := by
    -- The scalar operation is the action defined above.
    change torsionAction hM a 0 = 0
    rw [torsionAction_eq hM a (Submodule.zero_mem (Submodule.torsionBySet R M ↑(I ^ 0)))]
    simp only [torsionActionAt, (Submodule.mk_eq_zero _ _).mpr rfl, smul_zero,
      Submodule.coe_zero]
  smul_add a x y := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM a (x + y) = torsionAction hM a x + torsionAction hM a y
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    obtain ⟨m, hm⟩ := (Ideal.primaryComponent_mem M I y).mp (hM y)
    have hx : x ∈ Submodule.torsionBySet R M ↑(I ^ (max n m)) :=
      Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_left _ _) I hn
    have hy : y ∈ Submodule.torsionBySet R M ↑(I ^ (max n m)) :=
      Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_right _ _) I hm
    rw [torsionAction_eq hM a (Submodule.add_mem _ hx hy), torsionAction_eq hM a hx,
      torsionAction_eq hM a hy]
    have hxy : (⟨x + y, Submodule.add_mem _ hx hy⟩ :
        Submodule.torsionBySet R M ↑(I ^ (max n m))) = ⟨x, hx⟩ + ⟨y, hy⟩ :=
      Subtype.ext (by simp only [Submodule.coe_add])
    simp only [torsionActionAt, hxy, smul_add, Submodule.coe_add]
  add_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a + b) x = torsionAction hM a x + torsionAction hM b x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM (a + b) hn, torsionAction_eq hM a hn, torsionAction_eq hM b hn]
    simp [torsionActionAt, add_smul]
  zero_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 0 x = 0
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM 0 hn]
    simp [torsionActionAt]

end TauCeti.AdicCompletion

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A completed scalar acts on an element killed by `I ^ n` through its residue modulo
`I ^ n`. This formula permits any representative of the residue. -/
theorem torsion_smul_eq (a : AdicCompletion I R)
    (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I) (x : M) {n : ℕ} (r : R)
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (ha : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r) :
    letI := TauCeti.AdicCompletion.torsionModule hM
    a • x = r • x := by
  exact (torsionAction_eq hM a hx).trans (torsionActionAt_eq hx ha)

end AdicCompletion

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

/-- The canonical completion action extends the scalar tower from `R`. -/
instance torsionModule_isScalarTower :
    letI := torsionModule hM
    IsScalarTower R (AdicCompletion I R) M := by
  let := torsionModule hM
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
  exact _root_.AdicCompletion.torsion_smul_eq _ hM x r hn
    (_root_.AdicCompletion.evalₐ_of I n r)

end TauCeti.AdicCompletion

namespace LinearMap

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)
variable (hN : ∀ y : N, y ∈ Ideal.primaryComponent N I)

/-- An `R`-linear map between ideal-power-torsion modules commutes with the canonical
completion actions. -/
@[simp]
theorem map_adicCompletion_smul (f : M →ₗ[R] N) (a : AdicCompletion I R) (x : M) :
    letI := TauCeti.AdicCompletion.torsionModule hM
    letI := TauCeti.AdicCompletion.torsionModule hN
    f (a • x) = a • f x := by
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
  have hfx : f x ∈ Submodule.torsionBySet R N ↑(I ^ n) := by
    rw [Submodule.mem_torsionBySet_iff] at hn ⊢
    intro r
    rw [← f.map_smul, hn r, f.map_zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [a.torsion_smul_eq hM x r hn hr.symm,
    a.torsion_smul_eq hN (f x) r hfx hr.symm, f.map_smul]

end LinearMap

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)
variable (hN : ∀ y : N, y ∈ Ideal.primaryComponent N I)

/-- Restriction of scalars identifies linear maps for the canonical completion actions with
`R`-linear maps between ideal-power-torsion modules. -/
def torsionRestrictScalarsEquiv :
    letI := TauCeti.AdicCompletion.torsionModule hM
    letI := TauCeti.AdicCompletion.torsionModule hN
    (M →ₗ[AdicCompletion I R] N) ≃ₗ[R] (M →ₗ[R] N) := by
  letI := TauCeti.AdicCompletion.torsionModule hM
  letI := TauCeti.AdicCompletion.torsionModule hN
  exact
    { LinearMap.restrictScalarsₗ R (AdicCompletion I R) M N R with
      invFun := fun f ↦
        { toFun := f
          map_add' := f.map_add
          map_smul' := f.map_adicCompletion_smul hM hN }
      left_inv := fun f ↦ by ext; rfl
      right_inv := fun f ↦ by ext; rfl }

/-- The comparison of Hom modules is restriction of scalars. -/
@[simp]
theorem torsionRestrictScalarsEquiv_apply
    (f : letI := TauCeti.AdicCompletion.torsionModule hM
         letI := TauCeti.AdicCompletion.torsionModule hN
         M →ₗ[AdicCompletion I R] N) (x : M) :
    torsionRestrictScalarsEquiv hM hN f x = f x := (rfl)

/-- Extending a linear map to the canonical completion actions preserves its values. -/
@[simp]
theorem torsionRestrictScalarsEquiv_symm_apply (f : M →ₗ[R] N) (x : M) :
    (torsionRestrictScalarsEquiv hM hN).symm f x = f x := (rfl)

end TauCeti.AdicCompletion

/-! ### Maps out of the completion of a finite module -/

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {N E : Type*} [AddCommGroup N] [Module R N] [AddCommGroup E] [Module R E]
variable (hE : ∀ y : E, y ∈ Ideal.primaryComponent E I)

include hE in
/-- The image of a finite module in an ideal-power-torsion module is killed by one power. -/
private theorem exists_range_le_torsionBySet [Module.Finite R N] (f : N →ₗ[R] E) :
    ∃ n, LinearMap.range f ≤ Submodule.torsionBySet R E ↑(I ^ n) :=
  I.exists_le_torsionBySet_pow_of_le_primaryComponent
    (LinearMap.range_eq_map f ▸ Module.Finite.fg_top.map f) fun y _ ↦ hE y

/-- A linear map whose range is killed by `I ^ n` kills `I ^ n • ⊤`. -/
private theorem pow_smul_top_le_ker {f : N →ₗ[R] E} {n : ℕ}
    (hn : LinearMap.range f ≤ Submodule.torsionBySet R E ↑(I ^ n)) :
    I ^ n • (⊤ : Submodule R N) ≤ LinearMap.ker f := by
  refine Submodule.smul_le.mpr fun r hr x _ ↦ ?_
  rw [LinearMap.mem_ker, map_smul]
  exact (Submodule.mem_torsionBySet_iff _ _).mp (hn ⟨x, rfl⟩) ⟨r, hr⟩

/-- The extension of `f` to the completion through `N ⧸ I ^ n • ⊤`, for a power `I ^ n` killing
the range of `f`. -/
private def liftAux (f : N →ₗ[R] E) {n : ℕ}
    (hn : LinearMap.range f ≤ Submodule.torsionBySet R E ↑(I ^ n)) :
    letI := torsionModule hE
    AdicCompletion I N →ₗ[AdicCompletion I R] E :=
  letI := torsionModule hE
  { toFun := (I ^ n • ⊤ : Submodule R N).liftQ f (pow_smul_top_le_ker hn) ∘ₗ eval I N n
    map_add' := map_add _
    map_smul' := fun a x ↦ by
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n a)
      have hx : (I ^ n • ⊤ : Submodule R N).liftQ f (pow_smul_top_le_ker hn) (eval I N n x) ∈
          Submodule.torsionBySet R E ↑(I ^ n) := by
        obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _ (eval I N n x)
        rw [← hy]
        exact hn ⟨y, rfl⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, RingHom.id_apply]
      -- Both sides become the action of a representative `r` of the residue of `a` modulo `I ^ n`:
      -- on the right by the residue formula, on the left through the quotient `N ⧸ I ^ n • ⊤`.
      rw [torsion_smul_eq a hE _ r hx hr.symm, ← map_smul, eval_apply, smul_eval,
        val_smul_eq_evalₐ_smul, ← hr, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul,
        ← eval_apply] }

/-- The extension `liftAux` restricts to `f` along `AdicCompletion.of`. -/
private theorem liftAux_of (f : N →ₗ[R] E) {n : ℕ}
    (hn : LinearMap.range f ≤ Submodule.torsionBySet R E ↑(I ^ n)) (x : N) :
    liftAux hE f hn (of I N x) = f x := by
  simp [liftAux]

/-- **The completion adjunction for ideal-power-torsion modules.** For a finite module `N` and an
`I`-power-torsion module `E`, with the canonical completion action, restriction along
`AdicCompletion.of` identifies completion-linear maps `AdicCompletion I N → E` with `R`-linear
maps `N → E`. No Noetherian hypothesis is needed. Applied to the injective hull of the residue
field of a Noetherian local ring, this is the adjunction of Matlis duality. -/
def torsionHomEquiv [Module.Finite R N] :
    letI := torsionModule hE
    (AdicCompletion I N →ₗ[AdicCompletion I R] E) ≃ₗ[AdicCompletion I R] (N →ₗ[R] E) := by
  letI := torsionModule hE
  refine LinearEquiv.ofBijective
    { toFun := fun φ ↦ φ.restrictScalars R ∘ₗ of I N
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } ⟨fun φ ψ h ↦ ?_, fun f ↦ ?_⟩
  · exact map_ext_of_finite I fun x ↦ LinearMap.congr_fun h x
  · obtain ⟨n, hn⟩ := exists_range_le_torsionBySet hE f
    exact ⟨liftAux hE f hn, LinearMap.ext (liftAux_of hE f hn)⟩

/-- The adjunction restricts a completion-linear map along `AdicCompletion.of`. -/
@[simp]
theorem torsionHomEquiv_apply [Module.Finite R N]
    (φ : letI := torsionModule hE; AdicCompletion I N →ₗ[AdicCompletion I R] E) (x : N) :
    torsionHomEquiv hE φ x = φ (of I N x) := (rfl)

/-- The completion-linear extension of `f` agrees with `f` on the image of `N`. -/
@[simp]
theorem torsionHomEquiv_symm_apply_of [Module.Finite R N] (f : N →ₗ[R] E) (x : N) :
    (torsionHomEquiv hE).symm f (of I N x) = f x := by
  rw [← torsionHomEquiv_apply hE, LinearEquiv.apply_symm_apply]

/-- The completion-linear extension of `f` at a point is the value of `f` at any element of `N`
congruent to it modulo `I ^ n`, for a power `I ^ n` killing the range of `f`. -/
theorem torsionHomEquiv_symm_apply_eq [Module.Finite R N] (f : N →ₗ[R] E) {n : ℕ}
    (hn : LinearMap.range f ≤ Submodule.torsionBySet R E ↑(I ^ n))
    (x : AdicCompletion I N) (y : N) (hxy : eval I N n x = Submodule.Quotient.mk y) :
    (torsionHomEquiv hE).symm f x = f y := by
  have : (torsionHomEquiv hE).symm f = liftAux hE f hn :=
    (torsionHomEquiv hE).symm_apply_eq.mpr (LinearMap.ext fun x ↦ (liftAux_of hE f hn x).symm)
  rw [eval_apply] at hxy
  simp [this, liftAux, hxy]

/-- The adjunction is natural in the finite module. -/
theorem torsionHomEquiv_comp_map {N' : Type*} [AddCommGroup N'] [Module R N'] [Module.Finite R N]
    [Module.Finite R N']
    (φ : letI := torsionModule hE; AdicCompletion I N →ₗ[AdicCompletion I R] E)
    (g : N' →ₗ[R] N) :
    torsionHomEquiv hE (φ ∘ₗ map I g) = torsionHomEquiv hE φ ∘ₗ g := by
  ext x
  simp [map_of]

end TauCeti.AdicCompletion
