/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Pairing
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Associator
import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Homotopy

/-!
# Concatenation of the chain bimodules of Moore paths

For points `a`, `b` and `c` of a space `B`, concatenation of Moore paths
`P_{a→b} B × P_{b→c} B → P_{a→c} B` is balanced over the loops at `b` and commutes with the
loops at `a` acting in front and those at `c` acting behind. On normalized cubical chains it
therefore induces a morphism of differential graded `(C_*(Ω_a B), C_*(Ω_c B))`-bimodules

`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) → C_*(P_{a→c} B)`,

sending `σ ⊗ τ` to the concatenation of the cubes `σ` and `τ`. Since concatenation of Moore paths
is strictly associative, so is this composition of bimodules, through the associator of tensor
products.

The chain bimodule `C_*(P_{b→b'} B)` changes the basepoint of a DG local system from `b` to `b'`,
by derived tensor product. The composition morphism relates two successive changes of basepoint,
along paths from `a` to `b` and from `b` to `c`, to the change along paths from `a` to `c`.

When `a` and `b` are joined by a Moore path `γ`, the composition is a quasi-isomorphism. Its
homotopy inverse is `y ↦ [γ] ⊗ γ⁻¹ y`, for the `0`-chain `[γ]` of `γ`. One composite prepends
`γ` after `γ⁻¹`; the other is `m ⊗ n ↦ γ γ⁻¹ m ⊗ n`, by moving the loop chain `γ⁻¹ m` across
the tensor product. Both are homotopic to the identity through the homotopies of
`TauCeti.pathChainPrependHomotopy`, which are linear over the loop chains and so can be tensored
with the identity. In particular `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→a} B)` is
quasi-isomorphic to the chains on the loops at `a`: this is the comparison through which the
basepoint changes along `a → b` and back are shown to be mutually inverse.

## Main definitions

* `TauCeti.pathChainConcat B a b c R`: the composition morphism
  `C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)`.

## Main results

* `TauCeti.pathChainConcat_tmul`: on pure tensors, the composition is the pairing of cubical
  chains induced by concatenation of Moore paths.
* `TauCeti.pathChainConcat_tmul_ofCube`: the composition concatenates cubes pointwise.
* `TauCeti.pathChainConcat_assoc`: the composition is associative.
* `TauCeti.pathChainConcat_tmul_point`: composing with the `0`-chain of a path is prepending it.
* `TauCeti.isQuasiIso_pathChainConcat`: if `a` and `b` are joined by a Moore path, the composition
  is a quasi-isomorphism.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

open NormalizedCubicalChain BalancedTensorProduct

universe u v

variable (B : Type u) [TopologicalSpace B] (a b c d : B) (R : Type v) [CommRing R]

/-- Concatenation of Moore paths, as a continuous map on pairs. -/
private def concatMap :
    C(MoorePathBetween B a b × MoorePathBetween B b c, MoorePathBetween B a c) :=
  ⟨fun p ↦ p.1.trans p.2, MoorePathBetween.continuous_trans⟩

/-- **Concatenation of the chain bimodules of Moore paths**: the morphism of DG
`(C_*(Ω_a B), C_*(Ω_c B))`-bimodules
`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) ⟶ C_*(P_{a→c} B)` induced by concatenation. -/
def pathChainConcat :
    DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R) ⟶
      pathChainBimodule B a c R :=
  cubicalChainTensorHom (concatMap B a b c)
    (fun _ _ _ ↦ MoorePathBetween.ext (by simp [concatMap, MoorePath.trans_assoc]))
    (fun _ _ _ ↦ MoorePathBetween.ext (by simp [concatMap, MoorePath.trans_assoc]))
    (fun _ _ _ ↦ MoorePathBetween.ext (by simp [concatMap, MoorePath.trans_assoc]))

variable {B a b c d R}

/-- **The composition is the concatenation pairing**: on a pure tensor `m ⊗ n`, it is the
pairing of cubical chains induced by concatenation of Moore paths. -/
@[simp]
theorem pathChainConcat_tmul
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) m n) =
      cubicalChainPairing (MooreLoopSpace B b) (MooreLoopSpace B c) R
        ⟨fun p ↦ p.1.trans p.2, MoorePathBetween.continuous_trans⟩ m n :=
  cubicalChainTensorHom_tmul _ _ _ _ m n

/-- **The composition concatenates cubes**: on cubes `σ` of paths from `a` to `b` and `τ` of
paths from `b` to `c`, it is the cube of the concatenations `σ(s).trans τ(t)`. -/
theorem pathChainConcat_tmul_ofCube {p q : ℕ} (σ : SingularCube (MoorePathBetween B a b) p)
    (τ : SingularCube (MoorePathBetween B b c) q) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R)
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p
          (ofCube _ R σ))
        (cubicalChainModuleLof (MoorePathBetween B b c) (MooreLoopSpace B c) R q
          (ofCube _ R τ))) =
      cubicalChainModuleLof (MoorePathBetween B a c) (MooreLoopSpace B c) R (p + q)
        (ofCube _ R ⟨fun x ↦ (σ fun i ↦ x (Fin.castAdd q i)).trans (τ fun j ↦ x (Fin.natAdd p j)),
          by fun_prop⟩) := by
  rw [pathChainConcat_tmul, cubicalChainPairing_lof_lof, crossProduct_ofCube, map_ofCube]
  congr 2
  refine ContinuousMap.ext fun x ↦ ?_
  simp only [ContinuousMap.comp_apply, SingularCube.crossProduct_apply, ContinuousMap.coe_mk]

/-- **The composition of path bimodules is associative**: composing paths from `a` to `b`, from
`b` to `c` and from `c` to `d` in either order gives the same chains, through the associator of
tensor products. -/
theorem pathChainConcat_assoc :
    DGBimoduleCat.tensorMap (pathChainConcat B a b c R) (𝟙 (pathChainBimodule B c d R)) ≫
        pathChainConcat B a c d R =
      (DGBimoduleCat.tensorAssoc _ _ _).hom ≫
        DGBimoduleCat.tensorMap (𝟙 (pathChainBimodule B a b R)) (pathChainConcat B b c d R) ≫
          pathChainConcat B a b d R := by
  apply DGBimoduleCat.tensorObj_hom_ext
  intro z o
  induction z using BalancedTensorProduct.induction_on with
  | ht m n =>
    -- `simp` does not match the generic lemmas about bundled morphisms on these concrete
    -- bimodules, which are abbreviations; rewrite with them instead.
    rw [DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply,
      DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.tensorAssoc_hom_tmul,
      DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply, DGBimoduleCat.id_apply, pathChainConcat,
      pathChainConcat, pathChainConcat, pathChainConcat, cubicalChainTensorHom_tmul,
      cubicalChainTensorHom_tmul, cubicalChainTensorHom_tmul, cubicalChainTensorHom_tmul]
    exact cubicalChainPairing_assoc (f := concatMap B a b c) (g := concatMap B a c d)
      (f' := concatMap B b c d) (g' := concatMap B a b d)
      (fun _ _ _ ↦ MoorePathBetween.trans_assoc _ _ _) m n o
  | ha x y hx hy => simp only [add_tmul, map_add, hx, hy]


/-! ### Concatenation is a quasi-isomorphism -/

section QuasiIso

/-- **Concatenating with a point chain is prepending**: the composition sends `[γ] ⊗ n`, for the
`0`-chain `[γ]` of a path `γ` from `a` to `b`, to the chain `n` with `γ` prepended. -/
theorem pathChainConcat_tmul_point (γ : MoorePathBetween B a b)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R)
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
          (ofCube _ R (SingularCube.point γ))) n) =
      pathChainPrepend R γ c n := by
  rw [pathChainConcat_tmul, cubicalChainPairing_lof_point, pathChainPrepend_apply]
  exact congrArg (cubicalChainModuleLinearMap R · n) (ContinuousMap.ext fun _ ↦ by simp)

/-- The loop `γ⁻¹ ⋆ δ` at `b`, for a path `δ` from `a` to `b`. -/
private noncomputable def symmTransLoop (γ : MoorePathBetween B a b) :
    C(MoorePathBetween B a b, MooreLoopSpace B b) :=
  ((MoorePathBetween.loopHomeomorph b).symm : C(MoorePathBetween B b b, MooreLoopSpace B b)).comp
    (γ.symm.prepend b)

/-- The balancing step of the homotopy inverse: `[γ] ⊗ γ⁻¹ (m ⋆ n) = γ γ⁻¹ m ⊗ n`, by moving the
loop chain `γ⁻¹ ⋆ m` across the tensor product over the loops at `b`. -/
private theorem tmul_point_prepend_symm_pathChainConcat (γ : MoorePathBetween B a b)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    tmul R (loopChainAlgebra B b R)
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
          (ofCube _ R (SingularCube.point γ)))
        (pathChainPrepend R γ.symm c (pathChainConcat B a b c R (tmul R _ m n))) =
      tmul R (loopChainAlgebra B b R)
        (pathChainPrepend R γ b (pathChainPrepend R γ.symm b m)) n := by
  induction m using cubicalChainModule.induction_on with
  | add m m' hm hm' => simp only [add_tmul, map_add, tmul_add, hm, hm']
  | lof p x =>
    induction n using cubicalChainModule.induction_on with
    | add n n' hn hn' => simp only [tmul_add, map_add, hn, hn']
    | lof q y =>
      -- The chain `γ⁻¹ ⋆ (x ⋆ y)` is the loop chain `γ⁻¹ ⋆ x` acting on `y`.
      have h1 : cubicalChainModuleLof (MoorePathBetween B b c) (MooreLoopSpace B c) R (p + q)
            (map R ((γ.symm.prepend c).comp
              ⟨fun p ↦ p.1.trans p.2, MoorePathBetween.continuous_trans⟩)
              (p + q) (crossProduct _ _ R p q x y)) =
          cubicalChainLof (MooreLoopSpace B b) R p (map R (symmTransLoop γ) p x) •
            cubicalChainModuleLof (MoorePathBetween B b c) (MooreLoopSpace B c) R q y := by
        rw [lof_smul_cubicalChainModuleLof, leftAct_def]
        congr 1
        conv_rhs => rw [← LinearMap.id_apply (R := R) y, ← NormalizedCubicalChain.map_id,
          ← map_crossProduct, ← LinearMap.comp_apply, ← NormalizedCubicalChain.map_comp]
        congr 2
        refine ContinuousMap.ext fun ⟨δ, ε⟩ ↦ MoorePathBetween.ext ?_
        simp [symmTransLoop, MoorePath.trans_assoc]
      -- The loop chain `γ⁻¹ ⋆ x` acting on `[γ]` is the chain `γ ⋆ γ⁻¹ ⋆ x`.
      have h2 : op (cubicalChainLof (MooreLoopSpace B b) R p (map R (symmTransLoop γ) p x)) •
            cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
              (ofCube _ R (SingularCube.point γ)) =
          pathChainPrepend R γ b (pathChainPrepend R γ.symm b
            (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p x)) := by
        rw [op_lof_smul_cubicalChainModuleLof, act_def,
          ← cubicalChainModuleLof_cast (Nat.zero_add p), ← map_cast, crossProduct_point_left,
          pathChainPrepend_apply, pathChainPrepend_apply, cubicalChainModuleLinearMap_lof,
          cubicalChainModuleLinearMap_lof]
        simp only [← LinearMap.comp_apply, ← NormalizedCubicalChain.map_comp]
        congr 3
        refine ContinuousMap.ext fun δ ↦ MoorePathBetween.ext ?_
        simp [symmTransLoop]
      rw [pathChainConcat_tmul, cubicalChainPairing_lof_lof, pathChainPrepend_apply,
        cubicalChainModuleLinearMap_lof, ← LinearMap.comp_apply (map R (γ.symm.prepend c) (p + q)),
        ← NormalizedCubicalChain.map_comp, h1, ← balance, h2]

/-- The homotopy inverse `y ↦ [γ] ⊗ γ⁻¹ y` of concatenation. -/
private noncomputable def concatInv (γ : MoorePathBetween B a b) (c : B) :
    cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R →ₗ[R]
      BalancedTensorProduct R (loopChainAlgebra B b R)
        (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
        (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :=
  mk R (loopChainAlgebra B b R)
      (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
        (ofCube _ R (SingularCube.point γ))) ∘ₗ
    (pathChainPrepend R γ.symm c).toLinearMap.restrictScalars R

private theorem concatInv_apply (γ : MoorePathBetween B a b) (c : B)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    concatInv γ c y = tmul R (loopChainAlgebra B b R)
      (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
        (ofCube _ R (SingularCube.point γ))) (pathChainPrepend R γ.symm c y) := by
  simp only [concatInv, LinearMap.comp_apply, LinearMap.restrictScalars_apply, mk_apply,
    DGRightModuleHom.coe_toLinearMap]

/-- The homotopy `h ⊗ 1` on the tensor product, for the module-linear homotopy `h` of
`pathChainPrependHomotopy`. -/
private noncomputable def concatHomotopy (γ : MoorePathBetween B a b) (c : B) :
    BalancedTensorProduct R (loopChainAlgebra B b R)
        (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
        (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) →ₗ[R]
      BalancedTensorProduct R (loopChainAlgebra B b R)
        (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
        (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :=
  BalancedTensorProduct.map ((pathChainPrependHomotopy R γ b).restrictScalars R) LinearMap.id
    (fun x m ↦ (pathChainPrependHomotopy R γ b).map_smul (op x) m) (fun _ _ ↦ rfl)

private theorem concatHomotopy_tmul (γ : MoorePathBetween B a b) (c : B)
    (m : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    concatHomotopy γ c (tmul R _ m n) = tmul R _ (pathChainPrependHomotopy R γ b m) n := by
  exact BalancedTensorProduct.map_tmul _ _ _ _ m n

/-- The homotopy inverse commutes with the differentials, since the point chain is a cycle of
degree zero. -/
private theorem differential_concatInv (γ : MoorePathBetween B a b) (c : B)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    (DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R)).differential
        (concatInv γ c y) =
      concatInv γ c ((pathChainLocalSystem R a c).differential y) := by
  have hpt := cubicalChainModuleLof_mem (G := MooreLoopSpace B b)
    (ofCube (MoorePathBetween B a b) R (SingularCube.point γ))
  rw [Nat.cast_zero, neg_zero] at hpt
  rw [concatInv_apply, concatInv_apply, DGBimoduleCat.tensorObj_differential_tmul hpt]
  have hd : (pathChainBimodule B a b R).differential
      (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
        (ofCube _ R (SingularCube.point γ))) = 0 :=
    cubicalChainModuleDifferential_lof_zero _
  rw [hd, zero_tmul, zero_add, Int.negOnePow_zero, one_smul]
  exact congrArg (tmul R _ _) (DGRightModuleCat.map_d (pathChainPrepend R γ.symm c) y)

/-- Concatenation after the homotopy inverse is prepending `γ` after `γ⁻¹`, which is homotopic to
the identity. -/
private theorem pathChainConcat_concatInv (γ : MoorePathBetween B a b) (c : B)
    (y : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    pathChainConcat B a b c R (concatInv γ c y) =
      y + (pathChainLocalSystem R a c).differential (pathChainPrependHomotopy R γ c y) +
        pathChainPrependHomotopy R γ c ((pathChainLocalSystem R a c).differential y) := by
  rw [concatInv_apply, pathChainConcat_tmul_point, add_assoc]
  exact sub_eq_iff_eq_add'.mp (pathChainPrependHomotopy_spec γ c y).symm

/-- The homotopy inverse after concatenation, on a pure tensor with homogeneous first factor. -/
private theorem concatInv_pathChainConcat_tmul_lof (γ : MoorePathBetween B a b) (c : B) (p : ℕ)
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R p)
    (n : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    concatInv γ c (pathChainConcat B a b c R (tmul R _
        (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p x) n)) =
      tmul R _ (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p x) n +
        (DGBimoduleCat.tensorObj (pathChainBimodule B a b R)
          (pathChainBimodule B b c R)).differential (concatHomotopy γ c (tmul R _
            (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p x) n)) +
        concatHomotopy γ c ((DGBimoduleCat.tensorObj (pathChainBimodule B a b R)
          (pathChainBimodule B b c R)).differential (tmul R _
            (cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R p x) n)) := by
  -- This is the identity `f ⊗ 1 = d (h ⊗ 1) + (h ⊗ 1) d + 1` of
  -- `BalancedTensorProduct.map_eq_leibnizDifferential_comp_map_add_map_comp_add` for `f = γ γ⁻¹`,
  -- computed on a pure tensor: unifying that lemma's Leibniz hypotheses with these chain modules
  -- exceeds the default heartbeat budget.
  have hx := cubicalChainModuleLof_mem (G := MooreLoopSpace B b) x
  have hkx := pathChainPrependHomotopy_mem γ b hx
  rw [concatInv_apply, tmul_point_prepend_symm_pathChainConcat, concatHomotopy_tmul,
    DGBimoduleCat.tensorObj_differential_tmul hkx, DGBimoduleCat.tensorObj_differential_tmul hx,
    Units.smul_def, Units.smul_def, map_add, map_zsmul, concatHomotopy_tmul, concatHomotopy_tmul,
    sub_eq_iff_eq_add'.mp (pathChainPrependHomotopy_spec γ b _).symm, add_tmul, add_tmul,
    Int.negOnePow_sub, Int.negOnePow_one, mul_neg, _root_.mul_one, Units.val_neg, neg_smul]
  abel

/-- The homotopy inverse after concatenation is homotopic to the identity. -/
private theorem concatInv_pathChainConcat (γ : MoorePathBetween B a b) (c : B)
    (z : DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R)) :
    concatInv γ c (pathChainConcat B a b c R z) =
      z + (DGBimoduleCat.tensorObj (pathChainBimodule B a b R)
          (pathChainBimodule B b c R)).differential (concatHomotopy γ c z) +
        concatHomotopy γ c ((DGBimoduleCat.tensorObj (pathChainBimodule B a b R)
          (pathChainBimodule B b c R)).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, map_add, map_add, map_add]
    abel
  | ht m n =>
    induction m using cubicalChainModule.induction_on with
    | lof p x => exact concatInv_pathChainConcat_tmul_lof γ c p x n
    | add m m' hm hm' =>
      rw [add_tmul, map_add, map_add, hm, hm', map_add, map_add, map_add, map_add]
      abel

/-- **Concatenation of the chain bimodules of Moore paths is a quasi-isomorphism**: if there is a
Moore path from `a` to `b`, then the composition
`C_*(P_{a→b} B) ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B) → C_*(P_{a→c} B)` induces a bijection on
cohomology. For `c = a` the target is the chains on the Moore paths from `a` to `a`, that is on
the loops at `a`. -/
theorem isQuasiIso_pathChainConcat (h : Nonempty (MoorePathBetween B a b)) :
    DGRightModuleCat.IsQuasiIso
      (DGBimoduleCat.forgetToRightModuleCat.map (pathChainConcat B a b c R)) := by
  obtain ⟨γ⟩ := h
  -- Instance search does not see the bundled actions of the tensor product through the
  -- abbreviation `tensorObj`, so they are supplied explicitly.
  let T := DGBimoduleCat.tensorObj (pathChainBimodule B a b R) (pathChainBimodule B b c R)
  let := T.moduleOp
  have := T.scalarTower
  have := T.gradedSMul
  exact DGRightModuleHom.isQuasiIso_of_homotopyInverse (pathChainConcat B a b c R).val
    (concatInv γ c) (concatHomotopy γ c) ((pathChainPrependHomotopy R γ c).restrictScalars R)
    (differential_concatInv γ c) (concatInv_pathChainConcat γ c) (pathChainConcat_concatInv γ c)

end QuasiIso

end TauCeti

end
