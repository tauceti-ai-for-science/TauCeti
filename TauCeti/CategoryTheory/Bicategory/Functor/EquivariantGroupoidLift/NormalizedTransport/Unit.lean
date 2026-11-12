/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Normalized

/-!
# A lift maps to the reconstruction of its normalized transport

Let `L` be an equivariant groupoid lift with joint pseudofunctor `F` and fiber comparisons
`e_p : F (p, ⋆) ≌ C p`. Normalizing `L` and reconstructing gives the lift
`L.normalizedTransport.toLift`. Its joint pseudofunctor lives on the prescribed fibers and sends
`(g, a)` to `T_a ⋙ E_g`, where `E_g = e_p⁻¹ ⋙ F (g, 1) ⋙ e_q`, and its fiber comparisons are
identities. This file constructs the morphism of lifts

`L.normalizedTransportToLiftHom : L.Hom L.normalizedTransport.toLift`

whose joint strong transformation has the fiber comparisons `e_p` as components. Its naturality
isomorphism at `(g, a)` is `F (g, a) ⋙ e_q ≅ e_p ⋙ T_a ⋙ E_g`. It splits `(g, a)` as
`(𝟙 p, a) ≫ (g, 1)`, and combines the naturality isomorphism `F (𝟙 p, a) ⋙ e_p ≅ e_p ⋙ T_a` of the
fiber comparison with the isomorphism `jointMapTransportIso g : F (g, 1) ⋙ e_q ≅ e_p ⋙ E_g`
induced by the unit of `e_p`.
Compatibility with the joint compositors combines the composition axiom of the fiber comparison,
the mixed coherence of transport and associativity of the joint compositors.

This morphism compares a lift with normalization followed by reconstruction, in the direction
opposite to the counit `normalizationCounitEquiv`; it is the component at `L` of the unit of that
comparison.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.jointNormalizedTransportIso`: the isomorphism
  `F (g, a) ⋙ e_q ≅ e_p ⋙ T_a ⋙ E_g`, with its compatibility with the unit and composition
  comparisons of the two joint pseudofunctors;
* `TauCeti.EquivariantGroupoidLift.normalizedTransportJointHom`: the resulting strong
  transformation from `L.joint` to `L.normalizedTransport.joint`;
* `TauCeti.EquivariantGroupoidLift.normalizedTransportToLiftHom`: the morphism of lifts
  `L ⟶ L.normalizedTransport.toLift`, whose fiber isomorphisms are right unitors.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: strong transformations,
  modifications and biequivalences.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (L : EquivariantGroupoidLift Γ actions)

/-- The comparison `F (g, a) ⋙ e_q ≅ e_p ⋙ T_a ⋙ E_g` of the joint functor of `L` at `(g, a)`
with the joint functor of its normalized transport. It splits `(g, a)` as `(𝟙 p, a) ≫ (g, 1)`, and
combines the naturality isomorphism `F (𝟙 p, a) ⋙ e_p ≅ e_p ⋙ T_a` of the fiber comparison with
`jointMapTransportIso g`. -/
noncomputable def jointNormalizedTransportIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) :
    (L.joint.map (g ×ₘ a).toLoc).toFunctor ⋙ (L.fiberEquivalence q).functor ≅
      (L.fiberEquivalence p).functor ⋙ act actions p a ⋙ L.transport g :=
  Functor.isoWhiskerRight (Cat.Hom.toNatIso (L.joint.mapComp' (𝟙 p ×ₘ a).toLoc
      (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc (by rw [← Quiver.Hom.comp_toLoc]; simp)))
      (L.fiberEquivalence q).functor ≪≫
    Functor.isoWhiskerLeft (L.jointAct p a) (L.jointMapTransportIso g) ≪≫
    Functor.isoWhiskerRight (L.comparisonNaturality p a) (L.transport g)

@[simp]
lemma jointNormalizedTransportIso_hom_app {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber p) :
    (L.jointNormalizedTransportIso g a).hom.app Y =
      (L.fiberEquivalence q).functor.map ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc
          (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
          (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app Y) ≫
        (L.jointMapTransportIso g).hom.app ((L.jointAct p a).obj Y) ≫
          (L.transport g).map ((L.comparisonNaturality p a).hom.app Y) :=
  (rfl)

@[simp]
lemma jointNormalizedTransportIso_inv_app {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber p) :
    (L.jointNormalizedTransportIso g a).inv.app Y =
      (L.transport g).map ((L.comparisonNaturality p a).inv.app Y) ≫
        (L.jointMapTransportIso g).inv.app ((L.jointAct p a).obj Y) ≫
          (L.fiberEquivalence q).functor.map ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc
            (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
            (by rw [← Quiver.Hom.comp_toLoc]; simp)).inv.toNatTrans.app Y) := by
  -- The inverse of a threefold composite of isomorphisms is bracketed to the left.
  refine Eq.trans ?_ (Category.assoc _ _ _)
  rfl

/-- At an identity arrow, `jointNormalizedTransportIso` intertwines the unit comparisons of the
joint functors of `L` and of its normalized transport. -/
@[reassoc]
lemma jointNormalizedTransportIso_hom_app_comp_jointId_hom_app (p : Γ) (Y : L.jointFiber p) :
    (L.jointNormalizedTransportIso (𝟙 p) (𝟙 (SingleObj.star H))).hom.app Y ≫
        (L.normalizedTransport.jointId (p, SingleObj.star H)).hom.app
          ((L.fiberEquivalence p).functor.obj Y) =
      (L.fiberEquivalence p).functor.map ((L.jointMapId p).hom.app Y) := by
  rw [NormalizedTransport.jointId_hom_app]
  -- The unit comparison of the normalized transport is `E_(𝟙 p)` of the unit comparison of the
  -- action followed by `transportId`; state this with the transport of `L` itself.
  suffices key : (L.jointNormalizedTransportIso (𝟙 p) (𝟙 (SingleObj.star H))).hom.app Y ≫
      (L.transport (𝟙 p)).map ((actId actions p).hom.app ((L.fiberEquivalence p).functor.obj Y)) ≫
        (L.transportId p).hom.app ((L.fiberEquivalence p).functor.obj Y) =
      (L.fiberEquivalence p).functor.map ((L.jointMapId p).hom.app Y) from key
  have hμ : (L.joint.mapComp' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app Y ≫
        (L.jointMapId p).hom.app ((L.jointMap (𝟙 p)).obj Y) = 𝟙 _ := by
    rw [← L.jointMapComp_hom_app (𝟙 p) (𝟙 p) (𝟙 p) (by simp),
      ← L.jointMapComp_comp_id_inv_app (𝟙 p) (by simp), Iso.hom_inv_id_app]
  rw [jointNormalizedTransportIso_hom_app, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc (L.transport (𝟙 p)), L.comparisonNaturality_actId]
  -- The naturality square of `transportId` is stated at `(e_p ⋙ 𝟭).obj Y`, which is only
  -- definitionally the object of the goal.
  erw [(L.transportId p).hom.naturality]
  rw [L.jointMapTransportIso_hom_app_comp_transportId_hom_app_assoc, ← Functor.map_comp_assoc, hμ]
  simp

/-- At an arrow `(𝟙 p, a)`, `jointNormalizedTransportIso` followed by the unit isomorphism of
transport is the naturality isomorphism of the fiber comparison at `a`. -/
@[reassoc]
lemma jointNormalizedTransportIso_hom_app_comp_transportId_hom_app (p : Γ)
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber p) :
    (L.jointNormalizedTransportIso (𝟙 p) a).hom.app Y ≫
        (L.transportId p).hom.app ((act actions p a).obj ((L.fiberEquivalence p).functor.obj Y)) =
      (L.comparisonNaturality p a).hom.app Y := by
  have hμ : (L.joint.mapComp' (𝟙 p ×ₘ a).toLoc
      (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 p ×ₘ a).toLoc
      (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app Y ≫
        (L.jointMapId p).hom.app ((L.jointAct p a).obj Y) = 𝟙 _ := by
    rw [jointMapId_hom_app]
    simp only [← prod_id, Quiver.Hom.id_toLoc, Pseudofunctor.mapId'_eq_mapId]
    rw [Pseudofunctor.mapComp'_comp_id_hom_app]
    simp
  rw [jointNormalizedTransportIso_hom_app, Category.assoc, Category.assoc]
  -- As in `jointNormalizedTransportIso_hom_app_comp_jointId_hom_app`, the naturality square of
  -- `transportId` is stated at `(e_p ⋙ T_a).obj Y`, only definitionally the object of the goal.
  erw [(L.transportId p).hom.naturality]
  rw [L.jointMapTransportIso_hom_app_comp_transportId_hom_app_assoc, ← Functor.map_comp_assoc, hμ]
  simp

/-- Inside the transport along `h`, the composition comparison of the joint functors along `H` and
the commuting isomorphism of transport pass through `jointMapTransportIso g`. -/
private lemma jointMapTransportIso_jointActComp_transportCommIso {p q : Γ} (g : p ⟶ q)
    (a b ab : SingleObj.star H ⟶ SingleObj.star H) (hab : a ≫ b = ab) (Y : L.jointFiber p) :
    (L.jointMapTransportIso g).hom.app ((L.jointAct p ab).obj Y) ≫
        (L.transport g).map ((L.fiberEquivalence p).functor.map
          ((L.jointActComp p a b ab hab).hom.app Y) ≫
            (L.comparisonNaturality p b).hom.app ((L.jointAct p a).obj Y) ≫
              (act actions p b).map ((L.comparisonNaturality p a).hom.app Y)) ≫
          (L.transportCommIso g b).hom.app
            ((act actions p a).obj ((L.fiberEquivalence p).functor.obj Y)) =
      (L.fiberEquivalence q).functor.map ((L.jointMap g).map
          ((L.jointActComp p a b ab hab).hom.app Y) ≫
            (L.jointActCommIso g b).hom.app ((L.jointAct p a).obj Y)) ≫
        (L.comparisonNaturality q b).hom.app ((L.jointMap g).obj ((L.jointAct p a).obj Y)) ≫
          (act actions q b).map ((L.jointMapTransportIso g).hom.app ((L.jointAct p a).obj Y) ≫
            (L.transport g).map ((L.comparisonNaturality p a).hom.app Y)) := by
  have natν := (L.jointMapTransportIso g).hom.naturality
    ((L.jointActComp p a b ab hab).hom.app Y)
  have natκ := (L.transportCommIso g b).hom.naturality
    ((L.comparisonNaturality p a).hom.app Y)
  have hC := L.jointMapTransportIso_hom_app_comp_transportCommIso_hom_app g b
    ((L.jointAct p a).obj Y)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor]
    at natν natκ hC
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% natν, natκ, reassoc_of% hC]
  simp only [Functor.map_comp, Category.assoc]

/-- The two factorizations of `(gh, ab)` through `(𝟙 p, a) ≫ (g, 1) ≫ (𝟙 q, b) ≫ (h, 1)` given by
the joint compositors agree. -/
private lemma joint_mapComp'_factorization {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r)
    (hgh : g ≫ h = gh) (a b ab : SingleObj.star H ⟶ SingleObj.star H) (hab : a ≫ b = ab)
    (Y : L.jointFiber p) :
    (L.joint.mapComp' (𝟙 p ×ₘ ab).toLoc (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (gh ×ₘ ab).toLoc (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app Y ≫
        (L.jointMapComp g h gh hgh).hom.app ((L.jointAct p ab).obj Y) ≫
          (L.jointMap h).map ((L.jointMap g).map ((L.jointActComp p a b ab hab).hom.app Y) ≫
            (L.jointActCommIso g b).hom.app ((L.jointAct p a).obj Y)) =
      (L.joint.mapComp' (g ×ₘ a).toLoc (h ×ₘ b).toLoc (gh ×ₘ ab).toLoc
          (by rw [← Quiver.Hom.comp_toLoc, prod_comp, hgh, hab])).hom.toNatTrans.app Y ≫
        (L.joint.mapComp' (𝟙 q ×ₘ b).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ b).toLoc
          (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app
            ((L.joint.map (g ×ₘ a).toLoc).toFunctor.obj Y) ≫
          (L.jointMap h).map ((L.jointAct q b).map ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc
            (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
            (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app Y)) := by
  -- Unfold to the joint compositors and apply associativity four times: at
  -- `(1, ab) ≫ (g, 1) ≫ (h, 1)`, `(1, a) ≫ (1, b) ≫ (g, 1)`, `(1, a) ≫ (g, 1) ≫ (1, b)` and
  -- `(g, a) ≫ (1, b) ≫ (h, 1)`.
  rw [jointMapComp_hom_app, jointActComp_hom_app, jointActCommIso_hom_app,
    L.joint.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
      (𝟙 p ×ₘ ab).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ ab).toLoc (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc (gh ×ₘ ab).toLoc
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp)
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp [hgh])
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp),
    ← Functor.map_comp,
    L.joint.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
      (𝟙 p ×ₘ a).toLoc (𝟙 p ×ₘ b).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (𝟙 p ×ₘ ab).toLoc (g ×ₘ b).toLoc (g ×ₘ ab).toLoc
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp [hab])
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp)
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp),
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    L.joint.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app
      (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ b).toLoc
      (g ×ₘ a).toLoc (g ×ₘ b).toLoc (g ×ₘ ab).toLoc
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp)
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp)
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp [hab]),
    Functor.map_comp,
    L.joint.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
      (g ×ₘ a).toLoc (𝟙 q ×ₘ b).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ ab).toLoc (h ×ₘ b).toLoc (gh ×ₘ ab).toLoc
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp [hab])
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp)
      (by rw [← Quiver.Hom.comp_toLoc, prod_comp]; simp [hgh])]

/-- `jointNormalizedTransportIso` intertwines the composition comparisons of the joint functors of
`L` and of its normalized transport, at a factorization `(g, a) ≫ (h, b) = (gh, ab)`. -/
@[reassoc]
lemma jointNormalizedTransportIso_hom_app_comp_jointComp_hom_app {p q r : Γ} (g : p ⟶ q)
    (h : q ⟶ r) (gh : p ⟶ r) (hgh : g ≫ h = gh) (a b ab : SingleObj.star H ⟶ SingleObj.star H)
    (hab : a ≫ b = ab) (Y : L.jointFiber p) :
    (L.jointNormalizedTransportIso gh ab).hom.app Y ≫
        (L.normalizedTransport.jointComp (g ×ₘ a) (h ×ₘ b) (gh ×ₘ ab)
          (by rw [prod_comp, hgh, hab])).hom.app ((L.fiberEquivalence p).functor.obj Y) =
      (L.fiberEquivalence r).functor.map ((L.joint.mapComp' (g ×ₘ a).toLoc (h ×ₘ b).toLoc
          (gh ×ₘ ab).toLoc
          (by rw [← Quiver.Hom.comp_toLoc, prod_comp, hgh, hab])).hom.toNatTrans.app Y) ≫
        (L.jointNormalizedTransportIso h b).hom.app
          ((L.joint.map (g ×ₘ a).toLoc).toFunctor.obj Y) ≫
          (L.normalizedTransport.jointFunctor (h ×ₘ b)).map
            ((L.jointNormalizedTransportIso g a).hom.app Y) := by
  rw [NormalizedTransport.jointComp_hom_app]
  -- Display the composition comparison of the normalized transport through the transport of `L`:
  -- the composition comparison of the action, the inverse composition isomorphism of transport
  -- and the commuting isomorphism of `E_g` with `T_b`.
  suffices key : (L.jointNormalizedTransportIso gh ab).hom.app Y ≫
      (L.transport gh).map ((actComp actions p a b ab hab).hom.app
        ((L.fiberEquivalence p).functor.obj Y)) ≫
        (L.transportComp g h gh hgh).inv.app
          ((act actions p b).obj ((act actions p a).obj ((L.fiberEquivalence p).functor.obj Y))) ≫
          (L.transport h).map ((L.transportCommIso g b).hom.app
            ((act actions p a).obj ((L.fiberEquivalence p).functor.obj Y))) =
      (L.fiberEquivalence r).functor.map ((L.joint.mapComp' (g ×ₘ a).toLoc (h ×ₘ b).toLoc
          (gh ×ₘ ab).toLoc
          (by rw [← Quiver.Hom.comp_toLoc, prod_comp, hgh, hab])).hom.toNatTrans.app Y) ≫
        (L.jointNormalizedTransportIso h b).hom.app
          ((L.joint.map (g ×ₘ a).toLoc).toFunctor.obj Y) ≫
          (L.transport h).map ((act actions q b).map
            ((L.jointNormalizedTransportIso g a).hom.app Y)) from key
  rw [jointNormalizedTransportIso_hom_app, jointNormalizedTransportIso_hom_app,
    jointNormalizedTransportIso_hom_app]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor]
  simp only [Category.assoc, Functor.map_comp]
  -- Step 1: the comparison at `ab` followed by the composition comparison of the action.
  have h₁ := L.comparisonNaturality_actComp p a b ab hab Y
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor] at h₁
  rw [← Functor.map_comp_assoc (L.transport gh), h₁]
  -- Step 2: commute the inverse composition isomorphism of transport.
  have h₂ := (L.transportComp g h gh hgh).inv.naturality
    ((L.fiberEquivalence p).functor.map ((L.jointActComp p a b ab hab).hom.app Y) ≫
      (L.comparisonNaturality p b).hom.app ((L.jointAct p a).obj Y) ≫
        (act actions p b).map ((L.comparisonNaturality p a).hom.app Y))
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor] at h₂
  rw [reassoc_of% h₂]
  -- Step 3: composition along `Γ` of the comparisons `jointMapTransportIso`.
  have h₃ := L.jointMapTransportIso_hom_app_comp_transportComp_inv_app g h gh hgh
    ((L.jointAct p ab).obj Y)
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor] at h₃
  rw [reassoc_of% h₃]
  -- Step 4: inside `E_h`, move the joint composition comparison along `H` and the commuting
  -- isomorphism of transport across `jointMapTransportIso g`.
  rw [← Functor.map_comp (L.transport h), ← Functor.map_comp (L.transport h),
    L.jointMapTransportIso_jointActComp_transportCommIso g a b ab hab Y]
  -- Step 5: commute the resulting joint cell across `jointMapTransportIso h`.
  have h₅ := (L.jointMapTransportIso h).hom.naturality
    ((L.jointMap g).map ((L.jointActComp p a b ab hab).hom.app Y) ≫
      (L.jointActCommIso g b).hom.app ((L.jointAct p a).obj Y))
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor] at h₅
  rw [Functor.map_comp (L.transport h), ← reassoc_of% h₅]
  -- Step 6: on the right, commute the cells `(1, a) ≫ (g, 1) = (g, a)` and `(1, b)` across the
  -- naturality isomorphism of the comparison at `q` and across `jointMapTransportIso h`.
  have h₆ := (L.comparisonNaturality q b).hom.naturality
    ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
      (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app Y)
  have h₇ := (L.jointMapTransportIso h).hom.naturality
    ((L.jointAct q b).map ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ a).toLoc (by rw [← Quiver.Hom.comp_toLoc]; simp)).hom.toNatTrans.app Y))
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor]
    at h₆ h₇
  rw [← Functor.map_comp_assoc (L.transport h), ← h₆, Functor.map_comp_assoc,
    ← reassoc_of% h₇]
  -- Step 7: both sides now differ by two factorizations of `(gh, ab)` through
  -- `(1, a) ≫ (g, 1) ≫ (1, b) ≫ (h, 1)`, which agree by associativity of the joint compositors.
  simp only [← Functor.map_comp_assoc]
  rw [L.joint_mapComp'_factorization g h gh hgh a b ab hab Y]
  simp only [Functor.map_comp, Category.assoc]

/-- The strong transformation from the joint pseudofunctor of `L` to the joint pseudofunctor of its
normalized transport. Its components are the fiber comparisons `e_p`, and its naturality
isomorphism at `(g, a)` is `jointNormalizedTransportIso g a`. -/
-- Expose the components: the component equations for the naturality isomorphisms below type-check
-- only once the components are the fiber comparisons by definition.
@[expose] noncomputable def normalizedTransportJointHom :
    L.joint ⟶ L.normalizedTransport.joint where
  app X := (L.comparison X.as.1).app ⟨SingleObj.star H⟩
  naturality f := Cat.Hom.isoMk (L.jointNormalizedTransportIso f.as.1 f.as.2)
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete L.joint L.normalizedTransport.joint
      (fun X ↦ (L.comparison X.as.1).app ⟨SingleObj.star H⟩)
      (fun f ↦ Cat.Hom.isoMk (L.jointNormalizedTransportIso f.as.1 f.as.2)) η
  naturality_id X := by
    obtain ⟨⟨p, s⟩⟩ := X
    obtain rfl : s = SingleObj.star H := rfl
    have h := L.jointNormalizedTransportIso_hom_app_comp_jointId_hom_app p
    simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
      Pseudofunctor.mapId'_eq_mapId] at h
    ext Y
    -- Componentwise, the unitors of `Cat` contribute identities.
    change (L.jointNormalizedTransportIso (𝟙 p) (𝟙 _)).hom.app Y ≫
        (L.normalizedTransport.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app
          ((L.fiberEquivalence p).functor.obj Y) =
      (L.fiberEquivalence p).functor.map
        ((L.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app Y) ≫ 𝟙 _ ≫ 𝟙 _
    rw [NormalizedTransport.joint_mapId_hom_app]
    refine (h Y).trans ?_
    rw [Category.comp_id, Category.comp_id]
    rfl
  naturality_comp {X X' X''} f g := by
    obtain ⟨⟨p, s⟩⟩ := X
    obtain ⟨⟨q, s'⟩⟩ := X'
    obtain ⟨⟨r, s''⟩⟩ := X''
    obtain rfl : s = SingleObj.star H := rfl
    obtain rfl : s' = SingleObj.star H := rfl
    obtain rfl : s'' = SingleObj.star H := rfl
    have e : L.joint.mapComp' (f.as.1 ×ₘ f.as.2).toLoc (g.as.1 ×ₘ g.as.2).toLoc
        ((f.as.1 ≫ g.as.1) ×ₘ (f.as.2 ≫ g.as.2)).toLoc
        (by rw [← Quiver.Hom.comp_toLoc, prod_comp]) = L.joint.mapComp f g :=
      Pseudofunctor.mapComp'_eq_mapComp _ _ _
    have h := L.jointNormalizedTransportIso_hom_app_comp_jointComp_hom_app f.as.1 g.as.1 _ rfl
      f.as.2 g.as.2 _ rfl
    simp only [e] at h
    ext Y
    -- Componentwise, the associators of `Cat` contribute identities.
    change (L.jointNormalizedTransportIso (f.as.1 ≫ g.as.1) (f.as.2 ≫ g.as.2)).hom.app Y ≫
        (L.normalizedTransport.joint.mapComp f g).hom.toNatTrans.app
          ((L.fiberEquivalence p).functor.obj Y) =
      (L.fiberEquivalence r).functor.map ((L.joint.mapComp f g).hom.toNatTrans.app Y) ≫ 𝟙 _ ≫
        (L.jointNormalizedTransportIso g.as.1 g.as.2).hom.app ((L.joint.map f).toFunctor.obj Y) ≫
          𝟙 _ ≫ (L.normalizedTransport.joint.map g).toFunctor.map
            ((L.jointNormalizedTransportIso f.as.1 f.as.2).hom.app Y) ≫ 𝟙 _
    rw [NormalizedTransport.joint_mapComp_hom_app]
    refine (h Y).trans ?_
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    rfl

@[simp]
lemma normalizedTransportJointHom_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    L.normalizedTransportJointHom.app X = (L.comparison X.as.1).app ⟨SingleObj.star H⟩ :=
  (rfl)

@[simp]
lemma normalizedTransportJointHom_naturality_hom_app {X Y : LocallyDiscrete (Γ × SingleObj H)}
    (f : X ⟶ Y) (Z : L.jointFiber X.as.1) :
    (L.normalizedTransportJointHom.naturality f).hom.toNatTrans.app Z =
      (L.jointNormalizedTransportIso f.as.1 f.as.2).hom.app Z :=
  (rfl)

@[simp]
lemma normalizedTransportJointHom_naturality_inv_app {X Y : LocallyDiscrete (Γ × SingleObj H)}
    (f : X ⟶ Y) (Z : L.jointFiber X.as.1) :
    (L.normalizedTransportJointHom.naturality f).inv.toNatTrans.app Z =
      (L.jointNormalizedTransportIso f.as.1 f.as.2).inv.app Z :=
  (rfl)

/-- The strong transformation `normalizedTransportJointHom` is compatible with the fiber
comparisons: on each fiber its composite with the identity comparison of the reconstructed lift
is the fiber comparison of `L`, through right unitors. -/
noncomputable def normalizedTransportJointHomFiberIso (p : Γ) :
    (Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeft L.normalizedTransportJointHom ≫
        L.normalizedTransport.comparison p ≅ L.comparison p :=
  Pseudofunctor.StrongTrans.isoMk (fun a ↦ ρ_ ((L.comparison p).app a)) (fun {a b} f ↦ by
    obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
    obtain rfl : b = ⟨SingleObj.star H⟩ := rfl
    ext Y
    rw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Pseudofunctor.StrongTrans.comp_naturality_hom_app]
    change L.jointFiber p at Y
    -- Componentwise, the unitors of `Cat` and the identity components of the comparison of the
    -- reconstructed lift contribute identities.
    change 𝟙 _ ≫ ((L.comparison p).naturality f).hom.toNatTrans.app Y =
      ((L.jointNormalizedTransportIso (𝟙 p) f.as).hom.app Y ≫
        (L.transportId p).hom.app ((act actions p f.as).obj ((L.fiberEquivalence p).functor.obj Y)))
          ≫ (act actions p f.as).map (𝟙 _)
    refine (Category.id_comp _).trans
      (((L.jointNormalizedTransportIso_hom_app_comp_transportId_hom_app p f.as Y).trans
        (L.comparisonNaturality_hom_app p f.as Y)).symm.trans ?_)
    exact (Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) ((act actions p f.as).map_id _).symm))

/-- A lift maps to the reconstruction of its normalized transport. The joint transformation is
`normalizedTransportJointHom`, whose components are the fiber comparisons of `L`. -/
-- Expose the joint transformation and fiber isomorphisms for the component equations below.
@[expose] noncomputable def normalizedTransportToLiftHom : L.Hom L.normalizedTransport.toLift where
  joint := L.normalizedTransportJointHom
  fiberIso := L.normalizedTransportJointHomFiberIso

@[simp]
lemma normalizedTransportToLiftHom_joint :
    L.normalizedTransportToLiftHom.joint = L.normalizedTransportJointHom := (rfl)

@[simp]
lemma normalizedTransportToLiftHom_fiberIso_hom_as_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (L.normalizedTransportToLiftHom.fiberIso p).hom.as.app a = (ρ_ ((L.comparison p).app a)).hom :=
  (rfl)

@[simp]
lemma normalizedTransportToLiftHom_fiberIso_inv_as_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (L.normalizedTransportToLiftHom.fiberIso p).inv.as.app a = (ρ_ ((L.comparison p).app a)).inv :=
  (rfl)

end TauCeti.EquivariantGroupoidLift
