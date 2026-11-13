/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.CWComplex.Classical.Basic
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.CWComplex.Classical.Image
import TauCeti.Topology.CWComplex.Classical.TowerUnion
import TauCeti.Topology.Coherent

/-!
# Sequential colimits of CW complexes

Let `F : ℕ ⥤ TopCat` be a sequence of spaces, each carrying a CW structure on the whole space,
whose transition maps are closed embeddings, and suppose that the map `F k ⟶ F (k + 1)` carries
every cell of `F k` to a cell of `F (k + 1)`, recorded by maps `ι k m` of `m`-cells with
`⇑(map m (ι k m j)) = F.map _ ∘ map m j`. Then the colimit of `F` in `TopCat` is a CW complex
whose `m`-cells are the `m`-cells of `F 0` together with the `m`-cells of each `F (k + 1)` not
coming from `F k` (`TauCeti.TopCat.exists_cwComplex_of_isColimit`).

The maps from the stages to the colimit are closed embeddings
(`TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit`), so their images are CW complexes
(`Topology.IsClosedEmbedding.relCWComplex`). These images form a tower which covers the colimit,
and the colimit carries the topology coherent with them
(`TauCeti.TopCat.isCoherentWith_range_ι_of_isColimit`), so its CW structure is the union of the
tower (`TauCeti.cwSubcomplexTowerUnion`).

## Main results

* `TauCeti.TopCat.exists_cwComplex_of_isColimit`: the colimit of a sequence of CW complexes along
  closed embeddings carrying cells to cells is a CW complex, whose cells are the cells of the first
  stage together with the new cells of the later stages.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, on the topology of cell complexes.
-/

public section

open Set Topology Topology.RelCWComplex CategoryTheory Limits

universe u

namespace TauCeti.TopCat

variable {F : ℕ ⥤ TopCat.{u}} [∀ k, CWComplex (univ : Set (F.obj k))]

/-- **The colimit of a sequence of CW complexes.** Let `F : ℕ ⥤ TopCat` be a sequence of CW
complexes whose transition maps are closed embeddings, the map `F k ⟶ F (k + 1)` carrying each
`m`-cell `j` of `F k` to the `m`-cell `ι k m j` of `F (k + 1)`. Then the colimit of `F` is a CW
complex whose `m`-cells are the `m`-cells of `F 0` together with the `m`-cells of each `F (k + 1)`
not coming from `F k`. -/
theorem exists_cwComplex_of_isColimit
    (hF : ∀ ⦃i l : ℕ⦄ (hil : i ≤ l), IsClosedEmbedding (F.map (homOfLE hil)))
    (ι : ∀ k m, cell (univ : Set (F.obj k)) m → cell (univ : Set (F.obj (k + 1))) m)
    (hι : ∀ k m j, ⇑(map m (ι k m j)) = F.map (homOfLE k.le_succ) ∘ map m j)
    {c : Cocone F} (hc : IsColimit c) :
    ∃ _ : CWComplex (univ : Set c.pt), ∀ m, Nonempty (cell (univ : Set c.pt) m ≃
      cell (univ : Set (F.obj 0)) m ⊕
        Σ k, {j : cell (univ : Set (F.obj (k + 1))) m // j ∉ range (ι k m)}) := by
  have hj (k : ℕ) : IsClosedEmbedding (c.ι.app k) := isClosedEmbedding_ι_of_isColimit hF hc k
  -- The images `S k` of the stages are CW complexes, and they cover the colimit.
  let S (k : ℕ) : Set c.pt := range (c.ι.app k)
  have hSX : ⋃ k, S k = univ := iUnion_range_ι_of_isColimit hc
  let _ (k : ℕ) : RelCWComplex (S k) ∅ :=
    (hj k).relCWComplex (C := univ) (D := ∅) image_univ (image_empty _)
  let _ (k : ℕ) : CWComplex (S k) := RelCWComplex.toCWComplex (S k)
  let ε (k m : ℕ) : cell (S k) m ≃ cell (univ : Set (F.obj k)) m :=
    (hj k).relCWComplexCellEquiv image_univ (image_empty _) m
  have hmapS (k m : ℕ) (i : cell (S k) m) : ⇑(map m i) = c.ι.app k ∘ map m (ε k m i) :=
    (hj k).coe_map_relCWComplex image_univ (image_empty _) m i
  -- The cells of each `S k` are cells of `S (k + 1)`, with the same characteristic maps.
  let ιS (k m : ℕ) (i : cell (S k) m) : cell (S (k + 1)) m := (ε (k + 1) m).symm (ι k m (ε k m i))
  have hιS (k m : ℕ) (i : cell (S k) m) : ⇑(map m (ιS k m i)) = ⇑(map m i) := by
    rw [hmapS, hmapS, Equiv.apply_symm_apply, hι]
    funext x
    exact c.w_apply (homOfLE k.le_succ) _
  -- The colimit is the union of the tower of the `S k`, and its cells are their new cells.
  rw [← hSX]
  refine ⟨cwSubcomplexTowerUnion hιS fun A _ hA ↦
    (isCoherentWith_range_ι_of_isColimit hc).isClosed_of_forall_isClosed_inter
      (forall_mem_range.2 hA), fun m ↦ ⟨?_⟩⟩
  refine (cwSubcomplexTowerUnionCellEquiv _ _ m).trans ((Equiv.sigmaNatSucc _).trans
    (Equiv.sumCongr ((Equiv.subtypeUnivEquiv (isNewTowerCell_zero ιS)).trans (ε 0 m))
      (Equiv.sigmaCongrRight fun k ↦ (Equiv.subtypeEquivRight
        fun i ↦ isNewTowerCell_succ_iff ιS i).trans ((ε (k + 1) m).subtypeEquiv fun i ↦ ?_))))
  refine not_congr ⟨fun ⟨v, hv⟩ ↦ ⟨ε k m v, ?_⟩, fun ⟨v, hv⟩ ↦ ⟨(ε k m).symm v, ?_⟩⟩
  · simp [ιS, ← hv]
  · simp [ιS, hv]

end TauCeti.TopCat
