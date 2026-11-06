/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Abstract.Pushout
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex

/-!
# Attaching a classical relative CW complex along a map

Let `C` be a CW complex relative to `D` in a Hausdorff space `X`, in the sense of Mathlib's
classical `Topology.RelCWComplex`, and let `a : D → Z` be a continuous map to a space `Z`. The
adjunction space `Z ∪ₐ C` is the pushout in `TopCat` of the inclusion `D → C` and `a`, with its
quotient topology. This file shows that it is a CW complex relative to the image of `Z`
(`TauCeti.relCWComplexPushout`):

* its `n`-cells are the `n`-cells of `C` (`TauCeti.relCWComplexPushoutCellEquiv`);
* the characteristic map of a cell is the characteristic map of the corresponding cell of `C`
  followed by the map `C → Z ∪ₐ C` (`TauCeti.map_relCWComplexPushout`);
* the open cells are the images of the open cells of `C` (`TauCeti.openCell_relCWComplexPushout`).

Applied to `TauCeti.toRelativeCWComplex C`, the lemmas
`TopCat.RelativeCWComplex.isClosedEmbedding_of_isPushout` and
`TopCat.RelativeCWComplex.t2Space_of_isPushout` show that `Z → Z ∪ₐ C` is a closed embedding, so
the base of the structure is a closed copy of `Z`, and that `Z ∪ₐ C` is Hausdorff when `Z` is.

No cell structure on `Z` is needed. The structure is read off the categorical cell complex of
`(C, D)` (`TauCeti.toRelativeCWComplex`) by cobase change
(`TopCat.RelativeCWComplex.ofIsPushout`) and the comparison with classical relative CW complexes
(`TopCat.RelativeCWComplex.toRelCWComplex`).

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (attaching spaces) and the Appendix (the topology
  of cell complexes).
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

@[expose] public section

universe w

open CategoryTheory Limits Topology Set

namespace TauCeti

open Topology.RelCWComplex

variable {X : Type w} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Z P : TopCat.{w}} {a : C(D, Z)} {b : TopCat.of C ⟶ P} {f' : Z ⟶ P}
  (sq : IsPushout (TopCat.ofHom (ContinuousMap.inclusion base_subset_complex)) (TopCat.ofHom a)
    b f')

/-- **Attaching a relative CW complex along a map.** Let `C` be a CW complex relative to `D` and
`a : D → Z` continuous, and let `P` be a pushout in `TopCat` of the inclusion of `D` into `C` and
of `a`, such as the adjunction space `Z ∪ₐ C`. Then `P` is a CW complex relative to the image of
`Z`. Its cells are those of `C` (`TauCeti.relCWComplexPushoutCellEquiv`), with characteristic maps
followed by the map `b : C → P` (`TauCeti.map_relCWComplexPushout`). -/
@[instance_reducible] noncomputable def relCWComplexPushout :
    RelCWComplex (univ : Set P) (range f') :=
  ((toRelativeCWComplex C).ofIsPushout sq).toRelCWComplex

/-- The `n`-cells of the adjunction space `Z ∪ₐ C` are the `n`-cells of `C`. -/
noncomputable def relCWComplexPushoutCellEquiv (n : ℕ) :
    (relCWComplexPushout sq).cell n ≃ cell C n :=
  ((toRelativeCWComplex C).ofIsPushout sq).toRelCWComplexCellEquiv n

/-- **The characteristic maps of an adjunction space.** The characteristic map of an `n`-cell of
the adjunction space `Z ∪ₐ C` is the characteristic map of the corresponding cell of `C`,
followed by the map `b : C → P`. -/
theorem map_relCWComplexPushout (n : ℕ) (i : cell C n)
    (x : Metric.closedBall (0 : Fin n → ℝ) 1) :
    (relCWComplexPushout sq).map n ((relCWComplexPushoutCellEquiv sq n).symm i) x =
      b ⟨map n i x, closedCell_subset_complex n i ⟨x, x.2, rfl⟩⟩ := by
  refine (TopCat.RelativeCWComplex.map_toRelCWComplex_ofIsPushout (toRelativeCWComplex C) sq n i
    x).trans ?_
  congr 1
  apply Subtype.ext
  rw [TopCat.RelativeCWComplex.toRelCWComplex_map_apply, coe_toRelativeCWComplex_cells_ι_apply,
    Homeomorph.apply_symm_apply]
  -- The cells attached at stage `n` of `toRelativeCWComplex C` are `cell C n` only up to
  -- unfolding, so the index is generalized before it is identified with `i`.
  generalize hk : ((toRelativeCWComplex C).toRelCWComplexCellEquiv n)
    (((toRelativeCWComplex C).toRelCWComplexCellEquiv n).symm i) = k
  obtain rfl : k = i := hk.symm.trans (Equiv.apply_symm_apply _ _)
  rfl

/-- The map `b : C → P` sends the open cells of `C` onto the open cells of the adjunction
space. -/
theorem openCell_relCWComplexPushout (n : ℕ) (i : cell C n) :
    (relCWComplexPushout sq).openCell n ((relCWComplexPushoutCellEquiv sq n).symm i) =
      b '' (Subtype.val ⁻¹' openCell (C := C) n i) := by
  ext y
  simp only [Topology.RelCWComplex.openCell, mem_image, mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨map n i x, closedCell_subset_complex n i ⟨x, Metric.ball_subset_closedBall hx,
      rfl⟩⟩, ⟨x, hx, rfl⟩, ?_⟩
    exact (map_relCWComplexPushout sq n i ⟨x, Metric.ball_subset_closedBall hx⟩).symm
  · rintro ⟨⟨_, hz⟩, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, map_relCWComplexPushout sq n i ⟨x, Metric.ball_subset_closedBall hx⟩⟩

end TauCeti
