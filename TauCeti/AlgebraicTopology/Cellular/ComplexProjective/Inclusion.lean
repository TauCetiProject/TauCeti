/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Basic
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.Topology.ComplexProjectiveSpace.Inclusion

/-!
# The inclusion `CPⁿ ⊆ CPⁿ⁺¹` on singular homology

In the CW structure `TauCeti.ComplexProjectiveSpace.cwComplex (n + 1)` on `CPⁿ⁺¹`, the cells of
dimension `2i` are the classes of the unit vectors whose last nonzero coordinate is the `i`-th.
So the cells of dimension at most `2n + 1` make up the image of the inclusion `CPⁿ → CPⁿ⁺¹`, the
classes of the unit vectors with vanishing last coordinate
(`TauCeti.ComplexProjectiveSpace.skeletonLT_eq_range_inclusion`), and only the top cell, of
dimension `2n + 2`, is missing. Its attachment leaves homology unchanged below degree `2n + 1`
(`TauCeti.isIso_homologyMap_skeletonPair_map`): the inclusion induces an isomorphism
`Hₖ(CPⁿ; R) ≅ Hₖ(CPⁿ⁺¹; R)` for `k ≤ 2n`, and in degree `2n + 1` both groups vanish, so the
inclusion is an isomorphism in every degree except `2n + 2`, with coefficients in any abelian
category with coproducts (`TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_inclusion`).

These are the stage maps whose colimit computes the homology of `CP∞`.

## Main results

* `TauCeti.ComplexProjectiveSpace.skeletonLT_eq_range_inclusion`: `CPⁿ` is the
  `(2n + 1)`-skeleton of `CPⁿ⁺¹`.
* `TauCeti.ComplexProjectiveSpace.isIso_singularHomologyMap_inclusion`: `Hₖ(CPⁿ) ≅ Hₖ(CPⁿ⁺¹)` for
  `k ≠ 2n + 2`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.6, and Section 2.2, Lemma 2.34.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex Metric

universe v u

namespace TauCeti.ComplexProjectiveSpace

attribute [local instance] cwComplex Abelian.hasFiniteBiproducts

variable (n : ℕ)

/-- Every cell of the CW structure on `CPⁿ` is one of the open cells `openCell n i`, in dimension
`2i`. -/
private theorem exists_openCell_cwComplex_eq {m : ℕ}
    (j : cell (univ : Set (ComplexProjectiveSpace n)) m) :
    ∃ i : Fin (n + 1), 2 * (i : ℕ) = m ∧
      RelCWComplex.openCell (C := (univ : Set (ComplexProjectiveSpace n))) m j = openCell n i := by
  have hm : Nat.card (cell (univ : Set (ComplexProjectiveSpace n)) m) ≠ 0 :=
    Nat.card_ne_zero.2 ⟨⟨j⟩, inferInstance⟩
  rw [nat_card_cell_cwComplex, ne_eq, ite_eq_right_iff, not_forall] at hm
  obtain ⟨⟨hev, hle⟩, -⟩ := hm
  obtain ⟨i, rfl⟩ := hev.two_dvd
  refine ⟨⟨i, by omega⟩, rfl, ?_⟩
  rw [RelCWComplex.openCell, map_cwComplex ⟨i, by omega⟩ j, image_cellMap_ball]

/-- Each open cell `openCell n i` is a cell of the CW structure on `CPⁿ`, in dimension `2i`. -/
private theorem exists_openCell_cwComplex_eq_openCell (i : Fin (n + 1)) :
    ∃ j : cell (univ : Set (ComplexProjectiveSpace n)) (2 * i),
      RelCWComplex.openCell (C := (univ : Set (ComplexProjectiveSpace n))) (2 * i) j =
        openCell n i := by
  have hm : Nat.card (cell (univ : Set (ComplexProjectiveSpace n)) (2 * i)) ≠ 0 := by
    rw [nat_card_cell_cwComplex]
    split_ifs with h
    · exact one_ne_zero
    · exact absurd ⟨even_two_mul _, by omega⟩ h
  obtain ⟨j⟩ := (Nat.card_ne_zero.1 hm).1
  exact ⟨j, by rw [RelCWComplex.openCell, map_cwComplex i j, image_cellMap_ball]⟩

/-- **`CPⁿ` is the `(2n + 1)`-skeleton of `CPⁿ⁺¹`**: the cells of `CPⁿ⁺¹` of dimension below
`2n + 2` make up the image of the inclusion `CPⁿ → CPⁿ⁺¹`. -/
theorem skeletonLT_eq_range_inclusion :
    (skeletonLT (univ : Set (ComplexProjectiveSpace (n + 1))) ((2 * n + 2 : ℕ) : ℕ∞) :
      Set (ComplexProjectiveSpace (n + 1))) = range (inclusion n) := by
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT]
  ext p
  obtain ⟨y, rfl⟩ := mk_surjective (n + 1) p
  rw [mk_mem_range_inclusion_iff]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨m, hm, j, hj⟩
    obtain ⟨i, rfl, hji⟩ := exists_openCell_cwComplex_eq (n + 1) j
    rw [hji, mk_mem_openCell_iff] at hj
    exact hj.2 _ (Fin.lt_def.2 (by simp; norm_cast at hm; omega))
  · intro hy
    obtain ⟨i, hi, hyi⟩ := exists_lt_mk_mem_openCell y (k := n + 1) fun j hj ↦ by
      rwa [show j = Fin.last (n + 1) from
        Fin.ext (by have := j.is_lt; rw [Fin.val_last]; omega)]
    obtain ⟨j, hj⟩ := exists_openCell_cwComplex_eq_openCell (n + 1) i
    exact ⟨2 * i, by norm_cast; omega, j, hj ▸ hyi⟩

/-- The `(2n + 2)`-skeleton of `CPⁿ⁺¹` is all of `CPⁿ⁺¹`. -/
private theorem skeletonLT_eq_univ :
    (skeletonLT (univ : Set (ComplexProjectiveSpace (n + 1))) ((2 * n + 3 : ℕ) : ℕ∞) :
      Set (ComplexProjectiveSpace (n + 1))) = univ :=
  skeletonLT_eq_complex_of_isEmpty_cell _ (2 * n + 3) fun m hm ↦
    Finite.card_eq_zero_iff.1 <| by
      rw [nat_card_cell_cwComplex, ite_eq_right_iff]
      exact fun h ↦ absurd h.2 (by omega)

/-- `CPⁿ` is homeomorphic to the `(2n + 1)`-skeleton of `CPⁿ⁺¹`, through the inclusion. -/
private def toSkeletonIso :
    TopCat.of (ComplexProjectiveSpace n) ≅
      skeletonObj (univ : Set (ComplexProjectiveSpace (n + 1))) (2 * n + 2) :=
  TopCat.isoOfHomeo ((isClosedEmbedding_inclusion n).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (skeletonLT_eq_range_inclusion n).symm))

/-- The `(2n + 2)`-skeleton of `CPⁿ⁺¹` is `CPⁿ⁺¹`. -/
private def skeletonIso :
    skeletonObj (univ : Set (ComplexProjectiveSpace (n + 1))) (2 * n + 3) ≅
      TopCat.of (ComplexProjectiveSpace (n + 1)) :=
  TopCat.isoOfHomeo ((Homeomorph.setCongr (skeletonLT_eq_univ n)).trans (Homeomorph.Set.univ _))

/-- Through the two identifications, the inclusion of skeleta is the inclusion `CPⁿ → CPⁿ⁺¹`. -/
private lemma toSkeletonIso_hom_comp_map_comp_skeletonIso_hom :
    (toSkeletonIso n).hom ≫
        (skeletonPair (univ : Set (ComplexProjectiveSpace (n + 1))) (2 * n + 2)).map ≫
          (skeletonIso n).hom = TopCat.ofHom (inclusion n) :=
  (rfl)

variable {n} {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A] (R : A)

/-- **`Hₖ(CPⁿ) ≅ Hₖ(CPⁿ⁺¹)` for `k ≠ 2n + 2`.** The inclusion `CPⁿ → CPⁿ⁺¹` induces an
isomorphism on singular homology in every degree other than `2n + 2`, with coefficients in any
abelian category with coproducts: `CPⁿ⁺¹` is `CPⁿ` with one cell of dimension `2n + 2` attached.
In degree `2n + 1` both groups vanish. -/
theorem isIso_singularHomologyMap_inclusion {k : ℕ} (hk : k ≠ 2 * n + 2) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A k).obj R).map
      (TopCat.ofHom (inclusion n))) := by
  let H := (AlgebraicTopology.singularHomologyFunctor A k).obj R
  by_cases hk' : k = 2 * n + 1
  · -- In the odd degree `2n + 1` both homology groups vanish.
    have hX := isZero_singularHomology_of_odd (n := n) R (k := k) ⟨n, hk'⟩
    have hY := isZero_singularHomology_of_odd (n := n + 1) R (k := k) ⟨n, hk'⟩
    exact ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩
  -- Attaching the top cell, of dimension `2n + 2`, leaves homology unchanged in degree `k`.
  have : IsIso
      (H.map (skeletonPair (univ : Set (ComplexProjectiveSpace (n + 1))) (2 * n + 2)).map) :=
    isIso_homologyMap_skeletonPair_map (univ : Set (ComplexProjectiveSpace (n + 1))) R
      (j := 2 * n + 2) (k := k) hk (by omega)
  rw [← toSkeletonIso_hom_comp_map_comp_skeletonIso_hom]
  -- The skeletal pair presents the skeleta as `TopPair.snd` and `TopPair.fst`, equal to
  -- `skeletonObj` only up to unfolding, so `erw` is needed to split the composite.
  erw [Functor.map_comp, Functor.map_comp]
  exact IsIso.comp_isIso' (H.mapIso (toSkeletonIso n)).isIso_hom
    (IsIso.comp_isIso' this (H.mapIso (skeletonIso n)).isIso_hom)

end TauCeti.ComplexProjectiveSpace
