/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.E
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.Tree

/-!
# Higher Hochschild classes and non-intrinsic formality of non-Dynkin trees

Let `Z` be the zigzag algebra of a finite tree `G` with no isolated vertex, graded by path length
and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). By the ADE subgraph dichotomy for finite trees
(`SimpleGraph.IsTree.isContained_affineDynkinType_of_not_exists_dynkinType_iso`), if `G` is not
isomorphic to the diagram of any valid Dynkin type (`Aₙ`, `Dₙ`, `E₆`, `E₇`, `E₈`), then `G`
contains a copy of an affine Dynkin diagram of type `Dₙ` (`n ≥ 4`), `E₆`, `E₇` or `E₈`.

Combining this dichotomy with the loop deformations along affine subgraphs constructed in
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.MatrixRepresentation` and
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.E`, this file establishes the non-ADE
direction of Liu--Wang's intrinsic formality theorem for trees:

1. Over every nontrivial commutative ring, `HH^{n, 2 - n}(Z, Z) ≠ 0` for some
   `n ∈ {4, 6, 8, 12}`
   (`SimpleGraph.IsTree.exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra`).
2. Both over every nontrivial `ℚ`-algebra and over every commutative ring `k` in which `(2 : k)` is
   not a unit (in particular in characteristic `2` and over `ℤ`), there is a single closed walk on
   `G` of length `n ∈ {4, 6, 8, 12}` whose minimal, strictly unital loop deformation
   `TauCeti.zigzagLoopAInfinityAlgebra` is not formal, and consequently `Z` is not intrinsically
   formal
   (`SimpleGraph.IsTree.exists_not_isFormal_zigzagLoopAInfinityAlgebra`,
   `SimpleGraph.IsTree.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra`, and their
   `_of_not_isUnit_two` companions).

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Theorem 1.2 and Section 4.
-/

public section

namespace SimpleGraph.IsTree

open TauCeti

variable {k : Type*} [CommRing k] {V : Type*} [Finite V] {G : SimpleGraph V}
  {hns : ∀ i : V, ∃ j, G.Adj i j}

/-- **The zigzag algebra of a non-Dynkin tree has a nonzero higher Hochschild class.** If a finite
tree `G` is not isomorphic to the diagram of any valid Dynkin type, then over every nontrivial
commutative ring the Hochschild cohomology `HH^{n, 2 - n}` of the strict zigzag algebra of `G` is
nonzero for some `n ∈ {4, 6, 8, 12}`: some loop operation of a closed walk of length `n` is a
Hochschild cocycle which is not a coboundary. In particular Kadeishvili's criterion
`TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_hochschildVanishesAt` does not apply. -/
theorem exists_not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra [Nontrivial k] (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ n : {n : ℕ // 1 < n}, (n : ℕ) ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ¬(zigzagStrictAInfinityAlgebra k hns).HochschildVanishesAt n := by
  classical
  have := Fintype.ofFinite V
  rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
    ⟨n, hn, h⟩ | h | h | h
  · exact ⟨⟨4, by norm_num⟩, by simp,
      not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained hn h⟩
  · exact ⟨⟨6, by norm_num⟩, by simp,
      not_hochschildVanishesAt_six_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨8, by norm_num⟩, by simp,
      not_hochschildVanishesAt_eight_zigzagStrictAInfinityAlgebra h⟩
  · exact ⟨⟨12, by norm_num⟩, by simp,
      not_hochschildVanishesAt_twelve_zigzagStrictAInfinityAlgebra h⟩

/-- Common `Dₙ / E₆ / E₇ / E₈` case split for single-walk non-formality on non-Dynkin trees,
parameterized by single-walk non-formality along copies of affine `E₆`, `E₇` and `E₈`. -/
private theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_affineE [Nontrivial k]
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix))
    (hE6 : ∀ f : AffineDynkinType.E6.graph.Copy G,
      ¬(zigzagLoopAInfinityAlgebra hns
        (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE6Walk t)) (1 : k))
        (fst_eq_snd_of_mem_support_single
          (fun i ↦ congrArg f (affineE6Walk_fst_eq_snd i)) 1)).IsFormal)
    (hE7 : ∀ f : AffineDynkinType.E7.graph.Copy G,
      ¬(zigzagLoopAInfinityAlgebra hns
        (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE7Walk t)) (1 : k))
        (fst_eq_snd_of_mem_support_single
          (fun i ↦ congrArg f (affineE7Walk_fst_eq_snd i)) 1)).IsFormal)
    (hE8 : ∀ f : AffineDynkinType.E8.graph.Copy G,
      ¬(zigzagLoopAInfinityAlgebra hns
        (Finsupp.single (fun t ↦ f.toHom.mapDart (affineE8Walk t)) (1 : k))
        (fst_eq_snd_of_mem_support_single
          (fun i ↦ congrArg f (affineE8Walk_fst_eq_snd i)) 1)).IsFormal) :
    ∃ (n : ℕ) (_ : NeZero n), n ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ∃ (w : Fin n → G.Dart) (hw : ∀ i, (w i).fst = (w (i + 1)).snd),
        ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single w (1 : k))
          (fst_eq_snd_of_mem_support_single hw 1)).IsFormal := by
  classical
  have := Fintype.ofFinite V
  rcases hG.isContained_affineDynkinType_of_not_exists_dynkinType_iso hD with
    ⟨m, hm, ⟨f⟩⟩ | h | h | h
  · obtain ⟨w, hw, hnf⟩ :=
      exists_not_isFormal_zigzagLoopAInfinityAlgebra_four_of_copy_D (k := k) (hns := hns) hm f
    exact ⟨4, inferInstance, by simp, w, hw, hnf⟩
  · obtain ⟨f⟩ := h
    exact ⟨6, inferInstance, by simp, fun t ↦ f.toHom.mapDart (affineE6Walk t),
      fun i ↦ congrArg f (affineE6Walk_fst_eq_snd i), hE6 f⟩
  · obtain ⟨f⟩ := h
    exact ⟨8, inferInstance, by simp, fun t ↦ f.toHom.mapDart (affineE7Walk t),
      fun i ↦ congrArg f (affineE7Walk_fst_eq_snd i), hE7 f⟩
  · obtain ⟨f⟩ := h
    exact ⟨12, inferInstance, by simp, fun t ↦ f.toHom.mapDart (affineE8Walk t),
      fun i ↦ congrArg f (affineE8Walk_fst_eq_snd i), hE8 f⟩

/-- **A non-Dynkin tree admits a non-formal single-walk loop deformation in arity `4`, `6`, `8` or
`12`**, over every nontrivial `ℚ`-algebra. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra [Nontrivial k] [Algebra ℚ k]
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ (n : ℕ) (_ : NeZero n), n ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ∃ (w : Fin n → G.Dart) (hw : ∀ i, (w i).fst = (w (i + 1)).snd),
        ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single w (1 : k))
          (fst_eq_snd_of_mem_support_single hw 1)).IsFormal :=
  exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_affineE hG hD
    not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk
    not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk
    not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk

/-- **A non-Dynkin tree admits a non-formal single-walk loop deformation in arity `4`, `6`, `8` or
`12`**, over every commutative ring in which `(2 : k)` is not a unit (in particular in
characteristic `2` and over `ℤ`). -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two (h2 : ¬IsUnit (2 : k))
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ∃ (n : ℕ) (_ : NeZero n), n ∈ ({4, 6, 8, 12} : Finset ℕ) ∧
      ∃ (w : Fin n → G.Dart) (hw : ∀ i, (w i).fst = (w (i + 1)).snd),
        ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single w (1 : k))
          (fst_eq_snd_of_mem_support_single hw 1)).IsFormal :=
  have : Nontrivial k := ⟨⟨2, 1, fun h ↦ h2 (h ▸ isUnit_one)⟩⟩
  exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_affineE hG hD
    (not_isFormal_zigzagLoopAInfinityAlgebra_affineE6Walk_of_not_isUnit_two h2)
    (not_isFormal_zigzagLoopAInfinityAlgebra_affineE7Walk_of_not_isUnit_two h2)
    (not_isFormal_zigzagLoopAInfinityAlgebra_affineE8Walk_of_not_isUnit_two h2)

/-- **The zigzag algebra of a non-Dynkin tree is not intrinsically formal**, over every nontrivial
`ℚ`-algebra: if a finite tree `G` with no isolated vertex is not isomorphic to the diagram of any
valid Dynkin type, then some minimal `A∞` algebra whose cohomology algebra is the path-graded zigzag
algebra of `G` is not formal. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra [Nontrivial k] [Algebra ℚ k]
    (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ¬(zigzagStrictAInfinityAlgebra k hns).IsIntrinsicallyFormal := by
  obtain ⟨n, _, -, w, hw, hnf⟩ := hG.exists_not_isFormal_zigzagLoopAInfinityAlgebra (k := k)
    (hns := hns) hD
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The zigzag algebra of a non-Dynkin tree is not intrinsically formal** whenever `(2 : k)` is
not a unit (for instance in characteristic `2` or over `ℤ`). -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isUnit_two
    (h2 : ¬IsUnit (2 : k)) (hG : G.IsTree)
    (hD : ¬ ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix)) :
    ¬(zigzagStrictAInfinityAlgebra k hns).IsIntrinsicallyFormal := by
  obtain ⟨n, _, -, w, hw, hnf⟩ :=
    hG.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_not_isUnit_two (hns := hns) h2 hD
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

end SimpleGraph.IsTree
