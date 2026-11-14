/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.MatrixRepresentation
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal

/-!
# Quartic Hochschild classes and non-formality of the affine `Dₙ` zigzag algebras

In the numbering of `TauCeti.AffineDynkinType.graph (D n)`, for `n ≥ 5`, the nodes `1` and `n - 3`
are the two branch nodes of the affine `Dₙ` graph: the node `1` has the neighbours `0`, `2` and
`n - 1`, the node `n - 3` has the neighbours `n - 4`, `n - 2` and `n`, and they are joined by the
path `1 - 2 - ⋯ - (n - 3)`. The quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ`
zigzag algebra is nonzero over every nontrivial commutative ring, as a case of the result for every
graph containing an affine `Dₙ`
(`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`). When `2` is
invertible the affine `Dₙ` zigzag algebra is moreover not intrinsically formal, by the
two-branch-vertex criterion
`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_three_le_degree` of
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal`. The affine `D₄` graph, whose
only branch node has four neighbours, is treated in
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Four`.

## Main results

* `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_D` and
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_D`: when `2` is
  invertible and `G` contains a copy of affine `Dₙ` (`n ≥ 4`), some quartic loop deformation is not
  formal and the strict zigzag algebra of `G` is not intrinsically formal.
* `TauCeti.not_hochschildVanishesAt_four_affineD`: `HH^{4, -2}` of the affine `Dₙ` zigzag algebra
  is nonzero for `n ≥ 5`.
* `TauCeti.not_isIntrinsicallyFormal_affineD`: the affine `Dₙ` zigzag algebra is not
  intrinsically formal for `n ≥ 5`, when `2` is invertible.
-/

public section

namespace TauCeti

universe u w

variable {k : Type w} [CommRing k]

/-- **Graphs containing an affine `Dₙ` admit a non-formal quartic loop deformation** when `2` is
invertible: if `G` has no isolated vertex and contains a copy of the affine diagram `Dₙ` (`n ≥ 4`),
not necessarily induced, then over every nontrivial commutative ring in which `2` is invertible the
loop deformation supported on the image of the closed walk `1 → 0 → 1 → (n - 1) → 1` is not
formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_D
    [Nontrivial k] [Invertible (2 : k)] {V : Type u} {G : SimpleGraph V} [Finite V]
    {hns : ∀ i : V, ∃ j, G.Adj i j} {n : ℕ} (hn : 4 ≤ n)
    (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ∃ (c : (Fin 4 → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal := by
  classical
  obtain ⟨f⟩ := hG
  have hnodes := AffineDynkinType.nodes_D n
  let v₁ : Fin (AffineDynkinType.D n).nodes := ⟨1, by omega⟩
  let v₀ : Fin (AffineDynkinType.D n).nodes := ⟨0, by omega⟩
  let v₂ : Fin (AffineDynkinType.D n).nodes := ⟨n - 1, by omega⟩
  have h1n : 1 ≤ n - 2 := by omega
  have h₁ : (AffineDynkinType.D n).graph.Adj v₁ v₀ :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inl ⟨rfl, h1n⟩))
  have h₂ : (AffineDynkinType.D n).graph.Adj v₁ v₂ :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  let u : Fin 4 → (AffineDynkinType.D n).graph.Dart :=
    ![⟨(v₂, v₁), h₂.symm⟩, ⟨(v₁, v₂), h₂⟩, ⟨(v₀, v₁), h₁.symm⟩, ⟨(v₁, v₀), h₁⟩]
  have hu : ∀ i, (u i).fst = (u (i + 1)).snd := fun i ↦ by fin_cases i <;> rfl
  exact ⟨_, _, not_isFormal_zigzagLoopAInfinityAlgebra _ _ <|
    not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_of_trace_ne_zero
      f (AffineDynkinType.isBipartite_graph_D hn)
      (fun i j : Fin (AffineDynkinType.D n).nodes ↦ affineDMatrix k n i j)
      (sum_affineDMatrix_mul_affineDMatrix k hn) (n := 2) (by norm_num) hu <| by
        have htr := trace_affineDMatrix_backtracks k hn
        simp only [mul_assoc] at htr
        simp [List.ofFn_succ, u, v₁, v₀, v₂, htr]⟩

/-- **The strict zigzag algebra of a graph containing an affine `Dₙ` is not intrinsically formal**
for `n ≥ 4`, over every nontrivial commutative ring in which `2` is invertible. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_D
    [Nontrivial k] [Invertible (2 : k)] {V : Type u} {G : SimpleGraph V} [Finite V]
    {hns : ∀ i : V, ∃ j, G.Adj i j} {n : ℕ} (hn : 4 ≤ n)
    (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ¬(zigzagStrictAInfinityAlgebra k hns).IsIntrinsicallyFormal := by
  obtain ⟨_, _, hnf⟩ :=
    exists_not_isFormal_zigzagLoopAInfinityAlgebra_of_isContained_D (k := k) (hns := hns) hn hG
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ` zigzag algebra is nonzero**
for `n ≥ 5`, over every nontrivial commutative ring: this is the case `G = Dₙ` of
`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`. For `n = 4`
see `TauCeti.not_hochschildVanishesAt_four_affineD4`. -/
theorem not_hochschildVanishesAt_four_affineD [Nontrivial k] {n : ℕ} (hn : 5 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 (by omega)))).HochschildVanishesAt ⟨4, by norm_num⟩ :=
  not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained (by omega) .rfl

/-- **The affine `Dₙ` zigzag algebra is not intrinsically formal** for `n ≥ 5`, over every
nontrivial commutative ring in which `2` is invertible: some `A∞` algebra whose cohomology algebra
is the path-graded zigzag algebra is not formal. For `n = 4` see
`TauCeti.not_isIntrinsicallyFormal_affineD4`. -/
theorem not_isIntrinsicallyFormal_affineD [Nontrivial k] [Invertible (2 : k)] {n : ℕ}
    (hn : 5 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 (by omega)))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_D (by omega) .rfl

end TauCeti
