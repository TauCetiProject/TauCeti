/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless.Affine.D
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.MatrixRepresentation

/-!
# Quartic Hochschild classes and non-formality for affine `Dₙ` subgraphs

In the numbering of `TauCeti.AffineDynkinType.graph (D n)` (`n ≥ 4`), the node `1` has neighbours
`0` and `n - 1` (and for `n = 4` it is the central node of valency four, while for `n ≥ 5` the
nodes `1` and `n - 3` are the two trivalent branch nodes joined by `1 - 2 - ⋯ - (n - 3)`). Using
the signless matrix representation `TauCeti.affineDMatrix` of `Dₙ` on the closed backtrack walk
`1 → 0 → 1 → (n - 1) → 1` at node `1`, this file shows that for every finite simple graph `G`
without isolated vertices containing a copy of `Dₙ` (`n ≥ 4`), not necessarily induced:

1. Over every nontrivial commutative ring, `HH^{4, -2}(Z, Z)` is nonzero
   (`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`).
2. Over every nontrivial commutative ring, there exists a closed walk of length four in `G` whose
   single-walk loop deformation is not formal
   (`TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_four_of_copy_affineD`), and hence the
   strict zigzag algebra `Z` is not intrinsically formal
   (`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_affineD`).

Specializing to `G = Dₙ` gives the same conclusions for the affine `Dₙ` zigzag algebra itself for
all `n ≥ 4`. Explicit quartic deformations of the affine `D₄` zigzag algebra are constructed in
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Four`.

## Main results

* `TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`: if `G`
  contains a copy of an affine `Dₙ` diagram (`n ≥ 4`), then `HH^{4, -2}(Z, Z)` is nonzero over
  every nontrivial commutative ring.
* `TauCeti.exists_not_isFormal_zigzagLoopAInfinityAlgebra_four_of_copy_affineD`: along any copy of
  an affine `Dₙ` diagram (`n ≥ 4`) in `G`, there exists a closed walk of length four whose
  single-walk loop deformation is not formal over every nontrivial commutative ring.
* `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_affineD`: if `G`
  contains a copy of an affine `Dₙ` diagram (`n ≥ 4`), then `Z` is not intrinsically formal over
  every nontrivial commutative ring.
* `TauCeti.not_hochschildVanishesAt_four_affineD`: `HH^{4, -2}` of the affine `Dₙ` zigzag algebra
  is nonzero for `n ≥ 4`, over every nontrivial commutative ring.
* `TauCeti.not_isIntrinsicallyFormal_affineD`: the affine `Dₙ` zigzag algebra is not
  intrinsically formal for `n ≥ 4`, over every nontrivial commutative ring.
-/

public section

namespace TauCeti

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

/-- The four-dart backtrack walk `1 → 0 → 1 → (n - 1) → 1` at node `1` of the affine `Dₙ` diagram
(`n ≥ 4`), in product order. -/
private def affineDWalk {n : ℕ} (hn : 4 ≤ n) : Fin 4 → (AffineDynkinType.D n).graph.Dart :=
  have hnodes := AffineDynkinType.nodes_D n
  let c : Fin (AffineDynkinType.D n).nodes := ⟨1, by omega⟩
  let a : Fin (AffineDynkinType.D n).nodes := ⟨0, by omega⟩
  let b : Fin (AffineDynkinType.D n).nodes := ⟨n - 1, by omega⟩
  have h1n : 1 ≤ n - 2 := by omega
  have h₁ : (AffineDynkinType.D n).graph.Adj c a :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inl ⟨rfl, h1n⟩))
  have h₂ : (AffineDynkinType.D n).graph.Adj c b :=
    (AffineDynkinType.graph_D_adj hn).2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  ![⟨(b, c), h₂.symm⟩, ⟨(c, b), h₂⟩, ⟨(a, c), h₁.symm⟩, ⟨(c, a), h₁⟩]

/-- Consecutive darts of `affineDWalk` are cyclically composable in product order. -/
private theorem affineDWalk_fst_eq_snd {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    (affineDWalk hn i).fst = (affineDWalk hn (i + 1)).snd := by
  fin_cases i <;> rfl

/-- The matrix product of `affineDMatrix` along `affineDWalk` has trace `1`. -/
private theorem trace_affineDMatrix_affineDWalk (k : Type w) [CommRing k] {n : ℕ} (hn : 4 ≤ n) :
    Matrix.trace (List.ofFn fun t ↦
      affineDMatrix k n (affineDWalk hn t).fst (affineDWalk hn t).snd).prod = 1 := by
  have htr := trace_affineDMatrix_backtracks k hn
  simp only [mul_assoc] at htr
  simpa [List.ofFn_succ, affineDWalk] using htr

/-- **Graphs containing an affine `Dₙ` have `HH^{4, -2}` nonzero.** If a graph `G` with no isolated
vertex contains a copy of the affine diagram `Dₙ` (`n ≥ 4`), not necessarily induced, then over
every nontrivial commutative ring the Hochschild cohomology `HH^{4, -2}` of the strict zigzag
algebra of `G` is nonzero. -/
theorem not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained
    [Nontrivial k] {n : ℕ}
    (hn : 4 ≤ n) (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ¬(𝒵).HochschildVanishesAt ⟨4, by norm_num⟩ := by
  obtain ⟨f⟩ := hG
  refine not_hochschildVanishesAt_zigzagStrictAInfinityAlgebra_of_trace_ne_zero
    (fun i j : Fin (AffineDynkinType.D n).nodes ↦ affineDMatrix k n i j)
    (sum_affineDMatrix_mul_affineDMatrix k hn) f (AffineDynkinType.isBipartite_graph_D hn)
    (n := 2) (by norm_num) (affineDWalk_fst_eq_snd hn) ?_
  rw [trace_affineDMatrix_affineDWalk]
  exact one_ne_zero

/-- **A non-formal quartic loop deformation along a copy of an affine `Dₙ` diagram**, over every
nontrivial commutative ring: given a copy of `Dₙ` (`n ≥ 4`) in `G`, there exists a closed walk of
length four in `G` whose single-walk loop deformation is a minimal, strictly unital `A∞` structure
on the zigzag algebra of `G` which is not formal. -/
theorem exists_not_isFormal_zigzagLoopAInfinityAlgebra_four_of_copy_affineD [Nontrivial k] {n : ℕ}
    (hn : 4 ≤ n) (f : (AffineDynkinType.D n).graph.Copy G) :
    ∃ (w : Fin 4 → G.Dart) (hw : ∀ i, (w i).fst = (w (i + 1)).snd),
      ¬(zigzagLoopAInfinityAlgebra hns (Finsupp.single w (1 : k))
        (fst_eq_snd_of_mem_support_single hw (1 : k))).IsFormal :=
  ⟨fun t ↦ f.toHom.mapDart (affineDWalk hn t), fun i ↦ congrArg f (affineDWalk_fst_eq_snd hn i),
    not_isFormal_zigzagLoopAInfinityAlgebra_four_of_isUnit_trace f
      (AffineDynkinType.isBipartite_graph_D hn)
      (fun i j : Fin (AffineDynkinType.D n).nodes ↦ affineDMatrix k n i j)
      (sum_affineDMatrix_mul_affineDMatrix k hn) (affineDWalk_fst_eq_snd hn)
      (by rw [trace_affineDMatrix_affineDWalk]; exact isUnit_one)⟩

/-- **Graphs containing an affine `Dₙ` have non-intrinsically-formal zigzag algebras**, over every
nontrivial commutative ring. If a finite graph `G` with no isolated vertex contains a copy of the
affine diagram `Dₙ` (`n ≥ 4`), not necessarily induced, then `𝒵` is not intrinsically formal. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_affineD
    [Nontrivial k] {n : ℕ} (hn : 4 ≤ n) (hG : (AffineDynkinType.D n).graph.IsContained G) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨f⟩ := hG
  obtain ⟨w, hw, hnf⟩ := exists_not_isFormal_zigzagLoopAInfinityAlgebra_four_of_copy_affineD
    (k := k) (hns := hns) hn f
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal hnf

/-- **The quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ` zigzag algebra is nonzero**
for `n ≥ 4`, over every nontrivial commutative ring: this is the case `G = Dₙ` of
`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`. -/
theorem not_hochschildVanishesAt_four_affineD [Nontrivial k] {n : ℕ} (hn : 4 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 hn))).HochschildVanishesAt ⟨4, by norm_num⟩ :=
  not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained hn .rfl

/-- **The affine `Dₙ` zigzag algebra is not intrinsically formal** for `n ≥ 4`, over every
nontrivial commutative ring: some `A∞` algebra whose cohomology algebra is the path-graded zigzag
algebra is not formal. This is the case `G = Dₙ` of
`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_affineD`. -/
theorem not_isIntrinsicallyFormal_affineD [Nontrivial k] {n : ℕ} (hn : 4 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 hn))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_affineD hn .rfl

end TauCeti
