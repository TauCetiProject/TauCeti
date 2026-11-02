/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Obstruction.Invariance
public import TauCeti.Combinatorics.SimpleGraph.Degree
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.HochschildClass

/-!
# Non-formal quartic deformations of zigzag algebras

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). A quartic loop deformation
`TauCeti.zigzagLoopAInfinityAlgebra` is a minimal, strictly unital `A∞` structure on `Z` with the
same grading and product, `m₃ = 0`, and `m₄` a linear combination of loop operations of closed
walks. This file shows that such deformations can be **nontrivial modulo `A∞` isomorphism**, and
hence that `Z` is in general not intrinsically formal.

This combines two results. First, when `2` is invertible, a minimal `A∞`
structure with `m₃ = 0` which is `A∞` isomorphic to the graded algebra it deforms has a quartic
operation which is a Hochschild coboundary, even when the isomorphism has a nonzero quadratic
component
(`IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four` in
`TauCeti.AInfinityAlgebra`).
Second, the loop operation of a single closed walk of the shape `n₁ → v → n₀ → v → n₁` is not a
Hochschild coboundary in two situations: when the vertex `v` has four distinct neighbours, two of
which are `n₀` and `n₁`
(`TauCeti.not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single`),
and when `v` has three distinct neighbours, two of which are `n₀` and `n₁`, and is joined through
the third by a suitable walk to another vertex with three distinct neighbours
(`not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single_of_walk`).
Hence the loop deformation with coefficient one on that walk is not formal, equivalently not
`A∞` isomorphic to the strict zigzag algebra, and the strict zigzag algebra is not intrinsically
formal. For the affine `D₄` graph the walk is Liu--Wang's `β₄ α₁ β₁ α₄`; see
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.AffineD.Four`.

In terms of degrees, the strict zigzag algebra is not intrinsically formal when `G` has a vertex of
degree at least four, or two distinct vertices of degree at least three in one connected
component; for the second criterion the walk is taken along a path between the two vertices. The
results assume that `2` is invertible, as the invariance of the quartic obstruction does. Among the
finite trees which are not Dynkin diagrams they cover all except those with exactly one vertex of
degree three and none of larger degree, such as the affine `E₆`, `E₇` and `E₈` graphs; in
particular they cover the affine `Dₙ` graphs, see
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.AffineD.Basic`.

## Main results

* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra`: when `2` is invertible, a loop deformation
  whose quartic operation is not a Hochschild coboundary of the strict zigzag algebra is not
  formal.
* `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal`: if a loop
  deformation is not formal, then the strict zigzag algebra is not intrinsically formal.
* `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single` and
  `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk`: the loop deformation of a
  single closed walk `n₁ → v → n₀ → v → n₁` is not formal, at a vertex with four distinct
  neighbours, or at a vertex with three distinct neighbours joined by a walk to another such vertex.
* `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra` and
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_walk`: the corresponding
  statements that the strict zigzag algebra is not intrinsically formal.
* `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_four_le_degree` and
  `TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_three_le_degree`: the strict
  zigzag algebra is not intrinsically formal when `G` has a vertex of degree at least four, or two
  distinct vertices of degree at least three joined by a walk.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Section 4, for minimal `A∞` deformations of zigzag algebras and their intrinsic formality.
* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

/-- **A loop deformation whose quartic operation is not a coboundary is not formal**, when `2` is
invertible. If the quartic operation of the loop deformation with coefficients `c` is not the
Hochschild differential of a suspended cochain of degree zero of the strict zigzag algebra, then
the loop deformation is not formal. Equivalently it is not `A∞` isomorphic to the strict zigzag
algebra (`TauCeti.AInfinityAlgebra.IsMinimal.isFormal_iff_exists_isIso`). -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra [Invertible (2 : k)] (c : (Fin 4 → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (hobs : ¬∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨4, by norm_num⟩) :
    ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal :=
  AInfinityAlgebra.IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four
    (isMinimal_zigzagLoopAInfinityAlgebra c hc) isMinimal_zigzagStrictAInfinityAlgebra
    (fun _ hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega))
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading c hc)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two c hc)
    (zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by decide) (by decide)) hobs

/-- **A non-formal loop deformation shows that the strict zigzag algebra is not intrinsically
formal.** A loop deformation is a minimal `A∞` structure on the zigzag algebra with its grading and
product, so if it is not formal, then the strict zigzag algebra is not intrinsically formal. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal
    {c : (Fin 4 → G.Dart) →₀ k} {hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd}
    (h : ¬(zigzagLoopAInfinityAlgebra hns c hc).IsFormal) : ¬(𝒵).IsIntrinsicallyFormal := fun hf ↦
  h <| hf.isFormal_of_isMinimal
    (zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading _ _)
    (isMinimal_zigzagLoopAInfinityAlgebra _ _)
    (zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two _ _)

/-- **A non-formal quartic deformation of a zigzag algebra.** Assume that `2` is invertible and
that the ring is nontrivial. Let `δ 0, …, δ 3` be four distinct darts with a common head `v`, for
instance the darts into `v` from four distinct neighbours. The loop deformation whose quartic
operation is the loop operation of the single closed walk `(δ 3).symm, δ 0, (δ 0).symm, δ 3` (in
product order) is a minimal, strictly unital `A∞` structure on the zigzag algebra, with its grading
and product, which is not formal: it is not `A∞` isomorphic to the strict zigzag algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_single [Nontrivial k] [Invertible (2 : k)]
    {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V} (hv : ∀ i, (δ i).snd = v) :
    ¬(zigzagLoopAInfinityAlgebra hns _
      (fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk
        ((hv 3).trans (hv 0).symm) (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single hδ hv)

/-- **The zigzag algebra of a graph with a vertex of valency at least four is not intrinsically
formal**, over every nontrivial commutative ring in which `2` is invertible: when four distinct
darts of `G` have a common head, some `A∞` algebra whose cohomology algebra is the path-graded
zigzag algebra is not formal. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra [Nontrivial k]
    [Invertible (2 : k)] {δ : Fin 4 → G.Dart} (hδ : Function.Injective δ) {v : V}
    (hv : ∀ i, (δ i).snd = v) :
    ¬(𝒵).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal
    (not_isFormal_zigzagLoopAInfinityAlgebra_single hδ hv)

/-- **The zigzag algebra of a graph with a vertex of degree at least four is not intrinsically
formal**, over every nontrivial commutative ring in which `2` is invertible. This is
`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra` for the darts into `v` from four
distinct neighbours. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_four_le_degree [Nontrivial k]
    [Invertible (2 : k)] {v : V} [Fintype (G.neighborSet v)] (hv : 4 ≤ G.degree v) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  obtain ⟨ι⟩ : Nonempty (Fin 4 ↪ G.neighborSet v) := Function.Embedding.nonempty_of_card_le
    (by rwa [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree])
  exact not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra
    (δ := fun i ↦ ⟨((ι i : V), v), (ι i).2.symm⟩)
    (fun i j h ↦ ι.injective (Subtype.ext (congrArg (·.fst) h))) (v := v) fun _ ↦ rfl

/-! ### Two branch vertices joined by a walk -/

/-- **A non-formal quartic deformation at two branch vertices.** Assume that `2` is invertible and
that the ring is nontrivial. Let `d` and `e` be distinct darts with a common head `v`, and let the
non-backtracking walk of darts `f 0, …, f n` lead from `v`, along neither `d.symm` nor `e.symm`,
to a vertex `w` without returning to `v`. Let `d'` and `e'` be distinct darts with head `w`, both
distinct from the last dart `f n` of the walk. The loop deformation whose quartic operation is the
loop operation of the single closed walk `e.symm, d, d.symm, e` (in product order) is a minimal,
strictly unital `A∞` structure on the zigzag algebra, with its grading and product, which is not
formal: it is not `A∞` isomorphic to the strict zigzag algebra. -/
theorem not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk [Nontrivial k]
    [Invertible (2 : k)] {d e d' e' : G.Dart} {n : ℕ} {f : Fin (n + 1) → G.Dart} (hde : d ≠ e)
    (hed : e.snd = d.snd) (hf₀ : (f 0).fst = d.snd) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hf' : ∀ t : Fin n, f t.castSucc ≠ (f t.succ).symm) (hfd : ∀ t, (f t).snd ≠ d.snd)
    (hde' : d' ≠ e') (hd' : d'.snd = (f (Fin.last n)).snd) (he' : e'.snd = (f (Fin.last n)).snd)
    (hdf' : d' ≠ f (Fin.last n)) (hef' : e' ≠ f (Fin.last n)) :
    ¬(zigzagLoopAInfinityAlgebra hns _
      (fst_eq_snd_of_mem_support_single_rotate_zigzagBacktrackWalk hed (1 : k))).IsFormal :=
  not_isFormal_zigzagLoopAInfinityAlgebra _ _
    (not_exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_single_of_walk
      hde hed hf₀ hdf hef hf hf' hfd hde' hd' he' hdf' hef')

/-- **The zigzag algebra of a graph with two branch vertices joined by a suitable walk is not
intrinsically formal**, over every nontrivial commutative ring in which `2` is invertible. The
hypotheses are those of `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk`: two
vertices with three distinct neighbours each, joined by a non-backtracking walk which leaves the
first through its third neighbour, enters the second through its third neighbour, and does not
return to the first. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_walk [Nontrivial k]
    [Invertible (2 : k)] {d e d' e' : G.Dart} {n : ℕ} {f : Fin (n + 1) → G.Dart} (hde : d ≠ e)
    (hed : e.snd = d.snd) (hf₀ : (f 0).fst = d.snd) (hdf : d ≠ (f 0).symm)
    (hef : e ≠ (f 0).symm) (hf : ∀ t : Fin n, G.DartAdj (f t.castSucc) (f t.succ))
    (hf' : ∀ t : Fin n, f t.castSucc ≠ (f t.succ).symm) (hfd : ∀ t, (f t).snd ≠ d.snd)
    (hde' : d' ≠ e') (hd' : d'.snd = (f (Fin.last n)).snd) (he' : e'.snd = (f (Fin.last n)).snd)
    (hdf' : d' ≠ f (Fin.last n)) (hef' : e' ≠ f (Fin.last n)) :
    ¬(𝒵).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_not_isFormal
    (not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk hde hed hf₀ hdf hef hf hf' hfd hde' hd'
      he' hdf' hef')

/-- **The zigzag algebra of a graph with two branch vertices in one component is not
intrinsically formal**, over every nontrivial commutative ring in which `2` is invertible: if two
distinct vertices `v` and `w` of `G`, each of degree at least three, are joined by a walk, then
some `A∞` algebra whose cohomology algebra is the path-graded zigzag algebra is not formal. The
detecting deformation is that of `TauCeti.not_isFormal_zigzagLoopAInfinityAlgebra_single_of_walk`
along a path from `v` to `w`. Together with
`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_four_le_degree` this covers
every finite tree other than a path or a tree with exactly one vertex of degree three. -/
theorem not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_three_le_degree [Nontrivial k]
    [Invertible (2 : k)] {v w : V} [Fintype (G.neighborSet v)] [Fintype (G.neighborSet w)]
    (hvw : v ≠ w) (hr : G.Reachable v w) (hv : 3 ≤ G.degree v) (hw : 3 ≤ G.degree w) :
    ¬(𝒵).IsIntrinsicallyFormal := by
  classical
  -- The darts `f 0, …, f n` of a path `p` from `v` to `w`; the vertices of `p` are distinct.
  obtain ⟨p, hp⟩ := hr.exists_isPath
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 1 :=
    Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h ↦ hvw (p.eq_of_length_eq_zero h))
  have hinj {i j : ℕ} (hi : i ≤ n + 1) (hj : j ≤ n + 1) (h : p.getVert i = p.getVert j) : i = j :=
    hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  let f : Fin (n + 1) → G.Dart := fun t ↦
    ⟨(p.getVert t, p.getVert (t + 1)), p.adj_getVert_succ (by omega)⟩
  obtain ⟨a, b, ha, hb, hab, hau, hbu⟩ := G.exists_adj_adj_ne_of_three_le_degree hv (p.getVert 1)
  obtain ⟨a', b', ha', hb', hab', hau', hbu'⟩ :=
    G.exists_adj_adj_ne_of_three_le_degree hw (p.getVert n)
  have hd : (⟨(a, v), ha.symm⟩ : G.Dart).snd = p.getVert 0 := p.getVert_zero.symm
  -- Distinct darts are told apart by their tails. The vertices `(f 0).snd` and `(f n).fst` unfold
  -- to `p.getVert 1` and `p.getVert n`, and consecutive darts of `f` are adjacent by definition.
  refine not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_walk (f := f)
    (d := ⟨(a, v), ha.symm⟩) (e := ⟨(b, v), hb.symm⟩) (d' := ⟨(a', w), ha'.symm⟩)
    (e' := ⟨(b', w), hb'.symm⟩)
    (fun h ↦ hab (congrArg (·.fst) h)) rfl ?_ (fun h ↦ hau (congrArg (·.fst) h))
    (fun h ↦ hbu (congrArg (·.fst) h)) (fun _ ↦ rfl) (fun t h ↦ ?_) (fun t h ↦ ?_)
    (fun h ↦ hab' (congrArg (·.fst) h)) ?_ ?_ (fun h ↦ hau' (congrArg (·.fst) h))
    (fun h ↦ hbu' (congrArg (·.fst) h))
  · simp [f]
  · have := hinj (by omega) (by omega) (congrArg (·.fst) h)
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  · rw [hd] at h
    exact Nat.succ_ne_zero _ (hinj (by omega) (by omega) h)
  all_goals simp [f, ← hn]

end TauCeti
