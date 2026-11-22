/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.HalfTurn
public import TauCeti.KnotTheory.Grid.Differential.Symmetry
public import TauCeti.KnotTheory.Grid.Grading.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Grading.HalfTurn
public import TauCeti.KnotTheory.Grid.Homology.Commutation.FullyBlocked
public import TauCeti.KnotTheory.Grid.Homology.Symmetry
public import TauCeti.KnotTheory.Grid.Move.Components
public import TauCeti.KnotTheory.Grid.Move.Unknot
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading
public import TauCeti.KnotTheory.Grid.Unknot.PoincareSeries

/-!
# Grid-move invariance of fully blocked grid homology up to stabilization

The fully blocked grid homology `GH~(G)` of a grid diagram `G` (written $\widetilde{GH}$ in the
literature) is not an invariant of the link that `G` presents: a stabilization tensors it with the
two-dimensional bigraded vector space `W`, with generators in bidegrees `(0, 0)` and `(-1, -1)`.
This file proves that this is the only dependence on the diagram. For grid diagrams with an odd
number of components, so that the `(O-Maslov, Alexander)` bigrading is integral, the Poincaré
series `P(G)` of `GH~(G)` satisfies

`P(G) * W ^ m = P(G') * W ^ n`

whenever the `n × n` diagram `G` and the `m × m` diagram `G'` are related by grid moves
(`OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_mul_W_pow_eq_of_movesTo`).
Since a finite-dimensional bigraded vector space over `𝔽₂` is determined by its Poincaré series,
this says that `GH~(G) ⊗ W^{⊗ m}` and `GH~(G') ⊗ W^{⊗ n}` are isomorphic bigraded vector spaces. In
particular the class of `P(G)` modulo `⊗ W`-stabilization is an invariant of grid links with an odd
number of components (`GridLink.stableFullyBlockedHomologySeries`), and the Alexander-graded Euler
characteristic of `GH~(G)` divided by `(1 - T⁻¹) ^ n` does not depend on the diagram.

The proof assembles the elementary moves.

* **Symmetries.** A cyclic permutation of the rows or of the columns, the diagonal reflection and
  the half-turn each relabel grid states, intertwine the fully blocked differentials and preserve
  the bidegree of every state, so they preserve `P(G)`
  (`OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining`).
* **Commutations.** A column commutation preserves `P(G)` by the pentagon comparison, and a row
  commutation is a column commutation of the diagonal reflections.
* **Stabilizations.** The stabilization whose new `O`-marking is the south-west corner of the new
  block multiplies `P(G)` by `W`; the half-turn exchanges it with the north-east one, which
  therefore does too. Every other stabilization is connected to one of these two by cyclic
  permutations and commutations (`GridDiagram.IsStabilization.exists_commutationMovesTo`).

Combined with the identification `GH~(G) ≅ G-hat(L) ⊗ W^{⊗(n - ℓ)}` for an `ℓ`-component
link `L`, cancelling the factors `W` would give the invariance of the bigraded Poincaré series
of simply blocked homology `G-hat`; that identification is not used here. Only the isomorphism
class of the bigraded vector space is shown to be invariant; no maps are attached to the moves.

## Main results

* `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_of_isStabilization`:
  every elementary stabilization multiplies the Poincaré series of `GH~` by `W`.
* `OddComponentGridDiagram.bigradedFullyBlockedHomologyPoincareSeries_mul_W_pow_eq_of_movesTo`:
  **invariance of `GH~` up to stabilization**, with the exact number of factors `W`.
* `OddComponentGridDiagram.isStablyEquiv_bigradedFullyBlockedHomologyPoincareSeries_of_movesTo`:
  the stable classes of the Poincaré series agree.
* `TauCeti.GridLink.stableFullyBlockedHomologySeries`: the stable class as an invariant of grid
  links with an odd number of components, with value `[1]` on the unknot
  (`TauCeti.GridLink.stableFullyBlockedHomologySeries_unknot`).

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 5, in particular the invariance of `GH~` up to the factor `W`
  under commutation and stabilization (Sections 5.1 and 5.2).
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), arXiv:math/0610559, Section 3.
-/

public section

namespace TauCeti.OddComponentGridDiagram

open GridDiagram

variable {n m : ℕ}

local notation "F" => ZMod 2
local notation "P" => bigradedFullyBlockedHomologyPoincareSeries

/-! ### Symmetries -/

/-- A linear equivalence of grid chains that intertwines the fully blocked differentials and moves
each grid state to a grid state of the same bidegree identifies the Poincaré series of fully
blocked homology. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining
    (G G' : OddComponentGridDiagram n) (e : GridChain F n ≃ₗ[F] GridChain F n)
    (he : ∀ c, G'.val.fullyBlockedDifferential (e c) = e (G.val.fullyBlockedDifferential c))
    (σ : GridState n → GridState n) (heσ : ∀ x, e (Finsupp.single x 1) = Finsupp.single (σ x) 1)
    (hσ : ∀ x, G'.bidegree (σ x) = G.bidegree x) :
    P G = P G' := by
  refine G.bigradedFullyBlockedHomologyPoincareSeries_eq_of_linearEquiv
    (G.val.fullyBlockedHomologyEquivOfIntertwining G'.val e he) fun g y => ?_
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    rw [bigradedFullyBlockedHomologyProjection_mk, fullyBlockedHomologyEquivOfIntertwining_apply_mk,
      fullyBlockedHomologyEquivOfIntertwining_apply_mk, bigradedFullyBlockedHomologyProjection_mk]
    congr 1
    ext1
    simp only [fullyBlockedCyclesEquivOfIntertwining_apply]
    have h := G.map_bigradedChainInclusion_bigradedChainProjection G' e.toLinearMap 0
      (fun x y hy => by
        rw [LinearEquiv.coe_coe, heσ, Finsupp.single_apply, ite_eq_right_iff]
        rintro rfl
        exact absurd (by rw [add_zero, hσ]) hy)
      g z
    rwa [add_zero] at h

variable (G : OddComponentGridDiagram n)

/-- A cyclic permutation of the rows preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_relabelRows_finRotate :
    P (G.relabelRows (finRotate n)) = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.relabelRowsEquiv (finRotate n))
    (by simpa only [val_relabelRows] using
      G.val.fullyBlockedDifferential_relabelRows_finRotate_apply) _
    (fun x => GridChain.relabelRowsEquiv_single _ x 1)
    (G.bidegree_relabelRows_finRotate)).symm

/-- A cyclic permutation of the columns preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_relabelColumns_finRotate :
    P (G.relabelColumns (finRotate n)) = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.relabelColumnsEquiv (finRotate n))
    (by simpa only [val_relabelColumns] using
      G.val.fullyBlockedDifferential_relabelColumns_finRotate_apply) _
    (fun x => GridChain.relabelColumnsEquiv_single _ x 1)
    (G.bidegree_relabelColumns_finRotate)).symm

/-- The diagonal reflection preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_transpose : P G.transpose = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.transposeEquiv F n)
    (LinearMap.congr_fun G.val.fullyBlockedDifferential_transpose) _
    (fun x => GridChain.transposeEquiv_single x 1) G.bidegree_transpose).symm

/-- The half-turn preserves the Poincaré series of `GH~`. -/
@[simp]
theorem bigradedFullyBlockedHomologyPoincareSeries_rotate : P G.rotate = P G :=
  (bigradedFullyBlockedHomologyPoincareSeries_eq_of_intertwining G _
    (GridChain.halfTurnEquiv F) G.val.fullyBlockedDifferential_rotate_halfTurnEquiv _
    (fun x => GridChain.halfTurnEquiv_single F x 1) G.bidegree_rotate_halfTurn).symm

/-! ### Commutations -/

/-- An elementary row or column commutation preserves the Poincaré series of `GH~`; a row
commutation is a column commutation of the diagonal reflections. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_of_isCommutation
    {G G' : OddComponentGridDiagram n} (h : IsCommutation G.val G'.val) : P G = P G' := by
  rcases (isCommutation_iff _ _).mp h with h | h
  · rw [← G.bigradedFullyBlockedHomologyPoincareSeries_transpose,
      ← G'.bigradedFullyBlockedHomologyPoincareSeries_transpose]
    exact bigradedFullyBlockedHomologyPoincareSeries_eq_of_isColumnCommutation
      ((isColumnCommutation_transpose _ _).mpr h)
  · exact bigradedFullyBlockedHomologyPoincareSeries_eq_of_isColumnCommutation h

/-- Diagrams connected by cyclic permutations and commutations have the same Poincaré series of
`GH~`. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_of_commutationMovesTo
    {G G' : OddComponentGridDiagram n} (h : CommutationMovesTo G.val G'.val) : P G = P G' := by
  obtain ⟨G, hG⟩ := G
  obtain ⟨G', hG'⟩ := G'
  exact h.induction_on
    (motive := fun A B => ∀ (hA : Odd A.componentCount) (hB : Odd B.componentCount),
      P ⟨A, hA⟩ = P ⟨B, hB⟩)
    (fun A hA _ =>
      (bigradedFullyBlockedHomologyPoincareSeries_relabelRows_finRotate ⟨A, hA⟩).symm.trans
        (congrArg P (Subtype.ext (val_relabelRows _ _))))
    (fun A hA _ =>
      (bigradedFullyBlockedHomologyPoincareSeries_relabelColumns_finRotate ⟨A, hA⟩).symm.trans
        (congrArg P (Subtype.ext (val_relabelColumns _ _))))
    (fun h hA hB => bigradedFullyBlockedHomologyPoincareSeries_eq_of_isCommutation
      (G := ⟨_, hA⟩) (G' := ⟨_, hB⟩) h)
    (fun _ _ _ => rfl)
    (fun _ ih hA hB => (ih hB hA).symm)
    (fun h _ ih ih' hA hC =>
      have hB := h.movesTo.componentCount_eq ▸ hA
      (ih hA hB).trans (ih' hB hC))
    hG hG'

/-! ### Stabilizations -/

/-- The north-east corner stabilization multiplies the Poincaré series of `GH~` by `W`: it is the
half-turn of the south-west corner stabilization of the half-turned diagram. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_stabilizeXSucc (s : Fin n) :
    P (G.stabilizeXSucc s) = P G * Bigraded.W := by
  rw [← bigradedFullyBlockedHomologyPoincareSeries_rotate, rotate_stabilizeXSucc,
    bigradedFullyBlockedHomologyPoincareSeries_stabilizeX,
    bigradedFullyBlockedHomologyPoincareSeries_rotate]

/-- **Every elementary stabilization multiplies the Poincaré series of `GH~` by `W`.** -/
theorem bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_of_isStabilization
    {G : OddComponentGridDiagram n} {G' : OddComponentGridDiagram (n + 1)}
    (h : IsStabilization G.val G'.val) : P G' = P G * Bigraded.W := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · rw [bigradedFullyBlockedHomologyPoincareSeries_eq_of_commutationMovesTo
      (G' := G.stabilizeX s) hs, bigradedFullyBlockedHomologyPoincareSeries_stabilizeX]
  · rw [bigradedFullyBlockedHomologyPoincareSeries_eq_of_commutationMovesTo
      (G' := G.stabilizeXSucc s) hs, bigradedFullyBlockedHomologyPoincareSeries_stabilizeXSucc]

/-! ### Grid moves -/

/-- The move invariance on diagrams of varying size, stated for the presenting pairs. -/
private theorem mul_W_pow_eq_of_isMove {A B : Σ n, GridDiagram n} (h : IsMove A B)
    (hA : Odd A.2.componentCount) (hB : Odd B.2.componentCount) :
    P (⟨A.2, hA⟩ : OddComponentGridDiagram A.1) * Bigraded.W ^ B.1 =
      P (⟨B.2, hB⟩ : OddComponentGridDiagram B.1) * Bigraded.W ^ A.1 := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact congrArg (· * _) (bigradedFullyBlockedHomologyPoincareSeries_eq_of_commutationMovesTo
        (G := ⟨_, hA⟩) (G' := ⟨_, hB⟩) (commutationMovesTo_relabelRows_finRotate _))
    · exact congrArg (· * _) (bigradedFullyBlockedHomologyPoincareSeries_eq_of_commutationMovesTo
        (G := ⟨_, hA⟩) (G' := ⟨_, hB⟩) (commutationMovesTo_relabelRows_finRotate _).symm)
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact congrArg (· * _) (bigradedFullyBlockedHomologyPoincareSeries_eq_of_commutationMovesTo
        (G := ⟨_, hA⟩) (G' := ⟨_, hB⟩) (commutationMovesTo_relabelColumns_finRotate _))
    · exact congrArg (· * _) (bigradedFullyBlockedHomologyPoincareSeries_eq_of_commutationMovesTo
        (G := ⟨_, hA⟩) (G' := ⟨_, hB⟩) (commutationMovesTo_relabelColumns_finRotate _).symm)
  | commutation h =>
    exact congrArg (· * _) (bigradedFullyBlockedHomologyPoincareSeries_eq_of_isCommutation
      (G := ⟨_, hA⟩) (G' := ⟨_, hB⟩) h)
  | stabilization h =>
    rw [bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_of_isStabilization
      (G := ⟨_, hA⟩) (G' := ⟨_, hB⟩) h, pow_succ]
    ring
  | destabilization h =>
    rw [bigradedFullyBlockedHomologyPoincareSeries_eq_mul_W_of_isStabilization
      (G := ⟨_, hB⟩) (G' := ⟨_, hA⟩) ((isDestabilization_iff_isStabilization _ _).mp h), pow_succ]
    ring

/-- **Invariance of fully blocked grid homology up to stabilization.** If the `n × n` diagram `G`
and the `m × m` diagram `G'` are related by grid moves, then `GH~(G) ⊗ W^{⊗ m}` and
`GH~(G') ⊗ W^{⊗ n}` have the same Poincaré series. -/
theorem bigradedFullyBlockedHomologyPoincareSeries_mul_W_pow_eq_of_movesTo
    {G : OddComponentGridDiagram n} {G' : OddComponentGridDiagram m}
    (h : MovesTo G.val G'.val) : P G * Bigraded.W ^ m = P G' * Bigraded.W ^ n := by
  obtain ⟨G, hG⟩ := G
  obtain ⟨G', hG'⟩ := G'
  refine h.induction_on
    (motive := fun A B => ∀ (hA : Odd A.2.componentCount) (hB : Odd B.2.componentCount),
      P (⟨A.2, hA⟩ : OddComponentGridDiagram A.1) * Bigraded.W ^ B.1 =
        P (⟨B.2, hB⟩ : OddComponentGridDiagram B.1) * Bigraded.W ^ A.1)
    (fun h hA hB => mul_W_pow_eq_of_isMove h hA hB) (fun _ _ _ => rfl)
    (fun _ ih hA hB => (ih hB hA).symm) (fun {A B C} h _ ih ih' hA hC => ?_) hG hG'
  -- Multiply the two witnesses together and cancel the factor `W ^ k` of the middle diagram.
  have hB : Odd B.2.componentCount := h.componentCount_eq ▸ hA
  refine mul_left_injective₀ (pow_ne_zero B.1 Bigraded.W_ne_zero) ?_
  calc P ⟨A.2, hA⟩ * Bigraded.W ^ C.1 * Bigraded.W ^ B.1
      = P ⟨A.2, hA⟩ * Bigraded.W ^ B.1 * Bigraded.W ^ C.1 := by ring
    _ = P ⟨B.2, hB⟩ * Bigraded.W ^ C.1 * Bigraded.W ^ A.1 := by rw [ih hA hB]; ring
    _ = P ⟨C.2, hC⟩ * Bigraded.W ^ A.1 * Bigraded.W ^ B.1 := by rw [ih' hB hC]; ring

/-- Diagrams related by grid moves have stably equivalent Poincaré series of `GH~`. -/
theorem isStablyEquiv_bigradedFullyBlockedHomologyPoincareSeries_of_movesTo
    {G : OddComponentGridDiagram n} {G' : OddComponentGridDiagram m}
    (h : MovesTo G.val G'.val) : Bigraded.IsStablyEquiv (P G) (P G') :=
  Bigraded.stableMk_eq_stableMk_iff.mp (by
    rw [← Bigraded.stableMk_mul_W_pow (P G) m,
      bigradedFullyBlockedHomologyPoincareSeries_mul_W_pow_eq_of_movesTo h,
      Bigraded.stableMk_mul_W_pow])

/-- The Alexander-graded Euler characteristics `χ` of `GH~` of an `n × n` diagram `G` and of an
`m × m` diagram `G'` related by grid moves satisfy `χ(G) (1 - T⁻¹) ^ m = χ(G') (1 - T⁻¹) ^ n`: the
quotient of `χ(G)` by `(1 - T⁻¹) ^ n` does not depend on the diagram. -/
theorem euler_bigradedFullyBlockedHomologyPoincareSeries_mul_eq_of_movesTo
    {G : OddComponentGridDiagram n} {G' : OddComponentGridDiagram m}
    (h : MovesTo G.val G'.val) :
    Bigraded.euler (P G) * (1 - LaurentPolynomial.T (-1)) ^ m =
      Bigraded.euler (P G') * (1 - LaurentPolynomial.T (-1)) ^ n := by
  rw [← Bigraded.euler_mul_W_pow, ← Bigraded.euler_mul_W_pow,
    bigradedFullyBlockedHomologyPoincareSeries_mul_W_pow_eq_of_movesTo h]

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridLink

open OddComponentGridDiagram

local notation "P" => bigradedFullyBlockedHomologyPoincareSeries

/-- The class modulo `⊗ W`-stabilization of the Poincaré series of fully blocked grid homology of
a grid link with an odd number of components, evaluated on a presenting diagram.

It is independent of the presenting diagram by
`OddComponentGridDiagram.isStablyEquiv_bigradedFullyBlockedHomologyPoincareSeries_of_movesTo`. -/
noncomputable def stableFullyBlockedHomologySeries (L : GridLink) (hL : Odd L.componentCount) :
    Bigraded.StableSeries :=
  let G := Classical.choose L.exists_gridDiagram
  Bigraded.stableMk (P (⟨G.2, by
    rwa [← componentCount_toGridLink, Classical.choose_spec L.exists_gridDiagram]⟩ :
      OddComponentGridDiagram G.1))

/-- Evaluate the stable class on any diagram presenting the grid link. -/
theorem stableFullyBlockedHomologySeries_eq_of_toGridLink_eq {L : GridLink}
    (hL : Odd L.componentCount) {n : ℕ} (G : OddComponentGridDiagram n)
    (h : G.val.toGridLink = L) :
    L.stableFullyBlockedHomologySeries hL = Bigraded.stableMk (P G) := by
  rw [stableFullyBlockedHomologySeries, Bigraded.stableMk_eq_stableMk_iff]
  exact isStablyEquiv_bigradedFullyBlockedHomologyPoincareSeries_of_movesTo
    ((GridDiagram.toGridLink_eq_iff_movesTo _).mp
      ((Classical.choose_spec L.exists_gridDiagram).trans h.symm))

/-- On the grid link presented by a diagram, the stable class is that of the diagram's Poincaré
series of `GH~`. -/
@[simp]
theorem stableFullyBlockedHomologySeries_toGridLink {n : ℕ} (G : OddComponentGridDiagram n)
    (h : Odd G.val.toGridLink.componentCount) :
    G.val.toGridLink.stableFullyBlockedHomologySeries h = Bigraded.stableMk (P G) :=
  stableFullyBlockedHomologySeries_eq_of_toGridLink_eq h G rfl

/-- The unknot has the stable class of the series `1`: its fully blocked homology on an `n × n`
grid is `W ^ (n - 1)`. -/
@[simp]
theorem stableFullyBlockedHomologySeries_unknot (h : Odd unknot.componentCount) :
    unknot.stableFullyBlockedHomologySeries h = Bigraded.stableMk 1 := by
  rw [stableFullyBlockedHomologySeries_eq_of_toGridLink_eq h
      (GridDiagram.isKnot_unknot 0).toOddComponentGridDiagram (GridDiagram.toGridLink_unknot 0),
    bigradedFullyBlockedHomologyPoincareSeries_unknot, ← one_mul (Bigraded.W ^ _),
    Bigraded.stableMk_mul_W_pow]

end TauCeti.GridLink
