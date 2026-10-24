/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Regularity.Graph.StrongRegularity.Basic
public import TauCeti.Combinatorics.Regularity.Graph.SteppedCounting

/-!
# Induced counting from strong graph regularity

A strong regularity witness controls the labelled induced count of every three-vertex graph
by the density prediction on its coarse partition. The error consists of fine-pair irregularity,
the square root of the weighted-energy gap, and triples meeting a cell twice. Both edges and
nonedges enter the prediction, and counts are not divided by automorphisms.

## References

* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Chapter 2 (strong regularity and induced counting).
-/

public section

open Finset SimpleGraph

namespace TauCeti.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G} in
/-- **Strong regularity induced counting.** The densities on the coarse partition of a strong
regularity witness predict every labelled induced three-vertex pattern. No automorphism factor
is removed. The error includes irregular fine pairs, the energy gap, and repeated-cell triples. -/
theorem StrongRegular.inducedGraphCount3_estimate
    {P Q : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ} {l₀ : ℕ}
    (h : G.StrongRegular P Q ε F l₀) (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
    (hF : 0 < F #P.parts) {m : ℕ} (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |(J.inducedGraphCount3 G : ℝ) - J.coarseInducedGraphEstimate3 G P| ≤
      (16 * F #P.parts + 3 * √ε) * (Fintype.card V : ℝ) ^ 3 +
        6 * m * (Fintype.card V : ℝ) ^ 2 := by
  have hmQ (B : Finset V) (hB : B ∈ Q.parts) : #B ≤ m :=
    (card_le_card (Finpartition.le_refinementParent h.refines ⟨B, hB⟩)).trans
      (hm _ (Finpartition.refinementParent h.refines ⟨B, hB⟩).2)
  have hcount :=
    abs_inducedGraphCount3_sub_steppedInducedGraphCount3_le G J Q hF h.equitQ h.regQ hmQ
  have henergy := J.abs_steppedInducedGraphCount3_sub_le G h.refines h.energyClose
  have hdiag := J.steppedInducedGraphCount3_le_coarseInducedGraphEstimate3_add G P hm
  have hdiag₀ := J.coarseInducedGraphEstimate3_le_steppedInducedGraphCount3 G P
  have hdiag' : |J.steppedInducedGraphCount3 G P - J.coarseInducedGraphEstimate3 G P| ≤
      3 * m * (Fintype.card V : ℝ) ^ 2 := by
    rw [abs_of_nonneg (sub_nonneg.2 hdiag₀)]
    linarith
  have htriangle := (abs_sub_le (J.inducedGraphCount3 G : ℝ)
    (J.steppedInducedGraphCount3 G Q) (J.coarseInducedGraphEstimate3 G P)).trans
      (add_le_add_right (abs_sub_le (J.steppedInducedGraphCount3 G Q)
        (J.steppedInducedGraphCount3 G P) (J.coarseInducedGraphEstimate3 G P)) _)
  have hslack : 0 ≤ F #P.parts * (Fintype.card V : ℝ) ^ 3 := by positivity
  linarith

end TauCeti.SimpleGraph
