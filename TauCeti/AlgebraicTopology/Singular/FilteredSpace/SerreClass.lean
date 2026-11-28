/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# Homology of a filtered space modulo a Serre class

Let `A 0 ⊆ A 1 ⊆ ⋯ ⊆ A (N + 1)` be subspaces of a topological space and let `P` be a Serre class
of the coefficient category, for instance the zero objects, the torsion abelian groups, or the
abelian groups killed by a power of a fixed integer. If every step `Hₙ(A (j + 1), A j)` of the
filtration lies in `P`, so does `Hₙ(A (N + 1), A 0)`
(`TauCeti.prop_singularHomology_ofInclusion_of_monotone`). This is Serre's way of computing
modulo a class of abelian groups along a filtration; adding one step at a time, it is the
statement for one triple, `TauCeti.TopTriple.prop_singularHomology_totalPair`.

Over a division ring the dimension counts along a filtration are
`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Finrank`; the statement here needs no finiteness
and holds for every abelian coefficient category, for instance integral coefficients.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter I.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

variable {Y : TopCat.{w}} {A : ℕ → Set Y} (hA : Monotone A) {C : Type u} [Category.{v} C]
  [HasCoproducts.{w} C] [Abelian C] (R : C) (P : ObjectProperty C) [P.IsSerreClass]

/-- **Serre classes along a filtration.** If `A 0 ⊆ A 1 ⊆ ⋯ ⊆ A (N + 1)` and every step
`Hₙ(A (j + 1), A j)`, `j ≤ N`, lies in a Serre class `P`, then so does `Hₙ(A (N + 1), A 0)`. -/
theorem prop_singularHomology_ofInclusion_of_monotone {N : ℕ} (n : ℕ)
    (h : ∀ j ≤ N, P ((TopPair.ofInclusion (hA j.le_succ)).singularHomology R n)) :
    P ((TopPair.ofInclusion (hA (Nat.zero_le (N + 1)))).singularHomology R n) := by
  induction N with
  | zero => exact h 0 le_rfl
  | succ N ih =>
    -- Add the last step along the triple `(A (N + 2), A (N + 1), A 0)`.
    exact TopTriple.prop_singularHomology_totalPair
      (TopTriple.ofInclusions (hA (Nat.zero_le (N + 1))) (hA (N + 1).le_succ)) R P n
      (ih fun j hj ↦ h j (hj.trans N.le_succ)) (h (N + 1) le_rfl)

end TauCeti
