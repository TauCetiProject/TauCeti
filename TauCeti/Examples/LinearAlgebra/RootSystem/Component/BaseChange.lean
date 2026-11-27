/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.BaseChange
import TauCeti.LinearAlgebra.Matrix.Dual
import TauCeti.LinearAlgebra.RootSystem.PairingInvariance
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Rational components of A₁ × A₁

The adjoint integral datum has roots `±(2, 0)` and `±(0, 2)` and coroots `±(1, 0)` and
`±(0, 1)`. Its two components survive rationalization, including restriction to the rational
root and coroot spans, with the original four root labels and integer pairings.
-/

public section

open Matrix RootPairing

namespace TauCeti.Examples.RootComponents

private abbrev roots : Fin 4 → Fin 2 → ℤ := ![![2, 0], ![-2, 0], ![0, 2], ![0, -2]]

private abbrev coroots : Fin 4 → Fin 2 → ℤ := ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]]

/-- The adjoint integral root datum of A₁ × A₁, with opposite roots labelled consecutively. -/
def datum : RootPairing (Fin 4) ℤ (Fin 2 → ℤ) (Fin 2 → ℤ) where
  toLinearMap := dotProductBilin ℤ ℤ
  root := ⟨roots, by decide⟩
  coroot := ⟨coroots, by decide⟩
  root_coroot_two i := by
    fin_cases i <;> norm_num [dotProduct, Fin.sum_univ_two]
  reflectionPerm i := if i < 2 then Equiv.swap 0 1 else Equiv.swap 2 3
  reflectionPerm_root i j := by
    fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
      norm_num [dotProduct, Fin.sum_univ_two, Equiv.swap_apply_def]
  reflectionPerm_coroot i j := by
    fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
      norm_num [dotProduct, Fin.sum_univ_two, Equiv.swap_apply_def]

private theorem pairing_datum (i j : Fin 4) : datum.pairing i j = roots i ⬝ᵥ coroots j :=
  (rfl)

/-- Two roots lie in the same component exactly when they lie on the same coordinate axis. -/
private theorem componentOf_eq_iff (i j : Fin 4) :
    datum.componentOf i = datum.componentOf j ↔ i.val / 2 = j.val / 2 := by
  have hgraph : datum.nonorthogonalGraph =
      SimpleGraph.fromRel (fun i j : Fin 4 ↦ i.val / 2 = j.val / 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [nonorthogonalGraph_adj, IsOrthogonal, pairing_datum,
        dotProduct, Fin.sum_univ_two, SimpleGraph.fromRel_adj]
  rw [SimpleGraph.ConnectedComponent.eq, hgraph, SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      rw [SimpleGraph.fromRel_adj] at hstep
      exact ih.trans (hstep.2.elim id Eq.symm)
  · intro h
    by_cases hij : i = j
    · exact hij ▸ Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hij, Or.inl h⟩)

/-- There are exactly two components, represented by root labels `0` and `2`. -/
example : Nat.card datum.Component = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨datum.componentOf 0, datum.componentOf 2, ?_, ?_⟩
  · rw [Ne, componentOf_eq_iff]
    decide
  · ext C
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ i => fin_cases i <;> simp only [componentOf_eq_iff] <;> decide

/-- The first pair of opposite roots is precisely the support of the first component. -/
example : (datum.componentOf 0).supp = ({0, 1} : Set (Fin 4)) := by
  ext i
  fin_cases i <;> rw [SimpleGraph.ConnectedComponent.mem_supp_iff, componentOf_eq_iff] <;> decide

/-- The second pair of opposite roots is precisely the support of the second component. -/
example : (datum.componentOf 2).supp = ({2, 3} : Set (Fin 4)) := by
  ext i
  fin_cases i <;> rw [SimpleGraph.ConnectedComponent.mem_supp_iff, componentOf_eq_iff] <;> decide

/-- The two components remain distinct on the rational root and coroot spans. -/
example : ((datum.baseChange ℚ).restrictScalars' ℚ).componentOf 0 ≠
    ((datum.baseChange ℚ).restrictScalars' ℚ).componentOf 2 := by
  rw [← datum.rationalComponentEquiv_componentOf, ← datum.rationalComponentEquiv_componentOf,
    datum.rationalComponentEquiv.injective.ne_iff]
  rw [Ne, componentOf_eq_iff]
  decide

/-- Both rational components retain exactly their original supports. -/
example (C : datum.Component) : (datum.rationalComponentEquiv C).supp = C.supp := by
  simp

/-- Reading a rational component's integer pairing through the support equivalence gives the
original ordered pairing, for every pair in either component. -/
example (C : datum.Component) (i j : C.supp) :
    (((datum.baseChange ℚ).restrictScalars' ℚ).componentPairing
      (datum.rationalComponentEquiv C)).pairingIn ℤ
        (datum.rationalComponentSupportEquiv C i) (datum.rationalComponentSupportEquiv C j) =
      roots i ⬝ᵥ coroots j := by
  rw [rationalComponentPairing_pairingIn, pairingIn_eq_pairing, pairing_datum]

end TauCeti.Examples.RootComponents
