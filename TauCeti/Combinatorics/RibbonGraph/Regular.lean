/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Regular
public import TauCeti.Combinatorics.RibbonGraph.Classification

/-!
# Regularity comparisons for bipartite ribbon graphs and permutation triples

Matches `BipartiteRibbonGraph.IsRegular` with `PermutationTriple.IsRegular`.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, §4.2.
-/

public section

open Equiv

namespace TauCeti

namespace BipartiteRibbonGraph

/-- Numbering the edges of a bipartite ribbon graph preserves regularity. -/
@[simp] theorem isRegular_toPermutationTriple {n : ℕ} (Γ : BipartiteRibbonGraph.{u})
    (ν : Γ.E ≃ Fin n) : (Γ.toPermutationTriple ν).IsRegular ↔ Γ.IsRegular := by
  let φ : Γ.E →ₑ[Γ.autEquivAutomorphismGroup ν] Fin n :=
    ⟨ν, fun f e ↦ by simp [Aut.smul_def, Subgroup.smul_def, Perm.smul_def]⟩
  exact (PermutationTriple.isRegular_iff.trans <| and_congr (Γ.isConnected_toPermutationTriple ν)
    (MulAction.isPretransitive_congr (f := φ) (Γ.autEquivAutomorphismGroup ν).surjective
      ν.bijective).symm).trans isRegular_iff.symm

end BipartiteRibbonGraph

/-- Passing from a permutation triple to its ribbon graph preserves regularity. -/
@[simp] theorem PermutationTriple.isRegular_ribbonGraph {n : ℕ} (t : PermutationTriple n) :
    t.ribbonGraph.IsRegular ↔ t.IsRegular := by
  rw [← t.ribbonGraph.isRegular_toPermutationTriple (Equiv.refl (Fin n)),
    t.toPermutationTriple_ribbonGraph]

end TauCeti
