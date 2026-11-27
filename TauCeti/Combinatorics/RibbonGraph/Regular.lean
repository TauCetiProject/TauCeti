/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Regular
public import TauCeti.Combinatorics.RibbonGraph.Classification

/-!
# Regular bipartite ribbon graphs

Defines `BipartiteRibbonGraph.IsRegular`, the edge action of `Γ.Aut` on `Γ.E`, and matches
regularity with `PermutationTriple.IsRegular` and `Nat.card Γ.Aut = Fintype.card Γ.E`.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, §4.2.
-/

public section

universe u v
namespace TauCeti.BipartiteRibbonGraph

/-- Automorphisms of a bipartite ribbon graph act on its edges by evaluation. -/
instance (Γ : BipartiteRibbonGraph.{u}) : SMul Γ.Aut Γ.E := ⟨fun f e ↦ f.edge e⟩

/-- An automorphism acts on an edge by applying its underlying edge bijection. -/
@[simp] theorem Aut.smul_def {Γ : BipartiteRibbonGraph.{u}} (f : Γ.Aut) (e : Γ.E) :
    f • e = f.edge e := (rfl)

/-- The action of `Γ.Aut` on `Γ.E` is a multiplicative group action. -/
instance (Γ : BipartiteRibbonGraph.{u}) : MulAction Γ.Aut Γ.E :=
  { one_smul _ := by simp, mul_smul _ _ _ := by simp }

/-- A ribbon graph is *regular* when it is connected and `Γ.Aut` acts transitively on `Γ.E`. -/
def IsRegular (Γ : BipartiteRibbonGraph.{u}) : Prop :=
  Γ.IsConnected ∧ MulAction.IsPretransitive Γ.Aut Γ.E

/-- Unfold `BipartiteRibbonGraph.IsRegular` into connectedness and edge-transitivity. -/
theorem isRegular_iff {Γ : BipartiteRibbonGraph.{u}} :
    Γ.IsRegular ↔ Γ.IsConnected ∧ MulAction.IsPretransitive Γ.Aut Γ.E := Iff.rfl

/-- Every regular bipartite ribbon graph is connected. -/
theorem IsRegular.isConnected {Γ : BipartiteRibbonGraph.{u}} (hΓ : Γ.IsRegular) : Γ.IsConnected :=
  hΓ.1

/-- Regularity of bipartite ribbon graphs is invariant under isomorphism. -/
theorem Iso.isRegular_iff {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) : Γ.IsRegular ↔ Δ.IsRegular :=
  let ψ : Γ.E →ₑ[φ.autMulEquiv] Δ.E := ⟨φ.edge, fun f e ↦ by simp⟩
  and_congr φ.isConnected_iff
    (MulAction.isPretransitive_congr (f := ψ) φ.autMulEquiv.surjective φ.edge.bijective)

/-- Numbering the edges of a bipartite ribbon graph preserves regularity. -/
@[simp] theorem isRegular_toPermutationTriple {n : ℕ} (Γ : BipartiteRibbonGraph.{u})
    (ν : Γ.E ≃ Fin n) : (Γ.toPermutationTriple ν).IsRegular ↔ Γ.IsRegular := by
  let φ : Γ.E →ₑ[Γ.autEquivAutomorphismGroup ν] Fin n :=
    ⟨ν, fun f e ↦ by simp [Aut.smul_def, Subgroup.smul_def, Equiv.Perm.smul_def]⟩
  exact (PermutationTriple.isRegular_iff.trans <| and_congr (Γ.isConnected_toPermutationTriple ν)
    (MulAction.isPretransitive_congr (f := φ) (Γ.autEquivAutomorphismGroup ν).surjective
      ν.bijective).symm).trans isRegular_iff.symm

/-- `Γ` is regular iff it is connected and `Nat.card Γ.Aut = Fintype.card Γ.E`. -/
theorem isRegular_iff_natCard_aut {Γ : BipartiteRibbonGraph.{u}} :
    Γ.IsRegular ↔ Γ.IsConnected ∧ Nat.card Γ.Aut = Fintype.card Γ.E := by
  let ν := Fintype.equivFin Γ.E
  rw [← Γ.isRegular_toPermutationTriple ν, PermutationTriple.isRegular_iff_card_automorphismGroup,
    Γ.isConnected_toPermutationTriple ν, natCard_automorphismGroup_toPermutationTriple]

/-- Passing from a permutation triple to its ribbon graph preserves regularity. -/
@[simp] theorem _root_.TauCeti.PermutationTriple.isRegular_ribbonGraph {n : ℕ}
    (t : PermutationTriple n) : t.ribbonGraph.IsRegular ↔ t.IsRegular := by
  rw [← t.ribbonGraph.isRegular_toPermutationTriple (Equiv.refl (Fin n)),
    t.toPermutationTriple_ribbonGraph]

end TauCeti.BipartiteRibbonGraph
