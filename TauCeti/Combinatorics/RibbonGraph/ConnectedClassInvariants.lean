/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.ClassInvariants
public import TauCeti.Combinatorics.RibbonGraph.ConnectedClassification
public import TauCeti.Combinatorics.RibbonGraph.Genus

/-!
# Invariants of connected ribbon-graph classes

Descends `cycleData`, `eulerChar`, `genus`, `Nat.card Aut`, and `IsRegular` to
`Quotient (BipartiteRibbonGraph.connectedIsoSetoid n)` and matches them with `ConnectedIsoClass`.
-/

public section

namespace TauCeti.BipartiteRibbonGraph

universe u

private def clift {α : Sort*} (n : ℕ)
    (f : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.val.IsConnected} → α)
    (hf : ∀ {Γ Δ}, Γ.val.val.Iso Δ.val.val → f Γ = f Δ) : Quotient (connectedIsoSetoid.{u} n) → α :=
  Quotient.lift f fun _ _ h => (connectedIsoSetoid_mk_eq_mk_iff.1 (Quotient.sound h)).elim hf

variable {n : ℕ}
  (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.val.IsConnected})
  (c : Quotient (connectedIsoSetoid.{u} n))

/-- The degree-partition triple `(λ₀, λ₁, λ∞)` of a class of connected ribbon graphs. -/
def connectedCycleData (n : ℕ) :
    Quotient (connectedIsoSetoid.{u} n) → Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  clift n (fun Γ => Γ.val.val.cycleData) Iso.cycleData_eq

/-- Evaluating `connectedCycleData` on the class of `Γ` gives `Γ.val.val.cycleData`. -/
@[simp] theorem connectedCycleData_mk : connectedCycleData n ⟦Γ⟧ = Γ.val.val.cycleData := (rfl)

/-- `connectedIsoClassEquiv` matches `connectedCycleData` with `ConnectedIsoClass.cycleData`. -/
@[simp] theorem cycleData_connectedIsoClassEquiv : (connectedIsoClassEquiv n c).cycleData =
    connectedCycleData n c := Quotient.inductionOn c fun _ => by simp

/-- The Euler characteristic `|B| + |W| + F - |E|` of a class of connected ribbon graphs. -/
def connectedEulerChar (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℤ :=
  clift n (fun Γ => Γ.val.val.eulerChar) Iso.eulerChar_eq

/-- Evaluating `connectedEulerChar` on the class of `Γ` gives `Γ.val.val.eulerChar`. -/
@[simp] theorem connectedEulerChar_mk : connectedEulerChar n ⟦Γ⟧ = Γ.val.val.eulerChar := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the Euler characteristic. -/
@[simp] theorem eulerChar_connectedIsoClassEquiv : (connectedIsoClassEquiv n c).eulerChar =
    connectedEulerChar n c := Quotient.inductionOn c fun _ => by simp

/-- The combinatorial genus `((2 - χ) / 2).toNat` of a class of connected ribbon graphs. -/
def connectedGenus (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℕ :=
  clift n (fun Γ => Γ.val.val.genus) fun φ => φ.genus_eq

/-- Evaluating `connectedGenus` on the class of `Γ` gives `Γ.val.val.genus`. -/
@[simp] theorem connectedGenus_mk : connectedGenus n ⟦Γ⟧ = Γ.val.val.genus := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the combinatorial genus. -/
@[simp] theorem genus_connectedIsoClassEquiv : (connectedIsoClassEquiv n c).genus =
    connectedGenus n c := Quotient.inductionOn c fun _ => by simp

/-- The cardinality of the automorphism group of a class of connected ribbon graphs. -/
noncomputable def connectedNatCardAut (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℕ :=
  clift n (fun Γ => Nat.card Γ.val.val.Aut) Iso.natCard_aut_eq

/-- Evaluating `connectedNatCardAut` on the class of `Γ` gives `Nat.card Γ.val.val.Aut`. -/
@[simp] theorem connectedNatCardAut_mk : connectedNatCardAut n ⟦Γ⟧ = Nat.card Γ.val.val.Aut := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the automorphism-group order. -/
@[simp] theorem natCardAutomorphismGroup_connectedIsoClassEquiv :
    (connectedIsoClassEquiv n c).natCardAutomorphismGroup = connectedNatCardAut n c :=
  Quotient.inductionOn c fun _ => by simp

/-- Regularity on isomorphism classes of connected bipartite ribbon graphs. -/
def ConnectedIsRegular (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → Prop :=
  clift n (fun Γ => Γ.val.val.IsRegular) fun φ => propext φ.isRegular_iff

/-- Evaluating `ConnectedIsRegular` on the class of `Γ` recovers `Γ.val.val.IsRegular`. -/
@[simp] theorem connectedIsRegular_mk : ConnectedIsRegular n ⟦Γ⟧ ↔ Γ.val.val.IsRegular := Iff.rfl

/-- The classification `connectedIsoClassEquiv` preserves regularity. -/
@[simp] theorem isRegular_connectedIsoClassEquiv : (connectedIsoClassEquiv n c).IsRegular ↔
    ConnectedIsRegular n c := Quotient.inductionOn c fun _ => by simp

end TauCeti.BipartiteRibbonGraph
