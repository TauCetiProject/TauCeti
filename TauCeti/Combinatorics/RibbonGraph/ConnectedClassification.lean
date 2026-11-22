/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.ClassInvariants
public import TauCeti.Combinatorics.RibbonGraph.CycleData
public import TauCeti.Combinatorics.RibbonGraph.Genus

/-!
# Connected ribbon graphs and connected permutation triples

Isomorphism classes of connected finite bipartite ribbon graphs with `n` edges are equivalent to
`TauCeti.ConnectedIsoClass n`. These graphs are the combinatorial dessins d'enfants, so counting
their isomorphism classes reduces to counting connected triples. The equivalence restricts
`TauCeti.BipartiteRibbonGraph.isoClassEquiv`, with the same comparison of automorphism groups
given by `TauCeti.BipartiteRibbonGraph.autEquivAutomorphismGroup`.

The equations `connectedIsoClassEquiv_mk` and `connectedIsoClassEquiv_symm_mk` describe the
classification on representatives. Edge numberings are arbitrary, and the inverse uses universe
lifting so that graphs in any universe are classified. In degree zero both carriers are empty,
since connectedness requires a nonempty edge set, and in degree one both have a unique class.

The restriction uses Mathlib's `Equiv.subtypeQuotientEquivQuotientSubtype` to commute invariant
subtypes with quotients. The degree partitions (`cycleData`), Euler characteristic, genus,
automorphism-group order, and regularity descend to `Quotient (connectedIsoSetoid n)` and match
those of `TauCeti.ConnectedIsoClass n` along `connectedIsoClassEquiv`.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.2.
-/

open Equiv

public section

namespace TauCeti.BipartiteRibbonGraph

universe u

variable {n : ℕ}

/-! ### Classification of connected ribbon graphs -/

/-- Isomorphism of connected bipartite ribbon graphs with `n` edges. The inner subtype records
the edge count; the outer subtype records connectedness. -/
def connectedIsoSetoid (n : ℕ) :
    Setoid {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.val.IsConnected} :=
  (isoSetoid n).comap Subtype.val

/-- Two connected ribbon graphs have the same quotient class exactly when they are isomorphic. -/
@[simp]
theorem connectedIsoSetoid_mk_eq_mk_iff
    {Γ Δ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.val.IsConnected}} :
    Quotient.mk (connectedIsoSetoid n) Γ = Quotient.mk (connectedIsoSetoid n) Δ ↔
      Nonempty (Γ.val.val.Iso Δ.val.val) :=
  Quotient.eq.trans isoSetoid_r

/-- Isomorphism classes of connected ribbon graphs are the isomorphism classes of connected
permutation triples. -/
noncomputable def connectedIsoClassEquiv (n : ℕ) :
    Quotient (connectedIsoSetoid.{u} n) ≃ ConnectedIsoClass n :=
  ((Equiv.subtypeQuotientEquivQuotientSubtype
    (fun Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} => Γ.val.IsConnected)
    (fun c => (isoClassEquiv n c).IsConnected)
    (fun Γ => by
      rw [isoClassEquiv_mk_equivFinOfCardEq, PermutationTriple.IsoClass.isConnected_mk,
        isConnected_toPermutationTriple])
    (fun _ _ => Iff.rfl)).symm.trans
      (isoClassEquiv n).subtypeEquivOfSubtype).trans (ConnectedIsoClass.equivSubtype n).symm

/-- A connected graph determines the connected triple class of any numbering of its edges. -/
theorem connectedIsoClassEquiv_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.val.IsConnected})
    (ν : Γ.val.val.E ≃ Fin n) :
    connectedIsoClassEquiv n (Quotient.mk (connectedIsoSetoid n) Γ) =
      ConnectedIsoClass.mk ⟨Γ.val.val.toPermutationTriple ν,
        (Γ.val.val.isConnected_toPermutationTriple ν).2 Γ.property⟩ := by
  apply (ConnectedIsoClass.equivSubtype n).injective
  simp only [connectedIsoClassEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    ConnectedIsoClass.equivSubtype_mk]
  exact Subtype.ext (isoClassEquiv_mk Γ.val ν)

/-- The connected graph class evaluated using the canonical numbering of its edges. -/
@[simp]
theorem connectedIsoClassEquiv_mk_equivFinOfCardEq
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.val.IsConnected}) :
    connectedIsoClassEquiv n (Quotient.mk (connectedIsoSetoid n) Γ) =
      ConnectedIsoClass.mk ⟨Γ.val.val.toPermutationTriple (Fintype.equivFinOfCardEq Γ.val.property),
        (Γ.val.val.isConnected_toPermutationTriple _).2 Γ.property⟩ :=
  connectedIsoClassEquiv_mk Γ _

/-- Forgetting connectedness commutes with the classification of all ribbon graphs. -/
@[simp]
theorem forget_connectedIsoClassEquiv (c : Quotient (connectedIsoSetoid.{u} n)) :
    (connectedIsoClassEquiv n c).forget =
      isoClassEquiv n (Quotient.map (sa := connectedIsoSetoid n) (sb := isoSetoid n) Subtype.val
        (fun _ _ h => isoSetoid_r.mpr
          (connectedIsoSetoid_mk_eq_mk_iff.mp (Quotient.sound h))) c) := by
  induction c using Quotient.inductionOn with
  | _ Γ => simp

/-- The connected class of a triple determines the class of its universe-lifted ribbon graph. -/
@[simp]
theorem connectedIsoClassEquiv_symm_mk (t : ConnectedTriple n) :
    (connectedIsoClassEquiv.{u} n).symm (ConnectedIsoClass.mk t) =
      Quotient.mk (connectedIsoSetoid n)
        ⟨⟨t.val.ribbonGraph.ulift, t.val.ribbonGraph.card_E_ulift.trans t.val.card_E_ribbonGraph⟩,
          t.val.ribbonGraph.uliftIso.isConnected_iff.mpr
            (t.val.isConnected_ribbonGraph.mpr t.property)⟩ := by
  apply (connectedIsoClassEquiv n).injective
  rw [Equiv.apply_symm_apply, connectedIsoClassEquiv_mk _
    (t.val.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n)))]
  symm
  apply ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr
  simpa only [PermutationTriple.toPermutationTriple_ribbonGraph] using
    equivalent_toPermutationTriple_of_iso t.val.ribbonGraph.uliftIso
      (t.val.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n))) (Equiv.refl (Fin n))

/-- There are no connected bipartite ribbon graphs with zero edges. -/
instance : IsEmpty (Quotient (connectedIsoSetoid.{u} 0)) := (connectedIsoClassEquiv.{u} 0).isEmpty

/-- Up to isomorphism there is a unique connected bipartite ribbon graph with one edge. -/
noncomputable instance : Unique (Quotient (connectedIsoSetoid.{u} 1)) :=
  (connectedIsoClassEquiv.{u} 1).unique

/-! ### Invariants of connected ribbon-graph classes -/

section Invariants

variable (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.val.IsConnected})
  (c : Quotient (connectedIsoSetoid.{u} n))

/-- The degree-partition triple `(λ₀, λ₁, λ∞)` of a class of connected ribbon graphs. -/
def connectedCycleData (n : ℕ) :
    Quotient (connectedIsoSetoid.{u} n) → Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  Quotient.lift (fun Γ => Γ.val.val.cycleData) fun _ _ h => (isoSetoid_r.1 h).elim Iso.cycleData_eq

/-- Evaluating `connectedCycleData` on the class of `Γ` gives `Γ.val.val.cycleData`. -/
@[simp] theorem connectedCycleData_mk : connectedCycleData n ⟦Γ⟧ = Γ.val.val.cycleData := (rfl)

/-- `connectedIsoClassEquiv` matches `connectedCycleData` with `ConnectedIsoClass.cycleData`. -/
@[simp] theorem cycleData_connectedIsoClassEquiv :
    (connectedIsoClassEquiv n c).cycleData = connectedCycleData n c :=
  Quotient.inductionOn c fun _ => by simp

/-- The Euler characteristic `|B| + |W| + F - |E|` of a class of connected ribbon graphs. -/
def connectedEulerChar (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℤ :=
  Quotient.lift (fun Γ => Γ.val.val.eulerChar) fun _ _ h => (isoSetoid_r.1 h).elim Iso.eulerChar_eq

/-- Evaluating `connectedEulerChar` on the class of `Γ` gives `Γ.val.val.eulerChar`. -/
@[simp] theorem connectedEulerChar_mk : connectedEulerChar n ⟦Γ⟧ = Γ.val.val.eulerChar := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the Euler characteristic. -/
@[simp] theorem eulerChar_connectedIsoClassEquiv :
    (connectedIsoClassEquiv n c).eulerChar = connectedEulerChar n c :=
  Quotient.inductionOn c fun _ => by simp

/-- The combinatorial genus `((2 - χ) / 2).toNat` of a class of connected ribbon graphs. -/
def connectedGenus (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun Γ => Γ.val.val.genus) fun _ _ h => (isoSetoid_r.1 h).elim fun φ => φ.genus_eq

/-- Evaluating `connectedGenus` on the class of `Γ` gives `Γ.val.val.genus`. -/
@[simp] theorem connectedGenus_mk : connectedGenus n ⟦Γ⟧ = Γ.val.val.genus := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the combinatorial genus. -/
@[simp] theorem genus_connectedIsoClassEquiv :
    (connectedIsoClassEquiv n c).genus = connectedGenus n c :=
  Quotient.inductionOn c fun _ => by simp

/-- The cardinality of the automorphism group of a class of connected ribbon graphs. -/
noncomputable def connectedNatCardAut (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun Γ => Nat.card Γ.val.val.Aut) fun _ _ h =>
    (isoSetoid_r.1 h).elim Iso.natCard_aut_eq

/-- Evaluating `connectedNatCardAut` on the class of `Γ` gives `Nat.card Γ.val.val.Aut`. -/
@[simp] theorem connectedNatCardAut_mk : connectedNatCardAut n ⟦Γ⟧ = Nat.card Γ.val.val.Aut := (rfl)

/-- The classification `connectedIsoClassEquiv` preserves the automorphism-group order. -/
@[simp] theorem natCardAutomorphismGroup_connectedIsoClassEquiv :
    (connectedIsoClassEquiv n c).natCardAutomorphismGroup = connectedNatCardAut n c :=
  Quotient.inductionOn c fun _ => by simp

/-- Regularity on isomorphism classes of connected bipartite ribbon graphs. -/
def ConnectedIsRegular (n : ℕ) : Quotient (connectedIsoSetoid.{u} n) → Prop :=
  Quotient.lift (fun Γ => Γ.val.val.IsRegular) fun _ _ h =>
    (isoSetoid_r.1 h).elim fun φ => propext φ.isRegular_iff

/-- Evaluating `ConnectedIsRegular` on the class of `Γ` recovers `Γ.val.val.IsRegular`. -/
@[simp] theorem connectedIsRegular_mk : ConnectedIsRegular n ⟦Γ⟧ ↔ Γ.val.val.IsRegular := Iff.rfl

/-- The classification `connectedIsoClassEquiv` preserves regularity. -/
@[simp] theorem isRegular_connectedIsoClassEquiv :
    (connectedIsoClassEquiv n c).IsRegular ↔ ConnectedIsRegular n c :=
  Quotient.inductionOn c fun _ => by simp

end Invariants

end TauCeti.BipartiteRibbonGraph
