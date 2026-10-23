/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Classification
public import TauCeti.Combinatorics.PermutationTriple.IsoClass

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
since connectedness requires a nonempty edge set.

The restriction uses Mathlib's `Equiv.subtypeQuotientEquivQuotientSubtype` to commute invariant
subtypes with quotients.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.2.
-/

public section

namespace TauCeti.BipartiteRibbonGraph

universe u

variable {n : ℕ}

/-- Isomorphism of connected bipartite ribbon graphs with `n` edges. The inner subtype records
the edge count; the outer subtype records connectedness. -/
def connectedIsoSetoid (n : ℕ) :
    Setoid {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected} :=
  (isoSetoid n).comap Subtype.val

/-- Two connected ribbon graphs have the same quotient class exactly when they are isomorphic. -/
@[simp]
theorem connectedIsoSetoid_mk_eq_mk_iff
    {Γ Δ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}} :
    Quotient.mk (connectedIsoSetoid n) Γ = Quotient.mk (connectedIsoSetoid n) Δ ↔
      Nonempty (Γ.1.1.Iso Δ.1.1) :=
  Quotient.eq.trans isoSetoid_r

/-- Isomorphism classes of connected ribbon graphs are the isomorphism classes of connected
permutation triples. -/
noncomputable def connectedIsoClassEquiv (n : ℕ) :
    Quotient (connectedIsoSetoid.{u} n) ≃ ConnectedIsoClass n :=
  ((Equiv.subtypeQuotientEquivQuotientSubtype
    (fun Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} => Γ.1.IsConnected)
    (fun c => (isoClassEquiv n c).IsConnected)
    (fun Γ => by
      rw [isoClassEquiv_mk_equivFinOfCardEq, PermutationTriple.IsoClass.isConnected_mk,
        isConnected_toPermutationTriple])
    (fun _ _ => Iff.rfl)).symm.trans
      (isoClassEquiv n).subtypeEquivOfSubtype).trans (ConnectedIsoClass.equivSubtype n).symm

/-- A connected graph determines the connected triple class of any numbering of its edges. -/
theorem connectedIsoClassEquiv_mk
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected})
    (ν : Γ.1.1.E ≃ Fin n) :
    connectedIsoClassEquiv n (Quotient.mk (connectedIsoSetoid n) Γ) =
      ConnectedIsoClass.mk ⟨Γ.1.1.toPermutationTriple ν,
        (Γ.1.1.isConnected_toPermutationTriple ν).2 Γ.2⟩ := by
  apply (ConnectedIsoClass.equivSubtype n).injective
  simp only [connectedIsoClassEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    ConnectedIsoClass.equivSubtype_mk]
  exact Subtype.ext (isoClassEquiv_mk Γ.1 ν)

/-- The connected graph class evaluated using the canonical numbering of its edges. -/
@[simp]
theorem connectedIsoClassEquiv_mk_equivFinOfCardEq
    (Γ : {Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} // Γ.1.IsConnected}) :
    connectedIsoClassEquiv n (Quotient.mk (connectedIsoSetoid n) Γ) =
      ConnectedIsoClass.mk ⟨Γ.1.1.toPermutationTriple (Fintype.equivFinOfCardEq Γ.1.2),
        (Γ.1.1.isConnected_toPermutationTriple _).2 Γ.2⟩ :=
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
        ⟨⟨t.1.ribbonGraph.ulift, t.1.ribbonGraph.card_E_ulift.trans t.1.card_E_ribbonGraph⟩,
          t.1.ribbonGraph.uliftIso.isConnected_iff.mpr
            (t.1.isConnected_ribbonGraph.mpr t.2)⟩ := by
  apply (connectedIsoClassEquiv n).injective
  rw [Equiv.apply_symm_apply, connectedIsoClassEquiv_mk _
    (t.1.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n)))]
  symm
  apply ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr
  simpa only [PermutationTriple.toPermutationTriple_ribbonGraph] using
    equivalent_toPermutationTriple_of_iso t.1.ribbonGraph.uliftIso
      (t.1.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n))) (Equiv.refl (Fin n))

end TauCeti.BipartiteRibbonGraph
