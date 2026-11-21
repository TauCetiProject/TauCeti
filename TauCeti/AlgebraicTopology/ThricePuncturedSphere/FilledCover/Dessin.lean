/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Genus
public import TauCeti.Combinatorics.RibbonGraph.ConnectedClassification

/-!
# Dessin classification and invariant comparisons for three-point covers

This file connects isomorphism classes of `TopBranchedCover.{0} n` and `AnalyticBelyiPair.{0}`
with connected bipartite ribbon graphs `Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n)`.
It defines `equivConnectedRibbonGraph` and `isoClassEquivConnectedRibbonGraph`, proves diagram
commutativity, realises every connected dessin (`exists_iso_of_connectedRibbonGraph`), and matches
cycle data, Euler characteristic, genus, automorphism/deck groups, and regularity with dessins.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), LMS Lecture Note Series 242, CUP, 1997.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, CUP, 2012, §1.2.7, §2.7 and §4.2 (Theorem 4.27).
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, EMS 141, 2004.
-/

public noncomputable section

open Equiv Equiv.Perm Function

namespace TauCeti

open ThricePuncturedSphere RiemannSurface
open BipartiteRibbonGraph (cycleData_connectedIsoClassEquiv eulerChar_connectedIsoClassEquiv
  genus_connectedIsoClassEquiv natCardAutomorphismGroup_connectedIsoClassEquiv
  isRegular_connectedIsoClassEquiv)

universe u

/-! ### Ribbon-graph classification equivalences and diagram comparisons -/

namespace TopBranchedCover.IsoClass

/-- **Topological branched covers are classified by connected bipartite ribbon graphs.** -/
def equivConnectedRibbonGraph (n : ℕ) :
    IsoClass.{0} n ≃ Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) :=
  (equivConnectedIsoClass n).trans (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n).symm

/-- Composing `equivConnectedRibbonGraph` with `connectedIsoClassEquiv` recovers
`equivConnectedIsoClass`. -/
@[simp] theorem connectedIsoClassEquiv_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n (equivConnectedRibbonGraph.{u} n c) =
      equivConnectedIsoClass n c := by simp [equivConnectedRibbonGraph]

end TopBranchedCover.IsoClass

namespace AnalyticBelyiPair

/-- **Analytic Belyi pairs are classified by dessins d'enfants (connected ribbon graphs).** -/
def isoClassEquivConnectedRibbonGraph (n : ℕ) :
    Quotient (isoSetoid.{0} n) ≃ Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) :=
  (isoClassEquivConnectedIsoClass n).trans (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n).symm

/-- Forgetting the complex structure commutes with classification by connected ribbon graphs. -/
theorem isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedRibbonGraph (n : ℕ) :
    (isoClassEquivTopBranchedCoverIsoClass n).trans
        (TopBranchedCover.IsoClass.equivConnectedRibbonGraph.{u} n) =
      isoClassEquivConnectedRibbonGraph.{u} n := by
  rw [TopBranchedCover.IsoClass.equivConnectedRibbonGraph, isoClassEquivConnectedRibbonGraph,
    ← Equiv.trans_assoc, isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedIsoClass]

/-- Pointwise form of `isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedRibbonGraph`. -/
@[simp] theorem equivConnectedRibbonGraph_toTopBranchedCoverIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    TopBranchedCover.IsoClass.equivConnectedRibbonGraph.{u} n (toTopBranchedCoverIsoClass n P) =
      isoClassEquivConnectedRibbonGraph.{u} n P := by
  simpa using Equiv.congr_fun
    (isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedRibbonGraph.{u} n) P

/-- Composing `isoClassEquivConnectedRibbonGraph` with `connectedIsoClassEquiv` recovers
`isoClassEquivConnectedIsoClass`. -/
theorem isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv (n : ℕ) :
    (isoClassEquivConnectedRibbonGraph.{u} n).trans
        (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n) =
      isoClassEquivConnectedIsoClass n := by ext _; simp [isoClassEquivConnectedRibbonGraph]

/-- Pointwise form of `isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv`. -/
@[simp] theorem connectedIsoClassEquiv_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n
        (isoClassEquivConnectedRibbonGraph.{u} n P) = isoClassEquivConnectedIsoClass n P :=
  Equiv.congr_fun (isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv.{u} n) P

/-- On `⟦P⟧`, `isoClassEquivConnectedRibbonGraph` gives the lifted ribbon graph of its monodromy. -/
theorem isoClassEquivConnectedRibbonGraph_mk {n : ℕ}
    (P : {P : AnalyticBelyiPair.{0} // degree P.β = n}) (ν : P.1.restrict ⁻¹' {basePt} ≃ Fin n) :
    isoClassEquivConnectedRibbonGraph.{u} n ⟦P⟧ =
      Quotient.mk (BipartiteRibbonGraph.connectedIsoSetoid.{u} n)
        ⟨⟨(P.1.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.ulift,
            (P.1.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.card_E_ulift.trans
              (P.1.isCoveringMap_restrict.monodromyTriple ν).card_E_ribbonGraph⟩,
          (P.1.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.uliftIso.isConnected_iff.2
            ((P.1.isCoveringMap_restrict.monodromyTriple ν).isConnected_ribbonGraph.2
              (P.1.isCoveringMap_restrict.isConnected_monodromyTriple ν))⟩ := by
  rw [isoClassEquivConnectedRibbonGraph, Equiv.trans_apply, isoClassEquivConnectedIsoClass_mk P ν,
    BipartiteRibbonGraph.connectedIsoClassEquiv_symm_mk]

/-- **Analytic realisation of every connected dessin**, unique up to isomorphism. -/
theorem exists_iso_of_connectedRibbonGraph {n : ℕ} (Γ : BipartiteRibbonGraph.{u})
    (hcard : Fintype.card Γ.E = n) (hconn : Γ.IsConnected) :
    ∃ P : AnalyticBelyiPair.{0}, degree P.β = n ∧
      (∀ ν : P.restrict ⁻¹' {basePt} ≃ Fin n,
        Nonempty ((P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Iso Γ)) ∧
      ∀ (Q : AnalyticBelyiPair.{0}) (νQ : Q.restrict ⁻¹' {basePt} ≃ Fin n),
        Nonempty ((Q.isCoveringMap_restrict.monodromyTriple νQ).ribbonGraph.Iso Γ) →
          Nonempty (Q.Iso P) := by
  obtain ⟨⟨P, hdeg⟩, hP⟩ := Quotient.exists_rep ((isoClassEquivConnectedRibbonGraph.{u} n).symm
    (Quotient.mk (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) ⟨⟨Γ, hcard⟩, hconn⟩))
  have hg : isoClassEquivConnectedRibbonGraph.{u} n ⟦⟨P, hdeg⟩⟧ =
      Quotient.mk (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) ⟨⟨Γ, hcard⟩, hconn⟩ := by
    rw [hP, Equiv.apply_symm_apply]
  refine ⟨P, hdeg, fun ν ↦ ?_, fun Q νQ ⟨φ⟩ ↦ ?_⟩
  · rw [isoClassEquivConnectedRibbonGraph_mk ⟨P, hdeg⟩ ν,
      BipartiteRibbonGraph.connectedIsoSetoid_mk_eq_mk_iff] at hg
    exact hg.map fun ψ ↦
      (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.uliftIso.symm.trans ψ
  · have hQdeg := Q.degree_β_eq_of_restrict_preimage_singleton_equiv νQ
    refine isoSetoid_r.1 (Quotient.exact (a := ⟨Q, hQdeg⟩) (b := ⟨P, hdeg⟩)
      ((isoClassEquivConnectedRibbonGraph.{u} n).injective ?_))
    rw [hg, isoClassEquivConnectedRibbonGraph_mk ⟨Q, hQdeg⟩ νQ,
      BipartiteRibbonGraph.connectedIsoSetoid_mk_eq_mk_iff]
    exact ⟨(Q.isCoveringMap_restrict.monodromyTriple νQ).ribbonGraph.uliftIso.trans φ⟩

/-- **Two analytic Belyi pairs are isomorphic if and only if their dessins are isomorphic.** -/
theorem nonempty_iso_iff_nonempty_ribbonGraph_iso {P Q : AnalyticBelyiPair.{0}} {n m : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) (ν' : Q.restrict ⁻¹' {basePt} ≃ Fin m) :
    Nonempty (P.Iso Q) ↔
      Nonempty ((P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Iso
        (Q.isCoveringMap_restrict.monodromyTriple ν').ribbonGraph) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨φ⟩ ↦ ?_⟩
  · obtain rfl : n = m := (P.degree_β_eq_of_restrict_preimage_singleton_equiv ν).symm.trans
      (e.degree_eq.trans (Q.degree_β_eq_of_restrict_preimage_singleton_equiv ν'))
    exact PermutationTriple.nonempty_iso_ribbonGraph_iff.2
      (PermutationTriple.IsoClass.mk_eq_mk_iff.1
        ((nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν').1 ⟨e⟩))
  · obtain rfl : n = m := by simpa using Fintype.card_congr φ.edge
    exact (nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν').2
      (PermutationTriple.IsoClass.mk_eq_mk_iff.2
        (PermutationTriple.nonempty_iso_ribbonGraph_iff.1 ⟨φ⟩))

end AnalyticBelyiPair

/-! ### Matching degree partitions, Euler characteristic, and genus with dessins -/

namespace TopBranchedCover.IsoClass

/-- `equivConnectedRibbonGraph` matches `ramificationPartitions` with `connectedCycleData`. -/
@[simp] theorem connectedCycleData_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedCycleData n (equivConnectedRibbonGraph.{u} n c) =
      c.ramificationPartitions := by simp [← cycleData_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the Euler characteristic. -/
@[simp] theorem connectedEulerChar_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedEulerChar n (equivConnectedRibbonGraph.{u} n c) =
      c.eulerChar := by simp [← eulerChar_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the genus. -/
@[simp] theorem connectedGenus_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedGenus n (equivConnectedRibbonGraph.{u} n c) = c.genus := by
  rw [← genus_connectedIsoClassEquiv]; simp

end TopBranchedCover.IsoClass

namespace AnalyticBelyiPair

/-- `isoClassEquivConnectedRibbonGraph` matches `isoClassRamificationPartitions` with
`connectedCycleData`. -/
@[simp] theorem connectedCycleData_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedCycleData n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassRamificationPartitions n P := by simp [← cycleData_connectedIsoClassEquiv]

/-- `isoClassEquivConnectedRibbonGraph` matches the topological and dessin Euler characteristics. -/
@[simp] theorem connectedEulerChar_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedEulerChar n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassEulerChar n P := by simp [← eulerChar_connectedIsoClassEquiv]

/-- `isoClassEquivConnectedRibbonGraph` matches the topological genus with the dessin genus. -/
@[simp] theorem connectedGenus_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedGenus n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassGenus n P := by simp [← genus_connectedIsoClassEquiv]

end AnalyticBelyiPair

/-! ### Automorphism groups, deck groups, and regularity on dessins -/

namespace TopBranchedCover

/-- **The deck group of `X` is the automorphism group of the ribbon graph of its monodromy.** -/
def deckMulEquivRibbonGraphAut {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    deck X.π ≃* (X.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  (X.deckMulEquivAutomorphismGroup ν).trans
    (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroupMulEquivRibbonGraphAut

/-- On edges (`Fin n`), `deckMulEquivRibbonGraphAut` acts by the induced permutation on the fibre
over `1/2`. -/
@[simp] theorem deckMulEquivRibbonGraphAut_apply_edge {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) (φ : deck X.π) (i : Fin n) :
    (X.deckMulEquivRibbonGraphAut ν φ).edge i = ν (φ • ν.symm i) :=
  (Equiv.congr_fun (PermutationTriple.automorphismGroupMulEquivRibbonGraphAut_edge _ _) i).trans
    (X.coe_deckMulEquivAutomorphismGroup_apply ν φ i)

/-- The deck transformation attached to a ribbon-graph automorphism `f` sends `ν.symm i` to
`ν.symm (f.edge i)`. -/
@[simp] theorem deckMulEquivRibbonGraphAut_symm_smul {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n)
    (f : (X.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    (X.deckMulEquivRibbonGraphAut ν).symm f • ν.symm i = ν.symm (f.edge i) := by
  rw [deckMulEquivRibbonGraphAut, MulEquiv.symm_trans_apply,
    X.deckMulEquivAutomorphismGroup_symm_smul]
  exact congrArg ν.symm (Equiv.congr_fun
    (PermutationTriple.coe_automorphismGroupMulEquivRibbonGraphAut_symm_apply _ f) i)

/-- `IsoClass.equivConnectedRibbonGraph` preserves the order of the deck/automorphism group. -/
@[simp] theorem IsoClass.connectedNatCardAut_equivConnectedRibbonGraph {n : ℕ}
    (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedNatCardAut n (equivConnectedRibbonGraph.{u} n c) =
      c.natCardDeck := by simp [← natCardAutomorphismGroup_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves regularity. -/
@[simp] theorem IsoClass.connectedIsRegular_equivConnectedRibbonGraph {n : ℕ}
    (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.ConnectedIsRegular n (equivConnectedRibbonGraph.{u} n c) ↔
      c.IsRegular := by simp [← isRegular_connectedIsoClassEquiv]

end TopBranchedCover

namespace AnalyticBelyiPair

/-- **The automorphism group of `P` is the automorphism group of its dessin.** -/
def isoMulEquivRibbonGraphAut (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.Iso P ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  (P.isoMulEquivAutomorphismGroup ν).trans
    (P.isCoveringMap_restrict.monodromyTriple ν).automorphismGroupMulEquivRibbonGraphAut

/-- On edges (`Fin n`), `isoMulEquivRibbonGraphAut` sends `i` to `ν (e • ν.symm i)`. -/
@[simp] theorem isoMulEquivRibbonGraphAut_apply_edge (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) (e : P.Iso P) (i : Fin n) :
    (P.isoMulEquivRibbonGraphAut ν e).edge i = ν (e • ν.symm i) :=
  (Equiv.congr_fun (PermutationTriple.automorphismGroupMulEquivRibbonGraphAut_edge _ _) i).trans
    (P.coe_isoMulEquivAutomorphismGroup_apply ν e i)

/-- The automorphism of `P` attached to `f` sends `ν.symm i` to `ν.symm (f.edge i)`. -/
@[simp] theorem isoMulEquivRibbonGraphAut_symm_smul (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)
    (f : (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    (P.isoMulEquivRibbonGraphAut ν).symm f • ν.symm i = ν.symm (f.edge i) := by
  rw [isoMulEquivRibbonGraphAut, MulEquiv.symm_trans_apply,
    P.isoMulEquivAutomorphismGroup_symm_smul]
  exact congrArg ν.symm (Equiv.congr_fun
    (PermutationTriple.coe_automorphismGroupMulEquivRibbonGraphAut_symm_apply _ f) i)

/-- **The deck group of `P.β` is the automorphism group of its dessin.** -/
def deckMulEquivRibbonGraphAut (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    deck P.β ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  P.isoMulEquivDeck.symm.trans (P.isoMulEquivRibbonGraphAut ν)

/-- On edges (`Fin n`), `deckMulEquivRibbonGraphAut` acts via `isoMulEquivDeck.symm` on the fibre
over `1/2`. -/
@[simp] theorem deckMulEquivRibbonGraphAut_apply_edge (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) (φ : deck P.β) (i : Fin n) :
    (P.deckMulEquivRibbonGraphAut ν φ).edge i = ν (P.isoMulEquivDeck.symm φ • ν.symm i) :=
  P.isoMulEquivRibbonGraphAut_apply_edge ν (P.isoMulEquivDeck.symm φ) i

/-- The deck transformation of `P.β` attached to `f` sends `ν.symm i` to `ν.symm (f.edge i)`. -/
@[simp] theorem coe_deckMulEquivRibbonGraphAut_symm_apply (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)
    (f : (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    ((P.deckMulEquivRibbonGraphAut ν).symm f : P.X ≃ₜ P.X) (ν.symm i) =
      (ν.symm (f.edge i) : P.X) := by
  rw [deckMulEquivRibbonGraphAut, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    congrFun (P.coe_isoMulEquivDeck_apply _) _, ← Iso.coe_smul basePt _ (ν.symm i),
    P.isoMulEquivRibbonGraphAut_symm_smul ν f i]

/-- `P` is regular if and only if the ribbon graph of its monodromy triple is regular. -/
theorem isRegular_iff_ribbonGraph {P : AnalyticBelyiPair.{u}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.IsRegular ↔ (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.IsRegular := by
  rw [isRegular_iff_monodromyTriple ν, PermutationTriple.isRegular_ribbonGraph]

/-- `isoClassEquivConnectedRibbonGraph` matches `isoClassNatCardAut` with `connectedNatCardAut`. -/
@[simp] theorem connectedNatCardAut_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedNatCardAut n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassNatCardAut n P := by simp [← natCardAutomorphismGroup_connectedIsoClassEquiv]

/-- `isoClassEquivConnectedRibbonGraph` matches `IsoClassIsRegular` with `ConnectedIsRegular`. -/
@[simp] theorem connectedIsRegular_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.ConnectedIsRegular n (isoClassEquivConnectedRibbonGraph.{u} n P) ↔
      IsoClassIsRegular n P := by simp [← isRegular_connectedIsoClassEquiv]

end AnalyticBelyiPair

end TauCeti
