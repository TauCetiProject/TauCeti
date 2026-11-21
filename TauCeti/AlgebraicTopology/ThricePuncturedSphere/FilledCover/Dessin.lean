/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.AnalyticBelyiPair
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.TopBranchedCover.Dessin

/-!
# Dessin classification and invariant comparisons for three-point covers

Connects isomorphism classes of `TopBranchedCover.{0} n` and `AnalyticBelyiPair.{0}` with connected
bipartite ribbon graphs `Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n)`, proves diagram
commutativity and dessin realization (`exists_iso_of_connectedRibbonGraph`), and matches cycle data,
automorphism/deck groups, and regularity with dessins.
-/

public noncomputable section

open Equiv Equiv.Perm Function

namespace TauCeti

open ThricePuncturedSphere RiemannSurface BipartiteRibbonGraph
open PermutationTriple (nonempty_iso_ribbonGraph_iff)

universe u

/-! ### Ribbon-graph classification equivalences and diagram comparisons -/

namespace TopBranchedCover.IsoClass

/-- **Topological branched covers are classified by connected bipartite ribbon graphs.** -/
def equivConnectedRibbonGraph (n : ℕ) : IsoClass.{0} n ≃ Quotient (connectedIsoSetoid.{u} n) :=
  (equivConnectedIsoClass n).trans (connectedIsoClassEquiv.{u} n).symm

/-- Composing `equivConnectedRibbonGraph` with `connectedIsoClassEquiv` recovers
`equivConnectedIsoClass`. -/
@[simp] theorem connectedIsoClassEquiv_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    connectedIsoClassEquiv.{u} n (equivConnectedRibbonGraph.{u} n c) =
      equivConnectedIsoClass n c := by simp [equivConnectedRibbonGraph]

end TopBranchedCover.IsoClass

namespace AnalyticBelyiPair

/-- **Analytic Belyi pairs are classified by dessins d'enfants (connected ribbon graphs).** -/
def isoClassEquivConnectedRibbonGraph (n : ℕ) :
    Quotient (isoSetoid.{0} n) ≃ Quotient (connectedIsoSetoid.{u} n) :=
  (isoClassEquivConnectedIsoClass n).trans (connectedIsoClassEquiv.{u} n).symm

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
    (isoClassEquivConnectedRibbonGraph.{u} n).trans (connectedIsoClassEquiv.{u} n) =
      isoClassEquivConnectedIsoClass n := by ext _; simp [isoClassEquivConnectedRibbonGraph]

/-- Pointwise form of `isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv`. -/
@[simp] theorem connectedIsoClassEquiv_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    connectedIsoClassEquiv.{u} n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassEquivConnectedIsoClass n P :=
  Equiv.congr_fun (isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv.{u} n) P

/-- On `⟦P⟧`, `isoClassEquivConnectedRibbonGraph` gives the lifted ribbon graph of its monodromy. -/
theorem isoClassEquivConnectedRibbonGraph_mk {n : ℕ}
    (P : {P : AnalyticBelyiPair.{0} // degree P.β = n}) (ν : P.1.restrict ⁻¹' {basePt} ≃ Fin n) :
    isoClassEquivConnectedRibbonGraph.{u} n ⟦P⟧ =
      Quotient.mk (connectedIsoSetoid.{u} n)
        ⟨⟨(P.1.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.ulift,
            (P.1.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.card_E_ulift.trans
              (P.1.isCoveringMap_restrict.monodromyTriple ν).card_E_ribbonGraph⟩,
          (P.1.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.uliftIso.isConnected_iff.2
            ((P.1.isCoveringMap_restrict.monodromyTriple ν).isConnected_ribbonGraph.2
              (P.1.isCoveringMap_restrict.isConnected_monodromyTriple ν))⟩ := by
  rw [isoClassEquivConnectedRibbonGraph, Equiv.trans_apply, isoClassEquivConnectedIsoClass_mk P ν,
    connectedIsoClassEquiv_symm_mk]

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
    (Quotient.mk (connectedIsoSetoid.{u} n) ⟨⟨Γ, hcard⟩, hconn⟩))
  have hg : isoClassEquivConnectedRibbonGraph.{u} n ⟦⟨P, hdeg⟩⟧ = ⟦⟨⟨Γ, hcard⟩, hconn⟩⟧ :=
    (congrArg (isoClassEquivConnectedRibbonGraph.{u} n) hP).trans (Equiv.apply_symm_apply _ _)
  refine ⟨P, hdeg, fun ν ↦ ?_, fun Q νQ ⟨φ⟩ ↦ ?_⟩
  · rw [isoClassEquivConnectedRibbonGraph_mk ⟨P, hdeg⟩ ν, connectedIsoSetoid_mk_eq_mk_iff] at hg
    exact hg.map fun ψ ↦
      (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.uliftIso.symm.trans ψ
  · have hQdeg := Q.degree_β_eq_of_restrict_preimage_singleton_equiv νQ
    refine isoSetoid_r.1 (Quotient.exact (a := ⟨Q, hQdeg⟩) (b := ⟨P, hdeg⟩)
      ((isoClassEquivConnectedRibbonGraph.{u} n).injective ?_))
    rw [hg, isoClassEquivConnectedRibbonGraph_mk ⟨Q, hQdeg⟩ νQ, connectedIsoSetoid_mk_eq_mk_iff]
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
    exact nonempty_iso_ribbonGraph_iff.2 (PermutationTriple.IsoClass.mk_eq_mk_iff.1
      ((nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν').1 ⟨e⟩))
  · obtain rfl : n = m := by simpa using Fintype.card_congr φ.edge
    exact (nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν').2
      (PermutationTriple.IsoClass.mk_eq_mk_iff.2 (nonempty_iso_ribbonGraph_iff.1 ⟨φ⟩))

end AnalyticBelyiPair

/-! ### Matching degree partitions, automorphism/deck groups, and regularity with dessins -/

namespace TopBranchedCover.IsoClass

variable {n : ℕ} (c : IsoClass.{0} n)

/-- `equivConnectedRibbonGraph` matches `ramificationPartitions` with `connectedCycleData`. -/
@[simp] theorem connectedCycleData_equivConnectedRibbonGraph :
    connectedCycleData n (equivConnectedRibbonGraph.{u} n c) = c.ramificationPartitions := by
  simp [← cycleData_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the order of the deck/automorphism group. -/
@[simp] theorem connectedNatCardAut_equivConnectedRibbonGraph :
    connectedNatCardAut n (equivConnectedRibbonGraph.{u} n c) = c.natCardDeck := by
  simp [← natCardAutomorphismGroup_connectedIsoClassEquiv]

/-- `IsoClass.equivConnectedRibbonGraph` preserves regularity. -/
@[simp] theorem connectedIsRegular_equivConnectedRibbonGraph :
    ConnectedIsRegular n (equivConnectedRibbonGraph.{u} n c) ↔ c.IsRegular := by
  simp [← isRegular_connectedIsoClassEquiv]

end TopBranchedCover.IsoClass

namespace AnalyticBelyiPair

section RibbonAut

variable (P : AnalyticBelyiPair.{u}) {n : ℕ} (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)

/-- **The automorphism group of `P` is the automorphism group of its dessin.** -/
def isoMulEquivRibbonGraphAut :
    P.Iso P ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  (P.isoMulEquivAutomorphismGroup ν).trans
    (P.isCoveringMap_restrict.monodromyTriple ν).automorphismGroupMulEquivRibbonGraphAut

/-- On edges (`Fin n`), `isoMulEquivRibbonGraphAut` sends `i` to `ν (e • ν.symm i)`. -/
@[simp] theorem isoMulEquivRibbonGraphAut_apply_edge (e : P.Iso P) (i : Fin n) :
    (P.isoMulEquivRibbonGraphAut ν e).edge i = ν (e • ν.symm i) :=
  (Equiv.congr_fun (PermutationTriple.automorphismGroupMulEquivRibbonGraphAut_edge _ _) i).trans
    (P.coe_isoMulEquivAutomorphismGroup_apply ν e i)

/-- The automorphism of `P` attached to `f` sends `ν.symm i` to `ν.symm (f.edge i)`. -/
@[simp] theorem isoMulEquivRibbonGraphAut_symm_smul
    (f : (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    (P.isoMulEquivRibbonGraphAut ν).symm f • ν.symm i = ν.symm (f.edge i) := by
  simp [isoMulEquivRibbonGraphAut]; rfl

/-- **The deck group of `P.β` is the automorphism group of its dessin.** -/
def deckMulEquivRibbonGraphAut :
    deck P.β ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  P.isoMulEquivDeck.symm.trans (P.isoMulEquivRibbonGraphAut ν)

/-- On edges (`Fin n`), `deckMulEquivRibbonGraphAut` acts via `isoMulEquivDeck.symm` on the fibre
over `1/2`. -/
@[simp] theorem deckMulEquivRibbonGraphAut_apply_edge (φ : deck P.β) (i : Fin n) :
    (P.deckMulEquivRibbonGraphAut ν φ).edge i = ν (P.isoMulEquivDeck.symm φ • ν.symm i) :=
  P.isoMulEquivRibbonGraphAut_apply_edge ν (P.isoMulEquivDeck.symm φ) i

/-- The deck transformation of `P.β` attached to `f` sends `ν.symm i` to `ν.symm (f.edge i)`. -/
@[simp] theorem coe_deckMulEquivRibbonGraphAut_symm_apply
    (f : (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    ((P.deckMulEquivRibbonGraphAut ν).symm f : P.X ≃ₜ P.X) (ν.symm i) =
      (ν.symm (f.edge i) : P.X) := by
  simpa only [deckMulEquivRibbonGraphAut, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    coe_isoMulEquivDeck_apply, ← Iso.coe_smul] using
    congrArg Subtype.val (congrArg Subtype.val (P.isoMulEquivRibbonGraphAut_symm_smul ν f i))

end RibbonAut

/-- `P` is regular if and only if the ribbon graph of its monodromy triple is regular. -/
theorem isRegular_iff_ribbonGraph {P : AnalyticBelyiPair.{u}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.IsRegular ↔ (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.IsRegular := by
  rw [isRegular_iff_monodromyTriple ν, PermutationTriple.isRegular_ribbonGraph]

variable {n : ℕ} (P : Quotient (isoSetoid.{0} n))

/-- `isoClassEquivConnectedRibbonGraph` matches `isoClassRamificationPartitions` with
`connectedCycleData`. -/
@[simp] theorem connectedCycleData_isoClassEquivConnectedRibbonGraph :
    connectedCycleData n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassRamificationPartitions n P := by simp [← cycleData_connectedIsoClassEquiv]

/-- `isoClassEquivConnectedRibbonGraph` matches `isoClassNatCardAut` with `connectedNatCardAut`. -/
@[simp] theorem connectedNatCardAut_isoClassEquivConnectedRibbonGraph :
    connectedNatCardAut n (isoClassEquivConnectedRibbonGraph.{u} n P) = isoClassNatCardAut n P := by
  simp [← natCardAutomorphismGroup_connectedIsoClassEquiv]

/-- `isoClassEquivConnectedRibbonGraph` matches `IsoClassIsRegular` with `ConnectedIsRegular`. -/
@[simp] theorem connectedIsRegular_isoClassEquivConnectedRibbonGraph :
    ConnectedIsRegular n (isoClassEquivConnectedRibbonGraph.{u} n P) ↔ IsoClassIsRegular n P := by
  simp [← isRegular_connectedIsoClassEquiv]

end AnalyticBelyiPair

end TauCeti
