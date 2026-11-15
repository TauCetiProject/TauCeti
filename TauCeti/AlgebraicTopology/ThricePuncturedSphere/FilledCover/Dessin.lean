/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Genus
public import TauCeti.Combinatorics.RibbonGraph.ConnectedClassification

import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Deck

/-!
# Analytic Riemann existence for three-point covers and dessins d'enfants

This file assembles the four-way equivalence of degree-`n` isomorphism classes across:
1. `Quotient (AnalyticBelyiPair.isoSetoid.{0} n)` (analytic Belyi pairs over `OnePoint ℂ`);
2. `TopBranchedCover.IsoClass.{0} n` (topological branched covers over `{0, 1, ∞}`);
3. `ConnectedIsoClass n` (connected permutation triples `(σ0, σ1, σinf)` with `σinf * σ1 * σ0 = 1`);
4. `Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n)` (connected bipartite ribbon graphs /
   dessins d'enfants with `n` edges in any universe `u`).

All six pairwise equivalences commute, are empty in degree `0` and unique in degree `1`, and match
ramification/cycle/degree partitions (`isoClassRamificationPartitions`, `ramificationPartitions`,
`ConnectedIsoClass.cycleData`, `connectedCycleData`), Euler characteristic and genus
(`isoClassEulerChar`, `isoClassGenus`, `TopBranchedCover.IsoClass.eulerChar`,
`TopBranchedCover.IsoClass.genus`, `ConnectedIsoClass.eulerChar`, `ConnectedIsoClass.genus`,
`connectedEulerChar`, `connectedGenus`), and automorphism/deck groups, orders, regularity, and
representative-level dessin realisation (`exists_iso_of_connectedRibbonGraph`,
`nonempty_iso_iff_nonempty_ribbonGraph_iso`).

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), LMS Lecture Note Series 242, CUP, 1997.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, CUP, 2012, §1.2.7, §2.7 and §4.2 (Theorem 4.27).
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, EMS 141, Springer,
  2004, §1.3, §1.5 and §2.1.
-/

public noncomputable section

open Equiv Equiv.Perm Function
open scoped OnePoint

namespace TauCeti

open ThricePuncturedSphere RiemannSurface

universe u

/-! ### The four-way classification equivalences -/

namespace TopBranchedCover.IsoClass

/-- **Topological branched covers are classified by connected covers of `ℂ ∖ {0, 1}`.** -/
def equivConnectedCoverClass (n : ℕ) :
    IsoClass.{0} n ≃ ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n where
  toFun := restrict
  invFun := ConnectedCoverClass.toTopBranchedCover
  left_inv _ := restrict_injective (by simp)
  right_inv := ConnectedCoverClass.restrict_toTopBranchedCover

/-- Applying `equivConnectedCoverClass` restricts a class of branched covers over `ℂ ∖ {0, 1}`. -/
@[simp] theorem equivConnectedCoverClass_apply {n : ℕ} (c : IsoClass.{0} n) :
    equivConnectedCoverClass n c = c.restrict := (rfl)

/-- The inverse of `equivConnectedCoverClass` fills a class of connected covers. -/
@[simp] theorem equivConnectedCoverClass_symm_apply {n : ℕ}
    (c : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (equivConnectedCoverClass n).symm c = c.toTopBranchedCover := (rfl)

/-- **Topological branched covers are classified by connected permutation triples.** -/
def equivConnectedIsoClass (n : ℕ) : IsoClass.{0} n ≃ ConnectedIsoClass n :=
  (equivConnectedCoverClass n).trans ConnectedCoverClass.isoClassEquiv

/-- On `.mk X`, `equivConnectedIsoClass` returns the connected class of its monodromy triple. -/
theorem equivConnectedIsoClass_mk {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    equivConnectedIsoClass n (.mk X) =
      .mk ⟨X.isCoveringMap_restrict.monodromyTriple ν,
        X.isCoveringMap_restrict.isConnected_monodromyTriple ν⟩ := by
  obtain ⟨ν'⟩ := X.connectedCover.nonempty_equiv_fin
  rw [equivConnectedIsoClass, Equiv.trans_apply, equivConnectedCoverClass_apply, restrict_mk,
    ConnectedCoverClass.isoClassEquiv_apply, ConnectedCoverClass.isoClass_mk _ ν']
  refine ConnectedIsoClass.forget_injective ?_
  rw [ConnectedIsoClass.forget_mk, ConnectedIsoClass.forget_mk,
    ConnectedFiberNumberedCover.coe_connectedTriple]
  exact (X.connectedCover.cover.isCoveringMap_proj.isoClass_monodromyTriple_eq_of_homeomorph ν'
    X.isCoveringMap_restrict ν X.connectedCoverHomeomorph
    (funext X.restrict_connectedCoverHomeomorph)).symm

/-- **Topological branched covers are classified by connected bipartite ribbon graphs.** -/
def equivConnectedRibbonGraph (n : ℕ) :
    IsoClass.{0} n ≃ Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) :=
  (equivConnectedIsoClass n).trans (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n).symm

/-- Composing `equivConnectedRibbonGraph` with `connectedIsoClassEquiv` recovers
`equivConnectedIsoClass`. -/
@[simp] theorem connectedIsoClassEquiv_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n (equivConnectedRibbonGraph.{u} n c) =
      equivConnectedIsoClass n c := by
  simp [equivConnectedRibbonGraph]

/-- Up to isomorphism there is a unique topological branched cover of degree one. -/
instance : Unique (IsoClass.{0} 1) := (equivConnectedIsoClass 1).unique

end TopBranchedCover.IsoClass

namespace AnalyticBelyiPair

/-- **Analytic Belyi pairs and topological branched covers have equivalent isomorphism classes.** -/
def isoClassEquivTopBranchedCoverIsoClass (n : ℕ) :
    Quotient (isoSetoid.{0} n) ≃ TopBranchedCover.IsoClass.{0} n where
  toFun := toTopBranchedCoverIsoClass n
  invFun c := c.restrict.toAnalyticBelyiPair
  left_inv P := by
    dsimp only
    rw [← isoClassEquivConnectedCoverClass_apply, ← isoClassEquivConnectedCoverClass_symm_apply,
      Equiv.symm_apply_apply]
  right_inv c := by
    dsimp only
    rw [ConnectedCoverClass.toTopBranchedCoverIsoClass_toAnalyticBelyiPair]
    exact TopBranchedCover.IsoClass.restrict_injective (by simp)

/-- Applying `isoClassEquivTopBranchedCoverIsoClass` forgets the complex structure. -/
@[simp] theorem isoClassEquivTopBranchedCoverIsoClass_apply {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    isoClassEquivTopBranchedCoverIsoClass n P = toTopBranchedCoverIsoClass n P := (rfl)

/-- The inverse of `isoClassEquivTopBranchedCoverIsoClass` takes the filled analytic Belyi pair. -/
@[simp] theorem isoClassEquivTopBranchedCoverIsoClass_symm_apply {n : ℕ}
    (c : TopBranchedCover.IsoClass.{0} n) :
    (isoClassEquivTopBranchedCoverIsoClass n).symm c = c.restrict.toAnalyticBelyiPair := (rfl)

/-- **Analytic Belyi pairs are classified by dessins d'enfants (connected ribbon graphs).** -/
def isoClassEquivConnectedRibbonGraph (n : ℕ) :
    Quotient (isoSetoid.{0} n) ≃ Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) :=
  (isoClassEquivConnectedIsoClass n).trans (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n).symm

/-! ### Commutativity of the four-way diagram and representative formulas -/

/-- Forgetting the complex structure commutes with classification by connected triples. -/
theorem isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedIsoClass (n : ℕ) :
    (isoClassEquivTopBranchedCoverIsoClass n).trans
        (TopBranchedCover.IsoClass.equivConnectedIsoClass n) =
      isoClassEquivConnectedIsoClass n := by
  ext P
  rw [Equiv.trans_apply, isoClassEquivConnectedIsoClass_apply,
    isoClassEquivConnectedCoverClass_apply, isoClassEquivTopBranchedCoverIsoClass_apply,
    TopBranchedCover.IsoClass.equivConnectedIsoClass, Equiv.trans_apply,
    TopBranchedCover.IsoClass.equivConnectedCoverClass_apply,
    ConnectedCoverClass.isoClassEquiv_apply]

/-- Pointwise form of `isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedIsoClass`. -/
@[simp] theorem equivConnectedIsoClass_toTopBranchedCoverIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    TopBranchedCover.IsoClass.equivConnectedIsoClass n (toTopBranchedCoverIsoClass n P) =
      isoClassEquivConnectedIsoClass n P :=
  Equiv.congr_fun (isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedIsoClass n) P

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
      isoClassEquivConnectedRibbonGraph.{u} n P :=
  Equiv.congr_fun (isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedRibbonGraph.{u} n) P

/-- Composing `isoClassEquivConnectedRibbonGraph` with `connectedIsoClassEquiv` recovers
`isoClassEquivConnectedIsoClass`. -/
theorem isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv (n : ℕ) :
    (isoClassEquivConnectedRibbonGraph.{u} n).trans
        (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n) =
      isoClassEquivConnectedIsoClass n :=
  Equiv.ext fun _ ↦ by simp [isoClassEquivConnectedRibbonGraph]

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
  let g : {G : {G : BipartiteRibbonGraph.{u} // Fintype.card G.E = n} // G.1.IsConnected} :=
    ⟨⟨Γ, hcard⟩, hconn⟩
  obtain ⟨⟨P, hdeg⟩, hP⟩ := Quotient.exists_rep
    ((isoClassEquivConnectedRibbonGraph.{u} n).symm
      (Quotient.mk (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) g))
  have hg : isoClassEquivConnectedRibbonGraph.{u} n ⟦⟨P, hdeg⟩⟧ =
      Quotient.mk (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) g := by
    rw [hP, Equiv.apply_symm_apply]
  refine ⟨P, hdeg, fun ν ↦ ?_, fun Q νQ ⟨φ⟩ ↦ ?_⟩
  · rw [isoClassEquivConnectedRibbonGraph_mk ⟨P, hdeg⟩ ν,
      BipartiteRibbonGraph.connectedIsoSetoid_mk_eq_mk_iff] at hg
    exact hg.map fun ψ ↦
      (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.uliftIso.symm.trans ψ
  · have hQdeg := Q.degree_β_eq_of_restrict_preimage_singleton_equiv νQ
    suffices hcl : (⟦⟨Q, hQdeg⟩⟧ : Quotient (isoSetoid.{0} n)) = ⟦⟨P, hdeg⟩⟧ from
      isoSetoid_r.1 (Quotient.exact hcl)
    apply (isoClassEquivConnectedRibbonGraph.{u} n).injective
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
  · have hcard := Fintype.card_congr φ.edge
    rw [PermutationTriple.card_E_ribbonGraph, PermutationTriple.card_E_ribbonGraph] at hcard
    obtain rfl : n = m := hcard
    exact (nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν').2
      (PermutationTriple.IsoClass.mk_eq_mk_iff.2
        (PermutationTriple.nonempty_iso_ribbonGraph_iff.1 ⟨φ⟩))

end AnalyticBelyiPair

/-! ### Matching the three ramification, cycle, and degree partitions -/

namespace TopBranchedCover

/-- On `TopBranchedCover.{0} n`, `ramificationPartitions` equals `cycleData` of the monodromy. -/
theorem ramificationPartitions_eq_cycleData_monodromyTriple {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    X.ramificationPartitions = (X.isCoveringMap_restrict.monodromyTriple ν).cycleData := by
  rw [X.ramificationPartitions_def]
  exact Prod.ext
    (by rw [X.parts_ramificationPartition_zero ν, fullCycleType_def,
      PermutationTriple.cycleData_σ0])
    (Prod.ext
      (by rw [X.parts_ramificationPartition_one ν, fullCycleType_def,
        PermutationTriple.cycleData_σ1])
      (by rw [X.parts_ramificationPartition_inf ν, fullCycleType_def,
        PermutationTriple.cycleData_σinf]))

/-- `IsoClass.equivConnectedIsoClass` matches `ramificationPartitions` with `cycleData`. -/
@[simp] theorem IsoClass.cycleData_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).cycleData = c.ramificationPartitions := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.cycleData_mk, ramificationPartitions_mk,
    X.ramificationPartitions_eq_cycleData_monodromyTriple ν]

/-- `equivConnectedRibbonGraph` matches `ramificationPartitions` with `connectedCycleData`. -/
@[simp] theorem IsoClass.connectedCycleData_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedCycleData n (equivConnectedRibbonGraph.{u} n c) =
      c.ramificationPartitions := by
  rw [← BipartiteRibbonGraph.cycleData_connectedIsoClassEquiv]; simp

/-- `IsoClass.equivConnectedIsoClass` preserves the Euler characteristic. -/
@[simp] theorem IsoClass.eulerChar_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).eulerChar = c.eulerChar := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.eulerChar_mk, eulerChar_mk,
    X.eulerChar_Z_eq_eulerChar_monodromyTriple ν]

/-- `IsoClass.equivConnectedIsoClass` preserves the genus. -/
@[simp] theorem IsoClass.genus_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).genus = c.genus := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.genus_mk, genus_mk,
    X.genus_Z_eq_genus_monodromyTriple ν]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the Euler characteristic. -/
@[simp] theorem IsoClass.connectedEulerChar_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedEulerChar n (equivConnectedRibbonGraph.{u} n c) =
      c.eulerChar := by
  rw [← BipartiteRibbonGraph.eulerChar_connectedIsoClassEquiv]; simp

/-- `IsoClass.equivConnectedRibbonGraph` preserves the genus. -/
@[simp] theorem IsoClass.connectedGenus_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedGenus n (equivConnectedRibbonGraph.{u} n c) = c.genus := by
  rw [← BipartiteRibbonGraph.genus_connectedIsoClassEquiv]; simp

end TopBranchedCover

namespace AnalyticBelyiPair

/-- The ordered triple of analytic ramification partitions of `P.β` over `0`, `1` and `∞`. -/
def ramificationPartitions (P : AnalyticBelyiPair.{u}) :
    Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  ((P.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β),
    (P.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β),
    (P.β.finite_fiber (∞ : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β))

/-- Unfold `AnalyticBelyiPair.ramificationPartitions` into its `0`, `1` and `∞` components. -/
theorem ramificationPartitions_def (P : AnalyticBelyiPair.{u}) : P.ramificationPartitions =
    ((P.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β),
      (P.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β),
      (P.β.finite_fiber (∞ : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β)) := (rfl)

/-- `P.toTopBranchedCover h` has the same ramification partitions as `P`. -/
@[simp] theorem ramificationPartitions_toTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (h : degree P.β = n) :
    (P.toTopBranchedCover h).ramificationPartitions = P.ramificationPartitions := by
  simp only [TopBranchedCover.ramificationPartitions_def, ramificationPartitions_def,
    P.parts_ramificationPartition_toTopBranchedCover h]

/-- Isomorphic analytic Belyi pairs have the same ramification partitions over `0`, `1` and `∞`. -/
theorem Iso.ramificationPartitions_eq {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) :
    P.ramificationPartitions = Q.ramificationPartitions := by
  rw [← P.ramificationPartitions_toTopBranchedCover rfl,
    ← Q.ramificationPartitions_toTopBranchedCover e.degree_eq.symm]
  exact (e.toTopBranchedCover rfl e.degree_eq.symm).ramificationPartitions_eq

/-- On `AnalyticBelyiPair.{0}`, `ramificationPartitions` equals `cycleData` of the monodromy. -/
theorem ramificationPartitions_eq_cycleData_monodromyTriple (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.ramificationPartitions = (P.isCoveringMap_restrict.monodromyTriple ν).cycleData := by
  let h := P.degree_β_eq_of_restrict_preimage_singleton_equiv ν
  rw [← P.ramificationPartitions_toTopBranchedCover h]
  obtain ⟨νT⟩ := (P.toTopBranchedCover h).nonempty_restrict_preimage_singleton_equiv basePt
  exact ((P.toTopBranchedCover h).ramificationPartitions_eq_cycleData_monodromyTriple νT).trans
    (PermutationTriple.cycleData_eq_of_equivalent (PermutationTriple.IsoClass.mk_eq_mk_iff.1
      (P.isoClass_monodromyTriple_toTopBranchedCover h ν νT)))

/-- The ordered triple of ramification partitions over `0`, `1` and `∞` on `isoSetoid`. -/
def isoClassRamificationPartitions (n : ℕ) :
    Quotient (isoSetoid.{u} n) → Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  Quotient.lift (fun P ↦ P.1.ramificationPartitions) fun _ _ h ↦
    (isoSetoid_r.1 h).elim Iso.ramificationPartitions_eq

/-- Evaluating `isoClassRamificationPartitions` on `⟦P⟧` gives `P.1.ramificationPartitions`. -/
@[simp] theorem isoClassRamificationPartitions_mk {n : ℕ}
    (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassRamificationPartitions n ⟦P⟧ = P.1.ramificationPartitions := (rfl)

/-- Forgetting the complex structure preserves the ramification partitions over `0`, `1` and `∞`. -/
@[simp] theorem ramificationPartitions_toTopBranchedCoverIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{u} n)) :
    (toTopBranchedCoverIsoClass n P).ramificationPartitions =
      isoClassRamificationPartitions n P := Quotient.inductionOn P fun _ ↦ by simp

/-- `isoClassEquivConnectedIsoClass` matches `isoClassRamificationPartitions` with `cycleData`. -/
@[simp] theorem cycleData_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).cycleData = isoClassRamificationPartitions n P := by
  rw [← equivConnectedIsoClass_toTopBranchedCoverIsoClass,
    TopBranchedCover.IsoClass.cycleData_equivConnectedIsoClass,
    ramificationPartitions_toTopBranchedCoverIsoClass]

/-- `isoClassEquivConnectedRibbonGraph` matches `isoClassRamificationPartitions` with
`connectedCycleData`. -/
@[simp] theorem connectedCycleData_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedCycleData n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassRamificationPartitions n P := by
  rw [← BipartiteRibbonGraph.cycleData_connectedIsoClassEquiv]; simp

/-- `isoClassEquivConnectedRibbonGraph` matches the topological and dessin Euler characteristics. -/
@[simp] theorem connectedEulerChar_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedEulerChar n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassEulerChar n P := by
  rw [← BipartiteRibbonGraph.eulerChar_connectedIsoClassEquiv]; simp

/-- `isoClassEquivConnectedRibbonGraph` matches the topological genus with the dessin genus. -/
@[simp] theorem connectedGenus_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedGenus n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassGenus n P := by
  rw [← BipartiteRibbonGraph.genus_connectedIsoClassEquiv]; simp

end AnalyticBelyiPair

/-! ### Automorphism groups, deck groups, and regularity across all four descriptions -/

namespace TopBranchedCover

/-- **The deck group of `X` is the automorphism group of its monodromy triple.** -/
def deckMulEquivAutomorphismGroup {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    deck X.π ≃* (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup :=
  X.deckMulEquivDeckRestrict.trans (X.isCoveringMap_restrict.deckMulEquivAutomorphismGroup ν)

/-- `deckMulEquivAutomorphismGroup` sends `φ` to the permutation it induces on the numbered fibre
over `1/2`. -/
@[simp] theorem coe_deckMulEquivAutomorphismGroup_apply {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) (φ : deck X.π) (i : Fin n) :
    (X.deckMulEquivAutomorphismGroup ν φ : Perm (Fin n)) i = ν (φ • ν.symm i) := by
  refine (IsCoveringMap.coe_deckMulEquivAutomorphismGroup_apply _ ν
    (X.deckMulEquivDeckRestrict φ) i).trans (congrArg ν (Subtype.ext (Subtype.ext ?_)))
  exact (congrArg Subtype.val (deck.fiber_smul_coe _ (ν.symm i))).trans <|
    (X.coe_deckMulEquivDeckRestrict_apply φ _).trans
      (X.coe_deck_smul_restrictFiber basePt φ (ν.symm i)).symm

/-- The deck transformation attached to `τ` sends the sheet labelled `i` to that labelled `τ i`. -/
@[simp] theorem deckMulEquivAutomorphismGroup_symm_smul {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n)
    (τ : (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup) (i : Fin n) :
    (X.deckMulEquivAutomorphismGroup ν).symm τ • ν.symm i = ν.symm ((τ : Perm (Fin n)) i) := by
  rw [← ν.symm_apply_apply ((X.deckMulEquivAutomorphismGroup ν).symm τ • ν.symm i),
    ← coe_deckMulEquivAutomorphismGroup_apply, MulEquiv.apply_symm_apply]

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

/-- `X` is regular if and only if its monodromy triple is regular. -/
theorem isRegular_iff_monodromyTriple {n : ℕ} {X : TopBranchedCover.{u} n}
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    X.IsRegular ↔ (X.isCoveringMap_restrict.monodromyTriple ν).IsRegular := by
  rw [isRegular_iff, PermutationTriple.isRegular_iff_card_automorphismGroup,
    and_iff_right (X.isCoveringMap_restrict.isConnected_monodromyTriple ν),
    Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv]

/-- `IsoClass.equivConnectedIsoClass` preserves the order of the deck/automorphism group. -/
@[simp] theorem IsoClass.natCardAutomorphismGroup_equivConnectedIsoClass {n : ℕ}
    (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).natCardAutomorphismGroup = c.natCardDeck := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.natCardAutomorphismGroup_mk, natCardDeck_mk]
  exact (Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv).symm

/-- `IsoClass.equivConnectedIsoClass` preserves regularity. -/
@[simp] theorem IsoClass.isRegular_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).IsRegular ↔ c.IsRegular := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.isRegular_mk, isRegular_mk,
    X.isRegular_iff_monodromyTriple ν]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the order of the deck/automorphism group. -/
@[simp] theorem IsoClass.connectedNatCardAut_equivConnectedRibbonGraph {n : ℕ}
    (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedNatCardAut n (equivConnectedRibbonGraph.{u} n c) =
      c.natCardDeck := by
  rw [← BipartiteRibbonGraph.natCardAutomorphismGroup_connectedIsoClassEquiv]; simp

/-- `IsoClass.equivConnectedRibbonGraph` preserves regularity. -/
@[simp] theorem IsoClass.connectedIsRegular_equivConnectedRibbonGraph {n : ℕ}
    (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.ConnectedIsRegular n (equivConnectedRibbonGraph.{u} n c) ↔
      c.IsRegular := by
  rw [← BipartiteRibbonGraph.isRegular_connectedIsoClassEquiv]; simp

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

/-- The order of the automorphism group of an isomorphism class of analytic Belyi pairs. -/
def isoClassNatCardAut (n : ℕ) : Quotient (isoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun P ↦ Nat.card (P.1.Iso P.1)) fun _ _ h ↦
    (isoSetoid_r.1 h).elim Iso.natCard_iso_eq

/-- Evaluating `isoClassNatCardAut` on `⟦P⟧` gives `Nat.card (P.1.Iso P.1)`. -/
@[simp] theorem isoClassNatCardAut_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassNatCardAut n ⟦P⟧ = Nat.card (P.1.Iso P.1) := (rfl)

/-- Regularity on isomorphism classes of degree-`n` analytic Belyi pairs. -/
def IsoClassIsRegular (n : ℕ) : Quotient (isoSetoid.{u} n) → Prop :=
  Quotient.lift (fun P ↦ P.1.IsRegular) fun _ _ h ↦
    (isoSetoid_r.1 h).elim fun e ↦ propext e.isRegular_iff

/-- Evaluating `IsoClassIsRegular` on `⟦P⟧` recovers `P.1.IsRegular`. -/
@[simp] theorem isoClassIsRegular_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    IsoClassIsRegular n ⟦P⟧ ↔ P.1.IsRegular := Iff.rfl

/-- Forgetting the complex structure matches `isoClassNatCardAut` with `natCardDeck`. -/
@[simp] theorem natCardDeck_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{u} n)) :
    (toTopBranchedCoverIsoClass n P).natCardDeck = isoClassNatCardAut n P :=
  Quotient.inductionOn P fun P ↦ by
    rw [toTopBranchedCoverIsoClass_mk, TopBranchedCover.IsoClass.natCardDeck_mk,
      isoClassNatCardAut_mk]
    exact (Nat.card_congr (P.1.isoMulEquivDeckToTopBranchedCover P.2).toEquiv).symm

/-- Forgetting the complex structure preserves regularity. -/
@[simp] theorem isRegular_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{u} n)) :
    (toTopBranchedCoverIsoClass n P).IsRegular ↔ IsoClassIsRegular n P :=
  Quotient.inductionOn P fun _ ↦ by simp

/-- `isoClassEquivConnectedIsoClass` preserves the order of the automorphism group. -/
@[simp] theorem natCardAutomorphismGroup_isoClassEquivConnectedIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).natCardAutomorphismGroup = isoClassNatCardAut n P := by
  rw [← equivConnectedIsoClass_toTopBranchedCoverIsoClass,
    TopBranchedCover.IsoClass.natCardAutomorphismGroup_equivConnectedIsoClass,
    natCardDeck_toTopBranchedCoverIsoClass]

/-- `isoClassEquivConnectedIsoClass` preserves regularity. -/
@[simp] theorem isRegular_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).IsRegular ↔ IsoClassIsRegular n P := by
  rw [← equivConnectedIsoClass_toTopBranchedCoverIsoClass,
    TopBranchedCover.IsoClass.isRegular_equivConnectedIsoClass,
    isRegular_toTopBranchedCoverIsoClass]

/-- `isoClassEquivConnectedRibbonGraph` matches `isoClassNatCardAut` with `connectedNatCardAut`. -/
@[simp] theorem connectedNatCardAut_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedNatCardAut n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassNatCardAut n P := by
  rw [← BipartiteRibbonGraph.natCardAutomorphismGroup_connectedIsoClassEquiv]; simp

/-- `isoClassEquivConnectedRibbonGraph` matches `IsoClassIsRegular` with `ConnectedIsRegular`. -/
@[simp] theorem connectedIsRegular_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.ConnectedIsRegular n (isoClassEquivConnectedRibbonGraph.{u} n P) ↔
      IsoClassIsRegular n P := by
  rw [← BipartiteRibbonGraph.isRegular_connectedIsoClassEquiv]; simp

end AnalyticBelyiPair

end TauCeti
