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

This file assembles the four-way equivalence of degree-`n` isomorphism classes across analytic
Riemann surfaces, branched topological covers, monodromy permutation triples, and bipartite ribbon
graphs (dessins d'enfants):

1. `Quotient (AnalyticBelyiPair.isoSetoid.{0} n)`: compact connected Riemann surfaces equipped with
   a degree-`n` holomorphic map to `OnePoint ℂ` unramified outside `{0, 1, ∞}`, up to
   biholomorphism over `OnePoint ℂ`;
2. `TopBranchedCover.IsoClass.{0} n`: degree-`n` topological branched covers of `OnePoint ℂ` with
   branch values in `{0, 1, ∞}`, up to homeomorphism over `OnePoint ℂ`;
3. `ConnectedIsoClass n`: connected degree-`n` permutation triples `(σ0, σ1, σinf)` with
   `σinf * σ1 * σ0 = 1`, up to simultaneous relabelling;
4. `Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n)`: connected bipartite ribbon graphs
   with `n` edges in any universe `u`, up to ribbon-graph isomorphism.

All six pairwise equivalences among these four types commute, are empty in degree `0` and unique in
degree `1`, and match the three families of invariants across all four descriptions:

* **Ramification, cycle, and degree partitions.** The triple `(λ₀, λ₁, λ∞)` of local-multiplicity
  multisets of `P.β` over `0`, `1` and `∞` (`AnalyticBelyiPair.isoClassRamificationPartitions`),
  the triple of topological ramification partitions
  (`TopBranchedCover.IsoClass.ramificationPartitions`), the full cycle partitions
  (`ConnectedIsoClass.cycleData`), and the black-vertex, white-vertex and face degree multisets
  (`BipartiteRibbonGraph.connectedCycleData`) agree.
* **Euler characteristic and genus.** The topological Euler characteristic and Riemann–Hurwitz
  genus of `P.X` (`AnalyticBelyiPair.isoClassEulerChar`, `AnalyticBelyiPair.isoClassGenus`) and of
  `X.Z` (`TopBranchedCover.IsoClass.eulerChar`, `TopBranchedCover.IsoClass.genus`) agree with the
  combinatorial Euler characteristic and genus on `ConnectedIsoClass n` and on
  `Quotient (BipartiteRibbonGraph.connectedIsoSetoid n)`.
* **Automorphism groups, deck groups, and regularity.** For any fibre numbering over `1/2`,
  `P.Iso P`, `deck P.β`, `deck X.π`, the triple's `automorphismGroup`, and the ribbon graph's `Aut`
  are canonically isomorphic as groups; their orders and the regularity predicates agree across all
  four classifications.

## Main declarations

* `TauCeti.AnalyticBelyiPair.isoClassEquivTopBranchedCoverIsoClass`,
  `TauCeti.TopBranchedCover.IsoClass.equivConnectedIsoClass`,
  `TauCeti.AnalyticBelyiPair.isoClassEquivConnectedRibbonGraph`,
  `TauCeti.TopBranchedCover.IsoClass.equivConnectedRibbonGraph`: the equivalences completing the
  four-way classification diagram alongside `AnalyticBelyiPair.isoClassEquivConnectedIsoClass` and
  `BipartiteRibbonGraph.connectedIsoClassEquiv`.
* `TauCeti.AnalyticBelyiPair.exists_iso_of_connectedRibbonGraph`: every connected bipartite ribbon
  graph is realised by an analytic Belyi pair, unique up to isomorphism.
* `TauCeti.AnalyticBelyiPair.nonempty_iso_iff_nonempty_ribbonGraph_iso`: two analytic Belyi pairs
  are isomorphic if and only if the ribbon graphs of their monodromy triples are isomorphic.
* `TauCeti.AnalyticBelyiPair.ramificationPartitions`,
  `TauCeti.AnalyticBelyiPair.isoClassRamificationPartitions`,
  `TauCeti.TopBranchedCover.ramificationPartitions`,
  `TauCeti.TopBranchedCover.IsoClass.ramificationPartitions`: the ordered triples of ramification
  partitions over `0`, `1` and `∞`, matched with `ConnectedIsoClass.cycleData` and
  `BipartiteRibbonGraph.connectedCycleData`.
* `TauCeti.AnalyticBelyiPair.isoMulEquivRibbonGraphAut`,
  `TauCeti.AnalyticBelyiPair.deckMulEquivRibbonGraphAut`,
  `TauCeti.AnalyticBelyiPair.isoMulEquivAutOfMonodromyTripleEq`,
  `TauCeti.TopBranchedCover.deckMulEquivAutomorphismGroup`,
  `TauCeti.TopBranchedCover.deckMulEquivRibbonGraphAut`: group isomorphisms between analytic
  automorphisms, deck transformations, triple automorphisms, and ribbon-graph automorphisms.
* `TauCeti.AnalyticBelyiPair.IsRegular`, `TauCeti.AnalyticBelyiPair.IsoClassIsRegular`,
  `TauCeti.TopBranchedCover.IsRegular`, `TauCeti.TopBranchedCover.IsoClass.IsRegular`: regularity
  and automorphism-group cardinalities matched across all four classifications.

## References

* A. Grothendieck, *Esquisse d'un Programme* (1984), in *Geometric Galois Actions 1*, London
  Mathematical Society Lecture Note Series 242, Cambridge University Press, 1997.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7, §2.7 and §4.2 (Theorem 4.27).
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.3, §1.5 and §2.1.
-/

public noncomputable section

open Equiv Equiv.Perm Function
open scoped OnePoint

namespace TauCeti

open ThricePuncturedSphere RiemannSurface

universe u v

/-! ### Degree zero and degree one across the analytic and topological carriers -/

/-- No analytic Belyi pair has degree zero, since the degree of a finite holomorphic map onto a
connected target is positive. -/
instance : IsEmpty {P : AnalyticBelyiPair.{u} // degree P.β = 0} :=
  ⟨fun P ↦ (degree_pos P.1.β).ne' P.2⟩

/-- There are no isomorphism classes of analytic Belyi pairs of degree zero. -/
instance : IsEmpty (Quotient (AnalyticBelyiPair.isoSetoid.{u} 0)) :=
  ⟨Quotient.ind isEmptyElim⟩

/-- No topological branched cover has degree zero. -/
instance : IsEmpty (TopBranchedCover.{u} 0) :=
  ⟨fun X ↦ X.ne_zero rfl⟩

/-- There are no isomorphism classes of topological branched covers of degree zero. -/
instance : IsEmpty (TopBranchedCover.IsoClass.{u} 0) :=
  ⟨fun c ↦ by obtain ⟨X, -⟩ := TopBranchedCover.IsoClass.mk_surjective c; exact isEmptyElim X⟩

/-! ### The four-way classification equivalences -/

namespace TopBranchedCover.IsoClass

/-- **Topological branched covers are classified by connected covers of `ℂ ∖ {0, 1}`**:
restricting over `ℂ ∖ {0, 1}` and filling the punctures are inverse bijections on isomorphism
classes. -/
def equivConnectedCoverClass (n : ℕ) :
    IsoClass.{0} n ≃ ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n where
  toFun := restrict
  invFun := ConnectedCoverClass.toTopBranchedCover
  left_inv c := restrict_injective (by simp)
  right_inv := ConnectedCoverClass.restrict_toTopBranchedCover

/-- Applying `equivConnectedCoverClass` restricts a class of branched covers over `ℂ ∖ {0, 1}`. -/
@[simp]
theorem equivConnectedCoverClass_apply {n : ℕ} (c : IsoClass.{0} n) :
    equivConnectedCoverClass n c = c.restrict :=
  (rfl)

/-- The inverse of `equivConnectedCoverClass` fills a class of connected covers. -/
@[simp]
theorem equivConnectedCoverClass_symm_apply {n : ℕ}
    (c : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (equivConnectedCoverClass n).symm c = c.toTopBranchedCover :=
  (rfl)

/-- **Topological branched covers are classified by connected permutation triples.** -/
def equivConnectedIsoClass (n : ℕ) : IsoClass.{0} n ≃ ConnectedIsoClass n :=
  (equivConnectedCoverClass n).trans ConnectedCoverClass.isoClassEquiv

/-- On the class of `X`, `equivConnectedIsoClass` returns the connected isomorphism class of its
monodromy triple for any numbering of the fibre over `1/2`. -/
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

/-- Up to isomorphism there is a unique topological branched cover of degree one. -/
instance : Unique (IsoClass.{0} 1) :=
  (equivConnectedIsoClass 1).unique

end TopBranchedCover.IsoClass

namespace AnalyticBelyiPair

/-- **Analytic Belyi pairs and topological branched covers have canonically equivalent isomorphism
classes**: forgetting the complex structure is an equivalence, inverted by filling the unbranched
cover with its holomorphic puncture charts. -/
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
@[simp]
theorem isoClassEquivTopBranchedCoverIsoClass_apply {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    isoClassEquivTopBranchedCoverIsoClass n P = toTopBranchedCoverIsoClass n P :=
  (rfl)

/-- The inverse of `isoClassEquivTopBranchedCoverIsoClass` restricts over `ℂ ∖ {0, 1}` and takes
the filled analytic Belyi pair. -/
@[simp]
theorem isoClassEquivTopBranchedCoverIsoClass_symm_apply {n : ℕ}
    (c : TopBranchedCover.IsoClass.{0} n) :
    (isoClassEquivTopBranchedCoverIsoClass n).symm c = c.restrict.toAnalyticBelyiPair :=
  (rfl)

/-- **Analytic Belyi pairs are classified by dessins d'enfants (connected bipartite ribbon
graphs).** Isomorphism classes of degree-`n` analytic Belyi pairs correspond bijectively to
isomorphism classes of connected bipartite ribbon graphs with `n` edges in any universe `u`. -/
def isoClassEquivConnectedRibbonGraph (n : ℕ) :
    Quotient (isoSetoid.{0} n) ≃ Quotient (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) :=
  (isoClassEquivConnectedIsoClass n).trans (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n).symm

/-! ### Commutativity of the four-way diagram and representative formulas -/

/-- Forgetting the complex structure commutes with the classification by connected permutation
triples. -/
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
@[simp]
theorem equivConnectedIsoClass_toTopBranchedCoverIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    TopBranchedCover.IsoClass.equivConnectedIsoClass n (toTopBranchedCoverIsoClass n P) =
      isoClassEquivConnectedIsoClass n P :=
  Equiv.congr_fun (isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedIsoClass n) P

/-- Forgetting the complex structure commutes with the classification by connected ribbon graphs. -/
theorem isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedRibbonGraph (n : ℕ) :
    (isoClassEquivTopBranchedCoverIsoClass n).trans
        (TopBranchedCover.IsoClass.equivConnectedRibbonGraph.{u} n) =
      isoClassEquivConnectedRibbonGraph.{u} n := by
  rw [TopBranchedCover.IsoClass.equivConnectedRibbonGraph, isoClassEquivConnectedRibbonGraph,
    ← Equiv.trans_assoc, isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedIsoClass]

/-- Pointwise form of `isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedRibbonGraph`. -/
@[simp]
theorem equivConnectedRibbonGraph_toTopBranchedCoverIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    TopBranchedCover.IsoClass.equivConnectedRibbonGraph.{u} n (toTopBranchedCoverIsoClass n P) =
      isoClassEquivConnectedRibbonGraph.{u} n P :=
  Equiv.congr_fun (isoClassEquivTopBranchedCoverIsoClass_trans_equivConnectedRibbonGraph.{u} n) P

/-- Composing `isoClassEquivConnectedRibbonGraph` with `connectedIsoClassEquiv` recovers
`isoClassEquivConnectedIsoClass`. -/
theorem isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv (n : ℕ) :
    (isoClassEquivConnectedRibbonGraph.{u} n).trans
        (BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n) =
      isoClassEquivConnectedIsoClass n := by
  ext P
  simp [isoClassEquivConnectedRibbonGraph]

/-- Pointwise form of `isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv`. -/
@[simp]
theorem connectedIsoClassEquiv_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedIsoClassEquiv.{u} n
        (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassEquivConnectedIsoClass n P :=
  Equiv.congr_fun (isoClassEquivConnectedRibbonGraph_trans_connectedIsoClassEquiv.{u} n) P

/-- On a representative pair `P`, `isoClassEquivConnectedRibbonGraph` sends `⟦P⟧` to the class of
the (universe-lifted) ribbon graph of its monodromy triple for any numbering of the fibre over
`1/2`. -/
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

/-- **Analytic realisation of every connected dessin.** Every connected bipartite ribbon graph `Γ`
with `n` edges is realised by an analytic Belyi pair `P : AnalyticBelyiPair.{0}` of degree `n` whose
ribbon graph (for every fibre numbering over `1/2`) is isomorphic to `Γ`, and `P` is unique up to
isomorphism of analytic Belyi pairs. -/
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
  obtain ⟨⟨P, hdeg⟩, hP⟩ :=
    Quotient.exists_rep ((isoClassEquivConnectedRibbonGraph.{u} n).symm
      (Quotient.mk (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) g))
  have hg : isoClassEquivConnectedRibbonGraph.{u} n ⟦⟨P, hdeg⟩⟧ =
      Quotient.mk (BipartiteRibbonGraph.connectedIsoSetoid.{u} n) g := by
    rw [hP, Equiv.apply_symm_apply]
  refine ⟨P, hdeg, fun ν ↦ ?_, fun Q νQ ⟨φ⟩ ↦ ?_⟩
  · rw [isoClassEquivConnectedRibbonGraph_mk ⟨P, hdeg⟩ ν,
      BipartiteRibbonGraph.connectedIsoSetoid_mk_eq_mk_iff] at hg
    obtain ⟨ψ⟩ := hg
    exact ⟨(P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.uliftIso.symm.trans ψ⟩
  · have hQdeg := Q.degree_β_eq_of_restrict_preimage_singleton_equiv νQ
    suffices hcl : (⟦⟨Q, hQdeg⟩⟧ : Quotient (isoSetoid.{0} n)) = ⟦⟨P, hdeg⟩⟧ from
      isoSetoid_r.1 (Quotient.exact hcl)
    apply (isoClassEquivConnectedRibbonGraph.{u} n).injective
    rw [hg, isoClassEquivConnectedRibbonGraph_mk ⟨Q, hQdeg⟩ νQ,
      BipartiteRibbonGraph.connectedIsoSetoid_mk_eq_mk_iff]
    exact ⟨(Q.isCoveringMap_restrict.monodromyTriple νQ).ribbonGraph.uliftIso.trans φ⟩

/-- **Two analytic Belyi pairs are isomorphic if and only if their dessins are isomorphic**, for
any numberings of their fibres over `1/2`. -/
theorem nonempty_iso_iff_nonempty_ribbonGraph_iso {P Q : AnalyticBelyiPair.{0}} {n m : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) (ν' : Q.restrict ⁻¹' {basePt} ≃ Fin m) :
    Nonempty (P.Iso Q) ↔
      Nonempty ((P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Iso
        (Q.isCoveringMap_restrict.monodromyTriple ν').ribbonGraph) := by
  constructor
  · rintro ⟨e⟩
    have hn := P.degree_β_eq_of_restrict_preimage_singleton_equiv ν
    have hm := Q.degree_β_eq_of_restrict_preimage_singleton_equiv ν'
    obtain rfl : n = m := hn.symm.trans (e.degree_eq.trans hm)
    have heq := (nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν').1 ⟨e⟩
    exact PermutationTriple.nonempty_iso_ribbonGraph_iff.2
      (PermutationTriple.IsoClass.mk_eq_mk_iff.1 heq)
  · rintro ⟨φ⟩
    have hcard := Fintype.card_congr φ.edge
    rw [PermutationTriple.card_E_ribbonGraph, PermutationTriple.card_E_ribbonGraph] at hcard
    obtain rfl : n = m := hcard
    rw [nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν', PermutationTriple.IsoClass.mk_eq_mk_iff]
    exact PermutationTriple.nonempty_iso_ribbonGraph_iff.1 ⟨φ⟩

end AnalyticBelyiPair

/-! ### Matching the three ramification, cycle, and degree partitions -/

namespace TopBranchedCover

/-- The ordered triple of ramification partitions of a topological branched cover over `0`, `1`
and `∞`, viewed as multisets of local degrees summing to `n`. -/
def ramificationPartitions {n : ℕ} (X : TopBranchedCover.{u} n) :
    Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  ((X.ramificationPartition ((0 : ℂ) : OnePoint ℂ)).parts,
    (X.ramificationPartition ((1 : ℂ) : OnePoint ℂ)).parts,
    (X.ramificationPartition (∞ : OnePoint ℂ)).parts)

/-- Isomorphic topological branched covers have the same ramification partitions over `0`, `1` and
`∞`. -/
theorem Iso.ramificationPartitions_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y) :
    X.ramificationPartitions = Y.ramificationPartitions := by
  simp only [ramificationPartitions, ι.ramificationPartition_eq]

/-- On `X : TopBranchedCover.{0} n`, the ramification partitions over `0`, `1` and `∞` are the
full cycle types of `σ0`, `σ1` and `σinf` in its monodromy triple. -/
theorem ramificationPartitions_eq_cycleData_monodromyTriple {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    X.ramificationPartitions = (X.isCoveringMap_restrict.monodromyTriple ν).cycleData := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [ramificationPartitions, X.parts_ramificationPartition_zero ν, fullCycleType_def,
      PermutationTriple.cycleData_σ0]
  · rw [ramificationPartitions, X.parts_ramificationPartition_one ν, fullCycleType_def,
      PermutationTriple.cycleData_σ1]
  · rw [ramificationPartitions, X.parts_ramificationPartition_inf ν, fullCycleType_def,
      PermutationTriple.cycleData_σinf]

/-- The ordered triple of ramification partitions over `0`, `1` and `∞` on
`TopBranchedCover.IsoClass`. -/
def IsoClass.ramificationPartitions {n : ℕ} (c : IsoClass.{u} n) :
    Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  (surjInv mk_surjective c).ramificationPartitions

/-- Evaluating `IsoClass.ramificationPartitions` on `IsoClass.mk X` recovers
`X.ramificationPartitions`. -/
@[simp]
theorem IsoClass.ramificationPartitions_mk {n : ℕ} (X : TopBranchedCover.{u} n) :
    (IsoClass.mk X).ramificationPartitions = X.ramificationPartitions :=
  (mk_eq_mk_iff.1 (surjInv_eq mk_surjective (.mk X))).some.ramificationPartitions_eq

/-- `IsoClass.equivConnectedIsoClass` carries the ramification partitions over `0`, `1` and `∞` to
the cycle data of the connected permutation triple. -/
@[simp]
theorem IsoClass.cycleData_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).cycleData = c.ramificationPartitions := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.cycleData_mk, ramificationPartitions_mk,
    X.ramificationPartitions_eq_cycleData_monodromyTriple ν]

/-- `IsoClass.equivConnectedRibbonGraph` carries the ramification partitions over `0`, `1` and `∞`
to the vertex and face degree partitions of the connected ribbon graph. -/
@[simp]
theorem IsoClass.connectedCycleData_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedCycleData n (equivConnectedRibbonGraph.{u} n c) =
      c.ramificationPartitions := by
  rw [equivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.cycleData_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    cycleData_equivConnectedIsoClass]

/-- `IsoClass.equivConnectedIsoClass` preserves the Euler characteristic. -/
@[simp]
theorem IsoClass.eulerChar_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).eulerChar = c.eulerChar := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.eulerChar_mk, eulerChar_mk,
    X.eulerChar_Z_eq_eulerChar_monodromyTriple ν]

/-- `IsoClass.equivConnectedIsoClass` preserves the genus. -/
@[simp]
theorem IsoClass.genus_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).genus = c.genus := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.genus_mk, genus_mk,
    X.genus_Z_eq_genus_monodromyTriple ν]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the Euler characteristic. -/
@[simp]
theorem IsoClass.connectedEulerChar_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedEulerChar n (equivConnectedRibbonGraph.{u} n c) =
      c.eulerChar := by
  rw [equivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.eulerChar_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    eulerChar_equivConnectedIsoClass]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the genus. -/
@[simp]
theorem IsoClass.connectedGenus_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedGenus n (equivConnectedRibbonGraph.{u} n c) = c.genus := by
  rw [equivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.genus_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    genus_equivConnectedIsoClass]

end TopBranchedCover

namespace AnalyticBelyiPair

/-- The ordered triple of analytic ramification partitions of `P.β` over `0`, `1` and `∞`: the
multisets of local multiplicities on the three fibres. -/
def ramificationPartitions (P : AnalyticBelyiPair.{u}) :
    Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  ((P.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β),
    (P.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β),
    (P.β.finite_fiber (∞ : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β))

/-- The analytic ramification partitions of `P` agree with the topological ramification partitions
of `P.toTopBranchedCover h`. -/
@[simp]
theorem ramificationPartitions_toTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (h : degree P.β = n) :
    (P.toTopBranchedCover h).ramificationPartitions = P.ramificationPartitions := by
  simp only [TopBranchedCover.ramificationPartitions, ramificationPartitions,
    P.parts_ramificationPartition_toTopBranchedCover h]

/-- Isomorphic analytic Belyi pairs have the same ramification partitions over `0`, `1` and `∞`. -/
theorem Iso.ramificationPartitions_eq {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) :
    P.ramificationPartitions = Q.ramificationPartitions := by
  rw [← P.ramificationPartitions_toTopBranchedCover rfl,
    ← Q.ramificationPartitions_toTopBranchedCover e.degree_eq.symm]
  exact (e.toTopBranchedCover rfl e.degree_eq.symm).ramificationPartitions_eq

/-- On `P : AnalyticBelyiPair.{0}`, the analytic ramification partitions over `0`, `1` and `∞` are
the cycle data of its monodromy triple for any numbering of the fibre over `1/2`. -/
theorem ramificationPartitions_eq_cycleData_monodromyTriple (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.ramificationPartitions = (P.isCoveringMap_restrict.monodromyTriple ν).cycleData := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [ramificationPartitions, P.map_localMultiplicity_fiber_zero ν, fullCycleType_def,
      PermutationTriple.cycleData_σ0]
  · rw [ramificationPartitions, P.map_localMultiplicity_fiber_one ν, fullCycleType_def,
      PermutationTriple.cycleData_σ1]
  · rw [ramificationPartitions, P.map_localMultiplicity_fiber_inf ν, fullCycleType_def,
      PermutationTriple.cycleData_σinf]

/-- The ordered triple of ramification partitions over `0`, `1` and `∞` on isomorphism classes of
degree-`n` analytic Belyi pairs. -/
def isoClassRamificationPartitions (n : ℕ) :
    Quotient (isoSetoid.{u} n) → Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  Quotient.lift (fun P ↦ P.1.ramificationPartitions) fun _ _ h ↦
    (isoSetoid_r.1 h).some.ramificationPartitions_eq

/-- Evaluating `isoClassRamificationPartitions` on `⟦P⟧` gives `P.1.ramificationPartitions`. -/
@[simp]
theorem isoClassRamificationPartitions_mk {n : ℕ}
    (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassRamificationPartitions n ⟦P⟧ = P.1.ramificationPartitions := by
  rw [isoClassRamificationPartitions, Quotient.lift_mk]

/-- Passing to the underlying topological branched cover preserves the ramification partitions over
`0`, `1` and `∞`. -/
@[simp]
theorem ramificationPartitions_toTopBranchedCoverIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{u} n)) :
    (toTopBranchedCoverIsoClass n P).ramificationPartitions =
      isoClassRamificationPartitions n P := by
  induction P using Quotient.inductionOn with
  | h P => simp

/-- `isoClassEquivConnectedIsoClass` matches the analytic ramification partitions over `0`, `1` and
`∞` with the cycle data of the connected permutation triple. -/
@[simp]
theorem cycleData_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).cycleData = isoClassRamificationPartitions n P := by
  rw [← equivConnectedIsoClass_toTopBranchedCoverIsoClass,
    TopBranchedCover.IsoClass.cycleData_equivConnectedIsoClass,
    ramificationPartitions_toTopBranchedCoverIsoClass]

/-- `isoClassEquivConnectedRibbonGraph` matches the analytic ramification partitions over `0`, `1`
and `∞` with the black-vertex, white-vertex and face degree partitions of the connected ribbon
graph. -/
@[simp]
theorem connectedCycleData_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedCycleData n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassRamificationPartitions n P := by
  rw [isoClassEquivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.cycleData_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    cycleData_isoClassEquivConnectedIsoClass]

/-- `isoClassEquivConnectedRibbonGraph` matches the topological Euler characteristic of the Riemann
surface with the combinatorial Euler characteristic `|B| + |W| + F - |E|` of its dessin. -/
@[simp]
theorem connectedEulerChar_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedEulerChar n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassEulerChar n P := by
  rw [isoClassEquivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.eulerChar_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    eulerChar_isoClassEquivConnectedIsoClass]

/-- `isoClassEquivConnectedRibbonGraph` matches the topological genus of the Riemann surface with
the combinatorial genus of its dessin. -/
@[simp]
theorem connectedGenus_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedGenus n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassGenus n P := by
  rw [isoClassEquivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.genus_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    genus_isoClassEquivConnectedIsoClass]

end AnalyticBelyiPair

/-! ### Automorphism groups, deck groups, and regularity across all four descriptions -/

namespace TopBranchedCover

/-- Conjugation by an isomorphism of topological branched covers identifies their deck groups. -/
def Iso.deckMulEquiv {n : ℕ} {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y) :
    deck X.π ≃* deck Y.π :=
  Deck.conjMulEquiv ι.toHomeomorph ι.π_apply

/-- Isomorphic topological branched covers have deck groups of the same cardinality. -/
theorem Iso.natCard_deck_eq {n : ℕ} {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y) :
    Nat.card (deck X.π) = Nat.card (deck Y.π) :=
  Nat.card_congr ι.deckMulEquiv.toEquiv

/-- **The deck group of a topological branched cover is the automorphism group of its monodromy
triple**, for any numbering of its fibre over `1/2`. -/
def deckMulEquivAutomorphismGroup {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    deck X.π ≃* (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroup :=
  X.deckMulEquivDeckRestrict.trans (X.isCoveringMap_restrict.deckMulEquivAutomorphismGroup ν)

/-- **The deck group of a topological branched cover is the automorphism group of the ribbon graph
of its monodromy triple**, for any numbering of its fibre over `1/2`. -/
def deckMulEquivRibbonGraphAut {n : ℕ} (X : TopBranchedCover.{u} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    deck X.π ≃* (X.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  (X.deckMulEquivAutomorphismGroup ν).trans
    (X.isCoveringMap_restrict.monodromyTriple ν).automorphismGroupMulEquivRibbonGraphAut

/-- A degree-`n` topological branched cover is *regular* when its deck group has order `n`. -/
def IsRegular {n : ℕ} (X : TopBranchedCover.{u} n) : Prop :=
  Nat.card (deck X.π) = n

/-- Unfold `TopBranchedCover.IsRegular` to the order condition on the deck group. -/
theorem isRegular_iff {n : ℕ} {X : TopBranchedCover.{u} n} :
    X.IsRegular ↔ Nat.card (deck X.π) = n :=
  Iff.rfl

/-- A topological branched cover is regular if and only if its monodromy triple is regular, for any
numbering of its fibre over `1/2`. -/
theorem isRegular_iff_monodromyTriple {n : ℕ} {X : TopBranchedCover.{u} n}
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) :
    X.IsRegular ↔ (X.isCoveringMap_restrict.monodromyTriple ν).IsRegular := by
  rw [isRegular_iff, PermutationTriple.isRegular_iff_card_automorphismGroup,
    and_iff_right (X.isCoveringMap_restrict.isConnected_monodromyTriple ν),
    Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv]

/-- Regularity of topological branched covers is invariant under isomorphism. -/
theorem Iso.isRegular_iff {n : ℕ} {X Y : TopBranchedCover.{u} n} (ι : X.Iso Y) :
    X.IsRegular ↔ Y.IsRegular := by
  rw [TopBranchedCover.isRegular_iff, TopBranchedCover.isRegular_iff, ι.natCard_deck_eq]

/-- The order of the deck group of an isomorphism class of topological branched covers. -/
def IsoClass.natCardDeck {n : ℕ} (c : IsoClass.{u} n) : ℕ :=
  Nat.card (deck (surjInv mk_surjective c).π)

/-- Evaluating `IsoClass.natCardDeck` on `IsoClass.mk X` gives `Nat.card (deck X.π)`. -/
@[simp]
theorem IsoClass.natCardDeck_mk {n : ℕ} (X : TopBranchedCover.{u} n) :
    (IsoClass.mk X).natCardDeck = Nat.card (deck X.π) :=
  (mk_eq_mk_iff.1 (surjInv_eq mk_surjective (.mk X))).some.natCard_deck_eq

/-- Regularity on isomorphism classes of topological branched covers. -/
def IsoClass.IsRegular {n : ℕ} (c : IsoClass.{u} n) : Prop :=
  (surjInv mk_surjective c).IsRegular

/-- Evaluating `IsoClass.IsRegular` on `IsoClass.mk X` recovers `X.IsRegular`. -/
@[simp]
theorem IsoClass.isRegular_mk {n : ℕ} (X : TopBranchedCover.{u} n) :
    (IsoClass.mk X).IsRegular ↔ X.IsRegular :=
  (mk_eq_mk_iff.1 (surjInv_eq mk_surjective (.mk X))).some.isRegular_iff

/-- `IsoClass.equivConnectedIsoClass` preserves the order of the deck/automorphism group. -/
@[simp]
theorem IsoClass.natCardAutomorphismGroup_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).natCardAutomorphismGroup = c.natCardDeck := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.natCardAutomorphismGroup_mk, natCardDeck_mk]
  exact (Nat.card_congr (X.deckMulEquivAutomorphismGroup ν).toEquiv).symm

/-- `IsoClass.equivConnectedIsoClass` preserves regularity. -/
@[simp]
theorem IsoClass.isRegular_equivConnectedIsoClass {n : ℕ} (c : IsoClass.{0} n) :
    (equivConnectedIsoClass n c).IsRegular ↔ c.IsRegular := by
  obtain ⟨X, rfl⟩ := mk_surjective c
  obtain ⟨ν⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [equivConnectedIsoClass_mk X ν, ConnectedIsoClass.isRegular_mk, isRegular_mk,
    X.isRegular_iff_monodromyTriple ν]

/-- `IsoClass.equivConnectedRibbonGraph` preserves the order of the deck/automorphism group. -/
@[simp]
theorem IsoClass.connectedNatCardAut_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.connectedNatCardAut n (equivConnectedRibbonGraph.{u} n c) =
      c.natCardDeck := by
  rw [equivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.natCardAutomorphismGroup_connectedIsoClassEquiv,
    Equiv.apply_symm_apply, natCardAutomorphismGroup_equivConnectedIsoClass]

/-- `IsoClass.equivConnectedRibbonGraph` preserves regularity. -/
@[simp]
theorem IsoClass.connectedIsRegular_equivConnectedRibbonGraph {n : ℕ} (c : IsoClass.{0} n) :
    BipartiteRibbonGraph.ConnectedIsRegular n (equivConnectedRibbonGraph.{u} n c) ↔
      c.IsRegular := by
  rw [equivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.isRegular_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    isRegular_equivConnectedIsoClass]

end TopBranchedCover

namespace AnalyticBelyiPair

/-- Conjugation by an isomorphism `e : P.Iso Q` of analytic Belyi pairs identifies their
automorphism groups. -/
def Iso.autMulEquiv {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) : P.Iso P ≃* Q.Iso Q where
  toFun f := e.symm.trans (f.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv f := Iso.ext fun x ↦ by simp
  right_inv g := Iso.ext fun y ↦ by simp
  map_mul' f g := Iso.ext fun y ↦ by simp

/-- Isomorphic analytic Belyi pairs have automorphism groups of the same cardinality. -/
theorem Iso.natCard_iso_eq {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) :
    Nat.card (P.Iso P) = Nat.card (Q.Iso Q) :=
  Nat.card_congr e.autMulEquiv.toEquiv

/-- The automorphism group of an analytic Belyi pair is canonically isomorphic to the deck group
of its underlying topological branched cover. -/
def isoMulEquivDeckToTopBranchedCover (P : AnalyticBelyiPair.{u}) {n : ℕ} (h : degree P.β = n) :
    P.Iso P ≃* deck (P.toTopBranchedCover h).π :=
  P.isoMulEquivDeck.trans (Deck.conjMulEquiv (Homeomorph.refl P.X) (P.toTopBranchedCover_π_apply h))

/-- **The automorphism group of an analytic Belyi pair is the automorphism group of its dessin**,
the ribbon graph of its monodromy triple for any numbering of the fibre over `1/2`. -/
def isoMulEquivRibbonGraphAut (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.Iso P ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  (P.isoMulEquivAutomorphismGroup ν).trans
    (P.isCoveringMap_restrict.monodromyTriple ν).automorphismGroupMulEquivRibbonGraphAut

/-- **The deck group of a Belyi map is the automorphism group of its dessin**, for any numbering
of the fibre over `1/2`. -/
def deckMulEquivRibbonGraphAut (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    deck P.β ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  P.isoMulEquivDeck.symm.trans (P.isoMulEquivRibbonGraphAut ν)

/-- If a numbered ribbon graph `(Γ, μ)` has the same permutation triple as `P` with fibre numbering
`ν`, then `P.Iso P` is canonically isomorphic to `Γ.Aut`. -/
def isoMulEquivAutOfMonodromyTripleEq (P : AnalyticBelyiPair.{u}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) {Γ : BipartiteRibbonGraph.{v}} (μ : Γ.E ≃ Fin n)
    (h : Γ.toPermutationTriple μ = P.isCoveringMap_restrict.monodromyTriple ν) :
    P.Iso P ≃* Γ.Aut :=
  (P.isoMulEquivAutomorphismGroup ν).trans <|
    (MulEquiv.subgroupCongr (congrArg PermutationTriple.automorphismGroup h.symm)).trans
      (Γ.autEquivAutomorphismGroup μ).symm

/-- An analytic Belyi pair is *regular* (or *Galois*) when its automorphism group has order equal
to the degree of its Belyi map. -/
def IsRegular (P : AnalyticBelyiPair.{u}) : Prop :=
  Nat.card (P.Iso P) = degree P.β

/-- Unfold `AnalyticBelyiPair.IsRegular` to the order condition
`Nat.card (P.Iso P) = degree P.β`. -/
theorem isRegular_iff {P : AnalyticBelyiPair.{u}} :
    P.IsRegular ↔ Nat.card (P.Iso P) = degree P.β :=
  Iff.rfl

/-- An analytic Belyi pair is regular if and only if its monodromy triple is regular, for any
numbering of its fibre over `1/2`. -/
theorem isRegular_iff_monodromyTriple {P : AnalyticBelyiPair.{u}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.IsRegular ↔ (P.isCoveringMap_restrict.monodromyTriple ν).IsRegular := by
  rw [isRegular_iff, P.degree_β_eq_of_restrict_preimage_singleton_equiv ν,
    isRegular_monodromyTriple_iff_natCard_iso]

/-- An analytic Belyi pair is regular if and only if the ribbon graph of its monodromy triple is
regular, for any numbering of its fibre over `1/2`. -/
theorem isRegular_iff_ribbonGraph {P : AnalyticBelyiPair.{u}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.IsRegular ↔ (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.IsRegular := by
  rw [isRegular_iff_monodromyTriple ν, PermutationTriple.isRegular_ribbonGraph]

/-- Passing to the underlying topological branched cover preserves regularity. -/
@[simp]
theorem isRegular_toTopBranchedCover {P : AnalyticBelyiPair.{u}} {n : ℕ} (h : degree P.β = n) :
    (P.toTopBranchedCover h).IsRegular ↔ P.IsRegular := by
  rw [TopBranchedCover.isRegular_iff, isRegular_iff, h,
    Nat.card_congr (P.isoMulEquivDeckToTopBranchedCover h).toEquiv]

/-- Regularity of analytic Belyi pairs is invariant under isomorphism. -/
theorem Iso.isRegular_iff {P Q : AnalyticBelyiPair.{u}} (e : P.Iso Q) :
    P.IsRegular ↔ Q.IsRegular := by
  rw [AnalyticBelyiPair.isRegular_iff, AnalyticBelyiPair.isRegular_iff, e.natCard_iso_eq,
    e.degree_eq]

/-- The order of the automorphism group of an isomorphism class of degree-`n` analytic Belyi
pairs. -/
def isoClassNatCardAut (n : ℕ) : Quotient (isoSetoid.{u} n) → ℕ :=
  Quotient.lift (fun P ↦ Nat.card (P.1.Iso P.1)) fun _ _ h ↦ (isoSetoid_r.1 h).some.natCard_iso_eq

/-- Evaluating `isoClassNatCardAut` on `⟦P⟧` gives `Nat.card (P.1.Iso P.1)`. -/
@[simp]
theorem isoClassNatCardAut_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    isoClassNatCardAut n ⟦P⟧ = Nat.card (P.1.Iso P.1) := by
  rw [isoClassNatCardAut, Quotient.lift_mk]

/-- Regularity on isomorphism classes of degree-`n` analytic Belyi pairs. -/
def IsoClassIsRegular (n : ℕ) : Quotient (isoSetoid.{u} n) → Prop :=
  Quotient.lift (fun P ↦ P.1.IsRegular) fun _ _ h ↦ propext (isoSetoid_r.1 h).some.isRegular_iff

/-- Evaluating `IsoClassIsRegular` on `⟦P⟧` recovers `P.1.IsRegular`. -/
@[simp]
theorem isoClassIsRegular_mk {n : ℕ} (P : {P : AnalyticBelyiPair.{u} // degree P.β = n}) :
    IsoClassIsRegular n ⟦P⟧ ↔ P.1.IsRegular := by
  rw [IsoClassIsRegular, Quotient.lift_mk]

/-- Forgetting the complex structure matches the analytic automorphism-group order with the
topological deck-group order. -/
@[simp]
theorem natCardDeck_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{u} n)) :
    (toTopBranchedCoverIsoClass n P).natCardDeck = isoClassNatCardAut n P := by
  induction P using Quotient.inductionOn with
  | h P =>
    rw [toTopBranchedCoverIsoClass_mk, TopBranchedCover.IsoClass.natCardDeck_mk,
      isoClassNatCardAut_mk]
    exact (Nat.card_congr (P.1.isoMulEquivDeckToTopBranchedCover P.2).toEquiv).symm

/-- Forgetting the complex structure preserves regularity. -/
@[simp]
theorem isRegular_toTopBranchedCoverIsoClass {n : ℕ} (P : Quotient (isoSetoid.{u} n)) :
    (toTopBranchedCoverIsoClass n P).IsRegular ↔ IsoClassIsRegular n P := by
  induction P using Quotient.inductionOn with
  | h P => simp

/-- `isoClassEquivConnectedIsoClass` preserves the order of the automorphism group. -/
@[simp]
theorem natCardAutomorphismGroup_isoClassEquivConnectedIsoClass {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).natCardAutomorphismGroup = isoClassNatCardAut n P := by
  rw [← equivConnectedIsoClass_toTopBranchedCoverIsoClass,
    TopBranchedCover.IsoClass.natCardAutomorphismGroup_equivConnectedIsoClass,
    natCardDeck_toTopBranchedCoverIsoClass]

/-- `isoClassEquivConnectedIsoClass` preserves regularity. -/
@[simp]
theorem isRegular_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).IsRegular ↔ IsoClassIsRegular n P := by
  rw [← equivConnectedIsoClass_toTopBranchedCoverIsoClass,
    TopBranchedCover.IsoClass.isRegular_equivConnectedIsoClass,
    isRegular_toTopBranchedCoverIsoClass]

/-- `isoClassEquivConnectedRibbonGraph` matches the order of the automorphism group of an analytic
Belyi pair with the order of the automorphism group of its dessin. -/
@[simp]
theorem connectedNatCardAut_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.connectedNatCardAut n (isoClassEquivConnectedRibbonGraph.{u} n P) =
      isoClassNatCardAut n P := by
  rw [isoClassEquivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.natCardAutomorphismGroup_connectedIsoClassEquiv,
    Equiv.apply_symm_apply, natCardAutomorphismGroup_isoClassEquivConnectedIsoClass]

/-- `isoClassEquivConnectedRibbonGraph` matches regularity of an analytic Belyi pair with
regularity of its dessin. -/
@[simp]
theorem connectedIsRegular_isoClassEquivConnectedRibbonGraph {n : ℕ}
    (P : Quotient (isoSetoid.{0} n)) :
    BipartiteRibbonGraph.ConnectedIsRegular n (isoClassEquivConnectedRibbonGraph.{u} n P) ↔
      IsoClassIsRegular n P := by
  rw [isoClassEquivConnectedRibbonGraph, Equiv.trans_apply,
    ← BipartiteRibbonGraph.isRegular_connectedIsoClassEquiv, Equiv.apply_symm_apply,
    isRegular_isoClassEquivConnectedIsoClass]

end AnalyticBelyiPair

end TauCeti
