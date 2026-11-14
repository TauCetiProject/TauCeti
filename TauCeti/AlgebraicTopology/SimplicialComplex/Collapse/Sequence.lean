/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Deformation
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex
public import TauCeti.Topology.Homotopy.DeformationRetract
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Geometric deformation along finite collapse sequences

A finite simplicial collapse gives a strong deformation retraction of the original
polyhedron onto the terminal polyhedron. Consequently a collapsible polyhedron is
contractible, and the inclusion of the terminal polyhedron is a homotopy equivalence; for abstract
simplicial complexes this is the inclusion of realizations. Polyhedra are the support-defined
subspaces of any containing weak realization;
vertices removed by a collapse are absent from the target. Neither finiteness of the ambient
complex nor local finiteness is required.

The construction composes the elementary deformations from
`ElementaryCollapsesTo.exists_strong_deformation_retraction`, keeping the terminal
polyhedron fixed at every time, including along the empty collapse sequence.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*
(1972), Chapter 3 (simplicial collapse and its geometric deformation).
-/

public noncomputable section

open Set Function AbstractSimplicialComplex
open scoped ContinuousMap

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {K L : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι}

/-- Transport the elementary deformation from its nested target subtype to the flat
target polyhedron, expressing the fixed subset as the range of its inclusion. -/
private theorem ElementaryCollapsesTo.exists_strong_deformation_retraction_flat
    (h : ElementaryCollapsesTo K L)
    (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    let X : Set (Realization A) := {x | x.1.support ∈ K}
    let Y : Set (Realization A) := {x | x.1.support ∈ L}
    let i : C(Y, X) := ContinuousMap.inclusion (fun _ hx => h.le hx)
    ∃ r : C(X, Y), LeftInverse r i ∧
      (ContinuousMap.id X).HomotopicRel (i.comp r) (range i) := by
  obtain ⟨r, hr, ⟨H⟩⟩ := h.exists_strong_deformation_retraction hK
  let X : Set (Realization A) := {x | x.1.support ∈ K}
  let Y : Set (Realization A) := {x | x.1.support ∈ L}
  let i : C(Y, X) := ContinuousMap.inclusion (fun _ hx => h.le hx)
  -- Coercing the set X to a type gives exactly the subtype
  -- {x : Realization A // x.1.support ∈ K} used by the elementary theorem,
  -- with the same induced topology. Thus r, hr, and H need no source transport;
  -- the first endpoint of H.toHomotopy.cast below is unchanged (rfl).
  -- The nested target stores both K- and L-membership. Flatten it by retaining
  -- the ambient point and L-membership; continuity follows from the two projections.
  let r' : C(X, Y) :=
    ⟨fun x => ⟨(r x).1.1, (r x).2⟩,
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp r.continuous)).subtype_mk _⟩
  refine ⟨r', ?_, ⟨?_⟩⟩
  · intro x
    exact congrArg (fun y => (⟨y.1.1, y.2⟩ : Y))
      (hr ⟨i x, x.2⟩)
  · refine { toHomotopy := H.toHomotopy.cast rfl ?_, prop' := ?_ }
    · -- Both endpoint maps return the same point of X; Subtype.ext discards
      -- the differing membership proofs introduced by flattening and inclusion.
      ext x
      rfl
    · -- A point in range i has L-membership, so H already fixes it.
      rintro t x ⟨y, rfl⟩
      exact H.eq_fst t y.2

/-- A finite collapse strongly deformation retracts the original polyhedron onto its
terminal polyhedron. The retraction is a left inverse of the actual subspace inclusion,
and the homotopy fixes the image of that inclusion throughout. -/
theorem CollapsesTo.exists_strong_deformation_retraction (h : CollapsesTo K L)
    (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    let X : Set (Realization A) := {x | x.1.support ∈ K}
    let Y : Set (Realization A) := {x | x.1.support ∈ L}
    let i : C(Y, X) := ContinuousMap.inclusion (fun _ hx => h.le hx)
    ∃ r : C(X, Y), LeftInverse r i ∧
      (ContinuousMap.id X).HomotopicRel (i.comp r) (range i) := by
  induction h using CollapsesTo.trans_induction_on with
  | refl K =>
    refine ⟨ContinuousMap.id _, fun _ => rfl, ?_⟩
    -- Self-inclusion composed with id preserves every underlying point;
    -- extensionality identifies its endpoint with id regardless of membership proofs.
    exact ⟨(ContinuousMap.HomotopyRel.refl _ _).cast rfl (by ext x; rfl)⟩
  | @single K L h =>
    exact h.exists_strong_deformation_retraction_flat hK
  | @trans K P L hKP hPL ihKP ihPL =>
    obtain ⟨r, hr, hR⟩ := ihKP hK
    obtain ⟨s, hs, hS⟩ := ihPL (hKP.le.trans hK)
    refine ⟨s.comp r, ?_, ?_⟩
    · intro x
      exact (congrArg s (hr _)).trans (hs x)
    · have hi :
          (ContinuousMap.inclusion
            (s := {x : Realization A | x.1.support ∈ P})
            (t := {x : Realization A | x.1.support ∈ K}) (fun _ hx => hKP.le hx)).comp
          (ContinuousMap.inclusion
            (s := {x : Realization A | x.1.support ∈ L})
            (t := {x : Realization A | x.1.support ∈ P}) (fun _ hx => hPL.le hx)) =
          ContinuousMap.inclusion
            (s := {x : Realization A | x.1.support ∈ L})
            (t := {x : Realization A | x.1.support ∈ K})
            (fun _ hx => (hKP.trans hPL).le hx) := by
        exact ContinuousMap.inclusion_comp_inclusion _ _
      simpa only [hi] using hR.comp_retractions hS hr

/-- A collapsible polyhedron is contractible, with the subspace topology from any
containing weak realization. -/
theorem Collapsible.contractibleSpace (h : Collapsible K)
    (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    ContractibleSpace {x : Realization A // x.1.support ∈ K} := by
  classical
  obtain ⟨v, hv⟩ := collapsible_iff.mp h
  obtain ⟨r, _, hR⟩ := hv.exists_strong_deformation_retraction hK
  let X := {x : Realization A // x.1.support ∈ K}
  let p : X := ⟨vertex A v, hv.le (by
    rw [support_vertex]
    exact mem_point.mpr rfl)⟩
  have hend :
      (ContinuousMap.inclusion
        (s := {x : Realization A | x.1.support ∈ PreAbstractSimplicialComplex.point v})
        (t := {x : Realization A | x.1.support ∈ K}) (fun _ hx => hv.le hx)).comp r =
      ContinuousMap.const X p := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact Realization.eq_vertex_of_support_eq A (r x).1 (mem_point.mp (r x).2)
  exact (contractible_iff_id_nullhomotopic X).mpr ⟨p, hend ▸ hR.homotopic⟩

/-- The realization of a collapsible abstract simplicial complex is contractible. -/
theorem Collapsible.contractibleSpace_realization
    (h : Collapsible A.toPreAbstractSimplicialComplex) : ContractibleSpace (Realization A) := by
  have huniv : {x : Realization A | x.1.support ∈ A.toPreAbstractSimplicialComplex} = univ :=
    eq_univ_of_forall fun x => support_mem _ x
  have := h.contractibleSpace le_rfl
  exact ((Homeomorph.setCongr huniv).trans (Homeomorph.Set.univ _)).symm.contractibleSpace

namespace CollapsesTo

/-- **A collapse is a homotopy equivalence.** If `K` collapses to `L`, the inclusion of the
polyhedron of `L` into that of `K`, inside any containing weak realization, is a homotopy
equivalence. -/
theorem exists_homotopyEquiv (h : CollapsesTo K L) (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ L} ≃ₕ {x : Realization A // x.1.support ∈ K},
      (e : {x : Realization A // x.1.support ∈ L} → {x : Realization A // x.1.support ∈ K}) =
        fun x => ⟨x.1, h.le x.2⟩ := by
  obtain ⟨r, hr, hR⟩ := h.exists_strong_deformation_retraction hK
  refine ⟨.ofDeformationRetraction _ r hr hR.homotopic.symm, ?_⟩
  funext x
  rw [ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun]
  rfl

/-- If `K` collapses to `L`, the polyhedron of `L` is contractible exactly when that of `K` is,
inside any containing weak realization. -/
theorem contractibleSpace_iff (h : CollapsesTo K L) (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    ContractibleSpace {x : Realization A // x.1.support ∈ L} ↔
      ContractibleSpace {x : Realization A // x.1.support ∈ K} :=
  let ⟨e, _⟩ := h.exists_homotopyEquiv hK
  e.contractibleSpace_iff

/-- **A collapse of abstract simplicial complexes is a homotopy equivalence.** If `K` collapses to
`L`, the inclusion of the realization of `L` into that of `K` is a homotopy equivalence. -/
theorem exists_homotopyEquiv_realization {K L : AbstractSimplicialComplex ι}
    (h : CollapsesTo K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex) :
    ∃ e : Realization L ≃ₕ Realization K, (e : Realization L → Realization K) =
      realizationMap (toPreAbstractSimplicialComplex_le_iff.mp h.le) := by
  have hLK : L ≤ K := toPreAbstractSimplicialComplex_le_iff.mp h.le
  obtain ⟨e, he⟩ := h.exists_homotopyEquiv le_rfl
  let eL : Realization L ≃ₜ {x : Realization K | x.1.support ∈ L.toPreAbstractSimplicialComplex} :=
    (isClosedEmbedding_realizationMap hLK).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Set.ext fun x =>
        (mem_range_realizationMap hLK x).trans mem_toPreAbstractSimplicialComplex.symm))
  let eK : {x : Realization K | x.1.support ∈ K.toPreAbstractSimplicialComplex} ≃ₜ Realization K :=
    (Homeomorph.setCongr (eq_univ_of_forall fun x : Realization K =>
      mem_toPreAbstractSimplicialComplex.mpr (support_mem K x))).trans (Homeomorph.Set.univ _)
  refine ⟨eL.toHomotopyEquiv.trans (e.trans eK.toHomotopyEquiv), ?_⟩
  funext x
  change (eK (e (eL x)) : Realization K) = _
  rw [he]
  rfl

/-- If `K` collapses to `L`, the realization of `L` is contractible exactly when the realization
of `K` is. -/
theorem contractibleSpace_realization_iff {K L : AbstractSimplicialComplex ι}
    (h : CollapsesTo K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex) :
    ContractibleSpace (Realization L) ↔ ContractibleSpace (Realization K) :=
  let ⟨e, _⟩ := h.exists_homotopyEquiv_realization
  e.contractibleSpace_iff

end CollapsesTo

end PreAbstractSimplicialComplex
