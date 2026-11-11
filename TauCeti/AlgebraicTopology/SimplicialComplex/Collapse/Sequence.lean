/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Deformation
public import TauCeti.Topology.Homotopy.DeformationRetract
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Geometric deformation along finite collapse sequences

A finite simplicial collapse gives a strong deformation retraction of the original
polyhedron onto the terminal polyhedron. Consequently a collapsible polyhedron is
contractible. Polyhedra are the support-defined subspaces of any containing weak realization;
vertices removed by a collapse are absent from the target. Neither finiteness of the ambient
complex nor local finiteness is required.

More generally, a complex onto which a collapsible complex collapses has contractible
realization, even when it is not collapsible itself.

The construction composes the elementary deformations from
`ElementaryCollapsesTo.exists_strong_deformation_retraction`, keeping the terminal
polyhedron fixed at every time, including along the empty collapse sequence.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*
(1972), Chapter 3 (simplicial collapse and its geometric deformation).
-/

public noncomputable section

open Set Function AbstractSimplicialComplex

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

/-- If a collapsible complex collapses onto an abstract simplicial complex `L`, then the
realization of `L` is contractible, although `L` itself need not be collapsible. The polyhedron of
`L` is a strong deformation retract of the contractible polyhedron of the collapsible complex. -/
theorem CollapsesTo.contractibleSpace_realization {L : AbstractSimplicialComplex ι}
    (h : CollapsesTo K L.toPreAbstractSimplicialComplex) (hK : Collapsible K) :
    ContractibleSpace (Realization L) := by
  let T : AbstractSimplicialComplex ι := ⊤
  have hKT : K ≤ T.toPreAbstractSimplicialComplex := le_top
  have hLT : L ≤ T := le_top
  have := hK.contractibleSpace hKT
  obtain ⟨r, hr, hR⟩ := h.exists_strong_deformation_retraction hKT
  have hri : r.comp (ContinuousMap.inclusion fun _ hx => h.le hx) = ContinuousMap.id _ :=
    ContinuousMap.ext hr
  -- The retraction and the inclusion are mutually inverse homotopy equivalences.
  let e : ContinuousMap.HomotopyEquiv
      {x : Realization T | x.1.support ∈ L.toPreAbstractSimplicialComplex}
      {x : Realization T | x.1.support ∈ K} :=
    { toFun := ContinuousMap.inclusion fun _ hx => h.le hx
      invFun := r
      left_inv := hri ▸ ContinuousMap.Homotopic.refl _
      right_inv := hR.homotopic.symm }
  have := e.contractibleSpace
  have hrange : range (realizationMap hLT) =
      {x : Realization T | x.1.support ∈ L.toPreAbstractSimplicialComplex} := by
    ext x
    exact mem_range_realizationMap hLT x
  exact ((isClosedEmbedding_realizationMap hLT).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)).contractibleSpace

/-- The realization of a collapsible abstract simplicial complex is contractible. -/
theorem Collapsible.contractibleSpace_realization
    (h : Collapsible A.toPreAbstractSimplicialComplex) : ContractibleSpace (Realization A) :=
  (CollapsesTo.refl _).contractibleSpace_realization h

end PreAbstractSimplicialComplex
