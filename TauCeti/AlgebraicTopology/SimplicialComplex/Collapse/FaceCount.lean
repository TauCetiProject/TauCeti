/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic
public import Mathlib.Data.Set.Card

/-!
# Face counts under simplicial collapse

An elementary simplicial collapse removes exactly its free face and unique coface.  This file
turns that description into numerical control of finite complexes: every elementary collapse
decreases the number of faces by two, while an arbitrary collapse can only decrease it.

These facts are basic bookkeeping for the collapse track in layer 11 of the geometric-topology
roadmap.  In particular, they provide a termination measure for finite collapse arguments and
the parity obstruction that any proposed collapse certificate must satisfy.  The definitions of
free pairs and collapse are those in `ElementaryCollapse` and `Collapse`, following
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3.

## Main results

* `ElementaryCollapsesTo.ncard_faces_add_two`: the face counts before and after an elementary
  collapse differ by two.
* `CollapsesTo.ncard_faces_le`: a finite collapse cannot increase the number of faces.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*}
  {K L : _root_.PreAbstractSimplicialComplex ι}

namespace ElementaryCollapsesTo

/-- The set of faces after an elementary collapse is finite whenever the original face set is
finite. -/
theorem finite_faces (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    L.faces.Finite :=
  hK.subset h.le

/-- An elementary collapse of a finite complex removes exactly two faces. -/
theorem ncard_faces_add_two (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces + 2 = Set.ncard K.faces := by
  obtain ⟨σ, τ, hfree, hστ, hmem⟩ := h.exists_pair
  have hpair : ({σ, τ} : Set (Finset ι)) ⊆ K.faces := by
    rw [Set.pair_subset_iff]
    exact ⟨hfree.lower_mem, hfree.upper_mem⟩
  have hfaces : L.faces = K.faces \ {σ, τ} := by
    ext ω
    change (ω ∈ L ↔ ω ∈ K ∧ ω ∉ ({σ, τ} : Set (Finset ι)))
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hmem ω
  rw [hfaces]
  calc
    Set.ncard (K.faces \ {σ, τ}) + 2 =
        Set.ncard (K.faces \ {σ, τ}) + Set.ncard ({σ, τ} : Set (Finset ι)) := by
          rw [Set.ncard_pair hστ.ne]
    _ = Set.ncard K.faces := Set.ncard_sdiff_add_ncard_of_subset hpair hK

/-- The face count after an elementary collapse is the original face count minus two. -/
theorem ncard_faces_eq_sub_two (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces = Set.ncard K.faces - 2 := by
  have hcount := h.ncard_faces_add_two hK
  omega

/-- An elementary collapse strictly decreases the number of faces of a finite complex. -/
theorem ncard_faces_lt (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces < Set.ncard K.faces := by
  have hcount := h.ncard_faces_add_two hK
  omega

/-- An elementary collapse preserves the parity of the number of faces. -/
theorem ncard_faces_mod_two (h : ElementaryCollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces % 2 = Set.ncard K.faces % 2 := by
  have hcount := h.ncard_faces_add_two hK
  omega

end ElementaryCollapsesTo

namespace CollapsesTo

/-- A collapse of a finite complex cannot increase its number of faces. -/
theorem ncard_faces_le (h : CollapsesTo K L) (hK : K.faces.Finite) :
    Set.ncard L.faces ≤ Set.ncard K.faces :=
  Set.ncard_le_ncard h.le hK

/-- The endpoint of a collapse of a finite complex again has finitely many faces. -/
theorem finite_faces (h : CollapsesTo K L) (hK : K.faces.Finite) :
    L.faces.Finite :=
  hK.subset h.le

end CollapsesTo

end PreAbstractSimplicialComplex

end TauCeti
