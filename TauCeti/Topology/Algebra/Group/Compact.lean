/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open subgroups of a compact group

In a compact topological group, openness of a subgroup is the conjunction of two weaker
conditions: closedness and finite index. Mathlib has the two implications separately —
`Subgroup.isOpen_of_isClosed_of_finiteIndex` needs no compactness at all, while compactness
is exactly what makes the cosets of an open subgroup a finite open cover — and this file
records the resulting equivalence.

No total disconnectedness is involved: the statement holds for every compact group with
separately continuous multiplication, and it is the form used by the profinite development
to recognise finite index.

## Main results

* `Subgroup.isOpen_iff_isClosed_and_finiteIndex`: in a compact topological group, openness
  is equivalent to closedness together with finite index.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [CompactSpace G]

/-- A subgroup of a compact topological group is open exactly when it is closed and has
finite index. -/
theorem _root_.Subgroup.isOpen_iff_isClosed_and_finiteIndex (H : Subgroup G) :
    IsOpen (H : Set G) ↔ IsClosed (H : Set G) ∧ H.FiniteIndex := by
  constructor
  · intro hH
    have : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
    exact ⟨H.isClosed_of_isOpen hH, Subgroup.finiteIndex_of_finite_quotient⟩
  · rintro ⟨hH, hindex⟩
    let _ : H.FiniteIndex := hindex
    exact H.isOpen_of_isClosed_of_finiteIndex hH

end TauCeti
