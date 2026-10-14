/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# Products of cofibrations with spaces

If a closed subset `A ⊆ X` has the homotopy extension property, then so does
`P × A ⊆ P × X` for every space `P`.  The proof uses the retraction characterization of
the homotopy extension property: a retraction of `I × X` onto
`{0} × X ∪ I × A` acts on the time and `X` coordinates and leaves the `P` coordinate
fixed.

This product stability is the topological input for lifting homotopies through restriction maps
between compact-open mapping spaces.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

open Set unitInterval

universe u v

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {A : Set X}
  {P : Type v} [TopologicalSpace P]

/-- **The product of a closed cofibration with a space is a closed cofibration.**  In the subset
formulation, if `A ⊆ X` is closed and has the homotopy extension property, then the subset of
`P × X` consisting of pairs whose second coordinate lies in `A` also has the homotopy extension
property. -/
theorem HasHomotopyExtensionProperty.prod_left (h : HasHomotopyExtensionProperty A)
    (hA : IsClosed A) :
    HasHomotopyExtensionProperty {q : P × X | q.2 ∈ A} := by
  obtain ⟨r, hr, hr'⟩ := h.exists_retraction
  let R : C(I × (P × X), I × (P × X)) :=
    ⟨fun q ↦ ((r (q.1, q.2.2)).1, (q.2.1, (r (q.1, q.2.2)).2)), by fun_prop⟩
  refine hasHomotopyExtensionProperty_of_retraction (hA.preimage continuous_snd)
    (r := R) (fun q ↦ ?_) (fun q hq ↦ ?_)
  · apply (mem_cylinderExtensionDomain_iff (A := {q : P × X | q.2 ∈ A})).2
    simpa [R] using (mem_cylinderExtensionDomain_iff (A := A)).1 (hr (q.1, q.2.2))
  · have hq' : (q.1, q.2.2) ∈ cylinderExtensionDomain A := by
      apply (mem_cylinderExtensionDomain_iff (A := A)).2
      exact ((mem_cylinderExtensionDomain_iff (A := {q : P × X | q.2 ∈ A})).1 hq).elim
        Or.inl Or.inr
    have heq := hr' (q.1, q.2.2) hq'
    simp [R, heq]

end TauCeti

end
