/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic

/-!
# Products of closed cofibrations with arbitrary spaces

If a closed subset `A ⊆ X` has the homotopy extension property, then so does `Y × A ⊆ Y × X`
for every space `Y`. No compactness or separation hypothesis on the parameter space is needed.
This allows homotopies to be extended continuously in additional parameters, in particular
when proving the homotopy lifting property of restriction between compact-open mapping spaces.

The construction uses the cylinder retraction characterization of
`TauCeti.HasHomotopyExtensionProperty.exists_retraction` and leaves the parameter unchanged.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I, homotopy extension and cofibrations.
-/

public section

open Set unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}

/-- A closed cofibration remains a cofibration after taking its product with any space. -/
theorem HasHomotopyExtensionProperty.univ_prod (h : HasHomotopyExtensionProperty A)
    (hA : IsClosed A) : HasHomotopyExtensionProperty ((univ : Set Y) ×ˢ A) := by
  obtain ⟨r, hr, hr'⟩ := h.exists_retraction
  let R : C(I × (Y × X), I × (Y × X)) :=
    ⟨fun q ↦ ((r (q.1, q.2.2)).1, (q.2.1, (r (q.1, q.2.2)).2)), by fun_prop⟩
  refine hasHomotopyExtensionProperty_of_retraction (isClosed_univ.prod hA)
    (r := R) (fun q ↦ ?_) (fun q hq ↦ ?_)
  · exact mem_cylinderExtensionDomain_iff.mpr
      ((mem_cylinderExtensionDomain_iff.mp (hr (q.1, q.2.2))).imp id
        (fun hx ↦ ⟨mem_univ _, hx⟩))
  · have hq' : (q.1, q.2.2) ∈ cylinderExtensionDomain A := by
      rcases mem_cylinderExtensionDomain_iff.mp hq with h₀ | h₁
      · exact mem_cylinderExtensionDomain_iff.mpr (Or.inl h₀)
      · exact mem_cylinderExtensionDomain_iff.mpr (Or.inr h₁.2)
    simp [R, hr' _ hq']

end TauCeti
