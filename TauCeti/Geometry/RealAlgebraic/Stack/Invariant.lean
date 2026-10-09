/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Local

/-!
# Gluing constant data on root sections

Suppose a real polynomial family admits local delineations, and a quantity is constant along
each section of each local stack. Then the quantity is locally constant along every section
of any global delineation. Over a preconnected base it is constant along each global section,
and the local stacks themselves glue to a global delineation.

The quantity may take values in any type, with no topology. In particular, it can be the
ambient polynomial order at a section point. Its values on sectors are unconstrained. Root
labels need no identification in the hypotheses: increasing complete root lists identify the
sections on overlaps. Neither finiteness of the polynomial family nor continuity of its
coefficients is required.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268, Sections 2–3 (order-invariance and globalization of delineability).
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {X ι α : Type*} [TopologicalSpace X] {P : ι → X → ℝ[X]}

/-- If a quantity is constant on the sections of local delineations around every point, it is
locally constant on the sections of any global delineation. No agreement of local labels is
assumed. -/
theorem Delineation.isLocallyConstant_root_of_locally (D : Delineation P) (q : X → ℝ → α)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ D' : Delineation (fun k (y : U) ↦ P k y),
        ∀ i, ∀ y z : U, q y (D'.root i y) = q z (D'.root i z))
    (i : Fin D.count) : IsLocallyConstant (fun x ↦ q x (D.root i x)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ ?_
  obtain ⟨U, hU, hxU, D', hq⟩ := hlocal x
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  -- Restricting the global stack gives the unique delineation of the local family.
  have hD : D.comp Subtype.val continuous_subtype_val = D' := Subsingleton.elim _ _
  rw [← hD] at hq
  filter_upwards [hU.mem_nhds hxU] with y hy
  have h := hq (Fin.cast (D.comp_count Subtype.val continuous_subtype_val).symm i)
    ⟨y, hy⟩ ⟨x, hxU⟩
  simpa only [Delineation.comp_root, Fin.cast_cast, Fin.cast_refl, id_eq] using h

/-- Local delineations carrying quantities constant along their sections glue over a
preconnected base to a global delineation with those quantities constant along its sections.
The constants, root counts, and local root labels may depend on the neighborhood. -/
theorem exists_delineation_of_locally_const_on_sections [PreconnectedSpace X]
    (q : X → ℝ → α)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ D : Delineation (fun k (y : U) ↦ P k y),
        ∀ i, ∀ y z : U, q y (D.root i y) = q z (D.root i z)) :
    ∃ D : Delineation P, ∀ i, ∀ x y, q x (D.root i x) = q y (D.root i y) := by
  obtain ⟨D⟩ := nonempty_delineation_of_locally fun x ↦ by
    obtain ⟨U, hU, hxU, D, _⟩ := hlocal x
    exact ⟨U, hU, hxU, ⟨D⟩⟩
  exact ⟨D, fun i ↦ (D.isLocallyConstant_root_of_locally q hlocal i).apply_eq_of_preconnectedSpace⟩

end TauCeti
