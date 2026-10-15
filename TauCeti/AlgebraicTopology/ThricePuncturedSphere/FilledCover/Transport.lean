/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic

/-!
# Local-degree preservation under isomorphisms of covers

The added-point transport `FilledPoint.congr` preserves the local degree at each added point.
It uses the homeomorphism over each standard punctured neighbourhood to identify the fibres
whose cardinalities define the local degrees.

The construction needs neither finiteness nor the covering property: these hypotheses are
needed for the filling charts, not for transporting components or counting their fibres.
This is the degree comparison needed to extend an isomorphism to the filled covers.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §1.2.7.
* O. Forster, *Lectures on Riemann Surfaces*, §8, Theorems 8.4 and 8.5.
-/

public section

noncomputable section

namespace TauCeti

open Function Set ThricePuncturedSphere

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
  {p : E → ThricePuncturedSphere} {p' : F → ThricePuncturedSphere}

namespace FilledCover

/-- Isomorphic covers have the same local degree at corresponding added points. -/
@[simp]
theorem degree_congr (h : E ≃ₜ F) (hh : p' ∘ h = p) (i : FilledPoint p) :
    degree p' (FilledPoint.congr h hh i) = degree p i := by
  rw [degree_def, degree_def]
  -- Express the component sets through their membership API: set equalities are needed to
  -- transport the domains of the restricted maps whose fibres define the degrees.
  rw [show component p i = ConnectedComponents.mk ⁻¹' {(FilledPoint.sigmaEquiv p i).2}
    from Set.ext fun _ ↦ mem_component_iff p]
  rw [show component p' (FilledPoint.congr h hh i) =
      ConnectedComponents.mk ⁻¹' {(FilledPoint.sigmaEquiv p' (FilledPoint.congr h hh i)).2}
    from Set.ext fun _ ↦ mem_component_iff p']
  rw [FilledPoint.sigmaEquiv_congr]
  let q := (FilledPoint.sigmaEquiv p i).1
  let c := (FilledPoint.sigmaEquiv p i).2
  let e := FilledPoint.neighborhoodCongr h hh q
  let ce := e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y ↦ by
      convert (isConnected_singleton (x := e.symm y)) using 1
      ext x
      exact e.eq_symm_apply.symm)
  have hm (x : p ⁻¹' q.neighborhood) :
      ConnectedComponents.mk x = c ↔ ConnectedComponents.mk (e x) = ce c := by
    rw [← ce.injective.eq_iff]
    simp [ce]
  let ec := e.subtype (p := fun x ↦ ConnectedComponents.mk x = c)
    (q := fun y ↦ ConnectedComponents.mk y = ce c) hm
  refine (Nat.card_congr (ec.toEquiv.subtypeEquiv fun x ↦ ?_)).symm
  suffices heq : q.coord (q.neighborhood.restrictPreimage p x.val) =
      q.coord (q.neighborhood.restrictPreimage p' (ec x).val) by
    exact congrArg (· = puncturedDiscBasepoint) heq |>.to_iff
  congr 1
  apply Subtype.ext
  exact ((congrArg p' (FilledPoint.coe_neighborhoodCongr_apply h hh q x.val)).trans
    (congr_fun hh _)).symm

end FilledCover

end TauCeti
