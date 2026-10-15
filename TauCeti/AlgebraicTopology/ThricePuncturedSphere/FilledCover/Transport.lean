/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Transport of filled points under isomorphisms of covers

A homeomorphism over the thrice-punctured sphere restricts to a homeomorphism over each
standard punctured neighbourhood. It therefore transports the connected components that label
the added points of a filled cover. This transport preserves the puncture and the local degree,
and respects identities, inverses, and composition.

The construction needs neither finiteness nor the covering property: these hypotheses are
needed for the filling charts, not for transporting components or counting their fibres.
This is the added-point part of extending an isomorphism to the filled covers. The component
bijections use Mathlib's `Topology.IsCoinducing.connectedComponentsHomeomorph`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §1.2.7.
* O. Forster, *Lectures on Riemann Surfaces*, §8, Theorems 8.4 and 8.5.
-/

public section

noncomputable section

namespace TauCeti

open Function Set ThricePuncturedSphere

variable {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → ThricePuncturedSphere} {p' : F → ThricePuncturedSphere}
  {p'' : G → ThricePuncturedSphere}

namespace FilledPoint

/-- Restrict an isomorphism over the sphere to the preimage of a standard punctured
neighbourhood. -/
def neighborhoodCongr (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture) :
    (p ⁻¹' q.neighborhood) ≃ₜ (p' ⁻¹' q.neighborhood) :=
  h.subtype fun x ↦ by simp only [mem_preimage, ← congr_fun hh x, comp_apply]

@[simp]
theorem coe_neighborhoodCongr_apply (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture)
    (x : p ⁻¹' q.neighborhood) : (neighborhoodCongr h hh q x : F) = h x :=
  (rfl)

@[simp]
theorem coe_neighborhoodCongr_symm_apply (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture)
    (y : p' ⁻¹' q.neighborhood) : ((neighborhoodCongr h hh q).symm y : E) = h.symm y :=
  (rfl)

/-- An isomorphism over the sphere transports added points by its induced bijection on
components over each puncture. -/
def congr (h : E ≃ₜ F) (hh : p' ∘ h = p) : FilledPoint p ≃ FilledPoint p' :=
  (sigmaEquiv p).trans <| (Equiv.sigmaCongrRight fun q ↦
    ((neighborhoodCongr h hh q).isQuotientMap.isCoinducing.connectedComponentsHomeomorph
      fun y ↦ by
        convert (isConnected_singleton (x := (neighborhoodCongr h hh q).symm y)) using 1
        ext x
        exact (neighborhoodCongr h hh q).eq_symm_apply.symm).toEquiv).trans (sigmaEquiv p').symm

/-- The puncture and component of a transported point. -/
@[simp]
theorem sigmaEquiv_congr (h : E ≃ₜ F) (hh : p' ∘ h = p) (i : FilledPoint p) :
    sigmaEquiv p' (congr h hh i) =
      ⟨(sigmaEquiv p i).1,
        (neighborhoodCongr h hh (sigmaEquiv p i).1).continuous.connectedComponentsMap
          (sigmaEquiv p i).2⟩ := by
  simp [congr, Topology.IsCoinducing.connectedComponentsHomeomorph]

/-- On a component represented by a point, transport is represented by the image point. -/
@[simp]
theorem congr_sigmaEquiv_symm_mk (h : E ≃ₜ F) (hh : p' ∘ h = p) (q : Puncture)
    (x : p ⁻¹' q.neighborhood) :
    congr h hh ((sigmaEquiv p).symm ⟨q, ConnectedComponents.mk x⟩) =
      (sigmaEquiv p').symm ⟨q, ConnectedComponents.mk (neighborhoodCongr h hh q x)⟩ := by
  apply (sigmaEquiv p').injective
  rw [sigmaEquiv_congr, Equiv.apply_symm_apply]
  simp only [Equiv.apply_symm_apply, Continuous.connectedComponentsMap_mk]

/-- Transport does not change the puncture label. -/
@[simp]
theorem puncture_congr (h : E ≃ₜ F) (hh : p' ∘ h = p) (i : FilledPoint p) :
    puncture p' (congr h hh i) = puncture p i := by
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p).symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hi := congr_sigmaEquiv_symm_mk h hh q x
  rw [hi]
  cases q with
  | zero =>
    simp only [sigmaEquiv_symm_zero]
    exact (puncture_overZero _ _).trans (puncture_overZero _ _).symm
  | one =>
    simp only [sigmaEquiv_symm_one]
    exact (puncture_overOne _ _).trans (puncture_overOne _ _).symm
  | inf =>
    simp only [sigmaEquiv_symm_inf]
    exact (puncture_overInf _ _).trans (puncture_overInf _ _).symm

/-- Identity isomorphisms fix every added point. -/
@[simp]
theorem congr_refl : congr (Homeomorph.refl E) (p := p) (by simp) = Equiv.refl _ := by
  ext i
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p).symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [congr_sigmaEquiv_symm_mk]
  rfl

/-- Transport along a composite is the composite of the two transports. -/
theorem congr_trans (h : E ≃ₜ F) (hh : p' ∘ h = p) (k : F ≃ₜ G)
    (hk : p'' ∘ k = p') :
    congr (h.trans k) (by funext x; exact (congr_fun hk (h x)).trans (congr_fun hh x)) =
      (congr h hh).trans (congr k hk) := by
  ext i
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p).symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp only [Equiv.trans_apply, congr_sigmaEquiv_symm_mk]
  rfl

/-- Transport along the inverse isomorphism reverses transport. -/
@[simp]
theorem symm_congr (h : E ≃ₜ F) (hh : p' ∘ h = p) :
    (congr h hh).symm =
      congr h.symm (by funext y; simpa using (congr_fun hh (h.symm y)).symm) := by
  symm
  ext i
  apply (congr h hh).injective
  obtain ⟨⟨q, c⟩, rfl⟩ := (sigmaEquiv p').symm.surjective i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp only [congr_sigmaEquiv_symm_mk, Equiv.apply_symm_apply]
  congr 2
  congr 1
  apply Subtype.ext
  simp

end FilledPoint

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
  exact (congr_fun hh _).symm

end FilledCover

end TauCeti
