/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Map

/-!
# Transporting filled covers along isomorphisms of covers

Let `h : E ≃ₜ F` be an isomorphism of covers of `ℂ ∖ {0, 1}`, a homeomorphism with `p' ∘ h = p`.
It transports the added points of the filled cover of `p` to those of `p'` by its bijection
`FilledPoint.congr h hh` on the components over the three punctures, preserving the local degree
at each added point (`TauCeti.FilledCover.degree_congr`). The local-degree comparison needs
neither finiteness nor the covering property.

When `p` is a covering map with finite fibres, `h` extends to a homeomorphism of filled covers
`TauCeti.FilledCover.congr`, which is `h` on `E` and is the transport of added points on the
added points, and which commutes with the extended projections to the Riemann sphere
(`TauCeti.FilledCover.fillMap_congr_apply`). The extension exists because the end of a filling
chart is intrinsic to the cover (`TauCeti.FilledCover.map_chart_comap_nhds_zero`): it is the
filter of points of the component going to infinity in `ℂ ∖ {0, 1}`, which `h` carries to the
corresponding filter for `p'`. Thus the filled cover is functorial in isomorphisms of covers:
the extension respects identities and composition (`TauCeti.FilledCover.congr_refl`,
`TauCeti.FilledCover.congr_trans`).

## Main declarations

* `TauCeti.FilledCover.degree_congr`: isomorphic covers have the same local degree at
  corresponding added points.
* `TauCeti.FilledCover.range_chart_congr`: an isomorphism of covers carries each component over a
  puncture onto the corresponding component.
* `TauCeti.FilledCover.congr`: the homeomorphism of filled covers extending an isomorphism of
  covers.
* `TauCeti.FilledCover.fillMap_congr_apply`: it commutes with the extended projections.
* `TauCeti.FilledCover.congr_refl`, `TauCeti.FilledCover.congr_trans`: the extension respects
  identities and composition.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §1.2.7.
* O. Forster, *Lectures on Riemann Surfaces*, §8, Theorems 8.4 and 8.5.
-/

public section

noncomputable section

namespace TauCeti

open Filter Function Set Topology ThricePuncturedSphere

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

section Homeomorph

variable (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
  (h : E ≃ₜ F) (hh : p' ∘ h = p)
include hp hfin hh

/-- **An isomorphism of covers carries components onto components.** The image under `h` of the
component of `p ⁻¹' D_q*` giving the added point `i` is the component of `p' ⁻¹' D_q*` giving the
transported added point. -/
theorem range_chart_congr (i : FilledPoint p) :
    range (chart p' (FilledPoint.congr h hh i)) = h '' range (chart p i) := by
  rw [← h.image_preimage (range (chart p' _))]
  congr 1
  ext x
  rw [mem_preimage, range_chart ((IsCoveringMap.comp_homeomorph_iff h).1 (hh ▸ hp))
    ((finite_coe_iff.1 (hh ▸ hfin)).of_preimage h.surjective).to_subtype,
    range_chart hp hfin, FilledPoint.sigmaEquiv_congr]
  simp only [mem_ofPred_eq]
  generalize FilledPoint.sigmaEquiv p i = s
  obtain ⟨q, c⟩ := s
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  let e := FilledPoint.neighborhoodCongr h hh q
  have hx : p' (h x) = p x := congr_fun hh x
  have he (hq : p x ∈ q.neighborhood) : e ⟨x, hq⟩ = ⟨h x, mem_preimage.2 (hx ▸ hq)⟩ :=
    Subtype.ext (FilledPoint.coe_neighborhoodCongr_apply h hh q _)
  simp only [Continuous.connectedComponentsMap_mk]
  constructor
  · rintro ⟨hq, H⟩
    have hq' : p x ∈ q.neighborhood := hx ▸ hq
    refine ⟨hq', ?_⟩
    -- Pull the equality of components back along the inverse of `e`.
    rw [← he hq'] at H
    have H' := congrArg e.symm.continuous.connectedComponentsMap H
    rwa [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk,
      Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at H'
  · rintro ⟨hq, H⟩
    refine ⟨hx ▸ hq, ?_⟩
    have H' := congrArg e.continuous.connectedComponentsMap H
    rwa [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk, he] at H'

/-- An isomorphism of covers carries the end of the filling chart of each added point onto the
end of the filling chart of the transported added point. -/
private theorem map_comp_chart_comap_nhds_zero (i : FilledPoint p) :
    map (h ∘ chart p i) (comap (↑) (𝓝 (0 : ℂ))) =
      map (chart p' (FilledPoint.congr h hh i)) (comap (↑) (𝓝 (0 : ℂ))) := by
  have hcomap : map h (comap p (cocompact ThricePuncturedSphere)) =
      comap p' (cocompact ThricePuncturedSphere) := by
    rw [← hh, ← comap_comap, map_comap_of_surjective h.surjective]
  rw [← map_map, map_chart_comap_nhds_zero hp hfin,
    map_chart_comap_nhds_zero ((IsCoveringMap.comp_homeomorph_iff h).1 (hh ▸ hp))
      ((finite_coe_iff.1 (hh ▸ hfin)).of_preimage h.surjective).to_subtype,
    range_chart_congr hp hfin, map_inf h.injective, map_principal, hcomap]

/-- **Functoriality of the filled cover in isomorphisms of covers.** An isomorphism `h : E ≃ₜ F`
over `ℂ ∖ {0, 1}` from a covering map `p` with finite fibres to `p'` extends to a homeomorphism
of their filled covers. It is `h` on `E` (`TauCeti.FilledCover.congr_apply_incl`), sends the added
point of a component to the added point of its image component
(`TauCeti.FilledCover.congr_apply_center`), and commutes with the extended projections to the
Riemann sphere (`TauCeti.FilledCover.fillMap_congr_apply`). -/
def congr : FilledCover p ≃ₜ FilledCover p' :=
  PunctureFilling.congr (fun i ↦ (isOpenEmbedding_chart hp hfin i).continuous)
    (fun i ↦ (isOpenEmbedding_chart ((IsCoveringMap.comp_homeomorph_iff h).1 (hh ▸ hp))
      ((finite_coe_iff.1 (hh ▸ hfin)).of_preimage h.surjective).to_subtype i).continuous)
    h (FilledPoint.congr h hh) (map_comp_chart_comap_nhds_zero hp hfin h hh)

@[simp]
theorem congr_apply_incl (x : E) :
    congr hp hfin h hh (PunctureFilling.incl (chart p) x) =
      PunctureFilling.incl (chart p') (h x) :=
  PunctureFilling.congr_apply_incl _ _ _ _ _ x

@[simp]
theorem congr_apply_center (i : FilledPoint p) :
    congr hp hfin h hh (PunctureFilling.center (chart p) i) =
      PunctureFilling.center (chart p') (FilledPoint.congr h hh i) :=
  PunctureFilling.congr_apply_center _ _ _ _ _ i

@[simp]
theorem congr_symm_apply_incl (x : F) :
    (congr hp hfin h hh).symm (PunctureFilling.incl (chart p') x) =
      PunctureFilling.incl (chart p) (h.symm x) :=
  PunctureFilling.congr_symm_apply_incl _ _ _ _ _ x

@[simp]
theorem congr_symm_apply_center (i : FilledPoint p') :
    (congr hp hfin h hh).symm (PunctureFilling.center (chart p') i) =
      PunctureFilling.center (chart p) ((FilledPoint.congr h hh).symm i) :=
  PunctureFilling.congr_symm_apply_center _ _ _ _ _ i

/-- **The extended homeomorphism lies over the Riemann sphere**: it commutes with the extended
projections `fillMap p` and `fillMap p'`. -/
@[simp]
theorem fillMap_congr_apply (y : FilledCover p) :
    fillMap p' (congr hp hfin h hh y) = fillMap p y := by
  induction y using PunctureFilling.induction with
  | incl x => simp [← congr_fun hh x]
  | center i => simp

end Homeomorph

section Functoriality

variable {G : Type*} [TopologicalSpace G] {p'' : G → ThricePuncturedSphere}
  (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))

/-- The identity isomorphism of covers extends to the identity of the filled cover. -/
@[simp]
theorem congr_refl :
    congr hp hfin (Homeomorph.refl E) (p' := p) (by simp) = Homeomorph.refl _ := by
  ext y
  induction y using PunctureFilling.induction <;> simp

/-- The extension of a composite of isomorphisms of covers is the composite of the extensions. -/
theorem congr_trans (hp' : IsCoveringMap p') {z₁ : ThricePuncturedSphere}
    (hfin' : Finite (p' ⁻¹' {z₁})) (h : E ≃ₜ F) (hh : p' ∘ h = p) (k : F ≃ₜ G)
    (hk : p'' ∘ k = p') :
    congr hp hfin (h.trans k) (by funext x; exact (congr_fun hk (h x)).trans (congr_fun hh x)) =
      (congr hp hfin h hh).trans (congr hp' hfin' k hk) := by
  ext y
  induction y using PunctureFilling.induction <;> simp [FilledPoint.congr_trans h hh k hk]

end Functoriality

end FilledCover

end TauCeti
