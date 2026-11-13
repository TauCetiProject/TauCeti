/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Connected.Ends.Basic
public import TauCeti.Topology.Homotopy.Proper

/-!
# Proper maps on ends

A proper continuous map induces a map on ends. Its component outside a compact set `K` is
obtained by mapping the source end's component outside the compact preimage of `K`.
A compact exhaustion of the target realizes these compatible components as an end.
The resulting map is independent of that exhaustion, respects identities and composition,
and is unchanged by a homotopy that is proper as a map on the whole cylinder.
Consequently a proper homotopy equivalence induces an equivalence on ends.

The target spaces are assumed to admit compact exhaustions, as do locally compact
second-countable manifolds and locally finite countable CW complexes.

## References

* H. Freudenthal, *Über die Enden topologischer Räume und Gruppen*, Math. Z. 33 (1931), 692–713.
* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, §1.
-/

public section

noncomputable section

open CategoryTheory Set

namespace TauCeti.EndComponents

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private def mapComponent (e : EndComponents X) (f : C(X, Y)) (hf : IsProperMap f)
    {K : Set Y} (hK : IsCompact K) : ConnectedComponents ↥Kᶜ :=
  (f.restrictPreimage Kᶜ).continuous.connectedComponentsMap
    (e.component (hf.isCompact_preimage hK))

private theorem mapComponent_mono (e : EndComponents X) (f : C(X, Y)) (hf : IsProperMap f)
    {K L : Set Y} (hK : IsCompact K) (hL : IsCompact L) (h : K ⊆ L) :
    (continuous_inclusion (compl_subset_compl.2 h)).connectedComponentsMap
      (mapComponent e f hf hL) = mapComponent e f hf hK := by
  rw [mapComponent, mapComponent,
    ← e.connectedComponentsMap_component (hf.isCompact_preimage hK)
      (hf.isCompact_preimage hL) (preimage_mono h)]
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe
    (e.component (hf.isCompact_preimage hL))
  rw [← hx]
  simp only [Continuous.connectedComponentsMap_mk]
  rfl

variable [WeaklyLocallyCompactSpace Y] [SigmaCompactSpace Y]

/-- The map on ends induced by a proper continuous map. Its component outside a compact set
is the image of the source component outside that set's preimage (`component_map`). -/
def map (e : EndComponents X) (f : C(X, Y)) (hf : IsProperMap f) : EndComponents Y :=
  let K := CompactExhaustion.choice Y
  K.endComponentsEquivSections.symm
    ⟨fun n ↦ mapComponent e f hf (K.isCompact n.unop),
      fun {_ _} a ↦ mapComponent_mono e f hf _ _ (K.subset (leOfHom a.unop))⟩

private theorem component_map_exhaustion (e : EndComponents X) (f : C(X, Y))
    (hf : IsProperMap f) (n : ℕ) :
    (e.map f hf).component ((CompactExhaustion.choice Y).isCompact n) =
      mapComponent e f hf ((CompactExhaustion.choice Y).isCompact n) := by
  simp only [map, CompactExhaustion.endComponentsEquivSections_symm_apply, component_mk]
  exact EndSequence.component_ofSections _ _ _ _ n

/-- The component of the image end outside `K` is obtained by mapping the source end's
component outside `f ⁻¹' K`. This characterizes the map without choosing an exhaustion. -/
@[simp]
theorem component_map (e : EndComponents X) (f : C(X, Y)) (hf : IsProperMap f)
    {K : Set Y} (hK : IsCompact K) :
    (e.map f hf).component hK =
      (f.restrictPreimage Kᶜ).continuous.connectedComponentsMap
        (e.component (hf.isCompact_preimage hK)) := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice Y).exists_superset_of_isCompact hK
  rw [← (e.map f hf).connectedComponentsMap_component hK
    ((CompactExhaustion.choice Y).isCompact n) hn, component_map_exhaustion]
  exact mapComponent_mono e f hf hK ((CompactExhaustion.choice Y).isCompact n) hn

/-- The identity map fixes every end. -/
@[simp]
theorem map_id [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] (e : EndComponents X) :
    e.map (ContinuousMap.id X) (by simp) = e := by
  apply ext_component
  intro K hK
  -- Rewriting must see through the coercion of the bundled identity in its properness proof.
  erw [component_map]
  simp only [ContinuousMap.coe_id, preimage_id]
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.component hK)
  rw [← hx]
  simp only [Continuous.connectedComponentsMap_mk]
  rfl

/-- A jointly proper homotopy induces the same map on ends at both endpoints. Properness
of the time slices alone is not sufficient. -/
theorem map_eq_of_proper_homotopy (e : EndComponents X) {f g : C(X, Y)}
    (hf : IsProperMap f) (hg : IsProperMap g) (H : ContinuousMap.Homotopy f g)
    (hH : IsProperMap H) : e.map f hf = e.map g hg := by
  apply ext_component
  intro K hK
  let P := Prod.snd '' (H ⁻¹' K)
  have hP : IsCompact P := (hH.isCompact_preimage hK).image continuous_snd
  have hfP : f ⁻¹' K ⊆ P := fun x hx ↦ ⟨(0, x), by simpa using hx, rfl⟩
  have hgP : g ⁻¹' K ⊆ P := fun x hx ↦ ⟨(1, x), by simpa using hx, rfl⟩
  rw [component_map, component_map,
    ← e.connectedComponentsMap_component (hf.isCompact_preimage hK) hP hfP,
    ← e.connectedComponentsMap_component (hg.isCompact_preimage hK) hP hgP]
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.component hP)
  rw [← hx]
  simp only [Continuous.connectedComponentsMap_mk]
  have havoid (t) : H (t, x) ∉ K := fun ht ↦ x.2 ⟨(t, x), ht, rfl⟩
  let γ : Path ((f.restrictPreimage Kᶜ) (inclusion (compl_subset_compl.2 hfP) x))
      ((g.restrictPreimage Kᶜ) (inclusion (compl_subset_compl.2 hgP) x)) :=
    { toFun := fun t ↦ ⟨H (t, x), havoid t⟩
      continuous_toFun := (H.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _
      source' := Subtype.ext (H.apply_zero x)
      target' := Subtype.ext (H.apply_one x) }
  exact ConnectedComponents.coe_eq_coe'.2 (pathComponent_subset_component _ ⟨γ.symm⟩)

variable [WeaklyLocallyCompactSpace Z] [SigmaCompactSpace Z]

/-- Maps on ends respect composition of proper maps. -/
@[simp]
theorem map_comp (e : EndComponents X) (f : C(X, Y)) (hf : IsProperMap f)
    (g : C(Y, Z)) (hg : IsProperMap g) :
    (e.map f hf).map g hg = e.map (g.comp f) (by simpa using hg.comp hf) := by
  apply ext_component
  intro K hK
  rw [component_map, component_map, component_map]
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe
    (e.component (hf.isCompact_preimage (hg.isCompact_preimage hK)))
  rw [← hx]
  simp only [Continuous.connectedComponentsMap_mk]
  rfl

end TauCeti.EndComponents

namespace ContinuousMap.HasProperHomotopyInverse

open TauCeti

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
  [WeaklyLocallyCompactSpace Y] [SigmaCompactSpace Y]

/-- A proper homotopy equivalence induces a bijection on ends. The inverse is the map on
ends induced by any proper inverse with jointly proper inverse homotopies. -/
theorem endComponentsMap_bijective {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    Function.Bijective (fun e : EndComponents X ↦ e.map f hf.isProperMap) := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf.exists_inverse
  have hleft : Function.LeftInverse (fun e : EndComponents Y ↦ e.map g hg)
      (fun e : EndComponents X ↦ e.map f hf.isProperMap) := by
    intro e
    dsimp only
    rw [EndComponents.map_comp,
      EndComponents.map_eq_of_proper_homotopy e _ (by simp) H hH, EndComponents.map_id]
  have hright : Function.RightInverse (fun e : EndComponents Y ↦ e.map g hg)
      (fun e : EndComponents X ↦ e.map f hf.isProperMap) := by
    intro e
    dsimp only
    rw [EndComponents.map_comp,
      EndComponents.map_eq_of_proper_homotopy e _ (by simp) H' hH', EndComponents.map_id]
  exact ⟨hleft.injective, hright.surjective⟩

/-- The equivalence on ends induced by a proper homotopy equivalence, with forward map
induced by the given continuous map. -/
def endComponentsEquiv {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    EndComponents X ≃ EndComponents Y :=
  Equiv.ofBijective _ hf.endComponentsMap_bijective

@[simp]
theorem endComponentsEquiv_apply {f : C(X, Y)} (hf : f.HasProperHomotopyInverse)
    (e : EndComponents X) : hf.endComponentsEquiv e = e.map f hf.isProperMap :=
  (rfl)

/-- Given a proper right inverse up to a jointly proper homotopy, the inverse equivalence
on ends is the map induced by that specified inverse. -/
theorem endComponentsEquiv_symm_apply {f : C(X, Y)} (hf : f.HasProperHomotopyInverse)
    (g : C(Y, X)) (hg : IsProperMap g)
    (H : Homotopy (f.comp g) (ContinuousMap.id Y)) (hH : IsProperMap H)
    (e : EndComponents Y) : hf.endComponentsEquiv.symm e = e.map g hg := by
  apply hf.endComponentsEquiv.injective
  rw [Equiv.apply_symm_apply, endComponentsEquiv_apply, EndComponents.map_comp,
    EndComponents.map_eq_of_proper_homotopy e _ (by simp) H hH, EndComponents.map_id]

end ContinuousMap.HasProperHomotopyInverse
