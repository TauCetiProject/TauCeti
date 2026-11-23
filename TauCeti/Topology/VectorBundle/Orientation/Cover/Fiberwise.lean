/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Comap
public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# The orientation double cover of a fibrewise isomorphism

Let `E' → B'` and `E → B` be real vector bundles with model fibres `F'` and `F`, let `g : B' → B`
be a continuous map, and let `φ b' : E'_{b'} ≃ E_{g b'}` be a family of continuous linear
equivalences whose total-space map `v ↦ (g (π v), φ (π v) v)` is continuous. Sending an
orientation `o` of `E'_{b'}` to its image under `φ b'`, an orientation of `E_{g b'}`, is a
continuous map of orientation double covers (`TauCeti.VectorBundleOrientationCover.map`) over
`g`, commuting with the deck involutions that reverse orientations
(`TauCeti.VectorBundleOrientationCover.map_deck`). It is continuous because, near each point, `φ`
carries the orientations that a trivialization of `E'` reads alike to orientations that a
trivialization of `E` reads alike
(`TauCeti.VectorBundleOrientation.eventually_mapOrientation_map_eq`), so the preimage of a sheet
is open.

Over the identity of a common base, the map of covers carries orientations of `E'` to orientations
of `E`. With the transport `TauCeti.VectorBundleOrientation.comap` in the other direction, this
shows that `E'` is orientable if and only if `E` is
(`TauCeti.VectorBundleOrientation.nonempty_iff_of_fiberwise`), without asking the inverse of `φ`
to be continuous on total spaces. The map of covers also induces an isomorphism of orientation
local systems `o(E) ≅ o(E')`
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfFiberwise`, in
`TauCeti.Topology.VectorBundle.Orientation.LocalSystem`).

## Main definitions

* `TauCeti.VectorBundleOrientationCover.map`: the map of orientation double covers induced by a
  fibrewise isomorphism.

## Main results

* `TauCeti.VectorBundleOrientationCover.map_deck`: the map of covers commutes with the deck
  involutions.
* `TauCeti.VectorBundleOrientation.nonempty_iff_of_fiberwise`: isomorphic bundles over the same
  base are orientable together.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (orientation-preserving bundle maps) and §12 (the orientation double
  cover).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Topology

namespace TauCeti

namespace VectorBundleOrientationCover

section Map

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {B' : Type*} [TopologicalSpace B']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {E' : B' → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  {ι : Type*} [Fintype ι] {g : C(B', B)} {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}
  (hι : Fintype.card ι = finrank ℝ F')
  (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))

include hι hφ in
/-- The points of the orientation double cover of `E'` whose image under `φ` lies on a sheet of
the orientation double cover of `E` form an open set. -/
private theorem isOpen_setOf_mk_map_mem_sheet (b : B) (o : Orientation ℝ F ι) :
    IsOpen {p : VectorBundleOrientationCover F' E' ι |
      (⟨g p.proj, Orientation.map ι (φ p.proj).toLinearEquiv p.orientation⟩ :
        VectorBundleOrientationCover F E ι) ∈ sheet (trivializationAt F E b) o} := by
  refine isOpen_iff_mem_nhds.2 fun p hp ↦ ?_
  obtain ⟨hpe, hpo⟩ := mem_sheet_iff.1 hp
  set e' := trivializationAt F' E' p.proj
  have hp' : p.proj ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.proj
  -- Near `p`, on the sheet of `e'` through `p`, the images under `φ` read in the sheet of `p`'s
  -- image.
  filter_upwards [continuous_proj.continuousAt.preimage_mem_nhds
      ((VectorBundleOrientation.eventually_mapOrientation_map_eq hι hφ _ e' hp' hpe
        p.orientation).and ((trivializationAt F E b).open_baseSet.preimage g.continuous
          |>.mem_nhds hpe)),
    (isOpen_sheet_trivializationAt p.proj _).mem_nhds (mem_sheet_iff.2 ⟨hp', rfl⟩)]
    with q ⟨hqS, hq⟩ hqc
  obtain ⟨hq', hqc⟩ := mem_sheet_iff.1 hqc
  exact mem_sheet_iff.2 ⟨hq, (hqS hq' hq _ hqc).trans hpo⟩

/-- **The map of orientation double covers induced by a fibrewise isomorphism.** For a fibrewise
isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over a continuous map `g : B' → B`, with continuous
total-space map, the continuous map sending an orientation of `E'_{b'}` to its image under `φ b'`,
an orientation of `E_{g b'}`. This needs `ι` to have cardinality the rank of `E'`. -/
def map : C(VectorBundleOrientationCover F' E' ι, VectorBundleOrientationCover F E ι) where
  toFun p := ⟨g p.proj, Orientation.map ι (φ p.proj).toLinearEquiv p.orientation⟩
  continuous_toFun := continuous_of_isOpen_preimage_sheet (g.continuous.comp continuous_proj)
    (isOpen_setOf_mk_map_mem_sheet hι hφ)

/-- The map of orientation double covers induced by `φ` sends an orientation of `E'_{b'}` to its
image under `φ b'`. -/
@[simp]
theorem map_mk (b' : B') (o : Orientation ℝ (E' b') ι) :
    map hι hφ ⟨b', o⟩ = ⟨g b', Orientation.map ι (φ b').toLinearEquiv o⟩ :=
  (rfl)

/-- The map of orientation double covers induced by `φ` lies over `g`. -/
@[simp]
theorem proj_map (p : VectorBundleOrientationCover F' E' ι) : (map hι hφ p).proj = g p.proj :=
  (rfl)

/-- The map of orientation double covers induced by `φ` commutes with the deck involutions,
which reverse orientations. -/
@[simp]
theorem map_deck (p : VectorBundleOrientationCover F' E' ι) :
    map hι hφ (deck p) = deck (map hι hφ p) := by
  rw [deck_apply, deck_apply]
  exact congrArg (mk (g p.proj)) (Module.Ray.map_neg _ p.orientation)

end Map

end VectorBundleOrientationCover

namespace VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {E' : B → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  {ι : Type*} [Fintype ι] {φ : ∀ b, E' b ≃L[ℝ] E b}

/-- **Isomorphic bundles are orientable together.** If `φ b : E'_b ≃ E_b` is a fibrewise
isomorphism with continuous total-space map, then `E'` is orientable if and only if `E` is. An
orientation of `E` transports back to `E'` (`TauCeti.VectorBundleOrientation.comap`), and the
images under `φ` of an orientation of `E'` vary continuously in the orientation double cover of
`E` (`TauCeti.VectorBundleOrientationCover.map`), so they orient `E`. -/
theorem nonempty_iff_of_fiberwise (hι' : Fintype.card ι = finrank ℝ F')
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.snd)) :
    Nonempty (VectorBundleOrientation F' E' ι) ↔ Nonempty (VectorBundleOrientation F E ι) :=
  ⟨fun ⟨o'⟩ ↦ ⟨ofContinuous (fun b ↦ Orientation.map ι (φ b).toLinearEquiv (o' b))
      ((VectorBundleOrientationCover.map (g := ContinuousMap.id B) hι' hφ).continuous.comp
        (o'.continuous_mk_cover hι'))⟩,
    fun ⟨o⟩ ↦ ⟨o.comap (g := ContinuousMap.id B) hι' hφ⟩⟩

end VectorBundleOrientation

end TauCeti
