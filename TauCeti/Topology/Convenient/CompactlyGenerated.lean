/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Small.Basic
public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.Compactness.CompactlyGeneratedSpace
public import TauCeti.Topology.Convenient.GeneratedBy
public import TauCeti.Topology.Convenient.HomSpace

/-!
# Compact Hausdorff generators, products, and mapping spaces

Mathlib provides both compact generation (`TopologicalSpace.compactlyGenerated`,
`UCompactlyGeneratedSpace`) and generation by a family (`TopologicalSpace.generatedBy`,
`Topology.IsGeneratedBy`). Here we identify them for `CompHaus.{u}` in an explicit test universe `u`
and establish the point-set inputs for `CompactlyGenerated.{u, w}`:

* `TopologicalSpace.generatedBy_compHaus`, `Topology.isGeneratedBy_compHaus_iff`, and idempotence
  `TopologicalSpace.compactlyGenerated_compactlyGenerated`.
* Compact subsets as `CompHaus.{u}` images (`IsCompact.exists_compHaus_range_eq`), giving
  `TauCeti.instUCompactlyGeneratedSpaceOfCompactlyCoherentSpaceOfT2` and the compact-open comparison
  `Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapCompHaus`.
* Locally compact product preservation (`UCompactlyGeneratedSpace.prod_right`,
  `UCompactlyGeneratedSpace.prod_left`,
  `TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right`,
  `TauCeti.uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left`).

## References

* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
-/

public section

open Set Topology

universe u v w

namespace TopologicalSpace

/-- Generation by all compact Hausdorff spaces is compact generation. -/
theorem generatedBy_compHaus (Y : Type v) [TopologicalSpace Y] :
    generatedBy (fun K : CompHaus.{u} ↦ K) (Y := Y) = compactlyGenerated.{u} Y := by
  rw [generatedBy_eq_coinduced]
  rfl

/-- Every continuous map from a `CompHaus.{u}` test space is continuous into
`compactlyGenerated.{u} Y`. -/
theorem continuous_to_compactlyGenerated {Y : Type v} [TopologicalSpace Y] {S : CompHaus.{u}}
    (g : C(S, Y)) : Continuous[inferInstance, compactlyGenerated.{u} Y] g := by
  let p : (Σ (i : (T : CompHaus.{u}) × C(T, Y)), i.fst) → Y := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  suffices ∀ i, Continuous[inferInstance, compactlyGenerated.{u} Y] fun a : i.fst ↦ p ⟨i, a⟩ from
    this ⟨S, g⟩
  rw [← @continuous_sigma_iff]; exact continuous_coinduced_rng

/-- The compactly generated topology refines (is finer than or equal to, in Mathlib's order `≤`)
the original topology. -/
theorem compactlyGenerated_le (Y : Type v) [t : TopologicalSpace Y] :
    compactlyGenerated.{u} Y ≤ t :=
  generatedBy_compHaus.{u} Y ▸ generatedBy_le

/-- `TopologicalSpace.compactlyGenerated` is monotone in the ambient topology. -/
theorem compactlyGenerated_mono {Y : Type v} {t₁ t₂ : TopologicalSpace Y} (h : t₁ ≤ t₂) :
    @compactlyGenerated.{u} Y t₁ ≤ @compactlyGenerated.{u} Y t₂ := by
  simpa only [← @generatedBy_compHaus.{u} Y t₁, ← @generatedBy_compHaus.{u} Y t₂] using
    generatedBy_mono (X := fun K : CompHaus.{u} ↦ K) h

/-- `TopologicalSpace.compactlyGenerated` is idempotent. -/
@[simp]
theorem compactlyGenerated_compactlyGenerated (Y : Type v) [TopologicalSpace Y] :
    @compactlyGenerated.{u} Y (compactlyGenerated.{u} Y) = compactlyGenerated.{u} Y := by
  rw [← @generatedBy_compHaus.{u} Y (compactlyGenerated.{u} Y), ← generatedBy_compHaus.{u} Y,
    generatedBy_generatedBy]

/-- Any type equipped with `TopologicalSpace.compactlyGenerated.{u}` is `u`-compactly generated. -/
theorem uCompactlyGeneratedSpace_compactlyGenerated (Y : Type v) [TopologicalSpace Y] :
    @UCompactlyGeneratedSpace.{u} Y (compactlyGenerated.{u} Y) :=
  @UCompactlyGeneratedSpace.mk Y (compactlyGenerated.{u} Y)
    (compactlyGenerated_compactlyGenerated.{u} Y).symm.le

/-- Refining a Hausdorff topology by `TopologicalSpace.compactlyGenerated` preserves `T2Space`. -/
theorem t2Space_compactlyGenerated (Y : Type v) [TopologicalSpace Y] [T2Space Y] :
    @T2Space Y (compactlyGenerated.{u} Y) :=
  t2Space_antitone (compactlyGenerated_le.{u} Y) inferInstance

end TopologicalSpace

namespace Topology

/-- The two compact-generation predicates agree, with the same test-space universe. -/
theorem isGeneratedBy_compHaus_iff (Y : Type v) [TopologicalSpace Y] :
    IsGeneratedBy (fun K : CompHaus.{u} ↦ K) Y ↔ UCompactlyGeneratedSpace.{u} Y := by
  rw [IsGeneratedBy.iff_le_generatedBy, TopologicalSpace.generatedBy_compHaus]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.le_compactlyGenerated⟩

/-- Compactly generated spaces are generated by the family of compact Hausdorff spaces. -/
instance (Y : Type v) [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} Y] :
    IsGeneratedBy (fun K : CompHaus.{u} ↦ K) Y :=
  (isGeneratedBy_compHaus_iff Y).2 inferInstance

/-- The compactly generated refinement of any topological space is `u`-compactly generated. -/
instance (Y : Type v) [TopologicalSpace Y] :
    UCompactlyGeneratedSpace.{u} (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) Y) :=
  (isGeneratedBy_compHaus_iff _).1 inferInstance

end Topology

namespace IsCompact

/-- Every `u`-small compact Hausdorff subset of a topological space is the range of a continuous map
from a compact Hausdorff space in universe `u`. -/
theorem exists_compHaus_range_eq {Y : Type v} [TopologicalSpace Y]
    {K : Set Y} [T2Space K] [Small.{u} K] (hK : IsCompact K) :
    ∃ (S : CompHaus.{u}) (p : C(S, Y)), range p = K := by
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  let e : ↑K ≃ₜ Shrink.{u} ↑K := Shrink.homeomorph ↑K
  have : CompactSpace (Shrink.{u} ↑K) := e.compactSpace
  have : T2Space (Shrink.{u} ↑K) := e.symm.isEmbedding.t2Space
  refine ⟨CompHaus.of (Shrink.{u} ↑K),
    ⟨Subtype.val ∘ e.symm, continuous_subtypeVal.comp e.symm.continuous⟩, ?_⟩
  simp only [ContinuousMap.coe_mk, range_comp, EquivLike.range_eq_univ, image_univ,
    Subtype.range_coe]

end IsCompact

namespace TauCeti

/-- Every `u`-small Hausdorff compactly coherent space is `u`-compactly generated. In particular,
this applies to every `u`-small Hausdorff weakly locally compact space. -/
instance (priority := 100) instUCompactlyGeneratedSpaceOfCompactlyCoherentSpaceOfT2
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactlyCoherentSpace Y] [Small.{u} Y] :
    UCompactlyGeneratedSpace.{u} Y := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s hs ↦
    (CompactlyCoherentSpace.isClosed_iff s).2 fun K hK ↦ ?_
  obtain ⟨S, p, rfl⟩ := hK.exists_compHaus_range_eq.{u}
  have hclosed : IsClosed (s ∩ range p) := by
    rw [← Set.image_preimage_eq_inter_range]
    exact p.continuous.isClosedMap _ (hs S p)
  rw [← Subtype.preimage_coe_inter_self]
  exact hclosed.preimage continuous_subtypeVal

variable (X : Type v) (Y : Type w) [TopologicalSpace X] [TopologicalSpace Y]
  [UCompactlyGeneratedSpace.{u} X] [UCompactlyGeneratedSpace.{u} Y]

/-- If `X` and `Y` are `u`-compactly generated and `Y` is locally compact, then the ordinary
product `X × Y` is `u`-compactly generated. -/
theorem uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_right [LocallyCompactSpace Y] :
    UCompactlyGeneratedSpace.{u} (X × Y) :=
  (Topology.isGeneratedBy_compHaus_iff (X × Y)).1
    (Topology.IsGeneratedBy.prod_of_locallyCompactSpace_right X Y)

/-- If `X` and `Y` are `u`-compactly generated and `X` is locally compact, then the ordinary
product `X × Y` is `u`-compactly generated. -/
theorem uCompactlyGeneratedSpace_prod_of_locallyCompactSpace_left [LocallyCompactSpace X] :
    UCompactlyGeneratedSpace.{u} (X × Y) :=
  (Topology.isGeneratedBy_compHaus_iff (X × Y)).1
    (Topology.IsGeneratedBy.prod_of_locallyCompactSpace_left X Y)

end TauCeti

namespace UCompactlyGeneratedSpace

/-- Taking the product on the right with a `u`-small locally compact Hausdorff space preserves
`u`-compact generation. -/
theorem prod_right {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [UCompactlyGeneratedSpace.{u} X] [LocallyCompactSpace Y] [T2Space Y] [Small.{u} Y] :
    UCompactlyGeneratedSpace.{u} (X × Y) :=
  (Topology.isGeneratedBy_compHaus_iff.{u} (X × Y)).1
    (Topology.IsGeneratedBy.prod_right (G := fun K : CompHaus.{u} ↦ K))

/-- Taking the product on the left with a `u`-small locally compact Hausdorff space preserves
`u`-compact generation. -/
theorem prod_left {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space X] [Small.{u} X] [UCompactlyGeneratedSpace.{u} Y] :
    UCompactlyGeneratedSpace.{u} (X × Y) :=
  (Topology.isGeneratedBy_compHaus_iff.{u} (X × Y)).1
    (Topology.IsGeneratedBy.prod_left (G := fun K : CompHaus.{u} ↦ K))

instance instProdUnitIntervalRight (X : Type v) [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] : UCompactlyGeneratedSpace.{u} (X × unitInterval) := prod_right

instance instProdUnitIntervalLeft (X : Type v) [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] : UCompactlyGeneratedSpace.{u} (unitInterval × X) := prod_left

end UCompactlyGeneratedSpace

namespace Topology.ContinuousMapGeneratedBy

/-- When `Y` is `u`-small, Hausdorff, and `u`-compactly generated, the `CompHaus.{u}`-probed
mapping space `ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z` is homeomorphic to
`C(Y, Z)` with the compact-open topology. -/
@[expose]
noncomputable def homeomorphContinuousMapCompHaus
    (Y : Type v) (Z : Type w) [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y] [T2Space Y] [Small.{u} Y] :
    ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z ≃ₜ C(Y, Z) :=
  homeomorphContinuousMap fun _ hK ↦ by
    obtain ⟨S, p, hp⟩ := hK.exists_compHaus_range_eq.{u}
    exact ⟨S, univ, p, isCompact_univ, by simpa only [image_univ] using hp⟩

@[simp]
theorem homeomorphContinuousMapCompHaus_apply
    {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y] [T2Space Y] [Small.{u} Y]
    (f : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z) :
    homeomorphContinuousMapCompHaus.{u} Y Z f = f.toContinuousMap := (rfl)

@[simp]
theorem homeomorphContinuousMapCompHaus_symm_apply
    {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y] [T2Space Y] [Small.{u} Y] (f : C(Y, Z)) :
    (homeomorphContinuousMapCompHaus.{u} Y Z).symm f =
      f.toContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) := (rfl)

end Topology.ContinuousMapGeneratedBy
