/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Small.Basic
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.Convenient.CartesianClosed

/-!
# Compact Hausdorff generators, products, and mapping spaces

Mathlib provides both compact generation (`TopologicalSpace.compactlyGenerated`,
`UCompactlyGeneratedSpace`) and generation by an arbitrary family of spaces
(`TopologicalSpace.generatedBy`, `Topology.IsGeneratedBy`). Here we identify these constructions
for the family of compact Hausdorff spaces in an explicit test universe `u` independent of the
ambient space's universe, and establish the point-set topological inputs for the coreflection and
Cartesian closed structure on `CompactlyGenerated.{u, w}`:

* `TopologicalSpace.generatedBy_compHaus` and `Topology.isGeneratedBy_compHaus_iff` identify the
  two refinements and predicates, from which
  `TopologicalSpace.compactlyGenerated_compactlyGenerated` gives idempotence of
  `compactlyGenerated.{u}`.
* Every compact subset of a `u`-small Hausdorff space is the range of a continuous map from a
  `CompHaus.{u}` space (`TauCeti.exists_compHaus_range_eq_of_isCompact`). Consequently every
  `u`-small Hausdorff compactly coherent space—in particular every `u`-small Hausdorff weakly
  locally compact space—is `u`-compactly generated
  (`TauCeti.instUCompactlyGeneratedSpaceOfCompactlyCoherentSpaceOfT2`), and for any `u`-small
  Hausdorff `u`-compactly generated space `Y` the Escardó–Lawson–Simpson mapping space
  `ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z` is homeomorphic to `C(Y, Z)` with the
  compact-open topology (`Topology.ContinuousMapGeneratedBy.homeomorphContinuousMapCompHaus`).
* Taking a product with a `u`-small locally compact Hausdorff space (in particular `unitInterval`)
  preserves `u`-compact generation (`UCompactlyGeneratedSpace.prod_right`,
  `UCompactlyGeneratedSpace.prod_left`).
* Compact generation imposes no separation axiom: Sierpiński space (`Prop`) is `u`-compactly
  generated for every universe `u` while failing `T1Space` and `T2Space`
  (`TauCeti.not_t1Space_sierpinski`, `TauCeti.not_t2Space_sierpinski`).

## References

* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Math. Z. 119
  (1971), 11–28.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
-/

public section

open Set Topology
open scoped Set.Notation

universe u v w

namespace TopologicalSpace

/-- Generation by all compact Hausdorff spaces is compact generation. -/
theorem generatedBy_compHaus (Y : Type v) [TopologicalSpace Y] :
    generatedBy (fun K : CompHaus.{u} ↦ K) (Y := Y) = compactlyGenerated.{u} Y := by
  rw [generatedBy_eq_coinduced]
  rfl

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
  @T2Space.mk Y (compactlyGenerated.{u} Y) fun _ _ hxy ↦
    let ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hxy
    ⟨u, v, compactlyGenerated_le.{u} Y u hu, compactlyGenerated_le.{u} Y v hv, hxu, hyv, huv⟩

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

end Topology

namespace TauCeti

/-- Every compact subset of a `u`-small Hausdorff space is the range of a continuous map from a
compact Hausdorff space in universe `u`. -/
theorem exists_compHaus_range_eq_of_isCompact {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [Small.{u} Y] {K : Set Y} (hK : IsCompact K) :
    ∃ (S : CompHaus.{u}) (p : C(S, Y)), range p = K := by
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  let e : ↑K ≃ₜ Shrink.{u} ↑K := Shrink.homeomorph ↑K
  have : CompactSpace (Shrink.{u} ↑K) := e.compactSpace
  have : T2Space (Shrink.{u} ↑K) := e.symm.isEmbedding.t2Space
  refine ⟨CompHaus.of (Shrink.{u} ↑K),
    ⟨Subtype.val ∘ e.symm, continuous_subtype_val.comp e.symm.continuous⟩, ?_⟩
  simp only [ContinuousMap.coe_mk, range_comp, EquivLike.range_eq_univ, image_univ,
    Subtype.range_coe]

/-- Every `u`-small Hausdorff compactly coherent space is `u`-compactly generated. In particular,
this applies to every `u`-small Hausdorff weakly locally compact space. -/
instance (priority := 100) instUCompactlyGeneratedSpaceOfCompactlyCoherentSpaceOfT2
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactlyCoherentSpace Y] [Small.{u} Y] :
    UCompactlyGeneratedSpace.{u} Y := by
  refine uCompactlyGeneratedSpace_of_isOpen fun s hs ↦
    CompactlyCoherentSpace.isOpen_iff.2 fun K hK ↦ ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  let e : ↑K ≃ₜ Shrink.{u} ↑K := Shrink.homeomorph ↑K
  have : CompactSpace (Shrink.{u} ↑K) := e.compactSpace
  have : T2Space (Shrink.{u} ↑K) := e.symm.isEmbedding.t2Space
  let f : C(CompHaus.of (Shrink.{u} ↑K), Y) :=
    ⟨Subtype.val ∘ e.symm, continuous_subtype_val.comp e.symm.continuous⟩
  have hpre : (K ↓∩ s) = e ⁻¹' (f ⁻¹' s) := by
    ext x
    simp [f]
  rw [hpre]
  exact (hs _ f).preimage e.continuous

/-- Every `u`-small Hausdorff weakly locally compact space is `u`-compactly generated. -/
theorem uCompactlyGeneratedSpace_of_weaklyLocallyCompactSpace
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [WeaklyLocallyCompactSpace Y] [Small.{u} Y] :
    UCompactlyGeneratedSpace.{u} Y :=
  inferInstance

/-- Sierpiński space (`Prop` with `{True}` open) is not `T₁`. -/
theorem not_t1Space_sierpinski : ¬ T1Space Prop := fun _ ↦
  true_ne_false (specializes_iff_nhds.2 (by simp) : Specializes True False).eq

/-- Sierpiński space (`Prop` with `{True}` open) is not Hausdorff, even though as a finite space it
is `u`-compactly generated for every universe `u`. -/
theorem not_t2Space_sierpinski : ¬ T2Space Prop := fun _ ↦
  not_t1Space_sierpinski inferInstance

/-- Sierpiński space (`Prop`) is `u`-compactly generated for every universe `u`. -/
theorem uCompactlyGeneratedSpace_sierpinski : UCompactlyGeneratedSpace.{u} Prop :=
  inferInstance

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
    [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (X × unitInterval) :=
  prod_right

instance instProdUnitIntervalLeft (X : Type v) [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{u} (unitInterval × X) :=
  prod_left

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
    obtain ⟨S, p, hp⟩ := TauCeti.exists_compHaus_range_eq_of_isCompact.{u} hK
    exact ⟨S, univ, p, isCompact_univ, by simpa only [image_univ] using hp⟩

@[simp]
theorem homeomorphContinuousMapCompHaus_apply
    {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y] [T2Space Y] [Small.{u} Y]
    (f : ContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) Y Z) :
    homeomorphContinuousMapCompHaus.{u} Y Z f = f.toContinuousMap := by
  simp [homeomorphContinuousMapCompHaus]

@[simp]
theorem homeomorphContinuousMapCompHaus_symm_apply
    {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y] [T2Space Y] [Small.{u} Y] (f : C(Y, Z)) :
    (homeomorphContinuousMapCompHaus.{u} Y Z).symm f =
      f.toContinuousMapGeneratedBy (fun K : CompHaus.{u} ↦ K) := by
  simp [homeomorphContinuousMapCompHaus]

end Topology.ContinuousMapGeneratedBy
