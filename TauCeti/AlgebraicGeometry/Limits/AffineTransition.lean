/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Separation, affineness and points of limits with affine transition maps

Let `D : I ⥤ Scheme` be a cofiltered diagram whose transition maps are affine, with limit cone
`c`. Mathlib shows that each projection `c.π.app i` is affine (`isAffineHom_π_app`) and that the
limit of quasi-compact schemes is quasi-compact (`Scheme.compactSpace_of_isLimit`). Since an
affine morphism is separated, separation and quasi-separation of a single member pass to the
limit (Stacks, Lemma 32.2.2 (01YX) with Morphisms, Lemma 29.11.2 (01S7)). Likewise affineness
and quasi-affineness pass from a member to the limit; combined with Mathlib's converses
(Stacks, Tags 01Z5 and 01Z6), for qcqs members the limit is affine
(quasi-affine) if and only if some member is.

The underlying topological space of such a limit is the limit of the underlying spaces (Stacks,
Lemma 32.4.2 (0CUF)). A compatible family of points `xᵢ ∈ Dᵢ` is hit by a point of the limit:
the residue fields `κ(xᵢ)` form a filtered diagram of fields, and the spectrum of its colimit maps
compatibly to every `Dᵢ`; this half needs neither affine transition maps nor quasi-compactness.
Two points with the same images agree, and the topology is the one induced by the projections,
because the preimages of affine opens of the members form a basis of the limit
(`isBasis_preimage_isAffineOpen`).

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.residueFieldDiagram`: the residue fields of a compatible
  family of points of a diagram of schemes, as a diagram in `CommRingCatᵒᵖ`.
* `TauCeti.AlgebraicGeometry.Scheme.fromSpecResidueFieldDiagram`: the morphisms `Spec κ(xᵢ) ⟶ Dᵢ`,
  as a natural transformation.
* `TauCeti.AlgebraicGeometry.Scheme.isSeparated_of_isLimit`: the limit is separated as soon as
  some member is.
* `TauCeti.AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isLimit`: the limit is
  quasi-separated as soon as some member is.
* `TauCeti.AlgebraicGeometry.Scheme.isAffine_iff_exists_of_isLimit`: for qcqs members, the
  limit is affine if and only if some member is.
* `TauCeti.AlgebraicGeometry.Scheme.isQuasiAffine_iff_exists_of_isLimit`: for qcqs members, the
  limit is quasi-affine if and only if some member is.
* `TauCeti.AlgebraicGeometry.Scheme.exists_π_app_eq_of_isLimit`: every compatible family of
  points of a cofiltered diagram of schemes comes from a point of the limit.
* `TauCeti.AlgebraicGeometry.Scheme.isLimit_ext`: points of the limit are determined by their
  images in the members.
* `TauCeti.AlgebraicGeometry.Scheme.preservesLimit_forgetToTop`: the underlying space of the limit
  is the limit of the underlying spaces.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace TauCeti.AlgebraicGeometry.Scheme

section Points

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (x : ∀ i, D.obj i)
  (hx : ∀ {i j} (f : i ⟶ j), D.map f (x i) = x j)

/-- The residue fields `κ(xᵢ)` of a compatible family of points of a diagram of schemes, as a
diagram in `CommRingCatᵒᵖ` along the residue field maps of the transition maps. -/
@[expose, simps, implicit_reducible]
noncomputable def residueFieldDiagram : I ⥤ CommRingCat.{u}ᵒᵖ where
  obj i := op ((D.obj i).residueField (x i))
  map {i j} f := (((D.obj j).residueFieldCongr (hx f)).inv ≫ (D.map f).residueFieldMap (x i)).op
  map_id i := by
    rw [Scheme.Hom.residueFieldCongr_inv_residueFieldMap_congr (D.map_id i) (hx (𝟙 i))
        ((congrArg (fun φ ↦ φ (x i)) (D.map_id i)).symm.trans (hx (𝟙 i))),
      Scheme.residueFieldCongr_inv_residueFieldMap_id]
    simp
  map_comp {i j k} f g := by
    rw [← op_comp,
      Scheme.Hom.residueFieldCongr_inv_residueFieldMap_congr (D.map_comp f g) (hx (f ≫ g))
        (by rw [Scheme.Hom.comp_apply, hx f, hx g]),
      Scheme.Hom.residueFieldCongr_inv_residueFieldMap_comp (D.map f) (D.map g) (hx f) (hx g)]

/-- The morphisms `Spec κ(xᵢ) ⟶ Dᵢ` from the spectra of the residue fields of a compatible family
of points, as a natural transformation out of the spectrum of `residueFieldDiagram`. -/
@[expose, simps]
noncomputable def fromSpecResidueFieldDiagram :
    residueFieldDiagram D x hx ⋙ Scheme.Spec ⟶ D where
  app i := (D.obj i).fromSpecResidueField (x i)
  naturality {i j} f := by
    rw [Functor.comp_map, residueFieldDiagram_map, Scheme.Spec_map, Quiver.Hom.unop_op,
      Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_inv,
      Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

variable [IsCofilteredOrEmpty I] {D} {c : Cone D} (hc : IsLimit c)

include hc hx in
/-- Every compatible family of points of a cofiltered diagram of schemes comes from a point of the
limit. Stacks, Lemma 32.4.2 (0CUF). -/
theorem exists_π_app_eq_of_isLimit : ∃ s : c.pt, ∀ i, c.π.app i s = x i := by
  -- The residue fields `κ(xᵢ)` form a filtered diagram of rings; the spectrum of its colimit maps
  -- compatibly to every `Dᵢ`, and each of its points maps to the family `x`.
  let F := residueFieldDiagram D x hx
  have (i : I) : Nonempty ((F ⋙ Scheme.Spec).obj i) := by dsimp [F]; infer_instance
  have (i : I) : CompactSpace ((F ⋙ Scheme.Spec).obj i) := by dsimp [F]; infer_instance
  have {i j : I} (f : i ⟶ j) : IsAffineHom ((F ⋙ Scheme.Spec).map f) := by
    dsimp [F]; infer_instance
  obtain ⟨e⟩ := Scheme.nonempty_of_isLimit _ _ (isLimitOfPreserves Scheme.Spec (limit.isLimit F))
  refine ⟨hc.lift ((Cone.postcompose (fromSpecResidueFieldDiagram D x hx)).obj
    (Scheme.Spec.mapCone (limit.cone F))) e, fun i ↦ ?_⟩
  rw [← Scheme.Hom.comp_apply, hc.fac]
  exact (D.obj i).fromSpecResidueField_apply (x i) _

end Points

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is separated as soon
as one member is. Stacks, Lemma 32.2.2 (01YX). -/
theorem isSeparated_of_isLimit (i : I) [(D.obj i).IsSeparated] : c.pt.IsSeparated := by
  have := isAffineHom_π_app D c hc i
  have : IsSeparated (c.π.app i) := .of_isAffineHom _
  refine ⟨?_⟩
  rw [terminal.hom_ext (terminal.from c.pt) (c.π.app i ≫ terminal.from (D.obj i))]
  infer_instance

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is quasi-separated as
soon as one member is. Stacks, Lemma 32.2.2 (01YX). -/
theorem quasiSeparatedSpace_of_isLimit (i : I) [QuasiSeparatedSpace (D.obj i)] :
    QuasiSeparatedSpace c.pt := by
  have := isAffineHom_π_app D c hc i
  have : IsSeparated (c.π.app i) := .of_isAffineHom _
  exact quasiSeparatedSpace_of_quasiSeparated (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is affine as soon as
one member is. Compare Mathlib's `AlgebraicGeometry.Scheme.isAffine_of_isLimit`, which needs every
member to be affine but no condition on the transition maps. -/
theorem isAffine_of_isLimit_of_isAffineHom (i : I) [IsAffine (D.obj i)] : IsAffine c.pt :=
  have := isAffineHom_π_app D c hc i
  isAffine_of_isAffineHom (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is quasi-affine as
soon as one member is. -/
theorem isQuasiAffine_of_isLimit_of_isAffineHom (i : I) [(D.obj i).IsQuasiAffine] :
    c.pt.IsQuasiAffine :=
  have := isAffineHom_π_app D c hc i
  .of_isAffineHom (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps is affine if and only if some member is. Stacks, Tag 01Z6. -/
theorem isAffine_iff_exists_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] : IsAffine c.pt ↔ ∃ i, IsAffine (D.obj i) :=
  ⟨fun _ ↦ Scheme.exists_isAffine_of_isLimit D c hc,
    fun ⟨i, _⟩ ↦ isAffine_of_isLimit_of_isAffineHom hc i⟩

include hc in
/-- The limit of a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps is quasi-affine if and only if some member is. Stacks, Tag 01Z5. -/
theorem isQuasiAffine_iff_exists_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] : c.pt.IsQuasiAffine ↔ ∃ i, (D.obj i).IsQuasiAffine :=
  ⟨fun _ ↦ Scheme.exists_isQuasiAffine_of_isLimit D c hc,
    fun ⟨i, _⟩ ↦ isQuasiAffine_of_isLimit_of_isAffineHom hc i⟩

include hc in
/-- A point of the limit of a cofiltered diagram of schemes with affine transition maps specializes
to every point with the same images in the members. -/
theorem specializes_of_isLimit {s t : c.pt} (h : ∀ i, c.π.app i s = c.π.app i t) : s ⤳ t := by
  rw [specializes_iff_forall_open]
  intro U hU htU
  obtain ⟨_, ⟨i, V, -, rfl⟩, htV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen D c hc)
      (U := ⟨U, hU⟩) htU
  exact hVU (Scheme.Hom.mem_preimage _ |>.mpr (h i ▸ htV))

include hc in
/-- Points of the limit of a cofiltered diagram of schemes with affine transition maps are
determined by their images in the members. Stacks, Lemma 32.4.2 (0CUF). -/
theorem isLimit_ext {s t : c.pt} (h : ∀ i, c.π.app i s = c.π.app i t) : s = t :=
  ((specializes_of_isLimit hc h).antisymm (specializes_of_isLimit hc fun i ↦ (h i).symm)).eq

include hc in
/-- The topology of the limit of a cofiltered diagram of schemes with affine transition maps is
induced by the projections to the members. -/
theorem topologicalSpace_eq_iInf_induced_of_isLimit :
    (inferInstance : TopologicalSpace c.pt) =
      ⨅ i, TopologicalSpace.induced (c.π.app i) inferInstance := by
  refine le_antisymm (le_iInf fun i ↦ (c.π.app i).continuous.le_induced) ?_
  rw [TopologicalSpace.IsTopologicalBasis.eq_generateFrom (isBasis_preimage_isAffineOpen D c hc)]
  refine le_generateFrom ?_
  rintro _ ⟨_, ⟨i, V, -, rfl⟩, rfl⟩
  exact TopologicalSpace.le_def.mp (iInf_le _ i) _ (isOpen_induced V.isOpen)

/-- The underlying topological space of the limit of a cofiltered diagram of schemes with affine
transition maps is the limit of the underlying spaces. Stacks, Lemma 32.4.2 (0CUF). -/
instance preservesLimit_forgetToTop : PreservesLimit D Scheme.forgetToTop where
  preserves {c} hc := by
    have h : Nonempty (IsLimit ((forget TopCat).mapCone (Scheme.forgetToTop.mapCone c))) := by
      rw [Types.isLimit_iff]
      intro x hx
      obtain ⟨s, hs⟩ := exists_π_app_eq_of_isLimit x hx hc
      exact ⟨s, hs, fun t ht ↦ isLimit_ext hc fun i ↦ (ht i).trans (hs i).symm⟩
    rw [TopCat.nonempty_isLimit_iff_eq_induced _ h.some]
    exact topologicalSpace_eq_iInf_induced_of_isLimit hc

end TauCeti.AlgebraicGeometry.Scheme
