/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

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
* `TauCeti.AlgebraicGeometry.Scheme.ext_of_isLimit`: points of the limit are determined by their
  images in the members.
* `TauCeti.AlgebraicGeometry.Scheme.preservesLimit_forgetToTop`: the underlying space of the limit
  is the limit of the underlying spaces.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace TauCeti.AlgebraicGeometry.Scheme

section Points

variable {I : Type u} [Category.{u} I] [IsCofilteredOrEmpty I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Every compatible family of points of a cofiltered diagram of schemes comes from a point of the
limit. Stacks, Lemma 32.4.2 (0CUF). -/
theorem exists_π_app_eq_of_isLimit (x : ∀ i, D.obj i)
    (hx : ∀ {i j} (f : i ⟶ j), D.map f (x i) = x j) : ∃ s : c.pt, ∀ i, c.π.app i s = x i := by
  -- The residue fields `κ(xᵢ)` form a filtered diagram of rings; the spectrum of its colimit maps
  -- compatibly to every `Dᵢ`, and each of its points maps to the family `x`.
  have map_id (i : I) (a : D.obj i) (h : D.map (𝟙 i) a = a) :
      ((D.obj i).residueFieldCongr h.symm).hom ≫ (D.map (𝟙 i)).residueFieldMap a = 𝟙 _ := by
    generalize hφ : D.map (𝟙 i) = φ at h ⊢
    obtain rfl : φ = 𝟙 _ := hφ ▸ D.map_id i
    rw [Scheme.residueFieldMap_id]
    rfl
  have map_comp {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (a : D.obj i) (b : D.obj j) (c : D.obj k)
      (hab : D.map f a = b) (hbc : D.map g b = c) (hac : D.map (f ≫ g) a = c) :
      ((D.obj k).residueFieldCongr hac.symm).hom ≫ (D.map (f ≫ g)).residueFieldMap a =
        (((D.obj k).residueFieldCongr hbc.symm).hom ≫ (D.map g).residueFieldMap b) ≫
          ((D.obj j).residueFieldCongr hab.symm).hom ≫ (D.map f).residueFieldMap a := by
    subst hab hbc
    generalize hψ : D.map (f ≫ g) = ψ at hac ⊢
    obtain rfl : ψ = D.map f ≫ D.map g := hψ ▸ D.map_comp f g
    rw [Scheme.residueFieldMap_comp]
    rfl
  let F : I ⥤ CommRingCat.{u}ᵒᵖ :=
    { obj i := op ((D.obj i).residueField (x i))
      map {i j} f :=
        (((D.obj j).residueFieldCongr (hx f).symm).hom ≫ (D.map f).residueFieldMap (x i)).op
      map_id i := Quiver.Hom.unop_inj (map_id i (x i) (hx (𝟙 i)))
      map_comp f g := Quiver.Hom.unop_inj (map_comp f g _ _ _ (hx f) (hx g) (hx (f ≫ g))) }
  let α : F ⋙ Scheme.Spec ⟶ D :=
    { app i := (D.obj i).fromSpecResidueField (x i)
      naturality {i j} f := by
        simp [F, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] }
  have (i : I) : Nonempty ((F ⋙ Scheme.Spec).obj i) := by dsimp; infer_instance
  have (i : I) : CompactSpace ((F ⋙ Scheme.Spec).obj i) := by dsimp; infer_instance
  have {i j : I} (f : i ⟶ j) : IsAffineHom ((F ⋙ Scheme.Spec).map f) := by
    dsimp; infer_instance
  obtain ⟨e⟩ := Scheme.nonempty_of_isLimit _ _ (isLimitOfPreserves Scheme.Spec (limit.isLimit F))
  refine ⟨hc.lift ((Cone.postcompose α).obj (Scheme.Spec.mapCone (limit.cone F))) e, fun i ↦ ?_⟩
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
theorem isAffine_of_isLimit (i : I) [IsAffine (D.obj i)] : IsAffine c.pt :=
  have := isAffineHom_π_app D c hc i
  isAffine_of_isAffineHom (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of schemes with affine transition maps is quasi-affine as
soon as one member is. -/
theorem isQuasiAffine_of_isLimit (i : I) [(D.obj i).IsQuasiAffine] : c.pt.IsQuasiAffine :=
  have := isAffineHom_π_app D c hc i
  .of_isAffineHom (c.π.app i)

include hc in
/-- The limit of a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps is affine if and only if some member is. Stacks, Tag 01Z6. -/
theorem isAffine_iff_exists_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] : IsAffine c.pt ↔ ∃ i, IsAffine (D.obj i) :=
  ⟨fun _ ↦ Scheme.exists_isAffine_of_isLimit D c hc,
    fun ⟨i, _⟩ ↦ isAffine_of_isLimit hc i⟩

include hc in
/-- The limit of a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition maps is quasi-affine if and only if some member is. Stacks, Tag 01Z5. -/
theorem isQuasiAffine_iff_exists_of_isLimit [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] : c.pt.IsQuasiAffine ↔ ∃ i, (D.obj i).IsQuasiAffine :=
  ⟨fun _ ↦ Scheme.exists_isQuasiAffine_of_isLimit D c hc,
    fun ⟨i, _⟩ ↦ isQuasiAffine_of_isLimit hc i⟩

include hc in
/-- A point of the limit of a cofiltered diagram of schemes with affine transition maps specializes
to every point with the same images in the members. -/
theorem specializes_of_isLimit {s t : c.pt} (h : ∀ i, c.π.app i s = c.π.app i t) : s ⤳ t := by
  rw [specializes_iff_forall_open]
  intro U hU htU
  obtain ⟨_, ⟨i, V, -, rfl⟩, htV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen D c hc)
      (U := ⟨U, hU⟩) htU
  exact hVU (show c.π.app i s ∈ V by rw [h i]; exact htV)

include hc in
/-- Points of the limit of a cofiltered diagram of schemes with affine transition maps are
determined by their images in the members. Stacks, Lemma 32.4.2 (0CUF). -/
theorem ext_of_isLimit {s t : c.pt} (h : ∀ i, c.π.app i s = c.π.app i t) : s = t :=
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
      obtain ⟨s, hs⟩ := exists_π_app_eq_of_isLimit hc x hx
      exact ⟨s, hs, fun t ht ↦ ext_of_isLimit hc fun i ↦ (ht i).trans (hs i).symm⟩
    rw [TopCat.nonempty_isLimit_iff_eq_induced _ h.some]
    exact topologicalSpace_eq_iInf_induced_of_isLimit hc

end TauCeti.AlgebraicGeometry.Scheme
