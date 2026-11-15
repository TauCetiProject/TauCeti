/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import TauCeti.AlgebraicGeometry.ResidueField
public import TauCeti.CategoryTheory.Comma.Over.Pullback

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

`opensDiagramObjIso` and `opensConePtIso` identify `opensDiagram` and `opensCone` with preimage
open subschemes; `pullbackDiagram` and `pullbackDiagramCone` base-change `D` and `c` along
`p : Y ⟶ D.obj i₀` (`isLimitPullbackDiagramCone`), giving `Over.pullback` cofiltered-limit descent
in `Scheme` (Stacks, Lemma 32.10.1 (01ZM)).

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

namespace TauCeti.AlgebraicGeometry

section OpensDiagram

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I)
  (U : (D.obj i).Opens)

/-- Identification of stage `j` of `opensDiagram D i U` with `(D.map j.hom ⁻¹ᵁ U).toScheme`. -/
noncomputable def opensDiagramObjIso (j : Over i) :
    (opensDiagram D i U).obj j ≅ (D.map j.hom ⁻¹ᵁ U).toScheme := eqToIso (opensDiagram_obj D i U j)

/-- Identification of the vertex of `opensCone D c i U` with `(c.π.app i ⁻¹ᵁ U).toScheme`. -/
noncomputable def opensConePtIso : (opensCone D c i U).pt ≅ (c.π.app i ⁻¹ᵁ U).toScheme :=
  eqToIso (opensCone_pt D c i U)

/-- Composing `(opensDiagramObjIso D i U j).hom` with `(D.map j.hom ⁻¹ᵁ U).ι`. -/
@[reassoc (attr := simp)] theorem opensDiagramObjIso_hom_ι (j : Over i) :
    (opensDiagramObjIso D i U j).hom ≫ (D.map j.hom ⁻¹ᵁ U).ι = (opensDiagramι D i U).app j :=
  (Category.id_comp _).trans (opensDiagramι_app D i U j).symm

/-- Composing `(opensDiagramObjIso D i U j).inv` with `(opensDiagramι D i U).app j`. -/
@[reassoc] theorem opensDiagramObjIso_inv_app (j : Over i) :
    (opensDiagramObjIso D i U j).inv ≫ (opensDiagramι D i U).app j = (D.map j.hom ⁻¹ᵁ U).ι := by
  rw [← opensDiagramObjIso_hom_ι, Iso.inv_hom_id_assoc]

/-- Transition morphisms of `opensDiagram D i U` correspond to `Scheme.Hom.resLE` along
`D.map f.left`. -/
@[reassoc] theorem opensDiagram_map_comp_objIso_hom {j k : Over i} (f : j ⟶ k) :
    (opensDiagram D i U).map f ≫ (opensDiagramObjIso D i U k).hom =
      (opensDiagramObjIso D i U j).hom ≫ (D.map f.left).resLE (D.map k.hom ⁻¹ᵁ U)
        (D.map j.hom ⁻¹ᵁ U) (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w f]) := by
  rw [← cancel_mono (D.map k.hom ⁻¹ᵁ U).ι, Category.assoc, opensDiagramObjIso_hom_ι,
    (opensDiagramι D i U).naturality f, Functor.comp_map, Over.forget_map,
    Category.assoc, Scheme.Hom.resLE_comp_ι, opensDiagramObjIso_hom_ι_assoc]

/-- Projections of `opensCone D c i U` correspond to `Scheme.Hom.resLE` along `c.π.app j.left`. -/
@[reassoc] theorem opensCone_π_app_comp_objIso_hom (j : Over i) :
    (opensCone D c i U).π.app j ≫ (opensDiagramObjIso D i U j).hom =
      (opensConePtIso D c i U).hom ≫ (c.π.app j.left).resLE (D.map j.hom ⁻¹ᵁ U)
        (c.π.app i ⁻¹ᵁ U) (by rw [← Scheme.Hom.comp_preimage, c.w]) :=
  (Category.comp_id _).trans ((opensCone_π_app D c i U j).trans (Category.id_comp _).symm)

/-- Composing `(opensCone D c i U).π.app j` with `(opensDiagramι D i U).app j`. -/
@[reassoc] theorem opensCone_π_app_comp_opensDiagramι_app (j : Over i) :
    (opensCone D c i U).π.app j ≫ (opensDiagramι D i U).app j =
      (opensConePtIso D c i U).hom ≫ (c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app j.left := by
  rw [← opensDiagramObjIso_hom_ι, ← Category.assoc, opensCone_π_app_comp_objIso_hom,
    Category.assoc, Scheme.Hom.resLE_comp_ι]

end OpensDiagram

section PullbackDiagram

section General

variable {I C : Type*} [Category* I] [Category* C] [HasPullbacks C] (D : I ⥤ C) (c : Cone D)

/-- Base-changing `D : I ⥤ C` along `p : Y ⟶ D.obj i₀` gives an `Over i₀`-indexed diagram. -/
@[expose, simps, implicit_reducible]
noncomputable def pullbackDiagram (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) : Over i₀ ⥤ C where
  obj j := pullback p (D.map j.hom)
  map f := pullback.map p _ p _ (𝟙 _) (D.map f.left) (𝟙 _) (by simp) (by simp [← D.map_comp])
  map_id _ := by apply pullback.hom_ext <;> simp
  map_comp _ _ := by apply pullback.hom_ext <;> simp

/-- Second projection from `pullbackDiagram D i₀ p` to `Over.forget i₀ ⋙ D`. -/
@[expose, simps] noncomputable def pullbackDiagramSnd (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) :
    pullbackDiagram D i₀ p ⟶ Over.forget i₀ ⋙ D where
  app j := pullback.snd p (D.map j.hom)

/-- Structural natural transformation from `pullbackDiagram D i₀ p` to the constant diagram on
`D.obj i₀`. -/
@[expose, simps] noncomputable def pullbackDiagramToBase (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) :
    pullbackDiagram D i₀ p ⟶ (Functor.const (Over i₀)).obj (D.obj i₀) where
  app j := pullback.snd p (D.map j.hom) ≫ D.map j.hom
  naturality _ _ _ := by simp [← D.map_comp]

/-- Cone over `pullbackDiagram D i₀ p` with vertex `pullback p (c.π.app i₀)` induced by `c`. -/
@[expose, simps, implicit_reducible]
noncomputable def pullbackDiagramCone (i₀ : I) {Y : C} (p : Y ⟶ D.obj i₀) :
    Cone (pullbackDiagram D i₀ p) where
  pt := pullback p (c.π.app i₀)
  π := { app j := pullback.map p _ p _ (𝟙 _) (c.π.app j.left) (𝟙 _) (by simp) (by simp [c.w])
         naturality _ _ _ := by apply pullback.hom_ext <;> simp [c.w] }

/-- Transition morphisms of `pullbackDiagram D i₀ p` form pullback squares with `D.map f.left`. -/
theorem isPullback_pullbackDiagram_map {i₀ : I} {Y : C} (p : Y ⟶ D.obj i₀)
    {j k : Over i₀} (f : j ⟶ k) :
    IsPullback ((pullbackDiagram D i₀ p).map f) (pullback.snd p (D.map j.hom))
      (pullback.snd p (D.map k.hom)) (D.map f.left) :=
  .of_right (by simpa [← D.map_comp, Over.w f] using IsPullback.of_hasPullback p (D.map j.hom))
    (by simp) (IsPullback.of_hasPullback p (D.map k.hom))

/-- When `(Over.forget i₀).Initial` and `c` is a limit cone over `D`, `pullbackDiagramCone D c i₀ p`
exhibits `pullback p (c.π.app i₀)` as the limit of `pullbackDiagram D i₀ p`. -/
noncomputable def isLimitPullbackDiagramCone (hc : IsLimit c)
    (i₀ : I) [(Over.forget i₀).Initial] {Y : C} (p : Y ⟶ D.obj i₀) :
    IsLimit (pullbackDiagramCone D c i₀ p) :=
  letI : IsConnected (Over i₀) := isConnected_of_hasTerminal (Over i₀)
  isLimitOfIsPullbackOfIsConnected (pullbackDiagramSnd D i₀ p)
    (pullbackDiagramCone D c i₀ p) (c.whisker (Over.forget i₀))
    { hom := pullback.snd p (c.π.app i₀), w := fun _ ↦ by simp }
    (fun j ↦ .of_right (by simpa [c.w j.hom] using IsPullback.of_hasPullback p (c.π.app i₀))
      (by simp) (IsPullback.of_hasPullback p (D.map j.hom)))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) c).symm hc)

end General

section SchemeInstances

variable {I : Type*} [Category* I] (D : I ⥤ Scheme.{u}) {i₀ : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i₀)

/-- Affine transition morphisms of `D` base-change to `pullbackDiagram D i₀ p`. -/
instance isAffineHom_pullbackDiagram_map {j k : Over i₀} (f : j ⟶ k) [IsAffineHom (D.map f.left)] :
    IsAffineHom ((pullbackDiagram D i₀ p).map f) :=
  MorphismProperty.of_isPullback (isPullback_pullbackDiagram_map D p f).flip inferInstance

/-- Quasi-compactness transfers to `pullbackDiagram D i₀ p` along quasi-compact `p`. -/
instance compactSpace_pullbackDiagram_obj [QuasiCompact p] (j : Over i₀)
    [CompactSpace (D.obj j.left)] : CompactSpace ((pullbackDiagram D i₀ p).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (D.map j.hom))

/-- Quasi-separation transfers to `pullbackDiagram D i₀ p` along quasi-separated `p`. -/
instance quasiSeparatedSpace_pullbackDiagram_obj [QuasiSeparated p] (j : Over i₀)
    [QuasiSeparatedSpace (D.obj j.left)] : QuasiSeparatedSpace ((pullbackDiagram D i₀ p).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd p (D.map j.hom))

end SchemeInstances

end PullbackDiagram

namespace Scheme

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

section OverPullbackDescent

section FstProj
variable {Z S : Scheme.{u}} {g : Z ⟶ S} {Y₁ Y₂ Y₃ : Over S}
@[reassoc] private theorem overLeft_snd (β : (Over.pullback g).obj Y₁ ⟶ (Over.pullback g).obj Y₂) :
    β.left ≫ pullback.snd Y₂.hom g = pullback.snd Y₁.hom g := Over.w β
private noncomputable def overFstProj (β : (Over.pullback g).obj Y₁ ⟶ (Over.pullback g).obj Y₂) :
    pullback Y₁.hom g ⟶ Y₂.left := β.left ≫ pullback.fst Y₂.hom g
private theorem overFstProj_comp_hom (β : (Over.pullback g).obj Y₁ ⟶ (Over.pullback g).obj Y₂) :
    overFstProj β ≫ Y₂.hom = pullback.snd Y₁.hom g ≫ g := by
  rw [overFstProj, Category.assoc, pullback.condition, overLeft_snd_assoc]
private noncomputable def overMkOfFstProj (a : pullback Y₁.hom g ⟶ Y₂.left)
    (ha : a ≫ Y₂.hom = pullback.snd Y₁.hom g ≫ g) :
    (Over.pullback g).obj Y₁ ⟶ (Over.pullback g).obj Y₂ :=
  Over.homMk (pullback.lift a (pullback.snd Y₁.hom g) ha) (pullback.lift_snd _ _ _)
private theorem overFstProj_mkOfFstProj (a : pullback Y₁.hom g ⟶ Y₂.left)
    (ha : a ≫ Y₂.hom = pullback.snd Y₁.hom g ≫ g) :
    overFstProj (Y₁ := Y₁) (Y₂ := Y₂) (overMkOfFstProj a ha) = a := pullback.lift_fst _ _ _
private theorem over_hom_ext_of_fstProj
    {β₁ β₂ : (Over.pullback g).obj Y₁ ⟶ (Over.pullback g).obj Y₂}
    (h : overFstProj β₁ = overFstProj β₂) : β₁ = β₂ :=
  Over.OverMorphism.ext <| pullback.hom_ext h ((overLeft_snd β₁).trans (overLeft_snd β₂).symm)
end FstProj

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

section StageHelpers
variable {i₀ : I} {Y Y₁ Y₂ Y₃ : Over (D.obj i₀)} {k j : Over i₀}
private noncomputable def overResStageHom (u : k ⟶ j)
    (β : (Over.pullback (D.map j.hom)).obj Y₁ ⟶ (Over.pullback (D.map j.hom)).obj Y₂) :
    (Over.pullback (D.map k.hom)).obj Y₁ ⟶ (Over.pullback (D.map k.hom)).obj Y₂ :=
  overMkOfFstProj ((pullbackDiagram D i₀ Y₁.hom).map u ≫ overFstProj β) (by
    rw [Category.assoc, overFstProj_comp_hom]; simp [← D.map_comp])
private theorem overFstProj_resStageHom (u : k ⟶ j)
    (β : (Over.pullback (D.map j.hom)).obj Y₁ ⟶ (Over.pullback (D.map j.hom)).obj Y₂) :
    overFstProj (overResStageHom D u β) = (pullbackDiagram D i₀ Y₁.hom).map u ≫ overFstProj β :=
  overFstProj_mkOfFstProj _ _
private theorem overResStageHom_id (u : k ⟶ j) :
    overResStageHom D u (𝟙 ((Over.pullback (D.map j.hom)).obj Y)) =
      𝟙 ((Over.pullback (D.map k.hom)).obj Y) :=
  over_hom_ext_of_fstProj (by rw [overFstProj_resStageHom]; simp [overFstProj])
private theorem overResStageHom_comp (u : k ⟶ j)
    (β₁ : (Over.pullback (D.map j.hom)).obj Y₁ ⟶ (Over.pullback (D.map j.hom)).obj Y₂)
    (β₂ : (Over.pullback (D.map j.hom)).obj Y₂ ⟶ (Over.pullback (D.map j.hom)).obj Y₃) :
    overResStageHom D u (β₁ ≫ β₂) = overResStageHom D u β₁ ≫ overResStageHom D u β₂ := by
  apply over_hom_ext_of_fstProj
  have hcomm : (overResStageHom D u β₁).left ≫ (pullbackDiagram D i₀ Y₂.hom).map u =
      (pullbackDiagram D i₀ Y₁.hom).map u ≫ β₁.left :=
    pullback.hom_ext (by simp [overResStageHom, overMkOfFstProj, overFstProj])
      (by simp [overResStageHom, overMkOfFstProj, overLeft_snd])
  change _ = (overResStageHom D u β₁).left ≫ overFstProj (overResStageHom D u β₂)
  rw [overFstProj_resStageHom, overFstProj_resStageHom, ← Category.assoc, hcomm]; rfl
private theorem overCone_π_resStageHom (u : k ⟶ j)
    {β : (Over.pullback (D.map j.hom)).obj Y₁ ⟶ (Over.pullback (D.map j.hom)).obj Y₂}
    {α : (Over.pullback (c.π.app i₀)).obj Y₁ ⟶ (Over.pullback (c.π.app i₀)).obj Y₂}
    (hβ : (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ overFstProj β = overFstProj α) :
    (pullbackDiagramCone D c i₀ Y₁.hom).π.app k ≫ overFstProj (overResStageHom D u β) =
      overFstProj α := by
  rw [overFstProj_resStageHom, ← Category.assoc, (pullbackDiagramCone D c i₀ Y₁.hom).w, hβ]
private theorem overCone_π_fstProj_comp
    (α : (Over.pullback (c.π.app i₀)).obj Y₁ ⟶ (Over.pullback (c.π.app i₀)).obj Y₂)
    (γ : (Over.pullback (c.π.app i₀)).obj Y₂ ⟶ (Over.pullback (c.π.app i₀)).obj Y₃)
    (βα : (Over.pullback (D.map j.hom)).obj Y₁ ⟶ (Over.pullback (D.map j.hom)).obj Y₂)
    (βγ : (Over.pullback (D.map j.hom)).obj Y₂ ⟶ (Over.pullback (D.map j.hom)).obj Y₃)
    (hβα : (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ overFstProj βα = overFstProj α)
    (hβγ : (pullbackDiagramCone D c i₀ Y₂.hom).π.app j ≫ overFstProj βγ = overFstProj γ) :
    (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ overFstProj (βα ≫ βγ) = overFstProj (α ≫ γ) := by
  have hcomm : (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ βα.left =
      α.left ≫ (pullbackDiagramCone D c i₀ Y₂.hom).π.app j :=
    pullback.hom_ext (by simpa [overFstProj] using hβα) (by simp [overLeft_snd, overLeft_snd_assoc])
  rw [overFstProj, Over.comp_left, Category.assoc, reassoc_of% hcomm]
  simpa [overFstProj] using α.left ≫= hβγ
private theorem overLift_eq_of_cone_π_fstProj
    (β : (Over.pullback (D.map j.hom)).obj Y₁ ⟶ (Over.pullback (D.map j.hom)).obj Y₂)
    (α : (Over.pullback (c.π.app i₀)).obj Y₁ ⟶ (Over.pullback (c.π.app i₀)).obj Y₂)
    (hβ : (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ overFstProj β = overFstProj α) :
    (Over.pullbackCompIsoOfEq (c.π.app j.left) (D.map j.hom) (c.π.app i₀) (c.w j.hom)).inv.app Y₁ ≫
      (Over.pullback (c.π.app j.left)).map β ≫
      (Over.pullbackCompIsoOfEq (c.π.app j.left) (D.map j.hom) (c.π.app i₀)
        (c.w j.hom)).hom.app Y₂ = α := by
  apply over_hom_ext_of_fstProj
  have hB : ((Over.pullback (c.π.app j.left)).map β).left ≫
      pullback.fst (pullback.snd Y₂.hom (D.map j.hom)) (c.π.app j.left) =
      pullback.fst (pullback.snd Y₁.hom (D.map j.hom)) (c.π.app j.left) ≫ β.left := by simp
  simp only [overFstProj, Over.comp_left] at hβ ⊢
  rw [Category.assoc, Category.assoc, Over.pullbackCompIsoOfEq_hom_app_left_fst,
    reassoc_of% hB, Over.pullbackCompIsoOfEq_inv_app_left_fst_assoc]; simpa using hβ
private theorem exists_overStageHom_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (hc : IsLimit c)
    [QuasiCompact Y₁.hom] [QuasiSeparated Y₁.hom] [LocallyOfFinitePresentation Y₂.hom]
    (α : (Over.pullback (c.π.app i₀)).obj Y₁ ⟶ (Over.pullback (c.π.app i₀)).obj Y₂) :
    ∃ (j : Over i₀) (β : (Over.pullback (D.map j.hom)).obj Y₁ ⟶
      (Over.pullback (D.map j.hom)).obj Y₂),
      (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ overFstProj β = overFstProj α := by
  obtain ⟨j, g, hg₁, hg₂⟩ :=
    AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (pullbackDiagram D i₀ Y₁.hom) (pullbackDiagramToBase D i₀ Y₁.hom) Y₂.hom
      (pullbackDiagramCone D c i₀ Y₁.hom) (isLimitPullbackDiagramCone D c hc i₀ Y₁.hom)
      (overFstProj α) (by ext j; simp [overFstProj_comp_hom, c.w j.hom])
  exact ⟨j, overMkOfFstProj g (hg₂.trans (pullbackDiagramToBase_app D i₀ Y₁.hom j)),
    by rw [overFstProj_mkOfFstProj, hg₁]⟩
private theorem exists_overResStageHom_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    (hc : IsLimit c) [QuasiCompact Y₁.hom] [LocallyOfFiniteType Y₂.hom] (j : Over i₀)
    (β₁ β₂ : (Over.pullback (D.map j.hom)).obj Y₁ ⟶ (Over.pullback (D.map j.hom)).obj Y₂)
    (hπ : (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ overFstProj β₁ =
      (pullbackDiagramCone D c i₀ Y₁.hom).π.app j ≫ overFstProj β₂) :
    ∃ (k : Over i₀) (u : k ⟶ j), overResStageHom D u β₁ = overResStageHom D u β₂ := by
  obtain ⟨k, u, hu⟩ := AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (pullbackDiagram D i₀ Y₁.hom) (pullbackDiagramToBase D i₀ Y₁.hom) Y₂.hom
    (pullbackDiagramCone D c i₀ Y₁.hom) (isLimitPullbackDiagramCone D c hc i₀ Y₁.hom)
    (overFstProj β₁) (overFstProj β₂) (overFstProj_comp_hom β₁).symm
    (overFstProj_comp_hom β₂).symm hπ
  exact ⟨k, u, over_hom_ext_of_fstProj
    (by rw [overFstProj_resStageHom, overFstProj_resStageHom, hu])⟩
end StageHelpers

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, any morphism over `c.pt` from the pullback of a qcqs scheme `Y₁` over `D.obj i₀` to the
pullback of a locally finitely presented scheme `Y₂` over `D.obj i₀` descends to a morphism over
some stage `j` mapping to `i₀`. -/
@[stacks 01ZM "morphism descent along cofiltered affine-transition limits"]
theorem exists_hom_pullback_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : IsLimit c) {i₀ : I} (Y₁ Y₂ : Over (D.obj i₀))
    [QuasiCompact Y₁.hom] [QuasiSeparated Y₁.hom] [LocallyOfFinitePresentation Y₂.hom]
    (α : (Over.pullback (c.π.app i₀)).obj Y₁ ⟶ (Over.pullback (c.π.app i₀)).obj Y₂) :
    ∃ (j : I) (fj : j ⟶ i₀)
      (β : (Over.pullback (D.map fj)).obj Y₁ ⟶ (Over.pullback (D.map fj)).obj Y₂),
      (Over.pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).inv.app Y₁ ≫
        (Over.pullback (c.π.app j)).map β ≫
        (Over.pullbackCompIsoOfEq (c.π.app j) (D.map fj) (c.π.app i₀) (c.w fj)).hom.app Y₂ = α :=
  let ⟨j, β, hβ⟩ := exists_overStageHom_of_isLimit D c hc α
  ⟨j.left, j.hom, β, overLift_eq_of_cone_π_fstProj D c β α hβ⟩

/-- Along a cofiltered limit of quasi-compact schemes with affine transition morphisms, two
morphisms over `D.obj i₀` from a quasi-compact scheme `Y₁` to a locally finite-type scheme `Y₂`
whose pullbacks to `c.pt` agree already agree after pullback to some stage `k` mapping to `i₀`. -/
@[stacks 01ZM "morphism uniqueness along cofiltered affine-transition limits"]
theorem exists_pullback_map_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    (hc : IsLimit c) {i₀ : I} {Y₁ Y₂ : Over (D.obj i₀)}
    [QuasiCompact Y₁.hom] [LocallyOfFiniteType Y₂.hom] (β₁ β₂ : Y₁ ⟶ Y₂)
    (h : (Over.pullback (c.π.app i₀)).map β₁ = (Over.pullback (c.π.app i₀)).map β₂) :
    ∃ (k : I) (fk : k ⟶ i₀),
      (Over.pullback (D.map fk)).map β₁ = (Over.pullback (D.map fk)).map β₂ := by
  let j₀ : Over i₀ := Over.mk (𝟙 i₀)
  have hfst (β : Y₁ ⟶ Y₂) : (pullbackDiagramCone D c i₀ Y₁.hom).π.app j₀ ≫
      overFstProj ((Over.pullback (D.map j₀.hom)).map β) =
      overFstProj ((Over.pullback (c.π.app i₀)).map β) := by dsimp [j₀, overFstProj]; simp
  obtain ⟨k, u, hu⟩ := exists_overResStageHom_eq_of_isLimit D c hc j₀ _ _
    ((hfst β₁).trans ((congrArg overFstProj h).trans (hfst β₂).symm))
  have hres (β : Y₁ ⟶ Y₂) : overResStageHom D u ((Over.pullback (D.map j₀.hom)).map β) =
      (Over.pullback (D.map k.hom)).map β :=
    over_hom_ext_of_fstProj (by rw [overFstProj_resStageHom]; dsimp [j₀, overFstProj]; simp)
  exact ⟨k.left, k.hom, (hres β₁).symm.trans (hu.trans (hres β₂))⟩

/-- Along a cofiltered limit of quasi-compact quasi-separated schemes with affine transition
morphisms, an isomorphism over `c.pt` between the pullbacks of two qcqs locally finitely presented
schemes `Y₁, Y₂` over `D.obj i₀` descends to an isomorphism over some stage `k` mapping to `i₀`
whose pullback to `c.pt` recovers `e.hom`. -/
@[stacks 01ZM "isomorphism descent along cofiltered affine-transition limits"]
theorem exists_iso_pullback_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : IsLimit c) {i₀ : I} (Y₁ Y₂ : Over (D.obj i₀))
    [QuasiCompact Y₁.hom] [QuasiSeparated Y₁.hom] [LocallyOfFinitePresentation Y₁.hom]
    [QuasiCompact Y₂.hom] [QuasiSeparated Y₂.hom] [LocallyOfFinitePresentation Y₂.hom]
    (e : (Over.pullback (c.π.app i₀)).obj Y₁ ≅ (Over.pullback (c.π.app i₀)).obj Y₂) :
    ∃ (k : I) (fk : k ⟶ i₀)
      (ek : (Over.pullback (D.map fk)).obj Y₁ ≅ (Over.pullback (D.map fk)).obj Y₂),
      (Over.pullbackCompIsoOfEq (c.π.app k) (D.map fk) (c.π.app i₀) (c.w fk)).inv.app Y₁ ≫
        (Over.pullback (c.π.app k)).map ek.hom ≫
        (Over.pullbackCompIsoOfEq (c.π.app k) (D.map fk) (c.π.app i₀) (c.w fk)).hom.app Y₂ =
      e.hom := by
  have step {Z₁ Z₂ : Over (D.obj i₀)} [QuasiCompact Z₁.hom] [LocallyOfFiniteType Z₁.hom]
      {j : Over i₀} {φ : (Over.pullback (D.map j.hom)).obj Z₁ ⟶
        (Over.pullback (D.map j.hom)).obj Z₂} {ψ : (Over.pullback (D.map j.hom)).obj Z₂ ⟶
        (Over.pullback (D.map j.hom)).obj Z₁} {α : (Over.pullback (c.π.app i₀)).obj Z₁ ⟶
        (Over.pullback (c.π.app i₀)).obj Z₂} {γ : (Over.pullback (c.π.app i₀)).obj Z₂ ⟶
        (Over.pullback (c.π.app i₀)).obj Z₁}
      (hφ : (pullbackDiagramCone D c i₀ Z₁.hom).π.app j ≫ overFstProj φ = overFstProj α)
      (hψ : (pullbackDiagramCone D c i₀ Z₂.hom).π.app j ≫ overFstProj ψ = overFstProj γ)
      (hαγ : α ≫ γ = 𝟙 _) :
      ∃ (k : Over i₀) (u : k ⟶ j), overResStageHom D u φ ≫ overResStageHom D u ψ = 𝟙 _ := by
    obtain ⟨k, u, hu⟩ := exists_overResStageHom_eq_of_isLimit D c hc j (φ ≫ ψ) (𝟙 _) (by
      rw [overCone_π_fstProj_comp D c α γ φ ψ hφ hψ, hαγ]; simp [overFstProj])
    exact ⟨k, u, by rw [← overResStageHom_comp, hu, overResStageHom_id]⟩
  obtain ⟨j₁, φ₁, hφ₁⟩ := exists_overStageHom_of_isLimit D c hc e.hom
  obtain ⟨j₂, ψ₂, hψ₂⟩ := exists_overStageHom_of_isLimit D c hc e.inv
  have hφ₃ := overCone_π_resStageHom D c (IsCofiltered.minToLeft j₁ j₂) hφ₁
  have hψ₃ := overCone_π_resStageHom D c (IsCofiltered.minToRight j₁ j₂) hψ₂
  obtain ⟨j₄, u₃, hu₃⟩ := step hφ₃ hψ₃ e.hom_inv_id
  have hφ₄ := overCone_π_resStageHom D c u₃ hφ₃
  obtain ⟨j₅, u₄, hu₄⟩ := step (overCone_π_resStageHom D c u₃ hψ₃) hφ₄ e.inv_hom_id
  exact ⟨j₅.left, j₅.hom,
    { hom := overResStageHom D u₄ (overResStageHom D u₃ _)
      inv := overResStageHom D u₄ (overResStageHom D u₃ _)
      hom_inv_id := by rw [← overResStageHom_comp, hu₃, overResStageHom_id]
      inv_hom_id := hu₄ },
    overLift_eq_of_cone_π_fstProj D c _ e.hom (overCone_π_resStageHom D c u₄ hφ₄)⟩

end OverPullbackDescent

end Scheme

end TauCeti.AlgebraicGeometry
