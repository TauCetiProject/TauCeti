/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.DiscBundle
public import TauCeti.Topology.CWComplex.Classical.Pushout
public import TauCeti.Topology.CWComplex.Classical.ULift
public import TauCeti.Topology.FiberBundle.Separation
public import TauCeti.Topology.Homotopy.HomotopyEquiv
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.ULift
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.CWComplex.Classical.Basic

/-!
# Universe-polymorphic disc-bundle attachments

Let `E → B` be a real vector bundle of rank `r` over a Hausdorff space `B : Type u`, with
finite-dimensional model fibre `F` and fibre inner products whose norm is continuous on the total
space (`TauCeti.ContinuousFiberNorm`). Given an arbitrary topological space `Z : Type v` (in a
universe independent of `u`) and a continuous attaching map `g : S(E) → Z` from the unit sphere
bundle of `E`, or more generally `g : S(E) ∪ D(E)|_A → Z` over a classical relative CW pair
`(B, A)`, this file constructs the universe-polymorphic adjunction space `Z ∪_g D(E)` in
`TopCat.{max u v}` and equips it with its classical relative CW structure over the image of `Z`.

For same-universe pushouts (`Z : Type u`), `TauCeti.discBundleAttachmentCellEquiv` in
`TauCeti.Topology.CWComplex.Classical.ThomSpace` applies directly to any `IsPushout` square.
For `Z : Type v` in an independent universe `v`, this file lifts `TauCeti.relCWComplexDiscBundleRel`
and `TauCeti.relCWComplexDiscBundleSphereBundle` via `Topology.RelCWComplex.ulift` to
`Type (max u v)` and passes through `TauCeti.relCWAdjunctionSpace` and
`TauCeti.relativeCWPushout`:

* `TauCeti.discBundleRelAttachmentSpace` and `TauCeti.discBundleRelAttachmentCWModel`: the general
  relative attachment `Z ∪_g D(E)` along `g : S(E) ∪ D(E)|_A → Z` over a relative CW pair
  `(B, A)`, together with its universe-polymorphic pushout universal property
  (`TauCeti.discBundleRelAttachmentDesc`, `TauCeti.discBundleRelAttachmentSpace_continuousMap_ext`,
  `TauCeti.isClosed_iff_discBundleRelAttachmentSpace`), closed base embedding
  (`TauCeti.isClosedEmbedding_discBundleRelAttachmentInr`), Hausdorffness over Hausdorff `Z`,
  cell correspondence (`TauCeti.discBundleRelAttachmentCWModelCellEquiv`), characteristic-map and
  cell-set formulas, finiteness preservation, and universe-polymorphic homotopy invariance in `Z`
  (`TauCeti.exists_homotopyEquiv_discBundleRelAttachmentSpace`);
* `TauCeti.discBundleAttachmentSpace` and `TauCeti.discBundleAttachmentCWModel`: the specialization
  to a Hausdorff CW complex `B` and an attaching map `g : S(E) → Z`, with its pushout universal
  property (`TauCeti.discBundleAttachmentDesc`,
  `TauCeti.discBundleAttachmentSpace_continuousMap_ext`,
  `TauCeti.isClosed_iff_discBundleAttachmentSpace`), cell equivalence
  (`TauCeti.discBundleAttachmentCWModelCellEquiv`), characteristic-map and cell-set formulas,
  finiteness preservation, and universe-polymorphic homotopy invariance in `Z`
  (`TauCeti.exists_homotopyEquiv_discBundleAttachmentSpace`).

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18 (the cell structure of the Thom space of a bundle over a
  CW complex).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0 and
  §4.D (disc bundles, cell attachments, and Thom spaces).
* R. Brown, *Topology and Groupoids*, 2006, Section 7.5 (gluing theorem for homotopy equivalences).
-/

public section

noncomputable section

open Bundle CategoryTheory ContinuousMap Limits Metric Set Topology Topology.RelCWComplex

universe u v w

namespace TauCeti

/-! ### Private universe-polymorphic relative-CW adjunction engine -/

section ULiftAdjunction

/-- Convert a homeomorphism to a bundled continuous map without requiring a coercion instance. -/
private abbrev homC {α : Type u} {β : Type v} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) : C(α, β) :=
  ⟨e, e.continuous⟩

/-- Canonical homeomorphism between a subset `S : Set X` and its universe-lifted preimage
`ULift.down ⁻¹' S` in `ULift.{v, u} X`. -/
private def uliftSubsetHomeo {X : Type u} [TopologicalSpace X] (S : Set X) :
    ↥S ≃ₜ ↥(ULift.down ⁻¹' S : Set (ULift.{v, u} X)) where
  toFun x := ⟨ULift.up x.val, x.property⟩
  invFun y := ⟨y.val.down, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_uliftUp.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun := (continuous_uliftDown.comp continuous_subtypeVal).subtype_mk _

/-- Transport `a : C(D, Z)` to the universe-lifted pair `(ULift.down ⁻¹' D, ULift.{u, v} Z)`. -/
private def liftedBaseMap {X : Type u} [TopologicalSpace X] {D : Set X}
    {Z : Type v} [TopologicalSpace Z] (a : C(D, Z)) :
    C(↥(ULift.down ⁻¹' D : Set (ULift.{v, u} X)), ULift.{u, v} Z) :=
  (homC Homeomorph.ulift.{u, v}.symm).comp
    (a.comp (homC (uliftSubsetHomeo.{u, v} D).symm))

variable {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]
  {Z : Type v} [TopologicalSpace Z] (a : C(D, Z))

private abbrev uliftAdjunctionSpace : TopCat.{max u v} :=
  letI := RelCWComplex.ulift.{v, u} C
  relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) (liftedBaseMap a)

private def uliftAdjunctionInr : C(Z, uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  (pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a))).hom.comp (homC Homeomorph.ulift.{u, v}.symm)

private def uliftAdjunctionInl : C(C, uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  (pushout.inl (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a))).hom.comp (homC (uliftSubsetHomeo.{u, v} C))

private lemma uliftAdjunctionInl_apply (x : C) :
    uliftAdjunctionInl C a x =
      letI := RelCWComplex.ulift.{v, u} C
      pushout.inl (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
        (TopCat.ofHom (liftedBaseMap a)) (uliftSubsetHomeo.{u, v} C x) :=
  rfl

private theorem uliftAdjunctionInl_eq_inr (d : D) :
    uliftAdjunctionInl C a ⟨d.val, base_subset_complex d.property⟩ =
      uliftAdjunctionInr C a (a d) :=
  letI := RelCWComplex.ulift.{v, u} C
  ConcreteCategory.congr_hom (pushout.condition
    (f := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (g := TopCat.ofHom (liftedBaseMap a))) (uliftSubsetHomeo.{u, v} D d)

private def uliftDescLeft {W : Type w} [TopologicalSpace W] (f : C(C, W)) :
    TopCat.uliftFunctor.{w, max u v}.obj
        (TopCat.of ↥(ULift.down ⁻¹' C : Set (ULift.{v, u} X))) ⟶
      TopCat.of (ULift.{max u v, w} W) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{max u v, w}.symm).comp
    (f.comp ((homC (uliftSubsetHomeo.{u, v} C).symm).comp
      (homC (TopCat.uliftFunctorObjHomeo.{w} _).symm)))

private def uliftDescRight {W : Type w} [TopologicalSpace W] (h : C(Z, W)) :
    TopCat.uliftFunctor.{w, max u v}.obj (TopCat.of (ULift.{u, v} Z)) ⟶
      TopCat.of (ULift.{max u v, w} W) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{max u v, w}.symm).comp
    (h.comp ((homC Homeomorph.ulift.{u, v}).comp (homC (TopCat.uliftFunctorObjHomeo.{w} _).symm)))

private lemma uliftDesc_compat {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) :
    letI := RelCWComplex.ulift.{v, u} C
    TopCat.uliftFunctor.{w, max u v}.map
        (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) ≫
        uliftDescLeft.{u, v, w} C f =
      TopCat.uliftFunctor.{w, max u v}.map (TopCat.ofHom (liftedBaseMap a)) ≫
        uliftDescRight.{u, v, w} h := by
  let _ := RelCWComplex.ulift.{v, u} C
  ext x
  let y := (TopCat.uliftFunctorObjHomeo.{w} _).symm x
  have h1 := TopCat.uliftFunctorObjHomeo_symm_naturality_apply.{w}
    (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) x
  have h2 := TopCat.uliftFunctorObjHomeo_symm_naturality_apply.{w}
    (TopCat.ofHom (liftedBaseMap a)) x
  have hL :
      (TopCat.uliftFunctor.{w, max u v}.map (relCWBaseInclusion _) ≫
          uliftDescLeft.{u, v, w} C f) x =
        ULift.up (f ⟨y.val.down, base_subset_complex y.property⟩) := by
    rw [ConcreteCategory.comp_apply]
    exact congrArg (fun p : ↥(ULift.down ⁻¹' C : Set (ULift.{v, u} X)) ↦
      ULift.up (f ((uliftSubsetHomeo.{u, v} C).symm p))) h1
  have hR :
      (TopCat.uliftFunctor.{w, max u v}.map (TopCat.ofHom (liftedBaseMap a)) ≫
          uliftDescRight.{u, v, w} h) x = ULift.up (h (a ⟨y.val.down, y.property⟩)) := by
    rw [ConcreteCategory.comp_apply]
    exact congrArg (fun z : ULift.{u, v} Z ↦ ULift.up (h z.down)) h2
  exact congrArg ULift.down
    (hL.trans <| (congrArg ULift.up (hfa ⟨y.val.down, y.property⟩)).trans hR.symm)

private def uliftAdjunctionDesc {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) :
    C(uliftAdjunctionSpace C a, W) :=
  letI := RelCWComplex.ulift.{v, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
  let sq := IsPushout.of_hasPushout ι (TopCat.ofHom (liftedBaseMap a))
  let dW := (sq.map TopCat.uliftFunctor.{w, max u v}).desc
    (uliftDescLeft.{u, v, w} C f) (uliftDescRight.{u, v, w} h)
    (uliftDesc_compat.{u, v, w} C a f h hfa)
  let eP := TopCat.uliftFunctorObjHomeo.{w} (pushout ι (TopCat.ofHom (liftedBaseMap a)))
  (homC Homeomorph.ulift.{max u v, w}).comp (dW.hom.comp (homC eP))

/-- Shared evaluation helper for `uliftAdjunctionDesc_inl` and `uliftAdjunctionDesc_inr`. -/
private lemma uliftDescAux_apply {W : Type w} [TopologicalSpace W]
    {P A : TopCat.{u}} (k : A ⟶ P)
    (dW : TopCat.uliftFunctor.{w, u}.obj P ⟶ TopCat.of (ULift.{u, w} W))
    (l : TopCat.uliftFunctor.{w, u}.obj A ⟶ TopCat.of (ULift.{u, w} W))
    (hkl : TopCat.uliftFunctor.{w, u}.map k ≫ dW = l) (y : A) :
    (dW (TopCat.uliftFunctorObjHomeo.{w} P (k y))).down =
      (l (TopCat.uliftFunctorObjHomeo.{w} A y)).down := by
  have hcomp := ConcreteCategory.congr_hom hkl (TopCat.uliftFunctorObjHomeo.{w} A y)
  rw [ConcreteCategory.comp_apply, TopCat.uliftFunctorObjHomeo_naturality_apply.{w} k y] at hcomp
  exact congrArg ULift.down hcomp

private lemma uliftAdjunctionDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) (x : C) :
    uliftAdjunctionDesc C a f h hfa (uliftAdjunctionInl C a x) = f x := by
  let _ := RelCWComplex.ulift.{v, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
  let sq := IsPushout.of_hasPushout ι (TopCat.ofHom (liftedBaseMap a))
  have hval := uliftDescAux_apply (pushout.inl ι (TopCat.ofHom (liftedBaseMap a))) _
    (uliftDescLeft.{u, v, w} C f)
    ((sq.map TopCat.uliftFunctor.{w, max u v}).inl_desc (uliftDescLeft.{u, v, w} C f)
      (uliftDescRight.{u, v, w} h) (uliftDesc_compat.{u, v, w} C a f h hfa))
    (uliftSubsetHomeo.{u, v} C x)
  refine hval.trans (congrArg f ?_)
  change (uliftSubsetHomeo.{u, v} C).symm
    ((TopCat.uliftFunctorObjHomeo.{w}
        (TopCat.of ↥(ULift.down ⁻¹' C : Set (ULift.{v, u} X)))).symm
      (TopCat.uliftFunctorObjHomeo.{w} (TopCat.of ↥(ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
        (uliftSubsetHomeo.{u, v} C x))) = x
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

private lemma uliftAdjunctionDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(C, W)) (h : C(Z, W))
    (hfa : ∀ d : D, f ⟨d.val, base_subset_complex d.property⟩ = h (a d)) (z : Z) :
    uliftAdjunctionDesc C a f h hfa (uliftAdjunctionInr C a z) = h z := by
  let _ := RelCWComplex.ulift.{v, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
  let sq := IsPushout.of_hasPushout ι (TopCat.ofHom (liftedBaseMap a))
  have hval := uliftDescAux_apply (pushout.inr ι (TopCat.ofHom (liftedBaseMap a))) _
    (uliftDescRight.{u, v, w} h)
    ((sq.map TopCat.uliftFunctor.{w, max u v}).inr_desc (uliftDescLeft.{u, v, w} C f)
      (uliftDescRight.{u, v, w} h) (uliftDesc_compat.{u, v, w} C a f h hfa))
    (ULift.up z)
  refine hval.trans (congrArg (fun y ↦ h (Homeomorph.ulift.{u, v} y)) ?_)
  change (TopCat.uliftFunctorObjHomeo.{w} (TopCat.of (ULift.{u, v} Z))).symm
    (TopCat.uliftFunctorObjHomeo.{w} (TopCat.of (ULift.{u, v} Z))
      (ULift.up.{u, v} z)) = ULift.up.{u, v} z
  exact Homeomorph.symm_apply_apply _ _

private theorem exists_uliftAdjunctionInl_or_inr (p : uliftAdjunctionSpace C a) :
    (∃ x : C, uliftAdjunctionInl C a x = p) ∨ ∃ z : Z, uliftAdjunctionInr C a z = p := by
  let _ := RelCWComplex.ulift.{v, u} C
  rcases Types.eq_or_eq_of_isPushout ((forget TopCat).map_isPushout (IsPushout.of_hasPushout
    (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a)))) p with ⟨⟨⟨x⟩, hx⟩, rfl⟩ | ⟨⟨z⟩, rfl⟩
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inr ⟨z, rfl⟩

private theorem uliftAdjunctionSpace_induction_on
    {P : uliftAdjunctionSpace C a → Prop} (p : uliftAdjunctionSpace C a)
    (hl : ∀ x : C, P (uliftAdjunctionInl C a x))
    (hr : ∀ z : Z, P (uliftAdjunctionInr C a z)) : P p := by
  rcases exists_uliftAdjunctionInl_or_inr C a p with ⟨x, rfl⟩ | ⟨z, rfl⟩
  · exact hl x
  · exact hr z

private theorem isClosed_iff_uliftAdjunctionSpace (s : Set (uliftAdjunctionSpace C a)) :
    IsClosed s ↔
      IsClosed (uliftAdjunctionInl C a ⁻¹' s) ∧ IsClosed (uliftAdjunctionInr C a ⁻¹' s) := by
  let _ := RelCWComplex.ulift.{v, u} C
  let sq := IsPushout.of_hasPushout
    (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (TopCat.ofHom (liftedBaseMap a))
  rw [TauCeti.TopCat.isClosed_iff_of_isPushout sq s,
    ← (uliftSubsetHomeo.{u, v} C).isClosed_preimage,
    ← (Homeomorph.ulift.{u, v} (X := Z)).symm.isClosed_preimage,
    preimage_preimage, preimage_preimage]
  rfl

private theorem isClosedEmbedding_uliftAdjunctionInr [T2Space X] :
    IsClosedEmbedding (uliftAdjunctionInr C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  (isClosedEmbedding_pushout_inr_relCWBaseInclusion
    (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X))) (liftedBaseMap a)).comp
    (Homeomorph.ulift.{u, v} (X := Z)).symm.isClosedEmbedding

private instance t2Space_uliftAdjunctionSpace [T2Space X] [T2Space Z] :
    T2Space (uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{v, u} C
  t2Space_relCWAdjunctionSpace (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (liftedBaseMap a)

private lemma range_uliftAdjunctionInr :
    letI := RelCWComplex.ulift.{v, u} C
    range (pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
        (TopCat.ofHom (liftedBaseMap a))) = range (uliftAdjunctionInr C a) := by
  ext p
  simp only [mem_range, uliftAdjunctionInr, ContinuousMap.comp_apply]
  exact ⟨fun ⟨⟨z⟩, hz⟩ ↦ ⟨z, hz⟩, fun ⟨z, hz⟩ ↦ ⟨⟨z⟩, hz⟩⟩

@[instance_reducible]
private def uliftAdjunctionCWModel [T2Space X] :
    RelCWComplex (univ : Set (uliftAdjunctionSpace C a)) (range (uliftAdjunctionInr C a)) :=
  letI := RelCWComplex.ulift.{v, u} C
  (relativeCWPushout (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) (liftedBaseMap a)).copy univ
    (range (uliftAdjunctionInr C a)) rfl (range_uliftAdjunctionInr C a)

private def uliftAdjunctionCellEquiv [T2Space X] (n : ℕ) :
    @RelCWComplex.cell _ _ _ _ (uliftAdjunctionCWModel C a) n ≃ cell C n :=
  letI := RelCWComplex.ulift.{v, u} C
  (((relativeCWPushout (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
    (liftedBaseMap a)).copyCellEquiv univ (range (uliftAdjunctionInr C a)) rfl
      (range_uliftAdjunctionInr C a) n).trans
    (relativeCWPushoutCellEquiv (ULift.down ⁻¹' C : Set (ULift.{v, u} X))
      (liftedBaseMap a) n)).trans (RelCWComplex.uliftCellEquiv.{v, u} C n)

private theorem uliftAdjunctionCWModel_map_apply [T2Space X] (n : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (uliftAdjunctionCWModel C a) n)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    @RelCWComplex.map _ _ _ _ (uliftAdjunctionCWModel C a) n i x =
      uliftAdjunctionInl C a ⟨map n (uliftAdjunctionCellEquiv C a n i) x,
        closedCell_subset_complex n _ (mem_image_of_mem _ hx)⟩ := by
  let _ := RelCWComplex.ulift.{v, u} C
  let P := relativeCWPushout (ULift.down ⁻¹' C : Set (ULift.{v, u} X)) (liftedBaseMap a)
  have hcopy := P.map_copy univ (range (uliftAdjunctionInr C a)) rfl
    (range_uliftAdjunctionInr C a) n i
  refine (congrArg (fun f : PartialEquiv _ _ ↦ f x) hcopy).trans ?_
  refine (relativeCWPushout_map_apply (C := (ULift.down ⁻¹' C : Set (ULift.{v, u} X)))
    (a := liftedBaseMap a) n _ ⟨x, hx⟩).trans ?_
  rw [uliftAdjunctionInl_apply]
  congr 1
  exact Subtype.ext (congrFun (RelCWComplex.coe_map_ulift.{v, u} C n _) x)

private theorem image_map_uliftAdjunctionCWModel [T2Space X] (n : ℕ)
    (i : @RelCWComplex.cell _ _ _ _ (uliftAdjunctionCWModel C a) n)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    @RelCWComplex.map _ _ _ _ (uliftAdjunctionCWModel C a) n i '' S =
      uliftAdjunctionInl C a ''
        (Subtype.val ⁻¹' (map n (uliftAdjunctionCellEquiv C a n i) '' S)) := by
  ext p
  simp only [mem_image, mem_preimage]
  refine ⟨fun ⟨x, hx, hp⟩ ↦ ?_, fun ⟨y, ⟨x, hx, hxy⟩, hp⟩ ↦ ?_⟩
  · exact ⟨⟨_, closedCell_subset_complex n _ (mem_image_of_mem _ (hS hx))⟩,
      ⟨x, hx, rfl⟩, hp ▸ (uliftAdjunctionCWModel_map_apply C a n i (hS hx)).symm⟩
  · refine ⟨x, hx, ?_⟩
    rw [← hp, uliftAdjunctionCWModel_map_apply C a n i (hS hx)]
    exact congrArg (uliftAdjunctionInl C a) (Subtype.ext hxy)

private theorem finiteDimensional_uliftAdjunctionCWModel [T2Space X]
    [RelCWComplex.FiniteDimensional C] :
    @RelCWComplex.FiniteDimensional _ _ _ _ (uliftAdjunctionCWModel C a) := by
  refine @RelCWComplex.FiniteDimensional.mk _ _ _ _ (uliftAdjunctionCWModel C a) ?_
  filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n _
  exact (uliftAdjunctionCellEquiv C a n).isEmpty_congr.2 inferInstance

private theorem finiteType_uliftAdjunctionCWModel [T2Space X] [RelCWComplex.FiniteType C] :
    @RelCWComplex.FiniteType _ _ _ _ (uliftAdjunctionCWModel C a) :=
  @RelCWComplex.FiniteType.mk _ _ _ _ (uliftAdjunctionCWModel C a) fun n ↦
    have := FiniteType.finite_cell (C := C) (D := D) n
    (uliftAdjunctionCellEquiv C a n).finite_iff.2 inferInstance

private theorem finite_uliftAdjunctionCWModel [T2Space X] [RelCWComplex.Finite C] :
    @RelCWComplex.Finite _ _ _ _ (uliftAdjunctionCWModel C a) :=
  @RelCWComplex.Finite.mk _ _ _ _ (uliftAdjunctionCWModel C a)
    (finiteDimensional_uliftAdjunctionCWModel C a) (finiteType_uliftAdjunctionCWModel C a)

private def uliftChangeUnivInvL :
    TopCat.of ↥(ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) ⟶
      TopCat.of (ULift.{w, max u v} (uliftAdjunctionSpace C a)) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{w, max u v}.symm).comp
    ((uliftAdjunctionInl C a).comp (homC (uliftSubsetHomeo.{u, max v w} C).symm))

private def uliftChangeUnivInvR :
    TopCat.of (ULift.{max u w, v} Z) ⟶
      TopCat.of (ULift.{w, max u v} (uliftAdjunctionSpace C a)) :=
  TopCat.ofHom <| (homC Homeomorph.ulift.{w, max u v}.symm).comp
    ((uliftAdjunctionInr C a).comp (homC Homeomorph.ulift.{max u w, v}))

private lemma uliftChangeUnivInv_compat
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) :
    letI := RelCWComplex.ulift.{max v w, u} C
    relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) ≫
        uliftChangeUnivInvL.{u, v, w} C a =
      TopCat.ofHom b ≫ uliftChangeUnivInvR.{u, v, w} C a := by
  ext x
  simp only [ConcreteCategory.comp_apply, TopCat.hom_ofHom, ContinuousMap.coe_comp,
    uliftChangeUnivInvL, uliftChangeUnivInvR, ContinuousMap.coe_mk, hb]
  exact uliftAdjunctionInl_eq_inr C a ((uliftSubsetHomeo.{u, max v w} D).symm x)

private def uliftAdjunctionChangeUnivInv
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) :
    letI := RelCWComplex.ulift.{max v w, u} C
    C(relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b,
      uliftAdjunctionSpace C a) :=
  letI := RelCWComplex.ulift.{max v w, u} C
  (homC Homeomorph.ulift.{w, max u v}).comp
    (pushout.desc (uliftChangeUnivInvL.{u, v, w} C a) (uliftChangeUnivInvR.{u, v, w} C a)
      (uliftChangeUnivInv_compat.{u, v, w} C a b hb)).hom

private lemma uliftAdjunctionChangeUnivInv_inl
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) (x : C) :
    letI := RelCWComplex.ulift.{max v w, u} C
    uliftAdjunctionChangeUnivInv.{u, v, w} C a b hb
      (pushout.inl (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
        (TopCat.ofHom b) (uliftSubsetHomeo.{u, max v w} C x)) = uliftAdjunctionInl C a x := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  have h := congrArg ULift.down <| ConcreteCategory.congr_hom
    (pushout.inl_desc (uliftChangeUnivInvL.{u, v, w} C a) (uliftChangeUnivInvR.{u, v, w} C a)
      (uliftChangeUnivInv_compat.{u, v, w} C a b hb))
    (uliftSubsetHomeo.{u, max v w} C x)
  exact h.trans (congrArg (uliftAdjunctionInl C a) (Homeomorph.symm_apply_apply _ x))

private lemma uliftAdjunctionChangeUnivInv_inr
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) (z : Z) :
    letI := RelCWComplex.ulift.{max v w, u} C
    uliftAdjunctionChangeUnivInv.{u, v, w} C a b hb
      (pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
        (TopCat.ofHom b) (ULift.up z)) = uliftAdjunctionInr C a z := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  exact congrArg ULift.down <| ConcreteCategory.congr_hom
    (pushout.inr_desc (uliftChangeUnivInvL.{u, v, w} C a) (uliftChangeUnivInvR.{u, v, w} C a)
      (uliftChangeUnivInv_compat.{u, v, w} C a b hb)) (ULift.up z)

private lemma exists_homeomorph_uliftAdjunctionSpace_ulift
    (b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z))
    (hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x))) :
    letI := RelCWComplex.ulift.{max v w, u} C
    ∃ Φ : uliftAdjunctionSpace.{u, v} C a ≃ₜ
        relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b,
      (∀ z, Φ (uliftAdjunctionInr C a z) =
        pushout.inr (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
          (TopCat.ofHom b) (ULift.up z)) ∧
      ∀ z, Φ.symm (pushout.inr
          (relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)))
          (TopCat.ofHom b) (ULift.up z)) = uliftAdjunctionInr C a z := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  let ι := relCWBaseInclusion (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X))
  -- Stage 1: build the forward map from `uliftAdjunctionSpace` into the larger-universe pushout.
  let inlBig : C(C, relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b) :=
    (pushout.inl ι (TopCat.ofHom b)).hom.comp (homC (uliftSubsetHomeo.{u, max v w} C))
  let inrBig : C(Z, relCWAdjunctionSpace (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b) :=
    (pushout.inr ι (TopCat.ofHom b)).hom.comp (homC Homeomorph.ulift.{max u w, v}.symm)
  have hcompat :
      ∀ d : D, inlBig ⟨d.val, base_subset_complex d.property⟩ = inrBig (a d) := fun d ↦ by
    have hc := ConcreteCategory.congr_hom (pushout.condition (f := ι) (g := TopCat.ofHom b))
      (uliftSubsetHomeo.{u, max v w} D d)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hc
    exact hc.trans
      (congrArg (pushout.inr ι (TopCat.ofHom b)) (hb (uliftSubsetHomeo.{u, max v w} D d)))
  let toF := uliftAdjunctionDesc C a inlBig inrBig hcompat
  -- Stage 2: use the extracted inverse map `uliftAdjunctionChangeUnivInv` and verify inverses.
  let invF := uliftAdjunctionChangeUnivInv.{u, v, w} C a b hb
  refine ⟨{
    toFun := toF, invFun := invF
    left_inv := fun p ↦ uliftAdjunctionSpace_induction_on (P := fun q ↦ invF (toF q) = q) C a p
      (fun x ↦ (congrArg invF (uliftAdjunctionDesc_inl C a inlBig inrBig hcompat x)).trans
        (uliftAdjunctionChangeUnivInv_inl C a b hb x))
      (fun z ↦ (congrArg invF (uliftAdjunctionDesc_inr C a inlBig inrBig hcompat z)).trans
        (uliftAdjunctionChangeUnivInv_inr C a b hb z))
    right_inv := fun q ↦ by
      rcases Types.eq_or_eq_of_isPushout
        ((forget TopCat).map_isPushout (IsPushout.of_hasPushout ι (TopCat.ofHom b))) q with
        ⟨⟨⟨x⟩, hx⟩, rfl⟩ | ⟨⟨z⟩, rfl⟩
      · exact (congrArg toF (uliftAdjunctionChangeUnivInv_inl C a b hb ⟨x, hx⟩)).trans
          (uliftAdjunctionDesc_inl C a inlBig inrBig hcompat ⟨x, hx⟩)
      · exact (congrArg toF (uliftAdjunctionChangeUnivInv_inr C a b hb z)).trans
          (uliftAdjunctionDesc_inr C a inlBig inrBig hcompat z)
    continuous_toFun := toF.continuous, continuous_invFun := invF.continuous },
    fun z ↦ uliftAdjunctionDesc_inr C a inlBig inrBig hcompat z,
    uliftAdjunctionChangeUnivInv_inr C a b hb⟩

private theorem exists_homotopyEquiv_uliftAdjunctionSpace [T2Space X]
    {Z' : Type w} [TopologicalSpace Z'] (e : Z ≃ₕ Z') :
    ∃ H : uliftAdjunctionSpace.{u, v} C a ≃ₕ
        uliftAdjunctionSpace.{u, w} C (e.toFun.comp a),
      (∀ z, H (uliftAdjunctionInr C a z) = uliftAdjunctionInr C (e.toFun.comp a) (e z)) ∧
      ∀ z', H.symm (uliftAdjunctionInr C (e.toFun.comp a) z') =
        uliftAdjunctionInr C a (e.symm z') := by
  let _ := RelCWComplex.ulift.{max v w, u} C
  let b : C(↥(ULift.down ⁻¹' D : Set (ULift.{max v w, u} X)), ULift.{max u w, v} Z) :=
    (homC Homeomorph.ulift.{max u w, v}.symm).comp
      (a.comp (homC (uliftSubsetHomeo.{u, max v w} D).symm))
  have hb : ∀ x, b x = ULift.up (a ((uliftSubsetHomeo.{u, max v w} D).symm x)) := fun _ ↦ rfl
  have heb : ∀ x, ((e.uliftCongr.{max u w, max u v}).toFun.comp b) x =
      ULift.up ((e.toFun.comp a) ((uliftSubsetHomeo.{u, max v w} D).symm x)) :=
    fun x ↦ e.uliftCongr_apply.{max u w, max u v} _
  obtain ⟨Hw, hHw, hHwsymm⟩ :=
    (e.uliftCongr.{max u w, max u v}).exists_homotopyEquiv_relCWAdjunctionSpace
      (ULift.down ⁻¹' C : Set (ULift.{max v w, u} X)) b
  obtain ⟨Φ₁, hΦ₁, hΦ₁s⟩ :=
    exists_homeomorph_uliftAdjunctionSpace_ulift.{u, v, w} C a b hb
  obtain ⟨Φ₂, hΦ₂, hΦ₂s⟩ := exists_homeomorph_uliftAdjunctionSpace_ulift.{u, w, v} C
    (e.toFun.comp a) ((e.uliftCongr.{max u w, max u v}).toFun.comp b) heb
  refine ⟨(Φ₁.toHomotopyEquiv.trans Hw).trans Φ₂.symm.toHomotopyEquiv,
    fun z ↦ ?_, fun z' ↦ ?_⟩
  · simp only [ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
      hΦ₁, hHw, ContinuousMap.HomotopyEquiv.uliftCongr_apply, hΦ₂s]
  · simp only [ContinuousMap.HomotopyEquiv.trans_symm_apply, ← Homeomorph.symm_toHomotopyEquiv,
      Homeomorph.symm_symm, Homeomorph.coe_toHomotopyEquiv,
      hΦ₂, hHwsymm, ContinuousMap.HomotopyEquiv.uliftCongr_symm_apply, hΦ₁s]

end ULiftAdjunction

/-! ### Relative disc-bundle attachment along `S(E) ∪ D(E)|_A` -/

section RelAttachment

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] (A : Set B) [RelCWComplex (univ : Set B) A]
  {Z : Type v} [TopologicalSpace Z]
  (g : C(↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A), Z))

/-- **Relative disc-bundle attachment space `Z ∪_g D(E)`.** The adjunction space obtained by
attaching the unit disc bundle `D(E)` to `Z` along a continuous map `g : S(E) ∪ D(E)|_A → Z`
over a relative CW pair `(B, A)`, constructed in the common universe `max u v`. -/
def discBundleRelAttachmentSpace : TopCat.{max u v} :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionSpace (discBundle F E) g

/-- The canonical inclusion `Z → Z ∪_g D(E)` into the relative disc-bundle attachment. -/
def discBundleRelAttachmentInr : C(Z, discBundleRelAttachmentSpace F E A g) :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionInr (discBundle F E) g

/-- The canonical characteristic-side map `D(E) → Z ∪_g D(E)` into the relative disc-bundle
attachment. -/
def discBundleRelAttachmentInl : C(discBundle F E, discBundleRelAttachmentSpace F E A g) :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionInl (discBundle F E) g

/-- On the relative base `S(E) ∪ D(E)|_A`, `discBundleRelAttachmentInl` agrees with
`discBundleRelAttachmentInr ∘ g`. -/
theorem discBundleRelAttachmentInl_eq_inr
    (b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A)) :
    discBundleRelAttachmentInl F E A g
        ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
      discBundleRelAttachmentInr F E A g (g b) :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionInl_eq_inr (discBundle F E) g b

/-- **Pushout eliminator for `discBundleRelAttachmentSpace`.** Compatible continuous maps out of
`D(E)` and `Z` into a space `W` in an arbitrary universe descend uniquely to a continuous map
`Z ∪_g D(E) → W`. -/
def discBundleRelAttachmentDesc {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b)) :
    C(discBundleRelAttachmentSpace F E A g, W) :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionDesc (discBundle F E) g f h hfg

@[simp]
theorem discBundleRelAttachmentDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b))
    (v : discBundle F E) :
    discBundleRelAttachmentDesc F E A g f h hfg (discBundleRelAttachmentInl F E A g v) = f v :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionDesc_inl (discBundle F E) g f h hfg v

@[simp]
theorem discBundleRelAttachmentDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b))
    (z : Z) :
    discBundleRelAttachmentDesc F E A g f h hfg (discBundleRelAttachmentInr F E A g z) = h z :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionDesc_inr (discBundle F E) g f h hfg z

@[simp]
theorem discBundleRelAttachmentDesc_comp_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b)) :
    (discBundleRelAttachmentDesc F E A g f h hfg).comp (discBundleRelAttachmentInl F E A g) = f :=
  ContinuousMap.ext (discBundleRelAttachmentDesc_inl F E A g f h hfg)

@[simp]
theorem discBundleRelAttachmentDesc_comp_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ b : ↥(sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A),
      f ⟨b.val, b.property.elim (fun h ↦ mem_discBundle.2 (mem_sphereBundle.1 h).le) And.left⟩ =
        h (g b)) :
    (discBundleRelAttachmentDesc F E A g f h hfg).comp (discBundleRelAttachmentInr F E A g) = h :=
  ContinuousMap.ext (discBundleRelAttachmentDesc_inr F E A g f h hfg)

/-- Every point of `Z ∪_g D(E)` lies in the image of `D(E)` or in the image of `Z`. -/
theorem exists_discBundleRelAttachmentInl_or_inr (p : discBundleRelAttachmentSpace F E A g) :
    (∃ v : discBundle F E, discBundleRelAttachmentInl F E A g v = p) ∨
      ∃ z : Z, discBundleRelAttachmentInr F E A g z = p :=
  let _ := relCWComplexDiscBundleRel F E A
  exists_uliftAdjunctionInl_or_inr (discBundle F E) g p

/-- Induction principle on points of `Z ∪_g D(E)` by splitting into the images of `D(E)` and
`Z`. -/
@[elab_as_elim]
theorem discBundleRelAttachmentSpace_induction_on
    {P : discBundleRelAttachmentSpace F E A g → Prop}
    (p : discBundleRelAttachmentSpace F E A g)
    (hl : ∀ v, P (discBundleRelAttachmentInl F E A g v))
    (hr : ∀ z, P (discBundleRelAttachmentInr F E A g z)) : P p :=
  let _ := relCWComplexDiscBundleRel F E A
  uliftAdjunctionSpace_induction_on (discBundle F E) g p hl hr

/-- The ranges of `discBundleRelAttachmentInl` and `discBundleRelAttachmentInr` cover
`Z ∪_g D(E)`. -/
theorem range_discBundleRelAttachmentInl_union_range_inr :
    range (discBundleRelAttachmentInl F E A g) ∪ range (discBundleRelAttachmentInr F E A g) =
      univ :=
  eq_univ_of_forall fun p ↦ exists_discBundleRelAttachmentInl_or_inr F E A g p

/-- Two continuous maps out of `Z ∪_g D(E)` agree as soon as they agree on the images of `D(E)`
and `Z`. -/
theorem discBundleRelAttachmentSpace_continuousMap_ext {W : Type w} [TopologicalSpace W]
    {f₁ f₂ : C(discBundleRelAttachmentSpace F E A g, W)}
    (hl : ∀ v, f₁ (discBundleRelAttachmentInl F E A g v) =
      f₂ (discBundleRelAttachmentInl F E A g v))
    (hr : ∀ z, f₁ (discBundleRelAttachmentInr F E A g z) =
      f₂ (discBundleRelAttachmentInr F E A g z)) : f₁ = f₂ :=
  ContinuousMap.ext fun p ↦ discBundleRelAttachmentSpace_induction_on F E A g p hl hr

/-- A subset of `Z ∪_g D(E)` is closed if and only if its preimages in `D(E)` and in `Z` are both
closed. -/
theorem isClosed_iff_discBundleRelAttachmentSpace
    (s : Set (discBundleRelAttachmentSpace F E A g)) :
    IsClosed s ↔
      IsClosed (discBundleRelAttachmentInl F E A g ⁻¹' s) ∧
        IsClosed (discBundleRelAttachmentInr F E A g ⁻¹' s) :=
  let _ := relCWComplexDiscBundleRel F E A
  isClosed_iff_uliftAdjunctionSpace (discBundle F E) g s

/-- The canonical map `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_discBundleRelAttachmentInr :
    IsClosedEmbedding (discBundleRelAttachmentInr F E A g) :=
  let _ := relCWComplexDiscBundleRel F E A
  isClosedEmbedding_uliftAdjunctionInr (discBundle F E) g

/-- When `Z` is Hausdorff, the relative disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_discBundleRelAttachmentSpace [T2Space Z] :
    T2Space (discBundleRelAttachmentSpace F E A g) :=
  letI := relCWComplexDiscBundleRel F E A
  t2Space_uliftAdjunctionSpace (discBundle F E) g

/-- **Classical relative CW model of a relative disc-bundle attachment.** Attaching `D(E)` to `Z`
along `g : S(E) ∪ D(E)|_A → Z` equips `Z ∪_g D(E)` with a classical relative CW structure relative
to the image of `Z`, with one `(m + r)`-cell for each relative `m`-cell of `(B, A)`. -/
@[instance_reducible]
def discBundleRelAttachmentCWModel :
    RelCWComplex (univ : Set (discBundleRelAttachmentSpace F E A g))
      (range (discBundleRelAttachmentInr F E A g)) :=
  letI := relCWComplexDiscBundleRel F E A
  uliftAdjunctionCWModel (discBundle F E) g

/-- The `n`-cells of `Z ∪_g D(E)` correspond bijectively to the relative `m`-cells of `(B, A)`
with `m + r = n`, where `r` is the rank of the bundle. -/
def discBundleRelAttachmentCWModelCellEquiv (n : ℕ) :
    letI := discBundleRelAttachmentCWModel F E A g
    cell (univ : Set (discBundleRelAttachmentSpace F E A g)) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleRel F E A
  (uliftAdjunctionCellEquiv (discBundle F E) g n).trans (relCWComplexDiscBundleRelCellEquiv F E A n)

/-- Below the fibre rank `r`, `discBundleRelAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_discBundleRelAttachmentCWModel_of_lt {n : ℕ} (hn : n < Module.finrank ℝ F) :
    letI := discBundleRelAttachmentCWModel F E A g
    IsEmpty (cell (univ : Set (discBundleRelAttachmentSpace F E A g)) n) :=
  let := discBundleRelAttachmentCWModel F E A g
  letI := relCWComplexDiscBundleRel F E A
  have := isEmpty_cell_relCWComplexDiscBundleRel_of_lt (F := F) (E := E) (A := A) hn
  (uliftAdjunctionCellEquiv (discBundle F E) g n).isEmpty_congr.2 inferInstance

/-- Each characteristic map of `discBundleRelAttachmentCWModel` is the corresponding characteristic
map of `TauCeti.relCWComplexDiscBundleRel` in `D(E)` followed by `discBundleRelAttachmentInl`. -/
theorem discBundleRelAttachmentCWModel_map_apply {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := discBundleRelAttachmentCWModel F E A g
    letI := relCWComplexDiscBundleRel F E A
    map n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) x =
      discBundleRelAttachmentInl F E A g
        ⟨map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) x,
          closedCell_subset_complex n _ (mem_image_of_mem _ hx)⟩ := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  refine (uliftAdjunctionCWModel_map_apply (discBundle F E) g n _ hx).trans ?_
  rw [show uliftAdjunctionCellEquiv (discBundle F E) g n
        ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      (relCWComplexDiscBundleRelCellEquiv F E A n).symm c from
    (uliftAdjunctionCellEquiv (discBundle F E) g n).apply_symm_apply _]
  rfl

private theorem image_map_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    letI := discBundleRelAttachmentCWModel F E A g
    letI := relCWComplexDiscBundleRel F E A
    map n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) '' S =
      discBundleRelAttachmentInl F E A g ''
        (Subtype.val ⁻¹' (map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) '' S)) := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  refine (image_map_uliftAdjunctionCWModel (discBundle F E) g n _ S hS).trans ?_
  rw [show uliftAdjunctionCellEquiv (discBundle F E) g n
        ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      (relCWComplexDiscBundleRelCellEquiv F E A n).symm c from
    (uliftAdjunctionCellEquiv (discBundle F E) g n).apply_symm_apply _]
  rfl

/-- The open cell of `discBundleRelAttachmentCWModel` over a relative `m`-cell `j` of `(B, A)` is
the image under `discBundleRelAttachmentInl` of the vectors of norm less than one in `D(E)` over
`openCell m j`. -/
@[simp]
theorem openCell_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleRelAttachmentCWModel F E A g
    openCell n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      discBundleRelAttachmentInl F E A g '' {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell c.1.val c.2 ∧ ‖(v : TotalSpace F E).snd‖ < 1} := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  rw [openCell,
    image_map_discBundleRelAttachmentCWModel F E A g c (ball 0 1) ball_subset_closedBall,
    ← openCell, openCell_relCWComplexDiscBundleRel]
  congr 1; ext v; simp [and_comm]

/-- The closed cell of `discBundleRelAttachmentCWModel` over a relative `m`-cell `j` of `(B, A)`
is the image under `discBundleRelAttachmentInl` of `D(E)` over `closedCell m j`. -/
@[simp]
theorem closedCell_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleRelAttachmentCWModel F E A g
    closedCell n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      discBundleRelAttachmentInl F E A g '' (discBundleProj F E ⁻¹' closedCell c.1.val c.2) := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  rw [closedCell,
    image_map_discBundleRelAttachmentCWModel F E A g c (closedBall 0 1) Subset.rfl,
    ← closedCell, closedCell_relCWComplexDiscBundleRel]
  congr 1; ext v; simp

/-- The boundary of the cell of `discBundleRelAttachmentCWModel` over a relative `m`-cell `j` of
`(B, A)` is the image under `discBundleRelAttachmentInl` of `S(E)` over `closedCell m j` together
with `D(E)` over `cellFrontier m j`. -/
@[simp]
theorem cellFrontier_discBundleRelAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleRelAttachmentCWModel F E A g
    cellFrontier n ((discBundleRelAttachmentCWModelCellEquiv F E A g n).symm c) =
      discBundleRelAttachmentInl F E A g ''
        (Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell c.1.val c.2 ∪
          discBundleProj F E ⁻¹' cellFrontier c.1.val c.2) := by
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  rw [cellFrontier,
    image_map_discBundleRelAttachmentCWModel F E A g c (sphere 0 1) sphere_subset_closedBall,
    ← cellFrontier, cellFrontier_relCWComplexDiscBundleRel]
  congr 1; ext v; simp

/-- `discBundleRelAttachmentCWModel` is finite-dimensional when `(B, A)` is finite-dimensional. -/
theorem finiteDimensional_discBundleRelAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := discBundleRelAttachmentCWModel F E A g
    RelCWComplex.FiniteDimensional (univ : Set (discBundleRelAttachmentSpace F E A g)) :=
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  have := finiteDimensional_relCWComplexDiscBundleRel F E A
  finiteDimensional_uliftAdjunctionCWModel (discBundle F E) g

/-- `discBundleRelAttachmentCWModel` has finite type when `(B, A)` has finite type. -/
theorem finiteType_discBundleRelAttachmentCWModel [RelCWComplex.FiniteType (univ : Set B)] :
    letI := discBundleRelAttachmentCWModel F E A g
    RelCWComplex.FiniteType (univ : Set (discBundleRelAttachmentSpace F E A g)) :=
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  have := finiteType_relCWComplexDiscBundleRel F E A
  finiteType_uliftAdjunctionCWModel (discBundle F E) g

/-- `discBundleRelAttachmentCWModel` is finite when `(B, A)` is finite. -/
theorem finite_discBundleRelAttachmentCWModel [RelCWComplex.Finite (univ : Set B)] :
    letI := discBundleRelAttachmentCWModel F E A g
    RelCWComplex.Finite (univ : Set (discBundleRelAttachmentSpace F E A g)) :=
  let _ := discBundleRelAttachmentCWModel F E A g
  let _ := relCWComplexDiscBundleRel F E A
  have := finite_relCWComplexDiscBundleRel F E A
  finite_uliftAdjunctionCWModel (discBundle F E) g

/-- **Base homotopy invariance of relative disc-bundle attachments.** A homotopy equivalence
`e : Z ≃ₕ Z'` (with `Z` and `Z'` in independent universes) induces a homotopy equivalence
`Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` compatible with the inclusions of `Z` and `Z'`. -/
theorem exists_homotopyEquiv_discBundleRelAttachmentSpace {Z' : Type w} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : discBundleRelAttachmentSpace.{u, v} F E A g ≃ₕ
        discBundleRelAttachmentSpace.{u, w} F E A (e.toFun.comp g),
      (∀ z, H (discBundleRelAttachmentInr F E A g z) =
        discBundleRelAttachmentInr F E A (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (discBundleRelAttachmentInr F E A (e.toFun.comp g) z') =
        discBundleRelAttachmentInr F E A g (e.symm z') :=
  let _ := relCWComplexDiscBundleRel F E A
  exists_homotopyEquiv_uliftAdjunctionSpace (discBundle F E) g e

end RelAttachment

/-! ### Disc-bundle attachment `Z ∪_g D(E)` along `g : S(E) → Z` -/

section SphereAttachment

variable {B : Type u} [TopologicalSpace B] [T2Space B] [Topology.CWComplex (univ : Set B)]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type u) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {Z : Type v} [TopologicalSpace Z] (g : C(sphereBundle F E, Z))

/-- **Disc-bundle attachment space `Z ∪_g D(E)`.** The adjunction space obtained by attaching the
unit disc bundle `D(E)` to `Z` along `g : S(E) → Z`, constructed in `TopCat.{max u v}` for `B`
and `Z` in independent universes. -/
def discBundleAttachmentSpace : TopCat.{max u v} :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionSpace (discBundle F E) g

/-- The canonical closed embedding `Z → Z ∪_g D(E)`. -/
def discBundleAttachmentInr : C(Z, discBundleAttachmentSpace F E g) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionInr (discBundle F E) g

/-- The canonical characteristic-side map `D(E) → Z ∪_g D(E)`. -/
def discBundleAttachmentInl : C(discBundle F E, discBundleAttachmentSpace F E g) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionInl (discBundle F E) g

/-- On the unit sphere bundle `S(E)`, `discBundleAttachmentInl` glues each vector `s` to `g s` in
`Z`. -/
theorem discBundleAttachmentInl_sphere (s : sphereBundle F E) :
    discBundleAttachmentInl F E g ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ =
      discBundleAttachmentInr F E g (g s) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionInl_eq_inr (discBundle F E) g s

/-- **Pushout eliminator for `discBundleAttachmentSpace`.** Continuous maps `f : D(E) → W` and
`h : Z → W` into a space `W` in an arbitrary universe that agree along `g : S(E) → Z` descend
uniquely to a continuous map `Z ∪_g D(E) → W`. -/
def discBundleAttachmentDesc {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    C(discBundleAttachmentSpace F E g, W) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionDesc (discBundle F E) g f h hfg

@[simp]
theorem discBundleAttachmentDesc_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s))
    (v : discBundle F E) :
    discBundleAttachmentDesc F E g f h hfg (discBundleAttachmentInl F E g v) = f v :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionDesc_inl (discBundle F E) g f h hfg v

@[simp]
theorem discBundleAttachmentDesc_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s))
    (z : Z) :
    discBundleAttachmentDesc F E g f h hfg (discBundleAttachmentInr F E g z) = h z :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionDesc_inr (discBundle F E) g f h hfg z

@[simp]
theorem discBundleAttachmentDesc_comp_inl {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    (discBundleAttachmentDesc F E g f h hfg).comp (discBundleAttachmentInl F E g) = f :=
  ContinuousMap.ext (discBundleAttachmentDesc_inl F E g f h hfg)

@[simp]
theorem discBundleAttachmentDesc_comp_inr {W : Type w} [TopologicalSpace W]
    (f : C(discBundle F E, W)) (h : C(Z, W))
    (hfg : ∀ s : sphereBundle F E,
      f ⟨s.val, mem_discBundle.2 (mem_sphereBundle.1 s.property).le⟩ = h (g s)) :
    (discBundleAttachmentDesc F E g f h hfg).comp (discBundleAttachmentInr F E g) = h :=
  ContinuousMap.ext (discBundleAttachmentDesc_inr F E g f h hfg)

/-- Every point of `Z ∪_g D(E)` lies in the image of `D(E)` or in the image of `Z`. -/
theorem exists_discBundleAttachmentInl_or_inr (p : discBundleAttachmentSpace F E g) :
    (∃ v : discBundle F E, discBundleAttachmentInl F E g v = p) ∨
      ∃ z : Z, discBundleAttachmentInr F E g z = p :=
  let _ := relCWComplexDiscBundleSphereBundle F E
  exists_uliftAdjunctionInl_or_inr (discBundle F E) g p

/-- Induction principle on points of `Z ∪_g D(E)` by splitting into the images of `D(E)` and
`Z`. -/
@[elab_as_elim]
theorem discBundleAttachmentSpace_induction_on
    {P : discBundleAttachmentSpace F E g → Prop} (p : discBundleAttachmentSpace F E g)
    (hl : ∀ v, P (discBundleAttachmentInl F E g v))
    (hr : ∀ z, P (discBundleAttachmentInr F E g z)) : P p :=
  let _ := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionSpace_induction_on (discBundle F E) g p hl hr

/-- The ranges of `discBundleAttachmentInl` and `discBundleAttachmentInr` cover `Z ∪_g D(E)`. -/
theorem range_discBundleAttachmentInl_union_range_inr :
    range (discBundleAttachmentInl F E g) ∪ range (discBundleAttachmentInr F E g) = univ :=
  eq_univ_of_forall fun p ↦ exists_discBundleAttachmentInl_or_inr F E g p

/-- Two continuous maps out of `Z ∪_g D(E)` agree as soon as they agree on the images of `D(E)`
and `Z`. -/
theorem discBundleAttachmentSpace_continuousMap_ext {W : Type w} [TopologicalSpace W]
    {f₁ f₂ : C(discBundleAttachmentSpace F E g, W)}
    (hl : ∀ v, f₁ (discBundleAttachmentInl F E g v) = f₂ (discBundleAttachmentInl F E g v))
    (hr : ∀ z, f₁ (discBundleAttachmentInr F E g z) = f₂ (discBundleAttachmentInr F E g z)) :
    f₁ = f₂ :=
  ContinuousMap.ext fun p ↦ discBundleAttachmentSpace_induction_on F E g p hl hr

/-- A subset of `Z ∪_g D(E)` is closed if and only if its preimages in `D(E)` and in `Z` are both
closed. -/
theorem isClosed_iff_discBundleAttachmentSpace (s : Set (discBundleAttachmentSpace F E g)) :
    IsClosed s ↔
      IsClosed (discBundleAttachmentInl F E g ⁻¹' s) ∧
        IsClosed (discBundleAttachmentInr F E g ⁻¹' s) :=
  let _ := relCWComplexDiscBundleSphereBundle F E
  isClosed_iff_uliftAdjunctionSpace (discBundle F E) g s

/-- The inclusion `Z → Z ∪_g D(E)` is a closed embedding. -/
theorem isClosedEmbedding_discBundleAttachmentInr :
    IsClosedEmbedding (discBundleAttachmentInr F E g) :=
  let _ := relCWComplexDiscBundleSphereBundle F E
  isClosedEmbedding_uliftAdjunctionInr (discBundle F E) g

/-- When `Z` is Hausdorff, the disc-bundle attachment `Z ∪_g D(E)` is Hausdorff. -/
instance t2Space_discBundleAttachmentSpace [T2Space Z] :
    T2Space (discBundleAttachmentSpace F E g) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  t2Space_uliftAdjunctionSpace (discBundle F E) g

/-- **Classical relative CW model of a disc-bundle attachment `Z ∪_g D(E)`.** For a finite-rank
vector bundle `E → B` with continuous fibre norm over a Hausdorff CW complex `B` and any continuous
attaching map `g : S(E) → Z`, the adjunction space `Z ∪_g D(E)` carries a classical relative CW
structure relative to `range (discBundleAttachmentInr F E g)`, whose `(m + r)`-cells correspond to
the `m`-cells of `B`. -/
@[instance_reducible]
def discBundleAttachmentCWModel :
    RelCWComplex (univ : Set (discBundleAttachmentSpace F E g))
      (range (discBundleAttachmentInr F E g)) :=
  letI := relCWComplexDiscBundleSphereBundle F E
  uliftAdjunctionCWModel (discBundle F E) g

/-- The `n`-cells of `discBundleAttachmentCWModel` correspond bijectively to the `m`-cells of `B`
with `m + r = n`, where `r` is the rank of the bundle. -/
def discBundleAttachmentCWModelCellEquiv (n : ℕ) :
    letI := discBundleAttachmentCWModel F E g
    cell (univ : Set (discBundleAttachmentSpace F E g)) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleSphereBundle F E
  (uliftAdjunctionCellEquiv (discBundle F E) g n).trans
    (relCWComplexDiscBundleSphereBundleCellEquiv F E n)

/-- Below the fibre rank `r`, `discBundleAttachmentCWModel` has no `n`-cells. -/
theorem isEmpty_cell_discBundleAttachmentCWModel_of_lt {n : ℕ} (hn : n < Module.finrank ℝ F) :
    letI := discBundleAttachmentCWModel F E g
    IsEmpty (cell (univ : Set (discBundleAttachmentSpace F E g)) n) :=
  let := discBundleAttachmentCWModel F E g
  letI := relCWComplexDiscBundleSphereBundle F E
  have := isEmpty_cell_relCWComplexDiscBundleSphereBundle_of_lt (F := F) (E := E) hn
  (uliftAdjunctionCellEquiv (discBundle F E) g n).isEmpty_congr.2 inferInstance

/-- Each characteristic map of `discBundleAttachmentCWModel` is the characteristic map of the
corresponding cell of `TauCeti.relCWComplexDiscBundleSphereBundle` in `D(E)` followed by
`discBundleAttachmentInl`. -/
theorem discBundleAttachmentCWModel_map_apply {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := discBundleAttachmentCWModel F E g
    letI := relCWComplexDiscBundleSphereBundle F E
    map n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) x =
      discBundleAttachmentInl F E g
        ⟨map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x,
          closedCell_subset_complex n _ (mem_image_of_mem _ hx)⟩ := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  refine (uliftAdjunctionCWModel_map_apply (discBundle F E) g n _ hx).trans ?_
  rw [show uliftAdjunctionCellEquiv (discBundle F E) g n
        ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      (relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c from
    (uliftAdjunctionCellEquiv (discBundle F E) g n).apply_symm_apply _]
  rfl

private theorem image_map_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    letI := discBundleAttachmentCWModel F E g
    letI := relCWComplexDiscBundleSphereBundle F E
    map n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) '' S =
      discBundleAttachmentInl F E g ''
        (Subtype.val ⁻¹'
          (map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) '' S)) := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  refine (image_map_uliftAdjunctionCWModel (discBundle F E) g n _ S hS).trans ?_
  rw [show uliftAdjunctionCellEquiv (discBundle F E) g n
        ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      (relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c from
    (uliftAdjunctionCellEquiv (discBundle F E) g n).apply_symm_apply _]
  rfl

/-- The open cell of `discBundleAttachmentCWModel` over an `m`-cell `j` of `B` is the image under
`discBundleAttachmentInl` of the vectors of norm less than one in `D(E)` over `openCell m j`. -/
@[simp]
theorem openCell_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleAttachmentCWModel F E g
    openCell n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      discBundleAttachmentInl F E g '' {v : discBundle F E |
        (v : TotalSpace F E).proj ∈ openCell c.1.val c.2 ∧ ‖(v : TotalSpace F E).snd‖ < 1} := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  rw [openCell, image_map_discBundleAttachmentCWModel F E g c (ball 0 1) ball_subset_closedBall,
    ← openCell, openCell_relCWComplexDiscBundleSphereBundle]
  congr 1; ext v; simp [and_comm]

/-- The closed cell of `discBundleAttachmentCWModel` over an `m`-cell `j` of `B` is the image under
`discBundleAttachmentInl` of `D(E)` over `closedCell m j`. -/
@[simp]
theorem closedCell_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleAttachmentCWModel F E g
    closedCell n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      discBundleAttachmentInl F E g '' (discBundleProj F E ⁻¹' closedCell c.1.val c.2) := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  rw [closedCell, image_map_discBundleAttachmentCWModel F E g c (closedBall 0 1) Subset.rfl,
    ← closedCell, closedCell_relCWComplexDiscBundleSphereBundle]
  congr 1; ext v; simp

/-- The boundary of the cell of `discBundleAttachmentCWModel` over an `m`-cell `j` of `B` is the
image under `discBundleAttachmentInl` of `S(E)` over `closedCell m j` together with `D(E)` over
`cellFrontier m j`. -/
@[simp]
theorem cellFrontier_discBundleAttachmentCWModel {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    letI := discBundleAttachmentCWModel F E g
    cellFrontier n ((discBundleAttachmentCWModelCellEquiv F E g n).symm c) =
      discBundleAttachmentInl F E g ''
        (Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell c.1.val c.2 ∪
          discBundleProj F E ⁻¹' cellFrontier c.1.val c.2) := by
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  rw [cellFrontier, image_map_discBundleAttachmentCWModel F E g c (sphere 0 1)
    sphere_subset_closedBall, ← cellFrontier, cellFrontier_relCWComplexDiscBundleSphereBundle]
  congr 1; ext v; simp

/-- `discBundleAttachmentCWModel` is finite-dimensional when `B` is finite-dimensional. -/
theorem finiteDimensional_discBundleAttachmentCWModel
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := discBundleAttachmentCWModel F E g
    RelCWComplex.FiniteDimensional (univ : Set (discBundleAttachmentSpace F E g)) :=
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  have := finiteDimensional_relCWComplexDiscBundleSphereBundle F E
  finiteDimensional_uliftAdjunctionCWModel (discBundle F E) g

/-- `discBundleAttachmentCWModel` has finite type when `B` has finite type. -/
theorem finiteType_discBundleAttachmentCWModel [RelCWComplex.FiniteType (univ : Set B)] :
    letI := discBundleAttachmentCWModel F E g
    RelCWComplex.FiniteType (univ : Set (discBundleAttachmentSpace F E g)) :=
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  have := finiteType_relCWComplexDiscBundleSphereBundle F E
  finiteType_uliftAdjunctionCWModel (discBundle F E) g

/-- `discBundleAttachmentCWModel` is finite when `B` is finite. -/
theorem finite_discBundleAttachmentCWModel [RelCWComplex.Finite (univ : Set B)] :
    letI := discBundleAttachmentCWModel F E g
    RelCWComplex.Finite (univ : Set (discBundleAttachmentSpace F E g)) :=
  let _ := discBundleAttachmentCWModel F E g
  let _ := relCWComplexDiscBundleSphereBundle F E
  have := finite_relCWComplexDiscBundleSphereBundle F E
  finite_uliftAdjunctionCWModel (discBundle F E) g

/-- **Base homotopy invariance of disc-bundle attachments.** A homotopy equivalence `e : Z ≃ₕ Z'`
(with `Z` and `Z'` in independent universes) induces a homotopy equivalence
`Z ∪_g D(E) ≃ₕ Z' ∪_{e ∘ g} D(E)` restricting to `e` on `Z` and to `e.symm` on `Z'`. -/
theorem exists_homotopyEquiv_discBundleAttachmentSpace {Z' : Type w} [TopologicalSpace Z']
    (e : Z ≃ₕ Z') :
    ∃ H : discBundleAttachmentSpace.{u, v} F E g ≃ₕ
        discBundleAttachmentSpace.{u, w} F E (e.toFun.comp g),
      (∀ z, H (discBundleAttachmentInr F E g z) =
        discBundleAttachmentInr F E (e.toFun.comp g) (e z)) ∧
      ∀ z', H.symm (discBundleAttachmentInr F E (e.toFun.comp g) z') =
        discBundleAttachmentInr F E g (e.symm z') :=
  let _ := relCWComplexDiscBundleSphereBundle F E
  exists_homotopyEquiv_uliftAdjunctionSpace (discBundle F E) g e

end SphereAttachment

end TauCeti
