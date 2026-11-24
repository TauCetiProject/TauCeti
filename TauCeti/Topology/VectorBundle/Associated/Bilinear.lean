/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Bilinear operations on associated bundles

An equivariant bilinear operation on three representations induces a bilinear operation on
associated fibres. Its value in any common principal frame is the original model operation.
This supplies the fibrewise descent needed for tensor operations and Clifford multiplication;
the inputs need not have the same representation. The operation preserves continuous families.
When the associated bundles are vector bundles, it also defines a continuous iterated Hom-bundle
section, and partial evaluation gives continuous families of linear maps.
No metric on the associated fibres is chosen.

The construction transports the model operation through continuous linear frames. Equivariance is
essential: changing a principal frame changes all three coordinates by the same group element.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, §10.7.
-/

public section

noncomputable section

open Bundle MulOpposite

namespace TauCeti.AssociatedBundle

variable {𝕜 B G F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [DistribMulAction G F₁] [ContinuousSMul G F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [DistribMulAction G F₂] [ContinuousSMul G F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [DistribMulAction G F₃] [ContinuousSMul G F₃]
  (β : F₁ →L[𝕜] F₂ →L[𝕜] F₃)
  (hβ : ∀ (g : G) v w, β (g • v) (g • w) = g • β v w)

variable [SMulCommClass G 𝕜 F₁] [SMulCommClass G 𝕜 F₂] [SMulCommClass G 𝕜 F₃]

/-- The bilinear operation on associated fibres induced by an equivariant continuous bilinear
map. It is characterized in every principal frame by `bilinearMap_mk`. -/
def bilinearMap (_hβ : ∀ (g : G) v w, β (g • v) (g • w) = g • β v w) (b : B) :
    AssociatedBundle G P F₁ b →L[𝕜]
      AssociatedBundle G P F₂ b →L[𝕜] AssociatedBundle G P F₃ b :=
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  ((mkContinuousLinearEquiv 𝕜 G (F := F₂) p).arrowCongr
    (mkContinuousLinearEquiv 𝕜 G (F := F₃) p)).toContinuousLinearMap.comp
      (β.comp (mkContinuousLinearEquiv 𝕜 G p).symm.toContinuousLinearMap)

/-- In any common principal frame, the descended operation is the model bilinear map. -/
@[simp]
theorem bilinearMap_mk {b : B} (p : P b) (v : F₁) (w : F₂) :
    bilinearMap β hβ b (mk G p v) (mk G p w) = mk G p (β v w) := by
  simp only [bilinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongr_apply, mkContinuousLinearEquiv_symm_apply_mk, hβ,
    mkContinuousLinearEquiv_apply]
  exact (mk_eq_mk_iff (G := G) (F := F₃)
    (p := (FiberBundle.homeomorphAt G P b).symm 1) (q := p)).mpr rfl

/-- Evaluate the descended operation in an arbitrary principal frame. -/
theorem bilinearMap_apply {b : B} (p : P b)
    (v : AssociatedBundle G P F₁ b) (w : AssociatedBundle G P F₂ b) :
    bilinearMap β hβ b v w =
      mk G p (β ((mkContinuousLinearEquiv 𝕜 G p).symm v)
        ((mkContinuousLinearEquiv 𝕜 G p).symm w)) := by
  obtain ⟨v, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₁) p).surjective v
  obtain ⟨w, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₂) p).surjective w
  simp

/-- In an arbitrary principal frame, transport of the model operator gives the descended
continuous bilinear map. -/
theorem bilinearMap_eq {b : B} (p : P b) :
    bilinearMap β hβ b =
      ((mkContinuousLinearEquiv 𝕜 G (F := F₂) p).arrowCongr
        (mkContinuousLinearEquiv 𝕜 G (F := F₃) p)).toContinuousLinearMap.comp
          (β.comp (mkContinuousLinearEquiv 𝕜 G p).symm.toContinuousLinearMap) := by
  ext v w
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongr_apply, mkContinuousLinearEquiv_apply] using
      bilinearMap_apply β hβ p v w

/-- Partial evaluation in a principal frame transports the corresponding model linear map. -/
theorem bilinearMap_mk_left {b : B} (p : P b) (v : F₁) :
    bilinearMap β hβ b (mk G p v) =
      (mkContinuousLinearEquiv 𝕜 G (F := F₂) p).arrowCongr
        (mkContinuousLinearEquiv 𝕜 G (F := F₃) p) (β v) := by
  rw [bilinearMap_eq β hβ p]
  simp

/-- The common-frame formula in a single frame uniquely determines the descended operation. -/
theorem bilinearMap_unique {b : B} (p : P b)
    (T : AssociatedBundle G P F₁ b →L[𝕜]
      AssociatedBundle G P F₂ b →L[𝕜] AssociatedBundle G P F₃ b)
    (hT : ∀ v w, T (mk G p v) (mk G p w) = mk G p (β v w)) :
    T = bilinearMap β hβ b := by
  ext v w
  obtain ⟨v, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₁) p).surjective v
  obtain ⟨w, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₂) p).surjective w
  simpa only [mkContinuousLinearEquiv_apply, bilinearMap_mk] using hT v w

/-- In preferred associated charts, the descended operation is the original bilinear map. -/
theorem trivializationAt_bilinearMap_snd {b b' : B}
    (hb : b ∈ (trivializationAt G P b').baseSet)
    (v : AssociatedBundle G P F₁ b) (w : AssociatedBundle G P F₂ b) :
    (trivializationAt F₃ (AssociatedBundle G P F₃) b'
      ⟨b, bilinearMap β hβ b v w⟩).2 =
        β (trivializationAt F₁ (AssociatedBundle G P F₁) b' ⟨b, v⟩).2
          (trivializationAt F₂ (AssociatedBundle G P F₂) b' ⟨b, w⟩).2 := by
  obtain ⟨p, v, rfl⟩ := exists_mk v
  obtain ⟨w, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₂) p).surjective w
  simp only [mkContinuousLinearEquiv_apply, bilinearMap_mk, trivializationAt_mk hb]
  exact (hβ _ v w).symm

section Hom

variable [VectorBundle 𝕜 F₁ (AssociatedBundle G P F₁)]
  [VectorBundle 𝕜 F₂ (AssociatedBundle G P F₂)]
  [VectorBundle 𝕜 F₃ (AssociatedBundle G P F₃)]

/-- In preferred iterated Hom-bundle coordinates the descended operator is the model operator. -/
theorem inCoordinates_bilinearMap {b b' : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) :
    ContinuousLinearMap.inCoordinates F₁ (AssociatedBundle G P F₁) (F₂ →L[𝕜] F₃)
      (fun b ↦ AssociatedBundle G P F₂ b →L[𝕜] AssociatedBundle G P F₃ b)
      b' b b' b (bilinearMap β hβ b) = β := by
  ext v w
  rw [inCoordinates_apply_eq₂
    (by simpa only [baseSet_trivializationAt] using hb)
    (by simpa only [baseSet_trivializationAt] using hb)
    (by simpa only [baseSet_trivializationAt] using hb), Trivialization.linearMapAt_apply,
    trivializationAt_bilinearMap_snd β hβ hb]
  simp [Trivialization.apply_mk_symm, hb, baseSet_trivializationAt]

omit [VectorBundle 𝕜 F₁ (AssociatedBundle G P F₁)] in
/-- Preferred Hom-bundle coordinates of a partial evaluation are partial model evaluation. -/
theorem inCoordinates_bilinearMap_apply {b b' : B}
    (hb : b ∈ (trivializationAt G P b').baseSet) (v : AssociatedBundle G P F₁ b) :
    ContinuousLinearMap.inCoordinates F₂ (AssociatedBundle G P F₂) F₃
      (AssociatedBundle G P F₃) b' b b' b (bilinearMap β hβ b v) =
        β (trivializationAt F₁ (AssociatedBundle G P F₁) b' ⟨b, v⟩).2 := by
  ext w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply]
  rw [Trivialization.symmL_apply _ (by simpa only [baseSet_trivializationAt] using hb),
    trivializationAt_bilinearMap_snd β hβ hb]
  simp [Trivialization.apply_mk_symm, hb, baseSet_trivializationAt]

/-- The descended bilinear operators form a continuous section of the iterated Hom bundle. -/
theorem continuous_bilinearMap :
    Continuous (fun b ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃) b (bilinearMap (P := P) β hβ b)) :=
  TauCeti.continuous_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ β) fun _ _ hb _ ↦
      inCoordinates_bilinearMap β hβ (by simpa only [baseSet_trivializationAt] using hb)

end Hom

end TauCeti.AssociatedBundle

open Filter Set TauCeti TauCeti.AssociatedBundle
open scoped Topology

variable {𝕜 B G F₁ F₂ F₃ X : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [DistribMulAction G F₁] [SMulCommClass G 𝕜 F₁] [ContinuousSMul G F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [DistribMulAction G F₂] [SMulCommClass G 𝕜 F₂] [ContinuousSMul G F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [DistribMulAction G F₃] [SMulCommClass G 𝕜 F₃] [ContinuousSMul G F₃]
  [TopologicalSpace X] (β : F₁ →L[𝕜] F₂ →L[𝕜] F₃)
  (hβ : ∀ (g : G) v w, β (g • v) (g • w) = g • β v w)
  {f : X → B} {v : ∀ x, AssociatedBundle G P F₁ (f x)}
  {w : ∀ x, AssociatedBundle G P F₂ (f x)} {s : Set X} {x₀ : X}

/-- A descended bilinear operation preserves families continuous within a set at a point. -/
theorem ContinuousWithinAt.associatedBundleBilinearMap
    (hv : ContinuousWithinAt
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) s x₀)
    (hw : ContinuousWithinAt
      (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂))) s x₀) :
    ContinuousWithinAt (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
      TotalSpace F₃ (AssociatedBundle G P F₃))) s x₀ := by
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv hw ⊢
  refine ⟨hv.1, ?_⟩
  have h := β.isBoundedBilinearMap.continuous.continuousAt.comp_continuousWithinAt
    (hv.2.prodMk hw.2)
  have h₀ := mem_baseSet_trivializationAt G P (f x₀)
  refine h.congr_of_eventuallyEq ?_ (trivializationAt_bilinearMap_snd β hβ h₀ _ _)
  filter_upwards [hv.1 ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds h₀)] with x hx
  exact trivializationAt_bilinearMap_snd β hβ hx _ _

/-- A descended bilinear operation preserves families continuous at a point. -/
theorem ContinuousAt.associatedBundleBilinearMap
    (hv : ContinuousAt
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) x₀)
    (hw : ContinuousAt
      (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂))) x₀) :
    ContinuousAt (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
      TotalSpace F₃ (AssociatedBundle G P F₃))) x₀ := by
  rw [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.associatedBundleBilinearMap β hβ hv hw

/-- A descended bilinear operation preserves continuous families on a set. -/
theorem ContinuousOn.associatedBundleBilinearMap
    (hv : ContinuousOn
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) s)
    (hw : ContinuousOn
      (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂))) s) :
    ContinuousOn (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
      TotalSpace F₃ (AssociatedBundle G P F₃))) s :=
  fun x hx ↦ (hv x hx).associatedBundleBilinearMap β hβ (hw x hx)

/-- A descended bilinear operation preserves continuous families, including sections. -/
theorem Continuous.associatedBundleBilinearMap
    (hv : Continuous (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))))
    (hw : Continuous (fun x ↦ (⟨f x, w x⟩ : TotalSpace F₂ (AssociatedBundle G P F₂)))) :
    Continuous (fun x ↦ (⟨f x, bilinearMap β hβ (f x) (v x) (w x)⟩ :
      TotalSpace F₃ (AssociatedBundle G P F₃))) :=
  continuous_iff_continuousAt.mpr fun _ ↦
    hv.continuousAt.associatedBundleBilinearMap β hβ hw.continuousAt

section Hom

variable [VectorBundle 𝕜 F₂ (AssociatedBundle G P F₂)]
  [VectorBundle 𝕜 F₃ (AssociatedBundle G P F₃)]

/-- Partial evaluation of the descended operator preserves continuity within a set at a point,
with values in the native Hom bundle. -/
theorem ContinuousWithinAt.associatedBundleBilinearMapLeft
    (hv : ContinuousWithinAt
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) s x₀) :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun b ↦ AssociatedBundle G P F₂ b →L[𝕜] AssociatedBundle G P F₃ b)
      (f x) (bilinearMap β hβ (f x) (v x))) s x₀ := by
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv
  rw [continuousWithinAt_hom_bundle]
  refine ⟨hv.1, ?_⟩
  have h := β.continuous.continuousAt.comp_continuousWithinAt hv.2
  have h₀ := mem_baseSet_trivializationAt G P (f x₀)
  refine h.congr_of_eventuallyEq ?_ (inCoordinates_bilinearMap_apply β hβ h₀ _)
  filter_upwards [hv.1 ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds h₀)] with x hx
  exact inCoordinates_bilinearMap_apply β hβ hx _

/-- Partial evaluation of the descended operator preserves continuity at a point into Hom. -/
theorem ContinuousAt.associatedBundleBilinearMapLeft
    (hv : ContinuousAt
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun b ↦ AssociatedBundle G P F₂ b →L[𝕜] AssociatedBundle G P F₃ b)
      (f x) (bilinearMap β hβ (f x) (v x))) x₀ := by
  rw [← continuousWithinAt_univ] at hv ⊢
  exact hv.associatedBundleBilinearMapLeft β hβ

/-- Partial evaluation of the descended operator preserves continuous families on a set into Hom. -/
theorem ContinuousOn.associatedBundleBilinearMapLeft
    (hv : ContinuousOn
      (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁))) s) :
    ContinuousOn (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun b ↦ AssociatedBundle G P F₂ b →L[𝕜] AssociatedBundle G P F₃ b)
      (f x) (bilinearMap β hβ (f x) (v x))) s :=
  fun x hx ↦ (hv x hx).associatedBundleBilinearMapLeft β hβ

/-- Partial evaluation of the descended operator preserves continuous families into Hom. -/
theorem Continuous.associatedBundleBilinearMapLeft
    (hv : Continuous (fun x ↦ (⟨f x, v x⟩ : TotalSpace F₁ (AssociatedBundle G P F₁)))) :
    Continuous (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
      (E := fun b ↦ AssociatedBundle G P F₂ b →L[𝕜] AssociatedBundle G P F₃ b)
      (f x) (bilinearMap β hβ (f x) (v x))) :=
  continuous_iff_continuousAt.mpr fun _ ↦ hv.continuousAt.associatedBundleBilinearMapLeft β hβ

end Hom
