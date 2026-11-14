/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated
public import TauCeti.Topology.FiberBundle.Associated.Map
public import TauCeti.Topology.FiberBundle.Associated.Prod
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Bilinear operations on associated bundles

An equivariant bilinear operation on three representations induces a bilinear operation on
associated fibres. Its value in any common principal frame is the original model operation.
This supplies the fibrewise descent needed for tensor operations and Clifford multiplication;
the inputs need not have the same representation. The operation preserves continuous families.
No metric on the associated fibres is chosen.

The construction reuses the associated map and associated-product comparison. Equivariance is
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

private def bilinearMapAux {b : B} (v : AssociatedBundle G P F₁ b)
    (w : AssociatedBundle G P F₂ b) : AssociatedBundle G P F₃ b :=
  map (⟨fun z : F₁ × F₂ ↦ β z.1 z.2, fun g z ↦ hβ g z.1 z.2⟩ : F₁ × F₂ →[G] F₃)
    ((prodEquiv b).symm (v, w))

private theorem bilinearMapAux_mk {b : B} (p : P b) (v : F₁) (w : F₂) :
    bilinearMapAux β hβ (mk G p v) (mk G p w) = mk G p (β v w) := by
  simp only [bilinearMapAux, prodEquiv_symm_mk, map_mk]
  rfl

variable [SMulCommClass G 𝕜 F₁] [SMulCommClass G 𝕜 F₂] [SMulCommClass G 𝕜 F₃]

/-- The bilinear operation on associated fibres induced by an equivariant continuous bilinear
map. It is characterized in every principal frame by `bilinearMap_mk`. -/
def bilinearMap (b : B) :
    AssociatedBundle G P F₁ b →ₗ[𝕜]
      AssociatedBundle G P F₂ b →ₗ[𝕜] AssociatedBundle G P F₃ b := by
  let p := (FiberBundle.homeomorphAt G P b).symm 1
  have h₁ := (mkContinuousLinearEquiv 𝕜 G (F := F₁) p).surjective
  have h₂ := (mkContinuousLinearEquiv 𝕜 G (F := F₂) p).surjective
  refine
    { toFun := fun v ↦
        { toFun := bilinearMapAux β hβ v
          map_add' := ?_
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro w w'
    obtain ⟨v, rfl⟩ := h₁ v
    obtain ⟨w, rfl⟩ := h₂ w
    obtain ⟨w', rfl⟩ := h₂ w'
    simp only [mkContinuousLinearEquiv_apply, ← mk_add, bilinearMapAux_mk, map_add]
  · intro r w
    obtain ⟨v, rfl⟩ := h₁ v
    obtain ⟨w, rfl⟩ := h₂ w
    simp only [mkContinuousLinearEquiv_apply, ← mk_smul_scalar, bilinearMapAux_mk,
      map_smul, RingHom.id_apply]
  · intro v v'
    ext w
    obtain ⟨v, rfl⟩ := h₁ v
    obtain ⟨v', rfl⟩ := h₁ v'
    obtain ⟨w, rfl⟩ := h₂ w
    simp only [mkContinuousLinearEquiv_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply, ← mk_add, bilinearMapAux_mk, map_add, add_apply]
  · intro r v
    ext w
    obtain ⟨v, rfl⟩ := h₁ v
    obtain ⟨w, rfl⟩ := h₂ w
    simp only [mkContinuousLinearEquiv_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, ← mk_smul_scalar, bilinearMapAux_mk, map_smul,
      smul_apply, RingHom.id_apply]

/-- In any common principal frame, the descended operation is the model bilinear map. -/
@[simp]
theorem bilinearMap_mk {b : B} (p : P b) (v : F₁) (w : F₂) :
    bilinearMap β hβ b (mk G p v) (mk G p w) = mk G p (β v w) :=
  bilinearMapAux_mk β hβ p v w

/-- Evaluate the descended operation in an arbitrary principal frame. -/
theorem bilinearMap_apply {b : B} (p : P b)
    (v : AssociatedBundle G P F₁ b) (w : AssociatedBundle G P F₂ b) :
    bilinearMap β hβ b v w =
      mk G p (β ((mkContinuousLinearEquiv 𝕜 G p).symm v)
        ((mkContinuousLinearEquiv 𝕜 G p).symm w)) := by
  obtain ⟨v, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₁) p).surjective v
  obtain ⟨w, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₂) p).surjective w
  simp

/-- The common-frame formula uniquely determines the descended bilinear operation. -/
theorem bilinearMap_unique {b : B}
    (T : AssociatedBundle G P F₁ b →ₗ[𝕜]
      AssociatedBundle G P F₂ b →ₗ[𝕜] AssociatedBundle G P F₃ b)
    (hT : ∀ (p : P b) v w, T (mk G p v) (mk G p w) = mk G p (β v w)) :
    T = bilinearMap β hβ b := by
  ext v w
  obtain ⟨p, v, rfl⟩ := exists_mk v
  obtain ⟨w, rfl⟩ := (mkContinuousLinearEquiv 𝕜 G (F := F₂) p).surjective w
  simpa only [mkContinuousLinearEquiv_apply, bilinearMap_mk] using hT p v w

/-- In preferred associated charts, the descended operation is the original bilinear map. -/
theorem trivializationAt_bilinearMap {b b' : B}
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
  refine h.congr_of_eventuallyEq ?_ (trivializationAt_bilinearMap β hβ h₀ _ _)
  filter_upwards [hv.1 ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds h₀)] with x hx
  exact trivializationAt_bilinearMap β hβ hx _ _

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
