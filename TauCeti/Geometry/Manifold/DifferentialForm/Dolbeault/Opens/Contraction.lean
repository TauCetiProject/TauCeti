/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ModelSpace
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction
import TauCeti.Geometry.Manifold.DifferentialForm.Interior
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Holomorphic contraction on model spaces and open domains

Constant-vector holomorphic contraction of smooth forms on a complex normed space or an open
subset is built from the same smooth-section construction. Its anticommutation with `∂bar` work in arbitrary dimension; the anticommutation of the
ambient contraction `SmoothForm.holInterior` is the case of the whole space. The final comparison
identifies coordinate differentiation on open subsets of finite-dimensional coordinate spaces.
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.SmoothForm

open SmoothAlmostComplexStructure
open ContinuousAlternatingMap (holCurry holCurry_apply)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

section Opens

open TopologicalSpace

variable {k : ℕ}

section ConstantFields

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

-- TangentSpace is definitionally the model space E. The witness below ensures that the
-- constant fibre vectors actually form smooth sections on the chosen manifold.
/-- The holomorphic contraction of a smooth form by a constant vector, before bundling. -/
private def holInteriorConstFun
    (hc : ∀ w : E, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z : M ↦ (⟨z, w⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (v : E) (η : SmoothForm 𝓘(ℝ, E) M F (k + 1)) :
    SmoothForm 𝓘(ℝ, E) M F k := by
  let insert (w : E) : SmoothForm 𝓘(ℝ, E) M F k :=
    ⟨_,
      (η.isSmoothForm.interior (hc w)).mem_smoothBundleForms⟩
  exact insert v - I • insert (I • v)

private theorem holInteriorConstFun_val
    (hc : ∀ w : E, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z : M ↦ (⟨z, w⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (v : E) (η : SmoothForm 𝓘(ℝ, E) M F (k + 1))
    (z : M) :
    (holInteriorConstFun hc v η).val z = holCurry v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F) := by
  unfold holInteriorConstFun
  simp only [sub_eq_add_neg, add_toRoughForm, neg_toRoughForm, smul_toRoughForm,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply]
  exact (congrArg₂ (fun a b : E [⋀^Fin k]→L[ℝ] F ↦ a + -(I • b))
    (RoughForm.interior_apply_eq_curryLeft (I := 𝓘(ℝ, E)) (F := F) (fun _ ↦ v) η.val z)
    (RoughForm.interior_apply_eq_curryLeft (I := 𝓘(ℝ, E)) (F := F) (fun _ ↦ I • v) η.val z)).trans
      (by simpa only [sub_eq_add_neg] using
        (holCurry_apply (E := E) (F := F) v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F)).symm)

private def holInteriorConst
    (hc : ∀ w : E, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z : M ↦ (⟨z, w⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    E →ₗ[ℂ] SmoothForm 𝓘(ℝ, E) M F (k + 1) →ₗ[ℂ] SmoothForm 𝓘(ℝ, E) M F k :=
  LinearMap.mk₂ ℂ (holInteriorConstFun hc)
    (fun v w η ↦ Subtype.ext <| funext fun z ↦ by
      simp only [add_toRoughForm, Pi.add_apply, holInteriorConstFun_val]
      exact congrArg (fun L ↦ L (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F)) (map_add holCurry v w))
    (fun c v η ↦ Subtype.ext <| funext fun z ↦ by
      simp only [smul_toRoughForm, Pi.smul_apply, holInteriorConstFun_val]
      exact congrArg (fun L ↦ L (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F)) (map_smul holCurry c v))
    (fun v η θ ↦ Subtype.ext <| funext fun z ↦ by
      simp only [add_toRoughForm, Pi.add_apply, holInteriorConstFun_val]
      exact map_add (holCurry v) (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F) (θ.val z))
    (fun c v η ↦ Subtype.ext <| funext fun z ↦ by
      simp only [smul_toRoughForm, Pi.smul_apply, holInteriorConstFun_val]
      exact map_smul (holCurry v) c (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F))

/-- The `(1,0)`-contraction lowers the holomorphic degree. -/
private theorem isOfType_holInteriorConst
    (hc : ∀ w : E, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z : M ↦ (⟨z, w⟩ : TangentBundle 𝓘(ℝ, E) M))) {p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, E) M F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold E M) (p + 1) q) (v : E) :
    (holInteriorConst hc v η).IsOfType (ofComplexManifold E M) p q := by
  refine isOfType_iff_forall.2 ⟨by have := hη.add_eq; omega, fun z ↦ ?_⟩
  have h := hη.apply z
  rw [toEndomorphism_ofComplexManifold] at h ⊢
  exact (holInteriorConstFun_val hc v η z).symm ▸
    ContinuousAlternatingMap.IsOfType.holCurry (E := E) h v

end ConstantFields

/-- The holomorphic contraction of smooth forms by constant vectors: the combination
`ι_v - I • ι_{I • v}`, with `I` acting on the output, as a complex-bilinear map in the vector and
the form. -/
def holInterior : E →ₗ[ℂ] SmoothForm 𝓘(ℝ, E) E F (k + 1) →ₗ[ℂ] SmoothForm 𝓘(ℝ, E) E F k :=
  holInteriorConst (fun w ↦
    contMDiff_tangentBundleModelSpaceHomeomorph_symm_prodMk_const 𝓘(ℝ, E) w ∞)

/-- The value of a holomorphic contraction is the pointwise contraction. -/
@[simp]
theorem holInterior_val (v : E) (η : SmoothForm 𝓘(ℝ, E) E F (k + 1)) (z : E) :
    (holInterior v η).val z = holCurry v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F) :=
  holInteriorConstFun_val (fun w ↦
    contMDiff_tangentBundleModelSpaceHomeomorph_symm_prodMk_const 𝓘(ℝ, E) w ∞) v η z

/-- The `(1,0)`-contraction lowers the holomorphic degree. -/
theorem isOfType_holInterior {p q : ℕ} {η : SmoothForm 𝓘(ℝ, E) E F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold E E) (p + 1) q) (v : E) :
    (holInterior v η).IsOfType (ofComplexManifold E E) p q :=
  isOfType_holInteriorConst _ hη v

private theorem contMDiff_constField_opens (U : Opens E) (w : E) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun z : U ↦ (⟨z, w⟩ : TangentBundle 𝓘(ℝ, E) U)) :=
  fun z ↦ Manifold.contMDiffAt_tangentBundle_opens_iff.2
    ((contMDiff_tangentBundleModelSpaceHomeomorph_symm_prodMk_const
      𝓘(ℝ, E) w ∞).contMDiffAt.comp z contMDiff_subtypeVal.contMDiffAt)

/-- The holomorphic contraction `ι_v - I • ι_{I • v}`, with `I` acting on the output
and no factor of `1/2`, as a complex-bilinear map on an open model domain. -/
def holInteriorOpens {U : Opens E} :
    E →ₗ[ℂ] SmoothForm 𝓘(ℝ, E) U F (k + 1) →ₗ[ℂ] SmoothForm 𝓘(ℝ, E) U F k :=
  holInteriorConst (contMDiff_constField_opens U)

/-- The value of a holomorphic contraction is the pointwise contraction. -/
@[simp]
theorem holInteriorOpens_val {U : Opens E} (v : E) (η : SmoothForm 𝓘(ℝ, E) U F (k + 1)) (z : U) :
    (holInteriorOpens v η).val z = holCurry v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F) :=
  holInteriorConstFun_val (contMDiff_constField_opens U) v η z

/-- Holomorphic contraction lowers the holomorphic degree on an open model domain. -/
theorem isOfType_holInteriorOpens {U : Opens E} {p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, E) U F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold E U) (p + 1) q) (v : E) :
    (holInteriorOpens v η).IsOfType (ofComplexManifold E U) p q :=
  isOfType_holInteriorConst _ hη v

/-- Constant-vector holomorphic contraction anticommutes with `∂bar` on an open subset of any
complex normed space, without a finite-dimensionality assumption. -/
theorem delBar_holInteriorOpens {U : Opens E} (v : E)
    (η : SmoothForm 𝓘(ℝ, E) U F (k + 1)) :
    (ofComplexManifold E U).delBar (holInteriorOpens v η) =
      -holInteriorOpens v ((ofComplexManifold E U).delBar η) := by
  obtain ⟨η₀, hη₀c, hη₀⟩ := η.isSmoothForm.exists_contDiffOn_opens
  refine Subtype.ext (funext fun z ↦ ?_)
  let C := (holCurry (k := k) (F := F) v).restrictScalars ℝ
  have hd : DifferentiableAt ℝ η₀ (z : E) :=
    (hη₀c.contDiffAt (U.isOpen.mem_nhds z.property)).differentiableAt (by simp)
  have hC (y : U) : (holInteriorOpens v η).val y = (C ∘ η₀) y :=
    (holInteriorOpens_val v η y).trans (congrArg C (hη₀ y))
  rw [neg_toRoughForm, Pi.neg_apply, holInteriorOpens_val,
    delBar_eq_alternatizeUncurryFin_of_opens _ hC,
    delBar_eq_alternatizeUncurryFin_of_opens η hη₀,
    C.fderiv_comp_left hd,
    ContinuousLinearMap.complexAntilinearPartL_restrictScalars_comp]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_holCurry_comp _
    (fun u ↦ (ContinuousLinearMap.complexAntilinearPartL_apply_I_smul _ u).trans
      (neg_smul I _).symm) v

/-- Restriction to an open domain commutes with constant-vector holomorphic contraction. -/
theorem mpullback_holInterior {U : Opens E} (v : E)
    (η : SmoothForm 𝓘(ℝ, E) E F (k + 1)) :
    mpullback (Subtype.val : U → E) contMDiff_subtypeVal (holInterior v η) =
      holInteriorOpens v (mpullback (Subtype.val : U → E) contMDiff_subtypeVal η) := by
  apply Subtype.ext
  funext z
  rw [coe_mpullback_subtype_val_apply, holInterior_val, holInteriorOpens_val,
    coe_mpullback_subtype_val_apply]

/-- The `(1,0)`-contraction with a constant vector anticommutes with `∂bar`. This is the case
`U = ⊤` of `delBar_holInteriorOpens`. -/
theorem delBar_holInterior (v : E) (η : SmoothForm 𝓘(ℝ, E) E F (k + 1)) :
    (ofComplexManifold E E).delBar (holInterior v η) =
      -holInterior v ((ofComplexManifold E E).delBar η) := by
  apply Subtype.ext
  funext z
  rw [delBar_val_eq_mpullback_top, mpullback_holInterior, delBar_holInteriorOpens,
    neg_toRoughForm, Pi.neg_apply, holInteriorOpens_val,
    ← delBar_val_eq_mpullback_top, neg_toRoughForm, Pi.neg_apply, holInterior_val]
  -- Negation in the manifold fibre is definitionally negation in the model fibre.
  rfl

end Opens

section Coordinates

open Metric TopologicalSpace
open scoped Finset

variable {ι : Type*} [Fintype ι]

/-- On an open subset of `ι → ℂ`, evaluations of `∂bar φ` on increasing tuples of coordinate
vectors are obtained by `TauCeti.delBarCoeff` from the corresponding evaluations of an ambient
representative. For forms of type `(0,k)`, these evaluations are the antiholomorphic coframe
coefficients. -/
theorem delBar_val_apply_orderEmbOfFin_of_opens [LinearOrder ι] {U : Opens (ι → ℂ)}
    {k : ℕ} {φ : SmoothForm 𝓘(ℝ, ι → ℂ) U F k} {φ₀ : (ι → ℂ) → (ι → ℂ) [⋀^Fin k]→L[ℝ] F}
    (hφ₀ : ∀ x : U, φ.val x = φ₀ x) {a : Finset ι → (ι → ℂ) → F}
    (ha : ∀ J (hJ : #J = k), ∀ y ∈ U, a J y = φ₀ y fun i ↦ Pi.single (J.orderEmbOfFin hJ i) 1)
    (z : U) {I : Finset ι} (hI : #I = k + 1) :
    ((ofComplexManifold (ι → ℂ) U).delBar φ).val z
      (fun i ↦ Pi.single (I.orderEmbOfFin hI i) 1) = delBarCoeff a I z := by
  have hc := (isSmoothForm_opens_iff hφ₀).1 φ.isSmoothForm
  rw [delBar_eq_alternatizeUncurryFin_of_opens φ hφ₀]
  exact (delBarCoeff_eq_alternatizeUncurryFin
    ((hc.contDiffAt (U.isOpen.mem_nhds z.property)).differentiableAt (by simp)) hI
    fun J hJ ↦ by
      filter_upwards [U.isOpen.mem_nhds z.property] with y hy
      rw [ha J hJ y hy, ContinuousAlternatingMap.conjCoeff_of_card_eq _ hJ]).symm

end Coordinates

end TauCeti.SmoothForm
