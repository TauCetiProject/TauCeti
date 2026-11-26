/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace
public import TauCeti.Analysis.Normed.Module.Alternating.Complex
import TauCeti.Analysis.Calculus.FDeriv.AlmostComplexType

/-!
# Flat formula for Dolbeault differentiation on open subsets

The Dolbeault differential on an open subset of a complex normed space is computed by
alternatizing the conjugate-linear part of the derivative of an ambient representative.
Only the germ of that representative is used, in arbitrary dimension.
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.SmoothForm

open SmoothAlmostComplexStructure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

/-- On a form of pure type, `∂bar` is the alternation of the conjugate-linear part of the
real derivative of its coefficient field. -/
private theorem delBar_eq_alternatizeUncurryFin_of_isOfType {p q : ℕ}
    {U : TopologicalSpace.Opens E} {η : SmoothForm 𝓘(ℝ, E) U F k}
    (hη : η.IsOfType (ofComplexManifold E U) p q)
    {η₀ : E → E [⋀^Fin k]→L[ℝ] F} (hη₀ : ∀ y : U, η.val y = η₀ y) (z : U) :
    ((ofComplexManifold E U).delBar η).val z =
      ContinuousAlternatingMap.alternatizeUncurryFin (E := E) (F := F)
        (ContinuousLinearMap.complexAntilinearPartL
          (fderiv ℝ η₀ (z : E))) := by
  let Θ : E → E [⋀^Fin k]→L[ℝ] F := η₀
  let Jm : E →L[ℝ] E := I • ContinuousLinearMap.id ℝ E
  let L : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F := fderiv ℝ Θ (z : E)
  have hJm (w : E) : Jm (Jm w) = -w := by simp [Jm, smul_smul]
  -- The derivative of a family of forms of type `(p,q)` still has that type.
  have htype (w : E) : (L w).IsOfType Jm p q := by
    have ht : ∀ᶠ y in 𝓝 (z : E), (Θ y).IsOfType Jm p q := by
      filter_upwards [U.isOpen.mem_nhds z.property] with y hy
      have h := hη.apply ⟨y, hy⟩
      rw [toEndomorphism_ofComplexManifold, hη₀] at h
      exact h
    simpa only [fderivWithin_univ, nhdsWithin_univ] using
      ContinuousAlternatingMap.isOfType_fderivWithin (Θ := Θ) (J := Jm)
        uniqueDiffWithinAt_univ (mem_univ (z : E)) (by simpa using ht) w
  have hflat : (mextDerivₗ 𝓘(ℝ, E) k η).val z = extDeriv Θ (z : E) := by
    rw [mextDerivₗ_apply]
    exact mextDeriv_opens_eq_extDeriv hη₀ z
  -- `∂bar η` is the alternation of the conjugate-linear part of the derivative of `Θ`.
  have hδ : ((ofComplexManifold E U).delBar η).val z =
      ContinuousAlternatingMap.alternatizeUncurryFin ((2 : ℂ)⁻¹ • (L + I • L ∘L Jm)) := by
    rw [hη.delBar_eq, coe_typeProjection]
    refine (congrArg (fun A : E →L[ℝ] E ↦ A.typeProjection p (q + 1)
      ((mextDerivₗ 𝓘(ℝ, E) k η).val z)) (toEndomorphism_ofComplexManifold (E := E) z)).trans ?_
    rw [hflat]
    exact ContinuousAlternatingMap.typeProjection_alternatizeUncurryFin_succ_right hJm htype
  refine hδ.trans (congrArg ContinuousAlternatingMap.alternatizeUncurryFin ?_)
  ext v : 1
  simp only [L, Θ, Jm, ContinuousLinearMap.complexAntilinearPartL_apply_apply,
    _root_.smul_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ← ofReal_ofNat, ← ofReal_inv, Complex.coe_smul]

/-- On an open subset of a complex normed space, `∂bar` is the alternation of the
conjugate-linear part of the derivative of any ambient representative. Its values outside the
open subset are irrelevant; no finite-dimensionality or boundary extension is required. -/
theorem delBar_eq_alternatizeUncurryFin_of_opens {U : TopologicalSpace.Opens E}
    (η : SmoothForm 𝓘(ℝ, E) U F k) {η₀ : E → E [⋀^Fin k]→L[ℝ] F}
    (hη₀ : ∀ y : U, η.val y = η₀ y) (z : U) :
    ((ofComplexManifold E U).delBar η).val z =
      ContinuousAlternatingMap.alternatizeUncurryFin
        (ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ η₀ (z : E))) := by
  classical
  let field (φ : SmoothForm 𝓘(ℝ, E) U F k) (y : E) :
      E [⋀^Fin k]→L[ℝ] F := if hy : y ∈ U then φ.val ⟨y, hy⟩ else 0
  have hfield (φ : SmoothForm 𝓘(ℝ, E) U F k) (y : U) : φ.val y = field φ y := by
    simp [field]
  have hd (φ : SmoothForm 𝓘(ℝ, E) U F k) : DifferentiableAt ℝ (field φ) (z : E) :=
    ((isSmoothForm_opens_iff (hfield φ)).1 φ.isSmoothForm).contDiffAt
      (U.isOpen.mem_nhds z.property) |>.differentiableAt (by simp)
  let C (Φ : E → E [⋀^Fin k]→L[ℝ] F) :=
    ContinuousAlternatingMap.alternatizeUncurryFin
      (ContinuousLinearMap.complexAntilinearPartL (fderiv ℝ Φ (z : E)))
  let A : SmoothForm 𝓘(ℝ, E) U F k →+ E [⋀^Fin (k + 1)]→L[ℝ] F :=
    { toFun φ := ((ofComplexManifold E U).delBar φ).val z
      -- `∂bar` is additive; the final `rfl` identifies the zero and addition of the fibre at `z`
      -- with those of its model space `E [⋀^Fin (k + 1)]→L[ℝ] F`.
      map_zero' := by rw [map_zero, ZeroMemClass.coe_zero, Pi.zero_apply]; rfl
      map_add' φ ψ := by rw [map_add, AddMemClass.coe_add, Pi.add_apply]; rfl }
  let B : SmoothForm 𝓘(ℝ, E) U F k →+ E [⋀^Fin (k + 1)]→L[ℝ] F :=
    { toFun φ := C (field φ)
      map_zero' := by
        have hzero : field 0 = fun _ ↦ 0 := by
          funext y
          -- Identify the zero tangent-fibre form with the zero model-fibre map.
          change (if _ : y ∈ U then 0 else (0 : E [⋀^Fin k]→L[ℝ] F)) = 0
          simp
        simp only [hzero, C, fderiv_const_apply, map_zero,
          ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
      map_add' φ ψ := by
        have hadd : field (φ + ψ) = field φ + field ψ := by
          funext y
          by_cases hy : y ∈ U
          · simp only [field, hy, ↓reduceDIte, Pi.add_apply]
            -- The value of `φ + ψ` at `⟨y, hy⟩`, read in the model fibre `E [⋀^Fin k]→L[ℝ] F`.
            exact congrFun (add_toRoughForm φ ψ) ⟨y, hy⟩
          · simp [field, hy]
        simp only [hadd, C, fderiv_add (hd φ) (hd ψ), map_add,
          ContinuousAlternatingMap.alternatizeUncurryFin_add] }
  have h := (ofComplexManifold E U).map_eq_of_forall_isOfType (f := A) (g := B)
    (fun _ _ _ _ hφ ↦ delBar_eq_alternatizeUncurryFin_of_isOfType hφ (hfield _) z) η
  have heq : field η =ᶠ[𝓝 (z : E)] η₀ := by
    filter_upwards [U.isOpen.mem_nhds z.property] with y hy
    exact (hfield η ⟨y, hy⟩).symm.trans (hη₀ ⟨y, hy⟩)
  exact h.trans (congrArg
    (fun L ↦ ContinuousAlternatingMap.alternatizeUncurryFin
      (ContinuousLinearMap.complexAntilinearPartL L)) heq.fderiv_eq)

end TauCeti.SmoothForm
