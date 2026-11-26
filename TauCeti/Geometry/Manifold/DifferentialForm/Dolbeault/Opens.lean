/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ModelSpace
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens.ModelSpace

/-!
# Dolbeault calculus on open model domains

The Dolbeault differential on open subsets of complex normed spaces agrees with that of any
ambient smooth representative near the point. In finite dimensions smooth germs extend to
ambient forms, preserving pure type. This file also provides constant-vector holomorphic
contraction and the comparison with coordinate differentiation on open subsets.
-/

public section

noncomputable section

open Complex Filter Set Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti.SmoothForm

open SmoothAlmostComplexStructure
open ContinuousAlternatingMap (holCurry)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

section Opens

open TopologicalSpace

variable {k : ℕ}

/-- On an open subset `U` of a complex vector space `E`, the Dolbeault differential of a form `η`
at a point `z` is that of any smooth form on `E` agreeing near `z` with an ambient representative
`η₀` of `η`. -/
theorem delBar_val_eq_of_eventuallyEq {U : Opens E} {η : SmoothForm 𝓘(ℝ, E) U F k}
    {η₀ : E → E [⋀^Fin k]→L[ℝ] F} (hη₀ : ∀ x : U, η.val x = η₀ x)
    {G : SmoothForm 𝓘(ℝ, E) E F k} {z : U} (hG : G.val =ᶠ[𝓝 (z : E)] η₀) :
    ((ofComplexManifold E U).delBar η).val z = ((ofComplexManifold E E).delBar G).val z := by
  obtain ⟨t, htG, ht, hzt⟩ := eventually_nhds_iff.1 hG
  let V : Opens E := ⟨t ∩ U, ht.inter U.isOpen⟩
  have hVU : V ≤ U := inter_subset_right
  -- The restrictions of `η` and `G` to `V` agree, and restriction commutes with `∂bar`.
  have hres : mpullback (Opens.inclusion hVU) (contMDiff_inclusion hVU) η =
      mpullback (Subtype.val : V → E) contMDiff_subtypeVal G := by
    refine Subtype.ext (funext fun y ↦ ?_)
    rw [coe_mpullback, mpullback_inclusion_apply, coe_mpullback_subtype_val_apply, hη₀,
      htG _ y.property.1]
  have h := congrArg (fun φ ↦ ((ofComplexManifold E V).delBar φ).val ⟨z, hzt, z.property⟩) hres
  simp only [← mpullback_delBar _ _ (isPseudoholomorphic_ofComplexManifold_inclusion hVU),
    ← mpullback_delBar _ _ (isPseudoholomorphic_ofComplexManifold_subtype_val V)] at h
  rwa [coe_mpullback, mpullback_inclusion_apply, coe_mpullback_subtype_val_apply] at h

variable [FiniteDimensional ℂ E]

/-- Near a point of an open subset `U` of a finite-dimensional complex vector space `E`, a form of
type `(p,q)` on `U`, with an ambient representative `η₀` smooth on `U`, agrees with a smooth form of
type `(p,q)` on `E`: the type-`(p,q)` component of any smooth form on `E` agreeing with `η₀` near
the point. -/
theorem IsOfType.exists_isOfType_eventuallyEq_of_opens {U : Opens E} {p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, E) U F k} (hη : η.IsOfType (ofComplexManifold E U) p q)
    {η₀ : E → E [⋀^Fin k]→L[ℝ] F} (hη₀ : ∀ x : U, η.val x = η₀ x)
    (hc : ContDiffOn ℝ ∞ η₀ U) (z : U) :
    ∃ G : SmoothForm 𝓘(ℝ, E) E F k,
      G.IsOfType (ofComplexManifold E E) p q ∧ G.val =ᶠ[𝓝 (z : E)] η₀ := by
  obtain ⟨G, hG⟩ := exists_eventuallyEq_of_opens hc z
  refine ⟨(ofComplexManifold E E).typeProjection p q G,
    (ofComplexManifold E E).isOfType_typeProjection hη.add_eq G, ?_⟩
  filter_upwards [hG, U.isOpen.mem_nhds z.property] with y hy hyU
  have h := hη.apply ⟨y, hyU⟩
  rw [toEndomorphism_ofComplexManifold, hη₀] at h
  simp only [coe_typeProjection, toEndomorphism_ofComplexManifold, hy]
  exact h.typeProjection_self

omit [FiniteDimensional ℂ E] in
/-- Holomorphic contraction by a constant ambient vector on an open model domain. -/
def holInteriorOpens {U : Opens E} (v : E) (η : SmoothForm 𝓘(ℝ, E) U F (k + 1)) :
    SmoothForm 𝓘(ℝ, E) U F k := by
  refine ⟨fun z ↦ holCurry v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F), ?_⟩
  obtain ⟨η₀, hη₀c, hη₀⟩ := η.isSmoothForm.exists_contDiffOn_opens
  let C := (holCurry (k := k) (F := F) v).restrictScalars ℝ
  exact ((isSmoothForm_opens_iff (fun z ↦ congrArg C (hη₀ z))).2
    (C.contDiff.comp_contDiffOn hη₀c)).mem_smoothBundleForms

omit [FiniteDimensional ℂ E] in
/-- The value of contraction on an open model domain is the fibrewise contraction. -/
@[simp]
theorem holInteriorOpens_val {U : Opens E} (v : E)
    (η : SmoothForm 𝓘(ℝ, E) U F (k + 1)) (z : U) :
    (holInteriorOpens v η).val z = holCurry v (η.val z : E [⋀^Fin (k + 1)]→L[ℝ] F) := by
  rfl

omit [FiniteDimensional ℂ E] in
/-- Holomorphic contraction lowers the holomorphic degree on an open model domain. -/
theorem isOfType_holInteriorOpens {U : Opens E} {p q : ℕ}
    {η : SmoothForm 𝓘(ℝ, E) U F (k + 1)}
    (hη : η.IsOfType (ofComplexManifold E U) (p + 1) q) (v : E) :
    (holInteriorOpens v η).IsOfType (ofComplexManifold E U) p q := by
  refine isOfType_iff_forall.2 ⟨by have := hη.add_eq; omega, fun z ↦ ?_⟩
  have h := hη.apply z
  rw [toEndomorphism_ofComplexManifold] at h ⊢
  exact ContinuousAlternatingMap.IsOfType.holCurry (E := E) h v

/-- Constant-vector holomorphic contraction anticommutes with `∂bar` on an open model domain. -/
theorem delBar_holInteriorOpens {U : Opens E} (v : E)
    (η : SmoothForm 𝓘(ℝ, E) U F (k + 1)) :
    (ofComplexManifold E U).delBar (holInteriorOpens v η) =
      -holInteriorOpens v ((ofComplexManifold E U).delBar η) := by
  obtain ⟨η₀, hη₀c, hη₀⟩ := η.isSmoothForm.exists_contDiffOn_opens
  refine Subtype.ext (funext fun z ↦ ?_)
  obtain ⟨G, hG⟩ := exists_eventuallyEq_of_opens hη₀c z
  have hC : (holInterior v G).val =ᶠ[𝓝 (z : E)] (fun x ↦ holCurry v (η₀ x)) := by
    filter_upwards [hG] with y hy
    rw [holInterior_val, hy]
  rw [delBar_val_eq_of_eventuallyEq (fun x ↦ congrArg (holCurry v) (hη₀ x)) hC,
    delBar_holInterior, neg_toRoughForm, Pi.neg_apply, holInterior_val,
    ← delBar_val_eq_of_eventuallyEq hη₀ hG]
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
    (hφ₀ : ∀ x : U, φ.val x = φ₀ x) (hc : ContDiffOn ℝ ∞ φ₀ U) {a : Finset ι → (ι → ℂ) → F}
    (ha : ∀ J (hJ : #J = k), ∀ y ∈ U, a J y = φ₀ y fun i ↦ Pi.single (J.orderEmbOfFin hJ i) 1)
    (z : U) {I : Finset ι} (hI : #I = k + 1) :
    ((ofComplexManifold (ι → ℂ) U).delBar φ).val z
      (fun i ↦ Pi.single (I.orderEmbOfFin hI i) 1) = delBarCoeff a I z := by
  obtain ⟨G, hG⟩ := exists_eventuallyEq_of_opens hc z
  have hcoeff (j : ι) (hj : j ∈ I) : a (I.erase j) =ᶠ[𝓝 (z : ι → ℂ)] G.conjCoeff (I.erase j) := by
    have hcard : #(I.erase j) = k := by rw [Finset.card_erase_of_mem hj, hI, Nat.add_sub_cancel]
    filter_upwards [hG, U.isOpen.mem_nhds z.property] with y hy hyU
    rw [ha _ hcard y hyU, conjCoeff_of_card_eq _ hcard, hy]
    -- Both sides evaluate `φ₀ y` on the same coordinate vectors, read in the tangent space.
    rfl
  rw [delBarCoeff_congr hcoeff, ← conjCoeff_delBar, conjCoeff_of_card_eq _ hI,
    delBar_val_eq_of_eventuallyEq hφ₀ hG]
  -- Both sides evaluate on the same coordinate vectors, read in the tangent space.
  rfl

end Coordinates

end TauCeti.SmoothForm
