/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Hom
public import TauCeti.Analysis.CStarAlgebra.Action.Lp
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Bochner `Lᵖ` functoriality of equivariant C⋆-algebra homomorphisms

This file packages pointwise application of an equivariant C⋆-algebra homomorphism
`φ : CStarAction.Hom α β` on Bochner `Lᵖ` spaces as a contractive continuous linear map
`TauCeti.CStarAction.Hom.mapLp : Lp A p μ →L[ℂ] Lp B p μ` (`1 ≤ p ≤ ∞`), without requiring local
compactness or twisted convolution, and shows that `mapLp` intertwines `CStarAction.actionLp` and
`CStarAction.translateLp`.

## Main definitions and results

* `TauCeti.CStarAction.Hom.mapLp`: pointwise postcomposition on `Lp A p μ`, with
  `TauCeti.CStarAction.Hom.coeFn_mapLp`, `TauCeti.CStarAction.Hom.norm_mapLp_le`,
  `TauCeti.CStarAction.Hom.mapLp_id`, `TauCeti.CStarAction.Hom.mapLp_comp`,
  `TauCeti.CStarAction.Hom.mapLp_injective`, `TauCeti.CStarAction.Hom.mapLp_actionLp`, and
  `TauCeti.CStarAction.Hom.mapLp_translateLp`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.CStarAction.Hom

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} {β : CStarAction G B} {γ : CStarAction G C}
  [MeasurableSpace G] (μ : Measure G) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pointwise application of an equivariant C⋆-algebra homomorphism `φ : Hom α β` on `Lp A p μ`,
as a contractive continuous linear map `Lp A p μ →L[ℂ] Lp B p μ`. -/
def mapLp (φ : Hom α β) : Lp A p μ →L[ℂ] Lp B p μ :=
  φ.toNonUnitalStarAlgHom.toContinuousLinearMap.compLpL p μ

variable {μ p}

/-- `Hom.mapLp` is composition on `Lp` with `φ.toNonUnitalStarAlgHom.toContinuousLinearMap`. -/
theorem mapLp_eq_compLpL (φ : Hom α β) :
    φ.mapLp μ p = φ.toNonUnitalStarAlgHom.toContinuousLinearMap.compLpL p μ :=
  (rfl)

/-- Pointwise almost-everywhere formula for `Hom.mapLp`. -/
theorem coeFn_mapLp (φ : Hom α β) (u : Lp A p μ) : φ.mapLp μ p u =ᵐ[μ] fun s => φ (u s) := by
  simpa only [mapLp_eq_compLpL, NonUnitalStarAlgHom.coe_toContinuousLinearMap,
    coe_toNonUnitalStarAlgHom] using
    φ.toNonUnitalStarAlgHom.toContinuousLinearMap.coeFn_compLpL (p := p) (μ := μ) u

/-- `Hom.mapLp` is a contraction: `‖φ.mapLp μ p‖ ≤ 1`. -/
theorem norm_mapLp_le (φ : Hom α β) : ‖φ.mapLp μ p‖ ≤ 1 := by
  rw [mapLp_eq_compLpL]
  exact (φ.toNonUnitalStarAlgHom.toContinuousLinearMap.norm_compLpL_le (p := p) (μ := μ)).trans
    φ.toNonUnitalStarAlgHom.norm_toContinuousLinearMap_le

/-- The identity equivariant homomorphism induces the identity on `Lp A p μ`. -/
@[simp]
theorem mapLp_id : (Hom.id α).mapLp μ p = ContinuousLinearMap.id ℂ (Lp A p μ) := by
  rw [mapLp_eq_compLpL]
  have hid : (Hom.id α).toNonUnitalStarAlgHom.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ A := by ext a; simp
  rw [hid, ContinuousLinearMap.id_compLpL]

/-- `Hom.mapLp` preserves composition of equivariant homomorphisms. -/
@[simp]
theorem mapLp_comp (ψ : Hom β γ) (φ : Hom α β) :
    (ψ.comp φ).mapLp μ p = (ψ.mapLp μ p).comp (φ.mapLp μ p) := by
  rw [mapLp_eq_compLpL, mapLp_eq_compLpL, mapLp_eq_compLpL,
    ContinuousLinearMap.compLpL_comp_compLpL]
  congr 1; ext a; simp

/-- An injective equivariant homomorphism induces an injective map on `Lp A p μ`. -/
theorem mapLp_injective (φ : Hom α β) (hφ : Function.Injective φ) :
    Function.Injective (φ.mapLp μ p) := by
  intro u v huv
  refine Lp.ext ?_
  filter_upwards [φ.coeFn_mapLp u, φ.coeFn_mapLp v, Lp.ext_iff.1 huv] with s hu hv hEq
  exact hφ (hu.symm.trans (hEq.trans hv))

/-- `Hom.mapLp` intertwines the pointwise action `actionLp`. -/
theorem mapLp_actionLp (φ : Hom α β) (r : G) (u : Lp A p μ) :
    φ.mapLp μ p (α.actionLp μ p r u) = β.actionLp μ p r (φ.mapLp μ p u) := by
  refine Lp.ext ?_
  filter_upwards [φ.coeFn_mapLp (α.actionLp μ p r u), α.coeFn_actionLp r u,
    β.coeFn_actionLp r (φ.mapLp μ p u), φ.coeFn_mapLp u] with s h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

/-- `Hom.mapLp` intertwines twisted left translation `translateLp`. -/
theorem mapLp_translateLp [MeasurableMul G] [μ.IsMulLeftInvariant] (φ : Hom α β) (r : G)
    (u : Lp A p μ) :
    φ.mapLp μ p (α.translateLp μ p r u) = β.translateLp μ p r (φ.mapLp μ p u) := by
  refine Lp.ext ?_
  filter_upwards [φ.coeFn_mapLp (α.translateLp μ p r u), α.coeFn_translateLp r u,
    β.coeFn_translateLp r (φ.mapLp μ p u),
    (measurePreserving_mul_left μ r⁻¹).quasiMeasurePreserving.ae (φ.coeFn_mapLp u)]
    with s h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄]

end TauCeti.CStarAction.Hom
