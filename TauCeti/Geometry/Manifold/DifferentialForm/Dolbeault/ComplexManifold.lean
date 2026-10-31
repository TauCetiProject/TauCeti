/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Basic
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# The Dolbeault operators on a complex manifold

Let `M` be a complex manifold modelled on `𝓘(ℂ, E)`, regarded as a real manifold modelled on
`𝓘(ℝ, E)` with the same charts, and let `J = ofComplexManifold E M` be its almost complex
structure, multiplication by `i` on every tangent space. On an arbitrary almost complex manifold
the exterior derivative of a form of type `(p,q)` has components of the four types `(p+2,q-1)`,
`(p+1,q)`, `(p,q+1)` and `(p-1,q+2)`. On a complex manifold the outer two vanish, so that
`d = ∂ + ∂bar` on complex-valued smooth forms of every degree. Taking the components of
`d² = 0` of the three possible types then gives

* `∂² = 0`,
* `∂bar² = 0`,
* `∂ ∂bar + ∂bar ∂ = 0`,

so that `∂bar` is the differential of the Dolbeault complexes of a complex manifold.

The vanishing is checked in the holomorphic chart at each point. There the tangent coordinates are
related by the derivatives of holomorphic coordinate changes, which are complex linear, so the
coordinate expression of a form of type `(p,q)` has type `(p,q)` for the constant structure given
by multiplication by `i`, and so do its derivatives. The pointwise statement
`ContinuousAlternatingMap.typeProjection_alternatizeUncurryFin_eq_zero_of_forall_isOfType` then
shows that the alternation of the derivative, the exterior derivative, has components of the types
`(p+1,q)` and `(p,q+1)` only. No finite-dimensionality of `E` is needed.

## Main declarations

* `TauCeti.SmoothForm.IsOfType.typeProjection_mextDerivₗ_eq_zero_ofComplexManifold`: on a complex
  manifold, the exterior derivative of a form of type `(p,q)` has components of the types
  `(p+1,q)` and `(p,q+1)` only.
* `TauCeti.SmoothAlmostComplexStructure.mextDerivₗ_eq_del_add_delBar_ofComplexManifold`:
  `d = ∂ + ∂bar` on a complex manifold.
* `TauCeti.SmoothAlmostComplexStructure.del_del_ofComplexManifold`,
  `TauCeti.SmoothAlmostComplexStructure.delBar_delBar_ofComplexManifold`,
  `TauCeti.SmoothAlmostComplexStructure.del_delBar_add_delBar_del_ofComplexManifold`:
  `∂² = 0`, `∂bar² = 0` and `∂ ∂bar + ∂bar ∂ = 0` on a complex manifold.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.3 and 2.6.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

open SmoothAlmostComplexStructure

/-- The almost complex structure of a complex manifold is multiplication by `i` on every tangent
space, as an endomorphism. -/
private theorem toEndomorphism_ofComplexManifold (x : M) :
    (ofComplexManifold E M).toEndomorphism x =
      (Complex.I • ContinuousLinearMap.id ℝ E :
        TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x) :=
  ContinuousLinearMap.ext fun v ↦ ofComplexManifold_apply (E := E) x v

/-- The derivative of the inverse of the chart at `x` commutes with multiplication by `i`: it is
the tangent coordinate change between two holomorphic charts, which is complex linear. -/
private theorem mfderivWithin_extChartAt_symm_I_smul (x : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target) (w : E) :
    mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x).symm (range 𝓘(ℝ, E)) z
        ((Complex.I • ContinuousLinearMap.id ℝ E) w) =
      (Complex.I • ContinuousLinearMap.id ℝ E)
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x).symm (range 𝓘(ℝ, E)) z w) := by
  have hy : (extChartAt 𝓘(ℝ, E) x).symm z ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) x).map_target hz
  rw [← (extChartAt 𝓘(ℝ, E) x).right_inv hz, ← TangentBundle.symmL_trivializationAt hy,
    TangentBundle.symmL_trivializationAt_eq_core hy]
  exact tangentCoordChange_smul ℝ (𝕜' := ℂ) ⟨hy, mem_chart_source E _⟩ Complex.I w

namespace SmoothForm

variable {φ : SmoothForm 𝓘(ℝ, E) M F k} {p q P Q : ℕ}

/-- In the chart at `x`, the coordinate expression of a form of type `(p,q)` has type `(p,q)` for
multiplication by `i`. -/
private theorem IsOfType.inChartAt_isOfType (hφ : φ.IsOfType (ofComplexManifold E M) p q) (x : M)
    {z : E} (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target) :
    (RoughForm.inChartAt φ.1 x z).IsOfType (Complex.I • ContinuousLinearMap.id ℝ E) p q := by
  have h := hφ.apply ((extChartAt 𝓘(ℝ, E) x).symm z)
  rw [toEndomorphism_ofComplexManifold] at h
  have heq : RoughForm.inChartAt φ.1 x z =
      (φ.1 ((extChartAt 𝓘(ℝ, E) x).symm z)).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x).symm (range 𝓘(ℝ, E)) z) := by
    ext v
    rw [RoughForm.inChartAt_apply]
    exact (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).symm
  rw [heq]
  exact h.compContinuousLinearMap fun w ↦ (mfderivWithin_extChartAt_symm_I_smul x hz w).symm

/-- **`d` has two bidegrees on a complex manifold.** The exterior derivative of a smooth form of
type `(p,q)` on a complex manifold has no component of type `(P,Q)` other than `(p+1,q)` and
`(p,q+1)`. -/
theorem IsOfType.typeProjection_mextDerivₗ_eq_zero_ofComplexManifold
    (hφ : φ.IsOfType (ofComplexManifold E M) p q) (h₁ : (P, Q) ≠ (p + 1, q))
    (h₂ : (P, Q) ≠ (p, q + 1)) :
    (ofComplexManifold E M).typeProjection P Q (mextDerivₗ 𝓘(ℝ, E) k φ) = 0 :=
  Subtype.ext <| funext fun x ↦ by
    -- In the chart at `x`, the almost complex structure is the constant structure `L`, and the
    -- coordinate expression `f` of `φ` satisfies the type equation `D_L f = c • f` for `L`.
    -- Differentiating it, every derivative of `f` has type `(p,q)` for `L`.
    set L : E →L[ℝ] E := Complex.I • ContinuousLinearMap.id ℝ E
    set c : ℂ := ((p : ℂ) - q) * Complex.I
    set f := RoughForm.inChartAt φ.1 x
    set z₀ := extChartAt 𝓘(ℝ, E) x x
    have hL (v : E) : L (L v) = -v := by
      simp [L, smul_smul]
    have hd : HasFDerivWithinAt f (fderivWithin ℝ f (range 𝓘(ℝ, E)) z₀) (range 𝓘(ℝ, E)) z₀ :=
      ((φ.isSmoothForm.contDiffWithinAt_inChartAt_self x).differentiableWithinAt
        (by simp)).hasFDerivWithinAt
    let T := (ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM F
      (ContinuousLinearMap.id ℝ E) (ι := Fin k)).flip L
    have hT (β : E [⋀^Fin k]→L[ℝ] F) : T β = L.alternatingDerivation β := by
      simp only [T, ContinuousLinearMap.flip_apply,
        ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM_apply,
        ← ContinuousLinearMap.alternatingDerivation_eq_fderivCompContinuousLinearMap]
    have heq : (fun z ↦ T (f z)) =ᶠ[𝓝[range 𝓘(ℝ, E)] z₀] fun z ↦ c • f z := by
      filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
      rw [hT]
      exact (hφ.inChartAt_isOfType x hz).alternatingDerivation_eq
    have hD := (𝓘(ℝ, E).uniqueDiffOn.uniqueDiffWithinAt (mem_range_self _)).eq
      ((T.hasFDerivAt.comp_hasFDerivWithinAt z₀ hd).congr_of_eventuallyEq heq.symm
        (heq.symm.eq_of_nhdsWithin (mem_range_self _))) (hd.const_smul c)
    have hη (v : E) : (fderivWithin ℝ f (range 𝓘(ℝ, E)) z₀ v).IsOfType L p q := by
      refine ContinuousAlternatingMap.isOfType_iff.2 ⟨hφ.add_eq, ?_⟩
      rw [← hT]
      exact congrArg (fun A ↦ A v) hD
    simp only [coe_typeProjection, mextDerivₗ_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    rw [mextDeriv_def, extDerivWithin, toEndomorphism_ofComplexManifold]
    exact ContinuousAlternatingMap.typeProjection_alternatizeUncurryFin_eq_zero_of_forall_isOfType
      (J := L) hL hη h₁ h₂

/-- On a smooth form of type `(p,q)` on a complex manifold, `d = ∂ + ∂bar`. -/
private theorem IsOfType.mextDerivₗ_eq_del_add_delBar_ofComplexManifold
    (hφ : φ.IsOfType (ofComplexManifold E M) p q) :
    mextDerivₗ 𝓘(ℝ, E) k φ = (ofComplexManifold E M).del φ + (ofComplexManifold E M).delBar φ := by
  rw [hφ.mextDerivₗ_eq_add_del_add_delBar_add,
    hφ.typeProjection_mextDerivₗ_eq_zero_ofComplexManifold (by grind) (by grind),
    hφ.typeProjection_mextDerivₗ_eq_zero_ofComplexManifold (by grind) (by grind)]
  abel

end SmoothForm

namespace SmoothAlmostComplexStructure

/-- **`d = ∂ + ∂bar` on a complex manifold.** On the complex-valued smooth forms of every degree
on a complex manifold, the exterior derivative is the sum of `∂` and `∂bar`. -/
theorem mextDerivₗ_eq_del_add_delBar_ofComplexManifold (φ : SmoothForm 𝓘(ℝ, E) M F k) :
    mextDerivₗ 𝓘(ℝ, E) k φ = (ofComplexManifold E M).del φ + (ofComplexManifold E M).delBar φ := by
  rw [← (ofComplexManifold E M).sum_typeProjection φ, map_sum, map_sum, map_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun pq h ↦
    ((ofComplexManifold E M).isOfType_typeProjection (Finset.mem_antidiagonal.1 h)
      φ).mextDerivₗ_eq_del_add_delBar_ofComplexManifold

end SmoothAlmostComplexStructure

namespace SmoothForm

variable {φ : SmoothForm 𝓘(ℝ, E) M F k} {p q : ℕ}

/-- On a smooth form `φ` of type `(p,q)` on a complex manifold, the components of `d²φ = 0` of
the types `(p+2,q)`, `(p+1,q+1)` and `(p,q+2)` are `∂∂φ`, `∂ ∂bar φ + ∂bar ∂φ` and
`∂bar ∂bar φ`, so these vanish. -/
private theorem IsOfType.del_del_and_delBar_delBar_ofComplexManifold
    (hφ : φ.IsOfType (ofComplexManifold E M) p q) :
    (ofComplexManifold E M).del ((ofComplexManifold E M).del φ) = 0 ∧
      (ofComplexManifold E M).del ((ofComplexManifold E M).delBar φ) +
        (ofComplexManifold E M).delBar ((ofComplexManifold E M).del φ) = 0 ∧
      (ofComplexManifold E M).delBar ((ofComplexManifold E M).delBar φ) = 0 := by
  set J := ofComplexManifold E M
  have h : J.del (J.del φ) + J.delBar (J.del φ) + (J.del (J.delBar φ) + J.delBar (J.delBar φ)) =
      0 := by
    rw [← SmoothAlmostComplexStructure.mextDerivₗ_eq_del_add_delBar_ofComplexManifold,
      ← SmoothAlmostComplexStructure.mextDerivₗ_eq_del_add_delBar_ofComplexManifold, ← map_add,
      ← SmoothAlmostComplexStructure.mextDerivₗ_eq_del_add_delBar_ofComplexManifold,
      ← LinearMap.comp_apply, mextDerivₗ_comp_mextDerivₗ, LinearMap.zero_apply]
  have h₂₀ := congrArg (J.typeProjection (p + 1 + 1) q) h
  have h₀₂ := congrArg (J.typeProjection p (q + 1 + 1)) h
  simp only [map_add, map_zero, hφ.del.del.typeProjection_self,
    hφ.delBar.delBar.typeProjection_self,
    hφ.del.delBar.typeProjection_of_ne (p' := p + 1 + 1) (q' := q) (by grind),
    hφ.delBar.del.typeProjection_of_ne (p' := p + 1 + 1) (q' := q) (by grind),
    hφ.delBar.delBar.typeProjection_of_ne (p' := p + 1 + 1) (q' := q) (by grind),
    hφ.del.del.typeProjection_of_ne (p' := p) (q' := q + 1 + 1) (by grind),
    hφ.del.delBar.typeProjection_of_ne (p' := p) (q' := q + 1 + 1) (by grind),
    hφ.delBar.del.typeProjection_of_ne (p' := p) (q' := q + 1 + 1) (by grind),
    add_zero, zero_add] at h₂₀ h₀₂
  refine ⟨h₂₀, ?_, h₀₂⟩
  rw [h₂₀, h₀₂, zero_add, add_zero] at h
  exact (add_comm _ _).trans h

end SmoothForm

namespace SmoothAlmostComplexStructure

/-- **`∂² = 0` on a complex manifold.** -/
@[simp]
theorem del_del_ofComplexManifold (φ : SmoothForm 𝓘(ℝ, E) M F k) :
    (ofComplexManifold E M).del ((ofComplexManifold E M).del φ) = 0 := by
  rw [← (ofComplexManifold E M).sum_typeProjection φ, map_sum, map_sum]
  exact Finset.sum_eq_zero fun pq h ↦
    ((ofComplexManifold E M).isOfType_typeProjection (Finset.mem_antidiagonal.1 h)
      φ).del_del_and_delBar_delBar_ofComplexManifold.1

/-- **`∂bar² = 0` on a complex manifold.** This is the identity making the forms of types `(p,•)`
with the operator `∂bar` the Dolbeault complex. -/
@[simp]
theorem delBar_delBar_ofComplexManifold (φ : SmoothForm 𝓘(ℝ, E) M F k) :
    (ofComplexManifold E M).delBar ((ofComplexManifold E M).delBar φ) = 0 := by
  rw [← (ofComplexManifold E M).sum_typeProjection φ, map_sum, map_sum]
  exact Finset.sum_eq_zero fun pq h ↦
    ((ofComplexManifold E M).isOfType_typeProjection (Finset.mem_antidiagonal.1 h)
      φ).del_del_and_delBar_delBar_ofComplexManifold.2.2

/-- **`∂` and `∂bar` anticommute on a complex manifold**: `∂ ∂bar φ + ∂bar ∂φ = 0`. -/
theorem del_delBar_add_delBar_del_ofComplexManifold (φ : SmoothForm 𝓘(ℝ, E) M F k) :
    (ofComplexManifold E M).del ((ofComplexManifold E M).delBar φ) +
      (ofComplexManifold E M).delBar ((ofComplexManifold E M).del φ) = 0 := by
  rw [← (ofComplexManifold E M).sum_typeProjection φ, map_sum, map_sum, map_sum, map_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun pq h ↦
    ((ofComplexManifold E M).isOfType_typeProjection (Finset.mem_antidiagonal.1 h)
      φ).del_del_and_delBar_delBar_ofComplexManifold.2.1

end SmoothAlmostComplexStructure

end TauCeti
