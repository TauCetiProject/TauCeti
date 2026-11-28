/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sard.HalfSpace

import TauCeti.Geometry.Manifold.Corners.Stratum.Manifold
import TauCeti.Geometry.Manifold.ModelWithCorners.LinearEquiv

/-!
# Sard's theorem for manifolds with corners

Let `f : M → N` be a `C^r` map between real manifolds modelled on finite-dimensional spaces, with
`M` Lindelöf, and suppose the model `I` of `M` has range cut out by the nonnegativity of a subset
`S` of coordinates in `EuclideanSpace ℝ ι` — or more generally, is carried onto such a coordinate
region by a continuous linear equivalence `e : E ≃L[ℝ] EuclideanSpace ℝ ι`. Examples include the
quadrant model `𝓡c m`, the half-space model `𝓡∂ m` (treated directly in
`TauCeti.Geometry.Manifold.Sard.HalfSpace` and re-exported here), every finite-dimensional
boundaryless model, and every finite product of these (such as `(𝓡∂ m).prod (𝓡∂ k)` for homotopies
on manifolds with boundary).

The boundaryless Sard theorem (`TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt` in
`TauCeti.Geometry.Manifold.Sard.Basic`) requires `I.Boundaryless` so that coordinate expressions
are `ContDiffAt` rather than only `ContDiffWithinAt`. To reach boundary and corner points in
unequal dimensions, this file decomposes `M` into its finitely many depth strata
`I.depthStratum M k` (`k = 0, …, dim M`). By `TauCeti.Geometry.Manifold.Corners.Stratum.Manifold`,
each depth stratum is a boundaryless Lindelöf `C^r` manifold of dimension `dim M - k ≤ dim M`
smoothly embedded in `M`. By the chain rule, any critical point of `f` lying on a depth stratum is
also a critical point of the restriction of `f` to that stratum. Because `(dim M - k) - dim N + 1 ≤
dim M - dim N + 1 ≤ r`, the boundaryless sharp-regularity Sard theorem applies on every stratum,
and taking the finite union over `k = 0, …, dim M` shows that the critical values of `f` — boundary
and corner critical points included — form a null set (`TauCeti.IsNullSet`) in `N`. Consequently
the regular values of `f` are dense in `N`.

For models linearly equivalent to coordinate regions (including products of half-spaces, quadrants,
and boundaryless models), changing model coordinates via
`ModelWithCorners.transContinuousLinearEquiv` leaves manifold regularity, `ContMDiffAt`, and
`IsRegularPoint` unchanged while preserving the target model `J`.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_range_eq`,
  `ContMDiff.isNullSet_image_criticalPoints_of_range_eq`,
  `ContMDiff.dense_isRegularValue_of_range_eq`: sharp-regularity Sard theorem for coordinate-region
  models `range I = {z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_image_range_eq`,
  `ContMDiff.isNullSet_image_criticalPoints_of_image_range_eq`,
  `ContMDiff.dense_isRegularValue_of_image_range_eq`: the same for any model linearly equivalent to
  a coordinate region.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_of_image_range_eq`,
  `ContMDiff.isNullSet_image_criticalPoints_prod_of_image_range_eq`,
  `ContMDiff.dense_isRegularValue_prod_of_image_range_eq`: product closure of the theorem.
* Specializations for the quadrant `𝓡c m`, products of quadrants `(𝓡c m).prod (𝓡c k)`, products of
  half-spaces `(𝓡∂ m).prod (𝓡∂ k)`, and products of a half-space with a boundaryless model in
  either order (`I₁.prod (𝓡∂ m)` and `(𝓡∂ m).prod I₁`).

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 (p. 129, Sard's theorem for manifolds with boundary).
* Formal foundations in this library: `TauCeti.Geometry.Manifold.Sard.Basic` (boundaryless
  sharp-regularity Sard theorem), `TauCeti.Geometry.Manifold.Sard.HalfSpace` (half-space Sard
  theorem), `TauCeti.Geometry.Manifold.Corners.Stratum.Manifold` (manifold structure on depth
  strata), and `TauCeti.Geometry.Manifold.ModelWithCorners.LinearEquiv` (linear coordinate changes
  on models with corners).
-/

public section

open Function Module Set MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-! ### Coordinate-region models -/

section RangeEq

variable {ι : Type*} [Fintype ι] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H} {S : Set ι}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {r : ℕ∞ω} [IsManifold I r M] [IsManifold J r N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for coordinate-region models with corners.** Let `M` be a Lindelöf `C^r`
manifold modelled on `range I = {z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}` and `N` a `C^r`
manifold modelled on a space `E'`. If `f` is `C^r` at every point of `s` with
`r > card ι - finrank ℝ E'` and `r ≥ 1`, and no point of `s` is regular, then `f '' s` is null in
`N`. This includes boundary and corner critical points at sharp regularity. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_range_eq
    [MeasurableSpace E'] [BorelSpace E']
    (hr : ((Fintype.card ι - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (hI : range I = {z | ∀ i ∈ S, 0 ≤ z i})
    (hf : ∀ x ∈ s, ContMDiffAt I J r f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have hr0 : r ≠ 0 := fun h ↦ by simp [h] at hr
  have : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hr0)
  have hcover : s = ⋃ k : Fin (Fintype.card ι + 1), s ∩ I.depthStratum M k.val := by
    rw [← inter_iUnion]
    have hU : ⋃ k : Fin (Fintype.card ι + 1), I.depthStratum M k.val = univ := by
      refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
      have hle : I.depth x ≤ Fintype.card ι := by
        simpa only [finrank_euclideanSpace] using I.depth_le_finrank x
      exact ⟨⟨I.depth x, Nat.lt_succ_of_le hle⟩, ModelWithCorners.mem_depthStratum.2 rfl⟩
    rw [hU, inter_univ]
  rw [hcover, image_iUnion]
  refine IsNullSet.iUnion fun k ↦ ?_
  let _ := I.depthStratumChartedSpace M hI k.val
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k.val))) r
      ↥(I.depthStratum M k.val) :=
    I.isManifold_depthStratum M hr0 hI k.val
  have : LindelofSpace ↥(I.depthStratum M k.val) := I.lindelofSpace_depthStratum (M := M) k.val
  have hval := (I.isImmersionOfComplement_subtypeVal_depthStratum M hr0 hI k.val).contMDiff
  have himg : f '' (s ∩ I.depthStratum M k.val) =
      (f ∘ (Subtype.val : ↥(I.depthStratum M k.val) → M)) ''
        ((Subtype.val : ↥(I.depthStratum M k.val) → M) ⁻¹' s) := by
    ext y
    simp [and_comm]
  rw [himg]
  have hk_le : ((finrank ℝ (EuclideanSpace ℝ (Fin (Fintype.card ι - k.val))) -
      finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r := by
    refine le_trans ?_ hr
    rw [finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : Fintype.card ι - k.val - finrank ℝ E' + 1 ≤
      Fintype.card ι - finrank ℝ E' + 1)
  refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (Fintype.card ι - k.val)))) hk_le
    (fun p hp ↦ (hf p.val hp).comp p (hval p)) fun p hp hreg ↦ hs p.val hp ?_
  rw [isRegularPoint_iff, mfderiv_comp p ((hf p.val hp).mdifferentiableAt hr0)
    ((hval p).mdifferentiableAt hr0), ContinuousLinearMap.coe_comp] at hreg
  exact isRegularPoint_iff.2 hreg.of_comp

/-- **Sard's theorem for coordinate-region models with corners.** The critical values of a `C^r`
map from a Lindelöf manifold modelled on `{z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}` form a null
set whenever `r > card ι - finrank ℝ E'` and `r ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_range_eq
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ContMDiff I J r f)
    (hr : ((Fintype.card ι - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (hI : range I = {z | ∀ i ∈ S, 0 ≤ z i}) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_range_eq hr hI
    (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- The regular values of a `C^r` map from a Lindelöf manifold modelled on
`{z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}` are dense whenever `r > card ι - finrank ℝ E'` and
`r ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_range_eq
    (hf : ContMDiff I J r f)
    (hr : ((Fintype.card ι - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (hI : range I = {z | ∀ i ∈ S, 0 ≤ z i}) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_range_eq hr hI).dense_compl

end RangeEq

/-! ### Models linearly equivalent to coordinate regions -/

section ImageRangeEq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {ι : Type*} [Finite ι] {S : Set ι}
  {r : ℕ∞ω} [IsManifold I r M] [IsManifold J r N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for models linearly equivalent to coordinate regions.** If a continuous linear
equivalence `e : E ≃L[ℝ] EuclideanSpace ℝ ι` carries `range I` onto `{z | ∀ i ∈ S, 0 ≤ z i}`, then
for any set `s` of critical points where `f` is `C^r` (`r > dim E - dim E'`, `r ≥ 1`), the image
`f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_image_range_eq
    [MeasurableSpace E'] [BorelSpace E']
    (hr : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i})
    (hf : ∀ x ∈ s, ContMDiffAt I J r f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hdim : finrank ℝ E = Fintype.card ι := by
    rw [e.toLinearEquiv.finrank_eq, finrank_euclideanSpace]
  have hr' : ((Fintype.card ι - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r := by rwa [← hdim]
  refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_range_eq
    (I := I.transContinuousLinearEquiv e) hr'
    (by rwa [I.transContinuousLinearEquiv_range])
    (fun x hx ↦ (e.contMDiffAt_transContinuousLinearEquiv_left).2 (hf x hx))
    fun x hx hreg ↦ hs x hx ?_
  -- Linear coordinate change conjugates `mfderiv` by continuous linear equivalences on both sides.
  rw [isRegularPoint_iff] at hreg ⊢
  have hsurj : Surjective (mfderiv (I.transContinuousLinearEquiv e)
      (J.transContinuousLinearEquiv (.refl ℝ E')) f x) := by
    rwa [J.transContinuousLinearEquiv_refl]
  rw [I.mfderiv_transContinuousLinearEquiv J e (.refl ℝ E') f x] at hsurj
  intro w
  let α := ((tangentSpaceCastModel J (f x)).trans (.refl ℝ E')).trans
    (tangentSpaceCastModel (J.transContinuousLinearEquiv (.refl ℝ E')) (f x)).symm
  let β := ((tangentSpaceCastModel (I.transContinuousLinearEquiv e) x).trans e.symm).trans
    (tangentSpaceCastModel I x).symm
  obtain ⟨u, hu⟩ := hsurj (α w)
  exact ⟨β u, α.injective (by simpa [α, β] using hu)⟩

/-- **Sard's theorem** for a `C^r` map out of a Lindelöf manifold whose model is linearly
equivalent to `{z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_image_range_eq
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ContMDiff I J r f)
    (hr : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i}) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_image_range_eq hr e hI
    (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- Density of regular values for a `C^r` map out of a Lindelöf manifold whose model is linearly
equivalent to `{z : EuclideanSpace ℝ ι | ∀ i ∈ S, 0 ≤ z i}`. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_image_range_eq
    (hf : ContMDiff I J r f)
    (hr : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (e : E ≃L[ℝ] EuclideanSpace ℝ ι)
    (hI : e '' range I = {z | ∀ i ∈ S, 0 ≤ z i}) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_image_range_eq hr e hI).dense_compl

end ImageRangeEq

/-! ### Product models -/

section Prod

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd H₁ H₂) M] [LindelofSpace M]
  {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂] {S₁ : Set ι₁} {S₂ : Set ι₂}
  {r : ℕ∞ω} [IsManifold (I₁.prod I₂) r M] [IsManifold J r N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for products of coordinate-region models.** If `I₁` and `I₂` have ranges
linearly equivalent to coordinate nonnegativity regions, then the critical values of a `C^r` map
from a Lindelöf manifold modelled on `I₁.prod I₂` are null whenever
`r > dim E₁ + dim E₂ - dim E'` and `r ≥ 1`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_of_image_range_eq
    [MeasurableSpace E'] [BorelSpace E']
    (hr : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (e₁ : E₁ ≃L[ℝ] EuclideanSpace ℝ ι₁) (e₂ : E₂ ≃L[ℝ] EuclideanSpace ℝ ι₂)
    (h₁ : e₁ '' range I₁ = {z | ∀ i ∈ S₁, 0 ≤ z i})
    (h₂ : e₂ '' range I₂ = {z | ∀ j ∈ S₂, 0 ≤ z j})
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod I₂) J r f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod I₂) J f x) :
    IsNullSet J (f '' s) := by
  let _ : Fintype ι₁ := Fintype.ofFinite ι₁
  let _ : Fintype ι₂ := Fintype.ofFinite ι₂
  have : FiniteDimensional ℝ E₁ := e₁.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E₂ := e₂.symm.toLinearEquiv.finiteDimensional
  exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_image_range_eq
    (I := I₁.prod I₂) (by simpa only [finrank_prod] using hr)
    ((e₁.prodCongr e₂).trans EuclideanSpace.sumEquivProd.symm)
    (ModelWithCorners.image_range_prod_eq I₁ I₂ h₁ h₂) hf hs

/-- The critical values of a `C^r` map out of a Lindelöf manifold modelled on a product of
coordinate-region models form a null set at sharp regularity. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_prod_of_image_range_eq
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ContMDiff (I₁.prod I₂) J r f)
    (hr : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (e₁ : E₁ ≃L[ℝ] EuclideanSpace ℝ ι₁) (e₂ : E₂ ≃L[ℝ] EuclideanSpace ℝ ι₂)
    (h₁ : e₁ '' range I₁ = {z | ∀ i ∈ S₁, 0 ≤ z i})
    (h₂ : e₂ '' range I₂ = {z | ∀ j ∈ S₂, 0 ≤ z j}) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (I₁.prod I₂) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_of_image_range_eq hr e₁ e₂ h₁ h₂
    (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- The regular values of a `C^r` map out of a Lindelöf manifold modelled on a product of
coordinate-region models are dense at sharp regularity. -/
theorem _root_.ContMDiff.dense_isRegularValue_prod_of_image_range_eq
    (hf : ContMDiff (I₁.prod I₂) J r f)
    (hr : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (e₁ : E₁ ≃L[ℝ] EuclideanSpace ℝ ι₁) (e₂ : E₂ ≃L[ℝ] EuclideanSpace ℝ ι₂)
    (h₁ : e₁ '' range I₁ = {z | ∀ i ∈ S₁, 0 ≤ z i})
    (h₂ : e₂ '' range I₂ = {z | ∀ j ∈ S₂, 0 ≤ z j}) :
    Dense {y | IsRegularValue (I₁.prod I₂) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_prod_of_image_range_eq hr e₁ e₂ h₁ h₂).dense_compl

end Prod

/-! ### Quadrant models -/

section Quadrant

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant m) M]
  [LindelofSpace M] {r : ℕ∞ω} [IsManifold (𝓡c m) r M] [IsManifold J r N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with corners modelled on the quadrant `𝓡c m`.** If `f` is `C^r`
at every point of a set `s` of critical points with `r > m - finrank ℝ E'` and `r ≥ 1`, then
`f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant
    [MeasurableSpace E'] [BorelSpace E']
    (hr : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡c m) J r f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡c m) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_range_eq
    (by simpa only [Fintype.card_fin] using hr)
    (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq m) hf hs

/-- **Sard's theorem for the quadrant model `𝓡c m`.** The critical values of a `C^r` map form a
null set whenever `r > m - finrank ℝ E'` and `r ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ContMDiff (𝓡c m) J r f)
    (hr : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡c m) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant hr (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- The regular values of a `C^r` map out of a Lindelöf manifold modelled on `𝓡c m` are dense
whenever `r > m - finrank ℝ E'` and `r ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant
    (hf : ContMDiff (𝓡c m) J r f)
    (hr : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    Dense {y | IsRegularValue (𝓡c m) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant hr).dense_compl

end Quadrant

section QuadrantProd

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ModelProd (EuclideanQuadrant m) (EuclideanQuadrant k)) M] [LindelofSpace M]
  {r : ℕ∞ω} [IsManifold ((𝓡c m).prod (𝓡c k)) r M] [IsManifold J r N] {f : M → N}

/-- **Sard's theorem for products of quadrants `(𝓡c m).prod (𝓡c k)`.** -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant_prod
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ContMDiff ((𝓡c m).prod (𝓡c k)) J r f)
    (hr : ((m + k - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡c m).prod (𝓡c k)) J f x}) :=
  hf.isNullSet_image_criticalPoints_prod_of_image_range_eq
    (by simpa only [finrank_euclideanSpace_fin] using hr)
    (.refl ℝ _) (.refl ℝ _)
    (by
      rw [ContinuousLinearEquiv.coe_refl', image_id]
      exact ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq m)
    (by
      rw [ContinuousLinearEquiv.coe_refl', image_id]
      exact ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq k)

/-- The regular values of a `C^r` map out of a Lindelöf manifold modelled on
`(𝓡c m).prod (𝓡c k)` are dense at sharp regularity. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant_prod
    (hf : ContMDiff ((𝓡c m).prod (𝓡c k)) J r f)
    (hr : ((m + k - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    Dense {y | IsRegularValue ((𝓡c m).prod (𝓡c k)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant_prod hr).dense_compl

end QuadrantProd

/-! ### Products involving half-space models -/

section HalfSpaceProd

variable {m k : ℕ} [NeZero m] [NeZero k] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ModelProd (EuclideanHalfSpace m) (EuclideanHalfSpace k)) M] [LindelofSpace M]
  {r : ℕ∞ω} [IsManifold ((𝓡∂ m).prod (𝓡∂ k)) r M] [IsManifold J r N] {f : M → N}

/-- **Sard's theorem for products of half-space manifolds `(𝓡∂ m).prod (𝓡∂ k)`** (for instance
`M × [0, 1]` where `M` has boundary). -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ContMDiff ((𝓡∂ m).prod (𝓡∂ k)) J r f)
    (hr : ((m + k - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ m).prod (𝓡∂ k)) J f x}) :=
  hf.isNullSet_image_criticalPoints_prod_of_image_range_eq
    (by simpa only [finrank_euclideanSpace_fin] using hr)
    (.refl ℝ _) (.refl ℝ _)
    (by
      rw [ContinuousLinearEquiv.coe_refl', image_id]
      exact ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq m)
    (by
      rw [ContinuousLinearEquiv.coe_refl', image_id]
      exact ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq k)

/-- The regular values of a `C^r` map out of a Lindelöf manifold modelled on
`(𝓡∂ m).prod (𝓡∂ k)` are dense at sharp regularity. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace_prod
    (hf : ContMDiff ((𝓡∂ m).prod (𝓡∂ k)) J r f)
    (hr : ((m + k - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    Dense {y | IsRegularValue ((𝓡∂ m).prod (𝓡∂ k)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace_prod hr).dense_compl

end HalfSpaceProd

section BoundarylessProdHalfSpace

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  {m : ℕ} [NeZero m] {r : ℕ∞ω} [IsManifold J r N]

/-- **Sard's theorem for the product of a boundaryless model with a half-space `I₁.prod (𝓡∂ m)`**
(for instance `M × [0, 1]` with `M` boundaryless). -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_boundaryless_prod_halfSpace
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd H₁ (EuclideanHalfSpace m)) M]
    [LindelofSpace M] [IsManifold (I₁.prod (𝓡∂ m)) r M]
    [MeasurableSpace E'] [BorelSpace E'] {f : M → N}
    (hf : ContMDiff (I₁.prod (𝓡∂ m)) J r f)
    (hr : ((finrank ℝ E₁ + m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (I₁.prod (𝓡∂ m)) J f x}) := by
  obtain ⟨e₁, he₁⟩ := I₁.exists_equiv_image_range_eq_of_boundaryless
  exact hf.isNullSet_image_criticalPoints_prod_of_image_range_eq
    (by simpa only [finrank_euclideanSpace_fin] using hr) e₁ (.refl ℝ _) he₁
    (by
      rw [ContinuousLinearEquiv.coe_refl', image_id]
      exact ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq m)

/-- The regular values of a `C^r` map out of a Lindelöf manifold modelled on `I₁.prod (𝓡∂ m)` with
`I₁` boundaryless are dense at sharp regularity. -/
theorem _root_.ContMDiff.dense_isRegularValue_boundaryless_prod_halfSpace
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd H₁ (EuclideanHalfSpace m)) M]
    [LindelofSpace M] [IsManifold (I₁.prod (𝓡∂ m)) r M] {f : M → N}
    (hf : ContMDiff (I₁.prod (𝓡∂ m)) J r f)
    (hr : ((finrank ℝ E₁ + m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    Dense {y | IsRegularValue (I₁.prod (𝓡∂ m)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_boundaryless_prod_halfSpace hr).dense_compl

/-- **Sard's theorem for the product of a half-space with a boundaryless model `(𝓡∂ m).prod I₁`**
(for instance `[0, 1] × M` with `M` boundaryless). -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod_boundaryless
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd (EuclideanHalfSpace m) H₁) M]
    [LindelofSpace M] [IsManifold ((𝓡∂ m).prod I₁) r M]
    [MeasurableSpace E'] [BorelSpace E'] {f : M → N}
    (hf : ContMDiff ((𝓡∂ m).prod I₁) J r f)
    (hr : ((m + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ m).prod I₁) J f x}) := by
  obtain ⟨e₁, he₁⟩ := I₁.exists_equiv_image_range_eq_of_boundaryless
  exact hf.isNullSet_image_criticalPoints_prod_of_image_range_eq
    (by simpa only [finrank_euclideanSpace_fin] using hr) (.refl ℝ _) e₁
    (by
      rw [ContinuousLinearEquiv.coe_refl', image_id]
      exact ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq m) he₁

/-- The regular values of a `C^r` map out of a Lindelöf manifold modelled on `(𝓡∂ m).prod I₁` with
`I₁` boundaryless are dense at sharp regularity. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace_prod_boundaryless
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd (EuclideanHalfSpace m) H₁) M]
    [LindelofSpace M] [IsManifold ((𝓡∂ m).prod I₁) r M] {f : M → N}
    (hf : ContMDiff ((𝓡∂ m).prod I₁) J r f)
    (hr : ((m + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ r) :
    Dense {y | IsRegularValue ((𝓡∂ m).prod I₁) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace_prod_boundaryless hr).dense_compl

end BoundarylessProdHalfSpace

end TauCeti
