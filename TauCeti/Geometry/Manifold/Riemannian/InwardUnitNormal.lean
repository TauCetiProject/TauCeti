/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.OutwardUnitNormal

/-!
# The inward unit normal and the sign test

Let `M` be a manifold modelled on the half-space `𝓡∂ (n + 1)` whose tangent spaces carry a
Riemannian metric. The **inward unit normal** at a boundary point `q` is
`ν_in(q) := -ν_out(q)`, for the outward unit normal `TauCeti.outwardUnitNormal`. The tangent space
`T_q∂M` of the boundary is the orthogonal complement of `ν_in(q)`
(`TauCeti.boundaryTangentSpace_eq_orthogonal_span_inwardUnitNormal`), so every `v ∈ T_qM` splits as
`v = vᵀ + ⟪v, ν_in⟫ ν_in` with `vᵀ ∈ T_q∂M`. The inner product with `ν_in` is the **sign test**: `v`
is inward exactly when `⟪v, ν_in⟫ > 0`, tangent exactly when it is zero and outward exactly when it
is negative. In particular `ν_in(q)` is the unique inward unit vector orthogonal to `T_q∂M`.

A function `f` with a local minimum and nonzero differential at a boundary point `q`, such as a
boundary defining function `ρ`, has gradient `grad f(q) = |df_q| ν_in(q)`, so `df_q(ν_in) = |df_q|`
(`TauCeti.IsBoundaryDefiningFunctionOn.mgradient_eq_norm_smul_inwardUnitNormal`). Applied to the
normal coordinate `x⁰` of any chart of the maximal atlas, this is the chart formula
`ν_in = grad x⁰ / |grad x⁰|` (`TauCeti.inwardUnitNormal_eq_normalize_mgradient`). An isometry of
Riemannian manifolds with boundary carries outward unit normals to outward unit normals
(`TauCeti.RiemannianIsometry.mfderiv_outwardUnitNormal`).

## Main declarations

* `TauCeti.inwardUnitNormal`: the inward unit normal at a boundary point.
* `TauCeti.eq_inwardUnitNormal_iff`: it is the unique inward unit vector orthogonal to `T_q∂M`.
* `TauCeti.boundaryTangentSpace_eq_orthogonal_span_inwardUnitNormal` and
  `TauCeti.sub_inner_smul_inwardUnitNormal_mem_boundaryTangentSpace`: the tangential
  decomposition.
* `TauCeti.isOutwardPointing_neg_iff_inner_inwardUnitNormal_pos`,
  `TauCeti.mem_boundaryTangentSpace_iff_inner_inwardUnitNormal_eq_zero` and
  `TauCeti.isOutwardPointing_iff_inner_inwardUnitNormal_neg`: the sign test.
* `TauCeti.IsBoundaryDefiningFunctionOn.mgradient_eq_norm_smul_inwardUnitNormal` and
  `TauCeti.IsBoundaryDefiningFunctionOn.mvfderiv_inwardUnitNormal`: the gradient formula for
  boundary defining functions.
* `TauCeti.inwardUnitNormal_eq_normalize_mgradient`: the chart formula in any chart of the maximal
  atlas.
* `TauCeti.RiemannianIsometry.mfderiv_outwardUnitNormal` and
  `TauCeti.RiemannianIsometry.mfderiv_inwardUnitNormal`: naturality under isometries.

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Section 3.1 (the inward unit normal `ν`).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

noncomputable section

open Bundle Set Filter Function
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

variable [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-! ### The inward unit normal -/

/-- The **inward unit normal** at a boundary point `q`: minus the outward unit normal, the unit
vector of `T_q M` orthogonal to the tangent space of the boundary and pointing inward. -/
def inwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) : TangentSpace (𝓡∂ (n + 1)) (q : M) :=
  -outwardUnitNormal q

/-- The inward unit normal is minus the outward unit normal. -/
theorem inwardUnitNormal_def (q : (𝓡∂ (n + 1)).boundary M) :
    inwardUnitNormal q = -outwardUnitNormal q :=
  (rfl)

/-- The outward unit normal is minus the inward unit normal. -/
theorem neg_inwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) :
    -inwardUnitNormal q = outwardUnitNormal q := by
  rw [inwardUnitNormal_def, neg_neg]

/-- The inward unit normal has norm one. -/
@[simp]
theorem norm_inwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) : ‖inwardUnitNormal q‖ = 1 := by
  rw [inwardUnitNormal_def, norm_neg, norm_outwardUnitNormal]

/-- The inward unit normal points inward: its negative points outward. -/
theorem isOutwardPointing_neg_inwardUnitNormal (q : (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing (q : M) (-inwardUnitNormal q) := by
  rw [neg_inwardUnitNormal]
  exact isOutwardPointing_outwardUnitNormal q

/-- The outward unit normal is orthogonal to the tangent space of the boundary. -/
theorem inner_outwardUnitNormal_of_mem_boundaryTangentSpace {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} (hv : v ∈ boundaryTangentSpace q) :
    ⟪outwardUnitNormal q, v⟫_ℝ = 0 := by
  rw [boundaryTangentSpace_def, LinearMap.mem_range] at hv
  obtain ⟨w, rfl⟩ := hv
  exact inner_outwardUnitNormal_mfderiv_subtypeVal q w

/-- The inward unit normal is orthogonal to the tangent space of the boundary. -/
theorem inner_inwardUnitNormal_of_mem_boundaryTangentSpace {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} (hv : v ∈ boundaryTangentSpace q) :
    ⟪inwardUnitNormal q, v⟫_ℝ = 0 := by
  rw [inwardUnitNormal_def, inner_neg_left, inner_outwardUnitNormal_of_mem_boundaryTangentSpace hv,
    neg_zero]

/-! ### The tangential decomposition -/

/-- The tangent space of the boundary is the orthogonal complement of the inward unit normal. -/
theorem boundaryTangentSpace_eq_orthogonal_span_inwardUnitNormal
    (q : (𝓡∂ (n + 1)).boundary M) :
    boundaryTangentSpace q = (ℝ ∙ inwardUnitNormal q)ᗮ := by
  have : FiniteDimensional ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (n + 1))))
  have hneg : (ℝ ∙ -outwardUnitNormal q)ᗮ = (ℝ ∙ outwardUnitNormal q)ᗮ := by
    ext w
    simp only [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_neg_left, neg_eq_zero]
  rw [inwardUnitNormal_def, hneg, ← orthogonalNormalSpace_subtypeVal_boundary_eq_span,
    orthogonalNormalSpace_def, Submodule.orthogonal_orthogonal]
  exact boundaryTangentSpace_def q

/-- **Tangential decomposition.** Every tangent vector `v` at a boundary point splits as
`v = vᵀ + ⟪v, ν_in⟫ ν_in` with `vᵀ` tangent to the boundary. -/
theorem sub_inner_smul_inwardUnitNormal_mem_boundaryTangentSpace
    (q : (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    v - ⟪v, inwardUnitNormal q⟫_ℝ • inwardUnitNormal q ∈ boundaryTangentSpace q := by
  rw [boundaryTangentSpace_eq_orthogonal_span_inwardUnitNormal,
    Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_inwardUnitNormal, real_inner_comm]
  ring

/-- The normal coordinate, in the preferred chart, of a tangent vector at a boundary point is its
inner product with the inward unit normal times the positive normal coordinate of `ν_in`. -/
private theorem proj_eq_inner_mul (q : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    EuclideanSpace.proj (0 : Fin (n + 1)) v = ⟪v, inwardUnitNormal q⟫_ℝ *
      EuclideanSpace.proj (0 : Fin (n + 1)) (inwardUnitNormal q) := by
  -- `TangentSpace` is a type synonym of the model space, so `proj 0` is applied as a linear form
  -- on the tangent space.
  let p₀ : Module.Dual ℝ (TangentSpace (𝓡∂ (n + 1)) (q : M)) := EuclideanSpace.projₗ 0
  have h : p₀ (v - ⟪v, inwardUnitNormal q⟫_ℝ • inwardUnitNormal q) = 0 :=
    mem_boundaryTangentSpace_iff_proj.mp
      (sub_inner_smul_inwardUnitNormal_mem_boundaryTangentSpace q v)
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
  exact h

/-- The inward unit normal has positive normal coordinate in the preferred chart. -/
private theorem proj_inwardUnitNormal_pos (q : (𝓡∂ (n + 1)).boundary M) :
    0 < EuclideanSpace.proj (0 : Fin (n + 1)) (inwardUnitNormal q) :=
  (isOutwardPointing_neg_iff_proj q.property).mp (isOutwardPointing_neg_inwardUnitNormal q)

/-- **Sign test.** A tangent vector at a boundary point is inward exactly when its inner product
with the inward unit normal is positive. -/
theorem isOutwardPointing_neg_iff_inner_inwardUnitNormal_pos {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    IsOutwardPointing (q : M) (-v) ↔ 0 < ⟪v, inwardUnitNormal q⟫_ℝ := by
  rw [isOutwardPointing_neg_iff_proj q.property, proj_eq_inner_mul,
    mul_pos_iff_of_pos_right (proj_inwardUnitNormal_pos q)]

/-- **Sign test.** A tangent vector at a boundary point is outward exactly when its inner product
with the inward unit normal is negative. -/
theorem isOutwardPointing_iff_inner_inwardUnitNormal_neg {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    IsOutwardPointing (q : M) v ↔ ⟪v, inwardUnitNormal q⟫_ℝ < 0 := by
  rw [isOutwardPointing_iff_proj q.property, proj_eq_inner_mul, ← neg_pos, ← neg_mul,
    mul_pos_iff_of_pos_right (proj_inwardUnitNormal_pos q), neg_pos]

/-- **Sign test.** A tangent vector at a boundary point is tangent to the boundary exactly when it
is orthogonal to the inward unit normal. -/
theorem mem_boundaryTangentSpace_iff_inner_inwardUnitNormal_eq_zero
    {q : (𝓡∂ (n + 1)).boundary M} {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    v ∈ boundaryTangentSpace q ↔ ⟪v, inwardUnitNormal q⟫_ℝ = 0 := by
  rw [boundaryTangentSpace_eq_orthogonal_span_inwardUnitNormal,
    Submodule.mem_orthogonal_singleton_iff_inner_left]

/-- The inward unit normal is the unique inward unit vector orthogonal to the tangent space of the
boundary. -/
theorem eq_inwardUnitNormal_iff {q : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (q : M)} :
    v = inwardUnitNormal q ↔ ‖v‖ = 1 ∧ IsOutwardPointing (q : M) (-v) ∧
      ∀ w ∈ boundaryTangentSpace q, ⟪v, w⟫_ℝ = 0 := by
  rw [inwardUnitNormal_def, ← neg_eq_iff_eq_neg, eq_outwardUnitNormal_iff]
  refine ⟨fun h ↦ ⟨by simpa using h.norm_eq_one, h.isOutwardPointing, fun w hw ↦ ?_⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨by simpa using h₁, h₂, fun w ↦ ?_⟩⟩
  · rw [boundaryTangentSpace_def, LinearMap.mem_range] at hw
    obtain ⟨u, rfl⟩ := hw
    simpa using h.inner_mfderiv_subtypeVal_eq_zero u
  · rw [inner_neg_left, h₃ _ (mfderiv_subtypeVal_mem_boundaryTangentSpace q w), neg_zero]

/-! ### The gradient of a function with a local minimum at a boundary point -/

/-- **Gradient formula.** A function differentiable at a boundary point `q`, with a local minimum
and nonzero differential there, has gradient `grad f(q) = |df_q| ν_in(q)`. -/
theorem mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin {f : M → ℝ}
    {q : (𝓡∂ (n + 1)).boundary M} (hmin : IsLocalMin f q)
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f q) (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0) :
    Manifold.mgradient (𝓡∂ (n + 1)) f q =
      ‖mvfderiv (𝓡∂ (n + 1)) f q‖ • inwardUnitNormal q := by
  -- The gradient is orthogonal to the boundary, since `df_q` vanishes on `T_q∂M`.
  have horth (w : TangentSpace (𝓡∂ (n + 1)) (q : M)) (hw : w ∈ boundaryTangentSpace q) :
      ⟪Manifold.mgradient (𝓡∂ (n + 1)) f q, w⟫_ℝ = 0 := by
    rw [Manifold.inner_mgradient]
    exact (mvfderiv_eq_zero_iff_mem_boundaryTangentSpace_of_isLocalMin hmin hf hne w).mpr hw
  have ht := sub_inner_smul_inwardUnitNormal_mem_boundaryTangentSpace q
    (Manifold.mgradient (𝓡∂ (n + 1)) f q)
  have hc : 0 < mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q) :=
    (isOutwardPointing_neg_iff_mvfderiv_pos_of_isLocalMin q.property hmin hf hne _).mp
      (isOutwardPointing_neg_inwardUnitNormal q)
  rw [Manifold.inner_mgradient] at ht
  have hg : Manifold.mgradient (𝓡∂ (n + 1)) f q =
      mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q) • inwardUnitNormal q := by
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
    nth_rw 1 [inner_sub_left]
    rw [horth _ ht, inner_smul_left, inner_inwardUnitNormal_of_mem_boundaryTangentSpace ht,
      mul_zero, sub_zero]
  have hnorm : ‖mvfderiv (𝓡∂ (n + 1)) f q‖ = mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q) := by
    rw [← Manifold.norm_mgradient_eq_norm_mvfderiv, hg, norm_smul, norm_inwardUnitNormal, mul_one,
      Real.norm_of_nonneg hc.le]
  rw [hnorm]
  exact hg

/-- A function differentiable at a boundary point `q`, with a local minimum and nonzero
differential there, has derivative `|df_q|` along the inward unit normal. -/
theorem mvfderiv_inwardUnitNormal_of_isLocalMin {f : M → ℝ}
    {q : (𝓡∂ (n + 1)).boundary M} (hmin : IsLocalMin f q)
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f q) (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0) :
    mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q) = ‖mvfderiv (𝓡∂ (n + 1)) f q‖ := by
  rw [← Manifold.inner_mgradient, mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin hmin hf hne,
    inner_smul_left, real_inner_self_eq_norm_sq, norm_inwardUnitNormal]
  simp

/-- **Gradient formula for boundary defining functions.** At a boundary point `q` of its domain, a
boundary defining function `ρ` has gradient `grad ρ(q) = |dρ_q| ν_in(q)`. -/
theorem IsBoundaryDefiningFunctionOn.mgradient_eq_norm_smul_inwardUnitNormal {ρ : M → ℝ}
    {U : Set M} (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : (𝓡∂ (n + 1)).boundary M}
    (hqU : (q : M) ∈ U) :
    Manifold.mgradient (𝓡∂ (n + 1)) ρ q = ‖mvfderiv (𝓡∂ (n + 1)) ρ q‖ • inwardUnitNormal q :=
  mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin (hρ.isLocalMin hqU q.property)
    (hρ.mdifferentiableAt hqU) (hρ.mvfderiv_ne_zero q hqU q.property)

/-- At a boundary point `q` of its domain, a boundary defining function `ρ` has derivative
`dρ_q(ν_in) = |dρ_q| > 0` along the inward unit normal. -/
theorem IsBoundaryDefiningFunctionOn.mvfderiv_inwardUnitNormal {ρ : M → ℝ} {U : Set M}
    (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : (𝓡∂ (n + 1)).boundary M}
    (hqU : (q : M) ∈ U) :
    mvfderiv (𝓡∂ (n + 1)) ρ q (inwardUnitNormal q) = ‖mvfderiv (𝓡∂ (n + 1)) ρ q‖ :=
  mvfderiv_inwardUnitNormal_of_isLocalMin (hρ.isLocalMin hqU q.property)
    (hρ.mdifferentiableAt hqU) (hρ.mvfderiv_ne_zero q hqU q.property)

/-- **Chart formula.** For every chart of the maximal atlas whose source contains the boundary
point `q`, the inward unit normal at `q` is the unit gradient of the normal coordinate `x⁰` of that
chart. -/
theorem inwardUnitNormal_eq_normalize_mgradient
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ e.source) :
    inwardUnitNormal q =
      NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q) := by
  have hne := mvfderiv_normal_ne_zero he hq
  rw [mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin
      (Eventually.of_forall fun y ↦ normal_le_of_mem_boundary q.property hq y)
      (mdifferentiableAt_normal he hq) hne]
  have hr : 0 < ‖mvfderiv (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q‖ := by
    rw [← Manifold.norm_mgradient_eq_norm_mvfderiv, norm_pos_iff, Ne,
      Manifold.mgradient_eq_zero_iff]
    exact hne
  rw [NormedSpace.normalize_smul_of_pos hr,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_inwardUnitNormal q)]

/-! ### Naturality -/

section Naturality

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 1 M']
  [Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]

omit [IsManifold (𝓡∂ (n + 1)) 1 M] [IsManifold (𝓡∂ (n + 1)) 1 M'] in
/-- An isometry of Riemannian manifolds with boundary maps boundary points to boundary points. -/
theorem RiemannianIsometry.apply_mem_boundary
    (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M) :
    Φ q ∈ (𝓡∂ (n + 1)).boundary M' := by
  rw [← mem_preimage, ← RiemannianIsometry.coe_toDiffeomorph,
    Φ.toDiffeomorph.preimage_boundary (by simp)]
  exact q.property

/-- **Naturality of the outward unit normal.** The differential of an isometry of Riemannian
manifolds with boundary carries the outward unit normal at `q` to the outward unit normal at
`Φ q`. -/
theorem RiemannianIsometry.mfderiv_outwardUnitNormal
    (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M) :
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q (outwardUnitNormal q) =
      outwardUnitNormal (⟨Φ q, Φ.apply_mem_boundary q⟩ : (𝓡∂ (n + 1)).boundary M') := by
  refine eq_outwardUnitNormal_iff.mpr
    ⟨by rw [Φ.norm_mfderiv, norm_outwardUnitNormal], ?_, fun w ↦ ?_⟩
  · exact (isOutwardPointing_mfderiv_iff (by simp) Φ.toDiffeomorph _).mpr
      (isOutwardPointing_outwardUnitNormal q)
  · have hw := mfderiv_subtypeVal_mem_boundaryTangentSpace
      (⟨Φ q, Φ.apply_mem_boundary q⟩ : (𝓡∂ (n + 1)).boundary M') w
    have hw' : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M' → M') ⟨Φ q, Φ.apply_mem_boundary q⟩ w ∈
        (boundaryTangentSpace q).map (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q).toLinearMap := by
      have hmap := map_mfderiv_boundaryTangentSpace (by simp) Φ.toDiffeomorph q
      simp only [RiemannianIsometry.coe_toDiffeomorph] at hmap
      rw [hmap]
      exact hw
    obtain ⟨u, hu, hu'⟩ := hw'
    rw [← hu']
    simp only [ContinuousLinearMap.coe_coe]
    rw [Φ.inner_mfderiv, inner_outwardUnitNormal_of_mem_boundaryTangentSpace hu]

/-- **Naturality of the inward unit normal.** The differential of an isometry of Riemannian
manifolds with boundary carries the inward unit normal at `q` to the inward unit normal at
`Φ q`. -/
theorem RiemannianIsometry.mfderiv_inwardUnitNormal
    (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M) :
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q (inwardUnitNormal q) =
      inwardUnitNormal (⟨Φ q, Φ.apply_mem_boundary q⟩ : (𝓡∂ (n + 1)).boundary M') := by
  rw [inwardUnitNormal_def, inwardUnitNormal_def, map_neg, Φ.mfderiv_outwardUnitNormal]

end Naturality

end TauCeti
