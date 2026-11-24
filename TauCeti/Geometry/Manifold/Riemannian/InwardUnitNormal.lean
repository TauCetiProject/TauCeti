/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Basic
public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Comparison
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.OutwardUnitNormal

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

A function `f` with a local minimum at a boundary point `q`, such as a boundary defining function
`ρ`, has gradient `grad f(q) = |df_q| ν_in(q)`, so `df_q(ν_in) = |df_q|`
(`TauCeti.mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin`,
`TauCeti.IsBoundaryDefiningFunctionOn.mgradient_eq_norm_smul_inwardUnitNormal`). Two boundary
defining functions on the same open set differ by a smooth positive factor
(`TauCeti.IsBoundaryDefiningFunctionOn.exists_eq_mul`), which on the boundary is the ratio
`|dρ'| / |dρ|` of the norms of their differentials
(`TauCeti.IsBoundaryDefiningFunctionOn.exists_eq_mul_norm_div_norm`). In any chart of the
`C¹` maximal atlas, `ν_in = grad x⁰ / |grad x⁰|` for the normal coordinate `x⁰`
(`TauCeti.inwardUnitNormal_eq_normalize_mgradient`). For a `C^k` metric on a `C^(k + 1)` manifold,
`q ↦ (q, ν_in(q))` is a `C^k` map, like the outward unit normal
(`TauCeti.contMDiff_inwardUnitNormal`). An isometry
of Riemannian manifolds with boundary carries inward unit normals to inward unit normals
(`TauCeti.RiemannianIsometry.mfderiv_inwardUnitNormal`).

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
* `TauCeti.IsBoundaryDefiningFunctionOn.exists_eq_mul_norm_div_norm`: two boundary defining
  functions differ by a smooth positive factor, equal to `|dρ'| / |dρ|` on the boundary.
* `TauCeti.inwardUnitNormal_eq_normalize_mgradient`: the chart formula in any chart of the `C¹`
  maximal atlas.
* `TauCeti.contMDiff_inwardUnitNormal`: it is a `C^k` map `∂M → TM` for a `C^k` metric on a
  `C^(k + 1)` manifold.
* `TauCeti.RiemannianIsometry.mfderiv_inwardUnitNormal`: naturality under isometries.

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
@[simp]
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
  rw [inwardUnitNormal_def, ← Set.neg_singleton, Submodule.span_neg,
    ← orthogonalNormalSpace_subtypeVal_boundary_eq_span, orthogonalNormalSpace_def,
    Submodule.orthogonal_orthogonal]
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

/-- **Gradient formula.** A function with a local minimum at a boundary point `q` has gradient
`grad f(q) = |df_q| ν_in(q)`. -/
theorem mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin {f : M → ℝ}
    {q : (𝓡∂ (n + 1)).boundary M} (hmin : IsLocalMin f q) :
    Manifold.mgradient (𝓡∂ (n + 1)) f q =
      ‖mvfderiv (𝓡∂ (n + 1)) f q‖ • inwardUnitNormal q := by
  by_cases hne : mvfderiv (𝓡∂ (n + 1)) f q = 0
  · -- The norm of `df_q` is that of the gradient, which vanishes with `df_q`.
    rw [← Manifold.norm_mgradient_eq_norm_mvfderiv, Manifold.mgradient_eq_zero_iff.mpr hne,
      norm_zero, zero_smul]
  -- The gradient is orthogonal to the boundary, since `df_q` vanishes on `T_q∂M`.
  have horth (w : TangentSpace (𝓡∂ (n + 1)) (q : M)) (hw : w ∈ boundaryTangentSpace q) :
      ⟪Manifold.mgradient (𝓡∂ (n + 1)) f q, w⟫_ℝ = 0 := by
    rw [Manifold.inner_mgradient]
    exact (mvfderiv_eq_zero_iff_mem_boundaryTangentSpace_of_isLocalMin hmin hne w).mpr hw
  have ht := sub_inner_smul_inwardUnitNormal_mem_boundaryTangentSpace q
    (Manifold.mgradient (𝓡∂ (n + 1)) f q)
  have hc : 0 < mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q) :=
    (isOutwardPointing_neg_iff_mvfderiv_pos_of_isLocalMin q.property hmin hne _).mp
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

/-- A function with a local minimum at a boundary point `q` has derivative `|df_q|` along the
inward unit normal. -/
theorem mvfderiv_inwardUnitNormal_of_isLocalMin {f : M → ℝ}
    {q : (𝓡∂ (n + 1)).boundary M} (hmin : IsLocalMin f q) :
    mvfderiv (𝓡∂ (n + 1)) f q (inwardUnitNormal q) = ‖mvfderiv (𝓡∂ (n + 1)) f q‖ := by
  rw [← Manifold.inner_mgradient, mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin hmin,
    inner_smul_left, real_inner_self_eq_norm_sq, norm_inwardUnitNormal]
  simp

/-- **Gradient formula for boundary defining functions.** At a boundary point `q` of its domain, a
boundary defining function `ρ` has gradient `grad ρ(q) = |dρ_q| ν_in(q)`. -/
theorem IsBoundaryDefiningFunctionOn.mgradient_eq_norm_smul_inwardUnitNormal {ρ : M → ℝ}
    {U : Set M} (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : (𝓡∂ (n + 1)).boundary M}
    (hqU : (q : M) ∈ U) :
    Manifold.mgradient (𝓡∂ (n + 1)) ρ q = ‖mvfderiv (𝓡∂ (n + 1)) ρ q‖ • inwardUnitNormal q :=
  mgradient_eq_norm_smul_inwardUnitNormal_of_isLocalMin (hρ.isLocalMin hqU q.property)

/-- At a boundary point `q` of its domain, a boundary defining function `ρ` has derivative
`dρ_q(ν_in) = |dρ_q|` along the inward unit normal. -/
theorem IsBoundaryDefiningFunctionOn.mvfderiv_inwardUnitNormal {ρ : M → ℝ} {U : Set M}
    (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : (𝓡∂ (n + 1)).boundary M}
    (hqU : (q : M) ∈ U) :
    mvfderiv (𝓡∂ (n + 1)) ρ q (inwardUnitNormal q) = ‖mvfderiv (𝓡∂ (n + 1)) ρ q‖ :=
  mvfderiv_inwardUnitNormal_of_isLocalMin (hρ.isLocalMin hqU q.property)

omit [IsManifold (𝓡∂ (n + 1)) 1 M] in
/-- **Comparison of boundary defining functions, Riemannian form.** Two boundary defining functions
`ρ`, `ρ'` on the same open set `U` satisfy `ρ' = u ρ` on `U` for a function `u` smooth and positive
on `U` with `u = |dρ'| / |dρ|` at the boundary points of `U`. -/
theorem IsBoundaryDefiningFunctionOn.exists_eq_mul_norm_div_norm [IsManifold (𝓡∂ (n + 1)) ∞ M]
    {ρ ρ' : M → ℝ} {U : Set M} (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    (hρ' : IsBoundaryDefiningFunctionOn n ρ' U) :
    ∃ u : M → ℝ, ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ u U ∧ (∀ x ∈ U, 0 < u x) ∧
      (∀ x ∈ U, ρ' x = u x * ρ x) ∧
      ∀ q : (𝓡∂ (n + 1)).boundary M, (q : M) ∈ U →
        u q = ‖mvfderiv (𝓡∂ (n + 1)) ρ' q‖ / ‖mvfderiv (𝓡∂ (n + 1)) ρ q‖ := by
  obtain ⟨u, hu, hpos, hmul, hderiv⟩ := hρ.exists_eq_mul hρ'
  refine ⟨u, hu, hpos, hmul, fun q hqU ↦ ?_⟩
  -- Both norms are the derivatives along the inward unit normal, where `dρ` is positive.
  rw [← hρ.mvfderiv_inwardUnitNormal hqU, ← hρ'.mvfderiv_inwardUnitNormal hqU,
    hderiv q hqU q.property, smul_apply, smul_eq_mul, mul_div_cancel_right₀]
  exact ((hρ.isOutwardPointing_neg_iff_mvfderiv_pos hqU q.property _).mp
    (isOutwardPointing_neg_inwardUnitNormal q)).ne'

/-- **Chart formula.** For every chart of the `C¹` maximal atlas whose source contains the boundary
point `q`, the inward unit normal at `q` is the unit gradient of the normal coordinate `x⁰` of that
chart. -/
theorem inwardUnitNormal_eq_normalize_mgradient
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) 1 M) {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ e.source) :
    inwardUnitNormal q =
      NormedSpace.normalize (Manifold.mgradient (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q) := by
  have hneg : Manifold.mgradient (𝓡∂ (n + 1)) (fun y ↦ -(e y).val 0) q =
      -Manifold.mgradient (𝓡∂ (n + 1)) (fun y ↦ (e y).val 0) q :=
    Manifold.mgradient_neg
  rw [inwardUnitNormal_def, outwardUnitNormal_eq_normalize_mgradient he hq, hneg,
    NormedSpace.normalize_neg, neg_neg]

/-! ### Regularity -/

/-- **The inward unit normal is as regular as the metric**: for a `C^k` metric on a `C^(k + 1)`
manifold, `q ↦ (q, ν_in(q))` is a `C^k` map from the boundary manifold to the tangent bundle. -/
theorem contMDiff_inwardUnitNormal {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent k
      (fun q : (𝓡∂ (n + 1)).boundary M ↦
        (⟨q, inwardUnitNormal q⟩ : TangentBundle (𝓡∂ (n + 1)) M)) := by
  intro q₀
  -- `ν_in = -ν_out`, and the trivializations of the tangent bundle are linear on the fibres.
  have h := contMDiff_outwardUnitNormal (M := M) (k := k) q₀
  rw [ModelWithCorners.tangent, contMDiffAt_totalSpace_iff] at h ⊢
  refine ⟨h.1, h.2.neg.congr_of_eventuallyEq ?_⟩
  let e := trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1)))
    (q₀ : M)
  filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ (q₀ : M)))] with q hq
  exact (e.linear ℝ hq).map_neg _

/-! ### Naturality -/

section Naturality

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 1 M']
  [Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **Naturality of the inward unit normal.** The differential of an isometry of Riemannian
manifolds with boundary carries the inward unit normal at `q` to the inward unit normal at
`Φ q`. -/
theorem RiemannianIsometry.mfderiv_inwardUnitNormal
    (Φ : RiemannianIsometry (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) M M') (q : (𝓡∂ (n + 1)).boundary M) :
    mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q (inwardUnitNormal q) =
      inwardUnitNormal (⟨Φ q, Φ.apply_mem_boundary q.property⟩ : (𝓡∂ (n + 1)).boundary M') := by
  rw [inwardUnitNormal_def, inwardUnitNormal_def, map_neg, Φ.mfderiv_outwardUnitNormal]

end Naturality

end TauCeti
