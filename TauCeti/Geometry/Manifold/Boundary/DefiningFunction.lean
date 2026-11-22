/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Boundary.TangentSpace
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Boundary defining functions

Let `M` be a manifold modelled on the half-space `𝓡∂ (n + 1)`. A **boundary defining function**
on an open set `U ⊆ M` (`TauCeti.IsBoundaryDefiningFunctionOn`) is a function `ρ : M → ℝ`,
smooth on `U`, positive at the interior points of `U`, zero at the boundary points of `U`, with
nonzero differential at the boundary points of `U`. The normal coordinate `x⁰` of a chart of the
maximal atlas is one on the chart source (`TauCeti.isBoundaryDefiningFunctionOn_normal`), so
boundary defining functions exist locally. On a Hausdorff σ-compact manifold a smooth partition of
unity glues local ones into a global boundary defining function
(`TauCeti.exists_isBoundaryDefiningFunctionOn_univ`): at a boundary point `q` the glued
differential is `∑ φ_i(q) dρ_i`, a convex combination of forms that are positive on the inward
vectors.

The sign of the differential of a boundary defining function at a boundary point `q` detects the
three kinds of tangent vectors: `dρ_q v` is negative exactly on the outward vectors, zero exactly
on the tangent space `T_q∂M` of the boundary and positive exactly on the inward vectors. This is
Fermat's theorem at a boundary point (`TauCeti.mvfderiv_nonneg_of_isLocalMin`): a function with a
local minimum at `q` has nonnegative differential on every vector that is not outward. A
differentiable function with a local minimum at `q` and nonzero differential there is therefore a
positive multiple of `x⁰` to first order
(`TauCeti.isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin`). The
normal coordinate of a chart at the image point, pulled back along a diffeomorphism, is such a
function, so diffeomorphisms of manifolds with boundary preserve outward vectors
(`TauCeti.isOutwardPointing_mfderiv_iff`) and pull back boundary defining functions
(`TauCeti.IsBoundaryDefiningFunctionOn.comp_diffeomorph`).

## Main declarations

* `TauCeti.mvfderiv_nonneg_of_isLocalMin`: Fermat's theorem at a boundary point.
* `TauCeti.isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin`: a function with a local minimum and
  nonzero differential at a boundary point decreases exactly along the outward vectors.
* `TauCeti.isOutwardPointing_mfderiv_iff`: diffeomorphisms preserve outward vectors.
* `TauCeti.IsBoundaryDefiningFunctionOn`: boundary defining functions on an open set.
* `TauCeti.IsBoundaryDefiningFunctionOn.isOutwardPointing_iff_mvfderiv_neg`,
  `TauCeti.IsBoundaryDefiningFunctionOn.isOutwardPointing_neg_iff_mvfderiv_pos` and
  `TauCeti.IsBoundaryDefiningFunctionOn.ker_mvfderiv`: the sign test.
* `TauCeti.isBoundaryDefiningFunctionOn_normal`: local existence, from the normal coordinate of a
  chart.
* `TauCeti.exists_isBoundaryDefiningFunctionOn_univ_of_iUnion_eq` and
  `TauCeti.exists_isBoundaryDefiningFunctionOn_univ`: gluing and global existence.
* `TauCeti.IsBoundaryDefiningFunctionOn.mono` and
  `TauCeti.IsBoundaryDefiningFunctionOn.comp_diffeomorph`: restriction to open subsets and
  pullback along diffeomorphisms.

## References

* G. Uhlmann, A. Vasy, *The inverse problem for the local geodesic ray transform*, Invent. Math.
  205 (2016), 83–120, Section 1 (the boundary defining function `ρ`).
* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), Section 3.1.
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-! ### Functions with a local minimum at a boundary point -/

/-- **Fermat's theorem at a boundary point.** A function differentiable at a boundary point `q`
with a local minimum there has nonnegative differential on every tangent vector at `q` that is not
outward. -/
theorem mvfderiv_nonneg_of_isLocalMin {f : M → ℝ} {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hmin : IsLocalMin f q)
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f q) {v : TangentSpace (𝓡∂ (n + 1)) q}
    (hv : ¬IsOutwardPointing q v) : 0 ≤ mvfderiv (𝓡∂ (n + 1)) f q v := by
  let I := 𝓡∂ (n + 1)
  -- Read `f` in the preferred chart at `q`, as a function on the model half-space.
  have hd := hf.hasMFDerivAt.2
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp] at hd
  have hy0 : extChartAt I q q 0 = 0 := by
    simpa only [I, extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_toFun] using
      (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff (mem_chart_source _ q)).mp hq
  have hmin' : IsLocalMinOn (f ∘ (extChartAt I q).symm) (range I) (extChartAt I q q) := by
    have h := (map_extChartAt_symm_nhdsWithin_range (I := I) q).le
    refine IsMinFilter.comp_of_tendsto ?_ h
    rwa [extChartAt_to_inv]
  -- The tangent space at `q` is the model space, in which `v` is a vector with `0 ≤ v 0`.
  let w : EuclideanSpace ℝ (Fin (n + 1)) := v
  have hw : 0 ≤ w 0 := by
    rw [isOutwardPointing_iff_proj hq, not_lt] at hv
    exact hv
  have hcone : w ∈ posTangentConeAt (range I) (extChartAt I q q) := by
    apply mem_posTangentConeAt_of_segment_subset
    apply I.convex_range.segment_subset (mem_range_self (chartAt _ q q))
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp only [mem_ofPred_eq, PiLp.add_apply, hy0, zero_add]
    exact hw
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact hmin'.hasFDerivWithinAt_nonneg hd hcone

/-- A function differentiable at a boundary point `q`, with a local minimum and nonzero
differential there, decreases exactly along the outward vectors: to first order it is a positive
multiple of the normal coordinate of a chart. -/
theorem isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin {f : M → ℝ} {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hmin : IsLocalMin f q)
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f q) (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔ mvfderiv (𝓡∂ (n + 1)) f q v < 0 := by
  let π : Module.Dual ℝ (TangentSpace (𝓡∂ (n + 1)) q) := EuclideanSpace.projₗ (0 : Fin (n + 1))
  let e₀ : TangentSpace (𝓡∂ (n + 1)) q := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
  have hπ : π e₀ = 1 := by
    change (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0 = 1
    simp
  have hnonneg (w : TangentSpace (𝓡∂ (n + 1)) q) (hw : 0 ≤ π w) :
      0 ≤ mvfderiv (𝓡∂ (n + 1)) f q w :=
    mvfderiv_nonneg_of_isLocalMin hq hmin hf fun h ↦
      ((isOutwardPointing_iff_proj hq).mp h).not_ge hw
  have hfactor (w : TangentSpace (𝓡∂ (n + 1)) q) :
      mvfderiv (𝓡∂ (n + 1)) f q w = mvfderiv (𝓡∂ (n + 1)) f q e₀ * π w :=
    Module.Dual.apply_eq_mul_apply_of_nonneg π
      (mvfderiv (𝓡∂ (n + 1)) f q : TangentSpace (𝓡∂ (n + 1)) q →ₗ[ℝ] ℝ) hπ hnonneg w
  have hpos : 0 < mvfderiv (𝓡∂ (n + 1)) f q e₀ := by
    refine (hnonneg e₀ (hπ ▸ zero_le_one)).lt_of_ne fun h0 ↦ hne ?_
    ext w
    rw [hfactor w, ← h0, zero_mul, zero_apply]
  rw [hfactor v, isOutwardPointing_iff_proj hq, ← smul_eq_mul, smul_neg_iff_of_pos_left hpos]
  rfl

/-- A function differentiable at a boundary point `q`, with a local minimum and nonzero
differential there, increases exactly along the inward vectors. -/
theorem isOutwardPointing_neg_iff_mvfderiv_pos_of_isLocalMin {f : M → ℝ} {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (hmin : IsLocalMin f q)
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f q) (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0)
    (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q (-v) ↔ 0 < mvfderiv (𝓡∂ (n + 1)) f q v := by
  rw [isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hq hmin hf hne, map_neg, neg_lt_zero]

/-- A function differentiable at a boundary point `q`, with a local minimum and nonzero
differential there, has differential vanishing exactly on the tangent space of the boundary. -/
theorem mvfderiv_eq_zero_iff_mem_boundaryTangentSpace_of_isLocalMin {f : M → ℝ}
    {q : (𝓡∂ (n + 1)).boundary M} (hmin : IsLocalMin f q)
    (hf : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) f q)
    (hne : mvfderiv (𝓡∂ (n + 1)) f q ≠ 0) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    mvfderiv (𝓡∂ (n + 1)) f q v = 0 ↔ v ∈ boundaryTangentSpace q := by
  rw [mem_boundaryTangentSpace_iff_not_isOutwardPointing_and_not_isOutwardPointing_neg,
    isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin q.property hmin hf hne,
    isOutwardPointing_neg_iff_mvfderiv_pos_of_isLocalMin q.property hmin hf hne, not_lt, not_lt]
  exact ⟨fun h ↦ ⟨h.ge, h.le⟩, fun h ↦ le_antisymm h.2 h.1⟩

section Diffeomorph

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanHalfSpace (n + 1)) M']
  [IsManifold (𝓡∂ (n + 1)) 1 M']

/-- **Diffeomorphisms preserve outward vectors.** For a diffeomorphism `Φ` of manifolds with
boundary, of class `C^k` with `k ≠ 0`, a tangent vector `v` at `q` is outward exactly when its
image `dΦ_q v` is outward at `Φ q`. -/
theorem isOutwardPointing_mfderiv_iff {k : WithTop ℕ∞} (hk : k ≠ 0)
    (Φ : M ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M') {q : M} (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing (Φ q) (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q v) ↔
      IsOutwardPointing q v := by
  by_cases hq : q ∈ (𝓡∂ (n + 1)).boundary M
  swap
  · refine iff_of_false (fun h ↦ hq ?_) fun h ↦ hq h.mem_boundary
    rw [← Φ.preimage_boundary hk]
    exact h.mem_boundary
  have hΦq : Φ q ∈ (𝓡∂ (n + 1)).boundary M' := by
    simpa [← Φ.preimage_boundary hk] using hq
  -- The normal coordinate of the preferred chart at `Φ q`, and its pullback along `Φ`.
  let x₀ : M' → ℝ := fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) (Φ q) y).val 0
  have hmin' : IsLocalMin x₀ (Φ q) := Eventually.of_forall fun y ↦
    normal_le_of_mem_boundary hΦq (mem_chart_source _ _) y
  have hx₀ : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) x₀ (Φ q) :=
    mdifferentiableAt_normal (IsManifold.chart_mem_maximalAtlas _) (mem_chart_source _ _)
  have hne' : mvfderiv (𝓡∂ (n + 1)) x₀ (Φ q) ≠ 0 :=
    mvfderiv_normal_ne_zero (IsManifold.chart_mem_maximalAtlas _) (mem_chart_source _ _)
  have hΦ : MDifferentiableAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q := Φ.mdifferentiable hk q
  have hcomp (w : TangentSpace (𝓡∂ (n + 1)) q) : mvfderiv (𝓡∂ (n + 1)) (x₀ ∘ Φ) q w =
      mvfderiv (𝓡∂ (n + 1)) x₀ (Φ q) (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) Φ q w) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply,
      mfderiv_comp_apply q hx₀ hΦ]
  have hne : mvfderiv (𝓡∂ (n + 1)) (x₀ ∘ Φ) q ≠ 0 := by
    intro h0
    refine hne' (ContinuousLinearMap.ext fun w ↦ ?_)
    obtain ⟨u, rfl⟩ := (Φ.isInvertible_mfderiv hk).surjective w
    rw [← hcomp, h0]
    rfl
  rw [isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hΦq hmin' hx₀ hne',
    isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hq
      (hmin'.comp_continuous Φ.continuous.continuousAt)
      (hx₀.comp q hΦ) hne, hcomp]

end Diffeomorph

/-! ### Boundary defining functions -/

variable (n) in
/-- `ρ` is a **boundary defining function** on the open set `U ⊆ M`: it is smooth on `U`, positive
at the interior points of `U`, zero at the boundary points of `U`, and has nonzero differential at
the boundary points of `U`. A global boundary defining function is one on `U = univ`. -/
structure IsBoundaryDefiningFunctionOn (ρ : M → ℝ) (U : Set M) : Prop where
  /-- The domain of a boundary defining function is open. -/
  isOpen : IsOpen U
  /-- A boundary defining function is smooth on its domain. -/
  contMDiffOn : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ ρ U
  /-- A boundary defining function is positive at interior points. -/
  pos : ∀ x ∈ U, x ∈ (𝓡∂ (n + 1)).interior M → 0 < ρ x
  /-- A boundary defining function vanishes at boundary points. -/
  eq_zero : ∀ x ∈ U, x ∈ (𝓡∂ (n + 1)).boundary M → ρ x = 0
  /-- A boundary defining function has nonzero differential at boundary points. -/
  mvfderiv_ne_zero : ∀ x ∈ U, x ∈ (𝓡∂ (n + 1)).boundary M → mvfderiv (𝓡∂ (n + 1)) ρ x ≠ 0

namespace IsBoundaryDefiningFunctionOn

variable {ρ : M → ℝ} {U : Set M}

/-- A boundary defining function is nonnegative on its domain. -/
theorem nonneg (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M} (hx : x ∈ U) : 0 ≤ ρ x := by
  rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x with h | h
  · exact (hρ.pos x hx h).le
  · exact (hρ.eq_zero x hx h).ge

/-- A boundary defining function has a local minimum at each boundary point of its domain. -/
theorem isLocalMin (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : M} (hqU : q ∈ U)
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) : IsLocalMin ρ q := by
  filter_upwards [hρ.isOpen.mem_nhds hqU] with y hy
  rw [hρ.eq_zero q hqU hq]
  exact hρ.nonneg hy

/-- A boundary defining function is differentiable at each point of its domain. -/
theorem mdifferentiableAt (hρ : IsBoundaryDefiningFunctionOn n ρ U) {x : M} (hx : x ∈ U) :
    MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) ρ x :=
  ((hρ.contMDiffOn x hx).contMDiffAt (hρ.isOpen.mem_nhds hx)).mdifferentiableAt
    (by simp)

/-- **Sign test.** At a boundary point of its domain, a boundary defining function decreases
exactly along the outward vectors. -/
theorem isOutwardPointing_iff_mvfderiv_neg (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : M}
    (hqU : q ∈ U) (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q v ↔ mvfderiv (𝓡∂ (n + 1)) ρ q v < 0 :=
  isOutwardPointing_iff_mvfderiv_neg_of_isLocalMin hq (hρ.isLocalMin hqU hq)
    (hρ.mdifferentiableAt hqU) (hρ.mvfderiv_ne_zero q hqU hq) v

/-- **Sign test.** At a boundary point of its domain, a boundary defining function increases
exactly along the inward vectors. -/
theorem isOutwardPointing_neg_iff_mvfderiv_pos (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : M}
    (hqU : q ∈ U) (hq : q ∈ (𝓡∂ (n + 1)).boundary M) (v : TangentSpace (𝓡∂ (n + 1)) q) :
    IsOutwardPointing q (-v) ↔ 0 < mvfderiv (𝓡∂ (n + 1)) ρ q v :=
  isOutwardPointing_neg_iff_mvfderiv_pos_of_isLocalMin hq (hρ.isLocalMin hqU hq)
    (hρ.mdifferentiableAt hqU) (hρ.mvfderiv_ne_zero q hqU hq) v

/-- At a boundary point of its domain, the differential of a boundary defining function vanishes
exactly on the tangent space of the boundary. -/
theorem mvfderiv_eq_zero_iff (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    {q : (𝓡∂ (n + 1)).boundary M} (hqU : (q : M) ∈ U) (v : TangentSpace (𝓡∂ (n + 1)) (q : M)) :
    mvfderiv (𝓡∂ (n + 1)) ρ q v = 0 ↔ v ∈ boundaryTangentSpace q :=
  mvfderiv_eq_zero_iff_mem_boundaryTangentSpace_of_isLocalMin (hρ.isLocalMin hqU q.property)
    (hρ.mdifferentiableAt hqU) (hρ.mvfderiv_ne_zero q hqU q.property) v

/-- At a boundary point of its domain, the kernel of the differential of a boundary defining
function is the tangent space of the boundary. -/
theorem ker_mvfderiv (hρ : IsBoundaryDefiningFunctionOn n ρ U)
    {q : (𝓡∂ (n + 1)).boundary M} (hqU : (q : M) ∈ U) :
    LinearMap.ker (mvfderiv (𝓡∂ (n + 1)) ρ q).toLinearMap = boundaryTangentSpace q := by
  ext v
  exact hρ.mvfderiv_eq_zero_iff hqU v

/-- A boundary defining function restricts to a boundary defining function on every open subset of
its domain. -/
theorem mono (hρ : IsBoundaryDefiningFunctionOn n ρ U) {V : Set M} (hV : IsOpen V)
    (hVU : V ⊆ U) : IsBoundaryDefiningFunctionOn n ρ V where
  isOpen := hV
  contMDiffOn := hρ.contMDiffOn.mono hVU
  pos x hx := hρ.pos x (hVU hx)
  eq_zero x hx := hρ.eq_zero x (hVU hx)
  mvfderiv_ne_zero x hx := hρ.mvfderiv_ne_zero x (hVU hx)

/-- A boundary defining function pulls back along a smooth diffeomorphism `Φ` of manifolds with
boundary to a boundary defining function on the preimage of its domain. -/
theorem comp_diffeomorph {M' : Type*} [TopologicalSpace M']
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M'] (Φ : M' ≃ₘ^∞⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ M)
    (hρ : IsBoundaryDefiningFunctionOn n ρ U) :
    IsBoundaryDefiningFunctionOn n (ρ ∘ Φ) (Φ ⁻¹' U) where
  isOpen := hρ.isOpen.preimage Φ.continuous
  contMDiffOn := hρ.contMDiffOn.comp Φ.contMDiff.contMDiffOn (mapsTo_preimage Φ U)
  pos x hx hint := hρ.pos (Φ x) hx (by rwa [← mem_preimage, Φ.preimage_interior (by simp)])
  eq_zero x hx hb :=
    hρ.eq_zero (Φ x) hx (by rwa [← mem_preimage, Φ.preimage_boundary (by simp)])
  mvfderiv_ne_zero x hx hb := by
    have hΦx : Φ x ∈ (𝓡∂ (n + 1)).boundary M := by
      rwa [← mem_preimage, Φ.preimage_boundary (by simp)]
    intro h0
    refine hρ.mvfderiv_ne_zero (Φ x) hx hΦx (ContinuousLinearMap.ext fun w ↦ ?_)
    obtain ⟨u, rfl⟩ := (Φ.isInvertible_mfderiv (by simp)).surjective w
    have h := congrArg (fun L ↦ L u) h0
    simp only [mvfderiv_apply_eq_mfderiv_apply] at h ⊢
    rw [mfderiv_comp_apply x (hρ.mdifferentiableAt hx) (Φ.mdifferentiable (by simp) x)] at h
    exact h

end IsBoundaryDefiningFunctionOn

/-- **Local existence.** The normal coordinate `x⁰` of a chart of the smooth maximal atlas is a
boundary defining function on the chart source. -/
theorem isBoundaryDefiningFunctionOn_normal
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) ∞ M) :
    IsBoundaryDefiningFunctionOn n (fun y ↦ (e y).val 0) e.source where
  isOpen := e.open_source
  contMDiffOn := by
    have h := ((EuclideanSpace.proj (0 : Fin (n + 1)) :
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contMDiff.comp_contMDiffOn
        (e.contMDiffOn_extend he))
    exact h.congr fun y _ ↦ by simp
  pos x hx hint := (ModelWithCorners.isInteriorPoint_euclideanHalfSpace_iff hx).mp hint
  eq_zero x hx hb := (ModelWithCorners.mem_boundary_euclideanHalfSpace_iff hx).mp hb
  mvfderiv_ne_zero x hx _ :=
    mvfderiv_normal_ne_zero (IsManifold.maximalAtlas_subset_of_le (by simp) he) hx

/-- On an open set of interior points, the constant `1` is a boundary defining function. -/
theorem isBoundaryDefiningFunctionOn_one {U : Set M} (hU : IsOpen U)
    (hUi : U ⊆ (𝓡∂ (n + 1)).interior M) :
    IsBoundaryDefiningFunctionOn n (fun _ ↦ (1 : ℝ)) U where
  isOpen := hU
  contMDiffOn := contMDiffOn_const
  pos _ _ _ := one_pos
  eq_zero _ hx hb := absurd (hUi hx) fun hi ↦
    (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ (n + 1))).ne_of_mem hi hb rfl
  mvfderiv_ne_zero _ hx hb := absurd (hUi hx) fun hi ↦
    (ModelWithCorners.disjoint_interior_boundary (I := 𝓡∂ (n + 1))).ne_of_mem hi hb rfl

/-- The differential at a boundary point `q` of the sum `∑ᶠ i, φ i • ρ i`, for a smooth partition
of unity `φ` subordinate to the domains of boundary defining functions `ρ i`, is positive on the
inward vectors: it is `∑ i, φ i q • dρ_i`, since every `ρ i` with `q` in the support of `φ i`
vanishes at `q`. -/
private theorem mvfderiv_finsum_smul_pos {ι : Type*}
    {U : ι → Set M} {ρ : ι → M → ℝ} (hρ : ∀ i, IsBoundaryDefiningFunctionOn n (ρ i) (U i))
    {φ : SmoothPartitionOfUnity ι (𝓡∂ (n + 1)) M univ} (hφ : φ.IsSubordinate U) {q : M}
    (hq : q ∈ (𝓡∂ (n + 1)).boundary M) {v : TangentSpace (𝓡∂ (n + 1)) q}
    (hv : IsOutwardPointing q (-v)) :
    0 < mvfderiv (𝓡∂ (n + 1)) (fun x ↦ ∑ᶠ i, φ i x • ρ i x) q v := by
  have hU {i : ι} (hi : i ∈ φ.fintsupport q) : q ∈ U i :=
    hφ i ((φ.mem_fintsupport_iff q i).mp hi)
  -- Near `q` the sum runs over the finite set of `i` with `q` in the support of `φ i`.
  have heq : (fun x ↦ ∑ᶠ i, φ i x • ρ i x) =ᶠ[𝓝 q]
      fun x ↦ ∑ i ∈ φ.fintsupport q, φ i x • ρ i x := by
    filter_upwards [φ.eventually_fintsupport_subset q] with y hy
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ hy ?_
    exact (φ.mem_fintsupport_iff y i).mpr (subset_tsupport _ (left_ne_zero_of_smul hi))
  have hdφ (i : ι) : MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ) (φ i) q :=
    (φ i).contMDiff.mdifferentiableAt (by simp)
  have hterm (i : ι) (hi : i ∈ φ.fintsupport q) :
      mvfderiv (𝓡∂ (n + 1)) (fun x ↦ φ i x • ρ i x) q v =
        φ i q * mvfderiv (𝓡∂ (n + 1)) (ρ i) q v := by
    rw [mvfderiv_fun_smul (hdφ i) ((hρ i).mdifferentiableAt (hU hi)),
      (hρ i).eq_zero q (hU hi) hq]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      mul_zero, add_zero]
  rw [heq.mvfderiv_eq, mvfderiv_fun_sum (f := fun i x ↦ φ i x • ρ i x) fun i hi ↦
      (hdφ i).smul ((hρ i).mdifferentiableAt (hU hi)), sum_apply,
    Finset.sum_congr rfl hterm]
  obtain ⟨j, hj⟩ := φ.exists_pos_of_mem (mem_univ q)
  have hjF : j ∈ φ.fintsupport q :=
    (φ.mem_fintsupport_iff q j).mpr (subset_tsupport _ hj.ne')
  refine Finset.sum_pos' (fun i hi ↦ mul_nonneg (φ.nonneg i q)
    ((((hρ i).isOutwardPointing_neg_iff_mvfderiv_pos (hU hi) hq v).mp hv).le))
    ⟨j, hjF, mul_pos hj (((hρ j).isOutwardPointing_neg_iff_mvfderiv_pos (hU hjF) hq v).mp hv)⟩

/-- **Gluing.** If boundary defining functions on open sets cover a Hausdorff σ-compact manifold,
then gluing them with a smooth partition of unity gives a global boundary defining function. -/
theorem exists_isBoundaryDefiningFunctionOn_univ_of_iUnion_eq [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M] {ι : Type*} {U : ι → Set M} {ρ : ι → M → ℝ}
    (hρ : ∀ i, IsBoundaryDefiningFunctionOn n (ρ i) (U i)) (hU : ⋃ i, U i = univ) :
    ∃ ρ' : M → ℝ, IsBoundaryDefiningFunctionOn n ρ' univ := by
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓡∂ (n + 1)) isClosed_univ U
    (fun i ↦ (hρ i).isOpen) hU.ge
  have hmem {i : ι} {x : M} (hx : φ i x ≠ 0) : x ∈ U i := hφ i (subset_tsupport _ hx)
  refine ⟨fun x ↦ ∑ᶠ i, φ i x • ρ i x, isOpen_univ,
    (hφ.contMDiff_finsum_smul (fun i ↦ (hρ i).isOpen) fun i ↦ (hρ i).contMDiffOn).contMDiffOn,
    fun x _ hx ↦ ?_, fun x _ hx ↦ ?_, fun q _ hq h0 ↦ ?_⟩
  · exact φ.finsum_smul_mem_convex (g := ρ) (mem_univ x) (fun i hi ↦ (hρ i).pos x (hmem hi) hx)
      (convex_Ioi 0)
  · exact φ.finsum_smul_mem_convex (g := ρ) (t := {0}) (mem_univ x)
      (fun i hi ↦ (hρ i).eq_zero x (hmem hi) hx) (convex_singleton 0)
  · -- The differential is positive on the inward vector `e₀` of the preferred chart.
    let e₀ : TangentSpace (𝓡∂ (n + 1)) q := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
    have he₀ : IsOutwardPointing q (-e₀) := by
      rw [isOutwardPointing_neg_iff_proj hq]
      change 0 < (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) 0
      simp
    have h := mvfderiv_finsum_smul_pos hρ hφ hq he₀
    rw [h0] at h
    exact h.ne rfl

/-- **Global existence.** A Hausdorff σ-compact smooth manifold modelled on the half-space, for
instance a Hausdorff second-countable one, has a global boundary defining function. It is glued
from the normal coordinates of the preferred charts at boundary points and the constant `1` on the
interior. -/
theorem exists_isBoundaryDefiningFunctionOn_univ [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M]
    [SigmaCompactSpace M] : ∃ ρ : M → ℝ, IsBoundaryDefiningFunctionOn n ρ univ := by
  classical
  let U : M → Set M := fun x ↦ if x ∈ (𝓡∂ (n + 1)).boundary M then
    (chartAt (EuclideanHalfSpace (n + 1)) x).source else (𝓡∂ (n + 1)).interior M
  let ρ : M → M → ℝ := fun x ↦ if x ∈ (𝓡∂ (n + 1)).boundary M then
    (fun y ↦ (chartAt (EuclideanHalfSpace (n + 1)) x y).val 0) else fun _ ↦ 1
  refine exists_isBoundaryDefiningFunctionOn_univ_of_iUnion_eq (U := U) (ρ := ρ) (fun x ↦ ?_)
    (eq_univ_of_forall fun x ↦ mem_iUnion.mpr ⟨x, ?_⟩)
  · by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
    · simpa only [U, ρ, hx, ↓reduceIte] using
        isBoundaryDefiningFunctionOn_normal (IsManifold.chart_mem_maximalAtlas x)
    · simpa only [U, ρ, hx, ↓reduceIte] using isBoundaryDefiningFunctionOn_one
        ((𝓡∂ (n + 1)).isOpen_interior (M := M) (n := ∞) (by simp)) subset_rfl
  · by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
    · simpa only [U, hx, ↓reduceIte] using mem_chart_source _ x
    · simp only [U, hx, ↓reduceIte]
      rw [← ModelWithCorners.compl_boundary]
      exact hx

end TauCeti
