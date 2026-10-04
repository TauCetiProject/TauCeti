/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Analysis.Normed.Module.Ball.LinearIsometry
public import TauCeti.Geometry.Euclidean.Inversion
public import TauCeti.Geometry.Manifold.Boundary.Basic
public import TauCeti.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.Orientation
import TauCeti.Analysis.InnerProductSpace.Reflection

/-!
# The closed unit ball as an analytic manifold with boundary

The closed unit ball `Dⁿ = closedBall (0 : E) 1` of an `n`-dimensional real inner product space
`E` is an analytic manifold with boundary, modelled on the half-space `EuclideanHalfSpace n`, and
its manifold boundary is the unit sphere. This is the disc that handles `Dᵏ × Dⁿ⁻ᵏ` are built
from, that ball embeddings and connected sums use, and whose diffeomorphisms fixing the boundary
form the group `Diff(Dⁿ, ∂)`.

## Charts

Write `e₀` for the first standard basis vector of `EuclideanSpace ℝ (Fin n)`. The inversion in
the sphere of radius `√2` centred at `-e₀` passes the unit sphere through its centre, so it maps
the unit sphere minus `-e₀` onto the hyperplane `{y | y 0 = 0}` and the closed unit ball minus
`-e₀` onto the closed half-space `{y | 0 ≤ y 0}`. Precomposing with a linear isometry
`φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)` gives the chart `TauCeti.closedBallChart φ`, defined
on the ball minus `φ.symm (-e₀)`, whose target is the whole half-space. The atlas consists of
these charts for all `φ`. Every transition map is a composite of two inversions and a linear
isometry, hence analytic, so the ball is an analytic manifold.

## Main declarations

* `TauCeti.closedBallChart φ`: the chart attached to a linear isometry `φ`.
* `TauCeti.instChartedSpaceClosedBall`, `TauCeti.instIsManifoldClosedBall`: the closed unit ball
  of an `n`-dimensional real inner product space is an analytic manifold modelled on
  `EuclideanHalfSpace n`.
* `TauCeti.boundary_closedBall`: its manifold boundary is the unit sphere.
* `TauCeti.isInteriorPoint_closedBall_iff`: its interior points are those of norm less than `1`.
* `TauCeti.orientable_closedBall`: in dimension at least two it is orientable, the charts attached
  to the isometries `φ` of one orientation class forming an oriented atlas.
* `TauCeti.contMDiff_subtypeVal_closedBall`: the inclusion into `E` is analytic.
* `TauCeti.contMDiff_iff_comp_subtypeVal_closedBall`: a map into the ball is `C^k` exactly when
  it is `C^k` as a map into `E`.
* `LinearIsometry.isSmoothEmbedding_unitClosedBallMap`: a linear isometry `F →ₗᵢ[ℝ] E` restricts
  to a smooth embedding of closed unit balls, in the sense of manifolds with boundary. In charts
  `closedBallChart φ` and `closedBallChart ψ` with `ψ ∘ ι ∘ φ⁻¹` fixing `e₀`, the inversions
  cancel and the map reads as that linear isometry of the model spaces, which is the inclusion of a
  factor of a product decomposition (`LinearIsometry.prodOrthogonalRangeEquiv`). This is the flat
  disc `D² ⊆ D⁴` bounded by a great circle, the slice disc of the unknot.
* `LinearIsometryEquiv.unitClosedBallDiffeomorph`: a linear isometry equivalence restricts to a
  diffeomorphism of closed unit balls.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 1, §4 (manifolds with boundary).
-/

public section

noncomputable section

open Set Metric Function Manifold Module EuclideanGeometry
open scoped Manifold ContDiff InnerProductSpace Topology

namespace TauCeti

variable {n : ℕ} [NeZero n]

/-! ### The inversion onto the half-space -/

section Inversion

local notation "e₀" => (EuclideanSpace.single (0 : Fin _) (1 : ℝ))

/-- The first coordinate of the inversion of `y` in the sphere of radius `√2` centred at `-e₀`. -/
private theorem inversion_apply_zero {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ -e₀) :
    inversion (-e₀) √2 y 0 = (1 - ‖y‖ ^ 2) / ‖y + e₀‖ ^ 2 := by
  have hd : ‖y + e₀‖ ≠ 0 := by
    rwa [norm_ne_zero_iff, ← sub_neg_eq_add, sub_ne_zero]
  have hsq : ‖y + e₀‖ ^ 2 = ‖y‖ ^ 2 + 2 * y 0 + 1 := by
    rw [norm_add_sq_real, EuclideanSpace.inner_single_right, PiLp.norm_single]
    simp
  simp only [inversion, dist_eq_norm, vsub_eq_sub, vadd_eq_add, sub_neg_eq_add, div_pow,
    Real.sq_sqrt zero_le_two, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
    PiLp.single_apply, ite_true, smul_eq_mul]
  field_simp
  rw [hsq]
  ring

private theorem norm_add_single_sq_pos {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ -e₀) :
    0 < ‖y + e₀‖ ^ 2 := by
  have : y + e₀ ≠ 0 := by rwa [← sub_neg_eq_add, sub_ne_zero]
  positivity

/-- The inversion carries the closed unit ball minus its centre into the half-space. -/
private theorem inversion_apply_zero_nonneg_iff {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ -e₀) :
    0 ≤ inversion (-e₀) √2 y 0 ↔ ‖y‖ ≤ 1 := by
  rw [inversion_apply_zero hy, le_div_iff₀ (norm_add_single_sq_pos hy), zero_mul, sub_nonneg,
    sq_le_one_iff₀ (norm_nonneg _)]

/-- The inversion carries the open unit ball into the open half-space. -/
private theorem inversion_apply_zero_pos_iff {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ -e₀) :
    0 < inversion (-e₀) √2 y 0 ↔ ‖y‖ < 1 := by
  rw [inversion_apply_zero hy, div_pos_iff_of_pos_right (norm_add_single_sq_pos hy), sub_pos,
    sq_lt_one_iff₀ (norm_nonneg _)]

/-- The centre of the inversion lies outside the half-space. -/
private theorem ne_neg_single_of_nonneg {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) :
    y ≠ -e₀ := by
  rintro rfl
  norm_num at hy

/-- The inversion carries the half-space back into the closed unit ball. -/
private theorem norm_inversion_le_one {y : EuclideanSpace ℝ (Fin n)} (hy : 0 ≤ y 0) :
    ‖inversion (-e₀) √2 y‖ ≤ 1 := by
  have hc := ne_neg_single_of_nonneg hy
  have hR : (√2 : ℝ) ≠ 0 := by positivity
  rw [← inversion_apply_zero_nonneg_iff ((inversion_eq_center hR).not.2 hc),
    inversion_inversion _ hR]
  exact hy

/-- The inversion is analytic away from its centre. -/
private theorem contDiffAt_inversion {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ -e₀) :
    ContDiffAt ℝ ω (inversion (-e₀) √2) y := by
  have : ContDiffAt ℝ ω (fun z : EuclideanSpace ℝ (Fin n) ↦ √2 / dist z (-e₀)) y :=
    contDiffAt_const.div (contDiffAt_id.dist ℝ contDiffAt_const hy) (dist_ne_zero.2 hy)
  exact ((this.pow 2).smul (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const

end Inversion

/-! ### The charts -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "e₀" => (EuclideanSpace.single (0 : Fin _) (1 : ℝ))

private theorem symm_inversion_mem_closedBall (φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (y : EuclideanHalfSpace n) : φ.symm (inversion (-e₀) √2 y.1) ∈ closedBall (0 : E) 1 := by
  rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
  exact norm_inversion_le_one y.2

/-- The chart of a point of the closed ball lies in the half-space. -/
private theorem zero_le_inversion_apply_zero (φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {x : closedBall (0 : E) 1} (hx : φ x ≠ -e₀) : 0 ≤ inversion (-e₀) √2 (φ x) 0 := by
  rw [inversion_apply_zero_nonneg_iff hx, LinearIsometryEquiv.norm_map]
  exact mem_closedBall_zero_iff.1 x.2

/-- The chart of the closed unit ball attached to a linear isometry
`φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)`: transport along `φ`, then invert in the sphere of radius
`√2` centred at `-e₀`. It is defined on the ball minus `φ.symm (-e₀)`, maps the unit sphere into
the boundary hyperplane `{y | y 0 = 0}`, and its target is the whole half-space. -/
def closedBallChart (φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    OpenPartialHomeomorph (closedBall (0 : E) 1) (EuclideanHalfSpace n) where
  toFun x := (𝓡∂ n).symm (inversion (-e₀) √2 (φ x))
  invFun y := ⟨φ.symm (inversion (-e₀) √2 y.1), symm_inversion_mem_closedBall φ y⟩
  source := {x | φ x ≠ -e₀}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' y _ := by
    simp only [mem_ofPred_eq, LinearIsometryEquiv.apply_symm_apply]
    exact (inversion_eq_center (by positivity)).not.2 (ne_neg_single_of_nonneg y.2)
  left_inv' x hx := by
    have h0 := zero_le_inversion_apply_zero φ hx
    ext1
    simp [modelWithCornersEuclideanHalfSpace_symm_apply_of_le h0,
      inversion_inversion _ (by positivity : (√2 : ℝ) ≠ 0)]
  right_inv' y _ := by
    simp [inversion_inversion _ (by positivity : (√2 : ℝ) ≠ 0),
      modelWithCornersEuclideanHalfSpace_symm_apply_of_le y.2]
  open_source := isOpen_ne_fun (φ.continuous.comp continuous_subtype_val) continuous_const
  open_target := isOpen_univ
  continuousOn_toFun := (𝓡∂ n).continuous_symm.comp_continuousOn <|
    ContinuousOn.inversion continuousOn_const continuousOn_const
      (φ.continuous.comp continuous_subtype_val).continuousOn fun _ hx ↦ hx
  continuousOn_invFun := Continuous.continuousOn <| Continuous.subtype_mk
    (φ.symm.continuous.comp <| Continuous.inversion continuous_const continuous_const
      continuous_subtype_val fun y ↦ ne_neg_single_of_nonneg y.2) (symm_inversion_mem_closedBall φ)

variable (φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))

/-- The chart attached to `φ` is defined away from `φ.symm (-e₀)`. -/
@[simp]
theorem closedBallChart_source :
    (closedBallChart φ).source = {x : closedBall (0 : E) 1 | φ x ≠ -e₀} := (rfl)

/-- The chart attached to `φ` maps onto the whole half-space. -/
@[simp]
theorem closedBallChart_target : (closedBallChart φ).target = univ := (rfl)

/-- The chart attached to `φ` inverts the image of a point under `φ` and reads the result in the
half-space; off the source the result is clamped into the half-space by the model. -/
theorem closedBallChart_apply (x : closedBall (0 : E) 1) :
    closedBallChart φ x = (𝓡∂ n).symm (inversion (-e₀) √2 (φ x)) := (rfl)

/-- On its source, the chart reads a point as the inversion of its image under `φ`. -/
theorem closedBallChart_apply_val {x : closedBall (0 : E) 1} (hx : φ x ≠ -e₀) :
    (closedBallChart φ x).val = inversion (-e₀) √2 (φ x) := by
  rw [closedBallChart_apply,
    modelWithCornersEuclideanHalfSpace_symm_apply_of_le (zero_le_inversion_apply_zero φ hx)]

/-- The inverse of the chart attached to `φ` inverts a point of the half-space and transports it
back along `φ`. -/
@[simp]
theorem closedBallChart_symm_apply_coe (y : EuclideanHalfSpace n) :
    ((closedBallChart φ).symm y : E) = φ.symm (inversion (-e₀) √2 y.val) := (rfl)

/-- The first coordinate of the chart image of `x` is `(1 - ‖x‖ ^ 2) / ‖φ x + e₀‖ ^ 2`. -/
private theorem closedBallChart_apply_val_zero {x : closedBall (0 : E) 1} (hx : φ x ≠ -e₀) :
    (closedBallChart φ x).val 0 = (1 - ‖(x : E)‖ ^ 2) / ‖φ x + e₀‖ ^ 2 := by
  rw [closedBallChart_apply_val φ hx, inversion_apply_zero hx, LinearIsometryEquiv.norm_map]

/-! ### The manifold structure -/

variable [Fact (finrank ℝ E = n)]

/-- The isometry identifying `E` with `EuclideanSpace ℝ (Fin n)` from which the preferred charts
of the closed ball are chosen. -/
private def closedBallIsometry : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  haveI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos <| by
    rw [Fact.out (p := finrank ℝ E = n)]
    exact Nat.pos_of_neZero n
  ((stdOrthonormalBasis ℝ E).reindex (finCongr Fact.out)).repr

/-- The closed unit ball of an `n`-dimensional real inner product space is a charted space
modelled on `EuclideanHalfSpace n`, with the charts `closedBallChart φ` for all linear isometries
`φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)`. Use `atlas_closedBall` and
`exists_chartAt_closedBall_eq` to reason about the charts. -/
@[irreducible, instance] noncomputable def instChartedSpaceClosedBall :
    ChartedSpace (EuclideanHalfSpace n) (closedBall (0 : E) 1) where
  atlas := range closedBallChart
  chartAt x := closedBallChart <| if closedBallIsometry (x : E) = -e₀ then
    closedBallIsometry.trans (LinearIsometryEquiv.neg ℝ) else closedBallIsometry
  mem_chart_source x := by
    split_ifs with h
    · intro h'
      have := congrArg (· 0) (h.symm.trans (by simpa using h'))
      norm_num at this
    · exact h
  chart_mem_atlas _ := mem_range_self _

/-- The atlas of the closed ball consists of the charts `closedBallChart φ`. -/
@[simp]
theorem atlas_closedBall :
    atlas (EuclideanHalfSpace n) (closedBall (0 : E) 1) = range closedBallChart := by
  unfold instChartedSpaceClosedBall
  rfl

/-- The preferred chart of the closed ball at `x` is `closedBallChart φ` for an isometry `φ` not
sending `x` to `-e₀`. -/
theorem exists_chartAt_closedBall_eq (x : closedBall (0 : E) 1) :
    ∃ φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n), φ x ≠ -e₀ ∧
      chartAt (EuclideanHalfSpace n) x = closedBallChart φ := by
  obtain ⟨φ, hφ⟩ : chartAt (EuclideanHalfSpace n) x ∈ range closedBallChart :=
    atlas_closedBall (E := E) (n := n) ▸ chart_mem_atlas (EuclideanHalfSpace n) x
  refine ⟨φ, ?_, hφ.symm⟩
  have := mem_chart_source (EuclideanHalfSpace n) x
  rwa [← hφ, closedBallChart_source] at this

/-- The closed unit ball of an `n`-dimensional real inner product space is an analytic manifold
with boundary. -/
instance instIsManifoldClosedBall : IsManifold (𝓡∂ n) ω (closedBall (0 : E) 1) := by
  refine isManifold_of_contDiffOn _ _ _ ?_
  rw [atlas_closedBall]
  rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
  have hg : ContDiffOn ℝ ω (fun z ↦ inversion (-e₀) √2 (ψ (φ.symm (inversion (-e₀) √2 z))))
      {z | z ≠ -e₀ ∧ ψ (φ.symm (inversion (-e₀) √2 z)) ≠ -e₀} := fun z hz ↦ by
    have h₁ : ContDiffAt ℝ ω (fun z ↦ ψ (φ.symm (inversion (-e₀) √2 z))) z :=
      (ψ.contDiff.comp φ.symm.contDiff).contDiffAt.comp z (contDiffAt_inversion hz.1)
    exact ((contDiffAt_inversion hz.2).comp z h₁).contDiffWithinAt
  have key : ∀ z ∈ (𝓡∂ n).symm ⁻¹' ((closedBallChart φ).symm ≫ₕ closedBallChart ψ).source ∩
      range (𝓡∂ n), ∃ hz : 0 ≤ z 0, ψ ((closedBallChart φ).symm ⟨z, hz⟩) ≠ -e₀ := by
    rintro z ⟨hz, hzr⟩
    rw [range_modelWithCornersEuclideanHalfSpace] at hzr
    refine ⟨hzr, ?_⟩
    have := hz.2
    rwa [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hzr] at this
  refine hg.congr_mono (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · obtain ⟨h0, hψ⟩ := key z hz
    simp only [comp_apply, OpenPartialHomeomorph.coe_trans,
      modelWithCornersEuclideanHalfSpace_symm_apply_of_le h0,
      modelWithCornersEuclideanHalfSpace_apply, closedBallChart_apply_val ψ hψ,
      closedBallChart_symm_apply_coe]
  · obtain ⟨h0, hψ⟩ := key z hz
    exact ⟨ne_neg_single_of_nonneg h0, hψ⟩

/-! ### The boundary is the unit sphere -/

/-- A point of the closed unit ball is a boundary point exactly when it has norm `1`. -/
@[simp]
theorem isBoundaryPoint_closedBall_iff {x : closedBall (0 : E) 1} :
    (𝓡∂ n).IsBoundaryPoint x ↔ ‖(x : E)‖ = 1 := by
  obtain ⟨φ, hx, h⟩ := exists_chartAt_closedBall_eq (n := n) x
  rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range (k := ω) (by simp)
    (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source _ x), h,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  simp [closedBallChart_apply_val_zero φ hx, (norm_add_single_sq_pos hx).ne',
    eq_comm (a := (0 : ℝ)), sub_eq_zero, eq_comm (a := (1 : ℝ)),
    pow_eq_one_iff_of_nonneg (norm_nonneg (x : E))]

/-- A point of the closed unit ball is an interior point exactly when it has norm less than `1`. -/
@[simp]
theorem isInteriorPoint_closedBall_iff {x : closedBall (0 : E) 1} :
    (𝓡∂ n).IsInteriorPoint x ↔ ‖(x : E)‖ < 1 := by
  obtain ⟨φ, hx, h⟩ := exists_chartAt_closedBall_eq (n := n) x
  rw [ModelWithCorners.isInteriorPoint_iff_mem_interior_range (k := ω) (by simp)
    (IsManifold.chart_mem_maximalAtlas x) (mem_chart_source _ x), h,
    interior_range_modelWithCornersEuclideanHalfSpace]
  simp [closedBallChart_apply_val φ hx, inversion_apply_zero_pos_iff hx]

/-- The manifold boundary of the closed unit ball is the unit sphere. -/
theorem boundary_closedBall :
    (𝓡∂ n).boundary (closedBall (0 : E) 1) = Subtype.val ⁻¹' sphere (0 : E) 1 := by
  ext x
  exact isBoundaryPoint_closedBall_iff.trans mem_sphere_zero_iff_norm.symm

/-! ### Smooth maps to and from the closed ball -/

/-- The inclusion of the closed unit ball into `E` is analytic. -/
theorem contMDiff_subtypeVal_closedBall {k : ℕ∞ω} :
    ContMDiff (𝓡∂ n) 𝓘(ℝ, E) k (Subtype.val : closedBall (0 : E) 1 → E) := by
  intro x
  obtain ⟨φ, -, h⟩ := exists_chartAt_closedBall_eq (n := n) x
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have hmem : extChartAt (𝓡∂ n) x x ∈ range (𝓡∂ n) := extChartAt_target_subset_range x
    (mem_extChartAt_target x)
  rw [range_modelWithCornersEuclideanHalfSpace] at hmem
  refine ((φ.symm.contDiff.contDiffAt.comp _ (contDiffAt_inversion (ne_neg_single_of_nonneg
    hmem))).contDiffWithinAt.of_le le_top).congr_of_mem (fun z hz ↦ ?_) ?_
  · rw [range_modelWithCornersEuclideanHalfSpace] at hz
    simp [h, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hz]
  · rw [range_modelWithCornersEuclideanHalfSpace]
    exact hmem

/-! ### Orientability -/

omit [Fact (finrank ℝ E = n)] in
/-- Near a point of its domain, the coordinate change from the chart attached to `φ` to the chart
attached to `ψ`, read in the model, is `y ↦ inversion (ψ (φ⁻¹ (inversion y)))`. -/
private theorem closedBallChart_symm_trans_eventuallyEq (φ ψ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {z : EuclideanHalfSpace n} (hz : z ∈ ((closedBallChart φ).symm ≫ₕ closedBallChart ψ).source) :
    (𝓡∂ n) ∘ ((closedBallChart φ).symm ≫ₕ closedBallChart ψ) ∘ (𝓡∂ n).symm
      =ᶠ[𝓝[range (𝓡∂ n)] ((𝓡∂ n) z)]
        fun y ↦ inversion (-e₀) √2 (φ.symm.trans ψ (inversion (-e₀) √2 y)) := by
  have hopen : IsOpen ((𝓡∂ n).symm ⁻¹' ((closedBallChart φ).symm ≫ₕ closedBallChart ψ).source) :=
    ((closedBallChart φ).symm ≫ₕ closedBallChart ψ).open_source.preimage (𝓡∂ n).continuous_symm
  filter_upwards [inter_mem_nhdsWithin (range (𝓡∂ n))
    (hopen.mem_nhds (by rwa [mem_preimage, ModelWithCorners.left_inv]))] with y ⟨hyr, hy⟩
  rw [range_modelWithCornersEuclideanHalfSpace] at hyr
  have hψ : ψ ((closedBallChart φ).symm ⟨y, hyr⟩) ≠ -e₀ := by
    have := hy.2
    rwa [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hyr] at this
  simp only [comp_apply, OpenPartialHomeomorph.coe_trans,
    modelWithCornersEuclideanHalfSpace_symm_apply_of_le hyr,
    modelWithCornersEuclideanHalfSpace_apply, closedBallChart_apply_val ψ hψ,
    closedBallChart_symm_apply_coe, LinearIsometryEquiv.trans_apply]

omit [Fact (finrank ℝ E = n)] in
/-- The coordinate change from the chart attached to `φ` to the chart attached to `ψ` preserves
orientation when the linear isometry `ψ ∘ φ⁻¹` of the model space does. In the model it is
`y ↦ inversion (ψ (φ⁻¹ (inversion y)))`, and each of the two inversions reverses orientation
(`EuclideanGeometry.det_fderiv_inversion_neg`). -/
private theorem orientationPreservingOn_closedBallChart_symm_trans
    (φ ψ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (h : 0 < (LinearEquiv.det (φ.symm.trans ψ).toLinearEquiv : ℝ)) :
    OrientationPreservingOn (𝓡∂ n) ((closedBallChart φ).symm ≫ₕ closedBallChart ψ)
      ((closedBallChart φ).symm ≫ₕ closedBallChart ψ).source := by
  set A := φ.symm.trans ψ
  set inv := inversion (-e₀) √2 (P := EuclideanSpace ℝ (Fin n))
  have hR : (√2 : ℝ) ≠ 0 := by positivity
  rw [orientationPreservingOn_iff]
  intro z hz
  have h₁ : (𝓡∂ n) z ≠ -e₀ := ne_neg_single_of_nonneg z.2
  have h₂ : A (inv ((𝓡∂ n) z)) ≠ -e₀ := hz.2
  have d₁ : HasFDerivAt inv (fderiv ℝ inv ((𝓡∂ n) z)) ((𝓡∂ n) z) :=
    (hasFDerivAt_inversion h₁).differentiableAt.hasFDerivAt
  have d₂ : HasFDerivAt inv (fderiv ℝ inv (A (inv ((𝓡∂ n) z)))) (A (inv ((𝓡∂ n) z))) :=
    (hasFDerivAt_inversion h₂).differentiableAt.hasFDerivAt
  have dA : HasFDerivAt (fun y ↦ A y) (A.toContinuousLinearEquiv : _ →L[ℝ] _) (inv ((𝓡∂ n) z)) :=
    A.toContinuousLinearEquiv.hasFDerivAt
  have heq := closedBallChart_symm_trans_eventuallyEq φ ψ hz
  have hFW := (d₂.comp ((𝓡∂ n) z) (dA.comp ((𝓡∂ n) z) d₁)).hasFDerivWithinAt.congr_of_eventuallyEq
    heq (heq.eq_of_nhdsWithin (mem_range_self z))
  refine ⟨hFW.differentiableWithinAt, ?_⟩
  rw [hFW.fderivWithin (𝓡∂ n).uniqueDiffWithinAt_image, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, LinearMap.det_comp]
  -- The linear map underlying the continuous linear map of `A` is that of its linear equivalence.
  have hA : LinearMap.det ((A.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      (LinearEquiv.det A.toLinearEquiv : ℝ) := by
    rw [LinearEquiv.coe_det]
    rfl
  rw [hA]
  exact mul_pos_of_neg_of_neg (det_fderiv_inversion_neg hR h₂)
    (mul_neg_of_pos_of_neg h (det_fderiv_inversion_neg hR h₁))

/-- In dimension at least two, the closed unit ball is orientable: the charts
`closedBallChart φ` with `φ` in a fixed orientation class form an oriented atlas, since the
coordinate change between two of them is a composite of two inversions, each reversing
orientation, and a linear isometry of positive determinant.

The hypothesis `2 ≤ n` cannot be dropped: a chart of `D¹ = [-1, 1]` at either endpoint takes values
in the half-line `[0, ∞)`, so it is increasing at `-1` and decreasing at `1`, and no atlas of `D¹`
modelled on the half-line has all its coordinate changes orientation preserving. -/
theorem orientable_closedBall (hn : 2 ≤ n) {k : ℕ∞ω} [NeZero k] :
    Orientable (𝓡∂ n) k (closedBall (0 : E) 1) := by
  let φ₀ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := closedBallIsometry
  let S := {φ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) |
    0 < (LinearEquiv.det (φ₀.symm.trans φ).toLinearEquiv : ℝ)}
  refine ⟨⟨closedBallChart '' S, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨φ, -, rfl⟩
    exact IsManifold.maximalAtlas_subset_of_le le_top
      (IsManifold.subset_maximalAtlas (atlas_closedBall (E := E) (n := n) ▸ mem_range_self φ))
  · intro x
    by_cases hx : φ₀ x = -e₀
    · obtain ⟨r, hr, hr'⟩ := exists_det_eq_one_apply_eq_neg
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n) ▸ hn) (v := -e₀) (by simp)
      refine ⟨closedBallChart (φ₀.trans r), ⟨φ₀.trans r, ?_, rfl⟩, ?_⟩
      · have : φ₀.symm.trans (φ₀.trans r) = r := by ext; simp
        simp only [S, mem_ofPred_eq, this, hr, zero_lt_one]
      · intro h
        rw [LinearIsometryEquiv.trans_apply, hx, hr', neg_neg] at h
        have := congrArg (· (0 : Fin n)) h
        norm_num at this
    · refine ⟨closedBallChart φ₀, ⟨φ₀, ?_, rfl⟩, hx⟩
      simp [S]
  · rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    have hdet (φ ψ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (hφ : φ ∈ S) (hψ : ψ ∈ S) :
        0 < (LinearEquiv.det (φ.symm.trans ψ).toLinearEquiv : ℝ) := by
      have : φ.symm.trans ψ = (φ₀.symm.trans φ).symm.trans (φ₀.symm.trans ψ) := by ext; simp
      rw [this, LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.det_trans, Units.val_mul,
        LinearIsometryEquiv.toLinearEquiv_symm, LinearEquiv.det_symm, map_inv,
        Units.val_inv_eq_inv_val]
      exact mul_pos hψ (inv_pos.2 hφ)
    rw [mem_orientationPreservingGroupoid_iff, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, ← OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact ⟨orientationPreservingOn_closedBallChart_symm_trans φ ψ (hdet φ ψ hφ hψ),
      orientationPreservingOn_closedBallChart_symm_trans ψ φ (hdet ψ φ hψ hφ)⟩

/-! ### The closed unit ball of `EuclideanSpace ℝ (Fin n)` -/

/-- The closed unit ball of `EuclideanSpace ℝ (Fin n)` is a charted space modelled on
`EuclideanHalfSpace n`. -/
instance instChartedSpaceClosedBallEuclideanSpace :
    ChartedSpace (EuclideanHalfSpace n) (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  instChartedSpaceClosedBall

/-- The closed unit ball of `EuclideanSpace ℝ (Fin n)` is an analytic manifold with boundary. -/
instance instIsManifoldClosedBallEuclideanSpace :
    IsManifold (𝓡∂ n) ω (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  have := Fact.mk (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  instIsManifoldClosedBall

variable {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A map into the closed unit ball is `C^k` exactly when it is `C^k` as a map into `E`. -/
theorem contMDiff_iff_comp_subtypeVal_closedBall {k : ℕ∞ω} {f : M → closedBall (0 : E) 1} :
    ContMDiff I (𝓡∂ n) k f ↔ ContMDiff I 𝓘(ℝ, E) k (Subtype.val ∘ f) := by
  refine ⟨contMDiff_subtypeVal_closedBall.comp, fun hf x ↦ ?_⟩
  obtain ⟨φ, hx, h⟩ := exists_chartAt_closedBall_eq (n := n) (f x)
  have hcont : Continuous f := continuous_induced_rng.2 hf.continuous
  rw [contMDiffAt_iff_target]
  refine ⟨hcont.continuousAt, ?_⟩
  have hg : ContDiffAt ℝ k (fun y : E ↦ inversion (-e₀) √2 (φ y)) (f x) :=
    ((contDiffAt_inversion hx).comp _ φ.contDiff.contDiffAt).of_le le_top
  refine (hg.comp_contMDiffAt (f := Subtype.val ∘ f) (hf x)).congr_of_eventuallyEq ?_
  filter_upwards [hcont.continuousAt.preimage_mem_nhds
    ((closedBallChart φ).open_source.mem_nhds hx)] with y hy
  simp [h, closedBallChart_apply_val φ hy]

/-! ### Smooth embeddings of closed balls induced by linear isometries -/

section LinearIsometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {m : ℕ} [NeZero m]
  [Fact (finrank ℝ F = m)] (ι : F →ₗᵢ[ℝ] E)

omit [Fact (finrank ℝ F = m)] in
/-- Given a chart isometry `φ` of the closed ball of `F`, there is a chart isometry `ψ` of the
closed ball of `E` in which `ι` reads as a linear isometry `L` of the model spaces fixing `e₀`, the
negative of the centre of the inversions defining the charts. -/
private theorem exists_linearIsometryEquiv_comp_eq (φ : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ (ψ : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
      (L : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
      L (EuclideanSpace.single (0 : Fin m) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∧
        ∀ y, ψ (ι y) = L (φ y) := by
  set w : EuclideanSpace ℝ (Fin n) :=
    closedBallIsometry (ι (φ.symm (EuclideanSpace.single (0 : Fin m) (1 : ℝ))))
  have hw : ‖w‖ = ‖(EuclideanSpace.single (0 : Fin n) (1 : ℝ))‖ := by simp [w]
  refine ⟨closedBallIsometry.trans (ℝ ∙ (w - e₀))ᗮ.reflection,
    (closedBallIsometry.trans (ℝ ∙ (w - e₀))ᗮ.reflection).toLinearIsometry.comp
      (ι.comp φ.symm.toLinearIsometry), ?_, fun y ↦ by simp⟩
  simpa [w] using Submodule.reflection_sub hw

variable {k : ℕ∞ω}

/-- The restriction of a linear isometry to the closed unit balls is an immersion at every point,
in the sense of manifolds with boundary: in suitable inversion charts it reads as a linear
isometry of the model spaces, hence as the inclusion of a factor of a product decomposition. -/
theorem _root_.LinearIsometry.isImmersionAt_unitClosedBallMap (x : closedBall (0 : F) 1) :
    IsImmersionAt (𝓡∂ m) (𝓡∂ n) k ι.unitClosedBallMap x := by
  obtain ⟨φ, hφx, -⟩ := exists_chartAt_closedBall_eq (n := m) x
  obtain ⟨ψ, L, hL, hψ⟩ := exists_linearIsometryEquiv_comp_eq (n := n) ι φ
  have hL' : L (-e₀) = -e₀ := by rw [map_neg, hL]
  have hne : ∀ y : closedBall (0 : F) 1, φ y ≠ -e₀ → ψ (ι.unitClosedBallMap y) ≠ -e₀ := by
    intro y hy h
    rw [LinearIsometry.coe_unitClosedBallMap_apply, hψ, ← hL', L.map_eq_iff] at h
    exact hy h
  refine (IsImmersionAtOfComplement.mk_of_charts L.prodOrthogonalRangeEquiv (closedBallChart φ)
    (closedBallChart ψ) hφx (hne x hφx)
    (IsManifold.maximalAtlas_subset_of_le le_top
      (IsManifold.subset_maximalAtlas (atlas_closedBall (E := F) (n := m) ▸ mem_range_self φ)))
    (IsManifold.maximalAtlas_subset_of_le le_top
      (IsManifold.subset_maximalAtlas (atlas_closedBall (E := E) (n := n) ▸ mem_range_self ψ)))
    (fun y hy ↦ hne y hy) fun u hu ↦ ?_).isImmersionAt
  rw [OpenPartialHomeomorph.extend_target', closedBallChart_target, image_univ,
    range_modelWithCornersEuclideanHalfSpace] at hu
  have hu : 0 ≤ u 0 := hu
  have hLu : 0 ≤ L u 0 := by rw [LinearIsometry.apply_eq_of_map_single hL]; exact hu
  -- `L` fixes the centre `-e₀` of the inversion, so it commutes with the inversion.
  have key (y : EuclideanSpace ℝ (Fin m)) :
      inversion (-e₀) √2 (L y) = L (inversion (-e₀) √2 y) := by
    rw [L.map_inversion, hL']
  simp only [comp_apply, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersEuclideanHalfSpace_symm_apply_of_le hu, closedBallChart_apply,
    LinearIsometry.coe_unitClosedBallMap_apply, closedBallChart_symm_apply_coe, hψ,
    LinearIsometryEquiv.apply_symm_apply, key, inversion_inversion _ (by positivity : (√2 : ℝ) ≠ 0),
    modelWithCornersEuclideanHalfSpace_symm_apply_of_le hLu,
    modelWithCornersEuclideanHalfSpace_apply, LinearIsometry.prodOrthogonalRangeEquiv_apply_zero]

/-- The restriction of a linear isometry to the closed unit balls is a `C^k` immersion. -/
theorem _root_.LinearIsometry.isImmersion_unitClosedBallMap :
    IsImmersion (𝓡∂ m) (𝓡∂ n) k ι.unitClosedBallMap :=
  isImmersion_iff_forall_isImmersionAt.2 ι.isImmersionAt_unitClosedBallMap

/-- The restriction of a linear isometry to the closed unit balls is a `C^k` smooth embedding of
manifolds with boundary. -/
theorem _root_.LinearIsometry.isSmoothEmbedding_unitClosedBallMap :
    IsSmoothEmbedding (𝓡∂ m) (𝓡∂ n) k ι.unitClosedBallMap :=
  ⟨ι.isImmersion_unitClosedBallMap, ι.isEmbedding_unitClosedBallMap⟩

/-- A linear isometry equivalence restricts to a `C^k` diffeomorphism of closed unit balls, in the
sense of manifolds with boundary. -/
def _root_.LinearIsometryEquiv.unitClosedBallDiffeomorph (e : F ≃ₗᵢ[ℝ] E) :
    closedBall (0 : F) 1 ≃ₘ^k⟮𝓡∂ m, 𝓡∂ n⟯ closedBall (0 : E) 1 where
  toFun := e.toLinearIsometry.unitClosedBallMap
  invFun := e.symm.toLinearIsometry.unitClosedBallMap
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  contMDiff_toFun := e.toLinearIsometry.isSmoothEmbedding_unitClosedBallMap.contMDiff
  contMDiff_invFun := e.symm.toLinearIsometry.isSmoothEmbedding_unitClosedBallMap.contMDiff

@[simp]
theorem _root_.LinearIsometryEquiv.coe_unitClosedBallDiffeomorph (e : F ≃ₗᵢ[ℝ] E) :
    ⇑(e.unitClosedBallDiffeomorph (m := m) (n := n) (k := k)) =
      e.toLinearIsometry.unitClosedBallMap :=
  (rfl)

@[simp]
theorem _root_.LinearIsometryEquiv.unitClosedBallDiffeomorph_symm (e : F ≃ₗᵢ[ℝ] E) :
    (e.unitClosedBallDiffeomorph (m := m) (n := n) (k := k)).symm =
      e.symm.unitClosedBallDiffeomorph :=
  (rfl)

end LinearIsometry

end TauCeti
