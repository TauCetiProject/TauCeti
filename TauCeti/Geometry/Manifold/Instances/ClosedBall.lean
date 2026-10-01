/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Calculus
public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Boundary.Basic

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
* `TauCeti.contMDiff_subtypeVal_closedBall`: the inclusion into `E` is analytic.
* `TauCeti.contMDiff_iff_comp_subtypeVal_closedBall`: a map into the ball is `C^k` exactly when
  it is `C^k` as a map into `E`.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 1, §4 (manifolds with boundary).
-/

public section

noncomputable section

open Set Metric Function Module EuclideanGeometry
open scoped Manifold ContDiff

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
    (chart_mem_atlas _ x) (mem_chart_source _ x), h,
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
    (chart_mem_atlas _ x) (mem_chart_source _ x), h,
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

end TauCeti
