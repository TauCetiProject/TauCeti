/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.CompletelyContinuous
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix

/-!
# Row-compact operators between model spaces

Let `R` be a normed ring and `I`, `J` discrete index types. A continuous linear map
`u : C₀(J, R) →L[R] C₀(I, R)` has the matrix `aᵢⱼ = u.matrixCoeff i j`, whose rows are indexed by
output coordinates. Its **row norms** are the suprema `rᵢ(u) = ⨆ j, ‖aᵢⱼ‖`
(`ContinuousLinearMap.rowNorm`), and `u` is **row compact** (`ContinuousLinearMap.IsRowCompact`)
if its entries are uniformly bounded and its row norms tend to zero along the cofinite filter.
The bound on the entries keeps the real suprema meaningful; it is automatic over Tate scalars.
Row compactness is the matrix condition of Serre's criterion for complete continuity. For an
endomorphism `u` of `C₀(I, R)` over a complete commutative ultrametric normed field, it is also
the condition under which Serre's Fredholm determinant `det (1 - T u)` is an entire power series;
that determinant is not developed here.

Every column of the matrix of a continuous linear map tends to zero, but its rows need not: the
identity of `C₀(I, R)` has all row norms one, so it is not row compact on an infinite index type
(`ContinuousLinearMap.not_isRowCompact_id`).

Over ultrametric Tate scalars the operator norm is the supremum of the row norms
(`ContinuousLinearMap.ringOpNorm_eq_iSup_rowNorm`), and row compactness says exactly that the
*output truncations* `π_S ∘ u` approximate `u` in operator norm as the finite set `S` of output
coordinates grows (`ContinuousLinearMap.isRowCompact_iff_tendsto_ringOpNorm_sub_indicatorCLM_comp`).
Here `π_S = ZeroAtInftyContinuousMap.indicatorCLM R S` is the coordinate projection. These
truncations have finite rank, so every row-compact map is completely continuous
(`ContinuousLinearMap.IsRowCompact.isCompletelyContinuous`), over any ultrametric normed ring and
with no Noetherian hypothesis. The *input* truncations `u ∘ π_S` need not converge, because a
row-compact map of rank one can have a row of entries of norm one.

Row-compact maps form a closed two-sided operator ideal over ultrametric Tate scalars: they are
stable under sums and scalar multiples, under composition on either side with continuous linear
maps (`ContinuousLinearMap.IsRowCompact.comp_clm`, `ContinuousLinearMap.IsRowCompact.clm_comp`),
and under limits in operator norm (`ContinuousLinearMap.isRowCompact_of_tendsto`).

## Main definitions

* `ContinuousLinearMap.rowNorm`: the row norms of the matrix of a map between model spaces.
* `ContinuousLinearMap.IsRowCompact`: bounded entries and row norms tending to zero.

## Main results

* `ContinuousLinearMap.isRowCompact_of_norm_matrixCoeff_le`: a null row majorant of the entries
  gives row compactness.
* `ContinuousLinearMap.isRowCompact_of_apply_single_eq_sum`: columns that are uniformly bounded
  combinations of finitely many vectors give a row-compact map.
* `ContinuousLinearMap.ringOpNorm_eq_iSup_rowNorm`: `‖u‖ = ⨆ i, rᵢ(u)` over ultrametric Tate
  scalars.
* `ContinuousLinearMap.isRowCompact_iff_tendsto_ringOpNorm_sub_indicatorCLM_comp`: row compactness
  is norm convergence of the output truncations.
* `ContinuousLinearMap.IsRowCompact.tendsto_ringOpNorm_indicatorCLM_comp_sub`: the output
  truncations of a row-compact map converge to it in operator norm.
* `ContinuousLinearMap.IsRowCompact.isCompletelyContinuous`: row-compact maps are completely
  continuous.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §3.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I J K L R : Type*} [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J]
  [DecidableEq J]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

section SeminormedRing

variable [SeminormedRing R]

/-- The **row norms** of a continuous linear map `u : C₀(J, R) →L[R] C₀(I, R)`: the norm of row
`i` of its matrix is `⨆ j, ‖u.matrixCoeff i j‖`. As a real supremum this is only meaningful for a
bounded row, which is automatic over Tate scalars (`ContinuousLinearMap.rowNorm_le_ringOpNorm`). -/
noncomputable def rowNorm (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) : ℝ :=
  ⨆ j, ‖u.matrixCoeff i j‖

theorem rowNorm_def (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) :
    u.rowNorm i = ⨆ j, ‖u.matrixCoeff i j‖ :=
  (rfl)

theorem rowNorm_nonneg (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) : 0 ≤ u.rowNorm i :=
  Real.iSup_nonneg fun _ ↦ norm_nonneg _

/-- A bound on every entry of a row bounds its row norm. -/
theorem rowNorm_le_of_forall_le {u : C₀(J, R) →L[R] C₀(I, R)} {i : I} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j, ‖u.matrixCoeff i j‖ ≤ C) : u.rowNorm i ≤ C :=
  Real.iSup_le h hC

/-- In a bounded row, every entry is bounded by the row norm. -/
theorem norm_matrixCoeff_le_rowNorm_of_le {u : C₀(J, R) →L[R] C₀(I, R)} {i : I} {C : ℝ}
    (h : ∀ j, ‖u.matrixCoeff i j‖ ≤ C) (j : J) : ‖u.matrixCoeff i j‖ ≤ u.rowNorm i :=
  le_ciSup ⟨C, by rintro _ ⟨j, rfl⟩; exact h j⟩ j

/-- A continuous linear map between model spaces is **row compact** if the entries of its matrix
are uniformly bounded and its row norms tend to zero along the cofinite filter of output indices.
The bound is automatic over Tate scalars (`ContinuousLinearMap.isRowCompact_iff_tendsto_rowNorm`);
it is part of the definition so that the real suprema defining the row norms are meaningful. -/
def IsRowCompact (u : C₀(J, R) →L[R] C₀(I, R)) : Prop :=
  (∃ C, ∀ i j, ‖u.matrixCoeff i j‖ ≤ C) ∧ Tendsto u.rowNorm cofinite (𝓝 0)

theorem isRowCompact_iff {u : C₀(J, R) →L[R] C₀(I, R)} :
    u.IsRowCompact ↔
      (∃ C, ∀ i j, ‖u.matrixCoeff i j‖ ≤ C) ∧ Tendsto u.rowNorm cofinite (𝓝 0) :=
  Iff.rfl

theorem IsRowCompact.tendsto_rowNorm {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) :
    Tendsto u.rowNorm cofinite (𝓝 0) :=
  hu.2

/-- The entries of a row-compact map are bounded by its row norms. -/
theorem IsRowCompact.norm_matrixCoeff_le_rowNorm {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (i : I) (j : J) : ‖u.matrixCoeff i j‖ ≤ u.rowNorm i :=
  have ⟨_, hC⟩ := hu.1
  norm_matrixCoeff_le_rowNorm_of_le (hC i) j

/-- **Row majorants**: if every entry of row `i` is bounded by `r i`, where `r` tends to zero
along the cofinite filter, then `u` is row compact. -/
theorem isRowCompact_of_norm_matrixCoeff_le {u : C₀(J, R) →L[R] C₀(I, R)} {r : I → ℝ}
    (hr : Tendsto r cofinite (𝓝 0)) (h : ∀ i j, ‖u.matrixCoeff i j‖ ≤ r i) : u.IsRowCompact := by
  obtain ⟨C, hC⟩ := hr.bddAbove_range_of_cofinite
  refine ⟨⟨C, fun i j ↦ (h i j).trans (hC ⟨i, rfl⟩)⟩, squeeze_zero (rowNorm_nonneg u)
    (fun i ↦ rowNorm_le_of_forall_le (le_max_right (r i) 0) fun j ↦ (h i j).trans
      (le_max_left _ _)) (by simpa using hr.max (tendsto_const_nhds (x := (0 : ℝ))))⟩

/-- **Bounded finite expansions of the columns give row decay.** If every column
`u (single j 1)` of `u` is a combination `∑ k, a k • w k` of a fixed finite family `w` with
coefficients of norm at most `B`, then `u` is row compact: row `i` is bounded by
`∑ k, B * ‖w k i‖`. -/
theorem isRowCompact_of_apply_single_eq_sum [DiscreteTopology I] {ι : Type*} [Fintype ι]
    {u : C₀(J, R) →L[R] C₀(I, R)} (w : ι → C₀(I, R)) {B : ℝ}
    (h : ∀ j, ∃ a : ι → R, (∀ k, ‖a k‖ ≤ B) ∧
      u (ZeroAtInftyContinuousMap.single j 1) = ∑ k, a k • w k) :
    u.IsRowCompact := by
  refine isRowCompact_of_norm_matrixCoeff_le (r := fun i ↦ ∑ k, B * ‖w k i‖) ?_ fun i j ↦ ?_
  · simpa using tendsto_finsetSum _ fun k _ ↦ (w k).tendsto_cofinite.norm.const_mul B
  · obtain ⟨a, ha, hj⟩ := h j
    calc ‖u.matrixCoeff i j‖ = ‖∑ k, a k * w k i‖ := by
          simp [matrixCoeff_apply, hj]
      _ ≤ ∑ k, ‖a k * w k i‖ := norm_sum_le _ _
      _ ≤ ∑ k, B * ‖w k i‖ := Finset.sum_le_sum fun k _ ↦
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _))

@[simp]
theorem isRowCompact_zero : (0 : C₀(J, R) →L[R] C₀(I, R)).IsRowCompact :=
  isRowCompact_of_norm_matrixCoeff_le tendsto_const_nhds fun _ _ ↦ by simp

theorem IsRowCompact.add {u v : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (hv : v.IsRowCompact) : (u + v).IsRowCompact := by
  refine isRowCompact_of_norm_matrixCoeff_le
    (by simpa using hu.tendsto_rowNorm.add hv.tendsto_rowNorm) fun i j ↦ ?_
  rw [matrixCoeff_add, Matrix.add_apply]
  exact (norm_add_le _ _).trans
    (add_le_add (hu.norm_matrixCoeff_le_rowNorm i j) (hv.norm_matrixCoeff_le_rowNorm i j))

theorem IsRowCompact.neg {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) :
    (-u).IsRowCompact :=
  isRowCompact_of_norm_matrixCoeff_le hu.tendsto_rowNorm fun i j ↦ by
    simpa using hu.norm_matrixCoeff_le_rowNorm i j

@[simp]
theorem isRowCompact_neg_iff {u : C₀(J, R) →L[R] C₀(I, R)} :
    (-u).IsRowCompact ↔ u.IsRowCompact :=
  ⟨fun hu ↦ neg_neg u ▸ hu.neg, IsRowCompact.neg⟩

theorem IsRowCompact.sub {u v : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (hv : v.IsRowCompact) : (u - v).IsRowCompact :=
  sub_eq_add_neg u v ▸ hu.add hv.neg

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing R]

/-- Scalar multiples of row-compact maps are row compact. -/
theorem IsRowCompact.smul {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) (c : R) :
    (c • u).IsRowCompact := by
  refine isRowCompact_of_norm_matrixCoeff_le
    (by simpa using hu.tendsto_rowNorm.const_mul ‖c‖) fun i j ↦ ?_
  rw [matrixCoeff_smul, Matrix.smul_apply, smul_eq_mul]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
    (hu.norm_matrixCoeff_le_rowNorm i j) (norm_nonneg c))

end SeminormedCommRing

section Tate

variable [SeminormedRing R] [TauCeti.NormedRing.IsTate R]

/-- Over Tate scalars, every row norm is bounded by the operator norm. -/
theorem rowNorm_le_ringOpNorm (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) : u.rowNorm i ≤ ‖u‖ :=
  rowNorm_le_of_forall_le (ringOpNorm_nonneg u) (u.norm_matrixCoeff_le i)

/-- Over Tate scalars, every entry is bounded by its row norm. -/
theorem norm_matrixCoeff_le_rowNorm (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) :
    ‖u.matrixCoeff i j‖ ≤ u.rowNorm i :=
  norm_matrixCoeff_le_rowNorm_of_le (u.norm_matrixCoeff_le i) j

/-- A row norm is bounded by the operator-norm distance to another map plus its row norm. -/
theorem rowNorm_le_ringOpNorm_sub_add (u v : C₀(J, R) →L[R] C₀(I, R)) (i : I) :
    u.rowNorm i ≤ ‖u - v‖ + v.rowNorm i := by
  refine rowNorm_le_of_forall_le
    (add_nonneg (ringOpNorm_nonneg _) (v.rowNorm_nonneg i)) fun j ↦ ?_
  calc ‖u.matrixCoeff i j‖ = ‖(u - v).matrixCoeff i j + v.matrixCoeff i j‖ := by simp
    _ ≤ ‖u - v‖ + v.rowNorm i :=
      (norm_add_le _ _).trans (add_le_add ((u - v).norm_matrixCoeff_le i j)
        (v.norm_matrixCoeff_le_rowNorm i j))

/-- Over Tate scalars, a row norm is at most `C ≥ 0` exactly when every entry of the row is. -/
theorem rowNorm_le_iff {u : C₀(J, R) →L[R] C₀(I, R)} {i : I} {C : ℝ} (hC : 0 ≤ C) :
    u.rowNorm i ≤ C ↔ ∀ j, ‖u.matrixCoeff i j‖ ≤ C :=
  ⟨fun h j ↦ (u.norm_matrixCoeff_le_rowNorm i j).trans h, rowNorm_le_of_forall_le hC⟩

/-- Over Tate scalars, row compactness only asks the row norms to tend to zero. -/
theorem isRowCompact_iff_tendsto_rowNorm {u : C₀(J, R) →L[R] C₀(I, R)} :
    u.IsRowCompact ↔ Tendsto u.rowNorm cofinite (𝓝 0) :=
  ⟨IsRowCompact.tendsto_rowNorm, fun h ↦ ⟨⟨‖u‖, u.norm_matrixCoeff_le⟩, h⟩⟩

/-- Over Tate scalars, every continuous linear map between model spaces on a finite output index
type is row compact. -/
theorem isRowCompact_of_finite [Finite I] (u : C₀(J, R) →L[R] C₀(I, R)) : u.IsRowCompact := by
  rw [isRowCompact_iff_tendsto_rowNorm, cofinite_eq_bot]
  exact tendsto_bot

/-- **Closedness**: over Tate scalars, a limit in operator norm of row-compact maps
is row compact. -/
theorem isRowCompact_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : C₀(J, R) →L[R] C₀(I, R)} {v : ι → C₀(J, R) →L[R] C₀(I, R)}
    (h : Tendsto (fun n ↦ ‖u - v n‖) l (𝓝 0)) (hv : ∀ᶠ n in l, (v n).IsRowCompact) :
    u.IsRowCompact := by
  refine isRowCompact_iff_tendsto_rowNorm.2 (tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall
    fun i ↦ ha.trans_le (u.rowNorm_nonneg i), fun ε hε ↦ ?_⟩)
  obtain ⟨n, hvn, hn⟩ := (hv.and (h.eventually_lt_const (half_pos hε))).exists
  filter_upwards [hvn.tendsto_rowNorm.eventually_lt_const (half_pos hε)] with i hi
  exact lt_of_le_of_lt (u.rowNorm_le_ringOpNorm_sub_add (v n) i)
    (add_halves ε ▸ add_lt_add hn hi)

end Tate

/-- **The identity is not row compact** on an infinite index type over a nonzero norm-one ring:
every row of its matrix has norm one. -/
theorem not_isRowCompact_id [SeminormedRing R] [NormOneClass R] [Infinite J] :
    ¬(ContinuousLinearMap.id R C₀(J, R)).IsRowCompact := by
  intro h
  have hrow (i : J) : (ContinuousLinearMap.id R C₀(J, R)).rowNorm i = 1 := by
    refine le_antisymm (rowNorm_le_of_forall_le zero_le_one fun j ↦ ?_) ?_
    · by_cases hij : i = j <;> simp [hij]
    · simpa using h.norm_matrixCoeff_le_rowNorm i i
  have := h.tendsto_rowNorm
  rw [show (ContinuousLinearMap.id R C₀(J, R)).rowNorm = fun _ ↦ 1 from funext hrow] at this
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

section Ultrametric

variable [NormedRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]

/-- **The sup-row norm**: over ultrametric Tate scalars, the operator norm of a map between
model spaces is the supremum of its row norms. -/
theorem ringOpNorm_eq_iSup_rowNorm (u : C₀(J, R) →L[R] C₀(I, R)) : ‖u‖ = ⨆ i, u.rowNorm i := by
  have hbdd : BddAbove (Set.range u.rowNorm) :=
    ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact u.rowNorm_le_ringOpNorm i⟩
  refine le_antisymm (u.ringOpNorm_le_of_forall_norm_matrixCoeff_le
    (Real.iSup_nonneg u.rowNorm_nonneg) fun i j ↦ ?_) ?_
  · exact (u.norm_matrixCoeff_le_rowNorm i j).trans (le_ciSup hbdd i)
  · exact Real.iSup_le u.rowNorm_le_ringOpNorm (ringOpNorm_nonneg u)

/-- Over ultrametric Tate scalars, the `i`-th coordinate of `u x` is bounded by the row norm
`rᵢ(u)` times `‖x‖`. -/
theorem norm_apply_apply_le_rowNorm_mul (u : C₀(J, R) →L[R] C₀(I, R)) (x : C₀(J, R)) (i : I) :
    ‖u x i‖ ≤ u.rowNorm i * ‖x‖ := by
  rw [← (u.hasSum_mul_matrixCoeff x i).tsum_eq, mul_comm]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg x) (u.rowNorm_nonneg i)) fun j ↦ (norm_mul_le _ _).trans ?_
  exact mul_le_mul (norm_coe_le_norm x j) (u.norm_matrixCoeff_le_rowNorm i j) (norm_nonneg _)
    (norm_nonneg _)

end Ultrametric

section Truncation

variable [DiscreteTopology I]

section SeminormedRing

variable [SeminormedRing R]

/-- The output truncation `π_S ∘ u` keeps the rows of the matrix of `u` indexed by `S` and
replaces the others by zero. -/
@[simp]
theorem matrixCoeff_indicatorCLM_comp (S : Set I) (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) :
    ((indicatorCLM R S).comp u).matrixCoeff i j = S.indicator (u.matrixCoeff · j) i := by
  simp [matrixCoeff_apply]

/-- The row norms of the output truncation `π_S ∘ u` are those of `u` on `S` and zero
elsewhere. -/
@[simp]
theorem rowNorm_indicatorCLM_comp (S : Set I) (u : C₀(J, R) →L[R] C₀(I, R)) :
    ((indicatorCLM R S).comp u).rowNorm = S.indicator u.rowNorm := by
  ext i
  by_cases hi : i ∈ S <;> simp [rowNorm_def, hi]

omit [DiscreteTopology J] [DecidableEq J] in
/-- Removing the output truncation `π_S ∘ u` from `u` leaves the truncation to the complement
of `S`. -/
theorem sub_indicatorCLM_comp (S : Set I) (u : C₀(J, R) →L[R] C₀(I, R)) :
    u - (indicatorCLM R S).comp u = (indicatorCLM R Sᶜ).comp u := by
  ext x i
  by_cases hi : i ∈ S <;> simp [hi]

/-- Over Tate scalars, the output truncation `π_S ∘ u` to a finite set `S` is row compact: its
rows outside `S` vanish. -/
theorem isRowCompact_indicatorCLM_comp [TauCeti.NormedRing.IsTate R] (S : Finset I)
    (u : C₀(J, R) →L[R] C₀(I, R)) : ((indicatorCLM R (S : Set I)).comp u).IsRowCompact := by
  refine isRowCompact_iff_tendsto_rowNorm.2 (tendsto_const_nhds.congr' ?_)
  filter_upwards [S.eventually_cofinite_notMem] with i hi
  simp [hi]

end SeminormedRing

variable [NormedRing R] [IsUltrametricDist R]

/-- Over an ultrametric ring, if the entries of `u` in the rows outside `S` have norm at most
`C`, the remainder `u - π_S ∘ u` of the output truncation satisfies
`‖(u - π_S ∘ u) x‖ ≤ C * ‖x‖`. -/
theorem norm_sub_indicatorCLM_comp_apply_le {u : C₀(J, R) →L[R] C₀(I, R)} {S : Set I} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i ∉ S, ∀ j, ‖u.matrixCoeff i j‖ ≤ C) (x : C₀(J, R)) :
    ‖(u - (indicatorCLM R S).comp u) x‖ ≤ C * ‖x‖ := by
  rw [sub_indicatorCLM_comp]
  refine norm_apply_le_of_forall_norm_matrixCoeff_le _ hC (fun i j ↦ ?_) x
  by_cases hi : i ∈ S
  · simpa [hi] using hC
  · simpa [hi] using h i hi j

/-- **Row-compact maps are completely continuous**, over any ultrametric normed ring: they are
uniformly approximated by their output truncations onto finite sets, which have finite rank. -/
theorem IsRowCompact.isCompletelyContinuous {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) : u.IsCompletelyContinuous := by
  refine isCompletelyContinuous_iff.2 fun ε hε ↦ ?_
  have hT : {i | ε ≤ u.rowNorm i}.Finite := by
    simpa only [not_lt] using eventually_cofinite.1 (hu.tendsto_rowNorm.eventually_lt_const hε)
  refine ⟨(indicatorCLM R (hT.toFinset : Set I)).comp u,
    (isFiniteRank_indicatorCLM _).comp_right (u : C₀(J, R) →ₗ[R] C₀(I, R)), fun x ↦ ?_⟩
  simpa using norm_sub_indicatorCLM_comp_apply_le hε.le (fun i hi j ↦
    (hu.norm_matrixCoeff_le_rowNorm i j).trans (not_le.1 (by simpa using hi)).le) x

variable [TauCeti.NormedRing.IsTate R]

/-- **Row compactness is norm convergence of output truncations**: over ultrametric Tate scalars,
`u` is row compact exactly when `‖u - π_S ∘ u‖ → 0` as the finite set `S` of output coordinates
grows. -/
theorem isRowCompact_iff_tendsto_ringOpNorm_sub_indicatorCLM_comp
    {u : C₀(J, R) →L[R] C₀(I, R)} :
    u.IsRowCompact ↔
      Tendsto (fun S : Finset I ↦ ‖u - (indicatorCLM R (S : Set I)).comp u‖) atTop (𝓝 0) := by
  refine ⟨fun hu ↦ ?_, fun h ↦ isRowCompact_iff_tendsto_rowNorm.2 ?_⟩
  · refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun _ ↦
      ha.trans_le (ringOpNorm_nonneg _), fun ε hε ↦ ?_⟩
    have hT : {i | ε / 2 ≤ u.rowNorm i}.Finite := by
      simpa only [not_lt] using
        eventually_cofinite.1 (hu.tendsto_rowNorm.eventually_lt_const (half_pos hε))
    filter_upwards [eventually_ge_atTop hT.toFinset] with S hS
    refine lt_of_le_of_lt (ringOpNorm_le_bound _ (half_pos hε).le
      (norm_sub_indicatorCLM_comp_apply_le (half_pos hε).le fun i hi j ↦ ?_)) (half_lt_self hε)
    exact (hu.norm_matrixCoeff_le_rowNorm i j).trans
      (not_le.1 fun h ↦ hi (hS (by simpa using h))).le
  · refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun i ↦ ha.trans_le
      (u.rowNorm_nonneg i), fun ε hε ↦ ?_⟩
    obtain ⟨S, hS⟩ := (h.eventually_lt_const hε).exists
    refine eventually_cofinite.2 (S.finite_toSet.subset fun i hi ↦ ?_)
    by_contra hiS
    refine hi (lt_of_le_of_lt ?_ hS)
    have := ((indicatorCLM R (S : Set I)ᶜ).comp u).rowNorm_le_ringOpNorm i
    rwa [rowNorm_indicatorCLM_comp, Set.indicator_of_mem (by simpa using hiS),
      ← sub_indicatorCLM_comp] at this

/-- Over ultrametric Tate scalars, the output truncations `π_S ∘ u` of a row-compact `u` converge
to `u` in operator norm as the finite set `S` grows. -/
theorem IsRowCompact.tendsto_ringOpNorm_indicatorCLM_comp_sub {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) :
    Tendsto (fun S : Finset I ↦ ‖(indicatorCLM R (S : Set I)).comp u - u‖) atTop (𝓝 0) := by
  simpa only [← neg_sub u, ringOpNorm_neg] using
    isRowCompact_iff_tendsto_ringOpNorm_sub_indicatorCLM_comp.1 hu

end Truncation

section Ideal

variable [NormedCommRing R] [IsUltrametricDist R] [TauCeti.NormedRing.IsTate R]
  [TopologicalSpace K] [DiscreteTopology K] [DecidableEq K] [TopologicalSpace L]
  [DiscreteTopology L]

/-- Over ultrametric Tate scalars, precomposing a row-compact map with a continuous linear map
gives a row-compact map: row `i` of `u ∘ w` has norm at most `rᵢ(u) * ‖w‖`. -/
theorem IsRowCompact.comp_clm {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (w : C₀(K, R) →L[R] C₀(J, R)) : (u.comp w).IsRowCompact := by
  refine isRowCompact_of_norm_matrixCoeff_le
    (by simpa using hu.tendsto_rowNorm.mul_const ‖w‖) fun i k ↦ ?_
  rw [matrixCoeff_comp]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (u.rowNorm_nonneg i) (ringOpNorm_nonneg w)) fun j ↦ ?_
  exact (norm_mul_le _ _).trans (mul_le_mul (u.norm_matrixCoeff_le_rowNorm i j)
    (w.norm_matrixCoeff_le j k) (norm_nonneg _) (u.rowNorm_nonneg i))

/-- Over ultrametric Tate scalars, postcomposing a row-compact map with a continuous linear map
gives a row-compact map. The finitely many large rows of `u` are absorbed by the null columns of
the matrix of `w`. -/
theorem IsRowCompact.clm_comp [DiscreteTopology I] {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) (w : C₀(I, R) →L[R] C₀(L, R)) : (w.comp u).IsRowCompact := by
  classical
  refine isRowCompact_iff_tendsto_rowNorm.2 (tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall
    fun l ↦ ha.trans_le ((w.comp u).rowNorm_nonneg l), fun ε hε ↦ ?_⟩)
  obtain ⟨C, hC₀, hC⟩ : ∃ C, 0 < C ∧ ∀ i j, ‖u.matrixCoeff i j‖ ≤ C :=
    ⟨‖u‖ + 1, by positivity, fun i j ↦ (u.norm_matrixCoeff_le i j).trans (by linarith)⟩
  -- The rows of `u` of norm at least `δ` form a finite set `T`. Off `T` the terms of the matrix
  -- product are small because the rows of `u` are; on `T` they are eventually small because the
  -- finitely many corresponding columns of the matrix of `w` tend to zero.
  have hδ : ‖w‖ * (ε / 2 / (‖w‖ + 1)) ≤ ε / 2 := by
    calc ‖w‖ * (ε / 2 / (‖w‖ + 1)) ≤ (‖w‖ + 1) * (ε / 2 / (‖w‖ + 1)) := by gcongr; linarith
      _ = ε / 2 := by field_simp
  have hT : {i | ε / 2 / (‖w‖ + 1) ≤ u.rowNorm i}.Finite := by
    simpa only [not_lt] using
      eventually_cofinite.1 (hu.tendsto_rowNorm.eventually_lt_const (by positivity))
  have hw : ∀ᶠ l in cofinite, ∀ i ∈ hT.toFinset, ‖w.matrixCoeff l i‖ < ε / 2 / C :=
    (eventually_all_finset _).2 fun i _ ↦
      (tendsto_norm_zero.comp (w.tendsto_matrixCoeff_cofinite i)).eventually_lt_const
        (by positivity)
  filter_upwards [hw] with l hl
  refine lt_of_le_of_lt (rowNorm_le_of_forall_le (by positivity) fun j ↦ ?_) (half_lt_self hε)
  rw [matrixCoeff_comp]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i ↦
    (norm_mul_le _ _).trans ?_
  by_cases hi : i ∈ hT.toFinset
  · calc ‖w.matrixCoeff l i‖ * ‖u.matrixCoeff i j‖ ≤ ε / 2 / C * C :=
          mul_le_mul (hl i hi).le (hC i j) (norm_nonneg _) (by positivity)
      _ = ε / 2 := div_mul_cancel₀ _ hC₀.ne'
  · have hi' : u.rowNorm i < ε / 2 / (‖w‖ + 1) := not_le.1 (by simpa using hi)
    calc ‖w.matrixCoeff l i‖ * ‖u.matrixCoeff i j‖ ≤ ‖w‖ * (ε / 2 / (‖w‖ + 1)) :=
          mul_le_mul (w.norm_matrixCoeff_le l i)
            ((u.norm_matrixCoeff_le_rowNorm i j).trans hi'.le) (norm_nonneg _)
            (ringOpNorm_nonneg w)
      _ ≤ ε / 2 := hδ

end Ideal

end ContinuousLinearMap
