/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.LinearCombination
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# Matrices of continuous linear maps between model spaces

Let `R` be a seminormed ring and `I`, `J` discrete index types. A continuous linear map
`u : C₀(J, R) →L[R] C₀(I, R)` between the model spaces of nonarchimedean functional analysis has
the matrix (only the input index `J` needs to be discrete for the definition)

`u.matrixCoeff i j = (u (single j 1)) i`,

with the output index first, as for Mathlib's `LinearMap.toMatrix'`: the columns of the matrix are
the images of the coordinate vectors. This file develops the dictionary between such maps and
their matrices.

* Every column tends to zero along the cofinite filter (`tendsto_matrixCoeff_cofinite`), and over
  a ring with a multiplicative pseudo-uniformiser every entry is bounded by the operator norm
  (`norm_matrixCoeff_le`), so convergence in operator norm gives uniform convergence of the
  entries (`tendstoUniformly_matrixCoeff_of_tendsto`).
* The value of `u` is given by the convergent matrix action: `(u x) i = ∑ j, A i j * x j` over a
  commutative ring (`hasSum_matrixCoeff_mul`), and the matrix of a composite is the convergent
  matrix product (`hasSum_matrixCoeff_comp`).
* A map is determined by its matrix (`matrixCoeff_injective`). Conversely a matrix with null
  columns and bounded entries over a complete ultrametric ring is the matrix of the map
  `Matrix.toZeroAtInftyCLM` (`matrixCoeff_toZeroAtInftyCLM`), which acts by the same convergent
  sums (`hasSum_toZeroAtInftyCLM_apply`). Over Tate scalars this characterises the matrices of
  continuous linear maps (`mem_range_matrixCoeff_iff`).
* Over an ultrametric ring a bound `C` on the entries gives `‖u x‖ ≤ C * ‖x‖`
  (`norm_apply_le_of_forall_norm_matrixCoeff_le`), so the operator norm is bounded by the supremum
  of the entries, and over Tate scalars it equals that supremum
  (`ringOpNorm_eq_iSup_norm_matrixCoeff`), which is Mathlib's operator norm over a nontrivially
  normed field (`opNorm_eq_iSup_norm_matrixCoeff`).
* For finite index types the matrix is the usual matrix of the underlying linear map
  `R ^ J → R ^ I` (`matrixCoeff_eq_toMatrix'`).
* A matrix over `R` with null columns and bounded entries also acts on the module-valued model
  space `C₀(J, E)` of a complete ultrametric normed `R`-module `E` with contractive action, by
  `(A x) i = ∑ j, A i j • x j` (`Matrix.toZeroAtInftySMulCLM`). This is linear over every
  semiring acting on `E` compatibly with `R`, and a bound `C` on the entries bounds it by `C`
  (`Matrix.norm_toZeroAtInftySMulCLM_apply_le`). The map `Matrix.toZeroAtInftyCLM`, which
  multiplies by the entries on the right, is the case of the matrix over the opposite ring `Rᵐᵒᵖ`
  acting on `R` (`Matrix.toZeroAtInftySMulCLM_map_op`).

Decay of the rows `i ↦ ⨆ j, ‖A i j‖`, which is uniform in the input index, is a strictly stronger
condition than decay of each column: over a nonzero norm-one ring, the identity of `C₀(ℕ, R)` has
null columns, but every row has norm one.

## Main definitions

* `ContinuousLinearMap.matrixCoeff`: the matrix of a continuous linear map between model spaces.
* `Matrix.toZeroAtInftyCLM`: the continuous linear map defined by a matrix with null columns and
  bounded entries.
* `Matrix.toZeroAtInftySMulCLM`: the continuous linear map `C₀(J, E) → C₀(I, E)` defined by such a
  matrix acting on module-valued null families.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §§2–3.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty ENNReal

variable {I J K R : Type*} [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J]
  [DecidableEq J]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

section SeminormedRing

variable [SeminormedRing R]

/-- The **matrix** of a continuous linear map `u : C₀(J, R) →L[R] C₀(I, R)` between model spaces:
its entry in row `i` and column `j` is the `i`-th coordinate of the image of the coordinate vector
`single j 1`. Rows are indexed by output coordinates. -/
noncomputable def matrixCoeff (u : C₀(J, R) →L[R] C₀(I, R)) : Matrix I J R :=
  Matrix.of fun i j ↦ u (ZeroAtInftyContinuousMap.single j 1) i

theorem matrixCoeff_apply (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) :
    u.matrixCoeff i j = u (ZeroAtInftyContinuousMap.single j 1) i :=
  (rfl)

@[simp]
theorem matrixCoeff_zero : (0 : C₀(J, R) →L[R] C₀(I, R)).matrixCoeff = 0 :=
  (rfl)

@[simp]
theorem matrixCoeff_add (u v : C₀(J, R) →L[R] C₀(I, R)) :
    (u + v).matrixCoeff = u.matrixCoeff + v.matrixCoeff :=
  (rfl)

@[simp]
theorem matrixCoeff_neg (u : C₀(J, R) →L[R] C₀(I, R)) : (-u).matrixCoeff = -u.matrixCoeff :=
  (rfl)

@[simp]
theorem matrixCoeff_sub (u v : C₀(J, R) →L[R] C₀(I, R)) :
    (u - v).matrixCoeff = u.matrixCoeff - v.matrixCoeff :=
  (rfl)

@[simp]
theorem matrixCoeff_sum {ι : Type*} (s : Finset ι) (u : ι → C₀(J, R) →L[R] C₀(I, R)) :
    (∑ k ∈ s, u k).matrixCoeff = ∑ k ∈ s, (u k).matrixCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, matrixCoeff_add, ih]

@[simp]
theorem matrixCoeff_id : (ContinuousLinearMap.id R C₀(J, R)).matrixCoeff = 1 := by
  ext i j
  simp [matrixCoeff_apply, Matrix.one_apply, Pi.single_apply]

@[simp]
theorem matrixCoeff_one : (1 : C₀(J, R) →L[R] C₀(J, R)).matrixCoeff = 1 :=
  matrixCoeff_id

/-- **Null columns**: each column of the matrix of a continuous linear map tends to zero along
the cofinite filter. -/
theorem tendsto_matrixCoeff_cofinite [DiscreteTopology I] (u : C₀(J, R) →L[R] C₀(I, R)) (j : J) :
    Tendsto (fun i ↦ u.matrixCoeff i j) cofinite (𝓝 0) :=
  (u (ZeroAtInftyContinuousMap.single j 1)).tendsto_cofinite

/-- **The matrix action**: the `i`-th coordinate of `u x` is the unconditional sum of the
`x j * u.matrixCoeff i j`. Over a commutative ring this is `hasSum_matrixCoeff_mul`. -/
theorem hasSum_mul_matrixCoeff (u : C₀(J, R) →L[R] C₀(I, R)) (x : C₀(J, R)) (i : I) :
    HasSum (fun j ↦ x j * u.matrixCoeff i j) (u x i) := by
  simpa [matrixCoeff_apply] using ((hasSum_smul_single_one x).mapL u).mapL (evalCLM R i)

/-- Over Tate scalars, every entry of the matrix is bounded by the operator norm. -/
theorem norm_matrixCoeff_le [TauCeti.NormedRing.IsTate R] (u : C₀(J, R) →L[R] C₀(I, R)) (i : I)
    (j : J) : ‖u.matrixCoeff i j‖ ≤ ‖u‖ := by
  simpa [matrixCoeff_apply] using
    (norm_coe_le_norm _ i).trans (le_ringOpNorm u (ZeroAtInftyContinuousMap.single j (1 : R)))

/-- Over Tate scalars, convergence in operator norm gives uniform convergence of the matrix
entries. -/
theorem tendstoUniformly_matrixCoeff_of_tendsto [TauCeti.NormedRing.IsTate R] {α : Type*}
    {l : Filter α} {w : α → C₀(J, R) →L[R] C₀(I, R)} {w₀ : C₀(J, R) →L[R] C₀(I, R)}
    (h : Tendsto (fun a ↦ ‖w a - w₀‖) l (𝓝 0)) :
    TendstoUniformly (fun a (p : I × J) ↦ (w a).matrixCoeff p.1 p.2)
      (fun p ↦ w₀.matrixCoeff p.1 p.2) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [h.eventually_lt_const hε] with a ha p
  rw [dist_comm]
  simpa only [dist_eq_norm, matrixCoeff_sub, Matrix.sub_apply] using
    ((w a - w₀).norm_matrixCoeff_le p.1 p.2).trans_lt ha

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing R]

@[simp]
theorem matrixCoeff_smul (c : R) (u : C₀(J, R) →L[R] C₀(I, R)) :
    (c • u).matrixCoeff = c • u.matrixCoeff :=
  (rfl)

/-- **The matrix action** over a commutative ring: the `i`-th coordinate of `u x` is the
unconditional sum `∑ j, u.matrixCoeff i j * x j`. -/
theorem hasSum_matrixCoeff_mul (u : C₀(J, R) →L[R] C₀(I, R)) (x : C₀(J, R)) (i : I) :
    HasSum (fun j ↦ u.matrixCoeff i j * x j) (u x i) := by
  simpa only [mul_comm] using u.hasSum_mul_matrixCoeff x i

/-- **The matrix of a composite** is the product of the matrices, an unconditionally convergent
sum over the middle index. -/
theorem hasSum_matrixCoeff_comp [TopologicalSpace K] [DiscreteTopology K] [DecidableEq K]
    (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(K, R) →L[R] C₀(J, R)) (i : I) (k : K) :
    HasSum (fun j ↦ u.matrixCoeff i j * v.matrixCoeff j k) ((u.comp v).matrixCoeff i k) :=
  u.hasSum_matrixCoeff_mul (v (ZeroAtInftyContinuousMap.single k 1)) i

/-- For finite index types, the matrix of `u` is the matrix, in the sense of
`LinearMap.toMatrix'`, of the linear map `R ^ J → R ^ I` obtained by identifying each model space
with the space of all families. -/
theorem matrixCoeff_eq_toMatrix' [DiscreteTopology I] [Fintype I] [Fintype J]
    (u : C₀(J, R) →L[R] C₀(I, R)) :
    u.matrixCoeff = LinearMap.toMatrix' ((equivFunOnFintype R R).toLinearEquiv.toLinearMap ∘ₗ
      (u : C₀(J, R) →ₗ[R] C₀(I, R)) ∘ₗ (equivFunOnFintype R R).symm.toLinearEquiv.toLinearMap) := by
  ext i j
  have : (equivFunOnFintype R R).symm (Pi.single j 1) = ZeroAtInftyContinuousMap.single j 1 := by
    ext; simp [Pi.single_apply]
  simp [matrixCoeff_apply, LinearMap.toMatrix'_apply, this]

end SeminormedCommRing

section NormedRing

variable [NormedRing R]

/-- A continuous linear map between model spaces is determined by its matrix. -/
theorem matrixCoeff_injective :
    Function.Injective (matrixCoeff : (C₀(J, R) →L[R] C₀(I, R)) → Matrix I J R) := by
  intro u v h
  refine continuousLinearMap_ext_single_one fun j ↦ ?_
  ext i
  exact congr_fun₂ h i j

@[simp]
theorem matrixCoeff_inj {u v : C₀(J, R) →L[R] C₀(I, R)} : u.matrixCoeff = v.matrixCoeff ↔ u = v :=
  matrixCoeff_injective.eq_iff

variable [IsUltrametricDist R]

/-- Over an ultrametric ring, a uniform bound `C` on the entries of the matrix of `u` gives the
uniform bound `‖u x‖ ≤ C * ‖x‖`. No pseudo-uniformiser is needed. -/
theorem norm_apply_le_of_forall_norm_matrixCoeff_le (u : C₀(J, R) →L[R] C₀(I, R)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i j, ‖u.matrixCoeff i j‖ ≤ C) (x : C₀(J, R)) : ‖u x‖ ≤ C * ‖x‖ := by
  refine (norm_le (by positivity)).2 fun i ↦ ?_
  rw [← (u.hasSum_mul_matrixCoeff x i).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j ↦ ?_
  refine (norm_mul_le _ _).trans ?_
  rw [mul_comm C]
  exact mul_le_mul (norm_coe_le_norm x j) (h i j) (norm_nonneg _) (norm_nonneg _)

/-- Over an ultrametric ring, a uniform bound `C` on the entries of the matrix bounds the operator
norm. -/
theorem ringOpNorm_le_of_forall_norm_matrixCoeff_le (u : C₀(J, R) →L[R] C₀(I, R)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i j, ‖u.matrixCoeff i j‖ ≤ C) : ‖u‖ ≤ C :=
  ringOpNorm_le_bound u hC (u.norm_apply_le_of_forall_norm_matrixCoeff_le hC h)

variable [TauCeti.NormedRing.IsTate R]

/-- Over ultrametric Tate scalars, `‖u‖ ≤ C` exactly when every entry of the matrix of `u` has
norm at most `C`. -/
theorem ringOpNorm_le_iff_forall_norm_matrixCoeff_le {u : C₀(J, R) →L[R] C₀(I, R)} {C : ℝ}
    (hC : 0 ≤ C) : ‖u‖ ≤ C ↔ ∀ i j, ‖u.matrixCoeff i j‖ ≤ C :=
  ⟨fun h i j ↦ (u.norm_matrixCoeff_le i j).trans h,
    u.ringOpNorm_le_of_forall_norm_matrixCoeff_le hC⟩

/-- **The sup-entry norm**: over ultrametric Tate scalars, the operator norm of a map between
model spaces is the supremum of the norms of the entries of its matrix. -/
theorem ringOpNorm_eq_iSup_norm_matrixCoeff (u : C₀(J, R) →L[R] C₀(I, R)) :
    ‖u‖ = ⨆ p : I × J, ‖u.matrixCoeff p.1 p.2‖ := by
  have hbdd : BddAbove (Set.range fun p : I × J ↦ ‖u.matrixCoeff p.1 p.2‖) :=
    ⟨‖u‖, by rintro _ ⟨p, rfl⟩; exact u.norm_matrixCoeff_le p.1 p.2⟩
  refine le_antisymm ((ringOpNorm_le_iff_forall_norm_matrixCoeff_le
    (Real.iSup_nonneg fun _ ↦ norm_nonneg _)).2 fun i j ↦ le_ciSup hbdd (i, j)) ?_
  exact Real.iSup_le (fun p ↦ u.norm_matrixCoeff_le p.1 p.2) (ringOpNorm_nonneg u)

end NormedRing

section NormedCommRing

variable [NormedCommRing R]

/-- The matrix of a composite is the product of the matrices, summed over the middle index. -/
theorem matrixCoeff_comp [TopologicalSpace K] [DiscreteTopology K] [DecidableEq K]
    (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(K, R) →L[R] C₀(J, R)) (i : I) (k : K) :
    (u.comp v).matrixCoeff i k = ∑' j, u.matrixCoeff i j * v.matrixCoeff j k :=
  (u.hasSum_matrixCoeff_comp v i k).tsum_eq.symm

/-- The matrix of a product of endomorphisms of a model space is the product of the matrices. -/
theorem matrixCoeff_mul (u v : C₀(J, R) →L[R] C₀(J, R)) (i j : J) :
    (u * v).matrixCoeff i j = ∑' k, u.matrixCoeff i k * v.matrixCoeff k j :=
  u.matrixCoeff_comp v i j

end NormedCommRing

end ContinuousLinearMap

namespace Matrix

variable [DiscreteTopology I] [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]

omit [DecidableEq J] in
/-- The continuous linear map `C₀(J, R) →L[R] C₀(I, R)` defined by a matrix `A` whose columns
tend to zero along the cofinite filter and whose entries are uniformly bounded, over a complete
ultrametric normed ring. It sends `x` to the family `i ↦ ∑ j, x j * A i j`, and its matrix is `A`
(`ContinuousLinearMap.matrixCoeff_toZeroAtInftyCLM`). -/
noncomputable def toZeroAtInftyCLM (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C) :
    C₀(J, R) →L[R] C₀(I, R) :=
  linearCombination R ⟨fun j ↦ mkOfDiscrete (fun i ↦ A i j) (hcol j), by
    obtain ⟨C, hC⟩ := hbdd
    refine memℓp_infty ⟨max C 0, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact (norm_le (le_max_right C 0)).2 fun i ↦ by simpa using (hC i j).trans (le_max_left C 0)⟩

/-- The map defined by a matrix `A` sends the coordinate vector `single j r` to `r` times the
`j`-th column of `A`. -/
@[simp]
theorem toZeroAtInftyCLM_single_apply (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (j : J) (r : R) (i : I) :
    A.toZeroAtInftyCLM hcol hbdd (ZeroAtInftyContinuousMap.single j r) i = r * A i j := by
  simp [toZeroAtInftyCLM]

end Matrix

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

variable [DiscreteTopology I] [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- The matrix of the map defined by a matrix `A` with null columns and bounded entries is `A`. -/
@[simp]
theorem matrixCoeff_toZeroAtInftyCLM (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C) :
    (A.toZeroAtInftyCLM hcol hbdd).matrixCoeff = A := by
  ext i j
  simp [matrixCoeff_apply, Matrix.toZeroAtInftyCLM]

omit [DecidableEq J] in
/-- The map defined by a matrix `A` with null columns and bounded entries sends `x` to the family
of unconditional sums `i ↦ ∑ j, x j * A i j`. -/
theorem hasSum_toZeroAtInftyCLM_apply (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (x : C₀(J, R)) (i : I) :
    HasSum (fun j ↦ x j * A i j) (A.toZeroAtInftyCLM hcol hbdd x i) := by
  classical
  simpa using (A.toZeroAtInftyCLM hcol hbdd).hasSum_mul_matrixCoeff x i

/-- Over Tate scalars, every continuous linear map between model spaces is the map defined by its
matrix. -/
theorem toZeroAtInftyCLM_matrixCoeff [TauCeti.NormedRing.IsTate R]
    (u : C₀(J, R) →L[R] C₀(I, R)) :
    u.matrixCoeff.toZeroAtInftyCLM u.tendsto_matrixCoeff_cofinite
      ⟨‖u‖, u.norm_matrixCoeff_le⟩ = u :=
  matrixCoeff_injective (matrixCoeff_toZeroAtInftyCLM _ _ _)

/-- **Matrices of continuous linear maps**: over a complete ultrametric ring with a multiplicative
pseudo-uniformiser, a matrix is the matrix of a continuous linear map `C₀(J, R) →L[R] C₀(I, R)`
exactly when its columns tend to zero along the cofinite filter and its entries are uniformly
bounded. -/
theorem mem_range_matrixCoeff_iff [TauCeti.NormedRing.IsTate R] {A : Matrix I J R} :
    A ∈ Set.range (matrixCoeff : (C₀(J, R) →L[R] C₀(I, R)) → Matrix I J R) ↔
      (∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) ∧ ∃ C, ∀ i j, ‖A i j‖ ≤ C := by
  refine ⟨?_, fun ⟨hcol, hbdd⟩ ↦ ⟨A.toZeroAtInftyCLM hcol hbdd, by simp⟩⟩
  rintro ⟨u, rfl⟩
  exact ⟨u.tendsto_matrixCoeff_cofinite, ‖u‖, u.norm_matrixCoeff_le⟩

end ContinuousLinearMap

/-- **The sup-entry norm** over a nontrivially normed ultrametric field: Mathlib's operator norm of
a map between model spaces is the supremum of the norms of the entries of its matrix. -/
theorem ContinuousLinearMap.opNorm_eq_iSup_norm_matrixCoeff {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] (u : C₀(J, 𝕜) →L[𝕜] C₀(I, 𝕜)) :
    ‖u‖ = ⨆ p : I × J, ‖u.matrixCoeff p.1 p.2‖ :=
  (ringOpNorm_eq_opNorm u).symm.trans u.ringOpNorm_eq_iSup_norm_matrixCoeff

/-! ### Matrices acting on module-valued model spaces -/

namespace Matrix

omit [DecidableEq J]

variable [DiscreteTopology I] {E : Type*} [NormedAddCommGroup E]

section SeminormedRing

variable [SeminormedRing R] [Module R E] [IsBoundedSMul R E]

/-- The `j`-th column of a matrix with null columns, multiplied by `e`, as an element of
`C₀(I, E)`. -/
private def smulColumn (A : Matrix I J R) (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0))
    (j : J) (e : E) : C₀(I, E) :=
  mkOfDiscrete (fun i ↦ A i j • e) (by simpa using (hcol j).smul_const e)

omit [TopologicalSpace J] [DiscreteTopology J] in
@[simp]
private theorem smulColumn_apply (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (j : J) (e : E) (i : I) :
    smulColumn A hcol j e i = A i j • e :=
  congrFun (coe_mkOfDiscrete _ _) i

omit [TopologicalSpace J] [DiscreteTopology J] in
private theorem norm_smulColumn_le (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i j, ‖A i j‖ ≤ C) (j : J) (e : E) : ‖smulColumn A hcol j e‖ ≤ C * ‖e‖ :=
  (ZeroAtInftyContinuousMap.norm_le (mul_nonneg hC0 (norm_nonneg e))).2 fun i ↦ by
    rw [smulColumn_apply]
    exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hC i j) (norm_nonneg e))

variable [IsUltrametricDist E]

omit [DiscreteTopology J] in
private theorem norm_tsum_smulColumn_le (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i j, ‖A i j‖ ≤ C) (x : C₀(J, E)) :
    ‖∑' j, smulColumn A hcol j (x j)‖ ≤ C * ‖x‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (mul_nonneg hC0 (norm_nonneg x)) fun j ↦
    (norm_smulColumn_le A hcol hC0 hC j (x j)).trans
      (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j) hC0)

variable [CompleteSpace E]

private theorem summable_smulColumn (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (x : C₀(J, E)) : Summable fun j ↦ smulColumn A hcol j (x j) := by
  obtain ⟨C, hC⟩ := hbdd
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| squeeze_zero_norm
    (fun j ↦ norm_smulColumn_le A hcol (le_max_right C 0)
      (fun i j ↦ (hC i j).trans (le_max_left C 0)) j (x j)) ?_
  simpa using (tendsto_zero_iff_norm_tendsto_zero.mp x.tendsto_cofinite).const_mul (max C 0)

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass R S E]

/-- The continuous linear map `C₀(J, E) →L[S] C₀(I, E)` defined by a matrix `A` over `R` whose
columns tend to zero along the cofinite filter and whose entries are uniformly bounded, for a
complete ultrametric normed `R`-module `E` with contractive action. It sends `x` to the family
`i ↦ ∑ j, A i j • x j` (`Matrix.hasSum_toZeroAtInftySMulCLM_apply`), and it is linear over every
semiring `S` whose action on `E` commutes with that of `R`. -/
noncomputable def toZeroAtInftySMulCLM (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C) :
    C₀(J, E) →L[S] C₀(I, E) :=
  let L : C₀(J, E) →ₗ[S] C₀(I, E) :=
    { toFun x := ∑' j, smulColumn A hcol j (x j)
      map_add' x y := by
        have h (j : J) : smulColumn A hcol j ((x + y) j) =
            smulColumn A hcol j (x j) + smulColumn A hcol j (y j) := by
          ext i
          simp [smul_add]
        simp only [h]
        exact (summable_smulColumn A hcol hbdd x).tsum_add (summable_smulColumn A hcol hbdd y)
      map_smul' s x := by
        have h (j : J) : smulColumn A hcol j ((s • x) j) = s • smulColumn A hcol j (x j) := by
          ext i
          simp [smul_comm _ s]
        simp only [h, RingHom.id_apply]
        exact (summable_smulColumn A hcol hbdd x).tsum_const_smul s }
  { L with
    cont := by
      obtain ⟨C, hC⟩ := hbdd
      exact AddMonoidHomClass.continuous_of_bound L (max C 0) fun x ↦
        norm_tsum_smulColumn_le A hcol (le_max_right C 0)
          (fun i j ↦ (hC i j).trans (le_max_left C 0)) x }

private theorem toZeroAtInftySMulCLM_eq_tsum (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (x : C₀(J, E)) : A.toZeroAtInftySMulCLM S hcol hbdd x = ∑' j, smulColumn A hcol j (x j) :=
  (rfl)

/-- The map defined by a matrix `A` with null columns and bounded entries sends `x` to the family
of unconditional sums `i ↦ ∑ j, A i j • x j`. -/
theorem hasSum_toZeroAtInftySMulCLM_apply (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (x : C₀(J, E)) (i : I) :
    HasSum (fun j ↦ A i j • x j) (A.toZeroAtInftySMulCLM S hcol hbdd x i) := by
  rw [toZeroAtInftySMulCLM_eq_tsum]
  simpa using
    (summable_smulColumn A hcol hbdd x).hasSum.mapL (ZeroAtInftyContinuousMap.evalCLM S i)

/-- The coordinates of the map defined by a matrix `A`. -/
theorem toZeroAtInftySMulCLM_apply (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (x : C₀(J, E)) (i : I) :
    A.toZeroAtInftySMulCLM S hcol hbdd x i = ∑' j, A i j • x j :=
  (A.hasSum_toZeroAtInftySMulCLM_apply S hcol hbdd x i).tsum_eq.symm

/-- The map defined by a matrix `A` sends the coordinate vector `single j e` to the `j`-th column
of `A` multiplied by `e`. -/
@[simp]
theorem toZeroAtInftySMulCLM_single_apply [DecidableEq J] (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (j : J) (e : E) (i : I) :
    A.toZeroAtInftySMulCLM S hcol hbdd (ZeroAtInftyContinuousMap.single j e) i = A i j • e := by
  rw [toZeroAtInftySMulCLM_apply, tsum_eq_single j fun k hk ↦ by
    simp [ZeroAtInftyContinuousMap.single_eq_of_ne hk]]
  simp

/-- A bound `C` on the entries of `A` gives `‖A x‖ ≤ C * ‖x‖`. -/
theorem norm_toZeroAtInftySMulCLM_apply_le (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i j, ‖A i j‖ ≤ C) (x : C₀(J, E)) :
    ‖A.toZeroAtInftySMulCLM S hcol hbdd x‖ ≤ C * ‖x‖ :=
  norm_tsum_smulColumn_le A hcol hC0 hC x

/-- The map defined by a difference of matrices is the difference of their maps. -/
theorem toZeroAtInftySMulCLM_sub_apply (A B : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ (A - B) i j) cofinite (𝓝 0))
    (hbdd : ∃ C, ∀ i j, ‖(A - B) i j‖ ≤ C)
    (hA : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hA' : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (hB : ∀ j, Tendsto (fun i ↦ B i j) cofinite (𝓝 0)) (hB' : ∃ C, ∀ i j, ‖B i j‖ ≤ C)
    (x : C₀(J, E)) :
    (A - B).toZeroAtInftySMulCLM S hcol hbdd x =
      A.toZeroAtInftySMulCLM S hA hA' x - B.toZeroAtInftySMulCLM S hB hB' x := by
  ext i
  refine ((A - B).hasSum_toZeroAtInftySMulCLM_apply S hcol hbdd x i).unique ?_
  simpa [sub_smul] using (A.hasSum_toZeroAtInftySMulCLM_apply S hA hA' x i).sub
    (B.hasSum_toZeroAtInftySMulCLM_apply S hB hB' x i)

end SeminormedRing

variable [NormedRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- Right multiplication by the entries of `A` is the action of `A` through the opposite ring: the
map `Matrix.toZeroAtInftyCLM` of a matrix over a complete ultrametric normed ring `R` is the map
defined by the matrix `A.map MulOpposite.op` over `Rᵐᵒᵖ`, acting on `R`. -/
theorem toZeroAtInftySMulCLM_map_op (A : Matrix I J R)
    (hcol : ∀ j, Tendsto (fun i ↦ A i j) cofinite (𝓝 0)) (hbdd : ∃ C, ∀ i j, ‖A i j‖ ≤ C)
    (hcol' : ∀ j, Tendsto (fun i ↦ A.map MulOpposite.op i j) cofinite (𝓝 0))
    (hbdd' : ∃ C, ∀ i j, ‖A.map MulOpposite.op i j‖ ≤ C) :
    (A.map MulOpposite.op).toZeroAtInftySMulCLM R hcol' hbdd' = A.toZeroAtInftyCLM hcol hbdd := by
  ext x i
  refine ((A.map MulOpposite.op).hasSum_toZeroAtInftySMulCLM_apply R hcol' hbdd' x i).unique ?_
  simpa using ContinuousLinearMap.hasSum_toZeroAtInftyCLM_apply A hcol hbdd x i

end Matrix
