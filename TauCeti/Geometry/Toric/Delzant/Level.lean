/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Geometry.Toric.Delzant.Torus

import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Analysis.Fredholm.Basic

/-!
# The level set of the Delzant construction

Let `i : N →+ V` be an integral lattice and let `(u, c)` be a facet presentation of a polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}` with `d = #ι` facets. Delzant's construction realizes
`Δ` as the moment polytope of a symplectic reduction of `ℂ^ι`.

The torus `(ℝ / 2πℤ)^ι` acts on `ℂ^ι` by `z_j ↦ exp(-i θ_j) z_j`. Writing `z_j = q_j + i p_j`, this
is the weight model of `TauCeti.weightMomentMap` with the weights `t ↦ -t_j`, so with the
conventions `ω = Σ dq_j ∧ dp_j` and `ι_{X_H} ω = dH` the action has the moment map

`⟨μ(z), t⟩ = Σ_j t_j (½ |z_j|² + c_j)`

(`TauCeti.Toric.delzantMomentMap c`), normalized by the support constants `c`. The Hamiltonian
vector field of `⟨μ, t⟩` is the generator of the rotation by the angles `-t`
(`TauCeti.Toric.hamiltonianVectorField_delzantMomentMap`).

The kernel torus `N_Δ` of `(ℝ / 2πℤ)^ι → V / 2π i(N)` (`TauCeti.Toric.facetTorusHom`) has Lie
algebra `𝔫`, the kernel of `β_ℝ : ℝ^ι → V`, `t ↦ Σ_j t_j i(u_j)`. Its moment map is `μ` followed
by restriction to `𝔫`, and its zero level is

`Z = {z | ⟨μ(z), t⟩ = 0 for every t ∈ 𝔫}`

(`TauCeti.Toric.delzantLevel i u c`, `TauCeti.Toric.mem_delzantLevel`). The symplectic toric
manifold of `Δ` is the quotient `Z / N_Δ`. This file proves the properties of `Z` that this
reduction needs.

* **Moment values.** A functional vanishing on `𝔫 = ker β_ℝ` factors through `β_ℝ`. So `z ∈ Z`
  exactly when `μ(z) = β_ℝ^* y` for some `y ∈ V*`, that is `½ |z_j|² + c_j = ⟨y, u_j⟩` for all `j`
  (`TauCeti.Toric.mem_delzantLevel_iff`). Such a `y` lies in `Δ`, the facets active at `y` are
  the `j` with `z_j = 0` (`TauCeti.Toric.activeSet_eq_of_forall_eq`), and every `y ∈ Δ` arises
  from a point of `Z` (`TauCeti.Toric.setOf_exists_mem_delzantLevel`).
* **Compactness.** Since `|z_j|² = 2 (⟨y, u_j⟩ - c_j)` with `y ∈ Δ`, the level is compact when
  `Δ` is bounded (`TauCeti.Toric.isCompact_delzantLevel`), in particular for a Delzant polytope.
* **Freeness.** Let `z ∈ Z` with moment value `y ∈ Δ`. The facets active at `y` are active at a
  vertex `v` of `Δ`, where the normals form a basis of `N`. An element of `N_Δ` fixing `z` has
  trivial coordinates wherever `z_j ≠ 0`, in particular outside the facets active at `v`, so it
  is trivial (`TauCeti.Toric.eq_zero_of_mem_ker_facetTorusHom`). Hence `N_Δ` acts freely on `Z`
  (`TauCeti.Toric.IsDelzant.weightRotation_neg_eq_self_iff`). The same argument for the vector
  group `𝔫` shows that its infinitesimal action is free on `Z`
  (`TauCeti.Toric.IsDelzant.weightGenerator_neg_eq_zero_iff`).
* **Regularity.** In the weight model the image of the derivative of the moment map at `z` has
  the dimension of the orbit through `z`. As the infinitesimal action is free, the derivative of
  the moment map of `N_Δ` is surjective at every point of `Z`, so `0` is a regular value
  (`TauCeti.Toric.IsDelzant.surjective_fderiv_delzantMomentMap_comp`).
* **Smoothness.** Hence `Z` is a regular level set, and a smooth manifold of dimension
  `2d - (d - n) = d + n`, where `n = dim V`, for the implicit-function atlas of
  `TauCeti.levelSetChartedSpace` (`TauCeti.Toric.IsDelzant.isManifold_delzantLevel`).

## Main definitions

* `TauCeti.Toric.delzantMomentMap c`: the moment map `Σ_j (½ |z_j|² + c_j) e_j^*` of the action of
  `(ℝ / 2πℤ)^ι` on `ℂ^ι` by `z_j ↦ exp(-i θ_j) z_j`.
* `TauCeti.Toric.delzantLevel i u c`: the zero level `Z` of the moment map of the kernel torus.
* `TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`: the implicit-function atlas of `Z`, modelled
  on `Fin (d + n) → ℝ`.

## Main results

* `TauCeti.Toric.hamiltonianVectorField_delzantMomentMap`: `μ` is a moment map for the action.
* `TauCeti.Toric.hasFDerivAt_delzantMomentMap`, `TauCeti.Toric.contDiff_delzantMomentMap`: the
  derivative of `μ`, and its smoothness.
* `TauCeti.Toric.mem_delzantLevel_iff`: `z ∈ Z` exactly when `μ(z) = β_ℝ^* y` for some `y ∈ V*`.
* `TauCeti.Toric.setOf_exists_mem_delzantLevel`: these values `y` form the polytope `Δ`.
* `TauCeti.Toric.isCompact_delzantLevel`: `Z` is compact when `Δ` is bounded.
* `TauCeti.Toric.IsDelzant.weightRotation_neg_eq_self_iff`: the kernel torus acts freely on `Z`.
* `TauCeti.Toric.IsDelzant.surjective_fderiv_delzantMomentMap_comp`: `0` is a regular value of the
  moment map of the kernel torus.
* `TauCeti.Toric.index_fderiv_delzantMomentMap_comp`: when the real normals span `V`, the
  derivative of the moment map of the kernel torus has index `d + n`.
* `TauCeti.Toric.IsDelzant.isManifold_delzantLevel`: `Z` is a smooth manifold of dimension `d + n`.
* `TauCeti.Toric.IsDelzant.contMDiff_coe_delzantLevel`: the inclusion of `Z` into `ℂ^ι` is smooth.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Module Set Real
open scoped Manifold

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### The moment map of the facet torus -/

variable (c) in
/-- The moment map `⟨μ(z), t⟩ = Σ_j t_j (½ |z_j|² + c_j)` of the action of the torus
`(ℝ / 2πℤ)^ι` on `ℂ^ι` by `z_j ↦ exp(-i θ_j) z_j`, normalized by the support constants `c`. In the
real coordinates `z_j = q_j + i p_j` it is the weight-model moment map for the weights `t ↦ -t_j`
plus the constant `Σ_j c_j e_j^*`. -/
def delzantMomentMap (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : StrongDual ℝ (ι → ℝ) :=
  weightMomentMap (fun j ↦ -ContinuousLinearMap.proj j) x + ∑ j, c j • ContinuousLinearMap.proj j

@[simp]
theorem delzantMomentMap_apply (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (t : ι → ℝ) :
    delzantMomentMap c x t = ∑ j, t j * ((x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j) := by
  simp only [delzantMomentMap, add_apply, weightMomentMap_apply, neg_apply,
    ContinuousLinearMap.proj_apply, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

variable (c) in
/-- The derivative of the moment map at `x`: `d⟨μ, t⟩ = Σ_j t_j (q_j dq_j + p_j dp_j)`. -/
theorem hasFDerivAt_delzantMomentMap (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    HasFDerivAt (delzantMomentMap c)
      (∑ j, ContinuousLinearMap.smulRight
        (x.1 j • (PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.fst ℝ _ _) +
          x.2 j • (PiLp.proj 2 (fun _ ↦ ℝ) j).comp (ContinuousLinearMap.snd ℝ _ _) :
            EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →L[ℝ] ℝ)
        (ContinuousLinearMap.proj j : StrongDual ℝ (ι → ℝ)))
      x := by
  refine ((hasFDerivAt_weightMomentMap (fun j ↦ -ContinuousLinearMap.proj j) x).add_const
    (∑ j, c j • ContinuousLinearMap.proj j : StrongDual ℝ (ι → ℝ))).congr_fderiv
      (Finset.sum_congr rfl fun j _ ↦ ?_)
  ext v t <;> simp

variable (c) in
/-- The moment map is smooth. -/
theorem contDiff_delzantMomentMap {n : WithTop ℕ∞} :
    ContDiff ℝ n (delzantMomentMap (ι := ι) c) := by
  have h : delzantMomentMap (ι := ι) c = fun x ↦
      ∑ j, ((x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j) • ContinuousLinearMap.proj j := by
    funext x
    ext t
    simp [mul_comm]
  rw [h]
  refine ContDiff.sum fun j _ ↦ (ContDiff.add ?_ contDiff_const).smul_const _
  have h1 : ContDiff ℝ n fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ x.1 j :=
    ((PiLp.proj 2 (fun _ ↦ ℝ) j).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contDiff
  have h2 : ContDiff ℝ n fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ x.2 j :=
    ((PiLp.proj 2 (fun _ ↦ ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι))).contDiff
  exact ((h1.pow 2).add (h2.pow 2)).div_const 2

variable (c) in
/-- The moment map is continuous. -/
theorem continuous_delzantMomentMap : Continuous (delzantMomentMap (ι := ι) c) :=
  (contDiff_delzantMomentMap c (n := 0)).continuous

/-- The moment map is invariant under the action of the torus. -/
@[simp]
theorem delzantMomentMap_weightRotation (θ : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    delzantMomentMap c (weightRotation θ x) = delzantMomentMap c x := by
  simp [delzantMomentMap]

/-- **The moment map equation.** The Hamiltonian vector field of the component `⟨μ, t⟩` is the
generator of the rotation `z_j ↦ exp(-i t_j) z_j`. -/
theorem hamiltonianVectorField_delzantMomentMap (t : ι → ℝ)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    stdSymplecticForm.hamiltonianVectorField (fun y ↦ delzantMomentMap c y t) x =
      weightGenerator (-t) x := by
  -- By definition, `⟨μ, t⟩` is the weight-model component `⟨μ_α, t⟩` plus the constant
  -- `Σ_j c_j t_j`.
  have hf : HasFDerivAt (fun y ↦ delzantMomentMap c y t) _ x :=
    (hasFDerivAt_weightMomentMap_apply (fun j ↦ -ContinuousLinearMap.proj j) t x).add_const
      ((∑ j, c j • ContinuousLinearMap.proj j : StrongDual ℝ (ι → ℝ)) t)
  rw [stdSymplecticForm_hamiltonianVectorField hf]
  ext j <;> simp

/-! ### The level set -/

variable (i u c) in
/-- The zero level `Z` of the moment map `z ↦ μ(z)|_𝔫` of the kernel torus `N_Δ`, whose Lie
algebra is `𝔫 = ker β_ℝ`, where `β_ℝ t = Σ_j t_j i(u_j)`: the points at which `⟨μ, t⟩` vanishes for
every `t ∈ 𝔫` (`TauCeti.Toric.mem_delzantLevel`). -/
def delzantLevel : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  {x | (delzantMomentMap c x).comp
    (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtypeL = 0}

theorem mem_delzantLevel {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    x ∈ delzantLevel i u c ↔ ∀ t ∈ LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)),
      delzantMomentMap c x t = 0 :=
  ⟨fun h t ht ↦ by simpa using DFunLike.congr_fun h ⟨t, ht⟩,
    fun h ↦ ContinuousLinearMap.ext fun t ↦ h t t.2⟩

/-- The level is invariant under the action of the torus. -/
@[simp]
theorem weightRotation_mem_delzantLevel_iff (θ : ι → ℝ)
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    weightRotation θ x ∈ delzantLevel i u c ↔ x ∈ delzantLevel i u c := by
  simp [mem_delzantLevel]

/-- A point at which `μ = β_ℝ^* y` for some `y ∈ V*` lies on the level. -/
theorem mem_delzantLevel_of_forall_eq {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    {y : StrongDual ℝ V} (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    x ∈ delzantLevel i u c := by
  refine mem_delzantLevel.2 fun t ht ↦ ?_
  rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at ht
  simpa [hy, map_sum, map_smul, smul_eq_mul] using congrArg y ht

/-- **Points of the level.** A point `x` lies on the level exactly when `μ(x) = β_ℝ^* y` for some
`y ∈ V*`, that is `½ |z_j|² + c_j = ⟨y, u_j⟩` for every facet `j`. -/
theorem mem_delzantLevel_iff [FiniteDimensional ℝ V]
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} :
    x ∈ delzantLevel i u c ↔
      ∃ y : StrongDual ℝ V, ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j)) := by
  classical
  refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ mem_delzantLevel_of_forall_eq hy⟩
  -- The functional `μ(x)` vanishes on `ker β_ℝ`, so it factors through `β_ℝ`.
  have hmem : (delzantMomentMap c x : Module.Dual ℝ (ι → ℝ)) ∈
      (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).2 (mem_delzantLevel.1 hx)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine ⟨LinearMap.toContinuousLinearMap y, fun j ↦ ?_⟩
  have h := LinearMap.congr_fun hy (Pi.single j 1)
  simp only [LinearMap.dualMap_apply, ContinuousLinearMap.coe_coe, delzantMomentMap_apply,
    Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  rw [← h]
  simp [Fintype.linearCombination_apply, Pi.single_apply]

omit [Fintype ι] in
variable (c) in
/-- If `μ(x) = β_ℝ^* y`, then `y` lies in the polytope `Δ`. -/
theorem mem_facetPolyhedron_of_forall_eq {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    {y : StrongDual ℝ V} (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    y ∈ facetPolyhedron i u c :=
  mem_facetPolyhedron.2 fun j ↦ by
    rw [← hy j]
    linarith [sq_nonneg (x.1 j), sq_nonneg (x.2 j)]

omit [Fintype ι] in
/-- If `μ(x) = β_ℝ^* y`, the facets active at `y` are those `j` with `z_j = q_j + i p_j = 0`. -/
theorem activeSet_eq_of_forall_eq {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    {y : StrongDual ℝ V} (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    activeSet (facetPairing i u) c y = {j | x.1 j = 0 ∧ x.2 j = 0} := by
  ext j
  rw [mem_activeSet, facetPairing_apply, ← hy j, mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg (x.1 j)) (sq_nonneg (x.2 j))).1
      (by linarith)
    exact ⟨pow_eq_zero_iff two_ne_zero |>.1 h1, pow_eq_zero_iff two_ne_zero |>.1 h2⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

variable (i u c) in
/-- **The moment image of the level.** The values `y ∈ V*` with `μ(x) = β_ℝ^* y` for some point
`x` of the level form exactly the polytope `Δ`. -/
theorem setOf_exists_mem_delzantLevel :
    {y : StrongDual ℝ V | ∃ x ∈ delzantLevel i u c,
      ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))} = facetPolyhedron i u c := by
  ext y
  refine ⟨fun ⟨x, _, hy⟩ ↦ mem_facetPolyhedron_of_forall_eq c hy, fun hy ↦ ?_⟩
  -- Take `z_j = √(2 (⟨y, u_j⟩ - c_j))`.
  let x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
    (WithLp.toLp 2 fun j ↦ √(2 * (y (i (u j)) - c j)), 0)
  have hx : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j)) := fun j ↦ by
    have h : 0 ≤ 2 * (y (i (u j)) - c j) := by linarith [mem_facetPolyhedron.1 hy j]
    simp only [x, Real.sq_sqrt h, PiLp.zero_apply]
    ring
  exact ⟨x, mem_delzantLevel_of_forall_eq hx, hx⟩

/-- **Compactness of the level.** The level set is compact when the polytope `Δ` is bounded, in
particular for a Delzant polytope. -/
theorem isCompact_delzantLevel [FiniteDimensional ℝ V]
    (hb : Bornology.IsBounded (facetPolyhedron i u c)) : IsCompact (delzantLevel i u c) := by
  have hclosed : IsClosed (delzantLevel i u c) :=
    isClosed_eq ((continuous_delzantMomentMap c).clm_comp continuous_const) continuous_const
  -- Bound `|z_j|² = 2 (⟨y, u_j⟩ - c_j)` using a bound `R` on the polytope.
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set M : ι → ℝ := fun j ↦ 2 * (R * ‖i (u j)‖ + |c j|)
  have hbound : ∀ x ∈ delzantLevel i u c, ∀ j, x.1 j ^ 2 + x.2 j ^ 2 ≤ M j := by
    intro x hx j
    obtain ⟨y, hy⟩ := mem_delzantLevel_iff.1 hx
    have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 (hR (mem_facetPolyhedron_of_forall_eq c hy))
    have h1 : y (i (u j)) ≤ R * ‖i (u j)‖ :=
      (le_abs_self _).trans ((y.le_opNorm _).trans (by gcongr))
    have h2 := neg_abs_le (c j)
    have h3 := hy j
    simp only [M]
    linarith
  have hnorm : ∀ x ∈ delzantLevel i u c, ∀ z ∈ ({x.1, x.2} : Set (EuclideanSpace ℝ ι)),
      ‖z‖ ≤ √(∑ j, M j) := by
    rintro x hx z hz
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [Real.norm_eq_abs, sq_abs]
    rcases hz with rfl | rfl
    · linarith [hbound x hx j, sq_nonneg (x.2 j)]
    · linarith [hbound x hx j, sq_nonneg (x.1 j)]
  refine Metric.isCompact_of_isClosed_isBounded hclosed
    ((Metric.isBounded_iff_subset_closedBall 0).2 ⟨√(∑ j, M j), fun x hx ↦ ?_⟩)
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  exact max_le (hnorm x hx _ (mem_insert _ _)) (hnorm x hx _ (mem_insert_of_mem _ rfl))

/-- The derivative of the moment map `z ↦ μ(z)|_𝔫` of the kernel torus has index `d + n`, where
`d` is the number of facets and `n = dim V`, as soon as the real normals span `V`. -/
theorem index_fderiv_delzantMomentMap_comp
    (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ContinuousLinearMap.index (𝕜 := ℝ) (fderiv ℝ (fun y ↦ (delzantMomentMap c y).comp
      (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtypeL) x) =
        (Fintype.card ι + finrank ℝ V : ℕ) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℝ fun j ↦ i (u j))
  rw [LinearMap.range_eq_top.2 hβ, finrank_top, finrank_fintype_fun_eq_card] at h
  rw [ContinuousLinearMap.index_eq_of_finiteDimensional, finrank_prod, finrank_euclideanSpace,
    ← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]
  push_cast
  omega

/-! ### Delzant polytopes -/

namespace IsDelzant

variable [FiniteDimensional ℝ V] (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ

/-- At a point `x` of the level there is a smooth vertex `v` of `Δ` such that `z_j ≠ 0` for every
facet `j` that is not active at `v`. -/
private theorem exists_isSmoothVertex_of_mem_delzantLevel
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} (hx : x ∈ delzantLevel i u c) :
    ∃ v, IsSmoothVertex i u c v ∧
      ∀ j ∉ activeSet (facetPairing i u) c v, x.1 j ≠ 0 ∨ x.2 j ≠ 0 := by
  obtain ⟨y, hy⟩ := mem_delzantLevel_iff.1 hx
  obtain ⟨v, hv, hsub⟩ :=
    exists_mem_extremePoints_activeSet_subset hΔ.isCompact (mem_facetPolyhedron_of_forall_eq c hy)
  refine ⟨v, hΔ.isSmoothVertex v hv, fun j hj ↦ ?_⟩
  have hj' : j ∉ activeSet (facetPairing i u) c y := fun h ↦ hj (hsub h)
  rw [activeSet_eq_of_forall_eq hy, mem_ofPred_eq, not_and_or] at hj'
  exact hj'

include hi in
/-- **The kernel torus acts freely on the level.** Let `t` be a lift of an element of the kernel
torus `N_Δ ⊆ (ℝ / 2πℤ)^ι`. The rotation `z_j ↦ exp(-i t_j) z_j` fixes a point of the level exactly
when the element is trivial. -/
theorem weightRotation_neg_eq_self_iff {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : x ∈ delzantLevel i u c) {t : ι → ℝ}
    (ht : (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker) :
    weightRotation (-t) x = x ↔ (fun j ↦ (t j : AddCircle (2 * π))) = 0 := by
  rw [weightRotation_apply_eq_self_iff]
  constructor
  · intro h
    obtain ⟨v, hv, hvx⟩ := hΔ.exists_isSmoothVertex_of_mem_delzantLevel hx
    refine eq_zero_of_mem_ker_facetTorusHom hi (isSmoothVertex_def.1 hv) ht fun j hj ↦ ?_
    obtain ⟨k, hk⟩ := h j (hvx j hj)
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨-k, ?_⟩
    rw [zsmul_eq_mul]
    simp only [Pi.neg_apply] at hk
    push_cast
    linarith
  · intro h j _
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (2 * π)).1 (congrFun h j)
    exact ⟨-k, by simp only [Pi.neg_apply, ← hk, zsmul_eq_mul]; push_cast; ring⟩

include hi in
/-- **The infinitesimal action of the kernel torus is free on the level.** For `t` in the Lie
algebra `𝔫 = ker β_ℝ` of the kernel torus, the generator of `z_j ↦ exp(-i t_j) z_j` vanishes at
a point of the level exactly when `t = 0`. -/
theorem weightGenerator_neg_eq_zero_iff {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : x ∈ delzantLevel i u c) {t : ι → ℝ}
    (ht : t ∈ LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) :
    weightGenerator (-t) x = 0 ↔ t = 0 := by
  rw [weightGenerator_apply_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  -- Apply the lattice argument to the vector group `ℝ^ι = (ℝ / 0ℤ)^ι`.
  obtain ⟨v, hv, hvx⟩ := hΔ.exists_isSmoothVertex_of_mem_delzantLevel hx
  have hker : (fun j ↦ (t j : AddCircle (0 : ℝ))) ∈ (facetTorusHom i u 0).ker := by
    rw [AddMonoidHom.mem_ker, facetTorusHom_coe, LinearMap.mem_ker.1 ht,
      QuotientAddGroup.mk_zero]
  have h0 := eq_zero_of_mem_ker_facetTorusHom hi (isSmoothVertex_def.1 hv) hker fun j hj ↦ by
    have htj : t j = 0 := by simpa using h j (hvx j hj)
    rw [htj, QuotientAddGroup.mk_zero]
  funext j
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (0 : ℝ)).1 (congrFun h0 j)
  simpa using hk.symm

include hi in
/-- **Regularity of the level.** At every point of the level of a Delzant polytope the derivative
of the moment map `z ↦ μ(z)|_𝔫` of the kernel torus is surjective, so `0` is a regular value. -/
theorem surjective_fderiv_delzantMomentMap_comp {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : x ∈ delzantLevel i u c) :
    Function.Surjective (fderiv ℝ (fun y ↦ (delzantMomentMap c y).comp
      (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtypeL) x) := by
  set 𝔫 := LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))
  -- Restricted to `𝔫`, `μ` is the weight-model moment map for the weights `t ↦ -t_j` on `𝔫`.
  set α : ι → StrongDual ℝ 𝔫 := fun j ↦ -(ContinuousLinearMap.proj j).comp 𝔫.subtypeL
  have hfun : (fun y ↦ (delzantMomentMap c y).comp 𝔫.subtypeL) = fun y ↦
      weightMomentMap α y + (∑ j, c j • ContinuousLinearMap.proj j).comp 𝔫.subtypeL := by
    funext y
    ext t
    simp only [ContinuousLinearMap.comp_apply, delzantMomentMap, add_apply,
      weightMomentMap_apply, α, neg_apply]
  -- The infinitesimal action of `𝔫` at `x` is injective.
  have hinj : Function.Injective (weightInfinitesimalAction α x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h : weightGenerator (-(t : ι → ℝ)) x = 0 := by
      simpa [α, Pi.neg_def] using ht
    exact Subtype.ext ((hΔ.weightGenerator_neg_eq_zero_iff hi hx t.2).1 h)
  suffices h : LinearMap.range (fderiv ℝ (fun y ↦ (delzantMomentMap c y).comp 𝔫.subtypeL)
      x).toLinearMap = ⊤ from LinearMap.range_eq_top.1 h
  have hd : HasFDerivAt (fun y ↦ (delzantMomentMap c y).comp 𝔫.subtypeL)
      (fderiv ℝ (weightMomentMap α) x) x := by
    rw [hfun]
    exact (hasFDerivAt_weightMomentMap α x).differentiableAt.hasFDerivAt.add_const _
  rw [hd.fderiv, range_fderiv_weightMomentMap]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [← finrank_range_weightInfinitesimalAction, LinearMap.finrank_range_of_inj hinj,
    ← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]

include hi in
/-- The derivative of the moment map `z ↦ μ(z)|_𝔫` of the kernel torus has index `d + n`, where
`d` is the number of facets and `n = dim V`, for a Delzant polytope. -/
theorem index_fderiv_delzantMomentMap_comp (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ContinuousLinearMap.index (𝕜 := ℝ) (fderiv ℝ (fun y ↦ (delzantMomentMap c y).comp
      (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtypeL) x) =
        (Fintype.card ι + finrank ℝ V : ℕ) :=
  Toric.index_fderiv_delzantMomentMap_comp
    (surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination) x

include hi in
/-- The atlas of the level `Z`, by the implicit-function charts of the regular level set of the
moment map of the kernel torus. It is modelled on `Fin (d + n) → ℝ`, where `d` is the number of
facets and `n = dim V`. -/
@[instance_reducible]
def delzantLevelChartedSpace :
    ChartedSpace (Fin (Fintype.card ι + finrank ℝ V) → ℝ) (delzantLevel i u c) :=
  levelSetChartedSpace
    (f := fun y ↦ (delzantMomentMap c y).comp
      (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))).subtypeL)
    (fun _ _ ↦ ((contDiff_delzantMomentMap c).clm_comp contDiff_const).hasStrictFDerivAt
      one_ne_zero)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (fun _ hx ↦ hΔ.surjective_fderiv_delzantMomentMap_comp hi hx)
    (fun _ _ ↦ hΔ.index_fderiv_delzantMomentMap_comp hi _)

include hi in
/-- **The level is a smooth manifold** of dimension `d + n`, indeed a `C^m` manifold for every `m`,
including the analytic case `m = ω`, for the atlas
`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`. -/
theorem isManifold_delzantLevel (m : WithTop ℕ∞) :
    letI := hΔ.delzantLevelChartedSpace hi
    IsManifold 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ) m (delzantLevel i u c) :=
  isManifold_levelSet _ _ _ _ fun _ _ ↦
    ((contDiff_delzantMomentMap c).clm_comp contDiff_const).contDiffAt

include hi in
/-- The inclusion of the level `Z` into `ℂ^ι` is smooth for the atlas
`TauCeti.Toric.IsDelzant.delzantLevelChartedSpace`. -/
theorem contMDiff_coe_delzantLevel {m : WithTop ℕ∞} :
    letI := hΔ.delzantLevelChartedSpace hi
    ContMDiff 𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ)
      𝓘(ℝ, EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) m
      ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
  contMDiff_coe_levelSet _ _ _ _ fun _ _ ↦
    ((contDiff_delzantMomentMap c).clm_comp contDiff_const).contDiffAt

end IsDelzant

end TauCeti.Toric
