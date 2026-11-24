/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedPoints
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra

/-!
# Homogeneous coordinates on projective space over a field

Let `K` be a field and `ι` a finite type. The projective space `ℙ(K^ι)` is the projective
spectrum `Proj (Sym_K (ι → K))`, whose homogeneous coordinates `X_i` are the images of the
standard basis vectors. A coordinate vector `v : ι → K` gives the evaluation
`X_i ↦ v i` of homogeneous polynomials, and when `v k ≠ 0` the evaluation
`X_i / X_k ↦ v i / v k` of the standard chart `D₊(X_k)`. Every `K`-algebra homomorphism on the
chart `D₊(X_k)` is such an evaluation, at a coordinate vector with `k`-th coordinate `1`.

## Main declarations

* `TauCeti.projCoord`: the homogeneous coordinate `X_i`.
* `TauCeti.projEval`: evaluation of homogeneous polynomials at a coordinate vector.
* `TauCeti.projChartEval`: evaluation of the standard chart `D₊(X_k)` at a coordinate vector
  `v` with `v k ≠ 0`.
* `TauCeti.exists_eq_projChartEval`: every `K`-algebra homomorphism on the chart `D₊(X_k)` is a
  chart evaluation.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TauCeti.SymmetricAlgebra

universe u

namespace TauCeti

variable {K : Type u} [Field K] {ι : Type u} [Fintype ι] [DecidableEq ι]

variable (K) in
/-- The homogeneous coordinate `X_i` of `ℙ(K^ι) = Proj (Sym_K (ι → K))`, the image of the
standard basis vector `Pi.single i 1`. -/
noncomputable def projCoord (i : ι) : _root_.SymmetricAlgebra K (ι → K) :=
  _root_.SymmetricAlgebra.ι K (ι → K) (Pi.single i 1)

omit [Fintype ι] in
/-- The homogeneous coordinate `X_i` is the image of the standard basis vector. -/
theorem projCoord_def (i : ι) :
    projCoord K i = _root_.SymmetricAlgebra.ι K (ι → K) (Pi.single i 1) :=
  (rfl)

omit [Fintype ι] in
/-- The homogeneous coordinate `X_i` has degree one. -/
theorem projCoord_mem (i : ι) : projCoord K i ∈ homogeneousSubmodule K (ι → K) 1 :=
  ι_mem_homogeneousSubmodule K (ι → K) _

/-- Evaluation of homogeneous polynomials at the coordinate vector `v`: the `K`-algebra map
`Sym_K (ι → K) → K` sending `X_i` to `v i`. -/
noncomputable def projEval (v : ι → K) : _root_.SymmetricAlgebra K (ι → K) →ₐ[K] K :=
  _root_.SymmetricAlgebra.lift (Fintype.linearCombination K v)

omit [DecidableEq ι] in
/-- The evaluation at `v` is the symmetric algebra lift of the linear form `m ↦ ∑ i, m i * v i`.
-/
theorem projEval_eq_lift (v : ι → K) :
    projEval v = _root_.SymmetricAlgebra.lift (Fintype.linearCombination K v) :=
  (rfl)

omit [DecidableEq ι] in
/-- The evaluation at `v` sends the linear form `m` to `∑ i, m i * v i`. -/
@[simp]
theorem projEval_ι (v : ι → K) (m : ι → K) :
    projEval v (_root_.SymmetricAlgebra.ι K (ι → K) m) = ∑ i, m i * v i := by
  simp [projEval_eq_lift, Fintype.linearCombination_apply]

/-- The evaluation at `v` sends the homogeneous coordinate `X_i` to `v i`. -/
@[simp]
theorem projEval_projCoord (v : ι → K) (i : ι) : projEval v (projCoord K i) = v i := by
  simp [projCoord_def, Pi.single_apply]

omit [DecidableEq ι] in
/-- Rescaling the coordinates by `c` multiplies the value of a homogeneous polynomial of degree
`n` by `cⁿ`. -/
theorem projEval_smul_of_mem (c : K) (v : ι → K) {n : ℕ} {s : _root_.SymmetricAlgebra K (ι → K)}
    (hs : s ∈ homogeneousSubmodule K (ι → K) n) :
    projEval (c • v) s = c ^ n * projEval v s := by
  have h : Fintype.linearCombination K (c • v) = c • Fintype.linearCombination K v := by
    ext m
    simp [Fintype.linearCombination_apply, Finset.mul_sum, mul_left_comm]
  rw [projEval_eq_lift, projEval_eq_lift, h,
    lift_smul_of_mem_homogeneousSubmodule K (ι → K) _ c hs, smul_eq_mul]

omit [DecidableEq ι] in
/-- A nonzero coordinate vector sends the irrelevant ideal to the unit ideal. -/
theorem map_irrelevant_projEval_eq_top {v : ι → K} {k : ι} (hk : v k ≠ 0) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule K (ι → K))).toIdeal.map
      (projEval v : _root_.SymmetricAlgebra K (ι → K) →+* K) = ⊤ := by
  classical
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (x := projCoord K k) ?_)
    (by simpa using hk)
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _ (projCoord_mem k) one_ne_zero]

omit [DecidableEq ι] in
/-- A nonzero coordinate vector, followed by any ring homomorphism out of `K`, sends the
irrelevant ideal to the unit ideal. -/
theorem map_irrelevant_comp_projEval_eq_top {R : Type*} [Semiring R] (g : K →+* R)
    {v : ι → K} (hv : v ≠ 0) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule K (ι → K))).toIdeal.map
      (g.comp (projEval v : _root_.SymmetricAlgebra K (ι → K) →+* K)) = ⊤ := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  rw [← Ideal.map_map, map_irrelevant_projEval_eq_top hk, Ideal.map_top]

omit [Fintype ι] in
/-- The standard chart `D₊(X_k)` of `ℙ(K^ι)` lies over `Spec K`. -/
theorem awayι_projCoord_projToSpec (k : ι) :
    Proj.awayι (homogeneousSubmodule K (ι → K)) (projCoord K k) (projCoord_mem k) one_pos ≫
        projToSpec K (ι → K) =
      Spec.algebraMap K (Away (homogeneousSubmodule K (ι → K)) (projCoord K k)) := by
  rw [awayι_projToSpec, ← algebraMap_eq_comp]

/-- The evaluation `X_i / X_k ↦ v i / v k` of the standard chart `D₊(X_k)` at a coordinate
vector `v` with `v k ≠ 0`. -/
noncomputable def projChartEval (v : ι → K) {k : ι} (hk : v k ≠ 0) :
    Away (homogeneousSubmodule K (ι → K)) (projCoord K k) →ₐ[K] K :=
  { Away.lift (homogeneousSubmodule K (ι → K)) (projEval v : _ →+* K)
      (f := projCoord K k) (by simpa using hk) with
    commutes' r := by
      -- The `K`-algebra structure of the chart factors through its degree-zero part.
      rw [algebraMap_eq_comp, RingHom.comp_apply, ← HomogeneousLocalization.algebraMap_eq]
      exact (Away.lift_algebraMap (𝒜 := homogeneousSubmodule K (ι → K)) _ _ _).trans
        ((projEval v).commutes r) }

/-- The chart evaluation is `Away.lift` of the evaluation at `v`. -/
theorem projChartEval_toRingHom (v : ι → K) {k : ι} (hk : v k ≠ 0) :
    (projChartEval v hk).toRingHom = Away.lift (homogeneousSubmodule K (ι → K))
      (projEval v : _ →+* K) (f := projCoord K k) (by simpa using hk) :=
  (rfl)

/-- The chart evaluation sends the fraction `a / X_kⁿ` to `a(v) / (v k)ⁿ`. -/
@[simp]
theorem projChartEval_awayMk (v : ι → K) {k : ι} (hk : v k ≠ 0) {n : ℕ}
    {a : _root_.SymmetricAlgebra K (ι → K)} (ha) :
    projChartEval v hk (Away.mk _ (projCoord_mem k) n a ha) = projEval v a / v k ^ n := by
  rw [← AlgHom.coe_toRingHom, ← AlgHom.toRingHom_eq_coe, projChartEval_toRingHom, Away.lift_mk]
  simp [div_eq_mul_inv]

/-- Every `K`-algebra homomorphism `α` on the standard chart `D₊(X_k)` is the chart evaluation at
a coordinate vector whose `k`-th coordinate is `1`. -/
theorem exists_eq_projChartEval (k : ι)
    (α : Away (homogeneousSubmodule K (ι → K)) (projCoord K k) →ₐ[K] K) :
    ∃ (v : ι → K) (hk : v k ≠ 0), v k = 1 ∧ α = projChartEval v hk := by
  -- By definition (`projCoord_def`), `projCoord K k` is the linear coordinate
  -- `ι (Pi.single k 1)`, so `α` is also a homomorphism `β` on the chart of that linear form, the
  -- form in which `AlgHom.chartFunctional` reads it; this step uses that definitional unfolding.
  let β : Away (homogeneousSubmodule K (ι → K))
      (_root_.SymmetricAlgebra.ι K (ι → K) (Pi.single k 1)) →ₐ[K] K := α
  -- The linear form `c ↦ α (c / X_k)`, as in the description of closed points of `Proj`.
  let w : Module.Dual K (ι → K) := β.chartFunctional
  have hw : projEval (fun i ↦ w (Pi.single i 1)) = _root_.SymmetricAlgebra.lift w := by
    refine _root_.SymmetricAlgebra.algHom_ext (LinearMap.ext fun m ↦ ?_)
    have hm : ∑ i, m i • (Pi.single i 1 : ι → K) = m := by
      simpa using (Pi.basisFun K ι).sum_repr m
    conv_rhs => rw [← hm]
    simp [map_sum, map_smul]
  have hk1 : w (Pi.single k 1) = 1 := β.chartFunctional_self
  refine ⟨fun i ↦ w (Pi.single i 1), by simp [hk1], hk1, ?_⟩
  refine Away.algHom_ext (projCoord_mem k) fun n a ha ↦ ?_
  rw [projChartEval_awayMk, hk1, one_pow, div_one, hw]
  exact β.apply_awayMk_eq_lift_chartFunctional (by simpa using ha)

end TauCeti
