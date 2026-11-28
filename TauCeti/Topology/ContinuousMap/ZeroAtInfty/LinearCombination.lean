/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.Banach
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.Analysis.Normed.Module.Bases.WeaklyNull
import TauCeti.Analysis.Normed.Module.BoundedCoefficients

/-!
# The universal property of the model space `C₀(I, R)`

Let `R` be a seminormed ring, `I` a discrete index type and `M` a complete ultrametric normed
`R`-module with contractive scalar action. A bounded family `e : I → M`, that is an element of
`lp (fun _ : I ↦ M) ∞`, defines a continuous linear map

`ZeroAtInftyContinuousMap.linearCombination R e : C₀(I, R) →L[R] M`, `a ↦ ∑' i, a i • e i`.

The series converges because its terms tend to zero along the cofinite filter, which suffices in
a complete ultrametric group, and the ultrametric inequality bounds its sum by `‖e‖ * ‖a‖`. The
map sends the coordinate vector `single i 1` to `e i`, and over a norm-one ring its operator norm
is the supremum `‖e‖` of the norms of the `e i`. None of this needs a pseudo-uniformiser.

Conversely, over a ring admitting a multiplicative pseudo-uniformiser
(`TauCeti.NormedRing.IsTate R`) every continuous linear map `u : C₀(I, R) →L[R] M` has a uniform
bound, so the family `i ↦ u (single i 1)` is bounded and `u` is its linear combination map. Over a
commutative such ring this gives the linear isometric equivalence

`linearCombinationEquiv R M : lp (fun _ : I ↦ M) ∞ ≃ₗᵢ[R] (C₀(I, R) →L[R] M)`

for the operator norm of the scope `TauCeti.RingOpNorm`. Over a nontrivially normed field the
norm identity is stated for Mathlib's operator norm (`opNorm_linearCombination`).

This is the basic way to construct continuous linear maps out of the model spaces `C₀(I, R)` of
nonarchimedean functional analysis, for instance from bounded lifts of the coordinate vectors.

Both the ultrametric map and its real or complex counterpart below are instances of
`ZeroAtInftyContinuousMap.linearCombinationOfSummable`, the map `a ↦ ∑' i, a i • e i` for any
family `e` whose series converge with sums bounded by a constant times `‖a‖`; its application,
expansion and coordinate lemmas, including uniqueness on a discrete index
(`ZeroAtInftyContinuousMap.eq_linearCombinationOfSummable_iff`), serve both regimes.

Over `ℝ` or `ℂ` the terms tending to zero no longer suffice for convergence. Instead, a family `v`
in a Banach space whose finite subsums `∑ i ∈ s, v i` are uniformly bounded, by `C` say, gives the
bounded operator
`ZeroAtInftyContinuousMap.linearCombinationOfBoundedSubsums 𝕜 v hv : C₀(I, 𝕜) →L[𝕜] X`,
`a ↦ ∑' i, a i • v i`, of operator norm at most `4 * C`
(`ZeroAtInftyContinuousMap.opNorm_linearCombinationOfBoundedSubsums_le`). The bounded-coefficient
estimates behind it are `TauCeti.summable_smul_of_forall_norm_sum_le` and
`TauCeti.norm_tsum_smul_le_of_forall_norm_sum_le`. Conversely, the images of the unit coordinate
vectors under any continuous linear map `u : C₀(I, 𝕜) →L[𝕜] X` have finite subsums of norm at most
`‖u‖` (`ZeroAtInftyContinuousMap.norm_sum_apply_single_one_le`). When `v` is moreover a basic
sequence with basis constant at most `B` and terms of norm at least `ε > 0`, its linear
combination map is antilipschitz with constant `2 * B / ε`
(`ZeroAtInftyContinuousMap.antilipschitzWith_linearCombinationOfBoundedSubsums`), so the closed
linear span of `v` is isomorphic to `c₀`.

## Main definitions

* `ZeroAtInftyContinuousMap.linearCombinationOfSummable`: the continuous linear map
  `a ↦ ∑' i, a i • e i` for a family `e` whose series converge with linearly bounded sums.
* `ZeroAtInftyContinuousMap.linearCombination`: the continuous linear map `C₀(I, R) →L[R] M`
  attached to a bounded family in `M`.
* `ZeroAtInftyContinuousMap.linearCombinationOfBoundedSubsums`: the bounded operator
  `C₀(I, 𝕜) →L[𝕜] X` attached to a family with bounded finite subsums in a real or complex Banach
  space.
* `ZeroAtInftyContinuousMap.linearCombinationEquiv`: over a commutative ring with a multiplicative
  pseudo-uniformiser, bounded families correspond isometrically to continuous linear maps.

## Main results

* `ZeroAtInftyContinuousMap.hasSum_linearCombination`: the unconditional expansion
  `∑ i, a i • e i = linearCombination R e a`.
* `ZeroAtInftyContinuousMap.linearCombination_single`: the value on a coordinate vector.
* `ZeroAtInftyContinuousMap.eq_linearCombination_iff`: a continuous linear map is the linear
  combination map of a bounded family exactly when it sends each unit coordinate vector to
  the corresponding family member.
* `ZeroAtInftyContinuousMap.linearCombination_eq_tsum_mul`: for scalar-valued families, the
  pairing `∑' i, b i * a i`.
* `ZeroAtInftyContinuousMap.ringOpNorm_linearCombination`: over a norm-one ring the operator
  norm is the family supremum.
* `ZeroAtInftyContinuousMap.linearCombination_injective` and
  `ZeroAtInftyContinuousMap.linearCombination_self`: bounded families are determined by their
  linear combination maps, and over Tate scalars every continuous linear map is one.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

open Filter Topology
open scoped ENNReal ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {I R M : Type*} [TopologicalSpace I]

section Construction

open scoped TauCeti.RingOpNorm

variable [SeminormedRing R] [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- The ultrametric inequality bounds `∑' i, a i • e i` by `‖e‖ * ‖a‖` for a family `a` vanishing
at infinity and a bounded family `e`. -/
theorem norm_tsum_smul_le [IsUltrametricDist M] (a : C₀(I, R)) (e : lp (fun _ : I ↦ M) ∞) :
    ‖∑' i, a i • e i‖ ≤ ‖e‖ * ‖a‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg e) (norm_nonneg a)) fun i ↦ (norm_smul_le (a i) (e i)).trans <| by
      rw [mul_comm]
      gcongr
      exacts [lp.norm_apply_le_norm ENNReal.top_ne_zero e i, norm_coe_le_norm a i]

variable (R) in
/-- The continuous linear map `C₀(I, R) →L[R] M` sending `a` to `∑' i, a i • e i`, for a family
`e` such that each of these series converges and their sums are bounded by a constant times
`‖a‖`. The ultrametric `linearCombination` and the real or complex
`linearCombinationOfBoundedSubsums` are both built from it. -/
noncomputable def linearCombinationOfSummable (e : I → M)
    (he : ∀ a : C₀(I, R), Summable fun i ↦ a i • e i)
    (hC : ∃ C, ∀ a : C₀(I, R), ‖∑' i, a i • e i‖ ≤ C * ‖a‖) : C₀(I, R) →L[R] M :=
  LinearMap.mkContinuousOfExistsBound
    { toFun a := ∑' i, a i • e i
      map_add' a b := by
        simp only [FunLike.coe_add, Pi.add_apply, add_smul]
        exact (he a).tsum_add (he b)
      map_smul' c a := by
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (he a).tsum_const_smul c }
    hC

section OfSummable

variable {e : I → M} (he : ∀ a : C₀(I, R), Summable fun i ↦ a i • e i)
  (hC : ∃ C, ∀ a : C₀(I, R), ‖∑' i, a i • e i‖ ≤ C * ‖a‖)

/-- The value of `linearCombinationOfSummable` is the sum `∑' i, a i • e i`. -/
theorem linearCombinationOfSummable_apply (a : C₀(I, R)) :
    linearCombinationOfSummable R e he hC a = ∑' i, a i • e i :=
  (rfl)

/-- The series `∑ i, a i • e i` converges unconditionally to `linearCombinationOfSummable` at
`a`. -/
theorem hasSum_linearCombinationOfSummable (a : C₀(I, R)) :
    HasSum (fun i ↦ a i • e i) (linearCombinationOfSummable R e he hC a) :=
  (he a).hasSum

/-- `linearCombinationOfSummable` sends the coordinate vector `single i r` to `r • e i`. -/
@[simp]
theorem linearCombinationOfSummable_single [DiscreteTopology I] [DecidableEq I] (i : I) (r : R) :
    linearCombinationOfSummable R e he hC (single i r) = r • e i := by
  rw [linearCombinationOfSummable_apply, tsum_eq_single i fun j hj ↦ by simp [single_eq_of_ne hj],
    single_eq_same]

/-- On a discrete index, `linearCombinationOfSummable` is the unique continuous linear map sending
each unit coordinate vector `single i 1` to `e i`. -/
theorem eq_linearCombinationOfSummable_iff [DiscreteTopology I] [DecidableEq I]
    {u : C₀(I, R) →L[R] M} :
    u = linearCombinationOfSummable R e he hC ↔ ∀ i, u (single i 1) = e i :=
  ⟨by rintro rfl i; simp, fun h ↦ continuousLinearMap_ext_single_one fun i ↦ by simp [h]⟩

end OfSummable

variable [DiscreteTopology I]

/-- On a discrete index, the terms `a i • e i` of a family `a` vanishing at infinity against a
bounded family `e` tend to zero along the cofinite filter. -/
theorem tendsto_smul_cofinite (a : C₀(I, R)) (e : lp (fun _ : I ↦ M) ∞) :
    Tendsto (fun i ↦ a i • e i) cofinite (𝓝 0) := by
  refine squeeze_zero_norm (fun i ↦ (norm_smul_le (a i) (e i)).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero e i)
      (norm_nonneg _))) ?_
  simpa using a.tendsto_cofinite.norm.mul_const ‖e‖

variable [IsUltrametricDist M] [CompleteSpace M]

/-- In a complete ultrametric module, the series `∑' i, a i • e i` is summable for every
`a ∈ C₀(I, R)` and every bounded family `e`. -/
theorem summable_smul (a : C₀(I, R)) (e : lp (fun _ : I ↦ M) ∞) :
    Summable fun i ↦ a i • e i :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (a.tendsto_smul_cofinite e)

variable (R) in
/-- The **linear combination map** of a bounded family `e` in a complete ultrametric module: the
continuous linear map `C₀(I, R) →L[R] M` sending `a` to the unconditional sum `∑' i, a i • e i`.
It sends the coordinate vector `single i 1` to `e i`. -/
noncomputable def linearCombination (e : lp (fun _ : I ↦ M) ∞) : C₀(I, R) →L[R] M :=
  linearCombinationOfSummable R (fun i ↦ e i) (summable_smul · e)
    ⟨‖e‖, fun a ↦ a.norm_tsum_smul_le e⟩

/-- The value of the linear combination map is the sum `∑' i, a i • e i`. -/
theorem linearCombination_apply (e : lp (fun _ : I ↦ M) ∞) (a : C₀(I, R)) :
    linearCombination R e a = ∑' i, a i • e i :=
  linearCombinationOfSummable_apply _ _ a

/-- **Unconditional expansion**: `linearCombination R e a` is the unconditional sum of the
`a i • e i`. -/
theorem hasSum_linearCombination (e : lp (fun _ : I ↦ M) ∞) (a : C₀(I, R)) :
    HasSum (fun i ↦ a i • e i) (linearCombination R e a) :=
  hasSum_linearCombinationOfSummable _ _ a

/-- The linear combination map sends the coordinate vector `single i r` to `r • e i`. -/
@[simp]
theorem linearCombination_single [DecidableEq I] (e : lp (fun _ : I ↦ M) ∞) (i : I) (r : R) :
    linearCombination R e (single i r) = r • e i :=
  linearCombinationOfSummable_single _ _ i r

/-- The linear combination map of a bounded family is the unique continuous linear map
sending each unit coordinate vector `single i 1` to `e i`. -/
theorem eq_linearCombination_iff [DecidableEq I] {e : lp (fun _ : I ↦ M) ∞}
    {u : C₀(I, R) →L[R] M} : u = linearCombination R e ↔ ∀ i, u (single i 1) = e i :=
  eq_linearCombinationOfSummable_iff _ _

/-- Pairing the coordinate family `lp.single ∞ i m` with `a` gives `a i • m`. -/
@[simp]
theorem linearCombination_lpSingle [DecidableEq I] (i : I) (m : M) (a : C₀(I, R)) :
    linearCombination R (lp.single ∞ i m) a = a i • m := by
  rw [linearCombination_apply, tsum_eq_single i fun j hj ↦ by simp [hj], lp.single_apply_self]

/-- The linear combination map is bounded by the supremum of the family. -/
theorem norm_linearCombination_apply_le (e : lp (fun _ : I ↦ M) ∞) (a : C₀(I, R)) :
    ‖linearCombination R e a‖ ≤ ‖e‖ * ‖a‖ :=
  a.norm_tsum_smul_le e

/-- The operator norm of the linear combination map is at most the supremum of the family. -/
theorem ringOpNorm_linearCombination_le (e : lp (fun _ : I ↦ M) ∞) :
    ‖linearCombination R e‖ ≤ ‖e‖ :=
  ContinuousLinearMap.ringOpNorm_le_bound _ (norm_nonneg e) (norm_linearCombination_apply_le e)

/-- **The norm of a linear combination map**: over a norm-one ring, the operator norm of
`linearCombination R e` is the supremum `‖e‖ = ⨆ i, ‖e i‖` of the family. -/
@[simp]
theorem ringOpNorm_linearCombination [NormOneClass R] (e : lp (fun _ : I ↦ M) ∞) :
    ‖linearCombination R e‖ = ‖e‖ := by
  classical
  refine le_antisymm (ringOpNorm_linearCombination_le e)
    (lp.norm_le_of_forall_le (ContinuousLinearMap.ringOpNorm_nonneg _) fun i ↦ ?_)
  simpa using ContinuousLinearMap.le_ringOpNorm_of_exists_bound (linearCombination R e)
    ⟨‖e‖, norm_linearCombination_apply_le e⟩ (single i 1)

/-- The zero family has the zero linear combination map. -/
@[simp]
theorem linearCombination_zero : linearCombination R (0 : lp (fun _ : I ↦ M) ∞) = 0 := by
  classical
  exact continuousLinearMap_ext fun i b ↦ by simp

/-- The linear combination map is additive in the family. -/
theorem linearCombination_add (e f : lp (fun _ : I ↦ M) ∞) :
    linearCombination R (e + f) = linearCombination R e + linearCombination R f := by
  classical
  exact continuousLinearMap_ext fun i b ↦ by simp [smul_add]

/-- A bounded family is determined by its linear combination map. -/
theorem linearCombination_injective :
    Function.Injective (linearCombination R : lp (fun _ : I ↦ M) ∞ → C₀(I, R) →L[R] M) := by
  classical
  intro e f h
  ext i
  simpa using congr($h (single i (1 : R)))

end Construction

/-- Over a nontrivially normed field, the operator norm of `linearCombination K e` for Mathlib's
operator norm is the supremum of the family. -/
@[simp]
theorem opNorm_linearCombination [DiscreteTopology I] {K : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup M] [NormedSpace K M] [IsUltrametricDist M] [CompleteSpace M]
    (e : lp (fun _ : I ↦ M) ∞) :
    ‖linearCombination K e‖ = ‖e‖ :=
  (ContinuousLinearMap.ringOpNorm_eq_opNorm _).symm.trans (ringOpNorm_linearCombination e)

section Tate

open scoped TauCeti.RingOpNorm

variable [DiscreteTopology I] [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]

/-- Over Tate scalars, the values of a continuous linear map `u` out of `C₀(I, R)` at the unit
coordinate vectors form a bounded family, bounded by the operator norm of `u`. -/
theorem memℓp_infty_apply_single [DecidableEq I] (u : C₀(I, R) →L[R] M) :
    Memℓp (fun i ↦ u (single i 1)) ∞ :=
  memℓp_infty ⟨‖u‖, by
    rintro _ ⟨i, rfl⟩
    simpa using ContinuousLinearMap.le_ringOpNorm u (single i 1)⟩

variable [IsUltrametricDist M] [CompleteSpace M]

/-- **Every continuous linear map out of `C₀(I, R)` is a linear combination map** over Tate
scalars: `u` is the linear combination map of its values at the unit coordinate vectors. -/
theorem linearCombination_self [DecidableEq I] (u : C₀(I, R) →L[R] M) :
    linearCombination R ⟨fun i ↦ u (single i 1), memℓp_infty_apply_single u⟩ = u :=
  continuousLinearMap_ext fun i b ↦ by
    rw [linearCombination_single, ← map_smul, smul_single_one]

/-- Over Tate scalars, every continuous linear map out of `C₀(I, R)` is the linear combination map
of a bounded family. -/
theorem linearCombination_surjective :
    Function.Surjective (linearCombination R : lp (fun _ : I ↦ M) ∞ → C₀(I, R) →L[R] M) := by
  classical
  exact fun u ↦ ⟨_, linearCombination_self u⟩

end Tate

section SMul

variable [DiscreteTopology I] [NormedCommRing R] [NormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]

/-- Over a commutative ring, the linear combination map is linear in the family. -/
theorem linearCombination_smul (c : R) (e : lp (fun _ : I ↦ M) ∞) :
    linearCombination R (c • e) = c • linearCombination R e := by
  classical
  exact continuousLinearMap_ext fun i b ↦ by simp [smul_comm b c]

end SMul

section Pairing

variable [DiscreteTopology I] [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **The pairing** of a bounded family `b` with `a ∈ C₀(I, R)` is the convergent sum
`∑' i, b i * a i`. -/
theorem linearCombination_eq_tsum_mul (b : lp (fun _ : I ↦ R) ∞) (a : C₀(I, R)) :
    linearCombination R b a = ∑' i, b i * a i := by
  simp_rw [linearCombination_apply, smul_eq_mul, mul_comm]

end Pairing

section CommRing

open scoped TauCeti.RingOpNorm

variable [DiscreteTopology I] [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M] [IsUltrametricDist M] [CompleteSpace M]
  [DecidableEq I]

variable (R M) in
/-- **The universal property of `C₀(I, R)`.** Over a commutative ring admitting a multiplicative
pseudo-uniformiser, bounded families `I → M` in a complete ultrametric module correspond to
continuous linear maps `C₀(I, R) →L[R] M`, isometrically for the sup norm and the operator norm.
A family `e` is sent to its linear combination map `a ↦ ∑' i, a i • e i`, and a map `u` to its
values `u (single i 1)` at the unit coordinate vectors. -/
noncomputable def linearCombinationEquiv : lp (fun _ : I ↦ M) ∞ ≃ₗᵢ[R] (C₀(I, R) →L[R] M) where
  toFun := linearCombination R
  invFun u := ⟨fun i ↦ u (single i 1), memℓp_infty_apply_single u⟩
  left_inv e := lp.ext <| funext fun i ↦ by simp
  right_inv := linearCombination_self
  map_add' := linearCombination_add
  map_smul' := linearCombination_smul
  norm_map' := ringOpNorm_linearCombination

/-- The universal property sends a bounded family to its linear combination map. -/
@[simp]
theorem linearCombinationEquiv_apply (e : lp (fun _ : I ↦ M) ∞) :
    linearCombinationEquiv R M e = linearCombination R e :=
  (rfl)

/-- The inverse of the universal property evaluates a map at the unit coordinate vectors. -/
@[simp]
theorem linearCombinationEquiv_symm_apply (u : C₀(I, R) →L[R] M) (i : I) :
    (linearCombinationEquiv R M).symm u i = u (single i 1) :=
  (rfl)

end CommRing

section BoundedSubsums

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [DiscreteTopology I]

/-- The images `u (single i 1)` of the unit coordinate vectors under a continuous linear map
`u : C₀(I, 𝕜) →L[𝕜] X` have finite subsums of norm at most `‖u‖`. -/
theorem norm_sum_apply_single_one_le [DecidableEq I] (u : C₀(I, 𝕜) →L[𝕜] X) (s : Finset I) :
    ‖∑ i ∈ s, u (single i 1)‖ ≤ ‖u‖ := by
  rw [← map_sum]
  refine (u.le_of_opNorm_le_of_le le_rfl ?_).trans_eq (mul_one _)
  rw [← coe_nnNorm, ← NNReal.coe_one, NNReal.coe_le_coe, nnnorm_sum_single]
  exact Finset.sup_le fun _ _ ↦ nnNorm_one.le

variable [CompleteSpace X]

variable (𝕜) in
/-- The **linear combination map** of a family `v` with bounded finite subsums in a real or complex
Banach space: the bounded operator `C₀(I, 𝕜) →L[𝕜] X` sending `a` to `∑' i, a i • v i`. It is the
real or complex counterpart of the ultrametric `linearCombination`, on whose construction and API
it is modelled; both are instances of `linearCombinationOfSummable`. -/
noncomputable def linearCombinationOfBoundedSubsums (v : I → X)
    (hv : ∃ C, ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C) : C₀(I, 𝕜) →L[𝕜] X :=
  linearCombinationOfSummable 𝕜 v
    (fun a ↦ TauCeti.summable_smul_of_forall_norm_sum_le hv.choose_spec a.tendsto_cofinite)
    ⟨4 * hv.choose, fun a ↦ TauCeti.norm_tsum_smul_le_of_forall_norm_sum_le hv.choose_spec
      (norm_nonneg a) (norm_coe_le_norm a)⟩

variable {v : I → X} (hv : ∃ C, ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C)

/-- The linear combination map at `a` is the sum `∑' i, a i • v i`. -/
theorem linearCombinationOfBoundedSubsums_apply (a : C₀(I, 𝕜)) :
    linearCombinationOfBoundedSubsums 𝕜 v hv a = ∑' i, a i • v i :=
  linearCombinationOfSummable_apply _ _ a

/-- The series `∑ i, a i • v i` converges unconditionally to the linear combination map at `a`. -/
theorem hasSum_linearCombinationOfBoundedSubsums (a : C₀(I, 𝕜)) :
    HasSum (fun i ↦ a i • v i) (linearCombinationOfBoundedSubsums 𝕜 v hv a) :=
  hasSum_linearCombinationOfSummable _ _ a

/-- The linear combination map sends the coordinate vector `single i r` to `r • v i`. -/
@[simp]
theorem linearCombinationOfBoundedSubsums_single [DecidableEq I] (i : I) (r : 𝕜) :
    linearCombinationOfBoundedSubsums 𝕜 v hv (single i r) = r • v i :=
  linearCombinationOfSummable_single _ _ i r

/-- The linear combination map of a family with bounded finite subsums is the unique continuous
linear map sending each unit coordinate vector `single i 1` to `v i`. -/
theorem eq_linearCombinationOfBoundedSubsums_iff [DecidableEq I] {u : C₀(I, 𝕜) →L[𝕜] X} :
    u = linearCombinationOfBoundedSubsums 𝕜 v hv ↔ ∀ i, u (single i 1) = v i :=
  eq_linearCombinationOfSummable_iff _ _

/-- The linear combination map has operator norm at most `4 * C` when the finite subsums of `v`
have norm at most `C`. -/
theorem opNorm_linearCombinationOfBoundedSubsums_le {C : ℝ}
    (hC : ∀ s : Finset I, ‖∑ i ∈ s, v i‖ ≤ C) :
    ‖linearCombinationOfBoundedSubsums 𝕜 v hv‖ ≤ 4 * C := by
  have hC0 : 0 ≤ C := by simpa using hC ∅
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a ↦
    TauCeti.norm_tsum_smul_le_of_forall_norm_sum_le hC (norm_nonneg a) (norm_coe_le_norm a)

/-- Let `v` be a sequence with bounded finite subsums in a real or complex Banach space. If `v` is
moreover a basic sequence with basis constant at most `B` whose terms have norm at least `ε > 0`,
then its linear combination map `C₀(ℕ, 𝕜) →L[𝕜] X` is bounded below: it is antilipschitz with
constant `2 * B / ε`, so the closed linear span of `v` is isomorphic to `c₀`. -/
theorem antilipschitzWith_linearCombinationOfBoundedSubsums {v : ℕ → X}
    (hv : ∃ C, ∀ s : Finset ℕ, ‖∑ i ∈ s, v i‖ ≤ C) {ε B : ℝ} (hε : 0 < ε)
    (hvε : ∀ j, ε ≤ ‖v j‖) (hbasic : ∀ (a : ℕ → 𝕜) {m n : ℕ}, m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • v i‖ ≤ B * ‖∑ i ∈ Finset.range n, a i • v i‖) :
    AntilipschitzWith (2 * B / ε).toNNReal (linearCombinationOfBoundedSubsums 𝕜 v hv) := by
  set T := linearCombinationOfBoundedSubsums 𝕜 v hv
  -- Each coefficient is controlled by the later partial sums, and these converge to `T a`.
  have hcoef (a : C₀(ℕ, 𝕜)) (m : ℕ) : ‖a m‖ * ε ≤ 2 * B * ‖T a‖ := by
    have hlim := (hasSum_linearCombinationOfBoundedSubsums hv a).tendsto_sum_nat.norm
    refine ge_of_tendsto (hlim.const_mul (2 * B)) (eventually_atTop.2 ⟨m + 1, fun n hn ↦ ?_⟩)
    calc ‖a m‖ * ε ≤ ‖a m • v m‖ := by rw [norm_smul]; gcongr; exact hvε m
      _ ≤ 2 * B * ‖∑ i ∈ Finset.range n, a i • v i‖ :=
          TauCeti.norm_smul_le_two_mul_mul_norm_sum_range (hbasic a) (by omega)
  refine T.antilipschitz_of_bound fun a ↦ (norm_le (by positivity)).2 fun m ↦ ?_
  calc ‖a m‖ ≤ 2 * B / ε * ‖T a‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]
        exact hcoef a m
    _ ≤ (2 * B / ε).toNNReal * ‖T a‖ := by gcongr; exact Real.le_coe_toNNReal _

end BoundedSubsums

end ZeroAtInftyContinuousMap
