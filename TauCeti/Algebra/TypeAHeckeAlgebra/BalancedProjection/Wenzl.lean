/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Complement
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Wenzl's projection convention for the type-A Hecke algebra

In `TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic`, when `τ * (q + q⁻¹) ^ 2 = 1`, the
isomorphism `TauCeti.BalancedProjectionAlgebra.heckeEquiv` sends each balanced projection generator
`e i` to the `q`-eigenprojection `P i = (q + q⁻¹)⁻¹ • (T i + q⁻¹)` of `T i`, and a Markov trace
with parameter `z = q * η - q⁻¹ * (1 - η)` multiplies by `η` when `P n` is appended.

Wenzl writes the quadratic relation in the rescaled generators `g i = q • T i` and parameter
`Q = q ^ 2`, where `(g i - Q) * (g i + 1) = 0`, and uses the `-1`-eigenprojection

`e_i^W = (1 + Q)⁻¹ • (Q - g i) = (q + q⁻¹)⁻¹ • (q - T i) = 1 - P i`.

This file builds the corresponding presentation isomorphism
`TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv` by composing `heckeEquiv` with the involutive
complement automorphism `TauCeti.InfiniteTypeAHeckeAlgebra.complementEquiv`, proves the generator
and stage comparisons between the two conventions, and shows that a Markov trace with native
projection parameter `η` multiplies by `1 - η` when Wenzl's projection `e_n^W` is appended. It
also records how the index and sign characters correspond to the two scalar characters `e i ↦ 0`
and `e i ↦ 1` in Wenzl's convention.

## Main definitions

* `TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv`: the isomorphism with the infinite type-A
  Hecke algebra sending `e i` to Wenzl's projection `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)`.

## Main results

* `TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv_e`,
  `TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv_e_eq_one_sub_heckeEquiv_e`, and
  `TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv_e_eq_wenzlProjection`: the image of `e i` and
  its comparison `e_i^W = 1 - P i` with the native eigenprojection.
* `TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv_symm_T` and
  `TauCeti.BalancedProjectionAlgebra.wenzlHeckeEquiv_symm_smul_T`: the inverse formulas
  `T i ↦ q - (q + q⁻¹) • e i` and `q • T i ↦ q ^ 2 - (1 + q ^ 2) • e i`.
* `TauCeti.BalancedProjectionAlgebra.map_stage_wenzlHeckeEquiv`: the isomorphism preserves every
  finite stage.
* `TauCeti.InfiniteTypeAHeckeAlgebra.wenzlProjection_eq_one_sub_eigenprojection`,
  `TauCeti.InfiniteTypeAHeckeAlgebra.isIdempotentElem_wenzlProjection`, and
  `TauCeti.InfiniteTypeAHeckeAlgebra.smul_T_eq_smul_one_sub_wenzlProjection_sub`: Wenzl's
  projection `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)` is `1 - P i`, is idempotent, and decomposes
  `q • T i` into eigenvalues `q ^ 2` and `-1`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_wenzlHeckeEquiv_mul_e` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_wenzlProjection`: a Markov trace with
  native projection parameter `η` has Wenzl projection parameter `1 - η`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3,
  for the generators `g i`, parameter `q^2`, and projections `(q^2 - g i) / (1 + q^2)`.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11, for Markov traces in projection generators.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] {τ : R} {q : Rˣ}

namespace BalancedProjectionAlgebra

open InfiniteTypeAHeckeAlgebra (T complementEquiv complementEquiv_T indexCharacter signCharacter)

variable (q) in
/-- **Wenzl's projection isomorphism** between the balanced projection algebra with parameter `τ`
and the infinite type-A Hecke algebra with parameter `q`, when `τ * (q + q⁻¹) ^ 2 = 1`. Defined as
`heckeEquiv` followed by `complementEquiv`, it sends `e i` to `(q + q⁻¹)⁻¹ • (q - T i) =
(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)`, the complementary eigenprojection `1 - P i`. -/
def wenzlHeckeEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    BalancedProjectionAlgebra R τ ≃ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  (heckeEquiv q hτ).trans (complementEquiv q)

variable (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)

/-- `wenzlHeckeEquiv` is `heckeEquiv` followed by `complementEquiv`. -/
theorem wenzlHeckeEquiv_apply (w : BalancedProjectionAlgebra R τ) :
    wenzlHeckeEquiv q hτ w = complementEquiv q (heckeEquiv q hτ w) :=
  (rfl)

/-- The inverse of `wenzlHeckeEquiv` is `complementEquiv` followed by `(heckeEquiv q hτ).symm`. -/
theorem wenzlHeckeEquiv_symm_apply (x : InfiniteTypeAHeckeAlgebra R q) :
    (wenzlHeckeEquiv q hτ).symm x = (heckeEquiv q hτ).symm (complementEquiv q x) := by
  simp [wenzlHeckeEquiv]

/-- Wenzl's isomorphism sends `e i` to `(q + q⁻¹)⁻¹ • (q - T i)`, where
`(q + q⁻¹)⁻¹ = τ * (q + q⁻¹)`. -/
@[simp]
theorem wenzlHeckeEquiv_e (i : ℕ) :
    wenzlHeckeEquiv q hτ (e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (algebraMap R _ (q : R) - T q i) := by
  rw [wenzlHeckeEquiv_apply, heckeEquiv_e, map_smul, map_add, complementEquiv_T, AlgEquiv.commutes]
  simp only [Algebra.algebraMap_eq_smul_one]
  module

/-- **Generator comparison `e_i^W = 1 - P_i`.** Under Wenzl's isomorphism, each generator `e i` maps
to `1` minus its image under the native eigenprojection isomorphism `heckeEquiv`. -/
theorem wenzlHeckeEquiv_e_eq_one_sub_heckeEquiv_e (i : ℕ) :
    wenzlHeckeEquiv q hτ (e τ i) = 1 - heckeEquiv q hτ (e τ i) := by
  have h : τ * ((q : R) + ↑q⁻¹) * ((q : R) + ↑q⁻¹) = 1 := by linear_combination hτ
  rw [wenzlHeckeEquiv_e, heckeEquiv_e]
  simp only [Algebra.algebraMap_eq_smul_one]
  match_scalars
  · linear_combination h
  · ring

/-- **Wenzl's formula `e_i^W = (1 + Q)⁻¹ • (Q - g_i)`.** When `u = 1 + q ^ 2` is a unit, Wenzl's
isomorphism sends `e i` to `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)`. -/
theorem wenzlHeckeEquiv_e_eq_wenzlProjection (u : Rˣ) (hu : (u : R) = 1 + (q : R) ^ 2) (i : ℕ) :
    wenzlHeckeEquiv q hτ (e τ i) =
      (↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i) := by
  have hqu : (u : R) = (q : R) * ((q : R) + ↑q⁻¹) := by
    have hq : (q : R) * ↑q⁻¹ = 1 := q.mul_inv
    linear_combination hu - hq
  have hcoeff : τ * ((q : R) + ↑q⁻¹) = (q : R) * ↑u⁻¹ := by
    have hu' : (u : R) * ↑u⁻¹ = 1 := u.mul_inv
    linear_combination -τ * ((q : R) + ↑q⁻¹) * hu' +
      τ * ((q : R) + ↑q⁻¹) * (↑u⁻¹ : R) * hqu + (↑u⁻¹ : R) * (q : R) * hτ
  rw [wenzlHeckeEquiv_e, hcoeff, mul_comm (q : R), ← smul_smul, smul_sub]
  simp [Algebra.algebraMap_eq_smul_one, smul_smul, sq]

/-- The inverse of Wenzl's isomorphism sends `T i` to `q - (q + q⁻¹) • e i`. -/
@[simp]
theorem wenzlHeckeEquiv_symm_T (i : ℕ) :
    (wenzlHeckeEquiv q hτ).symm (T q i) =
      algebraMap R _ (q : R) - ((q : R) + ↑q⁻¹) • e τ i := by
  rw [wenzlHeckeEquiv_symm_apply, complementEquiv_T, map_sub, AlgEquiv.commutes, heckeEquiv_symm_T]
  simp only [Algebra.algebraMap_eq_smul_one]
  module

/-- In Wenzl's generators `g i = q • T i` and parameter `Q = q ^ 2`, the inverse of Wenzl's
isomorphism sends `g i` to `Q - (1 + Q) • e i`. -/
theorem wenzlHeckeEquiv_symm_smul_T (i : ℕ) :
    (wenzlHeckeEquiv q hτ).symm ((q : R) • T q i) =
      algebraMap R _ ((q : R) ^ 2) - (1 + (q : R) ^ 2) • e τ i := by
  have hq : (q : R) * ↑q⁻¹ = 1 := q.mul_inv
  rw [map_smul, wenzlHeckeEquiv_symm_T, smul_sub]
  simp only [Algebra.algebraMap_eq_smul_one, smul_smul]
  match_scalars
  · ring
  · linear_combination -hq

/-- Wenzl's isomorphism carries the stage of the first `n` strands onto the corresponding stage of
the infinite type-A Hecke algebra. -/
theorem map_stage_wenzlHeckeEquiv (n : ℕ) :
    (stage R τ n).map (wenzlHeckeEquiv q hτ : BalancedProjectionAlgebra R τ →ₐ[R] _) =
      InfiniteTypeAHeckeAlgebra.stage R q n := by
  refine le_antisymm
    (Subalgebra.map_le.2 fun w hw ↦ ?_)
    (fun x hx ↦ Subalgebra.mem_map.2
      ⟨(wenzlHeckeEquiv q hτ).symm x, ?_, (wenzlHeckeEquiv q hτ).apply_symm_apply x⟩)
  · rw [Subalgebra.mem_comap, AlgEquiv.coe_toAlgHom, wenzlHeckeEquiv_apply,
      InfiniteTypeAHeckeAlgebra.complementEquiv_mem_stage_iff, heckeEquiv_mem_stage_iff]
    exact hw
  · rw [wenzlHeckeEquiv_symm_apply, ← heckeEquiv_mem_stage_iff hτ,
      AlgEquiv.apply_symm_apply, InfiniteTypeAHeckeAlgebra.complementEquiv_mem_stage_iff]
    exact hx

/-- An element lies in a stage of the balanced projection algebra exactly when its image under
Wenzl's isomorphism lies in the corresponding stage of the infinite type-A Hecke algebra. -/
@[simp]
theorem wenzlHeckeEquiv_mem_stage_iff {n : ℕ} {w : BalancedProjectionAlgebra R τ} :
    wenzlHeckeEquiv q hτ w ∈ InfiniteTypeAHeckeAlgebra.stage R q n ↔ w ∈ stage R τ n := by
  rw [wenzlHeckeEquiv_apply, InfiniteTypeAHeckeAlgebra.complementEquiv_mem_stage_iff,
    heckeEquiv_mem_stage_iff]

/-! ### Scalar characters in Wenzl's projection convention -/

/-- Under Wenzl's isomorphism `wenzlHeckeEquiv`, the index character `T i ↦ q` (`g i ↦ q ^ 2`)
corresponds to the scalar character `e i ↦ 0`. -/
@[simp]
theorem indexCharacter_wenzlHeckeEquiv (w : BalancedProjectionAlgebra R τ) :
    indexCharacter R q (wenzlHeckeEquiv q hτ w) = character 0 .zero w := by
  rw [wenzlHeckeEquiv_apply, InfiniteTypeAHeckeAlgebra.indexCharacter_complementEquiv,
    signCharacter_heckeEquiv]

/-- Under Wenzl's isomorphism `wenzlHeckeEquiv`, the sign character `T i ↦ -q⁻¹` (`g i ↦ -1`)
corresponds to the scalar character `e i ↦ 1`. -/
@[simp]
theorem signCharacter_wenzlHeckeEquiv (w : BalancedProjectionAlgebra R τ) :
    signCharacter R q (wenzlHeckeEquiv q hτ w) = character 1 .one w := by
  rw [wenzlHeckeEquiv_apply, InfiniteTypeAHeckeAlgebra.signCharacter_complementEquiv,
    indexCharacter_heckeEquiv]

end BalancedProjectionAlgebra

/-! ### Wenzl's projection and Markov trace parameters on the Hecke algebra -/

namespace InfiniteTypeAHeckeAlgebra

private theorem val_inv_mul_eq_add_inv (u : Rˣ) (hu : (u : R) = 1 + (q : R) ^ 2) :
    ((q⁻¹ * u : Rˣ) : R) = (q : R) + ↑q⁻¹ := by
  rw [Units.val_mul, hu, mul_add, mul_one, sq, ← mul_assoc, q.inv_mul, one_mul, add_comm]

/-- **Comparison of Wenzl's projection with the native eigenprojection.** Let `u = 1 + q ^ 2` be a
unit, so `q⁻¹ * u = q + q⁻¹`. Wenzl's projection `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)` equals
`1 - P i`, where `P i = (q + q⁻¹)⁻¹ • (T i + q⁻¹)` is the `q`-eigenprojection of `T i`. -/
theorem wenzlProjection_eq_one_sub_eigenprojection (u : Rˣ) (hu : (u : R) = 1 + (q : R) ^ 2)
    (i : ℕ) :
    (↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i) =
      1 - (↑(q⁻¹ * u)⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R)) := by
  set s : Rˣ := q⁻¹ * u
  have hs : (s : R) = (q : R) + ↑q⁻¹ := val_inv_mul_eq_add_inv u hu
  have hτ : (↑s⁻¹ : R) ^ 2 * ((q : R) + ↑q⁻¹) ^ 2 = 1 := by
    rw [← hs, ← mul_pow, s.inv_mul, one_pow]
  have h := (BalancedProjectionAlgebra.wenzlHeckeEquiv_e_eq_wenzlProjection hτ u hu i).symm.trans
    (BalancedProjectionAlgebra.wenzlHeckeEquiv_e_eq_one_sub_heckeEquiv_e hτ i)
  rwa [BalancedProjectionAlgebra.heckeEquiv_e, ← hs, sq (↑s⁻¹ : R), mul_assoc, s.inv_mul,
    mul_one] at h

/-- Wenzl's projection is the image of the native eigenprojection under `complementEquiv`. -/
theorem wenzlProjection_eq_complementEquiv_eigenprojection (u : Rˣ)
    (hu : (u : R) = 1 + (q : R) ^ 2) (i : ℕ) :
    (↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i) =
      complementEquiv q ((↑(q⁻¹ * u)⁻¹ : R) • (T q i + algebraMap R _ (↑q⁻¹ : R))) := by
  rw [wenzlProjection_eq_one_sub_eigenprojection u hu,
    complementEquiv_eigenprojection q (q⁻¹ * u) (val_inv_mul_eq_add_inv u hu)]

/-- Wenzl's projection `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)` is idempotent whenever `u = 1 + q ^ 2`
is a unit. -/
theorem isIdempotentElem_wenzlProjection (u : Rˣ) (hu : (u : R) = 1 + (q : R) ^ 2) (i : ℕ) :
    IsIdempotentElem ((↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i)) := by
  rw [wenzlProjection_eq_one_sub_eigenprojection u hu]
  exact (isIdempotentElem_eigenprojection (q⁻¹ * u) (val_inv_mul_eq_add_inv u hu) i).one_sub

/-- **Eigenvalue decomposition of Wenzl's generator `g i = q • T i`.** With `e_i^W` Wenzl's
projection `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)`, `g i = q ^ 2 • (1 - e_i^W) - e_i^W`. -/
theorem smul_T_eq_smul_one_sub_wenzlProjection_sub (u : Rˣ) (hu : (u : R) = 1 + (q : R) ^ 2)
    (i : ℕ) :
    (q : R) • T q i =
      ((q : R) ^ 2) • (1 - (↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i)) -
        (↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i) := by
  have hu' : (↑u⁻¹ : R) * (1 + (q : R) ^ 2) = 1 := hu ▸ u.inv_mul
  simp only [Algebra.algebraMap_eq_smul_one]
  match_scalars
  · linear_combination -(q : R) * hu'
  · linear_combination (q : R) ^ 2 * hu'

namespace IsMarkovTrace

open BalancedProjectionAlgebra

variable {z η : R} {μ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- **The Wenzl projection parameter of a Hecke Markov trace.** Transported along
`wenzlHeckeEquiv`, a Markov trace with parameter `z` multiplies by `(q - z) / (q + q⁻¹)` when a
new last projection `e n` is appended, where `(q + q⁻¹)⁻¹ = τ * (q + q⁻¹)`. -/
theorem map_wenzlHeckeEquiv_mul_e (hμ : IsMarkovTrace z μ) (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    {n : ℕ} {w : BalancedProjectionAlgebra R τ}
    (hw : w ∈ BalancedProjectionAlgebra.stage R τ (n + 1)) :
    μ (wenzlHeckeEquiv q hτ (w * e τ n)) =
      τ * ((q : R) + ↑q⁻¹) * ((q : R) - z) * μ (wenzlHeckeEquiv q hτ w) := by
  have h := hμ.comp_complementEquiv.map_heckeEquiv_mul_e hτ hw
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ← wenzlHeckeEquiv_apply,
    sub_add_eq_add_sub, sub_add_cancel, add_sub_cancel_right] using h

/-- **Trace comparison `η_W = 1 - η`.** If `z = q * η - q⁻¹ * (1 - η)`, so that `η` is the native
projection parameter of `μ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_eigenprojection`), then appending Wenzl's
projection `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T n)` to `x` in the stage on `n + 1` strands multiplies
`μ x` by `1 - η`. -/
theorem map_mul_wenzlProjection (hμ : IsMarkovTrace z μ) (u : Rˣ)
    (hu : (u : R) = 1 + (q : R) ^ 2) (hz : z = q * η - ↑q⁻¹ * (1 - η)) {n : ℕ}
    {x : InfiniteTypeAHeckeAlgebra R q} (hx : x ∈ InfiniteTypeAHeckeAlgebra.stage R q (n + 1)) :
    μ (x * (↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q n)) = (1 - η) * μ x := by
  rw [wenzlProjection_eq_one_sub_eigenprojection u hu, mul_sub, mul_one, map_sub,
    hμ.map_mul_eigenprojection (q⁻¹ * u) (val_inv_mul_eq_add_inv u hu) hz hx]
  ring

end IsMarkovTrace

end InfiniteTypeAHeckeAlgebra

end TauCeti
