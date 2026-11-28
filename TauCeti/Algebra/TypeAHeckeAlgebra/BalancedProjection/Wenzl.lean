/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Complement
import TauCeti.Algebra.Ring.Units
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
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_wenzlHeckeEquiv_mul_e`: transported along
  `wenzlHeckeEquiv`, a Markov trace with parameter `z` multiplies by `(q - z) / (q + q⁻¹)` when a
  new last projection is appended.

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

open InfiniteTypeAHeckeAlgebra (T complementEquiv complementEquiv_T indexCharacter signCharacter
  wenzlProjection_eq_one_sub_eigenprojection)

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
    wenzlHeckeEquiv q hτ w = complementEquiv q (heckeEquiv q hτ w) := by
  rw [wenzlHeckeEquiv, AlgEquiv.trans_apply]

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
  rw [wenzlHeckeEquiv_e, heckeEquiv_e]
  simp only [Algebra.algebraMap_eq_smul_one]
  match_scalars
  · linear_combination hτ
  · ring

/-- **Wenzl's formula `e_i^W = (1 + Q)⁻¹ • (Q - g_i)`.** When `u = 1 + q ^ 2` is a unit, Wenzl's
isomorphism sends `e i` to `(1 + q ^ 2)⁻¹ • (q ^ 2 - q • T i)`. -/
theorem wenzlHeckeEquiv_e_eq_wenzlProjection (u : Rˣ) (hu : (u : R) = 1 + (q : R) ^ 2) (i : ℕ) :
    wenzlHeckeEquiv q hτ (e τ i) =
      (↑u⁻¹ : R) • (algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i) := by
  have hs : ((q⁻¹ * u : Rˣ) : R) = (q : R) + ↑q⁻¹ := Units.val_inv_mul_eq_val_add_val_inv hu
  have hinv : (↑(q⁻¹ * u)⁻¹ : R) * ((q : R) + ↑q⁻¹) = 1 := by
    rw [← hs, Units.inv_mul]
  have hcoeff : τ * ((q : R) + ↑q⁻¹) = ↑(q⁻¹ * u)⁻¹ := by
    linear_combination (↑(q⁻¹ * u)⁻¹ : R) * hτ - τ * ((q : R) + ↑q⁻¹) * hinv
  rw [wenzlHeckeEquiv_e_eq_one_sub_heckeEquiv_e, heckeEquiv_e, hcoeff,
    wenzlProjection_eq_one_sub_eigenprojection u hu]

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

/-- An element lies in a stage of the balanced projection algebra exactly when its image under
Wenzl's isomorphism lies in the corresponding stage of the infinite type-A Hecke algebra. -/
@[simp]
theorem wenzlHeckeEquiv_mem_stage_iff {n : ℕ} {w : BalancedProjectionAlgebra R τ} :
    wenzlHeckeEquiv q hτ w ∈ InfiniteTypeAHeckeAlgebra.stage R q n ↔ w ∈ stage R τ n := by
  rw [wenzlHeckeEquiv_apply, InfiniteTypeAHeckeAlgebra.complementEquiv_mem_stage_iff,
    heckeEquiv_mem_stage_iff]

/-- Wenzl's isomorphism carries the stage of the first `n` strands onto the corresponding stage of
the infinite type-A Hecke algebra. -/
theorem map_stage_wenzlHeckeEquiv (n : ℕ) :
    (stage R τ n).map (wenzlHeckeEquiv q hτ : BalancedProjectionAlgebra R τ →ₐ[R] _) =
      InfiniteTypeAHeckeAlgebra.stage R q n := by
  ext x
  simp only [Subalgebra.mem_map, AlgEquiv.coe_toAlgHom]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (wenzlHeckeEquiv_mem_stage_iff hτ).2 hw
  · intro hx
    refine ⟨(wenzlHeckeEquiv q hτ).symm x, ?_, (wenzlHeckeEquiv q hτ).apply_symm_apply x⟩
    exact (wenzlHeckeEquiv_mem_stage_iff hτ).1 (by simpa only [AlgEquiv.apply_symm_apply] using hx)

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

namespace InfiniteTypeAHeckeAlgebra.IsMarkovTrace

open BalancedProjectionAlgebra

variable {z : R} {μ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}

/-- **The Wenzl projection parameter of a Hecke Markov trace.** Transported along
`wenzlHeckeEquiv`, a Markov trace with parameter `z` multiplies by `(q - z) / (q + q⁻¹)` when a
new last projection `e n` is appended, where `(q + q⁻¹)⁻¹ = τ * (q + q⁻¹)`. -/
theorem map_wenzlHeckeEquiv_mul_e (hμ : IsMarkovTrace z μ) (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    {n : ℕ} {w : BalancedProjectionAlgebra R τ}
    (hw : w ∈ BalancedProjectionAlgebra.stage R τ (n + 1)) :
    μ (wenzlHeckeEquiv q hτ (w * e τ n)) =
      τ * ((q : R) + ↑q⁻¹) * ((q : R) - z) * μ (wenzlHeckeEquiv q hτ w) := by
  have hz : (q : R) - ↑q⁻¹ - z + ↑q⁻¹ = q - z := by ring
  have h := hμ.comp_complementEquiv.map_heckeEquiv_mul_e hτ hw
  rw [hz] at h
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ← wenzlHeckeEquiv_apply] using h

end InfiniteTypeAHeckeAlgebra.IsMarkovTrace

end TauCeti
