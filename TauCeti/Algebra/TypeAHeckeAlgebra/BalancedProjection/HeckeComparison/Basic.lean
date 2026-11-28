/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Ring.Units

/-!
# Algebraic comparison between the balanced projection and type-A Hecke presentations

When `τ * (q + q⁻¹) ^ 2 = 1` for a unit `q : Rˣ`, the change of generators
`T i = (q + q⁻¹) • e i - q⁻¹`, with inverse `e i = (q + q⁻¹)⁻¹ • (T i + q⁻¹)`, identifies
`BalancedProjectionAlgebra R τ` with `InfiniteTypeAHeckeAlgebra R q`
(`TauCeti.BalancedProjectionAlgebra.heckeEquiv`). Here `(q + q⁻¹)⁻¹ = τ * (q + q⁻¹)`.

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.mul_self_sub_eq_smul`,
  `TauCeti.BalancedProjectionAlgebra.mul_mul_sub_mul_mul_eq_smul`,
  `TauCeti.BalancedProjectionAlgebra.mul_sub_mul_eq_smul`: general change-of-generator identities.
* `TauCeti.BalancedProjectionAlgebra.addInvUnit`: `q + q⁻¹` as a unit when `τ * (q + q⁻¹) ^ 2 = 1`.
* `TauCeti.BalancedProjectionAlgebra.heckeEquiv`: `R`-algebra isomorphism with
  `InfiniteTypeAHeckeAlgebra R q`.
* `TauCeti.BalancedProjectionAlgebra.map_stage_heckeEquiv`,
  `TauCeti.BalancedProjectionAlgebra.heckeEquiv_mem_stage_iff`: finite-stage matching.
* `TauCeti.BalancedProjectionAlgebra.indexCharacter_heckeEquiv`,
  `TauCeti.BalancedProjectionAlgebra.signCharacter_heckeEquiv`: scalar character matching.
* `TauCeti.BalancedProjectionAlgebra.heckeEquiv_one_sub_e`,
  `TauCeti.BalancedProjectionAlgebra.one_add_sq_smul_heckeEquiv_one_sub_e`: action on `1 - e i`
  and Wenzl's eigenprojection.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11.
-/

public section

namespace TauCeti.BalancedProjectionAlgebra

variable {R : Type*} [CommRing R] {τ : R}

section ChangeOfGenerators

/-! ### The change of generators `T = (q + q⁻¹) • e - q⁻¹`

The three identities below hold in every `R`-algebra and compare the Hecke relations of
`T = (q + q⁻¹) • e - q⁻¹` with the projection relations of `e`. -/

variable {A : Type*} [Ring A] [Algebra R A] {q : Rˣ}

/-- The quadratic defect of `T = (q + q⁻¹) • e - q⁻¹` is `(q + q⁻¹) ^ 2` times the idempotence
defect of `e`. -/
theorem mul_self_sub_eq_smul {e x : A} (hx : x = ((q : R) + ↑q⁻¹) • e - algebraMap R A ↑q⁻¹) :
    x * x - (((q : R) - ↑q⁻¹) • x + 1) = ((q : R) + ↑q⁻¹) ^ 2 • (e * e - e) := by
  have hq : (q : R) * ↑q⁻¹ = 1 := q.mul_inv
  subst hx
  simp only [Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, one_mul, mul_one, smul_sub]
  match_scalars <;> grind

/-- For idempotents `e` and `f` and `τ * (q + q⁻¹) ^ 2 = 1`, the braid defect of
`T = (q + q⁻¹) • e - q⁻¹` and `T' = (q + q⁻¹) • f - q⁻¹` is `(q + q⁻¹) ^ 3` times the balanced
defect `(e * f * e - τ • e) - (f * e * f - τ • f)`. -/
theorem mul_mul_sub_mul_mul_eq_smul (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) {e f x y : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hx : x = ((q : R) + ↑q⁻¹) • e - algebraMap R A ↑q⁻¹)
    (hy : y = ((q : R) + ↑q⁻¹) • f - algebraMap R A ↑q⁻¹) :
    x * y * x - y * x * y =
      ((q : R) + ↑q⁻¹) ^ 3 • ((e * f * e - τ • e) - (f * e * f - τ • f)) := by
  have hq : (q : R) * ↑q⁻¹ = 1 := q.mul_inv
  subst hx hy
  simp only [Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, one_mul, mul_one, smul_sub, mul_assoc, he.eq, hf.eq]
  match_scalars <;> grind

/-- The commutator of `T = (q + q⁻¹) • e - q⁻¹` and `T' = (q + q⁻¹) • f - q⁻¹` is
`(q + q⁻¹) ^ 2` times the commutator of `e` and `f`. -/
theorem mul_sub_mul_eq_smul {e f x y : A}
    (hx : x = ((q : R) + ↑q⁻¹) • e - algebraMap R A ↑q⁻¹)
    (hy : y = ((q : R) + ↑q⁻¹) • f - algebraMap R A ↑q⁻¹) :
    x * y - y * x = ((q : R) + ↑q⁻¹) ^ 2 • (e * f - f * e) := by
  subst hx hy
  simp only [Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, one_mul, mul_one, smul_sub]
  match_scalars <;> ring

end ChangeOfGenerators

section HeckeEquiv

/-! ### The isomorphism with the infinite type-A Hecke algebra -/

open InfiniteTypeAHeckeAlgebra (T)

variable {q : Rˣ}

/-- When `τ * (q + q⁻¹) ^ 2 = 1`, the sum `q + q⁻¹` as a unit with inverse `τ * (q + q⁻¹)`. -/
def addInvUnit (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) : Rˣ :=
  Units.mkOfMulEqOne ((q : R) + ↑q⁻¹) (τ * ((q : R) + ↑q⁻¹)) (by linear_combination hτ)

/-- The underlying element of `addInvUnit hτ` is `q + q⁻¹`. -/
@[simp]
theorem val_addInvUnit (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) : (addInvUnit hτ : R) = q + ↑q⁻¹ :=
  Units.val_mkOfMulEqOne _

/-- The inverse of `addInvUnit hτ` is `τ * (q + q⁻¹)`. -/
@[simp]
theorem val_inv_addInvUnit (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    (↑(addInvUnit hτ)⁻¹ : R) = τ * ((q : R) + ↑q⁻¹) :=
  Units.inv_eq_of_mul_eq_one_right (by rw [val_addInvUnit]; linear_combination hτ)

/-- The Hecke generator is recovered from the projection `(q + q⁻¹)⁻¹ • (T i + q⁻¹)`. -/
private theorem T_eq_smul_sub (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    T q i = ((q : R) + ↑q⁻¹) • ((τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹)) -
      algebraMap R (InfiniteTypeAHeckeAlgebra R q) ↑q⁻¹ := by
  rw [smul_smul, ← val_inv_addInvUnit hτ, ← val_addInvUnit hτ, Units.mul_inv, one_smul,
    add_sub_cancel_right]

/-- The projections `(q + q⁻¹)⁻¹ • (T i + q⁻¹)` of the Hecke algebra are idempotent. -/
private theorem isIdempotentElem_smul_T_add (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    IsIdempotentElem ((τ * ((q : R) + ↑q⁻¹)) •
      (T q i + algebraMap R (InfiniteTypeAHeckeAlgebra R q) ↑q⁻¹)) := by
  simpa only [val_inv_addInvUnit] using
    InfiniteTypeAHeckeAlgebra.isIdempotentElem_eigenprojection (addInvUnit hτ)
      (val_addInvUnit hτ) i

/-- The projections `(q + q⁻¹)⁻¹ • (T i + q⁻¹)` of the Hecke algebra satisfy the balanced
presentation. -/
private def toHecke (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    BalancedProjectionAlgebra R τ →ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  lift (fun i ↦ (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹))
    (isIdempotentElem_smul_T_add hτ)
    (fun i ↦ by
      refine sub_eq_zero.1 ((((isUnit_pow_iff two_ne_zero).1
        (IsUnit.of_mul_eq_one_right τ hτ)).pow 3).smul_eq_zero.1 ?_)
      rw [← mul_mul_sub_mul_mul_eq_smul hτ (isIdempotentElem_smul_T_add hτ i)
        (isIdempotentElem_smul_T_add hτ (i + 1)) (T_eq_smul_sub hτ i)
        (T_eq_smul_sub hτ (i + 1)), InfiniteTypeAHeckeAlgebra.T_braid, sub_self])
    (fun h ↦ by
      refine sub_eq_zero.1 ((IsUnit.of_mul_eq_one_right τ hτ).smul_eq_zero.1 ?_)
      rw [← mul_sub_mul_eq_smul (T_eq_smul_sub hτ _) (T_eq_smul_sub hτ _),
        (InfiniteTypeAHeckeAlgebra.commute_T (Or.inl h)).eq, sub_self])

/-- The Hecke generators `(q + q⁻¹) • e i - q⁻¹` of the balanced projection algebra satisfy the
Hecke presentation. -/
private def ofHecke (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    InfiniteTypeAHeckeAlgebra R q →ₐ[R] BalancedProjectionAlgebra R τ :=
  InfiniteTypeAHeckeAlgebra.lift (fun i ↦ ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹)
    (fun i ↦ by rw [← sub_eq_zero, mul_self_sub_eq_smul rfl, e_mul_self, sub_self, smul_zero])
    (fun i ↦ by
      rw [← sub_eq_zero, mul_mul_sub_mul_mul_eq_smul hτ (isIdempotentElem_e i)
        (isIdempotentElem_e (i + 1)) rfl rfl, e_balanced, sub_self, smul_zero])
    (fun h ↦ by
      rw [← sub_eq_zero, mul_sub_mul_eq_smul rfl rfl, (commute_e (Or.inl h)).eq, sub_self,
        smul_zero])

private theorem toHecke_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    toHecke hτ (e τ i) = (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) :=
  lift_e _ _ _ _ i

private theorem ofHecke_T (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    ofHecke hτ (T q i) = ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ :=
  InfiniteTypeAHeckeAlgebra.lift_T _ _ _ _ i

variable (q) in
/-- The balanced projection algebra with parameter `τ` is isomorphic to the infinite type-A Hecke
algebra with parameter `q` when `τ * (q + q⁻¹) ^ 2 = 1`, by the change of generators
`e i ↦ (q + q⁻¹)⁻¹ • (T i + q⁻¹)`, with inverse `T i ↦ (q + q⁻¹) • e i - q⁻¹`. Here
`(q + q⁻¹)⁻¹ = τ * (q + q⁻¹)`. -/
def heckeEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) :
    BalancedProjectionAlgebra R τ ≃ₐ[R] InfiniteTypeAHeckeAlgebra R q :=
  AlgEquiv.ofAlgHom (toHecke hτ) (ofHecke hτ)
    (InfiniteTypeAHeckeAlgebra.hom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, ofHecke_T, toHecke_e, map_sub, map_smul, AlgHom.commutes,
        AlgHom.id_apply]
      exact (T_eq_smul_sub hτ i).symm)
    (hom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, toHecke_e, ofHecke_T, map_smul, map_add, AlgHom.commutes,
        sub_add_cancel, smul_smul, AlgHom.id_apply]
      rw [← val_inv_addInvUnit hτ, ← val_addInvUnit hτ, Units.inv_mul, one_smul])

variable (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)

/-- The isomorphism sends the projection `e i` to `(q + q⁻¹)⁻¹ • (T i + q⁻¹)`, where
`(q + q⁻¹)⁻¹ = τ * (q + q⁻¹)`. -/
@[simp]
theorem heckeEquiv_e (i : ℕ) :
    heckeEquiv q hτ (e τ i) = (τ * ((q : R) + ↑q⁻¹)) • (T q i + algebraMap R _ ↑q⁻¹) :=
  lift_e _ _ _ _ i

/-- The Hecke generator `T i` is recovered from the image of `e i` under `heckeEquiv`:
`T i = (q + q⁻¹) • heckeEquiv q hτ (e τ i) - q⁻¹`. -/
theorem T_eq_smul_heckeEquiv_e_sub (i : ℕ) :
    T q i = ((q : R) + ↑q⁻¹) • heckeEquiv q hτ (e τ i) - algebraMap R _ ↑q⁻¹ := by
  rw [heckeEquiv_e]
  exact T_eq_smul_sub hτ i

/-- The inverse isomorphism sends the Hecke generator `T i` to `(q + q⁻¹) • e i - q⁻¹`. -/
@[simp]
theorem heckeEquiv_symm_T (i : ℕ) :
    (heckeEquiv q hτ).symm (T q i) = ((q : R) + ↑q⁻¹) • e τ i - algebraMap R _ ↑q⁻¹ :=
  InfiniteTypeAHeckeAlgebra.lift_T _ _ _ _ i

/-- The isomorphism carries the stage of the first `n` strands onto the corresponding stage of the
infinite type-A Hecke algebra. -/
theorem map_stage_heckeEquiv (n : ℕ) :
    (stage R τ n).map (heckeEquiv q hτ : BalancedProjectionAlgebra R τ →ₐ[R] _) =
      InfiniteTypeAHeckeAlgebra.stage R q n := by
  refine le_antisymm (Subalgebra.map_le.2 <| stage_le_iff.2 fun i hi ↦ ?_)
    (InfiniteTypeAHeckeAlgebra.stage_le_iff.2 fun i hi ↦
      Subalgebra.mem_map.2
        ⟨(heckeEquiv q hτ).symm (T q i), ?_, (heckeEquiv q hτ).apply_symm_apply _⟩)
  · rw [Subalgebra.mem_comap, AlgEquiv.coe_toAlgHom, heckeEquiv_e]
    exact Subalgebra.smul_mem _
      (add_mem (InfiniteTypeAHeckeAlgebra.T_mem_stage hi) (Subalgebra.algebraMap_mem _ _)) _
  · rw [heckeEquiv_symm_T]
    exact sub_mem (Subalgebra.smul_mem _ (e_mem_stage hi) _) (Subalgebra.algebraMap_mem _ _)

/-- An element lies in a stage of the balanced projection algebra exactly when its image under
the isomorphism lies in the corresponding stage of the infinite type-A Hecke algebra. -/
@[simp]
theorem heckeEquiv_mem_stage_iff {n : ℕ} {w : BalancedProjectionAlgebra R τ} :
    heckeEquiv q hτ w ∈ InfiniteTypeAHeckeAlgebra.stage R q n ↔ w ∈ stage R τ n := by
  rw [← map_stage_heckeEquiv hτ, Subalgebra.mem_map]
  exact ⟨fun ⟨v, hv, h⟩ ↦ (heckeEquiv q hτ).injective h ▸ hv, fun h ↦ ⟨w, h, rfl⟩⟩

/-- Under `heckeEquiv`, the Hecke index character `T i ↦ q` pulls back to `e i ↦ 1`. -/
@[simp]
theorem indexCharacter_heckeEquiv (x : BalancedProjectionAlgebra R τ) :
    InfiniteTypeAHeckeAlgebra.indexCharacter R q (heckeEquiv q hτ x) = character 1 .one x :=
  DFunLike.congr_fun
    (hom_ext (F := (InfiniteTypeAHeckeAlgebra.indexCharacter R q).comp (heckeEquiv q hτ).toAlgHom)
      (G := character 1 .one)
      fun i ↦ by
        simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, heckeEquiv_e, map_smul, map_add,
          InfiniteTypeAHeckeAlgebra.indexCharacter_T, AlgHom.commutes, Algebra.algebraMap_self,
          RingHom.id_apply, smul_eq_mul, character_e]
        linear_combination hτ) x

/-- Under `heckeEquiv`, the Hecke sign character `T i ↦ -q⁻¹` pulls back to `e i ↦ 0`. -/
@[simp]
theorem signCharacter_heckeEquiv (x : BalancedProjectionAlgebra R τ) :
    InfiniteTypeAHeckeAlgebra.signCharacter R q (heckeEquiv q hτ x) = character 0 .zero x :=
  DFunLike.congr_fun
    (hom_ext (F := (InfiniteTypeAHeckeAlgebra.signCharacter R q).comp (heckeEquiv q hτ).toAlgHom)
      (G := character 0 .zero) fun i ↦ by simp) x

@[simp]
theorem character_one_heckeEquiv_symm (x : InfiniteTypeAHeckeAlgebra R q) :
    character 1 .one ((heckeEquiv q hτ).symm x) =
      InfiniteTypeAHeckeAlgebra.indexCharacter R q x := by
  simpa using (indexCharacter_heckeEquiv hτ ((heckeEquiv q hτ).symm x)).symm

@[simp]
theorem character_zero_heckeEquiv_symm (x : InfiniteTypeAHeckeAlgebra R q) :
    character 0 .zero ((heckeEquiv q hτ).symm x) =
      InfiniteTypeAHeckeAlgebra.signCharacter R q x := by
  simpa using (signCharacter_heckeEquiv hτ ((heckeEquiv q hτ).symm x)).symm

end HeckeEquiv

section HeckeEigenprojection

open InfiniteTypeAHeckeAlgebra (T)

variable {q : Rˣ}

/-- The complementary projection `1 - e i` maps under `heckeEquiv` to the `-q⁻¹`-eigenprojection
`(q + q⁻¹)⁻¹ • (q - T i)`. -/
theorem heckeEquiv_one_sub_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeEquiv q hτ (1 - e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (algebraMap R _ (q : R) - T q i) := by
  rw [map_sub, map_one, heckeEquiv_e]
  simp only [Algebra.algebraMap_eq_smul_one]
  match_scalars
  · linear_combination -hτ
  · ring

/-- In Wenzl's generators `g i = q • T i` with `Q = q ^ 2`, the complementary projection `1 - e i`
satisfies `(1 + Q) • e_i^W = Q - g i`. -/
theorem one_add_sq_smul_heckeEquiv_one_sub_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    ((1 : R) + (q : R) ^ 2) • heckeEquiv q hτ (1 - e τ i) =
      algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i := by
  have hcoeff : ((1 : R) + (q : R) ^ 2) * (τ * ((q : R) + ↑q⁻¹)) = q := by
    rw [← Units.val_mul_add_inv q, mul_assoc, ← val_inv_addInvUnit hτ, ← val_addInvUnit hτ,
      Units.mul_inv, mul_one]
  rw [heckeEquiv_one_sub_e hτ, smul_smul, hcoeff, smul_sub, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, smul_smul, ← sq]

end HeckeEigenprojection

end TauCeti.BalancedProjectionAlgebra
