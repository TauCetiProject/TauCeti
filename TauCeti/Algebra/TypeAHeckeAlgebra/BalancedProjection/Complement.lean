/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Complement
import TauCeti.Algebra.Ring.Idempotent.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The complement automorphism of the balanced projection algebra

For idempotents `p` and `q`, replacing `p` and `q` by `1 - p` and `1 - q` negates the balanced
defect `(p * q * p - t • p) - (q * p * q - t • q)`. Sending `e i` to `1 - e i` therefore defines an
involutive `R`-algebra automorphism `TauCeti.BalancedProjectionAlgebra.complementEquiv` at the same
parameter `τ`. It preserves every finite stage, exchanges scalar characters `c ↔ 1 - c`, and
intertwines `TauCeti.InfiniteTypeAHeckeAlgebra.complementEquiv` under `heckeEquiv`, mapping
`1 - e i` to Wenzl's eigenprojection `(q + q⁻¹)⁻¹ • (q - T i)`.

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.complementEquiv`, `stageComplementEquiv`: the involutive
  complement automorphism `e i ↦ 1 - e i` and its restriction to finite stages.
* `TauCeti.BalancedProjectionAlgebra.character_complementEquiv`: precomposing a scalar character
  with `complementEquiv` sends `c` to `1 - c`.
* `TauCeti.BalancedProjectionAlgebra.heckeEquiv_complementEquiv`, `heckeEquiv_one_sub_e`,
  `one_add_sq_smul_heckeEquiv_one_sub_e`: Hecke compatibility of `complementEquiv` and Wenzl's
  eigenprojection.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11.
-/

public section

namespace TauCeti.BalancedProjectionAlgebra

variable {R : Type*} [CommRing R]

section Complement

variable (τ : R)

private def complementHom : BalancedProjectionAlgebra R τ →ₐ[R] BalancedProjectionAlgebra R τ :=
  lift (fun i ↦ 1 - e τ i) (fun i ↦ (isIdempotentElem_e i).one_sub)
    (fun i ↦ (isIdempotentElem_e i).one_sub_mul_mul_sub_smul_eq
      (isIdempotentElem_e (i + 1)) (e_balanced i))
    (fun h ↦ by simp [sub_mul, mul_sub, (commute_e (Or.inl h)).eq]; abel)

/-- The involutive complement automorphism of the balanced projection algebra, sending each
generator `e i` to `1 - e i` at the same parameter `τ`. -/
def complementEquiv : BalancedProjectionAlgebra R τ ≃ₐ[R] BalancedProjectionAlgebra R τ :=
  AlgEquiv.ofAlgHom (complementHom τ) (complementHom τ)
    (hom_ext fun i ↦ by simp [complementHom]) (hom_ext fun i ↦ by simp [complementHom])

@[simp]
theorem complementEquiv_e (i : ℕ) : complementEquiv (R := R) τ (e τ i) = 1 - e τ i :=
  lift_e _ _ _ _ i

@[simp]
theorem complementEquiv_symm : (complementEquiv (R := R) τ).symm = complementEquiv τ :=
  AlgEquiv.ofAlgHom_symm _ _ _ _

@[simp]
theorem complementEquiv_complementEquiv (x : BalancedProjectionAlgebra R τ) :
    complementEquiv τ (complementEquiv τ x) = x := by
  simpa only [complementEquiv_symm] using (complementEquiv (R := R) τ).symm_apply_apply x

/-- Every finite stage of the balanced projection algebra is invariant under `complementEquiv`. -/
@[simp]
theorem complementEquiv_mem_stage_iff {n : ℕ} {x : BalancedProjectionAlgebra R τ} :
    complementEquiv τ x ∈ stage R τ n ↔ x ∈ stage R τ n := by
  have hle : stage R τ n ≤ (stage R τ n).comap (complementEquiv τ).toAlgHom :=
    stage_le_iff.2 fun i hi ↦ by simpa using sub_mem (Subalgebra.one_mem _) (e_mem_stage hi)
  exact ⟨fun hx ↦ by simpa using hle hx, fun hx ↦ hle hx⟩

/-- The complement automorphism restricted to `stage R τ n`. -/
def stageComplementEquiv (n : ℕ) : stage R τ n ≃ₐ[R] stage R τ n where
  toFun x := ⟨complementEquiv τ x, (complementEquiv_mem_stage_iff τ).2 x.property⟩
  invFun x := ⟨complementEquiv τ x, (complementEquiv_mem_stage_iff τ).2 x.property⟩
  left_inv x := Subtype.ext (complementEquiv_complementEquiv τ x)
  right_inv x := Subtype.ext (complementEquiv_complementEquiv τ x)
  map_mul' x y := Subtype.ext (map_mul (complementEquiv τ) (x : BalancedProjectionAlgebra R τ) y)
  map_add' x y := Subtype.ext (map_add (complementEquiv τ) (x : BalancedProjectionAlgebra R τ) y)
  commutes' r := Subtype.ext ((complementEquiv τ).commutes r)

@[simp]
theorem coe_stageComplementEquiv (n : ℕ) (x : stage R τ n) :
    (stageComplementEquiv (R := R) τ n x : BalancedProjectionAlgebra R τ) =
      complementEquiv τ x := (rfl)

@[simp]
theorem stageComplementEquiv_symm (n : ℕ) :
    (stageComplementEquiv (R := R) τ n).symm = stageComplementEquiv τ n := (rfl)

variable {τ}

/-- Precomposing a scalar character `e i ↦ c` with `complementEquiv` yields the complementary
scalar character `e i ↦ 1 - c`. -/
@[simp]
theorem character_complementEquiv (c : R) (hc : IsIdempotentElem c)
    (x : BalancedProjectionAlgebra R τ) :
    character c hc (complementEquiv τ x) = character (1 - c) hc.one_sub x :=
  DFunLike.congr_fun
    (hom_ext (F := (character (τ := τ) c hc).comp (complementEquiv τ).toAlgHom)
      (G := character (1 - c) hc.one_sub) fun i ↦ by simp) x

end Complement

section HeckeComparison

open InfiniteTypeAHeckeAlgebra (T)

variable {τ : R} {q : Rˣ}

/-- Under `heckeEquiv`, the projection complement `e i ↦ 1 - e i` corresponds to the Hecke
complement automorphism `T i ↦ -T i⁻¹ = (q - q⁻¹) - T i`. -/
theorem heckeEquiv_complementEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (complementEquiv τ x) =
      InfiniteTypeAHeckeAlgebra.complementEquiv q (heckeEquiv q hτ x) :=
  DFunLike.congr_fun
    (hom_ext (F := (heckeEquiv q hτ).toAlgHom.comp (complementEquiv τ).toAlgHom)
      (G := (InfiniteTypeAHeckeAlgebra.complementEquiv q).toAlgHom.comp (heckeEquiv q hτ).toAlgHom)
      fun i ↦ by
        simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, complementEquiv_e, map_sub,
          map_one, heckeEquiv_e, ← val_inv_addInvUnit hτ] using
          (InfiniteTypeAHeckeAlgebra.complementEquiv_eigenprojection q (addInvUnit hτ)
            (val_addInvUnit hτ) i).symm) x

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
    linear_combination -(τ * ((q : R) + ↑q⁻¹)) * q.mul_inv + (q : R) * hτ
  rw [heckeEquiv_one_sub_e hτ, smul_smul, hcoeff, smul_sub, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, smul_smul, ← sq]

end HeckeComparison

end TauCeti.BalancedProjectionAlgebra
