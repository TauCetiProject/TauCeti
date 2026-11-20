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
# The complement automorphism and Markov traces on the balanced projection algebra

For idempotents `p` and `q`, replacing `p` and `q` by `1 - p` and `1 - q` negates the balanced
defect `(p * q * p - t • p) - (q * p * q - t • q)`. Sending `e i` to `1 - e i` therefore defines an
involutive `R`-algebra automorphism `TauCeti.BalancedProjectionAlgebra.complementEquiv` at the same
parameter `τ`. It preserves every finite stage, exchanges scalar characters `c ↔ 1 - c`, and
intertwines `TauCeti.InfiniteTypeAHeckeAlgebra.complementEquiv` under `heckeEquiv`, mapping
`1 - e i` to Wenzl's eigenprojection `(q + q⁻¹)⁻¹ • (q - T i)` and the endpoint characters
`e i ↦ 1, 0` to `indexCharacter` and `signCharacter`.

We also package the Markov trace condition `μ (w * e n) = η * μ w` (`w ∈ stage R τ (n + 1)`) as
`TauCeti.BalancedProjectionAlgebra.IsMarkovTrace`. Precomposing with `complementEquiv` sends `η` to
`1 - η`, and when `τ * (q + q⁻¹) ^ 2 = 1`, projection Markov traces of parameter `η` correspond
bijectively to Hecke Markov traces of parameter `z = q * η - q⁻¹ * (1 - η)`.

## Main definitions and results

* `IsIdempotentElem.one_sub_mul_mul_sub_smul_sub`, `IsIdempotentElem.one_sub_mul_mul_sub_smul_eq`:
  complementing idempotents negates and preserves the balanced defect.
* `TauCeti.BalancedProjectionAlgebra.complementEquiv`, `stageComplementEquiv`: the involutive
  complement automorphism `e i ↦ 1 - e i` and its restriction to finite stages.
* `TauCeti.BalancedProjectionAlgebra.heckeEquiv_complementEquiv`, `heckeEquiv_one_sub_e`,
  `one_add_sq_smul_heckeEquiv_one_sub_e`, `indexCharacter_heckeEquiv`, `signCharacter_heckeEquiv`:
  Hecke compatibility of `complementEquiv`, Wenzl's eigenprojection, and the endpoint characters.
* `TauCeti.BalancedProjectionAlgebra.IsMarkovTrace`, `isMarkovTrace_comp_complementEquiv_iff`,
  `isMarkovTrace_comp_heckeEquiv_iff`, `IsMarkovTrace.unique_of_hecke`: projection Markov traces,
  complement symmetry, Hecke transport, and uniqueness when `τ * (q + q⁻¹) ^ 2 = 1`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11.
-/

public section

namespace IsIdempotentElem

variable {S A : Type*} [Ring S] [Ring A] [Module S A] {t : S} {p q : A}

/-- Replacing idempotents `p` and `q` by `1 - p` and `1 - q` negates their balanced defect. -/
theorem one_sub_mul_mul_sub_smul_sub (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    ((1 - p) * (1 - q) * (1 - p) - t • (1 - p)) -
        ((1 - q) * (1 - p) * (1 - q) - t • (1 - q)) =
      -((p * q * p - t • p) - (q * p * q - t • q)) := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hp.eq, hq.eq, smul_sub]
  abel

/-- If idempotents `p` and `q` satisfy the balanced relation with parameter `t`, so do `1 - p` and
`1 - q`. -/
theorem one_sub_mul_mul_sub_smul_eq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : p * q * p - t • p = q * p * q - t • q) :
    (1 - p) * (1 - q) * (1 - p) - t • (1 - p) = (1 - q) * (1 - p) * (1 - q) - t • (1 - q) :=
  sub_eq_zero.mp <| by rw [hp.one_sub_mul_mul_sub_smul_sub hq, sub_eq_zero.mpr h, neg_zero]

end IsIdempotentElem

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

open InfiniteTypeAHeckeAlgebra (T indexCharacter indexCharacter_T signCharacter)

variable {τ : R} {q : Rˣ}

/-- Under `heckeEquiv`, the projection complement `e i ↦ 1 - e i` corresponds to the Hecke
complement automorphism `T i ↦ -T i⁻¹ = (q - q⁻¹) - T i`. -/
theorem heckeEquiv_complementEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    heckeEquiv q hτ (complementEquiv τ x) =
      InfiniteTypeAHeckeAlgebra.complementEquiv q (heckeEquiv q hτ x) := by
  let s : Rˣ := Units.mkOfMulEqOne ((q : R) + ↑q⁻¹) (τ * ((q : R) + ↑q⁻¹))
    (by linear_combination hτ)
  have hsinv : (↑s⁻¹ : R) = τ * ((q : R) + ↑q⁻¹) := rfl
  exact DFunLike.congr_fun
    (hom_ext (F := (heckeEquiv q hτ).toAlgHom.comp (complementEquiv τ).toAlgHom)
      (G := (InfiniteTypeAHeckeAlgebra.complementEquiv q).toAlgHom.comp (heckeEquiv q hτ).toAlgHom)
      fun i ↦ by
        simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, complementEquiv_e, map_sub,
          map_one, heckeEquiv_e, ← hsinv] using
          (InfiniteTypeAHeckeAlgebra.complementEquiv_eigenprojection q s rfl i).symm) x

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

/-- Under `heckeEquiv`, the Hecke index character `T i ↦ q` pulls back to `e i ↦ 1`. -/
@[simp]
theorem indexCharacter_heckeEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    indexCharacter R q (heckeEquiv q hτ x) = character 1 .one x :=
  DFunLike.congr_fun
    (hom_ext (F := (indexCharacter R q).comp (heckeEquiv q hτ).toAlgHom) (G := character 1 .one)
      fun i ↦ by
        simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, heckeEquiv_e, map_smul, map_add,
          indexCharacter_T, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
          smul_eq_mul, character_e]
        linear_combination hτ) x

/-- Under `heckeEquiv`, the Hecke sign character `T i ↦ -q⁻¹` pulls back to `e i ↦ 0`. -/
@[simp]
theorem signCharacter_heckeEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    signCharacter R q (heckeEquiv q hτ x) = character 0 .zero x :=
  DFunLike.congr_fun
    (hom_ext (F := (signCharacter R q).comp (heckeEquiv q hτ).toAlgHom) (G := character 0 .zero)
      fun i ↦ by simp) x

@[simp]
theorem character_one_heckeEquiv_symm (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    character 1 .one ((heckeEquiv q hτ).symm x) = indexCharacter R q x := by
  simpa using (indexCharacter_heckeEquiv hτ ((heckeEquiv q hτ).symm x)).symm

@[simp]
theorem character_zero_heckeEquiv_symm (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : InfiniteTypeAHeckeAlgebra R q) :
    character 0 .zero ((heckeEquiv q hτ).symm x) = signCharacter R q x := by
  simpa using (signCharacter_heckeEquiv hτ ((heckeEquiv q hτ).symm x)).symm

end HeckeComparison

section MarkovTrace

open InfiniteTypeAHeckeAlgebra (T)

variable {τ : R}

/-- A Markov trace with projection parameter `η : R` on `BalancedProjectionAlgebra R τ`: a
normalized tracial `R`-linear functional satisfying `μ (w * e n) = η * μ w` on
`stage R τ (n + 1)`. -/
structure IsMarkovTrace (η : R) (μ : BalancedProjectionAlgebra R τ →ₗ[R] R) : Prop where
  /-- A Markov trace is normalized at `1`. -/
  map_one : μ 1 = 1
  /-- A Markov trace is tracial. -/
  map_mul_comm (x y : BalancedProjectionAlgebra R τ) : μ (x * y) = μ (y * x)
  /-- Appending `e n` to an element of `stage R τ (n + 1)` multiplies the trace by `η`. -/
  map_mul_e {n : ℕ} {w : BalancedProjectionAlgebra R τ} (hw : w ∈ stage R τ (n + 1)) :
    μ (w * e τ n) = η * μ w

namespace IsMarkovTrace

variable {η : R} {μ : BalancedProjectionAlgebra R τ →ₗ[R] R}

/-- A Markov trace recovers scalars along `algebraMap`. -/
theorem map_algebraMap (hμ : IsMarkovTrace η μ) (r : R) : μ (algebraMap R _ r) = r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hμ.map_one, smul_eq_mul, mul_one]

/-- Every generator has trace equal to the projection parameter `η`. -/
theorem map_e (hμ : IsMarkovTrace η μ) (i : ℕ) : μ (e τ i) = η := by
  simpa [hμ.map_one] using hμ.map_mul_e (n := i) (Subalgebra.one_mem _)

/-- Precomposing a Markov trace of parameter `η` with `complementEquiv` produces a Markov trace of
parameter `1 - η`. -/
theorem comp_complementEquiv (hμ : IsMarkovTrace η μ) :
    IsMarkovTrace (1 - η) (μ.comp (complementEquiv τ).toLinearMap) where
  map_one := by simpa using hμ.map_one
  map_mul_comm x y := by simpa using hμ.map_mul_comm (complementEquiv τ x) (complementEquiv τ y)
  map_mul_e hw := by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, complementEquiv_e,
      mul_sub, mul_one, map_sub]
    rw [hμ.map_mul_e ((complementEquiv_mem_stage_iff τ).2 hw)]
    ring

end IsMarkovTrace

/-- Each scalar character `e i ↦ c` is a Markov trace with projection parameter `c`. -/
theorem isMarkovTrace_character (c : R) (hc : IsIdempotentElem c) :
    IsMarkovTrace c (character (τ := τ) c hc).toLinearMap where
  map_one := map_one (character (τ := τ) c hc)
  map_mul_comm x y := by simp [mul_comm]
  map_mul_e _ := by simp [mul_comm]

@[simp]
theorem isMarkovTrace_comp_complementEquiv_iff {η : R}
    {μ : BalancedProjectionAlgebra R τ →ₗ[R] R} :
    IsMarkovTrace (1 - η) (μ.comp (complementEquiv τ).toLinearMap) ↔ IsMarkovTrace η μ :=
  ⟨fun h ↦ by
    have hc :
        (μ.comp (complementEquiv τ).toLinearMap).comp (complementEquiv τ).toLinearMap = μ := by
      ext x; simp
    simpa only [hc, sub_sub_cancel] using h.comp_complementEquiv,
    IsMarkovTrace.comp_complementEquiv⟩

/-- Transporting along `heckeEquiv` identifies Hecke Markov traces of parameter
`z = q * η - q⁻¹ * (1 - η)` with projection Markov traces of parameter `η`. -/
theorem isMarkovTrace_comp_heckeEquiv_iff {q : Rˣ} (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    {z η : R} (hz : z = (q : R) * η - ↑q⁻¹ * (1 - η))
    {μ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} :
    IsMarkovTrace η (μ.comp (heckeEquiv q hτ).toLinearMap) ↔
      InfiniteTypeAHeckeAlgebra.IsMarkovTrace z μ := by
  constructor
  · intro hμ
    refine ⟨by simpa using hμ.map_one, fun x y ↦ by
        simpa using hμ.map_mul_comm ((heckeEquiv q hτ).symm x) ((heckeEquiv q hτ).symm y),
      fun {n x} hx ↦ ?_⟩
    have hmul := hμ.map_mul_e (show (heckeEquiv q hτ).symm x ∈ stage R τ (n + 1) by
      simpa [← heckeEquiv_mem_stage_iff hτ] using hx)
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      AlgEquiv.apply_symm_apply] at hmul
    have hT : T q n = ((q : R) + ↑q⁻¹) • heckeEquiv q hτ (e τ n) - algebraMap R _ ↑q⁻¹ := by
      simpa only [map_sub, map_smul, AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using
        congr_arg (heckeEquiv q hτ) (heckeEquiv_symm_T hτ n)
    rw [hT, mul_sub, mul_smul_comm, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
      map_sub, map_smul, map_smul, hmul, smul_eq_mul, smul_eq_mul, hz]
    ring
  · intro hμ
    refine ⟨by simpa using hμ.map_one, fun x y ↦ by
        simpa using hμ.map_mul_comm (heckeEquiv q hτ x) (heckeEquiv q hτ y),
      fun hw ↦ ?_⟩
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    rw [hμ.map_heckeEquiv_mul_e hτ hw, hz]
    linear_combination η * μ (heckeEquiv q hτ _) * hτ

/-- When `τ * (q + q⁻¹) ^ 2 = 1`, there is at most one Markov trace on
`BalancedProjectionAlgebra R τ` with a given projection parameter `η`. -/
theorem IsMarkovTrace.unique_of_hecke {q : Rˣ} (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) {η : R}
    {μ μ' : BalancedProjectionAlgebra R τ →ₗ[R] R}
    (hμ : IsMarkovTrace η μ) (hμ' : IsMarkovTrace η μ') : μ = μ' := by
  have toH {ν : BalancedProjectionAlgebra R τ →ₗ[R] R} (hν : IsMarkovTrace η ν) :
      InfiniteTypeAHeckeAlgebra.IsMarkovTrace ((q : R) * η - ↑q⁻¹ * (1 - η))
        (ν.comp (heckeEquiv q hτ).symm.toLinearMap) :=
    (isMarkovTrace_comp_heckeEquiv_iff hτ rfl).mp <| by convert hν; ext x; simp
  have heq := InfiniteTypeAHeckeAlgebra.IsMarkovTrace.unique (toH hμ) (toH hμ')
  exact LinearMap.ext fun x ↦ by simpa using LinearMap.congr_fun heq (heckeEquiv q hτ x)

end MarkovTrace

end TauCeti.BalancedProjectionAlgebra
