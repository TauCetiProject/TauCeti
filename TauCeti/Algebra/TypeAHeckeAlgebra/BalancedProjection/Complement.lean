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

For idempotents `p` and `q` in an `S`-module algebra `A`, replacing `p` and `q` by `1 - p` and
`1 - q` negates the balanced defect `(p * q * p - t • p) - (q * p * q - t • q)`. Consequently,
sending each generator `e i` to `1 - e i` defines an involutive `R`-algebra automorphism
`TauCeti.BalancedProjectionAlgebra.complementEquiv` of `BalancedProjectionAlgebra R τ` at the same
parameter `τ`.

This automorphism preserves every finite stage, exchanges scalar characters `c ↔ 1 - c` (in
particular `0 ↔ 1`), and intertwines `TauCeti.InfiniteTypeAHeckeAlgebra.complementEquiv` under
`heckeEquiv`: the image of `1 - e i` in the Hecke algebra is Wenzl's eigenprojection
`(q + q⁻¹)⁻¹ • (q - T i) = (1 + q²)⁻¹ • (q² - q • T i)` for the eigenvalue `-q⁻¹`. Under
`heckeEquiv`, the projection scalar characters `e i ↦ 1` and `e i ↦ 0` correspond to the Hecke
scalar characters `indexCharacter` (`T i ↦ q`) and `signCharacter` (`T i ↦ -q⁻¹`).

We also package the Markov trace condition `μ (w * e n) = η * μ w` (`w ∈ stage R τ (n + 1)`) as
`TauCeti.BalancedProjectionAlgebra.IsMarkovTrace`. Precomposing with `complementEquiv` sends a
Markov parameter `η` to `1 - η`, and when `τ * (q + q⁻¹) ^ 2 = 1`, projection Markov traces of
parameter `η` correspond bijectively to Hecke Markov traces of parameter
`z = q * η - q⁻¹ * (1 - η)`.

## Main definitions

* `TauCeti.BalancedProjectionAlgebra.complementEquiv`: the involutive automorphism `e i ↦ 1 - e i`.
* `TauCeti.BalancedProjectionAlgebra.stageComplementEquiv`: its restriction to `stage R τ n`.
* `TauCeti.BalancedProjectionAlgebra.IsMarkovTrace`: normalized tracial functionals satisfying
  `μ (w * e n) = η * μ w` on `stage R τ (n + 1)`.

## Main results

* `IsIdempotentElem.one_sub_mul_mul_sub_smul_sub`,
  `IsIdempotentElem.one_sub_mul_mul_sub_smul_eq`: complementing idempotents negates and preserves
  the balanced defect.
* `TauCeti.BalancedProjectionAlgebra.heckeEquiv_complementEquiv`,
  `TauCeti.BalancedProjectionAlgebra.heckeEquiv_one_sub_e`,
  `TauCeti.BalancedProjectionAlgebra.one_add_sq_smul_heckeEquiv_one_sub_e`: compatibility with the
  Hecke complement automorphism and Wenzl's eigenprojection `(Q - g i) / (1 + Q)`.
* `TauCeti.BalancedProjectionAlgebra.indexCharacter_heckeEquiv`,
  `TauCeti.BalancedProjectionAlgebra.signCharacter_heckeEquiv`: comparison of the endpoint scalar
  characters `e i ↦ 1, 0` with `T i ↦ q, -q⁻¹`.
* `TauCeti.BalancedProjectionAlgebra.isMarkovTrace_comp_complementEquiv_iff`,
  `TauCeti.BalancedProjectionAlgebra.isMarkovTrace_comp_heckeEquiv_iff`,
  `TauCeti.BalancedProjectionAlgebra.IsMarkovTrace.unique_of_hecke`: complement symmetry, Hecke
  transport, and uniqueness of projection Markov traces when `τ * (q + q⁻¹) ^ 2 = 1`.

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
  have hmul :
      (1 - p) * (1 - q) * (1 - p) - (1 - q) * (1 - p) * (1 - q) = q * p * q - p * q * p := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc, hp.eq, hq.eq]
    abel
  calc ((1 - p) * (1 - q) * (1 - p) - t • (1 - p)) -
          ((1 - q) * (1 - p) * (1 - q) - t • (1 - q))
      = ((1 - p) * (1 - q) * (1 - p) - (1 - q) * (1 - p) * (1 - q)) +
          (t • (1 - q) - t • (1 - p)) := by abel
    _ = (q * p * q - p * q * p) + (t • p - t • q) := by
          rw [hmul, ← smul_sub, sub_sub_sub_cancel_left, smul_sub]
    _ = -((p * q * p - t • p) - (q * p * q - t • q)) := by abel

/-- If idempotents `p` and `q` satisfy the balanced relation with parameter `t`, so do `1 - p` and
`1 - q`. -/
theorem one_sub_mul_mul_sub_smul_eq (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : p * q * p - t • p = q * p * q - t • q) :
    (1 - p) * (1 - q) * (1 - p) - t • (1 - p) = (1 - q) * (1 - p) * (1 - q) - t • (1 - q) :=
  sub_eq_zero.mp <| by
    rw [hp.one_sub_mul_mul_sub_smul_sub hq, sub_eq_zero.mpr h, neg_zero]

end IsIdempotentElem

namespace TauCeti.BalancedProjectionAlgebra

variable {R : Type*} [CommRing R]

section Complement

variable (τ : R)

private def complementHom : BalancedProjectionAlgebra R τ →ₐ[R] BalancedProjectionAlgebra R τ :=
  lift (fun i ↦ 1 - e τ i)
    (fun i ↦ (isIdempotentElem_e i).one_sub)
    (fun i ↦ (isIdempotentElem_e i).one_sub_mul_mul_sub_smul_eq
      (isIdempotentElem_e (i + 1)) (e_balanced i))
    (fun h ↦ by simp [sub_mul, mul_sub, (commute_e (Or.inl h)).eq]; abel)

private theorem complementHom_e (i : ℕ) :
    complementHom (R := R) τ (e τ i) = 1 - e τ i :=
  lift_e _ _ _ _ i

private theorem complementHom_comp_self :
    (complementHom (R := R) τ).comp (complementHom τ) = AlgHom.id R _ :=
  hom_ext fun i ↦ by simp [complementHom_e]

/-- The involutive complement automorphism of the balanced projection algebra, sending each
generator `e i` to `1 - e i` at the same parameter `τ`. -/
def complementEquiv : BalancedProjectionAlgebra R τ ≃ₐ[R] BalancedProjectionAlgebra R τ :=
  AlgEquiv.ofAlgHom (complementHom τ) (complementHom τ)
    (complementHom_comp_self τ) (complementHom_comp_self τ)

@[simp]
theorem complementEquiv_e (i : ℕ) :
    complementEquiv (R := R) τ (e τ i) = 1 - e τ i :=
  complementHom_e τ i

@[simp]
theorem complementEquiv_symm :
    (complementEquiv (R := R) τ).symm = complementEquiv τ :=
  AlgEquiv.ofAlgHom_symm _ _ _ _

@[simp]
theorem complementEquiv_complementEquiv (x : BalancedProjectionAlgebra R τ) :
    complementEquiv τ (complementEquiv τ x) = x := by
  simpa only [complementEquiv_symm] using (complementEquiv (R := R) τ).symm_apply_apply x

/-- Every finite stage of the balanced projection algebra is invariant under `complementEquiv`. -/
@[simp]
theorem complementEquiv_mem_stage_iff {n : ℕ} {x : BalancedProjectionAlgebra R τ} :
    complementEquiv τ x ∈ stage R τ n ↔ x ∈ stage R τ n := by
  have h : ∀ y ∈ stage R τ n, complementEquiv τ y ∈ stage R τ n := by
    have hle : stage R τ n ≤ (stage R τ n).comap (complementEquiv τ).toAlgHom :=
      stage_le_iff.2 fun i hi ↦ by
        simpa using sub_mem (Subalgebra.one_mem _) (e_mem_stage hi)
    exact fun y hy ↦ hle hy
  exact ⟨fun hx ↦ by simpa using h _ hx, h x⟩

/-- The complement automorphism restricted to `stage R τ n`. -/
def stageComplementEquiv (n : ℕ) : stage R τ n ≃ₐ[R] stage R τ n where
  toFun x := ⟨complementEquiv τ x, (complementEquiv_mem_stage_iff τ).2 x.2⟩
  invFun x := ⟨complementEquiv τ x, (complementEquiv_mem_stage_iff τ).2 x.2⟩
  left_inv x := Subtype.ext (complementEquiv_complementEquiv τ x)
  right_inv x := Subtype.ext (complementEquiv_complementEquiv τ x)
  map_mul' x y := Subtype.ext (map_mul (complementEquiv τ) (x : BalancedProjectionAlgebra R τ) y)
  map_add' x y := Subtype.ext (map_add (complementEquiv τ) (x : BalancedProjectionAlgebra R τ) y)
  commutes' r := Subtype.ext ((complementEquiv τ).commutes r)

@[simp]
theorem coe_stageComplementEquiv (n : ℕ) (x : stage R τ n) :
    (stageComplementEquiv (R := R) τ n x : BalancedProjectionAlgebra R τ) =
      complementEquiv τ x :=
  (rfl)

@[simp]
theorem stageComplementEquiv_symm (n : ℕ) :
    (stageComplementEquiv (R := R) τ n).symm = stageComplementEquiv τ n :=
  (rfl)

variable {τ}

/-- Precomposing a scalar character `e i ↦ c` with `complementEquiv` yields the complementary
scalar character `e i ↦ 1 - c`. -/
@[simp]
theorem character_complementEquiv (c : R) (hc : IsIdempotentElem c)
    (x : BalancedProjectionAlgebra R τ) :
    character c hc (complementEquiv τ x) = character (1 - c) hc.one_sub x := by
  have h : (character (τ := τ) c hc).comp (complementEquiv τ).toAlgHom =
      character (1 - c) hc.one_sub :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h x

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
  have hs : (s : R) = (q : R) + ↑q⁻¹ := rfl
  have hsinv : (↑s⁻¹ : R) = τ * ((q : R) + ↑q⁻¹) := rfl
  have h : (heckeEquiv q hτ).toAlgHom.comp (complementEquiv τ).toAlgHom =
      (InfiniteTypeAHeckeAlgebra.complementEquiv q).toAlgHom.comp (heckeEquiv q hτ).toAlgHom :=
    hom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, complementEquiv_e, map_sub, map_one,
        heckeEquiv_e, ← hsinv]
      exact (InfiniteTypeAHeckeAlgebra.complementEquiv_eigenprojection q s hs i).symm
  exact DFunLike.congr_fun h x

/-- The complementary projection `1 - e i` maps under `heckeEquiv` to the `-q⁻¹`-eigenprojection
`(q + q⁻¹)⁻¹ • (q - T i)`. -/
theorem heckeEquiv_one_sub_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    heckeEquiv q hτ (1 - e τ i) =
      (τ * ((q : R) + ↑q⁻¹)) • (algebraMap R _ (q : R) - T q i) := by
  have h : τ * ((q : R) + ↑q⁻¹) * ((q : R) + ↑q⁻¹) = 1 := by linear_combination hτ
  rw [map_sub, map_one, heckeEquiv_e]
  simp only [Algebra.algebraMap_eq_smul_one]
  match_scalars
  · linear_combination -h
  · ring

/-- In Wenzl's generators `g i = q • T i` with `Q = q ^ 2`, the complementary projection `1 - e i`
satisfies `(1 + Q) • e_i^W = Q - g i`. -/
theorem one_add_sq_smul_heckeEquiv_one_sub_e (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) (i : ℕ) :
    ((1 : R) + (q : R) ^ 2) • heckeEquiv q hτ (1 - e τ i) =
      algebraMap R _ ((q : R) ^ 2) - (q : R) • T q i := by
  have hq : (q : R) * ↑q⁻¹ = 1 := q.mul_inv
  have hcoeff : ((1 : R) + (q : R) ^ 2) * (τ * ((q : R) + ↑q⁻¹)) = q := by
    linear_combination -(τ * ((q : R) + ↑q⁻¹)) * hq + (q : R) * hτ
  rw [heckeEquiv_one_sub_e hτ, smul_smul, hcoeff, smul_sub, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, smul_smul, ← sq]

/-- Under `heckeEquiv`, the Hecke index character `T i ↦ q` pulls back to the projection character
`e i ↦ 1`. -/
@[simp]
theorem indexCharacter_heckeEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    indexCharacter R q (heckeEquiv q hτ x) = character 1 .one x := by
  have h : (indexCharacter R q).comp (heckeEquiv q hτ).toAlgHom = character 1 .one :=
    hom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, heckeEquiv_e, map_smul, map_add,
        indexCharacter_T, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul,
        character_e]
      linear_combination hτ
  exact DFunLike.congr_fun h x

/-- Under `heckeEquiv`, the Hecke sign character `T i ↦ -q⁻¹` pulls back to the projection
character `e i ↦ 0`. -/
@[simp]
theorem signCharacter_heckeEquiv (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    (x : BalancedProjectionAlgebra R τ) :
    signCharacter R q (heckeEquiv q hτ x) = character 0 .zero x := by
  have h : (signCharacter R q).comp (heckeEquiv q hτ).toAlgHom = character 0 .zero :=
    hom_ext fun i ↦ by simp
  exact DFunLike.congr_fun h x

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
normalized tracial `R`-linear functional satisfying `μ (w * e n) = η * μ w` whenever `w` belongs to
`stage R τ (n + 1)`. -/
structure IsMarkovTrace (η : R) (μ : BalancedProjectionAlgebra R τ →ₗ[R] R) : Prop where
  /-- A Markov trace is normalized at `1`. -/
  map_one : μ 1 = 1
  /-- A Markov trace is tracial. -/
  map_mul_comm (x y : BalancedProjectionAlgebra R τ) : μ (x * y) = μ (y * x)
  /-- Appending the projection `e n` to an element of `stage R τ (n + 1)` multiplies the trace by
  `η`. -/
  map_mul_e {n : ℕ} {w : BalancedProjectionAlgebra R τ} (hw : w ∈ stage R τ (n + 1)) :
    μ (w * e τ n) = η * μ w

namespace IsMarkovTrace

variable {η : R} {μ : BalancedProjectionAlgebra R τ →ₗ[R] R}

/-- A Markov trace recovers scalars along `algebraMap`. -/
theorem map_algebraMap (hμ : IsMarkovTrace η μ) (r : R) :
    μ (algebraMap R _ r) = r := by
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
  map_mul_comm x y := by
    simp only [AlgHom.toLinearMap_apply, map_mul, mul_comm]
  map_mul_e _ := by
    simp [mul_comm]

@[simp]
theorem isMarkovTrace_comp_complementEquiv_iff {η : R}
    {μ : BalancedProjectionAlgebra R τ →ₗ[R] R} :
    IsMarkovTrace (1 - η) (μ.comp (complementEquiv τ).toLinearMap) ↔ IsMarkovTrace η μ := by
  refine ⟨fun h ↦ ?_, IsMarkovTrace.comp_complementEquiv⟩
  have h' := h.comp_complementEquiv
  have hc : (μ.comp (complementEquiv τ).toLinearMap).comp (complementEquiv τ).toLinearMap = μ := by
    ext x
    simp
  simpa only [hc, sub_sub_cancel] using h'

/-- Transporting along `heckeEquiv` identifies Hecke Markov traces of parameter
`z = q * η - q⁻¹ * (1 - η)` with projection Markov traces of parameter `η`. -/
theorem isMarkovTrace_comp_heckeEquiv_iff {q : Rˣ} (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1)
    {z η : R} (hz : z = (q : R) * η - ↑q⁻¹ * (1 - η))
    {μ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} :
    IsMarkovTrace η (μ.comp (heckeEquiv q hτ).toLinearMap) ↔
      InfiniteTypeAHeckeAlgebra.IsMarkovTrace z μ := by
  constructor
  · intro hμ
    refine
      { map_one := by simpa using hμ.map_one
        map_mul_comm := fun x y ↦ by
          simpa using hμ.map_mul_comm ((heckeEquiv q hτ).symm x) ((heckeEquiv q hτ).symm y)
        map_mul_T := fun {n x} hx ↦ ?_ }
    have hw : (heckeEquiv q hτ).symm x ∈ stage R τ (n + 1) := by
      simpa [← heckeEquiv_mem_stage_iff hτ] using hx
    have hmul := hμ.map_mul_e hw
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      AlgEquiv.apply_symm_apply] at hmul
    have hT : T q n = ((q : R) + ↑q⁻¹) • heckeEquiv q hτ (e τ n) - algebraMap R _ ↑q⁻¹ := by
      simpa only [map_sub, map_smul, AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using
        congr_arg (heckeEquiv q hτ) (heckeEquiv_symm_T hτ n)
    rw [hT, mul_sub, mul_smul_comm, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
      map_sub, map_smul, map_smul, hmul, smul_eq_mul, smul_eq_mul, hz]
    ring
  · intro hμ
    refine
      { map_one := by simpa using hμ.map_one
        map_mul_comm := fun x y ↦ by
          simpa using hμ.map_mul_comm (heckeEquiv q hτ x) (heckeEquiv q hτ y)
        map_mul_e := fun hw ↦ ?_ }
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    rw [hμ.map_heckeEquiv_mul_e hτ hw, hz]
    linear_combination η * μ (heckeEquiv q hτ _) * hτ

/-- When `τ * (q + q⁻¹) ^ 2 = 1`, there is at most one Markov trace on
`BalancedProjectionAlgebra R τ` with a given projection parameter `η`. -/
theorem IsMarkovTrace.unique_of_hecke {q : Rˣ} (hτ : τ * ((q : R) + ↑q⁻¹) ^ 2 = 1) {η : R}
    {μ μ' : BalancedProjectionAlgebra R τ →ₗ[R] R}
    (hμ : IsMarkovTrace η μ) (hμ' : IsMarkovTrace η μ') : μ = μ' := by
  have heq : μ.comp (heckeEquiv q hτ).symm.toLinearMap =
      μ'.comp (heckeEquiv q hτ).symm.toLinearMap := by
    refine InfiniteTypeAHeckeAlgebra.IsMarkovTrace.unique
      (z := (q : R) * η - ↑q⁻¹ * (1 - η)) ?_ ?_
    · refine (isMarkovTrace_comp_heckeEquiv_iff hτ rfl).mp ?_
      convert hμ
      ext x
      simp
    · refine (isMarkovTrace_comp_heckeEquiv_iff hτ rfl).mp ?_
      convert hμ'
      ext x
      simp
  ext x
  simpa using LinearMap.congr_fun heq (heckeEquiv q hτ x)

end MarkovTrace

end TauCeti.BalancedProjectionAlgebra
