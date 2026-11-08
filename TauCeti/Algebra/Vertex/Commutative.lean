/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.Rat

/-!
# The commutative vertex algebra of a differential algebra

Let `V` be a commutative `R`-algebra over `ℚ` with an `R`-linear derivation `D`. Then

`Y(a,z) b = (e^{zD} a) · b = ∑_{k ≥ 0} (Dᵏ a / k!) · b zᵏ`

makes `V` a formal vertex algebra with vacuum `1` and translation `D`
(`Derivation.formalVertexAxioms`). Its modes are `a₍₋ₖ₋₁₎ = (Dᵏ a / k!) ·` and `a₍ₙ₎ = 0` for
`n ≥ 0`; the product of `V` is recovered as `a₍₋₁₎ b = a b`. All modes commute, so any two fields
are local of order `0`. For example, `ℚ[x]` with `D = d/dx` (`Polynomial.derivative'`) is a
formal vertex algebra.

In the terminology of Kac these are the holomorphic vertex algebras: every field `Y(a,z)` is a
power series in `z`.

## Main definitions

* `Derivation.formalVertexAxioms`: the formal vertex algebra of a differential algebra.

## Main results

* `Derivation.ncoeff_formalVertexAxioms_field_neg`: `a₍₋ₖ₋₁₎ = (Dᵏ a / k!) ·`.
* `Derivation.ncoeff_formalVertexAxioms_field_of_nonneg`: `a₍ₙ₎ = 0` for `n ≥ 0`.
* `Derivation.ncoeff_neg_one_formalVertexAxioms_field_apply`: `a₍₋₁₎ b = a b`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §1.4.
* R. Borcherds, *Vertex algebras, Kac-Moody algebras, and the Monster*, Proc. Natl. Acad. Sci.
  USA 83 (1986), §4.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.4.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator

namespace Derivation

variable {R V : Type*} [CommRing R] [CommRing V] [Algebra R V] [Algebra ℚ V]
variable (D : Derivation R V V)

/-- The coefficient `Dᵐ a / m!` of `zᵐ` in `e^{zD} a`, and `0` for `m < 0`. -/
private def expCoeff (a : V) (m : ℤ) : V :=
  if 0 ≤ m then (m.toNat.factorial : ℚ)⁻¹ • ((D : Module.End R V) ^ m.toNat) a else 0

private theorem expCoeff_add (a b : V) (m : ℤ) :
    D.expCoeff (a + b) m = D.expCoeff a m + D.expCoeff b m := by
  unfold expCoeff
  split_ifs <;> simp [smul_add]

private theorem expCoeff_smul (r : R) (a : V) (m : ℤ) :
    D.expCoeff (r • a) m = r • D.expCoeff a m := by
  unfold expCoeff
  split_ifs
  · rw [LinearMap.map_smul]
    exact smul_comm _ _ _
  · simp

private theorem expCoeff_of_neg (a : V) {m : ℤ} (hm : m < 0) : D.expCoeff a m = 0 := by
  simp [expCoeff, hm.not_ge]

/-- `D` commutes with taking the coefficients of `e^{zD} a`. -/
private theorem map_expCoeff (a : V) (m : ℤ) : D (D.expCoeff a m) = D.expCoeff (D a) m := by
  unfold expCoeff
  split_ifs
  · rw [map_rat_smul, ← coeFn_coe, ← mul_apply_eq_comp, ← mul_apply_eq_comp, pow_mul_comm']
  · exact D.map_zero

/-- `Dᵐ (D a) / m! = (m + 1) Dᵐ⁺¹ a / (m + 1)!`; both sides vanish for `m < 0`. -/
private theorem expCoeff_derivation (a : V) (m : ℤ) :
    D.expCoeff (D a) m = (m + 1) • D.expCoeff a (m + 1) := by
  rcases lt_or_ge m 0 with hm | hm
  · rcases (Int.add_one_le_iff.2 hm).eq_or_lt with hm' | hm'
    · simp [D.expCoeff_of_neg _ hm, hm']
    · rw [D.expCoeff_of_neg _ hm, D.expCoeff_of_neg _ hm', smul_zero]
  · lift m to ℕ using hm
    rw [← Int.cast_smul_eq_zsmul ℚ]
    simp only [expCoeff, ← Nat.cast_succ, Nat.cast_nonneg, ite_true, Int.toNat_natCast]
    rw [pow_succ, mul_apply_eq_comp, coeFn_coe, smul_smul, Nat.factorial_succ]
    congr 1
    push_cast
    field_simp

/-- The coefficients `Dᵏ a / k!` vanish on `1` for `k ≥ 1`, since `D 1 = 0`. -/
private theorem expCoeff_one (m : ℤ) : D.expCoeff 1 m = if m = 0 then 1 else 0 := by
  unfold expCoeff
  split_ifs with h₀ h₁ h₁
  · subst h₁
    simp
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m.toNat = k + 1 := ⟨m.toNat - 1, by omega⟩
    rw [hk, pow_succ, mul_apply_eq_comp, coeFn_coe, map_one_eq_zero, map_zero, smul_zero]
  · omega
  · rfl

/-- The field `Y(a,z) = (e^{zD} a) ·` as a vertex operator. -/
private def expField (a : V) : VertexOperator R V :=
  of_coeff (fun m ↦ LinearMap.mulLeft R (D.expCoeff a m)) fun _ ↦
    ⟨0, fun m hm ↦ not_lt.1 fun h ↦ hm (by simp [D.expCoeff_of_neg a h])⟩

private theorem ncoeff_expField (a : V) (n : ℤ) :
    (D.expField a)[[n]] = LinearMap.mulLeft R (D.expCoeff a (-n - 1)) :=
  ncoeff_of_coeff _ _ n

private theorem ncoeff_expField_neg (a : V) (k : ℕ) :
    (D.expField a)[[-k - 1]] = LinearMap.mulLeft R (D.expCoeff a k) := by
  rw [ncoeff_expField]
  congr 2
  ring

private theorem ncoeff_expField_of_nonneg (a : V) {n : ℤ} (hn : 0 ≤ n) :
    (D.expField a)[[n]] = 0 := by
  rw [ncoeff_expField, D.expCoeff_of_neg a (by omega), LinearMap.mulLeft_zero_eq_zero]

/-- The state-derivative identity `Y(D a, z) = ∂_z Y(a, z)`. -/
private theorem expField_derivation (a : V) : D.expField (D a) = derivative (D.expField a) := by
  refine ext_ncoeff fun n ↦ ?_
  have h₁ : -n - 1 + 1 = -n := by ring
  have h₂ : -(n - 1) - 1 = -n := by ring
  rw [ncoeff_expField, ncoeff_derivative, ncoeff_expField, D.expCoeff_derivation, h₁, h₂]
  ext v
  simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply, smul_mul_assoc]

/-- The commutative formal vertex algebra of a differential algebra: `V` with vacuum `1`,
translation `D` and fields `Y(a,z) b = (e^{zD} a) · b`. -/
def formalVertexAxioms : TauCeti.FormalVertexAxioms R V where
  field :=
    { toFun := D.expField
      map_add' a b := ext_ncoeff fun n ↦ by
        ext v
        simp [ncoeff_expField, expCoeff_add, add_mul]
      map_smul' r a := ext_ncoeff fun n ↦ by
        ext v
        simp [ncoeff_expField, expCoeff_smul] }
  vacuum := 1
  translation := D
  translation_vacuum := D.map_one_eq_zero
  ncoeff_field_vacuum n := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ncoeff_expField, expCoeff_one, sub_eq_zero,
      neg_eq_iff_eq_neg]
    split_ifs <;> simp
  ncoeff_field_apply_vacuum_of_nonneg a n hn := by
    simp [D.ncoeff_expField_of_nonneg a hn]
  ncoeff_neg_one_field_apply_vacuum a := by
    simp [ncoeff_expField, expCoeff]
  field_translation := D.expField_derivation
  lie_translation_ncoeff a n := by
    ext v
    simp [← expField_derivation, ncoeff_expField, Ring.lie_def, map_expCoeff, mul_comm]
  exists_isLocalOfOrder a b := ⟨0, isLocalOfOrder_iff.2 fun m n ↦ by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ncoeff_expField]
    simp [mul_left_comm]⟩

private theorem formalVertexAxioms_field (a : V) : D.formalVertexAxioms.field a = D.expField a :=
  (rfl)

/-- The vacuum of the commutative vertex algebra is `1`. -/
@[simp]
theorem formalVertexAxioms_vacuum : D.formalVertexAxioms.vacuum = 1 := (rfl)

/-- The translation operator of the commutative vertex algebra is the derivation `D`. -/
@[simp]
theorem formalVertexAxioms_translation : D.formalVertexAxioms.translation = D := (rfl)

/-- The negative modes are multiplications: `a₍₋ₖ₋₁₎ = (Dᵏ a / k!) ·`. -/
theorem ncoeff_formalVertexAxioms_field_neg (a : V) (k : ℕ) :
    (D.formalVertexAxioms.field a)[[-k - 1]] =
      LinearMap.mulLeft R ((k.factorial : ℚ)⁻¹ • ((D : Module.End R V) ^ k) a) := by
  rw [formalVertexAxioms_field, ncoeff_expField_neg]
  simp [expCoeff]

/-- All nonnegative modes vanish: the fields are power series in `z`. -/
@[simp]
theorem ncoeff_formalVertexAxioms_field_of_nonneg (a : V) {n : ℤ} (hn : 0 ≤ n) :
    (D.formalVertexAxioms.field a)[[n]] = 0 := by
  rw [formalVertexAxioms_field, D.ncoeff_expField_of_nonneg a hn]

/-- The product of `V` is the `(-1)`-product: `a₍₋₁₎ b = a b`. -/
@[simp]
theorem ncoeff_neg_one_formalVertexAxioms_field_apply (a b : V) :
    ((D.formalVertexAxioms.field a)[[-1]]) b = a * b := by
  simpa using LinearMap.congr_fun (D.ncoeff_formalVertexAxioms_field_neg a 0) b

end Derivation
