/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.DualNumber.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Iterated dual numbers `R[ε][ε]`

Applying the dual-number construction twice to a semiring `R` produces the algebra
`DualNumber (DualNumber R) = R[ε][ε]` generated over `R` by two commuting square-zero elements:
the inner generator `ε₁ = inl ε` and the outer generator `ε₂ = ε`, whose product is
`ε₁ ε₂ = inl ε * ε = ε • ε = inr ε`.

As an `R`-module, `R[ε][ε]` is free of rank four on the basis `{1, inl ε, ε, ε • ε}` indexed by
`Fin 2 × Fin 2` (`TauCeti.iteratedDualNumberBasis`), assembled as the tower product of
`TauCeti.dualNumberBasis R` and `TauCeti.dualNumberBasis R[ε]`. In particular, the `ε₁ ε₂`
coordinate `z.snd.snd` of `r • (inl ε * ε)` recovers `r` without zero-divisor or characteristic
hypotheses on `R`.

Over a commutative semiring `R`, `R`-algebra homomorphisms `R[ε][ε] →ₐ[R] A` into any `R`-algebra
`A` correspond bijectively via `TauCeti.iteratedDualNumberLift` to pairs `(e₁, e₂)` of commuting
square-zero elements of `A`, and swapping the two generators gives an `R`-algebra involution
`TauCeti.iteratedDualNumberSwap`. Evaluating `MvPolynomial (Fin 2) R` at `![inl ε, ε]` has kernel
`(X 0 ^ 2, X 1 ^ 2)` (`DualNumber.ker_aeval_inl_eps_eps`), yielding over a commutative ring `R`
the presentation `R[X₀, X₁] / (X₀², X₁²) ≃ₐ[R] R[ε][ε]`
(`TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv`).

## Main definitions

* `TauCeti.iteratedDualNumberBasis`: the `R`-module basis `{1, inl ε, ε, ε • ε}` of `R[ε][ε]`
  indexed by `Fin 2 × Fin 2`.
* `TauCeti.iteratedDualNumberLift`: universal property identifying `R[ε][ε] →ₐ[R] A` with pairs of
  commuting square-zero elements of `A`.
* `TauCeti.iteratedDualNumberSwap`: the `R`-algebra involution of `R[ε][ε]` exchanging `inl ε` and
  `ε`.
* `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv`: the `R`-algebra equivalence
  `MvPolynomial (Fin 2) R ⧸ Ideal.span {X 0 ^ 2, X 1 ^ 2} ≃ₐ[R] R[ε][ε]`.

## Main results

* `DualNumber.inl_eps_pow_two`, `DualNumber.inl_eps_mul_eps`: `(inl ε) ^ 2 = 0` and
  `inl ε * ε = ε • ε` in `R[ε][ε]`.
* `TauCeti.finrank_iteratedDualNumber`: `Module.finrank R R[ε][ε] = 4` under
  `StrongRankCondition R`.
* `TauCeti.iteratedDualNumber_algHom_ext`: `R`-algebra maps out of `R[ε][ε]` are determined by
  their values on `inl ε` and `ε`.
* `DualNumber.ker_aeval_inl_eps_eps`: the kernel of `MvPolynomial.aeval ![inl ε, ε]` is
  `Ideal.span {X 0 ^ 2, X 1 ^ 2}`.
-/

public section

open DualNumber TrivSqZeroExt

namespace DualNumber

section Semiring

variable {R : Type*} [Semiring R]

/-- The inner infinitesimal generator `inl ε` of `R[ε][ε]` squares to zero. -/
@[simp]
theorem inl_eps_mul_inl_eps :
    (inl (ε : R[ε]) * inl (ε : R[ε]) : R[ε][ε]) = 0 := by
  ext <;> simp

/-- The inner infinitesimal generator `inl ε` of `R[ε][ε]` satisfies `(inl ε) ^ 2 = 0`. -/
theorem inl_eps_pow_two : (inl (ε : R[ε]) : R[ε][ε]) ^ 2 = 0 := by
  simp

/-- The product of the inner generator `inl ε` and the outer generator `ε` of `R[ε][ε]` is
`ε • ε = inr ε`. -/
theorem inl_eps_mul_eps : (inl (ε : R[ε]) : R[ε][ε]) * ε = (ε : R[ε]) • ε := by
  ext <;> simp

/-- Reversed product of the outer generator `ε` and the inner generator `inl ε` of `R[ε][ε]`. -/
theorem eps_mul_inl_eps : (ε : R[ε][ε]) * inl (ε : R[ε]) = (ε : R[ε]) • ε := by
  rw [(commute_eps_left _).eq, inl_eps_mul_eps]

/-- The product `inl ε * ε` in `R[ε][ε]` squares to zero. -/
@[simp]
theorem inl_eps_mul_eps_pow_two : ((inl (ε : R[ε]) : R[ε][ε]) * ε) ^ 2 = 0 := by
  rw [inl_eps_mul_eps, ← inr_eq_smul_eps, sq, inr_mul_inr]

/-- Extracting the `ε₁ ε₂` coordinate of `r • (inl ε * ε)` recovers `r`. -/
theorem snd_snd_smul_inl_eps_mul_eps (r : R) :
    (r • ((inl (ε : R[ε]) : R[ε][ε]) * ε)).snd.snd = r := by
  simp

/-- Scalar multiplication on `inl ε * ε` in `R[ε][ε]` is injective over any semiring `R`. -/
theorem smul_inl_eps_mul_eps_injective :
    Function.Injective fun r : R ↦ r • ((inl (ε : R[ε]) : R[ε][ε]) * ε) := fun r₁ r₂ h ↦ by
  simpa using congrArg (fun z : R[ε][ε] ↦ z.snd.snd) h

/-- Over a nontrivial semiring, the top infinitesimal monomial `inl ε * ε` in `R[ε][ε]` is
nonzero. -/
theorem inl_eps_mul_eps_ne_zero [Nontrivial R] :
    (inl (ε : R[ε]) : R[ε][ε]) * ε ≠ 0 := fun h ↦
  one_ne_zero (α := R) (by simpa using congrArg (fun z : R[ε][ε] ↦ z.snd.snd) h)

end Semiring

end DualNumber

namespace TauCeti

section Basis

variable (R : Type*) [Semiring R]

/-- The `R`-module basis `{1, inl ε, ε, ε • ε}` of the iterated dual numbers `R[ε][ε]`, indexed
by `Fin 2 × Fin 2` via `(i, j) ↦ (inl ε) ^ i * ε ^ j`. -/
noncomputable def iteratedDualNumberBasis : Module.Basis (Fin 2 × Fin 2) R R[ε][ε] :=
  (dualNumberBasis R).smulTower (dualNumberBasis R[ε])

/-- Over a semiring satisfying the strong rank condition, the iterated dual numbers `R[ε][ε]`
have `R`-rank four. -/
@[simp]
theorem finrank_iteratedDualNumber [StrongRankCondition R] :
    Module.finrank R R[ε][ε] = 4 := by
  simp [Module.finrank_eq_card_basis (iteratedDualNumberBasis R)]

/-- The `(0, 0)` basis element of `TauCeti.iteratedDualNumberBasis` is `1`. -/
@[simp]
theorem iteratedDualNumberBasis_zero_zero : iteratedDualNumberBasis R (0, 0) = 1 := by
  simp [iteratedDualNumberBasis]

/-- The `(1, 0)` basis element of `TauCeti.iteratedDualNumberBasis` is `inl ε`. -/
@[simp]
theorem iteratedDualNumberBasis_one_zero :
    iteratedDualNumberBasis R (1, 0) = inl (ε : R[ε]) := by
  simp [iteratedDualNumberBasis, ← inl_mul_eq_smul]

/-- The `(0, 1)` basis element of `TauCeti.iteratedDualNumberBasis` is `ε`. -/
@[simp]
theorem iteratedDualNumberBasis_zero_one : iteratedDualNumberBasis R (0, 1) = ε := by
  simp [iteratedDualNumberBasis]

/-- The `(1, 1)` basis element of `TauCeti.iteratedDualNumberBasis` is `ε • ε = inl ε * ε`. -/
@[simp]
theorem iteratedDualNumberBasis_one_one :
    iteratedDualNumberBasis R (1, 1) = (ε : R[ε]) • (ε : R[ε][ε]) := by
  simp [iteratedDualNumberBasis]

variable {R}

/-- The `(0, 0)` coordinate of `z : R[ε][ε]` is `z.fst.fst`. -/
@[simp]
theorem _root_.DualNumber.iteratedDualNumberBasis_repr_zero_zero (z : R[ε][ε]) :
    (iteratedDualNumberBasis R).repr z (0, 0) = z.fst.fst := by
  simp [iteratedDualNumberBasis]

/-- The `(1, 0)` coordinate of `z : R[ε][ε]` (along `inl ε`) is `z.fst.snd`. -/
@[simp]
theorem _root_.DualNumber.iteratedDualNumberBasis_repr_one_zero (z : R[ε][ε]) :
    (iteratedDualNumberBasis R).repr z (1, 0) = z.fst.snd := by
  simp [iteratedDualNumberBasis]

/-- The `(0, 1)` coordinate of `z : R[ε][ε]` (along `ε`) is `z.snd.fst`. -/
@[simp]
theorem _root_.DualNumber.iteratedDualNumberBasis_repr_zero_one (z : R[ε][ε]) :
    (iteratedDualNumberBasis R).repr z (0, 1) = z.snd.fst := by
  simp [iteratedDualNumberBasis]

/-- The `(1, 1)` coordinate of `z : R[ε][ε]` (along `inl ε * ε`) is `z.snd.snd`. -/
@[simp]
theorem _root_.DualNumber.iteratedDualNumberBasis_repr_one_one (z : R[ε][ε]) :
    (iteratedDualNumberBasis R).repr z (1, 1) = z.snd.snd := by
  simp [iteratedDualNumberBasis]

/-- An `R`-linear map out of `R[ε][ε]` is determined by its values on `1`, `inl ε`, `ε`, and
`inl ε * ε`. -/
theorem iteratedDualNumber_linearMap_ext {M : Type*} [AddCommMonoid M] [Module R M]
    ⦃f g : R[ε][ε] →ₗ[R] M⦄ (h00 : f 1 = g 1) (h10 : f (inl ε) = g (inl ε))
    (h01 : f ε = g ε) (h11 : f (inl ε * ε) = g (inl ε * ε)) : f = g :=
  (iteratedDualNumberBasis R).ext fun ⟨i, j⟩ ↦ by
    fin_cases i <;> fin_cases j <;> simpa [← inl_eps_mul_eps]

end Basis

section UniversalProperty

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Two `R`-algebra homomorphisms out of `R[ε][ε]` are equal when they agree on `inl ε` and `ε`. -/
theorem iteratedDualNumber_algHom_ext ⦃f g : R[ε][ε] →ₐ[R] A⦄
    (h₁ : f (inl ε) = g (inl ε)) (h₂ : f ε = g ε) : f = g :=
  AlgHom.toLinearMap_injective <|
    iteratedDualNumber_linearMap_ext (by simp) (by simpa using h₁) (by simpa using h₂)
      (by simp [h₁, h₂])

/-- Universal property of the iterated dual numbers: `R`-algebra homomorphisms `R[ε][ε] →ₐ[R] A`
correspond bijectively to pairs `(e₁, e₂)` of commuting square-zero elements of `A`. -/
def iteratedDualNumberLift :
    {e : A × A // e.1 * e.1 = 0 ∧ e.2 * e.2 = 0 ∧ Commute e.1 e.2} ≃ (R[ε][ε] →ₐ[R] A) where
  toFun e :=
    let f₁ : R[ε] →ₐ[R] A :=
      DualNumber.lift ⟨(Algebra.ofId R A, e.val.1), e.prop.1,
        fun r ↦ Algebra.commute_algebraMap_right r e.val.1⟩
    DualNumber.lift ⟨(f₁, e.val.2), e.prop.2.1, fun x ↦ by
      rw [DualNumber.lift_apply_apply]
      dsimp only [Algebra.ofId_apply]
      exact (Algebra.commute_algebraMap_right x.fst e.val.2).add_right
        ((Algebra.commute_algebraMap_right x.snd e.val.2).mul_right e.prop.2.2.symm)⟩
  invFun F :=
    ⟨(F (inl ε), F ε),
      by rw [← map_mul, inl_eps_mul_inl_eps, map_zero],
      by rw [← map_mul, eps_mul_eps, map_zero],
      (commute_eps_right (inl ε)).map F⟩
  left_inv e := Subtype.ext <| Prod.ext (by simp) (by simp)
  right_inv F := iteratedDualNumber_algHom_ext (by simp) (by simp)

/-- `TauCeti.iteratedDualNumberLift` sends a dual number `z : R[ε][ε]` to the linear combination
of `1`, `e₁`, `e₂`, and `e₁ * e₂` with its four `R`-coordinates. -/
theorem iteratedDualNumberLift_apply
    (e : {e : A × A // e.1 * e.1 = 0 ∧ e.2 * e.2 = 0 ∧ Commute e.1 e.2}) (z : R[ε][ε]) :
    iteratedDualNumberLift e z =
      algebraMap R A z.fst.fst + algebraMap R A z.fst.snd * e.val.1 +
        (algebraMap R A z.snd.fst + algebraMap R A z.snd.snd * e.val.1) * e.val.2 := by
  simp [iteratedDualNumberLift, DualNumber.lift_apply_apply]

/-- `TauCeti.iteratedDualNumberLift` sends `inl ε` to the first chosen square-zero element. -/
@[simp]
theorem iteratedDualNumberLift_inl_eps
    (e : {e : A × A // e.1 * e.1 = 0 ∧ e.2 * e.2 = 0 ∧ Commute e.1 e.2}) :
    iteratedDualNumberLift e (inl (ε : R[ε])) = e.val.1 := by
  simp [iteratedDualNumberLift]

/-- `TauCeti.iteratedDualNumberLift` sends `ε` to the second chosen square-zero element. -/
@[simp]
theorem iteratedDualNumberLift_eps
    (e : {e : A × A // e.1 * e.1 = 0 ∧ e.2 * e.2 = 0 ∧ Commute e.1 e.2}) :
    iteratedDualNumberLift e (ε : R[ε][ε]) = e.val.2 := by
  simp [iteratedDualNumberLift]

/-- `TauCeti.iteratedDualNumberLift` sends `ε • ε = inl ε * ε` to `e₁ * e₂`. -/
@[simp]
theorem iteratedDualNumberLift_smul_eps
    (e : {e : A × A // e.1 * e.1 = 0 ∧ e.2 * e.2 = 0 ∧ Commute e.1 e.2}) :
    iteratedDualNumberLift e ((ε : R[ε]) • (ε : R[ε][ε])) = e.val.1 * e.val.2 := by
  rw [← inl_eps_mul_eps, map_mul, iteratedDualNumberLift_inl_eps, iteratedDualNumberLift_eps]

/-- The inverse of `TauCeti.iteratedDualNumberLift` evaluates an `R`-algebra map on `inl ε` and
`ε`. -/
@[simp]
theorem coe_iteratedDualNumberLift_symm_apply (F : R[ε][ε] →ₐ[R] A) :
    (iteratedDualNumberLift.symm F).val = (F (inl ε), F ε) :=
  (rfl)

end UniversalProperty

section Swap

variable (R : Type*) [CommSemiring R]

private def iteratedDualNumberSwapHom : R[ε][ε] →ₐ[R] R[ε][ε] :=
  iteratedDualNumberLift ⟨(ε, inl ε), eps_mul_eps, inl_eps_mul_inl_eps, commute_eps_left _⟩

private theorem iteratedDualNumberSwapHom_comp_self :
    (iteratedDualNumberSwapHom R).comp (iteratedDualNumberSwapHom R) = AlgHom.id R R[ε][ε] :=
  iteratedDualNumber_algHom_ext (by simp [iteratedDualNumberSwapHom])
    (by simp [iteratedDualNumberSwapHom])

/-- The `R`-algebra involution of `R[ε][ε]` exchanging the inner generator `inl ε` and the outer
generator `ε`. -/
def iteratedDualNumberSwap : R[ε][ε] ≃ₐ[R] R[ε][ε] :=
  AlgEquiv.ofAlgHom (iteratedDualNumberSwapHom R) (iteratedDualNumberSwapHom R)
    (iteratedDualNumberSwapHom_comp_self R) (iteratedDualNumberSwapHom_comp_self R)

variable {R}

@[simp]
theorem iteratedDualNumberSwap_inl_eps :
    iteratedDualNumberSwap R (inl (ε : R[ε])) = ε := by
  simp [iteratedDualNumberSwap, iteratedDualNumberSwapHom]

@[simp]
theorem iteratedDualNumberSwap_eps :
    iteratedDualNumberSwap R (ε : R[ε][ε]) = inl ε := by
  simp [iteratedDualNumberSwap, iteratedDualNumberSwapHom]

@[simp]
theorem iteratedDualNumberSwap_smul_eps :
    iteratedDualNumberSwap R ((ε : R[ε]) • (ε : R[ε][ε])) = (ε : R[ε]) • ε := by
  simp [iteratedDualNumberSwap, iteratedDualNumberSwapHom, eps_mul_inl_eps]

@[simp]
theorem iteratedDualNumberSwap_symm :
    (iteratedDualNumberSwap R).symm = iteratedDualNumberSwap R := by
  rw [iteratedDualNumberSwap, AlgEquiv.ofAlgHom_symm]

/-- Applying `TauCeti.iteratedDualNumberSwap` twice is the identity. -/
@[simp]
theorem _root_.DualNumber.iteratedDualNumberSwap_apply_apply (z : R[ε][ε]) :
    iteratedDualNumberSwap R (iteratedDualNumberSwap R z) = z := by
  simpa only [iteratedDualNumberSwap_symm] using (iteratedDualNumberSwap R).symm_apply_apply z

@[simp]
theorem _root_.DualNumber.fst_fst_iteratedDualNumberSwap (z : R[ε][ε]) :
    (iteratedDualNumberSwap R z).fst.fst = z.fst.fst := by
  simp [iteratedDualNumberSwap, iteratedDualNumberSwapHom, iteratedDualNumberLift_apply,
    algebraMap_eq_inl']

/-- `TauCeti.iteratedDualNumberSwap` exchanges the `inl ε` and `ε` coordinates of `z : R[ε][ε]`. -/
@[simp]
theorem _root_.DualNumber.snd_fst_iteratedDualNumberSwap (z : R[ε][ε]) :
    (iteratedDualNumberSwap R z).fst.snd = z.snd.fst := by
  simp [iteratedDualNumberSwap, iteratedDualNumberSwapHom, iteratedDualNumberLift_apply,
    algebraMap_eq_inl']

@[simp]
theorem _root_.DualNumber.fst_snd_iteratedDualNumberSwap (z : R[ε][ε]) :
    (iteratedDualNumberSwap R z).snd.fst = z.fst.snd := by
  simp [iteratedDualNumberSwap, iteratedDualNumberSwapHom, iteratedDualNumberLift_apply,
    algebraMap_eq_inl']

@[simp]
theorem _root_.DualNumber.snd_snd_iteratedDualNumberSwap (z : R[ε][ε]) :
    (iteratedDualNumberSwap R z).snd.snd = z.snd.snd := by
  simp [iteratedDualNumberSwap, iteratedDualNumberSwapHom, iteratedDualNumberLift_apply,
    algebraMap_eq_inl']

end Swap

end TauCeti

namespace MvPolynomial

section DualNumber

variable {R : Type*} [CommSemiring R]

/-- Evaluating a bivariate polynomial `p` at `![inl ε, ε]` in `R[ε][ε]` keeps its four coefficients
of degrees `≤ 1` in each variable. -/
theorem aeval_inl_eps_eps (p : MvPolynomial (Fin 2) R) :
    aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p =
      algebraMap R R[ε][ε] (p.coeff 0) +
        p.coeff (Finsupp.single 0 1) • inl (ε : R[ε]) +
        p.coeff (Finsupp.single 1 1) • (ε : R[ε][ε]) +
        p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) • ((ε : R[ε]) • (ε : R[ε][ε])) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply,
      add_smul]
    abel
  | monomial d r =>
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Fin.prod_univ_two]
    simp only [coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Finsupp.coe_zero,
      Finsupp.coe_add, Pi.zero_apply, Pi.add_apply, Finsupp.single_apply, Fin.isValue,
      zero_ne_one, one_ne_zero, ↓reduceIte, add_zero, zero_add]
    rcases d 0 with _ | _ | k₀ <;> rcases d 1 with _ | _ | k₁ <;>
      ext <;> simp [pow_add, mul_assoc, inl_eps_mul_inl_eps, algebraMap_eq_inl']

@[simp]
theorem fst_fst_aeval_inl_eps_eps (p : MvPolynomial (Fin 2) R) :
    (aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p).fst.fst = p.coeff 0 := by
  simp [aeval_inl_eps_eps, algebraMap_eq_inl']

@[simp]
theorem snd_fst_aeval_inl_eps_eps (p : MvPolynomial (Fin 2) R) :
    (aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p).fst.snd =
      p.coeff (Finsupp.single 0 1) := by
  simp [aeval_inl_eps_eps, algebraMap_eq_inl']

@[simp]
theorem fst_snd_aeval_inl_eps_eps (p : MvPolynomial (Fin 2) R) :
    (aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p).snd.fst =
      p.coeff (Finsupp.single 1 1) := by
  simp [aeval_inl_eps_eps, algebraMap_eq_inl']

@[simp]
theorem snd_snd_aeval_inl_eps_eps (p : MvPolynomial (Fin 2) R) :
    (aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p).snd.snd =
      p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) := by
  simp [aeval_inl_eps_eps, algebraMap_eq_inl']

end DualNumber

end MvPolynomial

namespace DualNumber

section MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- Evaluating bivariate polynomials over `R` at `![inl ε, ε]` in `R[ε][ε]` has kernel
`(X 0 ^ 2, X 1 ^ 2)`. -/
@[simp]
theorem ker_aeval_inl_eps_eps :
    RingHom.ker
        (MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] :
          MvPolynomial (Fin 2) R →ₐ[R] R[ε][ε]) =
      Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2} := by
  have hspan :
      ({MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2} : Set (MvPolynomial (Fin 2) R)) =
        (fun s ↦ MvPolynomial.monomial s (1 : R)) ''
          {Finsupp.single 0 2, Finsupp.single 1 2} := by
    simp [MvPolynomial.X_pow_eq_monomial]
  refine le_antisymm (fun p hp ↦ ?_) (Ideal.span_le.mpr ?_)
  · rw [RingHom.mem_ker] at hp
    rw [hspan, MvPolynomial.mem_ideal_span_monomial_image]
    intro d hd
    by_contra! hlt
    have hd0 : d 0 < 2 := by
      have := hlt (Finsupp.single 0 2) (Or.inl rfl)
      rw [Finsupp.single_le_iff] at this
      omega
    have hd1 : d 1 < 2 := by
      have := hlt (Finsupp.single 1 2) (Or.inr rfl)
      rw [Finsupp.single_le_iff] at this
      omega
    refine MvPolynomial.mem_support_iff.mp hd ?_
    rcases hp0 : d 0 with _ | _ | _ <;> rcases hp1 : d 1 with _ | _ | _ <;> try omega
    · have hdeq : d = 0 := by ext i; fin_cases i <;> assumption
      simpa [hdeq] using congrArg (fun z : R[ε][ε] ↦ z.fst.fst) hp
    · have hdeq : d = Finsupp.single 1 1 := by ext i; fin_cases i <;> simp_all
      simpa [hdeq] using congrArg (fun z : R[ε][ε] ↦ z.snd.fst) hp
    · have hdeq : d = Finsupp.single 0 1 := by ext i; fin_cases i <;> simp_all
      simpa [hdeq] using congrArg (fun z : R[ε][ε] ↦ z.fst.snd) hp
    · have hdeq : d = Finsupp.single 0 1 + Finsupp.single 1 1 := by
        ext i; fin_cases i <;> simp_all
      simpa [hdeq] using congrArg (fun z : R[ε][ε] ↦ z.snd.snd) hp
  · rintro _ (rfl | rfl) <;> simp [RingHom.mem_ker]

end MvPolynomial

end DualNumber

namespace TauCeti

section MvPolynomialQuotient

variable (R : Type*) [CommRing R]

private theorem mk_X_mul_self_eq_zero (i : Fin 2) :
    let I : Ideal (MvPolynomial (Fin 2) R) :=
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ 2, MvPolynomial.X 1 ^ 2}
    Ideal.Quotient.mkₐ R I (MvPolynomial.X i) * Ideal.Quotient.mkₐ R I (MvPolynomial.X i) = 0 := by
  simp only [← sq, ← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  fin_cases i <;> exact Ideal.subset_span (by simp)

/-- The bivariate polynomial presentation `R[X₀, X₁] / (X₀², X₁²) ≃ₐ[R] R[ε][ε]` of the iterated
dual numbers, sending the residue class of `X 0` to `inl ε` and the residue class of `X 1` to
`ε`. -/
noncomputable def iteratedDualNumberMvPolynomialQuotientAlgEquiv :
    (MvPolynomial (Fin 2) R ⧸
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ 2, MvPolynomial.X 1 ^ 2}) ≃ₐ[R]
      R[ε][ε] :=
  let I : Ideal (MvPolynomial (Fin 2) R) :=
    Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ 2, MvPolynomial.X 1 ^ 2}
  have hI : ∀ p ∈ I, MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p = 0 := fun _ hp ↦
    RingHom.mem_ker.mp ((DualNumber.ker_aeval_inl_eps_eps (R := R)).symm ▸ hp)
  -- `Ideal.Quotient.liftₐ` uses `Ring` quotient instances rather than the `CommRing` shortcut,
  -- so we rewrite via `liftₐ_comp` before `simp` unfolds `liftₐ_apply`.
  have hlift (p : MvPolynomial (Fin 2) R) :
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])]) hI
        (Ideal.Quotient.mkₐ R I p) = MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p := by
    simpa only [AlgHom.comp_apply] using congr($(Ideal.Quotient.liftₐ_comp I _ hI) p)
  AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])]) hI)
    (iteratedDualNumberLift ⟨(Ideal.Quotient.mkₐ R I (MvPolynomial.X 0),
        Ideal.Quotient.mkₐ R I (MvPolynomial.X 1)),
      mk_X_mul_self_eq_zero R 0, mk_X_mul_self_eq_zero R 1, Commute.all _ _⟩)
    (iteratedDualNumber_algHom_ext
      (by simp [-Ideal.Quotient.liftₐ_apply, -Ideal.Quotient.mkₐ_eq_mk, hlift])
      (by simp [-Ideal.Quotient.liftₐ_apply, -Ideal.Quotient.mkₐ_eq_mk, hlift]))
    (Ideal.Quotient.algHom_ext _ (by
      rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      fin_cases i <;> simp [I]))

variable {R}

/-- `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` evaluates a residue class at
`![inl ε, ε]`. -/
@[simp]
theorem _root_.MvPolynomial.iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk
    (p : MvPolynomial (Fin 2) R) :
    iteratedDualNumberMvPolynomialQuotientAlgEquiv R
        (Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2}) p) =
      MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p := by
  simp only [iteratedDualNumberMvPolynomialQuotientAlgEquiv, AlgEquiv.ofAlgHom_apply,
    Ideal.Quotient.liftₐ_apply]
  exact Ideal.Quotient.lift_mk _ _ _

/-- `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` sends the residue class of `X 0` to
`inl ε`. -/
theorem iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk_X_zero :
    iteratedDualNumberMvPolynomialQuotientAlgEquiv R
        (Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2})
          (MvPolynomial.X 0)) =
      inl (ε : R[ε]) := by
  simp

/-- `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` sends the residue class of `X 1` to
`ε`. -/
theorem iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk_X_one :
    iteratedDualNumberMvPolynomialQuotientAlgEquiv R
        (Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2})
          (MvPolynomial.X 1)) =
      (ε : R[ε][ε]) := by
  simp

/-- The inverse of `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` sends `inl ε` to the
residue class of `X 0`. -/
@[simp]
theorem iteratedDualNumberMvPolynomialQuotientAlgEquiv_symm_inl_eps :
    (iteratedDualNumberMvPolynomialQuotientAlgEquiv R).symm (inl (ε : R[ε])) =
      Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2})
        (MvPolynomial.X 0) := by
  rw [AlgEquiv.symm_apply_eq, iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk_X_zero]

/-- The inverse of `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` sends `ε` to the
residue class of `X 1`. -/
@[simp]
theorem iteratedDualNumberMvPolynomialQuotientAlgEquiv_symm_eps :
    (iteratedDualNumberMvPolynomialQuotientAlgEquiv R).symm (ε : R[ε][ε]) =
      Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2})
        (MvPolynomial.X 1) := by
  rw [AlgEquiv.symm_apply_eq, iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk_X_one]

/-- The inverse of `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` sends
`ε • ε = inl ε * ε` to the residue class of `X 0 * X 1`. -/
@[simp]
theorem iteratedDualNumberMvPolynomialQuotientAlgEquiv_symm_smul_eps :
    (iteratedDualNumberMvPolynomialQuotientAlgEquiv R).symm ((ε : R[ε]) • (ε : R[ε][ε])) =
      Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2})
        (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [← inl_eps_mul_eps, map_mul, iteratedDualNumberMvPolynomialQuotientAlgEquiv_symm_inl_eps,
    iteratedDualNumberMvPolynomialQuotientAlgEquiv_symm_eps, map_mul]

/-- The inverse of `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` expands `z : R[ε][ε]`
into the residue class of its four-term multilinear representative. -/
theorem _root_.DualNumber.iteratedDualNumberMvPolynomialQuotientAlgEquiv_symm_apply
    (z : R[ε][ε]) :
    (iteratedDualNumberMvPolynomialQuotientAlgEquiv R).symm z =
      Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2})
        (MvPolynomial.C z.fst.fst + MvPolynomial.C z.fst.snd * MvPolynomial.X 0 +
          MvPolynomial.C z.snd.fst * MvPolynomial.X 1 +
          MvPolynomial.C z.snd.snd * MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [AlgEquiv.symm_apply_eq, MvPolynomial.iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk]
  ext <;> simp [algebraMap_eq_inl']

end MvPolynomialQuotient

end TauCeti
