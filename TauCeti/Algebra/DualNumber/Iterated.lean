/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
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

Over a commutative semiring `R`, evaluating `MvPolynomial (Fin 2) R` at `![inl ε, ε]` has kernel
`(X 0 ^ 2, X 1 ^ 2)` (`TauCeti.ker_aeval_inl_eps_eps`). Over a commutative ring `R`, this yields
the presentation `R[X₀, X₁] / (X₀², X₁²) ≃ₐ[R] R[ε][ε]`
(`TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv`).

## Main definitions

* `TauCeti.iteratedDualNumberBasis`: the `R`-module basis `{1, inl ε, ε, ε • ε}` of `R[ε][ε]`
  indexed by `Fin 2 × Fin 2` (for a semiring `R`).
* `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv`: for a commutative ring `R`, the
  `R`-algebra equivalence
  `MvPolynomial (Fin 2) R ⧸ Ideal.span {X 0 ^ 2, X 1 ^ 2} ≃ₐ[R] R[ε][ε]`.

## Main results

* `TauCeti.inl_eps_pow_two`, `TauCeti.inl_eps_mul_eps`: `(inl ε) ^ 2 = 0` and
  `inl ε * ε = ε • ε` in `R[ε][ε]`.
* `TauCeti.finrank_iteratedDualNumber`: `Module.finrank R R[ε][ε] = 4` under
  `StrongRankCondition R`.
* `TauCeti.ker_aeval_inl_eps_eps`: over a commutative semiring `R`, the kernel of
  `MvPolynomial.aeval ![inl ε, ε]` is `Ideal.span {X 0 ^ 2, X 1 ^ 2}`.
-/

public section

open DualNumber TrivSqZeroExt

namespace TauCeti

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
      ext <;> simp [pow_add, mul_assoc, TauCeti.inl_eps_mul_inl_eps, algebraMap_eq_inl']

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

namespace TauCeti

section MvPolynomial

variable {R : Type*} [CommSemiring R]

private theorem aeval_inl_eps_eps_repr (z : R[ε][ε]) :
    MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])]
        (MvPolynomial.C z.fst.fst + MvPolynomial.C z.fst.snd * MvPolynomial.X 0 +
          MvPolynomial.C z.snd.fst * MvPolynomial.X 1 +
          MvPolynomial.C z.snd.snd * MvPolynomial.X 0 * MvPolynomial.X 1) = z := by
  ext <;> simp [algebraMap_eq_inl']

/-- Evaluating bivariate polynomials over `R` at `![inl ε, ε]` is surjective onto `R[ε][ε]`. -/
theorem aeval_inl_eps_eps_surjective :
    Function.Surjective
      (MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] :
        MvPolynomial (Fin 2) R →ₐ[R] R[ε][ε]) :=
  fun z ↦ ⟨_, aeval_inl_eps_eps_repr z⟩

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

section MvPolynomialQuotient

variable (R : Type*) [CommRing R]

/-- The bivariate polynomial presentation `R[X₀, X₁] / (X₀², X₁²) ≃ₐ[R] R[ε][ε]` of the iterated
dual numbers, sending the residue class of `X 0` to `inl ε` and the residue class of `X 1` to
`ε`. -/
noncomputable def iteratedDualNumberMvPolynomialQuotientAlgEquiv :
    (MvPolynomial (Fin 2) R ⧸
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ 2, MvPolynomial.X 1 ^ 2}) ≃ₐ[R]
      R[ε][ε] :=
  (Ideal.quotientEquivAlgOfEq R (ker_aeval_inl_eps_eps (R := R)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective aeval_inl_eps_eps_surjective)

variable {R}

/-- `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv` evaluates a residue class at
`![inl ε, ε]`. -/
@[simp]
theorem _root_.MvPolynomial.iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk
    (p : MvPolynomial (Fin 2) R) :
    iteratedDualNumberMvPolynomialQuotientAlgEquiv R
        (Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1 ^ 2}) p) =
      MvPolynomial.aeval ![inl (ε : R[ε]), (ε : R[ε][ε])] p := by
  simp only [iteratedDualNumberMvPolynomialQuotientAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

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
  rw [AlgEquiv.symm_apply_eq, MvPolynomial.iteratedDualNumberMvPolynomialQuotientAlgEquiv_mk,
    aeval_inl_eps_eps_repr]

end MvPolynomialQuotient

end TauCeti
