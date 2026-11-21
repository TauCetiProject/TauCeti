/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.TrivSqZeroExt
import TauCeti.RingTheory.MvPolynomial.Ideal.Taylor

/-!
# First jets of multivariate polynomials

For a point `P : σ → R`, the *first jet* of a polynomial `f` at `P` is its value `f(P)` together
with its gradient `(∂ⱼ f (P))ⱼ`. These form the square-zero extension `R ⊕ (σ → R)`, whose
multiplication `(a, v) (b, w) = (a b, a w + b v)` is the Leibniz rule, so taking first jets is an
algebra homomorphism `TauCeti.jetAlgebra P : R[X] →ₐ[R] TrivSqZeroExt R (σ → R)`. It is algebra
evaluation at the point whose `j`-th coordinate is `P j + εⱼ`, the infinitesimals `εⱼ` having
pairwise products zero; the derivatives are Mathlib's `MvPolynomial.pderiv`, with no factorials,
so everything holds in every characteristic. A single directional derivative is read off from
evaluation at a dual-number point by `MvPolynomial.aeval_inl_add_inr`; the first jet records all
partial derivatives at once.

Over any commutative ring, the kernel of the first jet at `P` is the square `𝔪_P²` of the ideal
`𝔪_P = ker (eval P)` of polynomials vanishing at `P`: a polynomial lies in `𝔪_P²` exactly when its
value and all its first partial derivatives vanish at `P`. For finitely many variables, the first
jet at `P` is surjective, identifying `R[X] ⧸ 𝔪_P²` with `TrivSqZeroExt R (σ → R)`
(`TauCeti.jetAlgebraEquiv`), the coordinate ring of the double point at `P`. Pointwise,
`TauCeti.jetEquivOption` identifies `TrivSqZeroExt R (σ → R)` linearly with `Option σ → R`.

## Main definitions

* `TauCeti.jetAlgebra P`: the first jet at `P`, as an algebra homomorphism to
  `TrivSqZeroExt R (σ → R)`.
* `TauCeti.jetAlgebraEquiv P`: for finitely many variables over a commutative ring, the algebra
  equivalence `MvPolynomial σ R ⧸ RingHom.ker (eval P) ^ 2 ≃ₐ[R] TrivSqZeroExt R (σ → R)`.
* `TauCeti.jetEquivOption R σ`: the linear equivalence
  `TrivSqZeroExt R (σ → R) ≃ₗ[R] (Option σ → R)`.

## Main results

* `TauCeti.fst_jetAlgebra`, `TauCeti.snd_jetAlgebra_apply`: the first jet consists of the value
  and the partial derivatives at `P`.
* `TauCeti.sub_sum_mem_ker_eval_sq`: the first-order Taylor expansion modulo `𝔪_P²`.
* `TauCeti.jetAlgebra_surjective`, `TauCeti.ker_jetAlgebra`: the first jet is surjective (in
  finitely many variables) with kernel `𝔪_P²`.
* `TauCeti.jetAlgebraEquiv_mk`: `jetAlgebraEquiv P` sends the class of `f` to `jetAlgebra P f`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3.
* M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz theorem*,
  arXiv:math/0701409, §2, Proposition 2.1.
-/

public section

namespace TauCeti

open MvPolynomial TrivSqZeroExt

variable {σ : Type*}

section PointIdeal

variable {R : Type*} [CommRing R]

/-- `Xⱼ - Pⱼ` vanishes at `P`. -/
theorem X_sub_C_mem_ker_eval (P : σ → R) (j : σ) : X j - C (P j) ∈ RingHom.ker (eval P) := by
  simp [RingHom.mem_ker]

/-- The first-order part `∑ⱼ ∂ⱼ f (P) (Xⱼ - Pⱼ)` of the expansion of `f` at `P` after a polynomial
`p * Xᵢ`: it is `Pᵢ` times that of `p`, plus `p(P) (Xᵢ - Pᵢ)`. -/
private theorem sum_pderiv_mul_X [Fintype σ] (P : σ → R) (p : MvPolynomial σ R) (i : σ) :
    ∑ j, C (eval P (pderiv j (p * X i))) * (X j - C (P j)) =
      C (eval P p) * (X i - C (P i)) +
        C (P i) * ∑ j, C (eval P (pderiv j p)) * (X j - C (P j)) := by
  classical
  simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Fintype.sum_eq_single i fun j hj ↦ by simp [hj.symm]]
    simp
  · exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **First-order Taylor expansion.** A polynomial agrees with its first-order Taylor polynomial
`f(P) + ∑ⱼ ∂ⱼ f (P) (Xⱼ - Pⱼ)` at `P` modulo the square of the ideal of `P`. -/
theorem sub_sum_mem_ker_eval_sq [Fintype σ] (P : σ → R) (f : MvPolynomial σ R) :
    f - C (eval P f) - ∑ j, C (eval P (pderiv j f)) * (X j - C (P j)) ∈
      RingHom.ker (eval P) ^ 2 := by
  rw [sq]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    convert add_mem hp hq using 1
    simp only [map_add, Finset.sum_add_distrib, add_mul]
    ring
  | mul_X p i hp =>
    -- The remainder for `p * Xᵢ` is the remainder for `p` times `Xᵢ`, plus the first-order part
    -- of `p` times `Xᵢ - Pᵢ`, which lies in `𝔪_P * 𝔪_P`.
    have key : p * X i - C (eval P (p * X i)) -
        ∑ j, C (eval P (pderiv j (p * X i))) * (X j - C (P j)) =
        (p - C (eval P p) - ∑ j, C (eval P (pderiv j p)) * (X j - C (P j))) * X i +
          (∑ j, C (eval P (pderiv j p)) * (X j - C (P j))) * (X i - C (P i)) := by
      rw [sum_pderiv_mul_X, eval_mul, eval_X, map_mul]
      ring
    rw [key]
    exact add_mem (Ideal.mul_mem_right _ _ hp) <| Ideal.mul_mem_mul
      (sum_mem fun j _ ↦ Ideal.mul_mem_left _ _ (X_sub_C_mem_ker_eval P j))
      (X_sub_C_mem_ker_eval P i)

end PointIdeal

section JetAlgebra

variable {R : Type*} [CommSemiring R]

/-- The linear equivalence identifying `TrivSqZeroExt R (σ → R)` with `Option σ → R`:
`none` selects the scalar part `fst`, and `some j` selects the `j`-th infinitesimal coordinate
`snd j`. -/
noncomputable def jetEquivOption (R σ : Type*) [CommSemiring R] :
    TrivSqZeroExt R (σ → R) ≃ₗ[R] (Option σ → R) :=
  (TrivSqZeroExt.linearEquivProd R (σ → R)).trans
    (LinearEquiv.piOptionEquivProd R (M := fun _ : Option σ ↦ R)).symm

/-- The `none` coordinate of `jetEquivOption` is the scalar part `fst`. -/
@[simp]
theorem jetEquivOption_apply_none (x : TrivSqZeroExt R (σ → R)) :
    jetEquivOption R σ x none = x.fst := by
  simp [jetEquivOption, LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]

/-- The `some j` coordinate of `jetEquivOption` is the `j`-th infinitesimal coordinate `snd j`. -/
@[simp]
theorem jetEquivOption_apply_some (x : TrivSqZeroExt R (σ → R)) (j : σ) :
    jetEquivOption R σ x (some j) = x.snd j := by
  simp [jetEquivOption, LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]

/-- The inverse of `jetEquivOption` sends an `Option σ`-indexed tuple `v` to
`inl (v none) + inr (fun j ↦ v (some j))`. -/
@[simp]
theorem jetEquivOption_symm_apply (v : Option σ → R) :
    (jetEquivOption R σ).symm v = inl (v none) + inr fun j ↦ v (some j) := by
  ext <;> simp [jetEquivOption, LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd]

variable [DecidableEq σ]

/-- The first jet of a polynomial at a point `P`: algebra evaluation at the point of
`TrivSqZeroExt R (σ → R)` whose `j`-th coordinate is `P j` plus the `j`-th infinitesimal
coordinate. Its value part is `f(P)` (`TauCeti.fst_jetAlgebra`) and its square-zero part is the
gradient `(∂ⱼ f (P))ⱼ` (`TauCeti.snd_jetAlgebra_apply`). -/
noncomputable def jetAlgebra (P : σ → R) : MvPolynomial σ R →ₐ[R] TrivSqZeroExt R (σ → R) :=
  aeval fun j ↦ inl (P j) + inr (Pi.single j 1)

theorem jetAlgebra_def (P : σ → R) :
    jetAlgebra P = aeval fun j ↦ inl (P j) + inr (Pi.single j 1) :=
  (rfl)

@[simp]
theorem jetAlgebra_X (P : σ → R) (j : σ) :
    jetAlgebra P (X j) = inl (P j) + inr (Pi.single j 1) :=
  aeval_X _ j

theorem jetAlgebra_C (P : σ → R) (a : R) : jetAlgebra P (C a) = inl a :=
  (jetAlgebra P).commutes a

/-- The value part of the first jet of `f` at `P` is `f(P)`. -/
@[simp]
theorem fst_jetAlgebra (P : σ → R) (f : MvPolynomial σ R) : (jetAlgebra P f).fst = eval P f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The square-zero part of the first jet of `f` at `P` is the gradient of `f` at `P`. -/
@[simp]
theorem snd_jetAlgebra_apply (P : σ → R) (f : MvPolynomial σ R) (j : σ) :
    (jetAlgebra P f).snd j = eval P (pderiv j f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, Pi.single_apply, Derivation.leibniz, pderiv_X, eq_comm (a := j)]
    split_ifs <;> simp

/-- The first jet of `f` at `P` is its value plus its gradient at `P`. -/
theorem jetAlgebra_apply (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebra P f = inl (eval P f) + inr fun j ↦ eval P (pderiv j f) := by
  ext <;> simp

/-- A polynomial has first jet zero at `P` exactly when its value and all its first partial
derivatives vanish at `P`. -/
theorem jetAlgebra_eq_zero_iff (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebra P f = 0 ↔ eval P f = 0 ∧ ∀ j, eval P (pderiv j f) = 0 := by
  simp [TrivSqZeroExt.ext_iff, funext_iff]

variable {R : Type*} [CommRing R]

/-- Over a commutative ring, every value and gradient at a point is the first jet of a
polynomial: `a + ∑ⱼ vⱼ (Xⱼ - Pⱼ)` has value `a` and gradient `v` at `P`. -/
theorem jetAlgebra_surjective [Finite σ] (P : σ → R) : Function.Surjective (jetAlgebra P) := by
  cases nonempty_fintype σ
  intro x
  refine ⟨C x.fst + ∑ j, C (x.snd j) * (X j - C (P j)), ?_⟩
  rw [jetAlgebra_apply]
  ext i
  · simp
  · simp [Pi.single_apply]

/-- The kernel of the first jet at `P` is the square of the ideal of `P`: a polynomial lies in
`𝔪_P²` exactly when its value and first partial derivatives vanish at `P`. This holds over any
commutative ring and in arbitrarily many variables. -/
theorem ker_jetAlgebra (P : σ → R) :
    RingHom.ker (jetAlgebra P) = RingHom.ker (eval P) ^ 2 := by
  ext f
  rw [RingHom.mem_ker, jetAlgebra_eq_zero_iff, mem_pow_ker_eval_iff, mem_pow_idealOfVars_iff']
  constructor
  · rintro ⟨h0, h1⟩ m hm
    obtain hdeg0 | hdeg1 : m.degree = 0 ∨ m.degree = 1 := by omega
    · rw [(Finsupp.degree_eq_zero_iff m).1 hdeg0, ← constantCoeff_eq, constantCoeff_taylor, h0]
    · obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff m).1
        (by simpa [Finsupp.degree_apply, Finsupp.sum] using hdeg1)
      rw [coeff_single_one_taylor, h1 j]
  · intro h
    refine ⟨?_, fun j ↦ ?_⟩
    · rw [← constantCoeff_taylor, constantCoeff_eq]
      exact h 0 (by simp)
    · rw [← coeff_single_one_taylor]
      exact h (Finsupp.single j 1) (by simp)

/-- For finitely many variables over a commutative ring, the quotient by `RingHom.ker (eval P) ^ 2`
is isomorphic as an `R`-algebra to the trivial square-zero extension `TrivSqZeroExt R (σ → R)`;
the class of a polynomial maps to its value and first partial derivatives at `P`
(`TauCeti.jetAlgebraEquiv_mk`). -/
noncomputable def jetAlgebraEquiv [Finite σ] (P : σ → R) :
    (MvPolynomial σ R ⧸ RingHom.ker (eval P) ^ 2) ≃ₐ[R] TrivSqZeroExt R (σ → R) :=
  (Ideal.quotientEquivAlgOfEq R (ker_jetAlgebra P).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (jetAlgebra_surjective P))

/-- The quotient equivalence `jetAlgebraEquiv P` sends the class of a polynomial `f` to its value
and first partial derivatives at `P`. -/
@[simp]
theorem jetAlgebraEquiv_mk [Finite σ] (P : σ → R) (f : MvPolynomial σ R) :
    jetAlgebraEquiv P (Ideal.Quotient.mk _ f) = jetAlgebra P f := by
  simp [jetAlgebraEquiv]

end JetAlgebra

end TauCeti
