/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import TauCeti.RingTheory.MvPolynomial.Trace
import Mathlib.Algebra.MvPolynomial.Funext
import TauCeti.RingTheory.Polynomial.Dickson

/-!
# The action of integral matrices on binary forms

Fix a commutative ring `R` and a natural number `w`. Let `V_w` be the `R`-module of binary forms
of degree `w`, modelled as `homogeneousSubmodule (Fin 2) R w` with `X = X 0` and `Y = X 1`.
Integral `2 × 2` matrices act on it on the right, `(P ∣ M)(X, Y) = P(aX + bY, cX + dY)` for
`M = !![a, b; c, d]`, so that `P ∣ (M * N) = (P ∣ M) ∣ N`. This action is the coefficient module
of both period polynomials and modular symbols of weight `w + 2`.

A linear functional `φ` on `V_w` determines the binary form `D φ` whose value at `(x, y)` is
`φ ((xY - yX)ʷ)`. This construction is compatible with the actions: the
action of `M` on `D φ` is the adjugate action on `φ`, transposed. Applied to the period functional
`P ↦ ∫₀^{i∞} f(τ) P(τ, 1) dτ` of a cusp form `f`, it produces the period polynomial
`r_f(X, Y) = ∫₀^{i∞} f(τ) (X - τY)ʷ dτ`.

## Main definitions

* `TauCeti.binaryFormRep R w`: the right action of integral matrices on binary forms of degree
  `w`, as a representation of `(Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ`.
* `TauCeti.binaryFormAdjugateRep R w`: the left action `P ↦ P ∣ adj M` of integral matrices, the
  right action precomposed with the anti-multiplicative adjugate.
* `TauCeti.binaryFormMonomialBasis R w`: the monomial basis `Xʲ Yʷ⁻ʲ`, `0 ≤ j ≤ w`.
* `TauCeti.linearFormPow R w x y`: the binary form `(xY - yX)ʷ`.
* `TauCeti.binaryFormDual R w`: the linear map `φ ↦ D φ` from functionals to binary forms.

## Main results

* `TauCeti.binaryFormRep_op_mul_apply`: the action is on the right, `P ∣ (M * N) =
  (P ∣ M) ∣ N`.
* `TauCeti.binaryFormRep_op_neg`, `TauCeti.binaryFormRep_op_scalar`: negated and scalar matrices
  act by `(-1)ʷ` and by the `w`th power of the scalar.
* `TauCeti.mapHomogeneousSubmodule_binaryFormRep`: changing coefficients commutes with the action.
* `TauCeti.trace_binaryFormRep_eq_dickson_eval`: the trace is the Dickson weight polynomial
  evaluated at the matrix trace and determinant.
* `TauCeti.trace_binaryFormRep_eq_one_of_trace_eq_zero_det_eq_neg_one`: reflections have trace
  one in even degree over every commutative coefficient ring.
* `TauCeti.binaryFormRep_adjugate_linearFormPow`: `(xY - yX)ʷ ∣ adj M = (x'Y - y'X)ʷ` for
  `(x', y') = M (x, y)`.
* `TauCeti.eval_binaryFormDual`: `D φ` takes the value `φ ((xY - yX)ʷ)` at `(x, y)`.
* `TauCeti.binaryFormRep_binaryFormDual`: `(D φ) ∣ M = D (φ ∘ (· ∣ adj M))`.
* `TauCeti.binaryFormDual_injective`: `D` is injective when the binomial coefficients
  `w choose j` are not zero divisors.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105--122, arXiv:1711.00327, Section 4.
-/

public section

open Matrix MulOpposite MvPolynomial

namespace TauCeti

variable (R : Type*) [CommRing R] (w : ℕ)

/-- The right action `P ↦ P ∣ M` of integral `2 × 2` matrices on binary forms of degree `w`,
`(P ∣ M)(X, Y) = P(aX + bY, cX + dY)` for `M = !![a, b; c, d]`, as a representation of the
opposite matrix monoid. -/
noncomputable def binaryFormRep :
    Representation R (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ (homogeneousSubmodule (Fin 2) R w) :=
  (linearSubstRep (Fin 2) R w).comp
    (MonoidHom.op (Int.castRingHom R).mapMatrix.toMonoidHom)

variable {R w}

/-- Integral substitution is homogeneous substitution after mapping the matrix entries into
its coefficient ring. -/
theorem binaryFormRep_op (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binaryFormRep R w (op M) =
      linearSubstRep (Fin 2) R w (op (M.map (Int.castRingHom R))) := (rfl)

/-- The trace of an integral matrix on binary forms is its Dickson weight polynomial. -/
theorem trace_binaryFormRep_eq_dickson_eval {K : Type*} [CommRing K] (w : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    LinearMap.trace K (homogeneousSubmodule (Fin 2) K w) (binaryFormRep K w (op M)) =
      (Polynomial.dickson 2 (M.det : K) w).eval (M.trace : K) := by
  have hd : (M.map (Int.castRingHom K)).det = (M.det : K) := (Int.cast_det M).symm
  have ht : (M.map (Int.castRingHom K)).trace = (M.trace : K) :=
    (AddMonoidHom.map_trace (Int.castRingHom K) M).symm
  rw [binaryFormRep_op]
  simpa only [hd, ht] using
    trace_linearSubstRep_eq_dickson_eval w (M.map (Int.castRingHom K))

/-- A trace-zero integral matrix of determinant `-1` has trace `1` on binary forms of even
degree, over any commutative coefficient ring. -/
theorem trace_binaryFormRep_eq_one_of_trace_eq_zero_det_eq_neg_one
    {M : Matrix (Fin 2) (Fin 2) ℤ} (ht : M.trace = 0) (hd : M.det = -1) (hw : Even w) :
    LinearMap.trace R (homogeneousSubmodule (Fin 2) R w) (binaryFormRep R w (op M)) = 1 := by
  obtain ⟨m, rfl⟩ := hw
  rw [trace_binaryFormRep_eq_dickson_eval, ht, hd]
  simpa [two_mul] using Polynomial.dickson_two_eval_zero_two_mul (-1 : R) m

@[simp]
theorem coe_binaryFormRep_apply (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    (binaryFormRep R w (op M) P : MvPolynomial (Fin 2) R) =
      linearSubst (M.map (Int.cast : ℤ → R)) P := by
  simp [binaryFormRep]

/-- The action is on the right: `P ∣ (M * N) = (P ∣ M) ∣ N`. -/
theorem binaryFormRep_op_mul_apply (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    binaryFormRep R w (op (M * N)) P = binaryFormRep R w (op N) (binaryFormRep R w (op M) P) := by
  rw [op_mul, map_mul, Module.End.mul_apply]

/-- Negating the matrix multiplies a form of degree `w` by `(-1)ʷ`. -/
theorem binaryFormRep_op_neg (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binaryFormRep R w (op (-M)) = (-1 : R) ^ w • binaryFormRep R w (op M) := by
  refine LinearMap.ext fun P ↦ Subtype.ext ?_
  simp only [coe_binaryFormRep_apply, LinearMap.smul_apply, Submodule.coe_smul]
  rw [Matrix.map_neg _ Int.cast_neg, P.2.linearSubst_neg]

/-- For even `w`, a matrix and its negative act in the same way. -/
theorem binaryFormRep_op_neg_of_even (hw : Even w) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binaryFormRep R w (op (-M)) = binaryFormRep R w (op M) := by
  rw [binaryFormRep_op_neg, hw.neg_one_pow, one_smul]

variable (R w) in
/-- **The left action `P ↦ P ∣ adj M` of integral matrices on binary forms of degree `w`**, as a
representation of the matrix monoid: the adjugate is anti-multiplicative, so precomposing the
right action `TauCeti.binaryFormRep` with it gives a left action. On `SL(2, ℤ)` the adjugate is
the inverse, so this restricts to `P ↦ P ∣ γ⁻¹`; on a matrix of determinant `n` it is the action
that appears in the Hecke operators on modular symbols, where `{α, β} ⊗ P` is sent to
`{δα, δβ} ⊗ (P ∣ adj δ)`. -/
noncomputable def binaryFormAdjugateRep :
    Representation R (Matrix (Fin 2) (Fin 2) ℤ) (homogeneousSubmodule (Fin 2) R w) :=
  (binaryFormRep R w).comp
    { toFun := fun M ↦ op (adjugate M)
      map_one' := by simp
      map_mul' := fun M N ↦ by simp [adjugate_mul_distrib] }

-- Low priority, so that lemmas stated at `binaryFormAdjugateRep` fire before it is unfolded to
-- the right action.
@[simp low]
theorem binaryFormAdjugateRep_apply (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    binaryFormAdjugateRep R w M P = binaryFormRep R w (op (adjugate M)) P := (rfl)

/-- An integer scalar matrix acts on degree-`w` binary forms by its `w`th power. -/
@[simp]
theorem binaryFormRep_op_scalar (a : ℤ) :
    binaryFormRep R w (op !![a, 0; 0, a]) =
      (a : R) ^ w • (1 : Module.End R (homogeneousSubmodule (Fin 2) R w)) := by
  have hmat : (!![a, 0; 0, a] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) =
      (a : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  simp [hmat, P.2.linearSubst_smul]

/-! ### Binary forms attached to linear functionals -/

/-- The monomial basis `Xʲ Yʷ⁻ʲ`, `0 ≤ j ≤ w`, of the binary forms of degree `w`, indexed by the
exponent `j` of `X`. -/
noncomputable def binaryFormMonomialBasis (R : Type*) [CommSemiring R] (w : ℕ) :
    Module.Basis (Fin (w + 1)) R (homogeneousSubmodule (Fin 2) R w) :=
  (homogeneousMonomialBasis w).reindex (finsuppDegreeFinTwoEquiv w)

@[simp]
theorem coe_binaryFormMonomialBasis {R : Type*} [CommSemiring R] {w : ℕ} (j : Fin (w + 1)) :
    (binaryFormMonomialBasis R w j : MvPolynomial (Fin 2) R) = X 0 ^ (j : ℕ) * X 1 ^ (w - j) := by
  rw [binaryFormMonomialBasis, Module.Basis.reindex_apply, coe_homogeneousMonomialBasis]
  simp only [coe_finsuppDegreeFinTwoEquiv_symm, X_pow_eq_monomial, monomial_mul_monomial,
    one_mul]

/-- Changing coefficients sends the monomial basis to the monomial basis. -/
@[simp]
theorem mapHomogeneousSubmodule_binaryFormMonomialBasis {S R : Type*} [CommSemiring S]
    [CommSemiring R] (f : S →+* R) (j : Fin (w + 1)) :
    mapHomogeneousSubmodule f w (binaryFormMonomialBasis S w j) = binaryFormMonomialBasis R w j :=
  Subtype.ext <| by simp

/-- Changing coefficients commutes with the action of integral matrices. -/
theorem mapHomogeneousSubmodule_binaryFormRep {S : Type*} [CommRing S] (f : S →+* R)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (P : homogeneousSubmodule (Fin 2) S w) :
    mapHomogeneousSubmodule f w (binaryFormRep S w (op M) P) =
      binaryFormRep R w (op M) (mapHomogeneousSubmodule f w P) := by
  apply Subtype.ext
  rw [coe_mapHomogeneousSubmodule_apply, coe_binaryFormRep_apply, map_linearSubst,
    Matrix.map_map, coe_binaryFormRep_apply, coe_mapHomogeneousSubmodule_apply]
  congr 3
  funext a
  simp

variable (R w) in
/-- The binary form `(xY - yX)ʷ` of degree `w`, the `w`th power of a linear form vanishing at
`(x, y)`. Its value at `(τ, 1)` is `(x - yτ)ʷ`. -/
noncomputable def linearFormPow (x y : R) : homogeneousSubmodule (Fin 2) R w :=
  ⟨(C x * X 1 - C y * X 0) ^ w, by
    simpa using ((isHomogeneous_C_mul_X x 1).sub (isHomogeneous_C_mul_X y 0)).pow w⟩

@[simp]
theorem coe_linearFormPow (x y : R) :
    (linearFormPow R w x y : MvPolynomial (Fin 2) R) = (C x * X 1 - C y * X 0) ^ w := (rfl)

/-- The binomial expansion of `(xY - yX)ʷ` in the monomial basis. -/
theorem linearFormPow_eq_sum (x y : R) :
    linearFormPow R w x y = ∑ j : Fin (w + 1),
      ((w.choose j : R) * (-y) ^ (j : ℕ) * x ^ (w - j)) • binaryFormMonomialBasis R w j := by
  apply Subtype.ext
  rw [coe_linearFormPow, Submodule.coe_sum, sub_eq_neg_add, add_pow,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Submodule.coe_smul, coe_binaryFormMonomialBasis, smul_eq_C_mul]
  simp only [map_mul, map_pow, map_neg, map_natCast]
  ring

/-- Substituting the adjugate of `M` into `(xY - yX)ʷ` gives `(x'Y - y'X)ʷ`, where
`(x', y') = M (x, y)`. -/
theorem binaryFormRep_adjugate_linearFormPow (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → R) :
    binaryFormRep R w (op (adjugate M)) (linearFormPow R w (v 0) (v 1)) =
      linearFormPow R w ((M.map (Int.cast : ℤ → R) *ᵥ v) 0)
        ((M.map (Int.cast : ℤ → R) *ᵥ v) 1) := by
  apply Subtype.ext
  simp only [coe_binaryFormRep_apply, coe_linearFormPow, map_pow, map_sub, map_mul,
    linearSubst_X, algHom_C, algebraMap_eq, adjugate_fin_two, Fin.sum_univ_two, mulVec,
    dotProduct, Matrix.map_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, Int.cast_neg]
  congr 1
  simp only [map_add, map_mul, map_neg]
  ring

variable (R w) in
/-- **The binary form attached to a functional.** A linear functional `φ` on the binary forms of
degree `w` determines the binary form `D φ` whose value at `(x, y)` is `φ ((xY - yX)ʷ)`
(`TauCeti.eval_binaryFormDual`). Explicitly,
`D φ = ∑ⱼ (-1)ʷ⁻ʲ (w choose j) φ (Xʷ⁻ʲ Yʲ) Xʲ Yʷ⁻ʲ`. For the period functional
`P ↦ ∫₀^{i∞} f(τ) P(τ, 1) dτ` of a cusp form `f` this is the period polynomial
`r_f(X, Y) = ∫₀^{i∞} f(τ) (X - τY)ʷ dτ`. -/
noncomputable def binaryFormDual :
    (homogeneousSubmodule (Fin 2) R w →ₗ[R] R) →ₗ[R] homogeneousSubmodule (Fin 2) R w :=
  (binaryFormMonomialBasis R w).equivFun.symm.toLinearMap ∘ₗ LinearMap.pi fun j ↦
    ((-1 : R) ^ (w - j) * (w.choose j : R)) •
      LinearMap.applyₗ (binaryFormMonomialBasis R w (Fin.rev j))

theorem binaryFormDual_apply (φ : homogeneousSubmodule (Fin 2) R w →ₗ[R] R) :
    binaryFormDual R w φ = ∑ j : Fin (w + 1),
      ((-1 : R) ^ (w - j) * (w.choose j : R) * φ (binaryFormMonomialBasis R w (Fin.rev j))) •
        binaryFormMonomialBasis R w j := by
  simp [binaryFormDual, Module.Basis.equivFun_symm_apply, mul_assoc]

/-- The value of `D φ` at `(x, y)` is `φ ((xY - yX)ʷ)`. -/
@[simp]
theorem eval_binaryFormDual (φ : homogeneousSubmodule (Fin 2) R w →ₗ[R] R) (v : Fin 2 → R) :
    eval v (binaryFormDual R w φ : MvPolynomial (Fin 2) R) = φ (linearFormPow R w (v 0) (v 1)) := by
  rw [binaryFormDual_apply, linearFormPow_eq_sum, map_sum, Submodule.coe_sum, map_sum]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : (j : ℕ) ≤ w := Nat.lt_succ_iff.mp j.2
  simp only [Fin.revPerm_apply, Fin.rev_rev, Submodule.coe_smul, coe_binaryFormMonomialBasis,
    smul_eq_mul, smul_eval, map_smul, Fin.val_rev, eval_mul, eval_pow, eval_X]
  have h₁ : w + 1 - (j + 1) = w - j := by omega
  have h₂ : w - (w - j) = j := by omega
  rw [h₁, h₂, Nat.choose_symm hj, neg_pow (v 1)]
  ring

private theorem binaryFormRep_binaryFormDual_of_infinite_domain [IsDomain R] [Infinite R]
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (φ : homogeneousSubmodule (Fin 2) R w →ₗ[R] R) :
    binaryFormRep R w (op M) (binaryFormDual R w φ) =
      binaryFormDual R w (φ ∘ₗ binaryFormAdjugateRep R w M) := by
  apply Subtype.ext
  refine MvPolynomial.funext fun v ↦ ?_
  rw [coe_binaryFormRep_apply, eval_linearSubst, eval_binaryFormDual, eval_binaryFormDual,
    LinearMap.comp_apply, binaryFormAdjugateRep_apply, binaryFormRep_adjugate_linearFormPow]

/-- **Equivariance of `D`.** For every integral matrix `M`, `(D φ) ∣ M =
`D (φ ∘ (· ∣ adj M))`: the action of `M` on the binary form attached to `φ` is the transpose of
the adjugate action on the functional. -/
theorem binaryFormRep_binaryFormDual (M : Matrix (Fin 2) (Fin 2) ℤ)
    (φ : homogeneousSubmodule (Fin 2) R w →ₗ[R] R) :
    binaryFormRep R w (op M) (binaryFormDual R w φ) =
      binaryFormDual R w (φ ∘ₗ binaryFormAdjugateRep R w M) := by
  classical
  let A := MvPolynomial R ℤ
  let f : A →+* R := eval₂Hom (Int.castRingHom R) id
  let φA : homogeneousSubmodule (Fin 2) A w →ₗ[A] A :=
    (binaryFormMonomialBasis A w).constr A fun j ↦ X (φ (binaryFormMonomialBasis R w j))
  have hfX (r : R) : f (X r) = r := eval₂Hom_X' (Int.castRingHom R) id r
  have hφ (P : homogeneousSubmodule (Fin 2) A w) :
      f (φA P) = φ (mapHomogeneousSubmodule f w P) := by
    have hmap : mapHomogeneousSubmodule f w P = ∑ j : Fin (w + 1),
        f ((binaryFormMonomialBasis A w).repr P j) • binaryFormMonomialBasis R w j := by
      apply (binaryFormMonomialBasis R w).repr.injective
      ext j
      have hrepr : (binaryFormMonomialBasis R w).repr (mapHomogeneousSubmodule f w P) j =
          f ((binaryFormMonomialBasis A w).repr P j) := by
        simp [binaryFormMonomialBasis, homogeneousMonomialBasis_repr_apply,
          MvPolynomial.coeff_map]
      rw [hrepr]
      simp [Finsupp.single_apply]
    rw [hmap, map_sum]
    simp [φA, hfX]
  have hdual (ψA : homogeneousSubmodule (Fin 2) A w →ₗ[A] A)
      (ψ : homogeneousSubmodule (Fin 2) R w →ₗ[R] R)
      (hψ : ∀ P, f (ψA P) = ψ (mapHomogeneousSubmodule f w P)) :
      mapHomogeneousSubmodule f w (binaryFormDual A w ψA) = binaryFormDual R w ψ := by
    rw [binaryFormDual_apply, binaryFormDual_apply]
    simp only [map_sum, map_smulₛₗ, map_mul, map_neg, map_one,
      map_pow, map_natCast, mapHomogeneousSubmodule_binaryFormMonomialBasis, hψ]
  have hcomp (P : homogeneousSubmodule (Fin 2) A w) :
      f ((φA ∘ₗ binaryFormAdjugateRep A w M) P) =
        (φ ∘ₗ binaryFormAdjugateRep R w M) (mapHomogeneousSubmodule f w P) := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, binaryFormAdjugateRep_apply,
      binaryFormAdjugateRep_apply, mapHomogeneousSubmodule_binaryFormRep]
  have h := binaryFormRep_binaryFormDual_of_infinite_domain (R := A) M φA
  have := congrArg (mapHomogeneousSubmodule f w) h
  rw [mapHomogeneousSubmodule_binaryFormRep, hdual φA φ hφ,
    hdual (φA ∘ₗ binaryFormAdjugateRep A w M)
      (φ ∘ₗ binaryFormAdjugateRep R w M) hcomp] at this
  exact this

/-- `D` is injective when the binomial coefficients `w choose j` are not zero divisors, for
instance over a domain of characteristic zero or of characteristic `p > w`. -/
theorem binaryFormDual_injective (h : ∀ j ≤ w, IsRegular (w.choose j : R)) :
    Function.Injective (binaryFormDual R w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have hc : ∀ j : Fin (w + 1),
      (-1 : R) ^ (w - j) * (w.choose j : R) * φ (binaryFormMonomialBasis R w (Fin.rev j)) = 0 := by
    intro j
    have := congrArg (fun P ↦ (binaryFormMonomialBasis R w).repr P j) hφ
    simpa [binaryFormDual_apply, Finsupp.single_apply] using this
  refine (binaryFormMonomialBasis R w).ext fun j ↦ ?_
  have hj := hc (Fin.rev j)
  rw [Fin.rev_rev, mul_assoc, ((isUnit_neg_one (α := R)).pow _).mul_right_eq_zero] at hj
  exact ((h _ (Nat.lt_succ_iff.mp j.rev.2)).left.mul_left_eq_zero_iff).1 hj

end TauCeti
