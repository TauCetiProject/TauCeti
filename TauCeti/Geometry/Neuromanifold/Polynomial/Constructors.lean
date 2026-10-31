/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import TauCeti.Geometry.Neuromanifold.Activation
public import TauCeti.Geometry.Neuromanifold.Convolution
public import TauCeti.Geometry.Neuromanifold.Dense
public import TauCeti.Geometry.Neuromanifold.Polynomial.Basic

/-!
# Constructors of jointly polynomial models

A tuple `P : J → MvPolynomial (W ⊕ I) K` supplies the realization map
`polynomialRealization P`. This file builds such tuples from smaller pieces and proves that
each construction realizes the expected map, as an equality of realization maps:

* constant tuples realize constant maps, and the variables realize coordinate projections
  of the input or of the parameters;
* `Sum.elim P Q` pairs two models with the same parameters and inputs;
* `polynomialReparametrize R P` substitutes polynomials `R` in new parameters for the old
  parameters, and realizes `P` at the evaluated parameters;
* `polynomialCompose P Q` substitutes the outputs of `P` for the inputs of `Q`, and realizes
  `compose (polynomialRealization P) (polynomialRealization Q)` after splitting the parameters
  with `Equiv.sumArrowEquivProdArrow`.

The concrete layers are polynomial models: `polynomialDense` and `polynomialLinear` realize
the dense affine and linear layers after the identifications `denseParameterEquiv` and
`linearParameterEquiv` of their parameter index types with matrices and bias vectors;
`polynomialConvolution` and `polynomialAffineConvolution` realize valid convolution;
`polynomialActivation p` realizes the coordinatewise activation by the polynomial `p`.
Since the identifications are equivalences, the polynomial and the original layers have the
same realized functions. The identity and monomial activations are the input variables and
their powers. Composing these layers with `polynomialCompose` presents a layer-by-layer network
with polynomial activations as a single jointly polynomial model.

The jointly polynomial setting follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. Substitution is Mathlib's
`MvPolynomial.bind₁`, evaluated with `MvPolynomial.aeval_bind₁`.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K W W' V I J L : Type*}

variable [CommSemiring K]

section Basic

/-- A tuple of constant polynomials realizes the constant map with those values. -/
@[simp] theorem polynomialRealization_C (a : J → K) :
    polynomialRealization (fun j => C (a j) : J → MvPolynomial (W ⊕ I) K) = fun _ _ => a := by
  funext w x j
  simp

/-- Input variables realize the coordinate projection of the input. -/
@[simp] theorem polynomialRealization_X_inr (e : J → I) :
    polynomialRealization (fun j => X (Sum.inr (e j)) : J → MvPolynomial (W ⊕ I) K) =
      fun _ x => x ∘ e := by
  funext w x j
  simp

/-- Parameter variables realize the input-independent map selecting those parameters. -/
@[simp] theorem polynomialRealization_X_inl (e : J → W) :
    polynomialRealization (fun j => X (Sum.inl (e j)) : J → MvPolynomial (W ⊕ I) K) =
      fun w _ => w ∘ e := by
  funext w x j
  simp

/-- Pairing two polynomial models with the same parameters and inputs realizes the pair of
their outputs, indexed by the sum of the output types. -/
@[simp] theorem polynomialRealization_sumElim (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (W ⊕ I) K) :
    polynomialRealization (Sum.elim P Q) =
      fun w x => Sum.elim (polynomialRealization P w x) (polynomialRealization Q w x) := by
  funext w x j
  cases j <;> simp

end Basic

section Substitution

/-- Substitute a polynomial `R i` in the new parameters `W'` for each old parameter `i`,
leaving the input variables unchanged. -/
def polynomialReparametrize (R : W → MvPolynomial W' K) (P : J → MvPolynomial (W ⊕ I) K) :
    J → MvPolynomial (W' ⊕ I) K :=
  fun j => bind₁ (Sum.elim (fun i => rename Sum.inl (R i)) (fun a => X (Sum.inr a))) (P j)

/-- Each output of a reparametrized model is the substitution into the original output. -/
theorem polynomialReparametrize_apply (R : W → MvPolynomial W' K)
    (P : J → MvPolynomial (W ⊕ I) K) (j : J) :
    polynomialReparametrize R P j =
      bind₁ (Sum.elim (fun i => rename Sum.inl (R i)) (fun a => X (Sum.inr a))) (P j) := (rfl)

/-- A reparametrized polynomial model realizes the original model at the evaluated
polynomial parameters. -/
@[simp] theorem polynomialRealization_polynomialReparametrize (R : W → MvPolynomial W' K)
    (P : J → MvPolynomial (W ⊕ I) K) :
    polynomialRealization (polynomialReparametrize R P) =
      fun w' => polynomialRealization P fun i => eval w' (R i) := by
  funext w' x j
  simp only [polynomialRealization_apply, polynomialReparametrize, ← aeval_eq_eval, aeval_bind₁]
  refine congrArg (fun F => aeval F (P j)) (funext fun i => ?_)
  cases i <;> simp [eval_rename, Function.comp_def]

/-- Substitute the outputs of `P` for the input variables of `Q`. The parameters of the
composite are those of `P` followed by those of `Q`. -/
def polynomialCompose (P : J → MvPolynomial (W ⊕ I) K) (Q : L → MvPolynomial (V ⊕ J) K) :
    L → MvPolynomial ((W ⊕ V) ⊕ I) K :=
  fun l => bind₁ (Sum.elim (fun v => X (Sum.inl (Sum.inr v)))
    (fun j => rename (Sum.map Sum.inl id) (P j))) (Q l)

/-- Each output of a composite model is the substitution of the outputs of `P` into the
corresponding output of `Q`. -/
theorem polynomialCompose_apply (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (V ⊕ J) K) (l : L) :
    polynomialCompose P Q l =
      bind₁ (Sum.elim (fun v => X (Sum.inl (Sum.inr v)))
        (fun j => rename (Sum.map Sum.inl id) (P j))) (Q l) := (rfl)

/-- Composition by polynomial substitution realizes the composite of the two realization
maps, after splitting the parameters into those of `P` and those of `Q`. -/
@[simp] theorem polynomialRealization_polynomialCompose (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (V ⊕ J) K) :
    polynomialRealization (polynomialCompose P Q) =
      compose (polynomialRealization P) (polynomialRealization Q) ∘
        Equiv.sumArrowEquivProdArrow W V K := by
  funext p x l
  simp only [polynomialRealization_apply, polynomialCompose, ← aeval_eq_eval, aeval_bind₁,
    Function.comp_apply, compose_apply_apply]
  refine congrArg (fun F => aeval F (Q l)) (funext fun i => ?_)
  rcases i with v | j
  · simp
  · simp only [Sum.elim_inr, aeval_eq_eval, eval_rename, polynomialRealization_apply]
    refine congrArg (fun F => eval F (P j)) (funext fun i => ?_)
    cases i <;> simp

/-- Composition by polynomial substitution realizes the same functions as the composite of
the two realization maps. -/
theorem realizedFunctions_polynomialCompose (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (V ⊕ J) K) :
    realizedFunctions (polynomialRealization (polynomialCompose P Q)) =
      realizedFunctions (compose (polynomialRealization P) (polynomialRealization Q)) := by
  rw [polynomialRealization_polynomialCompose, realizedFunctions_def, realizedFunctions_def,
    (Equiv.sumArrowEquivProdArrow W V K).surjective.range_comp]

end Substitution

section Layers

variable {ι ο : Type*} [Fintype ι]

/-- The linear layer as a polynomial model: output `o` is `∑ i, A o i * x i`, with one
parameter variable for each matrix entry. -/
def polynomialLinear : ο → MvPolynomial (ο × ι ⊕ ι) K :=
  fun o => ∑ i, X (Sum.inl (o, i)) * X (Sum.inr i)

/-- Output `o` of the polynomial linear layer. -/
theorem polynomialLinear_apply (o : ο) :
    (polynomialLinear o : MvPolynomial (ο × ι ⊕ ι) K) =
      ∑ i, X (Sum.inl (o, i)) * X (Sum.inr i) := (rfl)

/-- The polynomial linear layer realizes matrix evaluation of its weight matrix. -/
@[simp] theorem polynomialRealization_polynomialLinear :
    polynomialRealization (polynomialLinear : ο → MvPolynomial (ο × ι ⊕ ι) K) =
      Matrix.mulVec ∘ linearParameterEquiv K ο ι := by
  funext p x o
  simp [polynomialLinear, Matrix.mulVec, dotProduct]

/-- The polynomial linear layer realizes the same functions as matrix evaluation. -/
theorem realizedFunctions_polynomialLinear :
    realizedFunctions (polynomialRealization (polynomialLinear : ο → MvPolynomial (ο × ι ⊕ ι) K)) =
      realizedFunctions (Matrix.mulVec : Matrix ο ι K → (ι → K) → ο → K) := by
  rw [polynomialRealization_polynomialLinear, realizedFunctions_def, realizedFunctions_def,
    (linearParameterEquiv K ο ι).surjective.range_comp]

/-- The dense affine layer as a polynomial model: output `o` is `∑ i, A o i * x i + b o`,
with one parameter variable for each matrix entry and each bias coordinate. -/
def polynomialDense : ο → MvPolynomial ((ο × ι ⊕ ο) ⊕ ι) K :=
  fun o => ∑ i, X (Sum.inl (Sum.inl (o, i))) * X (Sum.inr i) + X (Sum.inl (Sum.inr o))

/-- Output `o` of the polynomial dense layer. -/
theorem polynomialDense_apply (o : ο) :
    (polynomialDense o : MvPolynomial ((ο × ι ⊕ ο) ⊕ ι) K) =
      ∑ i, X (Sum.inl (Sum.inl (o, i))) * X (Sum.inr i) + X (Sum.inl (Sum.inr o)) := (rfl)

/-- The polynomial dense layer realizes the dense affine layer. -/
@[simp] theorem polynomialRealization_polynomialDense :
    polynomialRealization (polynomialDense : ο → MvPolynomial ((ο × ι ⊕ ο) ⊕ ι) K) =
      dense ∘ denseParameterEquiv K ο ι := by
  funext p x o
  simp [polynomialDense, Matrix.mulVec, dotProduct]

/-- The polynomial dense layer realizes the same functions as the dense affine layer. -/
theorem realizedFunctions_polynomialDense :
    realizedFunctions
        (polynomialRealization (polynomialDense : ο → MvPolynomial ((ο × ι ⊕ ο) ⊕ ι) K)) =
      realizedFunctions (dense : Matrix ο ι K × (ο → K) → (ι → K) → ο → K) := by
  rw [polynomialRealization_polynomialDense, realizedFunctions_def, realizedFunctions_def,
    (denseParameterEquiv K ο ι).surjective.range_comp]

end Layers

section Activation

variable {ι : Type*}

/-- The coordinatewise activation by a polynomial `p`, as a polynomial model whose
parameters `W` do not occur. -/
def polynomialActivation (p : Polynomial K) : ι → MvPolynomial (W ⊕ ι) K :=
  fun i => Polynomial.aeval (X (Sum.inr i)) p

/-- Output `i` of a polynomial activation is `p` evaluated at the input variable `i`. -/
theorem polynomialActivation_apply (p : Polynomial K) (i : ι) :
    polynomialActivation (W := W) p i = Polynomial.aeval (X (Sum.inr i)) p := (rfl)

/-- A polynomial activation realizes the activation layer of its polynomial function, at
every parameter. -/
theorem polynomialRealization_polynomialActivation (p : Polynomial K) (w : W → K) :
    polynomialRealization (polynomialActivation (W := W) (ι := ι) p) w =
      activation (fun t => p.eval t) PUnit.unit := by
  funext x i
  rw [polynomialRealization_apply, activation_apply, polynomialActivation]
  have h := Polynomial.aeval_algHom_apply (aeval (Sum.elim w x)) (X (Sum.inr i)) p
  rw [aeval_X, Polynomial.coe_aeval_eq_eval, aeval_eq_eval] at h
  exact h.symm

/-- The identity activation is the input variable. -/
@[simp] theorem polynomialActivation_X :
    polynomialActivation (W := W) (ι := ι) (Polynomial.X : Polynomial K) =
      fun i => X (Sum.inr i) := by
  funext i
  simp [polynomialActivation]

/-- The monomial activation `t ↦ t ^ r` is the `r`th power of the input variable. -/
@[simp] theorem polynomialActivation_X_pow (r : ℕ) :
    polynomialActivation (W := W) (ι := ι) (Polynomial.X ^ r : Polynomial K) =
      fun i => X (Sum.inr i) ^ r := by
  funext i
  simp [polynomialActivation]

end Activation

section Convolution

variable {n k s m : ℕ}

/-- Valid convolution as a polynomial model in the filter weights and the input. -/
def polynomialConvolution (h : n = s * (m - 1) + k) : Fin m → MvPolynomial (Fin k ⊕ Fin n) K :=
  fun i => ∑ j, X (Sum.inl j) * X (Sum.inr (convolutionIndex h i j))

/-- Output `i` of the polynomial convolution. -/
theorem polynomialConvolution_apply (h : n = s * (m - 1) + k) (i : Fin m) :
    (polynomialConvolution h i : MvPolynomial (Fin k ⊕ Fin n) K) =
      ∑ j, X (Sum.inl j) * X (Sum.inr (convolutionIndex h i j)) := (rfl)

/-- The polynomial convolution realizes valid convolution. -/
@[simp] theorem polynomialRealization_polynomialConvolution (h : n = s * (m - 1) + k) :
    polynomialRealization (polynomialConvolution (K := K) h) = convolution h := by
  funext w x i
  simp [polynomialConvolution]

/-- Valid convolution with a shared bias as a polynomial model in the filter weights, the
bias and the input. -/
def polynomialAffineConvolution (h : n = s * (m - 1) + k) :
    Fin m → MvPolynomial ((Fin k ⊕ Unit) ⊕ Fin n) K :=
  fun i => ∑ j, X (Sum.inl (Sum.inl j)) * X (Sum.inr (convolutionIndex h i j)) +
    X (Sum.inl (Sum.inr ()))

/-- Output `i` of the polynomial affine convolution. -/
theorem polynomialAffineConvolution_apply (h : n = s * (m - 1) + k) (i : Fin m) :
    (polynomialAffineConvolution h i : MvPolynomial ((Fin k ⊕ Unit) ⊕ Fin n) K) =
      ∑ j, X (Sum.inl (Sum.inl j)) * X (Sum.inr (convolutionIndex h i j)) +
        X (Sum.inl (Sum.inr ())) := (rfl)

/-- The polynomial affine convolution realizes the affine convolution. -/
@[simp] theorem polynomialRealization_polynomialAffineConvolution (h : n = s * (m - 1) + k) :
    polynomialRealization (polynomialAffineConvolution (K := K) h) =
      affineConvolution h ∘ affineConvolutionParameterEquiv K k := by
  funext p x i
  simp [polynomialAffineConvolution]

/-- The polynomial affine convolution realizes the same functions as the affine convolution. -/
theorem realizedFunctions_polynomialAffineConvolution (h : n = s * (m - 1) + k) :
    realizedFunctions (polynomialRealization (polynomialAffineConvolution (K := K) h)) =
      realizedFunctions (affineConvolution (K := K) h) := by
  rw [polynomialRealization_polynomialAffineConvolution, realizedFunctions_def,
    realizedFunctions_def, (affineConvolutionParameterEquiv K k).surjective.range_comp]

end Convolution

end TauCeti.Neuromanifold
