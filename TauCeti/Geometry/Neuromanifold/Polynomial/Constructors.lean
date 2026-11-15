/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import TauCeti.Algebra.MvPolynomial.Polynomial
public import TauCeti.Geometry.Neuromanifold.Activation
public import TauCeti.Geometry.Neuromanifold.Convolution.Basic
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

On collected input polynomials, variables give input variables or constant parameter-variable
coefficients (`inputPolynomial_X_inr`, `inputPolynomial_X_inl`), reparametrization substitutes
into the parameter coefficients without increasing the uniform input-degree bound
(`inputPolynomial_polynomialReparametrize`, `polynomialInputDegree_polynomialReparametrize_le`,
including parameter renaming `inputPolynomial_rename_sumMap`), coordinatewise polynomial
postcomposition applies the polynomial to each collected input polynomial
(`inputPolynomial_aeval`), and binary composition substitutes the collected input polynomials of
`P` for the inputs of `Q` and multiplies uniform input-degree bounds
(`inputPolynomial_polynomialCompose`, `polynomialInputDegree_polynomialCompose_le`).

The concrete layers are polynomial models: `polynomialDense` and `polynomialLinear` realize
the dense affine and linear layers after the identifications `denseParameterEquiv` and
`linearParameterEquiv` of their parameter index types with matrices and bias vectors;
`polynomialConvolution` and `polynomialAffineConvolution` realize valid convolution;
`polynomialActivation p` realizes the coordinatewise activation by the polynomial `p`.
Substituting zero for the bias variables reduces `polynomialDense` to `polynomialLinear` and
`polynomialAffineConvolution` to `polynomialConvolution`.
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

/-- Input variables have the corresponding input variables as their collected input polynomials. -/
@[simp] theorem inputPolynomial_X_inr (e : J → I) (j : J) :
    inputPolynomial (fun k => X (Sum.inr (e k)) : J → MvPolynomial (W ⊕ I) K) j = X (e j) := by
  simp [inputPolynomial_def]

/-- Parameter variables realize the input-independent map selecting those parameters. -/
@[simp] theorem polynomialRealization_X_inl (e : J → W) :
    polynomialRealization (fun j => X (Sum.inl (e j)) : J → MvPolynomial (W ⊕ I) K) =
      fun w _ => w ∘ e := by
  funext w x j
  simp

/-- Parameter variables give constant collected input polynomials with those parameter variables as
coefficients. -/
@[simp] theorem inputPolynomial_X_inl (e : J → W) (j : J) :
    inputPolynomial (fun k => X (Sum.inl (e k)) : J → MvPolynomial (W ⊕ I) K) j =
      C (X (e j)) := by
  simp [inputPolynomial_def]

/-- Pairing two polynomial models with the same parameters and inputs realizes the pair of
their outputs, indexed by the sum of the output types. -/
@[simp] theorem polynomialRealization_sumElim (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (W ⊕ I) K) :
    polynomialRealization (Sum.elim P Q) =
      fun w x => Sum.elim (polynomialRealization P w x) (polynomialRealization Q w x) := by
  funext w x j
  cases j <;> simp

/-- Collecting the input polynomials of a paired model pairs the collected input polynomials of the
two components. -/
@[simp] theorem inputPolynomial_sumElim (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (W ⊕ I) K) :
    inputPolynomial (Sum.elim P Q) = Sum.elim (inputPolynomial P) (inputPolynomial Q) := by
  funext j
  cases j <;> simp [inputPolynomial_def]

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

/-- Substituting polynomials `R` for the parameters substitutes them into the parameter
coefficients of each collected input polynomial. -/
@[simp] theorem inputPolynomial_polynomialReparametrize (R : W → MvPolynomial W' K)
    (P : J → MvPolynomial (W ⊕ I) K) (j : J) :
    inputPolynomial (polynomialReparametrize R P) j =
      map (bind₁ R : MvPolynomial W K →ₐ[K] MvPolynomial W' K) (inputPolynomial P j) := by
  have hinr (q : MvPolynomial W' K) : sumAlgEquiv K I W' (rename Sum.inr q) = C q := by
    simpa using AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K I W') q
  simp only [inputPolynomial_def, polynomialReparametrize_apply]
  induction P j using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp, hinr, Function.comp_def]

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

/-- Reparametrizing a polynomial model cannot increase its uniform input-degree bound. -/
theorem polynomialInputDegree_polynomialReparametrize_le [Fintype J] (R : W → MvPolynomial W' K)
    (P : J → MvPolynomial (W ⊕ I) K) :
    polynomialInputDegree (polynomialReparametrize R P) ≤ polynomialInputDegree P :=
  polynomialInputDegree_le_of_inputPolynomial_eq_map (inputPolynomial_polynomialReparametrize R P)

/-- Renaming the parameter variables is reparametrization by the renamed variables. -/
@[simp] theorem polynomialReparametrize_X (f : W → W') (P : J → MvPolynomial (W ⊕ I) K) :
    polynomialReparametrize (fun w => X (f w)) P = fun j => rename (Sum.map f id) (P j) := by
  funext j
  rw [polynomialReparametrize_apply, rename_eq_aeval (Sum.map f id), aeval_eq_bind₁]
  refine congrArg (fun F => bind₁ F (P j)) (funext fun i => ?_)
  cases i <;> simp

/-- Renaming the parameter variables maps the parameter-polynomial coefficients of each collected
input polynomial. -/
@[simp] theorem inputPolynomial_rename_sumMap (f : W → W') (P : J → MvPolynomial (W ⊕ I) K)
    (j : J) :
    inputPolynomial (fun k => rename (Sum.map f id) (P k)) j =
      map (rename f : MvPolynomial W K →ₐ[K] MvPolynomial W' K) (inputPolynomial P j) := by
  have hf : (bind₁ (fun w => X (f w)) : MvPolynomial W K →ₐ[K] MvPolynomial W' K) = rename f :=
    (aeval_eq_bind₁ _).symm.trans (rename_eq_aeval f).symm
  rw [← polynomialReparametrize_X, inputPolynomial_polynomialReparametrize, hf]

/-- Renaming the parameter variables precomposes the realization map with that renaming. -/
@[simp] theorem polynomialRealization_rename_sumMap (f : W → W')
    (P : J → MvPolynomial (W ⊕ I) K) :
    polynomialRealization (fun j => rename (Sum.map f id) (P j)) =
      fun w' => polynomialRealization P (w' ∘ f) := by
  simp [← polynomialReparametrize_X, Function.comp_def]

/-- Renaming the parameter variables cannot increase the uniform input-degree bound. -/
theorem polynomialInputDegree_rename_sumMap_le [Fintype J] (f : W → W')
    (P : J → MvPolynomial (W ⊕ I) K) :
    polynomialInputDegree (fun j => rename (Sum.map f id) (P j)) ≤ polynomialInputDegree P := by
  rw [← polynomialReparametrize_X]
  exact polynomialInputDegree_polynomialReparametrize_le _ P

/-- Keeping variables `X ⟨i, a⟩` on the left summand and substituting `0` on the right summand of
an indexed sum `(i : ι) × (V i ⊕ B i)` applies `Sum.elim X 0` at each index `i` and tags the kept
variables with `Sigma.mk i`. -/
theorem sumElim_X_zero_eq_rename {ι : Type*} {V B : ι → Type*} :
    ((fun ⟨i, j⟩ => Sum.elim (fun a => X ⟨i, a⟩) (fun _ => 0) j) :
        ((k : ι) × (V k ⊕ B k)) → MvPolynomial ((k : ι) × V k) K) =
      fun p => rename (Sigma.mk p.1) (Sum.elim X (0 : B p.1 → MvPolynomial (V p.1) K) p.2) := by
  funext ⟨i, j⟩
  cases j <;> simp

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

/-- Collecting the inputs of a composite model substitutes the collected input polynomials of
`P`, with parameters renamed into the composite parameters, for the inputs of `Q`. -/
theorem inputPolynomial_polynomialCompose (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (V ⊕ J) K) (l : L) :
    inputPolynomial (polynomialCompose P Q) l =
      eval₂ (C.comp (rename Sum.inr : MvPolynomial V K →ₐ[K] MvPolynomial (W ⊕ V) K))
        (fun j => map (rename Sum.inl : MvPolynomial W K →ₐ[K] MvPolynomial (W ⊕ V) K)
          (inputPolynomial P j))
        (inputPolynomial Q l) := by
  have hP (j : J) :
      sumAlgEquiv K I (W ⊕ V) (rename (Sum.swap ∘ Sum.map Sum.inl id) (P j)) =
        map (rename Sum.inl : MvPolynomial W K →ₐ[K] MvPolynomial (W ⊕ V) K)
          (inputPolynomial P j) := by
    rw [← rename_rename, ← inputPolynomial_def (fun k => rename (Sum.map Sum.inl id) (P k)) j]
    exact inputPolynomial_rename_sumMap Sum.inl P j
  simp only [inputPolynomial_def, polynomialCompose_apply]
  induction Q l using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp, hP, ← inputPolynomial_def]

/-- The uniform input-degree bound of `polynomialCompose P Q` is at most the product of the uniform
input-degree bounds of `P` and `Q`. -/
theorem polynomialInputDegree_polynomialCompose_le [Fintype J] [Fintype L]
    (P : J → MvPolynomial (W ⊕ I) K) (Q : L → MvPolynomial (V ⊕ J) K) :
    polynomialInputDegree (polynomialCompose P Q) ≤
      polynomialInputDegree P * polynomialInputDegree Q := by
  refine (polynomialInputDegree_le_iff _).2 fun l => ?_
  rw [inputPolynomial_polynomialCompose, eval₂_eq]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [RingHom.comp_apply, RingHom.coe_coe, totalDegree_C, zero_add]
  calc
    _ ≤ ∑ j ∈ s.support, s j * polynomialInputDegree P :=
        (totalDegree_finsetProd _ _).trans <| Finset.sum_le_sum fun j _ =>
          (totalDegree_pow _ _).trans
            (Nat.mul_le_mul_left _ (totalDegree_map_inputPolynomial_le P _ j))
    _ = polynomialInputDegree P * (s.sum fun _ e => e) := by
        rw [Finsupp.sum, ← Finset.sum_mul, mul_comm]
    _ ≤ polynomialInputDegree P * polynomialInputDegree Q :=
        Nat.mul_le_mul_left _ ((le_totalDegree hs).trans (totalDegree_inputPolynomial_le Q l))

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

/-- The collected input polynomials of the linear layer are linear forms whose coefficients are
the weight variables. -/
@[simp] theorem inputPolynomial_polynomialLinear (o : ο) :
    inputPolynomial (polynomialLinear : ο → MvPolynomial (ο × ι ⊕ ι) K) o =
      ∑ i, C (X (o, i)) * X i := by
  simp [inputPolynomial_def, polynomialLinear_apply]

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

/-- The collected input polynomials of the dense affine layer are affine forms whose coefficients
are the weight and bias variables. -/
@[simp] theorem inputPolynomial_polynomialDense (o : ο) :
    inputPolynomial (polynomialDense : ο → MvPolynomial ((ο × ι ⊕ ο) ⊕ ι) K) o =
      ∑ i, C (X (Sum.inl (o, i))) * X i + C (X (Sum.inr o)) := by
  simp [inputPolynomial_def, polynomialDense_apply]

/-- Substituting zero for the bias variables in the polynomial dense layer gives the polynomial
linear layer. -/
@[simp] theorem polynomialReparametrize_sumElim_X_zero_polynomialDense :
    polynomialReparametrize (Sum.elim X (0 : ο → MvPolynomial (ο × ι) K))
      (polynomialDense : ο → MvPolynomial ((ο × ι ⊕ ο) ⊕ ι) K) = polynomialLinear := by
  funext o
  simp [polynomialReparametrize_apply, polynomialDense_apply, polynomialLinear_apply]

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

/-- Applying a one-variable polynomial coordinatewise to the outputs of a polynomial model applies
it to each collected input polynomial. -/
@[simp] theorem inputPolynomial_aeval (P : J → MvPolynomial (W ⊕ I) K) (p : Polynomial K)
    (j : J) :
    inputPolynomial (fun k => Polynomial.aeval (P k) p) j =
      Polynomial.aeval (inputPolynomial P j) p := by
  simpa [inputPolynomial_def] using
    (Polynomial.aeval_algHom_apply ((sumAlgEquiv K I W).toAlgHom.comp (rename Sum.swap))
      (P j) p).symm

/-- Applying a one-variable polynomial coordinatewise to the outputs of a polynomial model
evaluates that polynomial on each realized output coordinate. -/
@[simp] theorem polynomialRealization_aeval (P : J → MvPolynomial (W ⊕ I) K) (p : Polynomial K) :
    polynomialRealization (fun j => Polynomial.aeval (P j) p) =
      fun w x j => p.eval (polynomialRealization P w x j) := by
  funext w x j
  simp

/-- Reparametrization commutes with applying a one-variable polynomial coordinatewise to the
outputs. -/
@[simp] theorem polynomialReparametrize_aeval (R : W → MvPolynomial W' K)
    (P : J → MvPolynomial (W ⊕ I) K) (p : Polynomial K) :
    polynomialReparametrize R (fun j => Polynomial.aeval (P j) p) =
      fun j => Polynomial.aeval (polynomialReparametrize R P j) p := by
  funext j
  exact (Polynomial.aeval_algHom_apply (bind₁ _) (P j) p).symm

/-- The coordinatewise activation by a polynomial `p`, as a polynomial model whose
parameters `W` do not occur. -/
def polynomialActivation (p : Polynomial K) : ι → MvPolynomial (W ⊕ ι) K :=
  fun i => Polynomial.aeval (X (Sum.inr i)) p

/-- Output `i` of a polynomial activation is `p` evaluated at the input variable `i`. -/
theorem polynomialActivation_apply (p : Polynomial K) (i : ι) :
    polynomialActivation (W := W) p i = Polynomial.aeval (X (Sum.inr i)) p := (rfl)

/-- Each collected input polynomial of a polynomial activation evaluates the activation polynomial
at the corresponding input variable. -/
@[simp] theorem inputPolynomial_polynomialActivation (p : Polynomial K) (i : ι) :
    inputPolynomial (polynomialActivation (W := W) p) i = Polynomial.aeval (X i) p :=
  (inputPolynomial_aeval (fun j : ι => (X (Sum.inr j) : MvPolynomial (W ⊕ ι) K)) p i).trans
    (congrArg (Polynomial.aeval · p) (inputPolynomial_X_inr id i))

/-- Composing a polynomial model with a polynomial activation applies the activation polynomial to
each output and embeds the parameters of the first model into the composite parameter sum. -/
@[simp] theorem polynomialCompose_polynomialActivation (P : J → MvPolynomial (W ⊕ I) K)
    (p : Polynomial K) :
    polynomialCompose P (polynomialActivation (W := V) p) =
      fun j => rename (Sum.map Sum.inl id) (Polynomial.aeval (P j) p) := by
  funext j
  rw [polynomialCompose_apply, polynomialActivation_apply,
    ← Polynomial.aeval_algHom_apply (bind₁ _),
    ← Polynomial.aeval_algHom_apply (rename (Sum.map Sum.inl id))]
  simp

/-- A polynomial activation realizes the activation layer of its polynomial function, at
every parameter. -/
theorem polynomialRealization_polynomialActivation (p : Polynomial K) (w : W → K) :
    polynomialRealization (polynomialActivation (W := W) (ι := ι) p) w =
      activation (fun t => p.eval t) PUnit.unit := by
  funext x i
  rw [polynomialRealization_apply, activation_apply, polynomialActivation,
    eval_polynomial_aeval, eval_X, Sum.elim_inr]

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

/-- The collected input polynomials of valid convolution are linear forms in the window inputs
whose coefficients are the filter variables. -/
@[simp] theorem inputPolynomial_polynomialConvolution (h : n = s * (m - 1) + k) (i : Fin m) :
    inputPolynomial (polynomialConvolution (K := K) h) i =
      ∑ j, C (X j) * X (convolutionIndex h i j) := by
  simp [inputPolynomial_def, polynomialConvolution_apply]

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

/-- The collected input polynomials of affine valid convolution are affine forms in the window
inputs whose coefficients are the filter variables and the shared bias variable. -/
@[simp] theorem inputPolynomial_polynomialAffineConvolution (h : n = s * (m - 1) + k)
    (i : Fin m) :
    inputPolynomial (polynomialAffineConvolution (K := K) h) i =
      ∑ j, C (X (Sum.inl j)) * X (convolutionIndex h i j) + C (X (Sum.inr ())) := by
  simp [inputPolynomial_def, polynomialAffineConvolution_apply]

/-- Substituting zero for the shared bias variable in the polynomial affine convolution gives the
polynomial valid convolution. -/
@[simp] theorem polynomialReparametrize_sumElim_X_zero_polynomialAffineConvolution
    (h : n = s * (m - 1) + k) :
    polynomialReparametrize (Sum.elim X (0 : Unit → MvPolynomial (Fin k) K))
      (polynomialAffineConvolution (K := K) h) = polynomialConvolution h := by
  funext i
  simp [polynomialReparametrize_apply, polynomialAffineConvolution_apply,
    polynomialConvolution_apply]

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
