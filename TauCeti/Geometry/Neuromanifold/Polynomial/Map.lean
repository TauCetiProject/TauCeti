/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Basic.Complex.Basic
public import TauCeti.Geometry.Neuromanifold.Polynomial.Constructors

/-!
# Transporting polynomial models along ring homomorphisms

A jointly polynomial model `P : J → MvPolynomial (W ⊕ I) K` over `K` gives a model
`map φ ∘ P` over `L` for every ring homomorphism `φ : K →+* L`, by mapping the coefficients of
each output polynomial. This file shows that the transported model is compatible with all of
the structure attached to `P`:

* `polynomialRealization_map`: evaluating the transported model at mapped parameters and
  inputs gives the mapped outputs;
* `inputPolynomial_map`, `map_eval_inputPolynomial_map` and `polynomialCoefficientMap_map_coe`:
  collecting input monomials commutes with the transport, and the specialized coefficients of
  the transported model at mapped parameters are the mapped specialized coefficients;
* `polynomialInputDegree_map_le` and `polynomialInputDegree_map`: the uniform input-degree
  bound does not increase, and is unchanged when `φ` is injective;
* `map_polynomialCompose`, `map_polynomialReparametrize`, `map_polynomialDense`, … : the
  constructors of polynomial models over `K` are transported to the same constructors over `L`,
  with polynomial activations transported by `Polynomial.map`.

For an injective `φ`, two parameters over `K` realizing the same function over `L` realize the
same function over `K` (`polynomialRealization_eq_of_map_eq`). Over an infinite integral domain
the converse holds as well (`polynomialRealization_map_eq_iff`), since a function then determines
its coefficient polynomials. Thus the fibre of the model over `K` is the preimage of the fibre of
the transported model (`preimage_fiber_polynomialRealization_map`). This does not identify the
two fibres, nor the two neuromanifolds: the transported model has parameters and inputs outside
the image of `K`. The case of `Complex.ofRealHom : ℝ →+* ℂ` is spelled out in
`polynomialRealization_map_ofReal` and `polynomialRealization_map_ofReal_eq_iff`.

The jointly polynomial setting and its real and complex instantiations follow
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1. Coefficient mapping is
Mathlib's `MvPolynomial.map`, and the comparison of functions with coefficients over an infinite
domain is Mathlib's `MvPolynomial.funext`.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K L W W' V I J M : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] (φ : K →+* L)

/-- Evaluating a transported polynomial model at mapped parameters and a mapped input gives the
mapped outputs of the original model. -/
@[simp] theorem polynomialRealization_map (P : J → MvPolynomial (W ⊕ I) K) (w : W → K)
    (x : I → K) :
    polynomialRealization (map φ ∘ P) (φ ∘ w) (φ ∘ x) = φ ∘ polynomialRealization P w x := by
  funext j
  simpa [eval_map, ← Sum.comp_elim] using
    (eval₂_comp_left φ (RingHom.id K) (Sum.elim w x) (P j)).symm

/-- Collecting the input variables of a transported model maps the parameter-polynomial
coefficients. -/
@[simp] theorem inputPolynomial_map (P : J → MvPolynomial (W ⊕ I) K) (j : J) :
    inputPolynomial (map φ ∘ P) j = map (map φ) (inputPolynomial P j) := by
  rw [inputPolynomial_def, inputPolynomial_def, Function.comp_apply, ← map_rename,
    sumAlgEquiv_map]

/-- Specializing the coefficients of a transported model at mapped parameters gives the mapped
specialized coefficients of the original model. -/
theorem map_eval_inputPolynomial_map (P : J → MvPolynomial (W ⊕ I) K) (w : W → K) (j : J) :
    map (eval (φ ∘ w)) (inputPolynomial (map φ ∘ P) j) =
      map φ (map (eval w) (inputPolynomial P j)) := by
  rw [inputPolynomial_map, map_map, map_map]
  refine congrArg (fun g => map g _) (ringHom_ext (fun a => ?_) (fun i => ?_)) <;> simp

/-- Transporting a model cannot increase its uniform input-degree bound. -/
theorem polynomialInputDegree_map_le [Fintype J] (P : J → MvPolynomial (W ⊕ I) K) :
    polynomialInputDegree (map φ ∘ P) ≤ polynomialInputDegree P := by
  refine (polynomialInputDegree_le_iff _).2 fun j => ?_
  rw [inputPolynomial_map]
  exact (Finset.sup_mono (support_map_subset _ _)).trans (totalDegree_inputPolynomial_le P j)

/-- Transport along an injective ring homomorphism preserves the uniform input-degree bound. -/
theorem polynomialInputDegree_map [Fintype J] {φ : K →+* L} (hφ : Function.Injective φ)
    (P : J → MvPolynomial (W ⊕ I) K) :
    polynomialInputDegree (map φ ∘ P) = polynomialInputDegree P := by
  refine le_antisymm (polynomialInputDegree_map_le φ P)
    ((polynomialInputDegree_le_iff _).2 fun j => ?_)
  have h := totalDegree_inputPolynomial_le (map φ ∘ P) j
  rwa [inputPolynomial_map, totalDegree, support_map_of_injective _ (map_injective φ hφ)] at h

/-- The coefficient presentation of a transported model at mapped parameters is the mapped
coefficient presentation of the original model, after forgetting the degree bounds. -/
theorem polynomialCoefficientMap_map_coe [Fintype J] (P : J → MvPolynomial (W ⊕ I) K)
    (w : W → K) (j : J) :
    (polynomialCoefficientMap (map φ ∘ P) (φ ∘ w) j : MvPolynomial I L) =
      map φ (polynomialCoefficientMap P w j : MvPolynomial I K) := by
  rw [polynomialCoefficientMap_coe, polynomialCoefficientMap_coe, map_eval_inputPolynomial_map]

/-- If mapped parameters realize the same function after transport along an injective ring
homomorphism, then the original parameters realize the same function. -/
theorem polynomialRealization_eq_of_map_eq {φ : K →+* L} (hφ : Function.Injective φ)
    {P : J → MvPolynomial (W ⊕ I) K} {w v : W → K}
    (h : polynomialRealization (map φ ∘ P) (φ ∘ w) = polynomialRealization (map φ ∘ P) (φ ∘ v)) :
    polynomialRealization P w = polynomialRealization P v := by
  funext x j
  apply hφ
  have hx := congrFun (congrFun h (φ ∘ x)) j
  simpa only [polynomialRealization_map, Function.comp_apply] using hx

/-! ### Transporting the constructors -/

/-- Transporting a reparametrized model reparametrizes the transported model by the transported
substitution. -/
@[simp] theorem map_polynomialReparametrize (R : W → MvPolynomial W' K)
    (P : J → MvPolynomial (W ⊕ I) K) (j : J) :
    map φ (polynomialReparametrize R P j) =
      polynomialReparametrize (map φ ∘ R) (map φ ∘ P) j := by
  simp only [polynomialReparametrize_apply, map_bind₁, Function.comp_apply]
  refine congrArg (fun F => bind₁ F _) (funext fun i => ?_)
  cases i <;> simp [map_rename]

/-- Transporting a composite model composes the transported models. -/
@[simp] theorem map_polynomialCompose (P : J → MvPolynomial (W ⊕ I) K)
    (Q : M → MvPolynomial (V ⊕ J) K) (l : M) :
    map φ (polynomialCompose P Q l) = polynomialCompose (map φ ∘ P) (map φ ∘ Q) l := by
  simp only [polynomialCompose_apply, map_bind₁, Function.comp_apply]
  refine congrArg (fun F => bind₁ F _) (funext fun i => ?_)
  cases i <;> simp [map_rename]

section Layers

variable {ι ο : Type*} [Fintype ι]

/-- The polynomial linear layer over `K` is transported to the polynomial linear layer
over `L`. -/
@[simp] theorem map_polynomialLinear (o : ο) :
    map φ (polynomialLinear o : MvPolynomial (ο × ι ⊕ ι) K) = polynomialLinear o := by
  simp [polynomialLinear_apply]

/-- The polynomial dense layer over `K` is transported to the polynomial dense layer
over `L`. -/
@[simp] theorem map_polynomialDense (o : ο) :
    map φ (polynomialDense o : MvPolynomial ((ο × ι ⊕ ο) ⊕ ι) K) = polynomialDense o := by
  simp [polynomialDense_apply]

end Layers

/-- A polynomial activation is transported to the activation by the mapped polynomial. -/
@[simp] theorem map_polynomialActivation {ι : Type*} (p : Polynomial K) (i : ι) :
    map φ (polynomialActivation (W := W) p i) = polynomialActivation (p.map φ) i := by
  rw [polynomialActivation_apply, polynomialActivation_apply,
    Polynomial.map_aeval_eq_aeval_map (map_comp_C φ).symm, map_X]

section Convolution

variable {n k s m : ℕ}

/-- The polynomial convolution over `K` is transported to the polynomial convolution
over `L`. -/
@[simp] theorem map_polynomialConvolution (h : n = s * (m - 1) + k) (i : Fin m) :
    map φ (polynomialConvolution h i : MvPolynomial (Fin k ⊕ Fin n) K) =
      polynomialConvolution h i := by
  simp [polynomialConvolution_apply]

/-- The polynomial affine convolution over `K` is transported to the polynomial affine
convolution over `L`. -/
@[simp] theorem map_polynomialAffineConvolution (h : n = s * (m - 1) + k) (i : Fin m) :
    map φ (polynomialAffineConvolution h i : MvPolynomial ((Fin k ⊕ Unit) ⊕ Fin n) K) =
      polynomialAffineConvolution h i := by
  simp [polynomialAffineConvolution_apply]

end Convolution

end CommSemiring

/-! ### Parameter fibres over an infinite domain -/

section Fibres

variable [CommRing K] [IsDomain K] [Infinite K] [CommRing L] [IsDomain L]

/-- Over an infinite integral domain, a polynomial model realizes the same function at two
parameters exactly when it has the same specialized coefficients at both. -/
private theorem polynomialRealization_eq_iff (P : J → MvPolynomial (W ⊕ I) K) (w v : W → K) :
    polynomialRealization P w = polynomialRealization P v ↔
      ∀ j, map (eval w) (inputPolynomial P j) = map (eval v) (inputPolynomial P j) := by
  refine ⟨fun h j => MvPolynomial.funext fun x => ?_, fun h => funext fun x => funext fun j => ?_⟩
  · simpa [eval_map] using congrFun (congrFun h x) j
  · simpa [eval_map] using congrArg (eval x) (h j)

/-- Over an infinite integral domain and along an injective ring homomorphism, two parameters
realize the same function exactly when their images realize the same function for the
transported model. -/
theorem polynomialRealization_map_eq_iff {φ : K →+* L} (hφ : Function.Injective φ)
    (P : J → MvPolynomial (W ⊕ I) K) (w v : W → K) :
    polynomialRealization (map φ ∘ P) (φ ∘ w) = polynomialRealization (map φ ∘ P) (φ ∘ v) ↔
      polynomialRealization P w = polynomialRealization P v := by
  have : Infinite L := Infinite.of_injective φ hφ
  simp only [polynomialRealization_eq_iff, map_eval_inputPolynomial_map,
    (map_injective φ hφ).eq_iff]

/-- Over an infinite integral domain and along an injective ring homomorphism, the fibre of a
polynomial model through `w` consists of the parameters whose images lie in the fibre of the
transported model through the image of `w`. -/
theorem preimage_fiber_polynomialRealization_map {φ : K →+* L} (hφ : Function.Injective φ)
    (P : J → MvPolynomial (W ⊕ I) K) (w : W → K) :
    (φ ∘ ·) ⁻¹' fiber (polynomialRealization (map φ ∘ P))
        (polynomialRealization (map φ ∘ P) (φ ∘ w)) =
      fiber (polynomialRealization P) (polynomialRealization P w) := by
  ext v
  simp only [Set.mem_preimage, mem_fiber]
  exact polynomialRealization_map_eq_iff hφ P v w

end Fibres

/-! ### Real models as complex models -/

section Complex

/-- Evaluating the complexification of a real polynomial model at real parameters and a real
input gives the real outputs. -/
theorem polynomialRealization_map_ofReal (P : J → MvPolynomial (W ⊕ I) ℝ) (w : W → ℝ)
    (x : I → ℝ) (j : J) :
    polynomialRealization (map Complex.ofRealHom ∘ P) (fun i => (w i : ℂ)) (fun i => (x i : ℂ))
      j = ((polynomialRealization P w x j : ℝ) : ℂ) :=
  congrFun (polynomialRealization_map Complex.ofRealHom P w x) j

/-- Two real parameters of a real polynomial model realize the same real function exactly when
they realize the same complex function for its complexification. -/
theorem polynomialRealization_map_ofReal_eq_iff (P : J → MvPolynomial (W ⊕ I) ℝ) (w v : W → ℝ) :
    polynomialRealization (map Complex.ofRealHom ∘ P) (fun i => (w i : ℂ)) =
        polynomialRealization (map Complex.ofRealHom ∘ P) (fun i => (v i : ℂ)) ↔
      polynomialRealization P w = polynomialRealization P v :=
  polynomialRealization_map_eq_iff Complex.ofReal_injective P w v

end Complex

end TauCeti.Neuromanifold
