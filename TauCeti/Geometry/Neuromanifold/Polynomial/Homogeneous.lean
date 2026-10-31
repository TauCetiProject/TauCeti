/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Polynomial.Constructors
public import TauCeti.Geometry.Neuromanifold.Polynomial.Presentation

/-!
# Homogeneous coefficient presentations of polynomial models

A jointly polynomial tuple `P : J → MvPolynomial (W ⊕ X) K` is homogeneous of degree `d` in its
inputs when every collected input polynomial `inputPolynomial P j` is homogeneous of degree `d`,
in Mathlib's sense `MvPolynomial.IsHomogeneous`, with coefficients polynomial in the parameters.
Specializing the parameters keeps this homogeneity, so the coefficient presentation of such a
model takes values in a product of homogeneous submodules:

* `polynomialHomogeneousCoefficientMap P hP` is this coefficient map, and
  `MvPolynomial.homogeneousEvaluation` recovers the realization map from it. Over an infinite
  integral domain the evaluation is faithful, so coefficients and functions give the same fibres.
* `polynomialHomogeneousCoefficientCoordinates P hP` gives finite coordinates, indexed by an
  output and an input exponent of degree exactly `d`; each is polynomial in the parameters.
* The homogeneous presentation includes into the bounded-degree one with bound `d`:
  `inclusion_comp_polynomialHomogeneousCoefficientMap` compares the coefficient maps and
  `boundedCoefficientPadding_polynomialCoefficientCoordinates` shows that the zero-padded
  bounded-degree coordinates are the homogeneous coordinates extended by zero.

Input homogeneity is preserved by the polynomial constructors used to build bias-free networks.
Substituting polynomials for the parameters keeps the input degree
(`isHomogeneous_inputPolynomial_polynomialReparametrize`), and substituting a model homogeneous of
degree `a` into one homogeneous of degree `b` gives degree `a * b`
(`isHomogeneous_inputPolynomial_polynomialCompose`). The linear layer has degree one and the
monomial activation `t ↦ t ^ r` has degree `r`. Zero outputs are homogeneous of every degree.

Homogeneous polynomial networks and their coefficient spaces follow
Finkel–Rodriguez–Wu–Yahl, *Activation degree thresholds and expressiveness of polynomial neural
networks*, [arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1 and §1.1.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K W J : Type*} [CommSemiring K]

section Presentation

variable {X : Type*} {d : ℕ}

/-- If every collected input polynomial is homogeneous of degree `d`, the uniform input-degree
bound is at most `d`. -/
theorem polynomialInputDegree_le_of_isHomogeneous [Fintype J] {P : J → MvPolynomial (W ⊕ X) K}
    (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) : polynomialInputDegree P ≤ d :=
  polynomialInputDegree_le_iff.2 fun j => (hP j).totalDegree_le

/-- The coefficient presentation of a model whose input polynomials are homogeneous of degree
`d`, with values in a product of homogeneous submodules. -/
def polynomialHomogeneousCoefficientMap (P : J → MvPolynomial (W ⊕ X) K)
    (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) (w : W → K) :
    J → homogeneousSubmodule X K d :=
  fun j => ⟨map (eval w) (inputPolynomial P j), (hP j).map _⟩

/-- Forgetting homogeneity gives coefficientwise parameter evaluation. -/
@[simp] theorem polynomialHomogeneousCoefficientMap_coe (P : J → MvPolynomial (W ⊕ X) K)
    (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) (w : W → K) (j : J) :
    (polynomialHomogeneousCoefficientMap P hP w j : MvPolynomial X K) =
      map (eval w) (inputPolynomial P j) := (rfl)

/-- Evaluating the homogeneous coefficient presentation recovers the realization map. -/
theorem homogeneousEvaluation_comp_polynomialHomogeneousCoefficientMap
    (P : J → MvPolynomial (W ⊕ X) K) (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) :
    homogeneousEvaluation X K J d ∘ polynomialHomogeneousCoefficientMap P hP =
      polynomialRealization P := by
  funext w x j
  simp [eval_map]

/-- The homogeneous coefficient presentation includes into the bounded-degree presentation
with degree bound `d`: including the homogeneous coefficients gives the bounded coefficients,
included from the uniform input-degree bound into the bound `d`. -/
theorem inclusion_comp_polynomialHomogeneousCoefficientMap [Fintype J]
    (P : J → MvPolynomial (W ⊕ X) K) (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) (w : W → K) :
    Submodule.inclusion (homogeneousSubmodule_le_restrictTotalDegree X K le_rfl) ∘
        polynomialHomogeneousCoefficientMap P hP w =
      Submodule.inclusion
          (restrictTotalDegree_mono X K (polynomialInputDegree_le_of_isHomogeneous hP)) ∘
        polynomialCoefficientMap P w := by
  funext j
  ext1
  simp

/-- The functions realized by a model with homogeneous input polynomials are the evaluations of
its homogeneous coefficient image. -/
theorem realizedFunctions_polynomialRealization_of_isHomogeneous
    (P : J → MvPolynomial (W ⊕ X) K) (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) :
    realizedFunctions (polynomialRealization P) =
      homogeneousEvaluation X K J d '' Set.range (polynomialHomogeneousCoefficientMap P hP) :=
  realizedFunctions_eq_image_range
    (congrFun (homogeneousEvaluation_comp_polynomialHomogeneousCoefficientMap P hP))

section Coordinates

variable [Finite X]

/-- The homogeneous coefficient presentation in finite coordinates, indexed by an output and an
input exponent of degree `d`. -/
def polynomialHomogeneousCoefficientCoordinates (P : J → MvPolynomial (W ⊕ X) K)
    (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) (w : W → K) :
    J × {s : X →₀ ℕ // s.degree = d} → K :=
  homogeneousCoefficientEquiv X K J d (polynomialHomogeneousCoefficientMap P hP w)

/-- Each homogeneous coefficient coordinate is the evaluation at the parameters of a fixed
polynomial in the parameters. -/
@[simp] theorem polynomialHomogeneousCoefficientCoordinates_apply
    (P : J → MvPolynomial (W ⊕ X) K) (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d)
    (w : W → K) (i : J × {s : X →₀ ℕ // s.degree = d}) :
    polynomialHomogeneousCoefficientCoordinates P hP w i =
      eval w ((inputPolynomial P i.1).coeff i.2) := by
  simp [polynomialHomogeneousCoefficientCoordinates, coeff_map]

/-- Zero-padding the bounded-degree coordinates up to the bound `d` gives the homogeneous
coordinates extended by zero: every coordinate at an exponent of degree below `d` vanishes. -/
theorem boundedCoefficientPadding_polynomialCoefficientCoordinates [Fintype J]
    (P : J → MvPolynomial (W ⊕ X) K) (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d)
    (w : W → K) :
    boundedCoefficientPadding (polynomialInputDegree_le_of_isHomogeneous hP)
        (polynomialCoefficientCoordinates P w) =
      Function.ExtendByZero.linearMap K K (Prod.map (id : J → J)
          (Subtype.impEmbedding (fun s : X →₀ ℕ => s.degree = d) (fun s => s.degree ≤ d)
            fun _ hs => hs.le))
        (polynomialHomogeneousCoefficientCoordinates P hP w) := by
  ext i
  rw [boundedCoefficientPadding_eq_extendByZero_linearMap,
    extendByZero_polynomialCoefficientCoordinates_apply _
      (polynomialInputDegree_le_of_isHomogeneous hP),
    polynomialHomogeneousCoefficientCoordinates,
    ← boundedCoefficientEquiv_inclusion_comp_homogeneous le_rfl, boundedCoefficientEquiv_apply]
  simp [coeff_map]

end Coordinates

section Faithful

variable {K : Type*} [CommRing K] [IsDomain K] [Infinite K]

/-- Over an infinite integral domain, parameters of a model with homogeneous input polynomials
realize the same function exactly when they have the same homogeneous coefficients. -/
theorem polynomialHomogeneousCoefficientMap_eq_iff (P : J → MvPolynomial (W ⊕ X) K)
    (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) {w v : W → K} :
    polynomialHomogeneousCoefficientMap P hP w = polynomialHomogeneousCoefficientMap P hP v ↔
      polynomialRealization P w = polynomialRealization P v :=
  apply_eq_apply_iff_of_injective (homogeneousEvaluation_injective _)
    (congrFun (homogeneousEvaluation_comp_polynomialHomogeneousCoefficientMap P hP))

/-- Over an infinite integral domain, the realization fibre of a model with homogeneous input
polynomials over the evaluation of `q` is the homogeneous coefficient fibre over `q`. -/
theorem fiber_polynomialRealization_homogeneousEvaluation (P : J → MvPolynomial (W ⊕ X) K)
    (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d) (q : J → homogeneousSubmodule X K d) :
    fiber (polynomialRealization P) (homogeneousEvaluation X K J d q) =
      polynomialHomogeneousCoefficientMap P hP ⁻¹' {q} :=
  fiber_apply_eq_preimage (homogeneousEvaluation_injective _)
    (congrFun (homogeneousEvaluation_comp_polynomialHomogeneousCoefficientMap P hP)) q

end Faithful

end Presentation

section Constructors

variable {W' V I L : Type*}

/-- Substituting polynomials `R` for the parameters substitutes them into the parameter
coefficients of each collected input polynomial. -/
theorem inputPolynomial_polynomialReparametrize (R : W → MvPolynomial W' K)
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

/-- Substituting polynomials for the parameters preserves input homogeneity. -/
theorem isHomogeneous_inputPolynomial_polynomialReparametrize (R : W → MvPolynomial W' K)
    {P : J → MvPolynomial (W ⊕ I) K} {d : ℕ} (hP : ∀ j, (inputPolynomial P j).IsHomogeneous d)
    (j : J) : (inputPolynomial (polynomialReparametrize R P) j).IsHomogeneous d := by
  rw [inputPolynomial_polynomialReparametrize]
  exact (hP j).map _

/-- Collecting the inputs of a composite model substitutes the collected input polynomials of
`P`, with parameters renamed into the composite parameters, for the inputs of `Q`. -/
theorem inputPolynomial_polynomialCompose (P : J → MvPolynomial (W ⊕ I) K)
    (Q : L → MvPolynomial (V ⊕ J) K) (l : L) :
    inputPolynomial (polynomialCompose P Q) l =
      eval₂ (C.comp (rename Sum.inr : MvPolynomial V K →ₐ[K] MvPolynomial (W ⊕ V) K))
        (fun j => map (rename Sum.inl : MvPolynomial W K →ₐ[K] MvPolynomial (W ⊕ V) K)
          (inputPolynomial P j))
        (inputPolynomial Q l) := by
  -- Renaming the parameters of `P` into the composite parameters commutes with collecting inputs.
  have hP (p : MvPolynomial (W ⊕ I) K) :
      sumAlgEquiv K I (W ⊕ V) (rename (Sum.swap ∘ Sum.map Sum.inl id) p) =
        map (rename Sum.inl : MvPolynomial W K →ₐ[K] MvPolynomial (W ⊕ V) K)
          (sumAlgEquiv K I W (rename Sum.swap p)) := by
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => cases i <;> simp [hp]
  simp only [inputPolynomial_def, polynomialCompose_apply]
  induction Q l using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp, hP]

/-- Substituting a model whose input polynomials are homogeneous of degree `a` into one whose
input polynomials are homogeneous of degree `b` gives input polynomials homogeneous of degree
`a * b`. -/
theorem isHomogeneous_inputPolynomial_polynomialCompose {P : J → MvPolynomial (W ⊕ I) K}
    {Q : L → MvPolynomial (V ⊕ J) K} {a b : ℕ} (hP : ∀ j, (inputPolynomial P j).IsHomogeneous a)
    (hQ : ∀ l, (inputPolynomial Q l).IsHomogeneous b) (l : L) :
    (inputPolynomial (polynomialCompose P Q) l).IsHomogeneous (a * b) := by
  rw [inputPolynomial_polynomialCompose]
  exact (hQ l).eval₂ _ _ (fun _ => isHomogeneous_C _ _) fun j => (hP j).map _

section Layers

variable {ι ο : Type*}

/-- The collected input polynomials of the linear layer are linear forms whose coefficients are
the weight variables. -/
@[simp] theorem inputPolynomial_polynomialLinear [Fintype ι] (o : ο) :
    inputPolynomial (polynomialLinear : ο → MvPolynomial (ο × ι ⊕ ι) K) o =
      ∑ i, C (X (o, i)) * X i := by
  simp [inputPolynomial_def, polynomialLinear_apply]

/-- The linear layer is homogeneous of degree one in its inputs. -/
theorem isHomogeneous_inputPolynomial_polynomialLinear [Fintype ι] (o : ο) :
    (inputPolynomial (polynomialLinear : ο → MvPolynomial (ο × ι ⊕ ι) K) o).IsHomogeneous 1 := by
  rw [inputPolynomial_polynomialLinear]
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ i

/-- The monomial activation `t ↦ t ^ r` is homogeneous of degree `r` in its inputs. -/
theorem isHomogeneous_inputPolynomial_polynomialActivation_X_pow (r : ℕ) (i : ι) :
    IsHomogeneous
      (inputPolynomial (polynomialActivation (W := W) (Polynomial.X ^ r : Polynomial K)) i) r := by
  simpa [inputPolynomial_def] using isHomogeneous_X_pow (R := MvPolynomial W K) i r

end Layers

end Constructors

end TauCeti.Neuromanifold
