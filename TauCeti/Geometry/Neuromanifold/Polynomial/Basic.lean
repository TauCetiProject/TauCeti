/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Sum
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree

/-!
# Polynomial realization maps and input coefficients

A tuple of polynomials in parameter and input variables supplies a realization map
`polynomialRealization P`. Taking the variable types to be `Fin p` and `Fin n` gives
finite-dimensional polynomial models without prescribing a neural architecture.

`inputPolynomial P j` collects the input variables of output `j`, with coefficients
that are polynomials in the parameters. Its fixed finite support gives a reconstruction
formula for every parameter, including specializations at which coefficients vanish.
For finitely many outputs, `polynomialInputDegree P` is a uniform input-degree bound,
independent of the parameters. `polynomialCoefficientMap P` therefore takes values in
a product of bounded-degree polynomial submodules, ready for finite coefficient coordinates.
Zero outputs and constant polynomials are included; the degree bound need not be minimal.

A tuple of bounded-degree polynomials has finite coordinates:
`MvPolynomial.boundedCoefficientEquiv` identifies it with functions on the pairs of an output and
an exponent of degree at most `d`, by taking monomial coefficients. Its evaluation
`MvPolynomial.boundedEvaluation` is a linear map to vector-valued functions on inputs, injective
over an infinite integral domain, and
`boundedEvaluation_comp_polynomialCoefficientMap` recovers the realization map from the
coefficient presentation. Composing with the coordinates gives
`polynomialCoefficientCoordinates P`, whose coordinates are polynomial in the parameters.
Raising the degree bound zero-pads these coordinates, and the padded coordinates are given by the
same coefficient formula, so the coordinates for different bounds correspond under zero-padding.

The jointly polynomial setting and the coefficient/function viewpoint follow
Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
The extraction uses Mathlib's `MvPolynomial.sumAlgEquiv` and coefficient mapping;
the bounded spaces are Mathlib's `MvPolynomial.restrictTotalDegree`, with coordinates given by
its monomial basis, and faithfulness of evaluation is Mathlib's `MvPolynomial.funext`.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K W X J : Type*} [CommSemiring K]

/-- A jointly polynomial tuple, evaluated at the supplied parameters and input. -/
def polynomialRealization (P : J → MvPolynomial (W ⊕ X) K) :
    (W → K) → (X → K) → (J → K) :=
  fun w x j => eval (Sum.elim w x) (P j)

/-- Coordinate evaluation of a jointly polynomial realization map. -/
@[simp] theorem polynomialRealization_apply (P : J → MvPolynomial (W ⊕ X) K)
    (w : W → K) (x : X → K) (j : J) :
    polynomialRealization P w x j = eval (Sum.elim w x) (P j) := (rfl)

/-- Collect the input variables, leaving polynomial coefficients in the parameters.
The swap keeps the original joint-polynomial convention: parameters precede inputs. -/
def inputPolynomial (P : J → MvPolynomial (W ⊕ X) K) (j : J) :
    MvPolynomial X (MvPolynomial W K) :=
  sumAlgEquiv K X W (rename Sum.swap (P j))

/-- Input collection is the standard separation of the two variable families. -/
theorem inputPolynomial_def (P : J → MvPolynomial (W ⊕ X) K) (j : J) :
    inputPolynomial P j = sumAlgEquiv K X W (rename Sum.swap (P j)) := (rfl)

/-- Zero joint polynomials have no input coefficients. -/
@[simp] theorem inputPolynomial_zero (j : J) :
    inputPolynomial (fun _ : J => (0 : MvPolynomial (W ⊕ X) K)) j = 0 := by
  simp [inputPolynomial_def]

/-- Constant joint polynomials give constant input polynomials with constant coefficients. -/
@[simp] theorem inputPolynomial_C (a : J → K) (j : J) :
    inputPolynomial (fun j => C (a j) : J → MvPolynomial (W ⊕ X) K) j =
      C (C (a j)) := by
  simp [inputPolynomial_def]

/-- Specializing the parameter-polynomial coefficients and evaluating inputs recovers
the whole realization map, with no infinitude assumption on the scalars. -/
@[simp] theorem eval₂_inputPolynomial (P : J → MvPolynomial (W ⊕ X) K)
    (w : W → K) (x : X → K) (j : J) :
    eval₂ (eval w) x (inputPolynomial P j) = polynomialRealization P w x j := by
  rw [inputPolynomial_def]
  have h := eval₂_sumAlgEquiv (RingHom.id K) x w (rename Sum.swap (P j))
  rw [← eval] at h
  simpa only [eval₂_id, eval_rename, Sum.elim_swap, polynomialRealization_apply] using h

/-- Reconstruction using a fixed finite set of input monomials. The coefficients are
polynomials in the parameters; the support is independent of the parameter value. -/
theorem polynomialRealization_eq_sum (P : J → MvPolynomial (W ⊕ X) K)
    (w : W → K) (x : X → K) (j : J) :
    polynomialRealization P w x j =
      ∑ a ∈ (inputPolynomial P j).support,
        eval w ((inputPolynomial P j).coeff a) * a.prod (fun i n => x i ^ n) := by
  rw [← eval₂_inputPolynomial, eval₂_eq]
  rfl

section InputDegree

variable [Fintype J]

/-- A uniform bound on input degree, before specializing any parameters.
The bound is zero when there are no outputs. -/
def polynomialInputDegree (P : J → MvPolynomial (W ⊕ X) K) : ℕ :=
  Finset.univ.sup fun j => (inputPolynomial P j).totalDegree

/-- The zero model has input-degree bound zero. -/
@[simp] theorem polynomialInputDegree_zero :
    polynomialInputDegree (fun _ : J => (0 : MvPolynomial (W ⊕ X) K)) = 0 := by
  simp [polynomialInputDegree]

/-- Constant outputs have input-degree bound zero. -/
@[simp] theorem polynomialInputDegree_C (a : J → K) :
    polynomialInputDegree (fun j => C (a j) : J → MvPolynomial (W ⊕ X) K) = 0 := by
  simp [polynomialInputDegree]

/-- An empty tuple of outputs has input-degree bound zero. -/
@[simp] theorem polynomialInputDegree_of_isEmpty [IsEmpty J]
    (P : J → MvPolynomial (W ⊕ X) K) : polynomialInputDegree P = 0 := by
  simp [polynomialInputDegree]

/-- Each output's collected input polynomial has degree at most the uniform bound. -/
theorem totalDegree_inputPolynomial_le (P : J → MvPolynomial (W ⊕ X) K) (j : J) :
    (inputPolynomial P j).totalDegree ≤ polynomialInputDegree P :=
  Finset.le_sup (f := fun j => (inputPolynomial P j).totalDegree) (Finset.mem_univ j)

/-- Every input monomial in the reconstruction has degree at most the uniform bound. -/
theorem inputPolynomial_support_degree_le (P : J → MvPolynomial (W ⊕ X) K)
    (j : J) {a : X →₀ ℕ} (ha : a ∈ (inputPolynomial P j).support) :
    a.sum (fun _ n => n) ≤ polynomialInputDegree P :=
  (le_totalDegree ha).trans (totalDegree_inputPolynomial_le P j)

/-- Coefficients above the uniform input-degree bound vanish as parameter polynomials,
not just at one parameter value. -/
theorem inputPolynomial_coeff_eq_zero_of_degree_lt
    (P : J → MvPolynomial (W ⊕ X) K) (j : J) {a : X →₀ ℕ}
    (ha : polynomialInputDegree P < a.sum (fun _ n => n)) :
    (inputPolynomial P j).coeff a = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  exact lt_of_le_of_lt (totalDegree_inputPolynomial_le P j) ha

/-- Specializing parameters cannot increase the uniform input-degree bound. -/
theorem totalDegree_map_inputPolynomial_le (P : J → MvPolynomial (W ⊕ X) K)
    (w : W → K) (j : J) :
    (map (eval w) (inputPolynomial P j)).totalDegree ≤ polynomialInputDegree P := by
  have hs := support_map_subset (eval w) (inputPolynomial P j)
  exact (Finset.sup_mono hs).trans (totalDegree_inputPolynomial_le P j)

/-- The polynomial coefficient presentation takes values in a fixed product of
bounded-degree spaces, even when specialization cancels some monomials. -/
def polynomialCoefficientMap (P : J → MvPolynomial (W ⊕ X) K) (w : W → K) :
    J → restrictTotalDegree X K (polynomialInputDegree P) :=
  fun j => ⟨map (eval w) (inputPolynomial P j),
    (mem_restrictTotalDegree _ _ _).mpr (totalDegree_map_inputPolynomial_le P w j)⟩

/-- Forgetting the degree bound gives coefficientwise parameter evaluation. -/
@[simp] theorem polynomialCoefficientMap_coe (P : J → MvPolynomial (W ⊕ X) K)
    (w : W → K) (j : J) :
    (polynomialCoefficientMap P w j : MvPolynomial X K) =
      map (eval w) (inputPolynomial P j) := (rfl)

/-- Each monomial coefficient of the presentation is a polynomial function of parameters. -/
theorem coeff_polynomialCoefficientMap (P : J → MvPolynomial (W ⊕ X) K)
    (w : W → K) (j : J) (a : X →₀ ℕ) :
    (polynomialCoefficientMap P w j : MvPolynomial X K).coeff a =
      eval w ((inputPolynomial P j).coeff a) := by
  rw [polynomialCoefficientMap_coe, coeff_map]

end InputDegree

section Coordinates

/-- Evaluating the coefficient presentation recovers the jointly polynomial realization map. -/
theorem boundedEvaluation_comp_polynomialCoefficientMap [Fintype J]
    (P : J → MvPolynomial (W ⊕ X) K) :
    boundedEvaluation X K J (polynomialInputDegree P) ∘ polynomialCoefficientMap P =
      polynomialRealization P := by
  funext w x j
  simp [eval_map]

variable [Fintype J] [Finite X]

/-- The polynomial coefficient presentation in finite coordinates, indexed by an output and
an input exponent of degree at most `polynomialInputDegree P`. -/
def polynomialCoefficientCoordinates (P : J → MvPolynomial (W ⊕ X) K) (w : W → K) :
    J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P} → K :=
  boundedCoefficientEquiv X K J _ (polynomialCoefficientMap P w)

/-- Each finite coefficient coordinate is the evaluation at the parameters of a fixed
polynomial in the parameters. -/
@[simp] theorem polynomialCoefficientCoordinates_apply (P : J → MvPolynomial (W ⊕ X) K)
    (w : W → K) (i : J × {s : X →₀ ℕ // s.degree ≤ polynomialInputDegree P}) :
    polynomialCoefficientCoordinates P w i = eval w ((inputPolynomial P i.1).coeff i.2) := by
  simp [polynomialCoefficientCoordinates, coeff_map]

/-- Raising the degree bound to any `d ≥ polynomialInputDegree P` zero-pads the finite coefficient
coordinates, and the padded coordinates are given by the same formula: each is the evaluation at
the parameters of the corresponding input coefficient. The padding is thus independent of the
parameters, and the coefficients it introduces vanish identically. -/
theorem extendByZero_polynomialCoefficientCoordinates_apply (P : J → MvPolynomial (W ⊕ X) K)
    {d : ℕ} (h : polynomialInputDegree P ≤ d) (w : W → K)
    (i : J × {s : X →₀ ℕ // s.degree ≤ d}) :
    Function.ExtendByZero.linearMap K K (Prod.map (id : J → J)
        (Subtype.impEmbedding (fun s : X →₀ ℕ => s.degree ≤ polynomialInputDegree P)
          (fun s => s.degree ≤ d) fun _ hs => hs.trans h))
        (polynomialCoefficientCoordinates P w) i =
      eval w ((inputPolynomial P i.1).coeff i.2) := by
  rw [polynomialCoefficientCoordinates, ← boundedCoefficientEquiv_inclusion_comp h,
    boundedCoefficientEquiv_apply]
  simp [coeff_map]

end Coordinates

end TauCeti.Neuromanifold
