/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous forms by their coefficient vectors

A homogeneous form of degree `d` in the variables `σ` is determined by its coefficient vector,
indexed by the exponent vectors of the degree-`d` monomials. This file sets up that dictionary,
with unweighted monomials (no multinomial weights), as used for random hypersurfaces whose
coefficients are drawn uniformly:

* `FormDensity.Monomials σ d`, the finite set `M_d` of exponent vectors `m : σ →₀ ℕ` of total
  degree `d`, of cardinality `binom(#σ + d - 1, d)`;
* `FormDensity.form a = ∑ₘ aₘ Xᵐ`, the form with coefficient vector `a : M_d → R`;
* `FormDensity.veronese x = (xᵐ)ₘ`, the Veronese vector of a point `x : σ → R`, so that
  `f_a(x) = a ⬝ᵥ ν(x)` (`FormDensity.eval_form`).

The map `a ↦ f_a` is an `R`-linear isomorphism onto the homogeneous polynomials of degree `d`
(`FormDensity.formEquiv`), it commutes with coefficient ring homomorphisms (`FormDensity.map_form`),
and the Veronese vector of `c • x` is `c ^ d • ν(x)` (`FormDensity.veronese_smul`).

## References

* T. Browning, P. Le Boudec, W. Sawin, *The Hasse principle for random Fano hypersurfaces*,
  arXiv:2006.02356v1, §1 and §5.
-/

public section

open Finset MvPolynomial

namespace TauCeti.FormDensity

variable {σ R S : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}

variable (σ d) in
/-- The exponent vectors `m : σ →₀ ℕ` of the monomials of total degree `d` in the variables `σ`. -/
def Monomials : Finset (σ →₀ ℕ) :=
  univ.finsuppAntidiag d

/-- An exponent vector lies in `Monomials σ d` exactly when its total degree is `d`. -/
@[simp]
theorem mem_monomials {m : σ →₀ ℕ} : m ∈ Monomials σ d ↔ m.degree = d := by
  simp [Monomials, Finsupp.degree_eq_sum]

variable (σ d) in
/-- **Stars and bars.** There are `binom(#σ + d - 1, d)` monomials of degree `d` in the
variables `σ`. -/
theorem card_monomials : #(Monomials σ d) = (Fintype.card σ + d - 1).choose d := by
  rw [Monomials, card_finsuppAntidiag_nat_eq_choose, card_univ]

/-- In `n + 1` variables there are `binom(n + d, d)` monomials of degree `d`. -/
theorem card_monomials_fin (n d : ℕ) : #(Monomials (Fin (n + 1)) d) = (n + d).choose d := by
  rw [card_monomials, Fintype.card_fin, Nat.add_right_comm, Nat.add_sub_cancel]

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

/-- The form `f_a = ∑ₘ aₘ Xᵐ` of degree `d` with coefficient vector `a`, indexed by the exponent
vectors of the degree-`d` monomials. The monomials carry no multinomial weights. -/
noncomputable def form (a : Monomials σ d → R) : MvPolynomial σ R :=
  ∑ m : Monomials σ d, monomial (m : σ →₀ ℕ) (a m)

/-- The coefficient of `Xᵐ` in `f_a` is `aₘ` when `m` has degree `d`, and zero otherwise. -/
theorem coeff_form (a : Monomials σ d → R) (m : σ →₀ ℕ) :
    (form a).coeff m = if h : m ∈ Monomials σ d then a ⟨m, h⟩ else 0 := by
  rw [form, coeff_sum]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨m, h⟩ fun m' hm' ↦ ?_]
    · simp
    · simp only [coeff_monomial, ite_eq_right_iff]
      exact fun h' ↦ (hm' (Subtype.ext h')).elim
  · refine Fintype.sum_eq_zero _ fun m' ↦ ?_
    simp only [coeff_monomial, ite_eq_right_iff]
    rintro rfl
    exact (h m'.property).elim

/-- The coefficient of the monomial indexed by `m` in `f_a` is `aₘ`. -/
@[simp]
theorem coeff_form_coe (a : Monomials σ d → R) (m : Monomials σ d) :
    (form a).coeff (m : σ →₀ ℕ) = a m := by
  simp [coeff_form]

/-- A coefficient vector is determined by its form. -/
theorem form_injective : Function.Injective (form : (Monomials σ d → R) → MvPolynomial σ R) :=
  fun a b h ↦ funext fun m ↦ by rw [← coeff_form_coe a, h, coeff_form_coe]

@[simp]
theorem form_inj {a b : Monomials σ d → R} : form a = form b ↔ a = b :=
  form_injective.eq_iff

@[simp]
theorem form_zero : form (0 : Monomials σ d → R) = 0 := by
  simp [form]

@[simp]
theorem form_add (a b : Monomials σ d → R) : form (a + b) = form a + form b := by
  simp [form, sum_add_distrib]

@[simp]
theorem form_smul (c : R) (a : Monomials σ d → R) : form (c • a) = c • form a := by
  simp [form, smul_sum, smul_monomial]

/-- The form `f_a` is homogeneous of degree `d`. -/
theorem form_isHomogeneous (a : Monomials σ d → R) : (form a).IsHomogeneous d :=
  IsHomogeneous.sum _ _ _ fun m _ ↦ isHomogeneous_monomial _ (mem_monomials.mp m.property)

/-- Every homogeneous polynomial of degree `d` is the form of its coefficient vector. -/
theorem form_coeff {φ : MvPolynomial σ R} (hφ : φ.IsHomogeneous d) :
    form (fun m : Monomials σ d ↦ φ.coeff (m : σ →₀ ℕ)) = φ := by
  ext m
  rw [coeff_form]
  split_ifs with h
  · rfl
  · exact (hφ.coeff_eq_zero fun h' ↦ h (mem_monomials.mpr h')).symm

variable (σ R d) in
/-- Coefficient vectors indexed by the degree-`d` monomials are `R`-linearly isomorphic to the
homogeneous polynomials of degree `d`, through `a ↦ f_a`. -/
noncomputable def formEquiv : (Monomials σ d → R) ≃ₗ[R] homogeneousSubmodule σ R d where
  toFun a := ⟨form a, (mem_homogeneousSubmodule _ _).mpr (form_isHomogeneous a)⟩
  map_add' a b := Subtype.ext (form_add a b)
  map_smul' c a := Subtype.ext (form_smul c a)
  invFun φ m := (φ : MvPolynomial σ R).coeff (m : σ →₀ ℕ)
  left_inv a := funext fun m ↦ coeff_form_coe a m
  right_inv φ := Subtype.ext (form_coeff ((mem_homogeneousSubmodule _ _).mp φ.property))

@[simp]
theorem coe_formEquiv_apply (a : Monomials σ d → R) :
    (formEquiv σ R d a : MvPolynomial σ R) = form a :=
  (rfl)

@[simp]
theorem formEquiv_symm_apply (φ : homogeneousSubmodule σ R d) (m : Monomials σ d) :
    (formEquiv σ R d).symm φ m = (φ : MvPolynomial σ R).coeff (m : σ →₀ ℕ) :=
  (rfl)

/-- Applying a ring homomorphism to the coefficients of `f_a` gives the form of `φ ∘ a`; for
`φ : ℤ →+* ZMod Q` this is the reduction of an integral form modulo `Q`. -/
@[simp]
theorem map_form (φ : R →+* S) (a : Monomials σ d → R) : map φ (form a) = form (φ ∘ a) := by
  simp [form]

/-- The Veronese vector `ν(x) = (xᵐ)ₘ` of a point `x`, indexed by the degree-`d` monomials, with
unweighted monomials. -/
def veronese (x : σ → R) (m : Monomials σ d) : R :=
  ∏ i, x i ^ (m : σ →₀ ℕ) i

@[simp]
theorem veronese_apply (x : σ → R) (m : Monomials σ d) :
    veronese x m = ∏ i, x i ^ (m : σ →₀ ℕ) i :=
  (rfl)

/-- **The coefficient evaluation identity.** Evaluating `f_a` at `x` pairs the coefficient vector
with the Veronese vector: `f_a(x) = ∑ₘ aₘ xᵐ`. -/
theorem eval_form (x : σ → R) (a : Monomials σ d → R) : eval x (form a) = a ⬝ᵥ veronese x := by
  simp [form, dotProduct, veronese, eval_monomial, Finsupp.prod_fintype]

/-- Scaling a point by `c` scales its Veronese vector by `c ^ d`. -/
theorem veronese_smul (c : R) (x : σ → R) :
    veronese (c • x) = c ^ d • (veronese x : Monomials σ d → R) := by
  funext m
  have hm : ∑ i, (m : σ →₀ ℕ) i = d := by
    rw [← Finsupp.degree_eq_sum]
    exact mem_monomials.mp m.property
  simp [veronese, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hm]

/-- The Veronese vector commutes with ring homomorphisms applied coordinatewise. -/
theorem veronese_comp (φ : R →+* S) (x : σ → R) :
    veronese (φ ∘ x) = φ ∘ (veronese x : Monomials σ d → R) := by
  funext m
  simp [veronese, map_prod]

/-- Evaluation of forms commutes with ring homomorphisms applied to the coefficients and to the
point. -/
theorem eval_form_comp (φ : R →+* S) (x : σ → R) (a : Monomials σ d → R) :
    eval (φ ∘ x) (form (φ ∘ a)) = φ (eval x (form a)) := by
  simp [eval_form, dotProduct, map_sum]

end CommSemiring

end TauCeti.FormDensity
