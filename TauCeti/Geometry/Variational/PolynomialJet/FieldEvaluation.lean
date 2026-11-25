/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Variational.PolynomialJet.Basic
public import TauCeti.RingTheory.Derivation.Coordinates

/-!
# Evaluating polynomial jets along a field

Let `B` be a commutative `R`-algebra with pairwise commuting derivations `δᵢ`, for a finite type
`ι` of base directions, for instance smooth functions on a domain of `ℝⁿ` with their partial
derivatives. A *field* is a family `f : α → B` of field components, and coordinates `x : ι → B`
locate the base point. Evaluating a polynomial jet expression along the field substitutes
`xⱼ ↦ x j` for the base coordinates and the derivative `uᵃ_I ↦ ∂^I fᵃ` for the field-jet
coordinates, where `∂^I = ∏ᵢ δᵢ ^ I i` is the monomial `TauCeti.multiIndexDeriv` in the
commuting derivations. We write `j f` for the jets `∂^I fᵃ` of the field and `p(x, j f)` for the
value of `p` under this substitution, which is `TauCeti.PolynomialJet.fieldEval`.

When the coordinates are dual to the derivations in direction `i`, `δᵢ xⱼ = [i = j]`,
differentiating the evaluation of `p` is evaluating its total derivative:
`δᵢ (p(x, j f)) = (Dᵢ p)(x, j f)` (`TauCeti.PolynomialJet.apply_fieldEval`). This is the sense
in which `Dᵢ` is the derivative of a polynomial expression along every field, and it follows from
the generator criterion `Derivation.aeval_polynomialJet`, since the jets `∂^I fᵃ` satisfy the
prolongation equations `δᵢ (∂^I fᵃ) = ∂^(I + eᵢ) fᵃ`.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, §A, for prolongation of
  sections and total derivatives.
* P. J. Olver, *Applications of Lie Groups to Differential Equations*, 2nd ed. (1993), §2.3, for
  total derivatives of differential functions.
-/

public section

namespace TauCeti

namespace PolynomialJet

open MvPolynomial

noncomputable section

variable {R ι α B : Type*} [CommSemiring R] [Fintype ι] [CommSemiring B] [Algebra R B]
  (δ : ι → Derivation R B B) (hδ : ∀ i j, Commute (δ i : Module.End R B) (δ j))
  (x : ι → B) (f : α → B)

/-- Evaluation of polynomial jet expressions along a field `f : α → B` at coordinates
`x : ι → B`, in an algebra `B` with commuting derivations `δᵢ`: the base coordinate `xⱼ` is sent
to `x j` and the field-jet coordinate `uᵃ_I` to the derivative `∂^I fᵃ`. -/
def fieldEval : PolynomialJet R ι α →ₐ[R] B :=
  aeval (Sum.elim x fun aI ↦ multiIndexDeriv δ hδ aI.2 (f aI.1))

/-- The defining formula of evaluation along a field. -/
theorem fieldEval_def :
    fieldEval δ hδ x f = aeval (Sum.elim x fun aI ↦ multiIndexDeriv δ hδ aI.2 (f aI.1)) :=
  (rfl)

/-- Evaluation along a field sends the base coordinate `xⱼ` to `x j`. -/
@[simp]
theorem fieldEval_X_base (j : ι) :
    fieldEval δ hδ x f (X (Sum.inl j) : PolynomialJet R ι α) = x j := by
  simp [fieldEval_def]

/-- Evaluation along a field sends the field-jet coordinate `uᵃ_I` to `∂^I fᵃ`. -/
@[simp]
theorem fieldEval_X_field (a : α) (I : ι →₀ ℕ) :
    fieldEval δ hδ x f (X (Sum.inr (a, I)) : PolynomialJet R ι α) =
      multiIndexDeriv δ hδ I (f a) := by
  simp [fieldEval_def]

open Classical in
/-- **Total derivatives are derivatives along fields.** If the coordinates are dual to the
derivations in direction `i`, then differentiating the evaluation of a polynomial jet expression
along a field is evaluating its total derivative: `δᵢ (p(x, j f)) = (Dᵢ p)(x, j f)`, where
`p(x, j f)` is `fieldEval δ hδ x f p`, substituting `x j` for `xⱼ` and `∂^I fᵃ` for `uᵃ_I`. -/
theorem apply_fieldEval (i : ι) (hx : ∀ j, δ i (x j) = if i = j then 1 else 0)
    (p : PolynomialJet R ι α) :
    δ i (fieldEval δ hδ x f p) = fieldEval δ hδ x f (totalDeriv i p) := by
  refine (δ i).aeval_polynomialJet i x (fun a I ↦ multiIndexDeriv δ hδ I (f a)) hx
    (fun a I ↦ ?_) p
  rw [Finsupp.coe_add, Finsupp.single_eq_pi_single, multiIndexDeriv_add_single',
    mul_apply_eq_comp, Derivation.coeFn_coe]

end

end PolynomialJet

end TauCeti
