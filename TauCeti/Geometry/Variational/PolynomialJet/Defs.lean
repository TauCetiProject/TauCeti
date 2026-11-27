/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Data.Finsupp.Weight

/-!
# Polynomial jets, total derivatives, and finite-order stages

`TauCeti.PolynomialJet R ι α` is the polynomial algebra on base coordinates indexed by `ι`
and field coordinates indexed by a field label `α` and a symmetric multi-index `ι →₀ ℕ`.
The multi-index records multiplicities, so mixed derivatives have a single coordinate.
Base coordinates are included: total differentiation `PolynomialJet.totalDeriv` differentiates
position-dependent polynomial coefficients as well as field coordinates, sending `xⱼ` to the
Kronecker delta and `uᵃ_I` to `uᵃ_(I+eᵢ)`.

The subalgebra `PolynomialJet.stage R ι α r` contains the expressions using field jets through
order `r`, with unrestricted polynomial dependence on the base coordinates.

## Main definitions

* `TauCeti.PolynomialJet`: `MvPolynomial (ι ⊕ (α × (ι →₀ ℕ))) R`.
* `TauCeti.PolynomialJet.totalDeriv`: total differentiation along coordinate `i`.
* `TauCeti.PolynomialJet.stage`: finite-order subalgebra of field-jet order at most `r`.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, §A, for symmetric jet
  coordinates and total derivatives.
-/

public section

namespace TauCeti

/-- Polynomial expressions in base coordinates and symmetric field-jet coordinates.
The coefficient ring consists of constants; polynomial base dependence is represented by
the `Sum.inl` variables. -/
abbrev PolynomialJet (R ι α : Type*) [CommSemiring R] :=
  MvPolynomial (ι ⊕ (α × (ι →₀ ℕ))) R

namespace PolynomialJet

open MvPolynomial

noncomputable section

variable {R ι α : Type*} [CommSemiring R]

/-- Total differentiation in a base direction, including differentiation of base coordinates. -/
def totalDeriv (i : ι) :
    Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α) := by
  classical
  exact mkDerivation R (Sum.elim (fun j ↦ if i = j then 1 else 0)
    (fun aI ↦ X (Sum.inr (aI.1, aI.2 + Finsupp.single i 1))))

open Classical in
@[simp]
theorem totalDeriv_X_base (i j : ι) :
    totalDeriv (R := R) (α := α) i (X (Sum.inl j)) = if i = j then 1 else 0 := by
  classical
  simp [totalDeriv]

@[simp]
theorem totalDeriv_X_field (i : ι) (a : α) (I : ι →₀ ℕ) :
    totalDeriv (R := R) i (X (Sum.inr (a, I))) =
      X (Sum.inr (a, I + Finsupp.single i 1)) := by
  simp [totalDeriv]

open Classical in
/-- The total derivative is determined by its actions on base and field coordinates. -/
theorem totalDeriv_unique (i : ι)
    (D : Derivation R (PolynomialJet R ι α) (PolynomialJet R ι α))
    (hx : ∀ j, D (X (Sum.inl j)) = if i = j then 1 else 0)
    (hu : ∀ a I, D (X (Sum.inr (a, I))) = X (Sum.inr (a, I + Finsupp.single i 1))) :
    D = totalDeriv i := by
  classical
  apply MvPolynomial.derivation_ext
  rintro (j | ⟨a, I⟩) <;> simp [hx, hu]

variable (R ι α)

/-- The finite-order polynomial jet algebra, embedded in the algebra on all jet variables.
Base-coordinate degree is unrestricted. -/
def stage (r : ℕ) : Subalgebra R (PolynomialJet R ι α) :=
  supported R {v | Sum.elim (fun _ ↦ True) (fun aI ↦ aI.2.degree ≤ r) v}

variable {R ι α}

/-- `PolynomialJet.stage R ι α r` is the subalgebra of polynomials supported on base coordinates
and field-jet variables of order at most `r`. -/
theorem stage_eq_supported (r : ℕ) :
    stage R ι α r =
      supported R {v | Sum.elim (fun _ ↦ True) (fun aI ↦ aI.2.degree ≤ r) v} := by
  rw [stage]

/-- Membership in a finite stage means that every field variable occurring has bounded order. -/
theorem mem_stage_iff (p : PolynomialJet R ι α) (r : ℕ) :
    p ∈ stage R ι α r ↔ ∀ a I, Sum.inr (a, I) ∈ p.vars → I.degree ≤ r := by
  rw [stage_eq_supported, mem_supported]
  constructor
  · intro h a I hI
    exact h hI
  · intro h v hv
    rcases v with j | ⟨a, I⟩
    · trivial
    · exact h a I hv

/-- Increasing the jet-order budget gives the canonical inclusion of stage algebras. -/
theorem stage_mono : Monotone (stage R ι α) := by
  intro r s hrs
  apply supported_mono
  rintro (j | ⟨a, I⟩) h
  · trivial
  · exact h.trans hrs

@[simp]
theorem X_base_mem_stage (r : ℕ) (j : ι) :
    (X (Sum.inl j) : PolynomialJet R ι α) ∈ stage R ι α r := by
  rw [stage_eq_supported, supported_eq_adjoin_X]
  exact Algebra.subset_adjoin ⟨Sum.inl j, trivial, rfl⟩

/-- Base-coordinate polynomials lie in every finite stage of `PolynomialJet`. -/
@[simp]
theorem rename_inl_mem_stage (r : ℕ) (b : MvPolynomial ι R) :
    rename Sum.inl b ∈ stage R ι α r := by
  classical
  refine supported_mono ?_ (rename Sum.inl b).mem_supported_vars
  intro v hv
  rcases Finset.mem_image.mp (vars_rename Sum.inl b hv) with ⟨j, _, rfl⟩
  trivial

theorem X_field_mem_stage (r : ℕ) (a : α) (I : ι →₀ ℕ) (hI : I.degree ≤ r) :
    (X (Sum.inr (a, I)) : PolynomialJet R ι α) ∈ stage R ι α r := by
  rw [stage_eq_supported, supported_eq_adjoin_X]
  exact Algebra.subset_adjoin ⟨Sum.inr (a, I), hI, rfl⟩

@[simp]
theorem X_field_mem_stage_iff [Nontrivial R] (r : ℕ) (a : α) (I : ι →₀ ℕ) :
    (X (Sum.inr (a, I)) : PolynomialJet R ι α) ∈ stage R ι α r ↔ I.degree ≤ r := by
  simp [stage_eq_supported]

end

end PolynomialJet
end TauCeti
