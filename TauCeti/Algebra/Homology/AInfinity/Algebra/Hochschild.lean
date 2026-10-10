/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.LinearAlgebra.TensorCoalgebra.Brace

/-!
# The brace equation and the Hochschild differential of an `A∞` algebra

The suspended Hochschild cochains of a graded module `A` in positive arities are the linear maps
`Tᶜ(sA) ⟶ sA` from the reduced tensor coalgebra on the suspension to the suspension.  They carry
the brace `F{g}` and the Gerstenhaber bracket `[F, g]` of
`TauCeti.LinearAlgebra.TensorCoalgebra.Brace`.  An `A∞` structure on `A` is such a cochain `m`,
its suspended Taylor map, of degree one, and the square-zero law `b² = 0` for its bar differential
`b` is the brace equation `m{m} = 0` (`AInfinityAlgebra.brace_taylor_taylor`; conversely
`ReducedTensorWords.gradedCoderiv_comp_self_eq_zero_iff` turns a solution of the brace equation
into the input of `AInfinityAlgebra.ofTaylor`).

Bracketing with `m` is the Hochschild differential `d F = [m, F]`.  It raises degrees by one,
its graded coderivation is the graded commutator `b ∘ D F - (-1)^q • D F ∘ b` with the bar
differential, and it squares to zero because `b` does.  The cochains here are those of positive
arity, which form a subcomplex of the full Hochschild complex: the arity-zero cochains would need
the coaugmented tensor coalgebra.

## Main definitions

* `TauCeti.AInfinityAlgebra.hochschildDifferential`: the Hochschild differential `[m, -]` on
  suspended cochains of a fixed degree.

## Main results

* `TauCeti.AInfinityAlgebra.brace_taylor_taylor`: the brace equation `m{m} = 0`.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_taylor`: `[m, m] = 0`.
* `TauCeti.AInfinityAlgebra.gradedCoderiv_hochschildDifferential`: the coderivation of `[m, F]` is
  the graded commutator of the bar differential with the coderivation of `F`.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_hochschildDifferential`: the Hochschild
  differential squares to zero.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* M. Gerstenhaber, *The cohomology structure of an associative ring*, Annals of Mathematics 78
  (1963), 267--288.
-/

public section

universe uR uA

namespace TauCeti

namespace AInfinityAlgebra

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- **The brace equation**: the suspended Taylor map `m` of an `A∞` algebra satisfies
`m{m} = 0`.  This is the square-zero law of the bar differential. -/
@[simp]
theorem brace_taylor_taylor : brace (𝒜.grading.shift 1) 𝒜.taylor 𝒜.taylor 1 = 0 :=
  (gradedCoderiv_comp_self_eq_zero_iff (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree)
    odd_one).1 𝒜.bar_square_zero

/-- The **Hochschild differential** `d F = [m, F]` of a suspended Hochschild cochain `F` of
degree `q`: the Gerstenhaber bracket with the suspended Taylor map `m` of the `A∞` algebra. -/
noncomputable def hochschildDifferential (q : ℤ) (F : ReducedTensorWords R A →ₗ[R] A) :
    ReducedTensorWords R A →ₗ[R] A :=
  gerstenhaberBracket (𝒜.grading.shift 1) 1 q 𝒜.taylor F

theorem hochschildDifferential_def (q : ℤ) (F : ReducedTensorWords R A →ₗ[R] A) :
    𝒜.hochschildDifferential q F =
      gerstenhaberBracket (𝒜.grading.shift 1) 1 q 𝒜.taylor F :=
  (rfl)

/-- The Hochschild differential is additive. -/
theorem hochschildDifferential_add (q : ℤ) (F₁ F₂ : ReducedTensorWords R A →ₗ[R] A) :
    𝒜.hochschildDifferential q (F₁ + F₂) =
      𝒜.hochschildDifferential q F₁ + 𝒜.hochschildDifferential q F₂ :=
  gerstenhaberBracket_add_right _ _ _ _ _

/-- The Hochschild differential is `R`-linear. -/
theorem hochschildDifferential_smul (q : ℤ) (c : R) (F : ReducedTensorWords R A →ₗ[R] A) :
    𝒜.hochschildDifferential q (c • F) = c • 𝒜.hochschildDifferential q F :=
  gerstenhaberBracket_smul_right _ _ _ _ _

/-- The Hochschild differential of the zero cochain vanishes. -/
@[simp]
theorem hochschildDifferential_zero (q : ℤ) : 𝒜.hochschildDifferential q 0 = 0 :=
  gerstenhaberBracket_zero_right _ _ _

/-- The Hochschild differential raises the degree of a cochain by one. -/
theorem isHomogeneous_hochschildDifferential {q : ℤ} {F : ReducedTensorWords R A →ₗ[R] A}
    (hF : LinearMap.IsHomogeneous F (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece q) :
    LinearMap.IsHomogeneous (𝒜.hochschildDifferential q F) (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece (1 + q) :=
  isHomogeneous_gerstenhaberBracket (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree) hF

/-- The Hochschild differential of `m` itself vanishes: `[m, m] = 2 m{m} = 0`. -/
@[simp]
theorem hochschildDifferential_taylor : 𝒜.hochschildDifferential 1 𝒜.taylor = 0 := by
  rw [hochschildDifferential_def, gerstenhaberBracket_def, brace_taylor_taylor, smul_zero,
    sub_zero]

/-- The graded coderivation of `[m, F]` is the graded commutator
`b ∘ D F - (-1)^q • D F ∘ b` of the bar differential `b` with the coderivation of `F`. -/
theorem gradedCoderiv_hochschildDifferential {q : ℤ} {F : ReducedTensorWords R A →ₗ[R] A}
    (hF : LinearMap.IsHomogeneous F (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece q) :
    gradedCoderiv (𝒜.grading.shift 1) (𝒜.hochschildDifferential q F) (1 + q) =
      𝒜.barDifferential ∘ₗ gradedCoderiv (𝒜.grading.shift 1) F q -
        negOnePowCast R q • (gradedCoderiv (𝒜.grading.shift 1) F q ∘ₗ 𝒜.barDifferential) := by
  rw [hochschildDifferential_def,
    gradedCoderiv_gerstenhaberBracket (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree) hF,
    barDifferential_def, one_mul]

/-- **The Hochschild differential squares to zero**: `[m, [m, F]] = 0` for every cochain `F` of
degree `q`. -/
theorem hochschildDifferential_hochschildDifferential {q : ℤ}
    {F : ReducedTensorWords R A →ₗ[R] A}
    (hF : LinearMap.IsHomogeneous F (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece q) :
    𝒜.hochschildDifferential (1 + q) (𝒜.hochschildDifferential q F) = 0 := by
  rw [← letter_comp_gradedCoderiv (𝒜.grading.shift 1)
      (𝒜.hochschildDifferential (1 + q) (𝒜.hochschildDifferential q F)) (1 + (1 + q)),
    gradedCoderiv_hochschildDifferential _ (𝒜.isHomogeneous_hochschildDifferential hF),
    gradedCoderiv_hochschildDifferential _ hF, negOnePowCast_add, negOnePowCast_one]
  -- Expanding, the two terms containing `b ∘ b` vanish and the two copies of `b ∘ D F ∘ b`
  -- cancel.
  simp only [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    ← LinearMap.comp_assoc, barDifferential_sq, LinearMap.zero_comp]
  simp only [LinearMap.comp_assoc, barDifferential_sq, LinearMap.comp_zero]
  module

end AInfinityAlgebra

end TauCeti
