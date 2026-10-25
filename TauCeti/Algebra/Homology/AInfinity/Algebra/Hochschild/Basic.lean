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
* `TauCeti.AInfinityAlgebra.hochschildDifferential_eq_brace_sub`: `[m, F] = m{F} - (-1)^q F{m}`.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_taylor`: `[m, m] = 0`.
* `TauCeti.AInfinityAlgebra.gradedCoderiv_hochschildDifferential`: the coderivation of `[m, F]` is
  the graded commutator of the bar differential with the coderivation of `F`.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_hochschildDifferential`: the Hochschild
  differential squares to zero.
* `TauCeti.AInfinityAlgebra.brace_brace_sub_brace_brace_eq_hochschildDifferential`: the pre-Lie
  identity `m{ψ}{ψ} - m{ψ{ψ}} = δψ{ψ} + ψ{δψ} - δ(ψ{ψ})` for a cochain `ψ` of degree zero.

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

/-- The Hochschild differential in terms of braces: `[m, F] = m{F} - (-1)^q F{m}` for a cochain
`F` of degree `q`. -/
theorem hochschildDifferential_eq_brace_sub (q : ℤ) (F : ReducedTensorWords R A →ₗ[R] A) :
    𝒜.hochschildDifferential q F =
      brace (𝒜.grading.shift 1) 𝒜.taylor F q -
        negOnePowCast R q • brace (𝒜.grading.shift 1) F 𝒜.taylor 1 := by
  rw [hochschildDifferential_def, gerstenhaberBracket_def, one_mul]

/-- The Hochschild differential of a cochain `F` of degree zero on a word `z`:
`[m, F] z = m (D F z) - F{m} z`, for `D F` the ungraded Taylor expansion of `F`. -/
theorem hochschildDifferential_zero_apply (F : ReducedTensorWords R A →ₗ[R] A)
    (z : ReducedTensorWords R A) :
    𝒜.hochschildDifferential 0 F z =
      𝒜.taylor (coderiv R F z) - brace (𝒜.grading.shift 1) F 𝒜.taylor 1 z := by
  rw [hochschildDifferential_eq_brace_sub, negOnePowCast_zero, one_smul, LinearMap.sub_apply,
    brace_zero_apply]

/-- The Hochschild differential is additive. -/
@[simp]
theorem hochschildDifferential_add (q : ℤ) (F₁ F₂ : ReducedTensorWords R A →ₗ[R] A) :
    𝒜.hochschildDifferential q (F₁ + F₂) =
      𝒜.hochschildDifferential q F₁ + 𝒜.hochschildDifferential q F₂ :=
  gerstenhaberBracket_add_right _ _ _ _ _

/-- The Hochschild differential is `R`-linear. -/
@[simp]
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
@[simp]
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

/-- The Hochschild differential is a graded derivation of the Gerstenhaber bracket.
All degrees are suspended degrees, so the sign on the second term is `(-1)^p`. -/
theorem hochschildDifferential_gerstenhaberBracket {p q : ℤ}
    {F G : ReducedTensorWords R A →ₗ[R] A}
    (hF : LinearMap.IsHomogeneous F (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece p)
    (hG : LinearMap.IsHomogeneous G (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece q) :
    𝒜.hochschildDifferential (p + q) (gerstenhaberBracket (𝒜.grading.shift 1) p q F G) =
      gerstenhaberBracket (𝒜.grading.shift 1) (1 + p) q (𝒜.hochschildDifferential p F) G +
        negOnePowCast R p •
          gerstenhaberBracket (𝒜.grading.shift 1) p (1 + q) F
            (𝒜.hochschildDifferential q G) := by
  simpa only [hochschildDifferential_def, one_mul] using
    leibniz_gerstenhaberBracket (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree) hF hG

/-- The pre-Lie identity for the Taylor map and a cochain `ψ` of degree zero, in terms of the
Hochschild differential `δ`: `m{ψ}{ψ} - m{ψ{ψ}} = δψ{ψ} + ψ{δψ} - δ(ψ{ψ})`.  This is the
identity behind Gerstenhaber's homotopy commutativity of the cup product. -/
theorem brace_brace_sub_brace_brace_eq_hochschildDifferential
    {ψ : ReducedTensorWords R A →ₗ[R] A}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece (𝒜.grading.shift 1))
      (𝒜.grading.shift 1).piece 0) :
    brace (𝒜.grading.shift 1) (brace (𝒜.grading.shift 1) 𝒜.taylor ψ 0) ψ 0 -
        brace (𝒜.grading.shift 1) 𝒜.taylor (brace (𝒜.grading.shift 1) ψ ψ 0) 0 =
      brace (𝒜.grading.shift 1) (𝒜.hochschildDifferential 0 ψ) ψ 0 +
        brace (𝒜.grading.shift 1) ψ (𝒜.hochschildDifferential 0 ψ) 1 -
        𝒜.hochschildDifferential 0 (brace (𝒜.grading.shift 1) ψ ψ 0) := by
  have e₁ := 𝒜.hochschildDifferential_eq_brace_sub 0 ψ
  have e₂ := 𝒜.hochschildDifferential_eq_brace_sub 0 (brace (𝒜.grading.shift 1) ψ ψ 0)
  have e₃ := brace_brace_sub_smul_brace_brace ψ
    (𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree) hψ
  rw [negOnePowCast_zero, one_smul] at e₁ e₂
  rw [mul_zero, negOnePowCast_zero, one_smul, add_zero, ← hochschildDifferential_def] at e₃
  rw [eq_sub_iff_add_eq] at e₁ e₂
  rw [sub_eq_iff_eq_add] at e₃
  rw [← e₁, brace_add_left, e₃, ← e₂]
  abel

end AInfinityAlgebra

end TauCeti
