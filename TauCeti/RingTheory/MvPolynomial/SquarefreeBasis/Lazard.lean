/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.SquarefreeBasis
public import TauCeti.RingTheory.MvPolynomial.Lazard.Map

/-!
# Lazard content reconstruction from squarefree bases

Moving the distinguished polynomial variable into the coefficient ring preserves the
squarefree-basis reconstruction under multiplicative Lazard evaluation. The scalar factor
contains the evaluated content and a unit, and the removed base exponents are the content
exponents plus a weighted sum of the basis exponents. The weights do not depend on the base
point, so invariant content and basis exponents give invariant input exponents.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Sections 2 and 5.
The factorization is `Finset.IsSquarefreeBasis.exists_eq_C_content_mul_unit_mul_prod`;
the multiplicative evaluation is `MvPolynomial.lazardEvalHom`.
-/

public section

open MvPolynomial Polynomial

namespace Finset

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
  {F B : Finset (Polynomial (MvPolynomial (Fin n) R))}

local notation "swap" =>
  (AlgEquiv.trans (AlgEquiv.symm (optionEquivLeft R (Fin n)))
    (optionEquivRight R (Fin n)))

namespace IsSquarefreeBasis

section Content

variable [NormalizedGCDMonoid (MvPolynomial (Fin n) R)]

/-- The Lazard evaluation of each input is a scalar times the product of powers
of the Lazard evaluations of its basis factors. The scalar contains the Lazard-evaluated
content and a unit, and the same factorization works at every base point. -/
theorem exists_lazardEval_eq_C_mul_prod (hB : F.IsSquarefreeBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) :
    ∃ (u : (MvPolynomial (Fin n) R)ˣ) (e : Polynomial (MvPolynomial (Fin n) R) → ℕ),
      ∀ a : Fin n → R, (swap f).lazardEval (Polynomial.C ∘ a) =
        Polynomial.C (f.content.lazardEval a * (u : MvPolynomial (Fin n) R).lazardEval a) *
          ∏ b ∈ B, (swap b).lazardEval (Polynomial.C ∘ a) ^ e b := by
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  refine ⟨u, e, fun a ↦ ?_⟩
  conv_lhs => rw [hfe]
  rw [map_mul, optionEquivRight_optionEquivLeft_symm_C, lazardEval_mul,
    lazardEval_map Polynomial.C Polynomial.C_injective, lazardEval_mul]
  congr 1
  simp only [map_prod, map_pow]
  simpa only [map_pow, lazardEvalHom_apply] using
    map_prod (lazardEvalHom (Polynomial.C ∘ a)) (fun b ↦ swap b ^ e b) B

/-- For a nonzero input, the removed base exponents are the content exponents plus the
weighted sum of the basis exponents. The weights do not depend on the base point. -/
theorem exists_lazardExponent_eq_content_add_sum (hB : F.IsSquarefreeBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) (hf0 : f ≠ 0) :
    ∃ e : Polynomial (MvPolynomial (Fin n) R) → ℕ, ∀ a : Fin n → R,
      (swap f).lazardExponent (Polynomial.C ∘ a) = f.content.lazardExponent a +
        ∑ b ∈ B, e b • (swap b).lazardExponent (Polynomial.C ∘ a) := by
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  refine ⟨e, fun a ↦ ?_⟩
  have hc : f.content ≠ 0 := fun h ↦ hf0 (content_eq_zero_iff.mp h)
  have hu : (u : MvPolynomial (Fin n) R).lazardExponent a = 0 :=
    lazardExponent_eq_zero_of_eval_ne_zero (u.isUnit.map (MvPolynomial.eval a)).ne_zero
  have hb : ∀ b ∈ B, swap b ≠ 0 := fun b hb ↦
    EmbeddingLike.map_ne_zero_iff.mpr (hB.isPrimitive b hb).ne_zero
  have hc' : MvPolynomial.map Polynomial.C (f.content * (u : MvPolynomial (Fin n) R)) ≠ 0 := by
    exact (map_ne_zero_iff _ (MvPolynomial.map_injective Polynomial.C
      Polynomial.C_injective)).mpr (mul_ne_zero hc u.ne_zero)
  conv_lhs => rw [hfe, map_mul, optionEquivRight_optionEquivLeft_symm_C]
  simp only [map_prod, map_pow]
  rw [lazardExponent_mul hc'
      (Finset.prod_ne_zero_iff.mpr fun b hb' ↦ pow_ne_zero _ (hb b hb')),
    lazardExponent_map Polynomial.C Polynomial.C_injective,
    lazardExponent_mul hc u.ne_zero, hu, add_zero,
    lazardExponent_prod B _ (fun b hb' ↦ pow_ne_zero _ (hb b hb'))]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun b hb' ↦
    lazardExponent_pow (hb b hb') _ _)

/-- Invariant content and basis exponents give invariant input exponents, including
zero inputs. No connectedness or nonnullification hypothesis is required. -/
theorem lazardExponent_eq (hB : F.IsSquarefreeBasis B)
    {f : Polynomial (MvPolynomial (Fin n) R)} (hf : f ∈ F) {a a' : Fin n → R}
    (hc : f.content.lazardExponent a = f.content.lazardExponent a')
    (hb : ∀ b ∈ B, (swap b).lazardExponent (Polynomial.C ∘ a) =
      (swap b).lazardExponent (Polynomial.C ∘ a')) :
    (swap f).lazardExponent (Polynomial.C ∘ a) =
      (swap f).lazardExponent (Polynomial.C ∘ a') := by
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨e, he⟩ := hB.exists_lazardExponent_eq_content_add_sum hf hf0
  rw [he a, he a', hc]
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun b hb' ↦ congrArg (e b • ·) (hb b hb'))

end Content

end IsSquarefreeBasis

end Finset
