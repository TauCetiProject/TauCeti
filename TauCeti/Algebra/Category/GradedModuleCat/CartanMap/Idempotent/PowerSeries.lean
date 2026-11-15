/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Matrix
public import TauCeti.Algebra.Polynomial.Laurent.Polynomial
public import TauCeti.Algebra.Polynomial.Laurent.Symmetric
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The graded Cartan matrix over polynomials and power series

For a nonnegatively graded finite-dimensional algebra with semisimple degree-zero part,
the Cartan matrix in the primitive-idempotent bases has no negative powers and has
constant matrix the identity. It therefore has polynomial entries and is invertible over
`ℤ⟦X⟧`, without any finite-projective-dimension or Ext-vanishing hypothesis.

This is the coefficient ring in which Cartan--Poincaré identities for infinite linear
resolutions can be interpreted. Formal invertibility must not be confused with invertibility
over Laurent polynomials: for example, `1 + X` is a power-series unit but not a Laurent unit.
The field need not split the simple modules; the division-endomorphism dimensions cancel
in the constant coefficient calculation.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 2.11, for the Hilbert and Poincaré matrix identity in formal power series.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for graded Cartan
  matrices. Rows index simple modules and columns index left projective modules.
-/

public section

noncomputable section

namespace TauCeti

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsSemisimpleRing (𝒜 0)]
  {I : Type uI} [Fintype I] {e : I → A}
  (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

/-- The polynomial graded Cartan matrix in the primitive-idempotent bases.
Mapping its entries by `Polynomial.toLaurent` recovers the original Cartan matrix. -/
def gradedIdempotentCartanPolynomial : Matrix I I (Polynomial ℤ) :=
  (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasisOfPrimitive he hI hprim hnoniso)
    (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso)).map LaurentPolynomial.trunc

/-- Polynomialization retains every coefficient: the discarded negative coefficients vanish. -/
@[simp]
theorem map_toLaurent_gradedIdempotentCartanPolynomial :
    (gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso).map Polynomial.toLaurent =
      gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasisOfPrimitive he hI hprim hnoniso)
        (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso) := by
  ext i j : 2
  obtain ⟨p, hp⟩ := exists_toLaurent_eq_iff.mpr
    (fun n hn => coeff_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive_of_neg
      he he₀ hI hneg hprim hnoniso i j hn)
  simp only [gradedIdempotentCartanPolynomial, Matrix.map_apply, ← hp,
    Polynomial.trunc_toLaurent]

/-- The polynomial Cartan coefficients are the original Laurent coefficients. -/
@[simp]
theorem coeff_gradedIdempotentCartanPolynomial (i j : I) (n : ℕ) :
    (gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso i j).coeff n =
      (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasisOfPrimitive he hI hprim hnoniso)
        (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso) i j).coeff n := by
  simp [gradedIdempotentCartanPolynomial]

variable [DecidableEq I]

/-- The polynomial Cartan matrix evaluates to the identity at the origin. -/
@[simp]
theorem map_eval_zero_gradedIdempotentCartanPolynomial :
    (gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso).map
      (Polynomial.eval 0) = 1 := by
  ext i j
  simp only [Matrix.map_apply, ← Polynomial.coeff_zero_eq_eval_zero,
    coeff_gradedIdempotentCartanPolynomial, Nat.cast_zero,
    coeff_zero_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive, Matrix.one_apply]

/-- The polynomial Cartan matrix is invertible after passing to formal power series.
No eventual Ext-vanishing or finite-resolution assumption is required. -/
theorem isUnit_gradedIdempotentCartanPolynomial_powerSeries :
    IsUnit (Polynomial.coeToPowerSeries.ringHom.mapMatrix
      (gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso)) := by
  rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have h : PowerSeries.constantCoeff.mapMatrix (Polynomial.coeToPowerSeries.ringHom.mapMatrix
      (gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso)) = 1 := by
    ext i j
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.constantCoeff_coe,
      ← Polynomial.coeff_zero_eq_eval_zero] using
      congrFun (congrFun (map_eval_zero_gradedIdempotentCartanPolynomial
        he he₀ hI hneg hprim hnoniso) i) j
  rw [h, Matrix.det_one]
  exact isUnit_one

/-- The graded Cartan determinant is nonzero in Laurent polynomials, even when it is not a unit.
This is independent of the Cartan comparison theorem for finite resolutions. -/
theorem det_gradedCartanMatrix_gradedIdempotentProjectiveBasisOfPrimitive_ne_zero :
    (gradedCartanMatrix 𝒜 (gradedIdempotentProjectiveBasisOfPrimitive he hI hprim hnoniso)
      (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso)).det ≠ 0 := by
  have hp : (gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso).det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det
      (map_eval_zero_gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso)
    rw [← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      hz, map_zero, Matrix.det_one] at h
    exact zero_ne_one h
  rw [← map_toLaurent_gradedIdempotentCartanPolynomial he he₀ hI hneg hprim hnoniso,
    ← Polynomial.toLaurent.mapMatrix_apply, ← RingHom.map_det, Polynomial.toLaurent_ne_zero]
  exact hp

end TauCeti
