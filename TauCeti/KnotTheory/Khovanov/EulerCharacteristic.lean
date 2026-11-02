/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Homology
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The normalized Khovanov Euler polynomial

The graded Euler polynomial is formed from the ranks of the actual normalized cohomology
modules. Finite quantum and cochain support make its coefficients honest finite alternating
sums. Over the integers these ranks ignore torsion; over a field they are dimensions.

Euler–Poincaré identifies this polynomial with the enhanced state sum over any Noetherian
commutative ring satisfying rank-nullity, including the integers and every field. For a
nonempty planar diagram it is `(q + q⁻¹)` times the native Jones polynomial under `T ↦ -q`.
The empty diagram has Euler polynomial `1`, separately from that nonempty normalization.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §§1.3–2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  (R : Type u) [CommRing R]

/-- Normalization multiplies the homology Euler characteristic by `(-1)^n₋` and translates
the quantum index. This is an equality of alternating ranks of actual cohomology modules. -/
theorem homologyEulerChar_khovanovComplex (j : ℤ) :
    (D.khovanovComplex hD R j).homologyEulerChar =
      ((D.negativeCrossingCount : ℤ).negOnePow : ℤ) *
        (D.toPDCode.khovanovBracket hD R
          (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).homologyEulerChar := by
  simp only [homologyEulerChar, GradedObject.eulerChar, ComplexShape.eulerCharSignsUpInt_χ,
    mul_finsum]
  apply finsum_eq_of_bijective (fun i : ℤ ↦ i + D.negativeCrossingCount)
    (Equiv.addRight (D.negativeCrossingCount : ℤ)).bijective
  intro i
  rw [(D.khovanovHomologyBracketIso hD R i j).toLinearEquiv.finrank_eq]
  have hs : (D.negativeCrossingCount : ℤ).negOnePow *
      (i + D.negativeCrossingCount).negOnePow = i.negOnePow := by
    rw [Int.negOnePow_add, mul_left_comm]
    simp
  rw [← mul_assoc, ← Units.val_mul, hs]

section Nontrivial

variable [Nontrivial R]

private theorem finite_support_homologyEulerChar :
    (Function.support (fun j ↦ (D.khovanovComplex hD R j).homologyEulerChar)).Finite := by
  refine (Set.finite_Icc
    ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount -
      D.toPDCode.stateLoopCount (PDCode.cubeState ∅))
    ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount + n +
      D.toPDCode.stateLoopCount (PDCode.cubeState Finset.univ))).subset ?_
  intro j hj
  by_contra h
  apply hj
  simp only [homologyEulerChar, GradedObject.eulerChar]
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  have hz := D.isZero_khovanovHomology_of_quantum_notMem_Icc hD R h i
  rw [ModuleCat.finrank_eq_zero_of_isZero hz]
  simp

/-- The graded Euler polynomial of normalized Khovanov cohomology. Over `ℤ` it uses ranks of
free parts; over a field it uses dimensions. Its coefficients are alternating cohomology ranks,
not the state sum by definition. -/
def khovanovEulerPolynomial : ℤ[T;T⁻¹] :=
  AddMonoidAlgebra.coeffEquiv.symm (Finsupp.ofSupportFinite
    (fun j ↦ (D.khovanovComplex hD R j).homologyEulerChar)
    (D.finite_support_homologyEulerChar hD R))

/-- A coefficient of the Euler polynomial is the Euler characteristic of the corresponding
normalized quantum-component cohomology. -/
@[simp]
theorem coeff_khovanovEulerPolynomial (j : ℤ) :
    (D.khovanovEulerPolynomial hD R).coeff j =
      (D.khovanovComplex hD R j).homologyEulerChar := by
  rfl

/-- The coefficient formula as an honest finite alternating sum of ranks of `Khⁱʲ`.
Over a field these ranks are dimensions. -/
theorem coeff_khovanovEulerPolynomial_eq_sum (j : ℤ) :
    (D.khovanovEulerPolynomial hD R).coeff j =
      ∑ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
        (i.negOnePow : ℤ) * Module.finrank R (D.khovanovHomology hD R i j) := by
  rw [coeff_khovanovEulerPolynomial,
    homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset _ _
      (finrankSupport_homology_subset_Icc (D.khovanovComplex hD R j)
        (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount)]
  rfl

end Nontrivial

variable [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- Euler–Poincaré for the normalized complex identifies its Euler polynomial with the
native enhanced state sum. -/
theorem khovanovEulerPolynomial_eq_enhancedStateSum :
    D.khovanovEulerPolynomial hD R = D.enhancedStateSum := by
  ext j
  rw [coeff_khovanovEulerPolynomial, homologyEulerChar_khovanovComplex,
    coeff_enhancedStateSum_eq_homologyEulerChar_khovanovBracket D hD R]
  congr 3
  omega

/-- The graded Euler characteristic of normalized Khovanov cohomology recovers the native
Jones polynomial after `T ↦ -q`, with the extra circle factor for a nonempty link. -/
theorem khovanovEulerPolynomial_eq_mul_eval₂_jonesPolynomial
    (h : 0 < D.toPDCode.componentCount) :
    D.khovanovEulerPolynomial hD R =
      (T 1 + T (-1)) * eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial := by
  rw [khovanovEulerPolynomial_eq_enhancedStateSum]
  exact D.enhancedStateSum_eq_mul_eval₂_jonesPolynomial h

/-- The empty diagram has Euler polynomial `1`, without using the nonempty Jones formula. -/
@[simp]
theorem khovanovEulerPolynomial_empty (h : (empty : OrientedPDCode 0).toPDCode.IsPlanar) :
    empty.khovanovEulerPolynomial h R = 1 := by
  rw [khovanovEulerPolynomial_eq_enhancedStateSum, enhancedStateSum_empty]

end TauCeti.OrientedPDCode
