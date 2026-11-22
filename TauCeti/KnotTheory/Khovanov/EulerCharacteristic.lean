/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import TauCeti.Algebra.Homology.EulerCharacteristic.Shift
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Unlink
import Mathlib.Algebra.EuclideanDomain.Int
import TauCeti.KnotTheory.Khovanov.EnhancedState.Evaluation

/-!
# Khovanov homology and its graded Euler characteristic

The Khovanov homology `Khⁱʲ(D; R)` of a planar oriented code `D`, defined in
`TauCeti.KnotTheory.Khovanov.Homology`, is the cohomology in cochain degree `i` of the quantum
component `j` of the normalized Khovanov complex `TauCeti.OrientedPDCode.khovanovComplex`.
Its graded Euler characteristic is the Laurent polynomial

`χ_q Kh(D; R) = ∑ⱼ (∑ᵢ (-1) ^ i rank Khⁱʲ(D; R)) qʲ`,

with `q = T` (`TauCeti.OrientedPDCode.khovanovEulerChar`). Its coefficients are Mathlib's homology
Euler characteristics `HomologicalComplex.homologyEulerChar` of the quantum components of the
normalized Khovanov complex. Only finitely many of them are nonzero, because the bracket has
finite quantum support.

Over a Noetherian ring with the rank-nullity property, such as `ℤ` or a field, the ranks are the
ranks of finitely generated modules, the free ranks in the case of `ℤ`. Euler–Poincaré then
computes each coefficient from the terms of the complex instead of its homology, and the
normalized complex is a cochain shift of the bracket by `n₋`, so the coefficient of `qʲ` is the
signed count of enhanced states of quantum degree `j`. In other words, `χ_q Kh(D; R)` is the
enhanced state sum (`TauCeti.OrientedPDCode.khovanovEulerChar_eq_enhancedStateSum`). For a
nonempty diagram this is Khovanov's theorem that the graded Euler characteristic is `(q + q⁻¹)`
times the Jones polynomial at `t ^ (1/2) = -q`
(`TauCeti.OrientedPDCode.khovanovEulerChar_eq_mul_eval₂_jonesPolynomial`). The empty diagram has
graded Euler characteristic `1`. At `q = 1`, `χ_q Kh(D; R)` evaluates to `2 ^ c`, hence is nonzero
and has a nonzero coefficient in some quantum degree `j ≡ c (mod 2)` for every planar diagram,
including the empty diagram.

## Main definitions

* `TauCeti.OrientedPDCode.khovanovEulerChar D hD R`: the graded Euler characteristic of the
  Khovanov homology of `D` with coefficients in `R`.

## Main results

* `TauCeti.OrientedPDCode.homologyEulerChar_khovanovComplex_eq_negOnePow_mul`: normalization
  multiplies the bracket homology Euler characteristic by `(-1)^n₋` and translates the quantum
  index.
* `TauCeti.OrientedPDCode.coeff_khovanovEulerChar_eq_sum`: each coefficient is the finite
  alternating sum of homology ranks over the cochain interval `[-n₋, n₊]`.
* `TauCeti.OrientedPDCode.coeff_khovanovEulerChar_eq_zero_of_mod_two_ne`: over any nontrivial
  commutative ring, the coefficient of `qʲ` vanishes when `j % 2 ≠ D.componentCount % 2`.
* `TauCeti.OrientedPDCode.homologyEulerChar_khovanovComplex`: Euler–Poincaré for each quantum
  component, whose Euler characteristic is the coefficient of `qʲ` in the enhanced state sum.
* `TauCeti.OrientedPDCode.khovanovEulerChar_eq_enhancedStateSum`: `χ_q Kh(D; R)` is the enhanced
  state sum.
* `TauCeti.OrientedPDCode.khovanovEulerChar_eq_mul_eval₂_jonesPolynomial`: for a nonempty diagram,
  `χ_q Kh(D; R) = (q + q⁻¹) J(D)|_{t ^ (1/2) = -q}`.
* `TauCeti.OrientedPDCode.khovanovEulerChar_empty`: the empty diagram has `χ_q Kh = 1`.
* `TauCeti.OrientedPDCode.eval₂_one_khovanovEulerChar`,
  `TauCeti.OrientedPDCode.khovanovEulerChar_ne_zero`, and
  `TauCeti.OrientedPDCode.exists_coeff_khovanovEulerChar_ne_zero` (with specializations
  `khovanovEulerChar_int_ne_zero` and `khovanovEulerChar_rat_ne_zero`): `χ_q Kh(D; R)` evaluates
  to `2 ^ c` at `q = 1`, is nonzero, and has a nonzero coefficient in some parity-compatible quantum
  degree.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §1.3 and §2.2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

section Ring

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- Normalization multiplies the homology Euler characteristic by `(-1)^n₋` and translates
the quantum index. This is an equality of alternating ranks of actual cohomology modules. -/
theorem homologyEulerChar_khovanovComplex_eq_negOnePow_mul (j : ℤ) :
    (D.khovanovComplex hD R j).homologyEulerChar =
      ((D.negativeCrossingCount : ℤ).negOnePow : ℤ) *
        (D.toPDCode.khovanovBracket hD R
          (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).homologyEulerChar := by
  simp only [homologyEulerChar, GradedObject.eulerChar, ComplexShape.eulerCharSignsUpInt_χ,
    mul_finsum]
  apply finsum_eq_of_bijective (fun i : ℤ ↦ i + D.negativeCrossingCount)
    (Equiv.addRight (D.negativeCrossingCount : ℤ)).bijective
  intro i
  have he := (D.khovanovHomologyBracketIso hD R i j).toLinearEquiv.finrank_eq
  rw [khovanovHomology_def] at he
  rw [he]
  have hs : (D.negativeCrossingCount : ℤ).negOnePow *
      (i + D.negativeCrossingCount).negOnePow = i.negOnePow := by
    rw [Int.negOnePow_add, mul_left_comm]
    simp
  rw [← mul_assoc, ← Units.val_mul, hs]

/-- The Euler characteristic of the terms of the quantum component `j` of the normalized Khovanov
complex is `(-1) ^ n₋` times that of the quantum component `j - (n₊ - 2n₋)` of the bracket. -/
theorem eulerChar_khovanovComplex (j : ℤ) :
    (D.khovanovComplex hD R j).eulerChar = ((D.negativeCrossingCount : ℤ).negOnePow : ℤ) *
      (D.toPDCode.khovanovBracket hD R
        (j - (D.positiveCrossingCount - 2 * D.negativeCrossingCount))).eulerChar := by
  have hj : j - ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount) =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount := by
    ring
  rw [hj, ← CochainComplex.eulerChar_shift]
  exact HomologicalComplex.eulerChar_eq_of_iso (D.khovanovComplexShiftIso hD R j)

section Nontrivial

variable [Nontrivial R]

/-- Only finitely many quantum components of the normalized Khovanov complex have a nonzero
homology Euler characteristic. -/
theorem finite_support_homologyEulerChar_khovanovComplex :
    (Function.support fun j ↦ (D.khovanovComplex hD R j).homologyEulerChar).Finite := by
  refine (D.finite_quantumSupport_khovanovComplex hD R).subset fun j hj hK ↦ hj ?_
  exact finsum_eq_zero_of_forall_eq_zero fun i ↦ by
    rw [ModuleCat.finrank_eq_zero_of_isZero
      (ExactAt.of_isZero ((eval _ _ i).map_isZero hK)).isZero_homology,
      Nat.cast_zero, mul_zero]

/-- **The graded Euler characteristic of Khovanov homology** `χ_q Kh(D; R)` of a planar oriented
code `D`: the Laurent polynomial in `q = T` whose coefficient of `qʲ` is the alternating sum
`∑ᵢ (-1) ^ i rank Khⁱʲ(D; R)`, Mathlib's homology Euler characteristic of the quantum component `j`
of the normalized Khovanov complex. -/
def khovanovEulerChar : ℤ[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.ofSupportFinite
    (fun j ↦ (D.khovanovComplex hD R j).homologyEulerChar)
    (D.finite_support_homologyEulerChar_khovanovComplex hD R)

/-- The coefficient of `qʲ` in the graded Euler characteristic of Khovanov homology is the
homology Euler characteristic of the quantum component `j` of the normalized Khovanov complex. -/
@[simp]
theorem coeff_khovanovEulerChar (j : ℤ) :
    (D.khovanovEulerChar hD R).coeff j = (D.khovanovComplex hD R j).homologyEulerChar := by
  rw [khovanovEulerChar, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.ofSupportFinite_coe]

/-- The coefficient formula as an honest finite alternating sum of ranks of `Khⁱʲ`.
Over a field these ranks are dimensions. -/
theorem coeff_khovanovEulerChar_eq_sum (j : ℤ) :
    (D.khovanovEulerChar hD R).coeff j =
      ∑ i ∈ Finset.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount,
        (i.negOnePow : ℤ) * Module.finrank R (D.khovanovHomology hD R i j) := by
  rw [coeff_khovanovEulerChar,
    homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset _ _
      (finrankSupport_homology_subset_Icc (D.khovanovComplex hD R j)
        (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ComplexShape.eulerCharSignsUpInt_χ]

/-- Over any nontrivial commutative ring `R`, the coefficient of `q ^ j` in
`D.khovanovEulerChar hD R` vanishes whenever `j % 2 ≠ D.componentCount % 2`. -/
theorem coeff_khovanovEulerChar_eq_zero_of_mod_two_ne {j : ℤ}
    (hj : j % 2 ≠ (D.componentCount : ℤ) % 2) :
    (D.khovanovEulerChar hD R).coeff j = 0 := by
  rw [D.coeff_khovanovEulerChar_eq_sum hD R j]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [ModuleCat.finrank_eq_zero_of_isZero (D.isZero_khovanovHomology_of_mod_two_ne hD R i hj),
    Nat.cast_zero, mul_zero]

/-- The empty diagram has graded Euler characteristic `1` over every nontrivial
commutative ring. -/
@[simp]
theorem khovanovEulerChar_empty (h : (empty : OrientedPDCode 0).toPDCode.IsPlanar) :
    empty.khovanovEulerChar h R = 1 := by
  classical
  have hn : empty.negativeCrossingCount = 0 := by
    have := empty.positiveCrossingCount_add_negativeCrossingCount
    omega
  have hp : empty.positiveCrossingCount = 0 := by
    have := empty.positiveCrossingCount_add_negativeCrossingCount
    omega
  ext j
  rw [coeff_khovanovEulerChar_eq_sum]
  simp only [hn, hp, Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton,
    Int.negOnePow_zero, Units.val_one, one_mul]
  rw [khovanovHomology_def, ← coeff_pow_eq_finrank_homology_khovanovComplex empty h R j]
  simp [← card_crossinglessComponents, crossinglessComponents_empty]

end Nontrivial

variable [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- **Euler–Poincaré for Khovanov homology**: over a Noetherian ring with the rank-nullity property,
such as `ℤ` or a field, the homology Euler characteristic of the quantum component `j` of the
normalized Khovanov complex is the coefficient of `qʲ` in the enhanced state sum, the signed count
of enhanced states of quantum degree `j`. -/
theorem homologyEulerChar_khovanovComplex (j : ℤ) :
    (D.khovanovComplex hD R j).homologyEulerChar = D.enhancedStateSum.coeff j := by
  rw [coeff_enhancedStateSum_eq_homologyEulerChar_khovanovBracket D hD R,
    ← CochainComplex.eulerChar_eq_homologyEulerChar (D.toPDCode.khovanovBracket hD R _)
      (fun _ ↦ inferInstance) 0 n,
    ← eulerChar_khovanovComplex,
    CochainComplex.eulerChar_eq_homologyEulerChar _
      (fun _ ↦ inferInstance)
      (-D.negativeCrossingCount) D.positiveCrossingCount]

/-- **The graded Euler characteristic of Khovanov homology is the enhanced state sum**, over a
Noetherian ring with the rank-nullity property, such as `ℤ` or a field. -/
theorem khovanovEulerChar_eq_enhancedStateSum : D.khovanovEulerChar hD R = D.enhancedStateSum :=
  AddMonoidAlgebra.coeff_injective <| Finsupp.ext fun j ↦ by
    rw [coeff_khovanovEulerChar, homologyEulerChar_khovanovComplex]

/-- **Khovanov's theorem**: the graded Euler characteristic of the Khovanov homology of a nonempty
planar oriented code is `(q + q⁻¹)` times its Jones polynomial at `t ^ (1/2) = -q`, over a
Noetherian ring with the rank-nullity property, such as `ℤ` or a field. The hypothesis
`0 < componentCount` says that the diagram is nonempty; the empty diagram has graded Euler
characteristic `1` (`TauCeti.OrientedPDCode.khovanovEulerChar_empty`). -/
theorem khovanovEulerChar_eq_mul_eval₂_jonesPolynomial (h : 0 < D.toPDCode.componentCount) :
    D.khovanovEulerChar hD R =
      (T 1 + T (-1)) * eval₂ (Int.castRingHom ℤ[T;T⁻¹]) (-genericUnit ℤ) D.jonesPolynomial := by
  rw [khovanovEulerChar_eq_enhancedStateSum, enhancedStateSum_eq_mul_eval₂_jonesPolynomial D h]

/-- **At `q = 1`, the graded Euler characteristic `χ_q Kh(D; R)` equals `2 ^ c`**, for every
planar oriented diagram over any Noetherian commutative ring `R` satisfying rank-nullity. -/
theorem eval₂_one_khovanovEulerChar :
    eval₂ (RingHom.id ℤ) 1 (D.khovanovEulerChar hD R) = (2 : ℤ) ^ D.componentCount := by
  rw [D.khovanovEulerChar_eq_enhancedStateSum hD R, D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- **The graded Euler characteristic of Khovanov homology is nonzero** for every planar oriented
diagram (including the empty diagram) over any Noetherian commutative ring `R` satisfying
rank-nullity. -/
theorem khovanovEulerChar_ne_zero : D.khovanovEulerChar hD R ≠ 0 := by
  intro hzero
  have heval := D.eval₂_one_khovanovEulerChar hD R
  rw [hzero, map_zero] at heval
  exact (by positivity : (0 : ℤ) < (2 : ℤ) ^ D.componentCount).ne heval

/-- For every planar oriented PD-code `D`, some quantum degree `j ≡ D.componentCount (mod 2)` has a
nonzero coefficient in `D.khovanovEulerChar hD R`. -/
theorem exists_coeff_khovanovEulerChar_ne_zero :
    ∃ j : ℤ, j % 2 = (D.componentCount : ℤ) % 2 ∧ (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
  have ⟨j, hj⟩ : ∃ j : ℤ, (D.khovanovEulerChar hD R).coeff j ≠ 0 := by
    by_contra! hall
    exact D.khovanovEulerChar_ne_zero hD R
      (AddMonoidAlgebra.coeff_injective <| Finsupp.ext hall)
  exact ⟨j, by_contra fun hmod ↦ hj (D.coeff_khovanovEulerChar_eq_zero_of_mod_two_ne hD R hmod), hj⟩

end Ring

section IntAndRat

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)

/-- The integral graded Euler characteristic `χ_q Kh(D; ℤ)` of any planar oriented PD-code is
nonzero. -/
theorem khovanovEulerChar_int_ne_zero : D.khovanovEulerChar hD ℤ ≠ 0 :=
  D.khovanovEulerChar_ne_zero hD ℤ

/-- The rational graded Euler characteristic `χ_q Kh(D; ℚ)` of any planar oriented PD-code is
nonzero. -/
theorem khovanovEulerChar_rat_ne_zero : D.khovanovEulerChar hD ℚ ≠ 0 :=
  D.khovanovEulerChar_ne_zero hD ℚ

end IntAndRat

end TauCeti.OrientedPDCode
