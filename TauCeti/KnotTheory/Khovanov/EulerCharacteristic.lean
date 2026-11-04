/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.Shift
public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.Khovanov.Resolution.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Resolution.Support

/-!
# Khovanov homology and its graded Euler characteristic

The Khovanov homology `Khⁱʲ(D; R)` of a planar oriented code `D` is the cohomology in cochain
degree `i` of the quantum component `j` of the normalized Khovanov complex
`TauCeti.OrientedPDCode.khovanovComplex`. Its graded Euler characteristic is the Laurent
polynomial

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
graded Euler characteristic `1`.

## Main definitions

* `TauCeti.OrientedPDCode.khovanovHomology D hD R i j`: the Khovanov homology `Khⁱʲ(D; R)`.
* `TauCeti.OrientedPDCode.khovanovEulerChar D hD R`: the graded Euler characteristic of the
  Khovanov homology of `D` with coefficients in `R`.

## Main results

* `TauCeti.OrientedPDCode.homologyEulerChar_khovanovComplex`: Euler–Poincaré for each quantum
  component, whose Euler characteristic is the coefficient of `qʲ` in the enhanced state sum.
* `TauCeti.OrientedPDCode.khovanovEulerChar_eq_enhancedStateSum`: `χ_q Kh(D; R)` is the enhanced
  state sum.
* `TauCeti.OrientedPDCode.khovanovEulerChar_eq_mul_eval₂_jonesPolynomial`: for a nonempty diagram,
  `χ_q Kh(D; R) = (q + q⁻¹) J(D)|_{t ^ (1/2) = -q}`.
* `TauCeti.OrientedPDCode.khovanovEulerChar_empty`: the empty diagram has `χ_q Kh = 1`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000).
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §1.3 and §2.2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **Khovanov homology** `Khⁱʲ(D; R)` of a planar oriented code `D`: the cohomology in cochain
degree `i` of the quantum component `j` of the normalized Khovanov complex. -/
def khovanovHomology (i j : ℤ) : ModuleCat.{u} R :=
  (D.khovanovComplex hD R j).homology i

/-- Khovanov homology in bidegree `(i, j)` is the cohomology in degree `i` of the quantum
component `j` of the normalized Khovanov complex. -/
theorem khovanovHomology_def (i j : ℤ) :
    D.khovanovHomology hD R i j = (D.khovanovComplex hD R j).homology i :=
  (rfl)

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
  -- The quantum component `j` is a shift of the quantum component `j - n₊ + 2n₋` of the bracket,
  -- and only finitely many of those are nonzero.
  refine ((D.toPDCode.finite_quantumSupport_khovanovBracket hD R).image
    (· + ((D.positiveCrossingCount : ℤ) - 2 * D.negativeCrossingCount))).subset fun j hj ↦ ?_
  refine ⟨j - D.positiveCrossingCount + 2 * D.negativeCrossingCount, fun hzero ↦ hj ?_,
    by ring⟩
  have hK : IsZero (D.khovanovComplex hD R j) :=
    ((shiftFunctor _ (D.negativeCrossingCount : ℤ)).map_isZero hzero).of_iso
      (D.khovanovComplexShiftIso hD R j)
  refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
  have hX : IsZero ((D.khovanovComplex hD R j).X i) := (HomologicalComplex.eval _ _ i).map_isZero hK
  rw [ModuleCat.finrank_eq_zero_of_isZero (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology,
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
      (fun _ ↦ by rw [khovanovComplex_X]; infer_instance)
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

/-- The empty diagram has graded Euler characteristic of Khovanov homology `1`, over a Noetherian
ring with the rank-nullity property, such as `ℤ` or a field. -/
@[simp]
theorem khovanovEulerChar_empty (hD : empty.toPDCode.IsPlanar) :
    empty.khovanovEulerChar hD R = 1 := by
  rw [khovanovEulerChar_eq_enhancedStateSum, enhancedStateSum_empty]

end TauCeti.OrientedPDCode
