/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Normed.Operator.Compact.Calkin

/-!
# Fredholm operators are the units of the Calkin algebra

Atkinson's theorem (`TauCeti.isFredholm_iff_exists_isCompactOperator_comp_sub_one`) says that an
operator on a Banach space is Fredholm exactly when it is invertible modulo compact operators.
In the Calkin algebra `TauCeti.CalkinAlgebra 𝕜 E` this reads: `T` is Fredholm if and only if its
image `TauCeti.CalkinAlgebra.mk 𝕜 E T` is a unit. Thus Fredholmness, like the Fredholm index, only
depends on the class of an operator modulo compact operators.

On an infinite-dimensional space the Calkin algebra is nontrivial, so a compact operator, whose
class is `0`, is never Fredholm. On a complex Hilbert space the Calkin algebra is a C⋆-algebra,
and the class of a Fredholm isometry, such as a unilateral shift, is a unitary: the isometry `S`
satisfies `S† S = 1` exactly, and `S S† = 1` holds modulo compact operators.

## Main results

* `TauCeti.CalkinAlgebra.isUnit_mk_iff`: Atkinson's theorem in the Calkin algebra.
* `IsCompactOperator.not_isFredholm`: a compact operator on an infinite-dimensional Banach space
  is not Fredholm.
* `TauCeti.CalkinAlgebra.mk_mem_unitary_of_isometry`: the Calkin class of a Fredholm isometry of
  a complex Hilbert space is unitary.

## References

* F. V. Atkinson, *The normal solubility of linear equations in normed spaces*, Mat. Sbornik
  N.S. **28** (70) (1951), 3–14.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer, 1990, Chapter XI, §2.
-/

public section

open Module

namespace TauCeti.CalkinAlgebra

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **Atkinson's theorem** in the Calkin algebra: an operator on a Banach space is Fredholm if and
only if its image in the Calkin algebra is invertible. -/
@[simp]
theorem isUnit_mk_iff {T : E →L[𝕜] E} : IsUnit (mk 𝕜 E T) ↔ T.IsFredholm := by
  rw [isFredholm_iff_exists_isCompactOperator_comp_sub_one, isUnit_iff_exists]
  constructor
  · rintro ⟨x, hTS, hST⟩
    obtain ⟨S, rfl⟩ := mk_surjective x
    exact ⟨S, mk_eq_mk_iff.mp (by simp [hST]), mk_eq_mk_iff.mp (by simp [hTS])⟩
  · rintro ⟨S, hST, hTS⟩
    refine ⟨mk 𝕜 E S, ?_, ?_⟩ <;> rw [← mk_comp, ← map_one (mk 𝕜 E), mk_eq_mk_iff] <;> assumption

/-- A compact operator on an infinite-dimensional Banach space is not Fredholm: its class in the
nontrivial Calkin algebra is `0`, which is not a unit. -/
theorem _root_.IsCompactOperator.not_isFredholm {K : E →L[𝕜] E} (hK : IsCompactOperator K)
    (hE : ¬ FiniteDimensional 𝕜 E) : ¬ K.IsFredholm := by
  have := nontrivial hE
  rw [← isUnit_mk_iff, mk_eq_zero_iff.mpr hK]
  exact not_isUnit_zero

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Calkin class of a Fredholm isometry of a complex Hilbert space is unitary. For a
unilateral shift `S`, `S† S = 1` while `1 - S S†` is the projection onto the cokernel, of finite
rank. -/
theorem mk_mem_unitary_of_isometry {S : H →L[ℂ] H} (hS : S.IsFredholm) (hi : Isometry S) :
    mk ℂ H S ∈ unitary (CalkinAlgebra ℂ H) := by
  refine (isUnit_mk_iff.mpr hS).mem_unitary_of_star_mul_self ?_
  rw [← mk_adjoint, ← mk_comp, (ContinuousLinearMap.isometry_iff_adjoint_comp_self S).mp hi,
    map_one]

end Hilbert

end TauCeti.CalkinAlgebra
