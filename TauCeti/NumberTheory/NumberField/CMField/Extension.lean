/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.AlgebraicClosure
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Cyclotomic extensions and subfields of CM fields

A field algebraic over `ℚ` is totally real or CM exactly when every product `c₁ c₂` of two
complex conjugations of an algebraic closure of `ℚ` fixes it pointwise
(`TauCeti.NumberField.isTotallyReal_or_isCMField_iff`). Two consequences follow.

* A field embedded in a totally real or CM field is totally real or CM, since the products `c₁ c₂`
  fixing the larger field fix the smaller one. If the smaller field is totally complex, for
  instance because it contains a CM field, it is CM. In particular every intermediate field of an
  extension of CM fields is CM.
* A cyclotomic extension `L` of a totally real or CM field `K` is totally real or CM, and it is CM
  when `K` is. Every complex conjugation inverts roots of unity, so each `c₁ c₂` fixes the roots of
  unity, as well as `K`, and hence the field `L` they generate over `K`. The set of orders of the
  adjoined roots of unity may be infinite.

## Main results

* `TauCeti.NumberField.isTotallyReal_or_isCMField_of_algebra`: a field embedded in a totally real
  or CM field is totally real or CM.
* `NumberField.IsCMField.of_algebra`: a totally complex field embedded in a CM field is CM.
* `IntermediateField.isCMField`: an intermediate field of an extension of CM fields is CM.
* `TauCeti.NumberField.isTotallyReal_or_isCMField_of_isCyclotomicExtension`: a cyclotomic
  extension of a totally real or CM field is totally real or CM.
* `NumberField.IsCMField.of_isCyclotomicExtension`: a cyclotomic extension of a CM field is CM.

## References

* J. S. Milne, *Complex Multiplication*, Chapter I, Corollary 1.5 and Remark 1.6.
-/

public section

open NumberField

namespace TauCeti.NumberField

/-- **A field embedded in a totally real or CM field is totally real or CM.** Every product of
two complex conjugations fixing the image of `L` fixes the image of `F`. -/
theorem isTotallyReal_or_isCMField_of_algebra (F L : Type*) [Field F] [CharZero F] [Field L]
    [CharZero L] [Algebra.IsIntegral ℚ L] [Algebra F L] (h : IsTotallyReal L ∨ IsCMField L) :
    IsTotallyReal F ∨ IsCMField F := by
  let τ : L →+* AlgebraicClosure ℚ := (IsAlgClosed.lift : L →ₐ[ℚ] AlgebraicClosure ℚ).toRingHom
  rw [isTotallyReal_or_isCMField_iff (τ.comp (algebraMap F L))]
  exact fun c₁ hc₁ c₂ hc₂ x ↦ (isTotallyReal_or_isCMField_iff τ).mp h c₁ hc₁ c₂ hc₂ _

/-- **A cyclotomic extension of a totally real or CM field is totally real or CM.** Every product
of two complex conjugations fixes the image of `K` and the roots of unity, which generate `L` over
`K`. -/
theorem isTotallyReal_or_isCMField_of_isCyclotomicExtension (S : Set ℕ) (K L : Type*) [Field K]
    [CharZero K] [Algebra.IsIntegral ℚ K] [Field L] [CharZero L] [Algebra K L]
    [IsCyclotomicExtension S K L] (h : IsTotallyReal K ∨ IsCMField K) :
    IsTotallyReal L ∨ IsCMField L := by
  have := IsCyclotomicExtension.integral S K L
  have : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.trans K
  let τ : L →+* AlgebraicClosure ℚ := (IsAlgClosed.lift : L →ₐ[ℚ] AlgebraicClosure ℚ).toRingHom
  have hK := (isTotallyReal_or_isCMField_iff (τ.comp (algebraMap K L))).mp h
  rw [isTotallyReal_or_isCMField_iff τ]
  intro c₁ hc₁ c₂ hc₂ x
  induction IsCyclotomicExtension.adjoin_roots (S := S) (A := K) x using
    Algebra.adjoin_induction with
  | mem y hy =>
    -- A complex conjugation inverts the root of unity `τ y`, which has absolute value one
    -- under every embedding into `ℂ`; so `c₁ c₂` fixes it.
    obtain ⟨n, -, hn, hy⟩ := hy
    have hτy : τ y ^ n = 1 := by rw [← map_pow, hy, map_one]
    have hinv {c : Gal(AlgebraicClosure ℚ/ℚ)} (hc : c ∈ complexConjugations _) :
        c (τ y) = (τ y)⁻¹ := by
      obtain ⟨ι, hι⟩ := mem_complexConjugations_iff.mp hc
      apply ι.injective
      rw [hι.eq, map_inv₀, Complex.star_def]
      exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one
        (by rw [← map_pow, hτy, map_one]) hn)).symm
    rw [hinv hc₂, map_inv₀, hinv hc₁, inv_inv]
  | algebraMap r => exact hK c₁ hc₁ c₂ hc₂ r
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | mul y z _ _ hy hz => simp only [map_mul, hy, hz]

end TauCeti.NumberField

namespace NumberField.IsCMField

/-- **A totally complex field embedded in a CM field is CM.** It is totally real or CM
(`TauCeti.NumberField.isTotallyReal_or_isCMField_of_algebra`), and not totally real. -/
theorem of_algebra (F L : Type*) [Field F] [CharZero F] [IsTotallyComplex F] [Field L]
    [CharZero L] [Algebra.IsIntegral ℚ L] [IsCMField L] [Algebra F L] : IsCMField F := by
  have : Algebra.IsIntegral ℚ F :=
    Algebra.IsIntegral.of_injective (IsScalarTower.toAlgHom ℚ F L) (algebraMap F L).injective
  exact (TauCeti.NumberField.isTotallyReal_or_isCMField_of_algebra F L (.inr ‹_›)).resolve_left
    IsTotallyComplex.not_isTotallyReal

/-- **A cyclotomic extension of a CM field is CM.** For any set `S` of orders of roots of unity,
an extension `L` of a CM field `K` with `IsCyclotomicExtension S K L` is CM. -/
theorem of_isCyclotomicExtension (S : Set ℕ) (K L : Type*) [Field K] [CharZero K]
    [Algebra.IsIntegral ℚ K] [IsCMField K] [Field L] [CharZero L] [Algebra K L]
    [IsCyclotomicExtension S K L] : IsCMField L := by
  have := IsCyclotomicExtension.integral S K L
  have : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.trans K
  have : IsTotallyComplex L := isTotallyComplex_of_algebra K L
  exact (TauCeti.NumberField.isTotallyReal_or_isCMField_of_isCyclotomicExtension S K L
    (.inr ‹_›)).resolve_left IsTotallyComplex.not_isTotallyReal

end NumberField.IsCMField

namespace IntermediateField

variable {K L : Type*} [Field K] [CharZero K] [IsCMField K] [Field L] [CharZero L]
  [Algebra.IsIntegral ℚ L] [IsCMField L] [Algebra K L]

/-- **An intermediate field of an extension of CM fields is CM.** It is totally complex, as an
extension of the CM field `K`, and it embeds in the CM field `L`. -/
instance isCMField (K' : IntermediateField K L) : IsCMField K' :=
  have : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  IsCMField.of_algebra K' L

end IntermediateField
