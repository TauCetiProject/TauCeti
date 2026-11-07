/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.RingTheory.Polynomial.Radical
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Radical holomorphic hypersurface ideals

Weierstrass division identifies a distinguished polynomial quotient with its holomorphic
germ quotient. Thus radicality is equivalent for the two defining ideals. Squarefreeness
over the fraction field of the base germ ring gives a useful sufficient criterion.
In particular, `u^n = h` is reduced for every nonzero holomorphic germ `h` vanishing at the
base point, without any restriction on the multiplicity or factorization of `h`.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for Weierstrass division and analytic hypersurface local rings.
-/

public noncomputable section

open Polynomial
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A distinguished polynomial generates a radical holomorphic germ ideal exactly when
it generates a radical polynomial ideal over the base stalk. -/
theorem isRadical_span_evalVertical_iff {b : E} {w : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b))) :
    (Ideal.span {evalVertical b w P}).IsRadical ↔ (Ideal.span {P}).IsRadical := by
  let e := quotientEquivOfIsDistinguishedAt b w hP
  simp only [Ideal.isRadical_iff_quotient_reduced]
  exact ⟨fun h ↦ by
    let := h
    exact isReduced_of_injective e e.injective,
    fun h ↦ by
      let := h
      exact isReduced_of_injective e.symm e.symm.injective⟩

/-- The hypersurface `u^n = h` is reduced when the holomorphic germ `h` is nonzero and
vanishes at the base point. No squarefreeness or simple-zero assumption on `h` is needed. -/
theorem isRadical_span_evalVertical_X_pow_sub_C {b : E}
    (h : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b)
    (hh : h ≠ 0) (hb : eval 𝓘(ℂ, E) E b h = 0) {n : ℕ} (hn : n ≠ 0) :
    (Ideal.span {evalVertical b 0 (X ^ n - C h)}).IsRadical := by
  let A := (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b
  have hP : (X ^ n - C h).IsDistinguishedAt (IsLocalRing.maximalIdeal A) := by
    refine ⟨⟨fun {i} hi ↦ ?_⟩, monic_X_pow_sub_C h hn⟩
    have hi' : i ≠ n := by
      rw [natDegree_X_pow_sub_C h] at hi
      omega
    simp only [coeff_sub, coeff_X_pow, ite_eq_right hi', zero_sub]
    by_cases hi0 : i = 0
    · subst i
      simp [A, maximalIdeal_stalk, hb]
    · simp [coeff_C, hi0]
  apply (isRadical_span_evalVertical_iff hP).mpr
  apply (monic_X_pow_sub_C h hn).isRadical_span_of_map_squarefree
    (algebraMap A (FractionRing A)) (IsFractionRing.injective A (FractionRing A))
  have hnA : (n : A) ≠ 0 := by
    intro hz
    have hz' := congrArg (eval 𝓘(ℂ, E) E b) hz
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at hz'
    exact hn hz'
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using
    (separable_X_pow_sub_C (algebraMap A (FractionRing A) h)
      (by simpa only [map_natCast] using
        (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hnA)
      ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr hh)).squarefree

end TauCeti.holomorphicStructureSheaf
