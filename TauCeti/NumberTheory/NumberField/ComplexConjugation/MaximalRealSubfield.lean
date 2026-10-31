/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
import TauCeti.FieldTheory.Minpoly.Invariant

/-!
# Real elements of a CM field

Let `K` be a CM field with maximal real subfield `K⁺`. Mathlib defines `K⁺` by asking that an
element be real under *every* complex embedding (`NumberField.mem_maximalRealSubfield_iff`). Since
every complex embedding `φ` turns the complex conjugation `IsCMField.complexConj K` into complex
conjugation of `ℂ`, a single embedding already decides membership:
`x ∈ K⁺ ↔ star (φ x) = φ x`.

The same intertwining controls minimal polynomials. If `K` is a `ℂ`-subfield (`[Algebra K ℂ]`)
and `x` is a real complex number, then complex conjugation of `ℂ` fixes `x` and lies over
`complexConj K`, so the coefficients of `minpoly K x` are fixed by `complexConj K` and lie in `K⁺`.

If `K / F` is a CM extension, Mathlib identifies `F` with `K⁺`
(`NumberField.CMExtension.equivMaximalRealSubfield`); so `K⁺` is the image of `F` in `K`, and
under any complex embedding `φ` an element of `K` comes from `F` exactly when its image is real.
For an imaginary quadratic field `K⁺ = ℚ`, which is how a real algebraic integer generating an
extension of an imaginary quadratic field acquires a minimal polynomial with rational integer
coefficients in the class number one problem.

## Main results

* `NumberField.IsCMField.mem_maximalRealSubfield_iff_star_eq`: one complex embedding suffices to
  test membership in `K⁺`.
* `NumberField.IsCMField.coeff_minpoly_mem_maximalRealSubfield`: the minimal polynomial over `K`
  of a real complex number has its coefficients in `K⁺`.
* `NumberField.CMExtension.maximalRealSubfield_eq_fieldRange`: for a CM extension `K / F`, `K⁺`
  is the image of `F` in `K`.
* `NumberField.CMExtension.mem_range_algebraMap_iff_star_eq`: for a CM extension `K / F`, an
  element of `K` comes from `F` exactly when its image under a given complex embedding is real.

## References

* H. M. Stark, *On the “gap” in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
-/

public section

open Polynomial

namespace NumberField.IsCMField

variable {K : Type*} [Field K] [CharZero K] [IsCMField K] [Algebra.IsIntegral ℚ K]

/-- **One complex embedding detects the maximal real subfield of a CM field.** An element of a CM
field lies in its maximal real subfield as soon as it is real under one complex embedding. -/
theorem mem_maximalRealSubfield_iff_star_eq (φ : K →+* ℂ) (x : K) :
    x ∈ maximalRealSubfield K ↔ star (φ x) = φ x := by
  rw [← complexConj_eq_self_iff, ← φ.injective.eq_iff, complexEmbedding_complexConj,
    Complex.star_def]

/-- **Minimal polynomials of real numbers over a CM field are real.** For a CM field `K` embedded
in `ℂ` and a real complex number `x`, every coefficient of `minpoly K x` lies in the maximal real
subfield of `K`. -/
theorem coeff_minpoly_mem_maximalRealSubfield [Algebra K ℂ] {x : ℂ} (hx : star x = x) (n : ℕ) :
    (minpoly K x).coeff n ∈ maximalRealSubfield K := by
  have h := minpoly.map_eq_self (σ := (complexConj K : K →+* K)) (τ := starRingEnd ℂ)
    (RingHom.ext fun c ↦ complexEmbedding_complexConj K (algebraMap K ℂ) c) (by simpa using hx)
  rw [← complexConj_eq_self_iff]
  simpa using congrArg (coeff · n) h

end NumberField.IsCMField

namespace NumberField.CMExtension

variable (F K : Type*) [Field F] [IsTotallyReal F] [Field K] [CharZero K] [Algebra.IsIntegral ℚ K]
  [IsTotallyComplex K] [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- **The maximal real subfield of a CM extension is the base field.** If `K / F` is a CM
extension, the maximal real subfield of `K` is the image of `F`; this is the set-level form of
Mathlib's `NumberField.CMExtension.equivMaximalRealSubfield`. -/
theorem maximalRealSubfield_eq_fieldRange :
    maximalRealSubfield K = (algebraMap F K).fieldRange := by
  refine le_antisymm (fun x hx ↦ ⟨_,
    algebraMap_equivMaximalRealSubfield_symm_apply F K ⟨x, hx⟩⟩) ?_
  rintro _ ⟨q, rfl⟩
  exact (equivMaximalRealSubfield F K q).prop

variable {K} in
/-- **One complex embedding detects the base field of a CM extension.** If `K / F` is a CM
extension, an element of `K` comes from `F` exactly when its image under a given complex embedding
is real. -/
theorem mem_range_algebraMap_iff_star_eq (φ : K →+* ℂ) (x : K) :
    x ∈ Set.range (algebraMap F K) ↔ star (φ x) = φ x := by
  have := IsCMField.ofCMExtension F K
  rw [← IsCMField.mem_maximalRealSubfield_iff_star_eq, maximalRealSubfield_eq_fieldRange F K,
    RingHom.mem_fieldRange, Set.mem_range]

end NumberField.CMExtension
