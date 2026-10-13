/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.HilbertInvariant
public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
import TauCeti.FieldTheory.GaloisCohomology.MuTwo.LocalSymbol
import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol

/-!
# Localized Hilbert symbols as signs of the cohomological Hilbert invariants

For `a, b ∈ Kˣ` in a number field `K`, two families of local Hilbert symbols are attached to every
place of `K`.

* The **norm-equation symbols** `(a_v, b_v)_v ∈ {±1}`: the Hilbert symbol `TauCeti.hilbertSymbol`,
  `+1` exactly when `b = x² - a y²` is solvable, read over the completion `K_v` at a finite place
  and over `ℝ` through the real embedding at a real place. These are the symbols in which the
  Hasse invariants of quadratic forms over `K` are written.
* The **cohomological Hilbert invariants** in `ZMod 2`: the local invariant of the cup product of
  the Kummer classes of `a` and `b`, `TauCeti.ClassFieldTheory.finiteHilbertInvariantAt` at a finite
  place and `TauCeti.ClassFieldTheory.infiniteHilbertInvariantAt` at an infinite place. These are
  the terms of Hilbert's reciprocity law in its additive cohomological form
  `∑_v inv_v((a) ∪ (b)) = 0`.

This file proves that at every place the first is the sign of the second, under the dictionary
`TauCeti.hilbertSign` sending `0` to `+1` and `1` to `-1`. At a finite place this is
`TauCeti.hilbertSymbol_eq_cohomological` over the completion. At a real place the invariant is
that of a quaternion class in `Br ℝ ≃ ZMod 2`, which vanishes exactly when the norm equation is
solvable. At a complex place the invariant is `0` and every symbol is `1`.

Multiplying over all places, the product of the norm-equation symbols over the finite and real
places is the sign of the sum of all the cohomological invariants. So the multiplicative product
formula `∏_v (a_v, b_v)_v = 1` for the localized symbols is equivalent to the vanishing of that
sum, which is the additive cohomological form of Hilbert reciprocity.

## Main results

* `TauCeti.hilbertSymbol_unitAtFinitePlace_eq_hilbertSign`: at a finite place `v`,
  `(a_v, b_v)_v` is the sign of `finiteHilbertInvariantAt K v a b`.
* `TauCeti.hilbertSymbol_unitAtRealPlace_eq_hilbertSign`: at a real place `w`, the real symbol of
  the images of `a` and `b` is the sign of `infiniteHilbertInvariantAt K w a b`.
* `TauCeti.finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign`: the product of the
  localized symbols over all finite and real places is the sign of the sum of the cohomological
  Hilbert invariants over all places.

## References

* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter III, §2.
* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §§2–3.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:18.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace

namespace TauCeti

variable {K : Type} [Field K] [NumberField K]

/-- **The Hilbert symbol at a finite place is the sign of the cohomological invariant.** For
`a, b ∈ Kˣ` and a finite place `v`, the norm-equation Hilbert symbol of the images of `a` and `b`
in the completion `K_v` is the sign of their cohomological Hilbert invariant at `v`. -/
theorem hilbertSymbol_unitAtFinitePlace_eq_hilbertSign (v : HeightOneSpectrum (𝓞 K))
    (a b : Kˣ) :
    hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) =
      hilbertSign (ClassFieldTheory.finiteHilbertInvariantAt K v a b) := by
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  let : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
  have hζ : IsPrimitiveRoot (-1 : v.adicCompletion K) 2 := .neg_one 0 (by decide)
  have hmap (x : Kˣ) : v.unitAtFinitePlace x =
      Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) x :=
    Units.ext (by simp)
  rw [ClassFieldTheory.finiteHilbertInvariantAt_def K v a b hζ (isUnit_of_invertible _), hmap,
    hmap]
  exact hilbertSymbol_eq_cohomological hζ _ _ _

/-- **The Hilbert symbol at a real place is the sign of the cohomological invariant.** For
`a, b ∈ Kˣ` and a real place `w`, the real Hilbert symbol of the images of `a` and `b` under the
real embedding at `w` is the sign of their cohomological Hilbert invariant at `w`. -/
theorem hilbertSymbol_unitAtRealPlace_eq_hilbertSign (w : {w : InfinitePlace K // w.IsReal})
    (a b : Kˣ) :
    hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) =
      hilbertSign (ClassFieldTheory.infiniteHilbertInvariantAt K w.1 a b) := by
  let e := Completion.ringEquivRealOfIsReal w.2
  have : CharZero w.1.Completion :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  let : Invertible (2 : w.1.Completion) := invertibleOfNonzero two_ne_zero
  rw [ClassFieldTheory.infiniteHilbertInvariantAt_of_isReal K w.2,
    ← units_map_ringEquivRealOfIsReal_algebraMap w a,
    ← units_map_ringEquivRealOfIsReal_algebraMap w b, hilbertSymbol_units_map_ringEquiv]
  -- The invariant reads the Kummer-cup class over `K_w` through the injective map
  -- `Br K_w ≃ Br ℝ ≃ ZMod 2`.
  exact hilbertSymbol_eq_hilbertSign_kummerBrauerClass _
    (f := ((ClassFieldTheory.brCongr e).trans ClassFieldTheory.realInvEquiv).toAddMonoidHom)
    (AddEquiv.injective _) _ _

open scoped Classical in
/-- **The product of the localized Hilbert symbols is the sign of the cohomological reciprocity
sum.** For `a, b ∈ Kˣ`, the product of the norm-equation Hilbert symbols `(a_v, b_v)_v` over the
finite places and of the real Hilbert symbols `(a_w, b_w)_w` over the real places is the sign of
the sum of the cohomological Hilbert invariants of `a` and `b` over all finite and infinite
places. -/
theorem finprod_hilbertSymbol_mul_prod_hilbertSymbol_eq_hilbertSign (a b : Kˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b)) *
      ∏ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) =
      hilbertSign ((∑ v ∈ ClassFieldTheory.finiteHilbertSupport K a b,
          ClassFieldTheory.finiteHilbertInvariantAt K v a b) +
        ∑ w : InfinitePlace K, ClassFieldTheory.infiniteHilbertInvariantAt K w a b) := by
  rw [hilbertSign_add, hilbertSign_sum, hilbertSign_sum]
  congr 1
  · -- Off the support of the finite invariants every finite symbol is `1`.
    rw [finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_]
    · exact Finset.prod_congr rfl fun v _ ↦ hilbertSymbol_unitAtFinitePlace_eq_hilbertSign v a b
    · rw [Function.mem_mulSupport, hilbertSymbol_unitAtFinitePlace_eq_hilbertSign, Ne,
        hilbertSign_eq_one_iff] at hv
      exact (ClassFieldTheory.mem_finiteHilbertSupport K).mpr hv
  · -- The complex places contribute `1`, and the real ones are the real symbols.
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K ↦ w.IsReal),
      Fintype.prod_eq_one (fun w : {w : InfinitePlace K // ¬w.IsReal} ↦ _) fun w ↦ by
        rw [ClassFieldTheory.infiniteHilbertInvariantAt_eq_zero_of_isComplex K
          (not_isReal_iff_isComplex.mp w.2), hilbertSign_zero], mul_one]
    exact Fintype.prod_congr _ _ fun w ↦ hilbertSymbol_unitAtRealPlace_eq_hilbertSign w a b

end TauCeti
