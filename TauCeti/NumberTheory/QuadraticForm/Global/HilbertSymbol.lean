/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
import TauCeti.NumberTheory.HilbertSymbol.Henselian
import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.RingTheory.DedekindDomain.SelmerGroup

/-!
# Hilbert symbols of global units at the finite places

For `a, b ∈ Kˣ` in a number field `K`, the Hilbert symbol `(a_v, b_v)_v` of their images in the
completion `K_v` at a finite place `v` is `1` at every place `v` not above `2` at which `a` and
`b` are units: there the norm equation `x² - a y² = b` is solved in the ring of integers of `K_v`
by Hensel's lemma. The excluded places are finitely many, so the family of localized symbols has
finite multiplicative support. The lemma carries `@[fun_prop]`, so `fun_prop` extends this to
finite products of such symbols, such as `∏_{i<j} (a_i, a_j)_v` for the coefficients `a_i` of a
diagonal form `⟨a₁, …, aₙ⟩`.

Finite support is what makes the products of these signs over all finite places finite
products, as they occur in the product formula for the Hilbert symbol and for the Hasse
invariant of a global form.

## Main results

* `TauCeti.hilbertSymbol_mul_left_adicCompletion`: over the completion at a finite place, the
  symbol is multiplicative in its first argument.
* `TauCeti.hilbertSymbol_eq_one_of_valued_eq_one`: over the completion at a finite place not
  above `2`, the symbol of two elements of valuation `1` is `1`.
* `TauCeti.hilbertSymbol_unitAtFinitePlace_eq_one`: the localized symbol is `1` at a finite
  place at which `2`, `a` and `b` are units.
* `TauCeti.hasFiniteMulSupport_hilbertSymbol_of_eventually_valued_eq_one`: the symbol of a family
  of elements of the completions that are almost all local units, with a localized global
  element, is `1` at all but finitely many finite places.
* `TauCeti.hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace`: the localized symbol is `1` at
  all but finitely many finite places.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:11, 66:6 and 71:18.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **Multiplicativity of the Hilbert symbol at a finite place.** Over the completion `K_v` at a
finite place `v`, the Hilbert symbol is multiplicative in its first argument:
`(a a', c)_v = (a, c)_v (a', c)_v`. -/
theorem hilbertSymbol_mul_left_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (a a' c : (v.adicCompletion K)ˣ) :
    hilbertSymbol (a * a') c = hilbertSymbol a c * hilbertSymbol a' c := by
  let : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact hilbertSymbol_mul_left two_ne_zero c a a'

/-- **The Hilbert symbol of two local units at a nondyadic place.** If `2` is a unit at the
finite place `v`, then the Hilbert symbol over the completion `K_v` of two elements of valuation
`1` is `1`. -/
theorem hilbertSymbol_eq_one_of_valued_eq_one {v : HeightOneSpectrum (𝓞 K)}
    (h2 : v.valuation K 2 = 1) {u u' : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = 1) (hu' : Valued.v (u' : v.adicCompletion K) = 1) :
    hilbertSymbol u u' = 1 := by
  -- The ring of integers of `K_v` is Henselian with finite residue field, and `2` is a unit there.
  let : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  obtain ⟨t, ht, ht2⟩ := v.exists_isUnit_adicCompletionIntegers_of_valuation_eq_one h2
  have ht2' : t = 2 := Subtype.ext (by rw [ht2, map_ofNat]; norm_cast)
  -- An element of `K_v` of valuation `1` is the image of a unit of the ring of integers.
  have hunit {w : (v.adicCompletion K)ˣ} (hw : Valued.v (w : v.adicCompletion K) = 1) :
      ∃ r : (v.adicCompletionIntegers K)ˣ,
        Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) :
          v.adicCompletionIntegers K →* v.adicCompletion K) r = w :=
    ⟨(adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hw :
      IsUnit (⟨w, (mem_adicCompletionIntegers _ K v).mpr hw.le⟩ : v.adicCompletionIntegers K)).unit,
      Units.ext rfl⟩
  obtain ⟨r, rfl⟩ := hunit hu
  obtain ⟨r', rfl⟩ := hunit hu'
  exact hilbertSymbol_units_map_eq_one (ht2' ▸ ht) _ _

/-- **The Hilbert symbol at a good finite place.** If `2`, `a` and `b` are units at the finite
place `v`, then the Hilbert symbol of the images of `a` and `b` in the completion `K_v` is `1`. -/
@[simp]
theorem hilbertSymbol_unitAtFinitePlace_eq_one {a b : Kˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h2 : v.valuation K 2 = 1) (ha : v.valuation K a = 1) (hb : v.valuation K b = 1) :
    hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1 :=
  hilbertSymbol_eq_one_of_valued_eq_one h2 (by rwa [valued_unitAtFinitePlace])
    (by rwa [valued_unitAtFinitePlace])

/-- **Finite support of the local symbols of almost-everywhere local units.** If `c_v ∈ K_vˣ` has
valuation `1` at all but finitely many finite places `v`, then for `b ∈ Kˣ` the Hilbert symbol of
`c_v` and the image of `b` in `K_v` is `1` at all but finitely many finite places `v`. -/
theorem hasFiniteMulSupport_hilbertSymbol_of_eventually_valued_eq_one
    {c : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ}
    (hc : ∀ᶠ v in Filter.cofinite, Valued.v (c v : v.adicCompletion K) = 1) (b : Kˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      hilbertSymbol (c v) (v.unitAtFinitePlace b) := by
  refine (((Filter.eventually_cofinite.mp hc).union
    (finite_setOfPred_valuation_ne_one (two_ne_zero' K))).union
    (finite_setOfPred_valuation_ne_one b.ne_zero)).subset fun v hv ↦ ?_
  by_contra hbad
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hbad
  exact hv (hilbertSymbol_eq_one_of_valued_eq_one hbad.1.2 hbad.1.1
    (by rw [valued_unitAtFinitePlace, hbad.2]))

/-- **Finite support of the localized Hilbert symbol.** For `a, b ∈ Kˣ`, the Hilbert symbol of
the images of `a` and `b` in the completion `K_v` is `1` at all but finitely many finite
places `v`. -/
@[fun_prop]
theorem hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace (a b : Kˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) :=
  hasFiniteMulSupport_hilbertSymbol_of_eventually_valued_eq_one
    (Filter.eventually_cofinite.mpr ((finite_setOfPred_valuation_ne_one a.ne_zero).subset
      fun v hv ↦ by rwa [Set.mem_ofPred_eq, valued_unitAtFinitePlace] at hv)) b

end TauCeti
