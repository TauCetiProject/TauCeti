/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization
import TauCeti.NumberTheory.HilbertSymbol.Henselian
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
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

* `TauCeti.hilbertSymbol_unitAtFinitePlace_eq_one`: the localized symbol is `1` at a finite
  place at which `2`, `a` and `b` are units.
* `TauCeti.hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace`: the localized symbol is `1` at
  all but finitely many finite places.

## References

* `TauCetiRoadmap/GlobalQuadraticForms/README.md`, Layer 4.4 (finite support for the localized
  Hilbert symbol).
* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 63:11, 66:6 and 71:18.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The Hilbert symbol at a good finite place.** If `2`, `a` and `b` are units at the finite
place `v`, then the Hilbert symbol of the images of `a` and `b` in the completion `K_v` is `1`. -/
@[simp]
theorem hilbertSymbol_unitAtFinitePlace_eq_one {a b : Kˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h2 : v.valuation K 2 = 1) (ha : v.valuation K a = 1) (hb : v.valuation K b = 1) :
    hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1 := by
  -- The ring of integers of `K_v` is Henselian with finite residue field, and `2` is a unit there.
  let : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  obtain ⟨t, ht, ht2⟩ := v.exists_isUnit_adicCompletionIntegers_of_valuation_eq_one h2
  have ht2' : t = 2 := Subtype.ext (by rw [ht2, map_ofNat]; norm_cast)
  obtain ⟨u, hu, hua⟩ := v.exists_isUnit_adicCompletionIntegers_of_valuation_eq_one ha
  obtain ⟨u', hu', hub⟩ := v.exists_isUnit_adicCompletionIntegers_of_valuation_eq_one hb
  -- `a` and `b` are the images of the units `u` and `u'` of the ring of integers of `K_v`.
  have hmap {c : Kˣ} {w : v.adicCompletionIntegers K} (hw : IsUnit w)
      (hwc : (w : v.adicCompletion K) = algebraMap K (v.adicCompletion K) c) :
      Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) :
        v.adicCompletionIntegers K →* v.adicCompletion K) hw.unit = v.unitAtFinitePlace c :=
    Units.ext (by simpa using hwc)
  rw [← hmap hu hua, ← hmap hu' hub]
  exact hilbertSymbol_units_map_eq_one (ht2' ▸ ht) _ _

/-- **Finite support of the localized Hilbert symbol.** For `a, b ∈ Kˣ`, the Hilbert symbol of
the images of `a` and `b` in the completion `K_v` is `1` at all but finitely many finite
places `v`. -/
@[fun_prop]
theorem hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace (a b : Kˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) := by
  refine (((finite_setOfPred_valuation_ne_one (two_ne_zero' K)).union
    (finite_setOfPred_valuation_ne_one a.ne_zero)).union
    (finite_setOfPred_valuation_ne_one b.ne_zero)).subset fun v hv ↦ ?_
  by_contra hbad
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hbad
  exact hv (hilbertSymbol_unitAtFinitePlace_eq_one hbad.1.1 hbad.1.2 hbad.2)

end TauCeti
