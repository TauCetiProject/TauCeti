/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Finite
public import Mathlib.RingTheory.HahnSeries.Basic

/-!
# Eventual agreement of coefficients of Hahn series

Over a locally finite index order, a family of Hahn series whose supports are eventually bounded
below by one common index, and each of whose coefficients eventually agrees with the corresponding
coefficient of a fixed series, eventually agrees with that series at every coefficient below any
prescribed index. This upgrades pointwise stabilization to stabilization of every initial segment
of coefficients, which is the form in which order-based convergence statements consume it.

## Main results

* `TauCeti.hahnSeries_eventually_forall_lt_coeff_eq`: a common eventual lower support bound and
  eventual equality of each coefficient give eventual equality of all coefficients below any
  given index.
-/

public section

open Filter

namespace TauCeti

/-- If the supports of a family of Hahn series are eventually bounded below by a common index `b`,
and each coefficient eventually agrees with the corresponding coefficient of `g`, then for every
`D` the family eventually agrees with `g` at all coefficients below `D`. -/
theorem hahnSeries_eventually_forall_lt_coeff_eq {Γ R : Type*} [LinearOrder Γ]
    [LocallyFiniteOrder Γ] [Zero Γ] [Zero R]
    {ι : Type*} {l : Filter ι} {f : ι → HahnSeries Γ R} {g : HahnSeries Γ R}
    {b : Γ} (hlb : ∀ᶠ i in l, ∀ z < b, (f i).coeff z = 0)
    (hcoeff : ∀ z, ∀ᶠ i in l, (f i).coeff z = g.coeff z) (D : Γ) :
    ∀ᶠ i in l, ∀ z < D, (f i).coeff z = g.coeff z := by
  let a := min b g.order
  let c := max a D
  have hfinite : ∀ᶠ i in l, ∀ z ∈ Set.Icc a c, (f i).coeff z = g.coeff z :=
    (Filter.eventually_all_finite (Set.finite_Icc a c)).2 fun z _ ↦ hcoeff z
  filter_upwards [hlb, hfinite] with i hi hifinite
  intro z hz
  by_cases hza : z < a
  · rw [hi z (hza.trans_le (min_le_left _ _)),
      HahnSeries.coeff_eq_zero_of_lt_order (hza.trans_le (min_le_right _ _))]
  · exact hifinite z ⟨le_of_not_gt hza, hz.le.trans (le_max_right _ _)⟩

end TauCeti
