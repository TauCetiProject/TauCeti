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
below by one common index, and each of whose coefficients below a prescribed index eventually
agrees with the corresponding coefficient of a fixed series, eventually agrees with that series at
every coefficient below that index. This upgrades pointwise stabilization to stabilization of
initial segments of coefficients, which is the form in which order-based convergence statements
consume it.

The proof adapts the finite-interval assembly in
`LaurentSeries.Cauchy.coeff_eventually_equal` from Mathlib. Here its Cauchy-filter-specific
coefficient limit is replaced by an arbitrary fixed Hahn series and an arbitrary filter.

## Main results

* `TauCeti.hahnSeries_eventually_forall_lt_coeff_eq`: a common eventual lower support bound and
  eventual equality of each coefficient below a given index give eventual equality of all
  coefficients below that index.
-/

public section

open Filter

namespace TauCeti

/-- If the supports of a family of Hahn series are eventually bounded below by a common index `b`,
and each coefficient below `D` eventually agrees with the corresponding coefficient of `g`, then
the family eventually agrees with `g` at all coefficients below `D`. -/
theorem hahnSeries_eventually_forall_lt_coeff_eq {Γ R : Type*} [LinearOrder Γ]
    [LocallyFiniteOrder Γ] [Zero R]
    {ι : Type*} {l : Filter ι} {f : ι → HahnSeries Γ R} {g : HahnSeries Γ R}
    {b : Γ} (hlb : ∀ᶠ i in l, ∀ z < b, (f i).coeff z = 0) (D : Γ)
    (hcoeff : ∀ z < D, ∀ᶠ i in l, (f i).coeff z = g.coeff z) :
    ∀ᶠ i in l, ∀ z < D, (f i).coeff z = g.coeff z := by
  rcases l.eq_or_neBot with rfl | _
  · exact eventually_bot
  have hfinite : ∀ᶠ i in l, ∀ z ∈ Set.Ico b D, (f i).coeff z = g.coeff z :=
    (Set.finite_Ico b D).eventually_all.2 fun z hz ↦ hcoeff z hz.2
  filter_upwards [hlb, hfinite] with i hi hifinite z hz
  rcases lt_or_ge z b with hzb | hbz
  · -- Below `b` the coefficient of `g` vanishes too: it agrees with a vanishing coefficient of
    -- some member of the family, which exists because `l` is nontrivial.
    obtain ⟨j, hj, hjz⟩ := (hlb.and (hcoeff z hz)).exists
    rw [hi z hzb, ← hjz, hj z hzb]
  · exact hifinite z ⟨hbz, hz⟩

end TauCeti
