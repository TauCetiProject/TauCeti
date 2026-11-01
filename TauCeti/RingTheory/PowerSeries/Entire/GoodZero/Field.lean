/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero
public import TauCeti.RingTheory.PowerSeries.Entire.Taylor

/-!
# Finite order of zeros of entire series over a field

Every nonzero entire series over a complete ultrametric normed field has a unique
finite good-zero order at every scalar. The order is zero precisely when the value
is nonzero. At a zero this supplies the positive finite multiplicity needed to
construct a Riesz projector. Neither a discrete valuation nor characteristic zero
is required.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127
  (1997), Appendix A4.
-/

public section

namespace PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {f : K⟦X⟧}

/-- A nonzero entire series over a complete ultrametric field has a unique finite
order at every scalar, including order zero away from its zeros. -/
theorem IsEntire.existsUnique_isGoodZero (hf : f.IsEntire) (hne : f ≠ 0) (a : K) :
    ∃! h : ℕ, f.IsGoodZero a h := by
  classical
  have hex : ∃ k, (PowerSeries.hasseDeriv k f).evalAt a ≠ 0 := by
    by_contra! h
    exact hne (hf.eq_zero_of_forall_evalAt_hasseDeriv_eq_zero a h)
  have hg : f.IsGoodZero a (Nat.find hex) := by
    refine PowerSeries.isGoodZero_iff.mpr
      ⟨fun j hj ↦ ?_, isUnit_iff_ne_zero.mpr (Nat.find_spec hex)⟩
    exact not_ne_iff.mp (Nat.find_min hex hj)
  exact ⟨Nat.find hex, hg, fun _ hj ↦ hj.unique hg⟩

end PowerSeries
