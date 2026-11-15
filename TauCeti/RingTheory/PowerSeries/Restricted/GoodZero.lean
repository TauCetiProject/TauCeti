/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero
public import TauCeti.RingTheory.PowerSeries.Restricted.Taylor
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Multiplicities of zeros of restricted power series

Let `f` be a power series restricted at a radius `c`, so that it converges on the closed disc
`‖x‖ ≤ c`. The multiplicity of a zero `a` of `f` in that disc is the order `h` of the good zero
`PowerSeries.IsGoodZero f a h`: the Hasse derivatives `(Δʲ f)(a)` vanish for `j < h` and
`(Δʰ f)(a)` is a unit. Over a field, equivalently, the Taylor translate of `f` at `a`, which is
the expansion `f(X + a)` on the whole disc, has order `h`. This notion refers to no particular
radius, and no factorial is inverted, so it is meaningful in every characteristic and for
inseparable polynomials.

Over a complete ultrametric ring a factor which is a unit at `a` does not change the multiplicity
at `a` (`PowerSeries.IsRestricted.isGoodZero_mul_iff_of_isUnit`), since Taylor translation is
multiplicative on restricted series. Over a complete ultrametric field, Weierstrass preparation
writes a nonzero restricted series as `f = u * P` with `u` a unit of the ring of series restricted
at `c` and `P` a polynomial. The multiplicity of `f` at a point of the closed disc is therefore the
root multiplicity of `P` there
(`PowerSeries.isGoodZero_iff_rootMultiplicity_eq_of_isUnit_mul`). In particular every
point of the disc has a well-defined multiplicity (`PowerSeries.IsRestricted.exists_isGoodZero`).

## Main results

* `PowerSeries.IsRestricted.isGoodZero_mul_iff_of_isUnit`: cancelling a factor which is a unit at
  the point.
* `PowerSeries.isGoodZero_iff_rootMultiplicity_eq_of_isUnit_mul`: the multiplicity
  of a zero in the closed disc is its root multiplicity in the Weierstrass polynomial.
* `PowerSeries.isGoodZero_count_roots_of_isUnit_mul`: the same multiplicity, as the number of
  occurrences of the point among the roots of the Weierstrass polynomial.
* `PowerSeries.IsRestricted.exists_isGoodZero`: every point of the closed disc has a
  multiplicity.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer,
  1984, §5.2.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §3.
-/

public section

namespace PowerSeries

section Ring

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {c : ℝ}
  {f g : R⟦X⟧} {a : R} {h : ℕ}

/-- **Cancelling a unit factor.** For series restricted at `c` and a point `a` of the closed disc
of radius `c` at which `g(a)` is a unit, `f * g` has a good zero of order `h` at `a` exactly when
`f` does. -/
theorem IsRestricted.isGoodZero_mul_iff_of_isUnit (hf : f.IsRestricted c) (hg : g.IsRestricted c)
    (ha : ‖a‖ ≤ c) (hga : IsUnit (g.evalAt a)) :
    (f * g).IsGoodZero a h ↔ f.IsGoodZero a h := by
  rw [isGoodZero_iff_associated_taylor, isGoodZero_iff_associated_taylor, hf.taylor_mul hg ha,
    associated_mul_isUnit_right_iff
      (isUnit_iff_constantCoeff.2 (by rwa [constantCoeff_taylor]))]

end Ring

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {c : ℝ}
  {f : K⟦X⟧} {a : K} {h : ℕ}

/-- **Multiplicity and the Weierstrass polynomial.** Let `f = u * P` be a nonzero series, where `u`
is a unit of the ring of series restricted at `c` and `P` is a polynomial. At every point `a` of
the closed disc of radius `c`, the multiplicity of the zero of `f` at `a` is the root multiplicity
of `a` in `P`. -/
theorem isGoodZero_iff_rootMultiplicity_eq_of_isUnit_mul
    {u : IsRestricted.subring (R := K) c} (hu : IsUnit u) {P : Polynomial K}
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) (hf : f ≠ 0) (ha : ‖a‖ ≤ c) :
    f.IsGoodZero a h ↔ P.rootMultiplicity a = h := by
  have hP : P ≠ 0 := by
    rintro rfl
    simp [← hmul] at hf
  have hua : IsUnit ((u : K⟦X⟧).evalAt a) := by
    simpa using hu.map (IsRestricted.evalAtHom K ha)
  rw [← hmul, mul_comm,
    (TauCeti.PowerSeries.isRestricted_polynomial P).isGoodZero_mul_iff_of_isUnit u.2 ha hua,
    isGoodZero_coe_iff_of_field, and_iff_right hP]

/-- **Multiplicity as a count of roots.** Let `f = u * P` be a nonzero series, where `u` is a unit
of the ring of series restricted at `c` and `P` is a polynomial. At every point `a` of the closed
disc of radius `c`, `f` has a good zero of order the number of times `a` occurs among the roots of
`P`. -/
theorem isGoodZero_count_roots_of_isUnit_mul [DecidableEq K]
    {u : IsRestricted.subring (R := K) c} (hu : IsUnit u) {P : Polynomial K}
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) (hf : f ≠ 0) (ha : ‖a‖ ≤ c) :
    f.IsGoodZero a (P.roots.count a) := by
  rw [Polynomial.count_roots]
  exact (isGoodZero_iff_rootMultiplicity_eq_of_isUnit_mul hu hmul hf ha).2 rfl

/-- **Existence of multiplicities.** A nonzero series restricted at `c > 0` has a good zero of some
order at every point of the closed disc of radius `c`. -/
theorem IsRestricted.exists_isGoodZero (hfr : f.IsRestricted c) (hc : 0 < c) (hf : f ≠ 0)
    (ha : ‖a‖ ≤ c) : ∃ h, f.IsGoodZero a h := by
  obtain ⟨s, hs⟩ := TauCeti.PowerSeries.exists_isDistinguished hc hfr hf
  obtain ⟨u, P, hu, -, hmul⟩ :=
    hs.exists_isUnit_isMonicOfDegree_mul_eq hs.coeff_ne_zero.isUnit hc hfr
  exact ⟨_, (isGoodZero_iff_rootMultiplicity_eq_of_isUnit_mul hu hmul hf ha).2 rfl⟩

end Field

end PowerSeries
