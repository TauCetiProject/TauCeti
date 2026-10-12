/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Restricted power series and their coefficient algebra

Mathlib's `PowerSeries.IsRestricted` asks the weighted coefficient norms of a power series to
tend to zero. A series whose coefficients vanish in every degree past some bound — a polynomial —
satisfies that condition at every radius, and a series restricted at one radius is restricted at
every smaller one. Over an ultrametric normed commutative ring, constant series give the restricted
subring its coefficient algebra structure. The polynomial inclusion is an algebra homomorphism;
it induces the polynomial-to-series comparisons used in Weierstrass division and its quotients.

## Main results

* `TauCeti.PowerSeries.isRestricted_of_forall_coeff_eq_zero`: a series with a vanishing tail is
  restricted at every radius.
* `TauCeti.PowerSeries.isRestricted_of_abs_le`: restrictedness passes to smaller radii, and
  `TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le` is the resulting containment of subrings.
* `TauCeti.PowerSeries.isRestricted_polynomial`: every polynomial is restricted.
* `TauCeti.PowerSeries.polynomialToRestricted`: the polynomial inclusion as an algebra map.
-/

public section

namespace TauCeti.PowerSeries

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

/-- A power series whose coefficients vanish in every degree `≥ n` is restricted at every radius:
its weighted coefficient norms are eventually zero. Such a series is a polynomial of degree less
than `n`. -/
theorem isRestricted_of_forall_coeff_eq_zero {n : ℕ}
    (hf : ∀ m, n ≤ m → f.coeff m = 0) : f.IsRestricted c := by
  rw [PowerSeries.isRestricted_iff']
  have h : ∀ᶠ m in Filter.atTop, (0 : ℝ) = ‖f.coeff m‖ * c ^ m := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    simp [hf m hm]
  exact Filter.Tendsto.congr' h tendsto_const_nhds

/-- **Restrictedness passes to smaller radii.** If the weighted coefficient norms of `f` tend to
zero at the radius `c'`, they do so at every radius `c` with `|c| ≤ |c'|`, being dominated by the
former. -/
theorem isRestricted_of_abs_le {c' : ℝ} (hf : f.IsRestricted c') (h : |c| ≤ |c'|) :
    f.IsRestricted c := by
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff'] at hf ⊢
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hf
  gcongr

/-- Over an ultrametric ring, the subring of series restricted at `c'` lies in the subring of
series restricted at any `c` with `|c| ≤ |c'|`. -/
theorem isRestrictedSubring_le_of_abs_le [IsUltrametricDist R] {c' : ℝ} (h : |c| ≤ |c'|) :
    PowerSeries.IsRestricted.subring (R := R) c' ≤ PowerSeries.IsRestricted.subring c :=
  fun _ hf ↦ isRestricted_of_abs_le hf h

/-- Every polynomial is restricted at every radius. -/
theorem isRestricted_polynomial (p : Polynomial R) : (p : PowerSeries R).IsRestricted c :=
  isRestricted_of_forall_coeff_eq_zero (n := p.natDegree + 1) fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

section Algebra

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ}

/-- The coefficient algebra structure on restricted power series, given by constant series. -/
noncomputable instance instAlgebraIsRestrictedSubring :
    Algebra R (PowerSeries.IsRestricted.subring (R := R) c) :=
  (PowerSeries.C.codRestrict _ (PowerSeries.isRestricted_C c)).toAlgebra

/-- The coefficient map of the restricted-series algebra is the constant series map. -/
@[simp]
theorem coe_algebraMap_isRestrictedSubring (a : R) :
    (algebraMap R (PowerSeries.IsRestricted.subring (R := R) c) a : PowerSeries R) =
      PowerSeries.C a := (rfl)

/-- The inclusion of polynomials into the algebra of restricted power series. -/
noncomputable def polynomialToRestricted (c : ℝ) :
    Polynomial R →ₐ[R] PowerSeries.IsRestricted.subring (R := R) c where
  __ := Polynomial.coeToPowerSeries.ringHom.codRestrict _ isRestricted_polynomial
  commutes' a := Subtype.ext (Polynomial.coe_C a)

/-- The polynomial inclusion has the usual underlying power series. -/
@[simp]
theorem coe_polynomialToRestricted (p : Polynomial R) :
    (polynomialToRestricted c p : PowerSeries R) = p := (rfl)

/-- A restricted series whose coefficients vanish from degree `s` onward is the polynomial
inclusion of its `s`-truncation. -/
theorem polynomialToRestricted_trunc_eq_of_coeff_eq_zero {s : ℕ}
    (r : PowerSeries.IsRestricted.subring (R := R) c)
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0) :
    polynomialToRestricted c (PowerSeries.trunc s (r : PowerSeries R)) = r := by
  apply Subtype.ext
  ext n
  simp only [coe_polynomialToRestricted, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (hr n (by omega)).symm

end Algebra

end TauCeti.PowerSeries
