/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Coefficient Frobenius on Laurent series

The arithmetic `p^f`-Frobenius on `k((X))` acts on coefficients and fixes `X`. It is the
scalar twist for equal-characteristic isocrystals and their difference equations.
-/

public section

open scoped PowerSeries LaurentSeries
open Function HahnSeries

namespace TauCeti.LaurentSeries

variable (p : ℕ) {k : Type*}

/-- Apply the `p^f`-power automorphism to each coefficient of a Laurent series. -/
noncomputable def coefficientFrobenius [CommSemiring k] [ExpChar k p] [PerfectRing k p] (f : ℕ) :
    k⸨X⸩ ≃+* k⸨X⸩ :=
  RingEquiv.ofRingHom (mapRingHom (iterateFrobeniusEquiv k p f : k →+* k))
    (mapRingHom ((iterateFrobeniusEquiv k p f).symm : k →+* k))
    (by rw [← mapRingHom_comp, RingEquiv.comp_symm, mapRingHom_id])
    (by rw [← mapRingHom_comp, RingEquiv.symm_comp, mapRingHom_id])

variable [CommSemiring k] [ExpChar k p] [PerfectRing k p]

/-- The coefficient of a Laurent series is raised to `p^f` by coefficient Frobenius. -/
@[simp]
theorem coeff_coefficientFrobenius (f : ℕ) (x : k⸨X⸩) (j : ℤ) :
    (coefficientFrobenius p f x).coeff j = x.coeff j ^ p ^ f :=
  coeff_mapRingHom _ _ _

/-- Inverse coefficient Frobenius applies the inverse scalar Frobenius to each coefficient. -/
@[simp]
theorem coeff_coefficientFrobenius_symm (f : ℕ) (x : k⸨X⸩) (j : ℤ) :
    ((coefficientFrobenius p f).symm x).coeff j =
      (iterateFrobeniusEquiv k p f).symm (x.coeff j) :=
  coeff_mapRingHom _ _ _

/-- Coefficient Frobenius acts on a monomial without changing its exponent. -/
@[simp]
theorem coefficientFrobenius_single (f : ℕ) (j : ℤ) (a : k) :
    coefficientFrobenius p f (single j a) = single j (a ^ p ^ f) :=
  mapRingHom_single _ _ _

/-- Coefficient Frobenius restricts to coefficientwise Frobenius on power series. -/
@[simp]
theorem coefficientFrobenius_coe (f : ℕ) (x : k⟦X⟧) :
    coefficientFrobenius p f (x : k⸨X⸩) = (PowerSeries.map (iterateFrobenius k p f) x : k⸨X⸩) :=
  (mapRingHom_apply _ _).trans (map_ofPowerSeries _ _)

/-- The zeroth coefficient Frobenius is the identity. -/
@[simp]
theorem coefficientFrobenius_zero :
    coefficientFrobenius (k := k) p 0 = RingEquiv.refl k⸨X⸩ := by
  ext x j
  simp

/-- Composing coefficient Frobenius maps adds their iteration exponents. -/
theorem coefficientFrobenius_add_apply (f g : ℕ) (x : k⸨X⸩) :
    coefficientFrobenius p (f + g) x = coefficientFrobenius p f (coefficientFrobenius p g x) := by
  ext j
  simpa only [coeff_coefficientFrobenius, iterateFrobenius_def] using
    iterateFrobenius_add_apply k p f g (x.coeff j)

/-- Iterating coefficient Frobenius multiplies its exponent index by the number of iterations. -/
@[simp]
theorem coefficientFrobenius_iterate (f n : ℕ) :
    (coefficientFrobenius (k := k) p f)^[n] = coefficientFrobenius p (f * n) := by
  induction n with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    funext x
    rw [iterate_succ_apply, ih, Nat.mul_succ, coefficientFrobenius_add_apply]

end TauCeti.LaurentSeries
