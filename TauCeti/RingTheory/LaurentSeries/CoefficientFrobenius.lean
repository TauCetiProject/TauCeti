/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map

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
  mapRingEquiv (iterateFrobeniusEquiv k p f)

variable [CommSemiring k] [ExpChar k p] [PerfectRing k p]

/-- The underlying ring map acts coefficientwise by the iterated Frobenius. -/
@[simp]
theorem coefficientFrobenius_toRingHom (f : ℕ) :
    (coefficientFrobenius (k := k) p f : k⸨X⸩ →+* k⸨X⸩) = mapRingHom (iterateFrobenius k p f) := by
  rw [coefficientFrobenius, mapRingEquiv_toRingHom]
  exact congrArg (mapRingHom (Γ := ℤ)) (RingHom.ext fun y ↦
    congrFun (coe_iterateFrobeniusEquiv k p f) y)

/-- The inverse ring map acts coefficientwise by inverse Frobenius. -/
@[simp]
theorem coefficientFrobenius_symm_toRingHom (f : ℕ) :
    ((coefficientFrobenius (k := k) p f).symm : k⸨X⸩ →+* k⸨X⸩) =
      mapRingHom ((iterateFrobeniusEquiv k p f).symm : k →+* k) := by
  rw [coefficientFrobenius, mapRingEquiv_symm, mapRingEquiv_toRingHom]

/-- Coefficient Frobenius acts as the Hahn-series map of the iterated Frobenius. -/
theorem coe_coefficientFrobenius (f : ℕ) :
    ⇑(coefficientFrobenius (k := k) p f) = mapRingHom (iterateFrobenius k p f) := by
  simpa only [RingEquiv.coe_toRingHom] using
    congrArg DFunLike.coe (coefficientFrobenius_toRingHom (k := k) p f)

/-- Inverse coefficient Frobenius acts as the Hahn-series map of the inverse scalar map. -/
theorem coe_coefficientFrobenius_symm (f : ℕ) :
    ⇑(coefficientFrobenius (k := k) p f).symm =
      mapRingHom ((iterateFrobeniusEquiv k p f).symm : k →+* k) := by
  simpa only [RingEquiv.coe_toRingHom] using
    congrArg DFunLike.coe (coefficientFrobenius_symm_toRingHom (k := k) p f)

/-- The coefficient of a Laurent series is raised to `p^f` by coefficient Frobenius. -/
@[simp]
theorem coeff_coefficientFrobenius (f : ℕ) (x : k⸨X⸩) (j : ℤ) :
    (coefficientFrobenius p f x).coeff j = x.coeff j ^ p ^ f := by
  rw [coe_coefficientFrobenius, coeff_mapRingHom, iterateFrobenius_def]

/-- Inverse coefficient Frobenius applies the inverse scalar Frobenius to each coefficient. -/
@[simp]
theorem coeff_coefficientFrobenius_symm (f : ℕ) (x : k⸨X⸩) (j : ℤ) :
    ((coefficientFrobenius p f).symm x).coeff j =
      (iterateFrobeniusEquiv k p f).symm (x.coeff j) := by
  rw [coe_coefficientFrobenius_symm, coeff_mapRingHom, RingEquiv.coe_toRingHom]

/-- Coefficient Frobenius preserves Laurent-series order. -/
@[simp]
theorem order_coefficientFrobenius (f : ℕ) (x : k⸨X⸩) :
    (coefficientFrobenius p f x).order = x.order := by
  rw [coe_coefficientFrobenius,
    order_mapRingHom_of_injective x (iterateFrobeniusEquiv k p f).injective]

/-- Inverse coefficient Frobenius preserves Laurent-series order. -/
@[simp]
theorem order_coefficientFrobenius_symm (f : ℕ) (x : k⸨X⸩) :
    ((coefficientFrobenius p f).symm x).order = x.order := by
  rw [coe_coefficientFrobenius_symm,
    order_mapRingHom_of_injective x (iterateFrobeniusEquiv k p f).symm.injective]

/-- Coefficient Frobenius acts on a monomial without changing its exponent. -/
@[simp]
theorem coefficientFrobenius_single (f : ℕ) (j : ℤ) (a : k) :
    coefficientFrobenius p f (single j a) = single j (a ^ p ^ f) := by
  rw [coe_coefficientFrobenius, mapRingHom_single, iterateFrobenius_def]

/-- Coefficient Frobenius restricts to coefficientwise Frobenius on power series. -/
@[simp]
theorem coefficientFrobenius_coe (f : ℕ) (x : k⟦X⟧) :
    coefficientFrobenius p f (x : k⸨X⸩) = (PowerSeries.map (iterateFrobenius k p f) x : k⸨X⸩) := by
  rw [coe_coefficientFrobenius, mapRingHom_apply, map_ofPowerSeries]

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
  funext x
  ext j
  have h : Semiconj (fun y : k⸨X⸩ => y.coeff j) (coefficientFrobenius p f)
      (iterateFrobenius k p f) := fun y => coeff_coefficientFrobenius p f y j
  simpa only [← iterateFrobenius_mul_apply, coeff_coefficientFrobenius, iterateFrobenius_def]
    using h.iterate_right n x

section Algebra

variable (k₀ : Type*) [CommSemiring k₀] [Algebra k₀ k] {f : ℕ}

/-- Coefficient Frobenius is linear over the Laurent series of a base semiring
whose image is fixed by the `p ^ f` power map. -/
noncomputable def coefficientFrobeniusAlgEquiv
    (hfix : ∀ a : k₀, (algebraMap k₀ k a) ^ (p ^ f) = algebraMap k₀ k a) :
    letI := coefficientAlgebra ℤ k₀ k
    k⸨X⸩ ≃ₐ[k₀⸨X⸩] k⸨X⸩ := by
  letI := coefficientAlgebra ℤ k₀ k
  refine AlgEquiv.ofRingEquiv (f := coefficientFrobenius p f) fun x => ?_
  ext j
  rw [algebraMap_coefficientAlgebra, coeff_coefficientFrobenius, coeff_mapRingHom, hfix]

variable (hfix : ∀ a : k₀, (algebraMap k₀ k a) ^ (p ^ f) = algebraMap k₀ k a)

/-- Forgetting the base Laurent series recovers coefficient Frobenius. -/
@[simp]
theorem coefficientFrobeniusAlgEquiv_toRingEquiv :
    letI := coefficientAlgebra ℤ k₀ k
    (coefficientFrobeniusAlgEquiv (k := k) p k₀ hfix).toRingEquiv = coefficientFrobenius p f := by
  rfl

/-- The algebra automorphism acts on a Laurent series by coefficient Frobenius. -/
@[simp]
theorem coefficientFrobeniusAlgEquiv_apply (x : k⸨X⸩) :
    letI := coefficientAlgebra ℤ k₀ k
    coefficientFrobeniusAlgEquiv p k₀ hfix x = coefficientFrobenius p f x :=
  (rfl)

/-- The inverse algebra automorphism acts by inverse coefficient Frobenius. -/
@[simp]
theorem coefficientFrobeniusAlgEquiv_symm_apply (x : k⸨X⸩) :
    letI := coefficientAlgebra ℤ k₀ k
    (coefficientFrobeniusAlgEquiv p k₀ hfix).symm x = (coefficientFrobenius p f).symm x :=
  (rfl)

end Algebra

end TauCeti.LaurentSeries
