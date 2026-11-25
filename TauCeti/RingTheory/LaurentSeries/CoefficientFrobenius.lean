/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map
import Mathlib.FieldTheory.Finite.Basic

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

/-- Coefficient Frobenius applies the Hahn series coefficient map. -/
theorem coefficientFrobenius_apply (f : ℕ) (x : k⸨X⸩) :
    coefficientFrobenius p f x = mapRingHom (iterateFrobenius k p f) x := by
  have h : (iterateFrobeniusEquiv k p f : k →+* k) = iterateFrobenius k p f :=
    RingHom.ext fun y => by rw [RingEquiv.coe_toRingHom, coe_iterateFrobeniusEquiv]
  rw [coefficientFrobenius, RingEquiv.ofRingHom_apply, h]

/-- Inverse coefficient Frobenius applies the inverse Hahn series coefficient map. -/
theorem coefficientFrobenius_symm_apply (f : ℕ) (x : k⸨X⸩) :
    (coefficientFrobenius p f).symm x =
      mapRingHom ((iterateFrobeniusEquiv k p f).symm : k →+* k) x := by
  rw [coefficientFrobenius, RingEquiv.ofRingHom_symm, RingEquiv.ofRingHom_apply]

/-- The underlying ring map acts coefficientwise by the iterated Frobenius. -/
@[simp]
theorem coefficientFrobenius_toRingHom (f : ℕ) :
    (coefficientFrobenius (k := k) p f : k⸨X⸩ →+* k⸨X⸩) = mapRingHom (iterateFrobenius k p f) := by
  exact RingHom.ext (coefficientFrobenius_apply p f)

/-- The inverse ring map acts coefficientwise by inverse Frobenius. -/
@[simp]
theorem coefficientFrobenius_symm_toRingHom (f : ℕ) :
    ((coefficientFrobenius (k := k) p f).symm : k⸨X⸩ →+* k⸨X⸩) =
      mapRingHom ((iterateFrobeniusEquiv k p f).symm : k →+* k) := by
  exact RingHom.ext (coefficientFrobenius_symm_apply p f)

/-- The coefficient of a Laurent series is raised to `p^f` by coefficient Frobenius. -/
@[simp]
theorem coeff_coefficientFrobenius (f : ℕ) (x : k⸨X⸩) (j : ℤ) :
    (coefficientFrobenius p f x).coeff j = x.coeff j ^ p ^ f := by
  rw [coefficientFrobenius_apply, coeff_mapRingHom, iterateFrobenius_def]

/-- Inverse coefficient Frobenius applies the inverse scalar Frobenius to each coefficient. -/
@[simp]
theorem coeff_coefficientFrobenius_symm (f : ℕ) (x : k⸨X⸩) (j : ℤ) :
    ((coefficientFrobenius p f).symm x).coeff j =
      (iterateFrobeniusEquiv k p f).symm (x.coeff j) := by
  rw [coefficientFrobenius_symm_apply, coeff_mapRingHom, RingEquiv.coe_toRingHom]

/-- Coefficient Frobenius preserves Laurent-series order. -/
@[simp]
theorem order_coefficientFrobenius (f : ℕ) (x : k⸨X⸩) :
    (coefficientFrobenius p f x).order = x.order := by
  rw [coefficientFrobenius_apply, order_mapRingHom_of_injective x
    (iterateFrobeniusEquiv k p f).injective]

/-- Inverse coefficient Frobenius preserves Laurent-series order. -/
@[simp]
theorem order_coefficientFrobenius_symm (f : ℕ) (x : k⸨X⸩) :
    ((coefficientFrobenius p f).symm x).order = x.order := by
  rw [coefficientFrobenius_symm_apply, order_mapRingHom_of_injective x
    (iterateFrobeniusEquiv k p f).symm.injective]

/-- Coefficient Frobenius acts on a monomial without changing its exponent. -/
@[simp]
theorem coefficientFrobenius_single (f : ℕ) (j : ℤ) (a : k) :
    coefficientFrobenius p f (single j a) = single j (a ^ p ^ f) := by
  rw [coefficientFrobenius_apply, mapRingHom_single, iterateFrobenius_def]

/-- Coefficient Frobenius restricts to coefficientwise Frobenius on power series. -/
@[simp]
theorem coefficientFrobenius_coe (f : ℕ) (x : k⟦X⟧) :
    coefficientFrobenius p f (x : k⸨X⸩) = (PowerSeries.map (iterateFrobenius k p f) x : k⸨X⸩) := by
  rw [coefficientFrobenius_apply, mapRingHom_apply, map_ofPowerSeries]

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

section FiniteField

variable (k₀ : Type*) [Field k₀] [Fintype k₀] [Algebra k₀ k]

/-- Coefficient Frobenius over the Laurent series of an embedded field of cardinality `p ^ f`.
The scalar embedding maps each Laurent coefficient through the given field embedding. -/
noncomputable def coefficientFrobeniusAlgEquiv {f : ℕ} (hcard : Fintype.card k₀ = p ^ f) :
    letI := (mapRingHom (Γ := ℤ) (algebraMap k₀ k)).toAlgebra
    k⸨X⸩ ≃ₐ[k₀⸨X⸩] k⸨X⸩ := by
  letI := (mapRingHom (Γ := ℤ) (algebraMap k₀ k)).toAlgebra
  refine AlgEquiv.ofRingEquiv (f := coefficientFrobenius p f) fun x => ?_
  ext j
  rw [RingHom.algebraMap_toAlgebra, coeff_coefficientFrobenius, coeff_mapRingHom,
    ← map_pow, ← hcard, FiniteField.pow_card]

/-- Forgetting the base Laurent series recovers coefficient Frobenius. -/
@[simp]
theorem coefficientFrobeniusAlgEquiv_toRingEquiv {f : ℕ} (hcard : Fintype.card k₀ = p ^ f) :
    letI := (mapRingHom (Γ := ℤ) (algebraMap k₀ k)).toAlgebra
    (coefficientFrobeniusAlgEquiv (k := k) p k₀ hcard).toRingEquiv = coefficientFrobenius p f := by
  rfl

end FiniteField

end TauCeti.LaurentSeries
