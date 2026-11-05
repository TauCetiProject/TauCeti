/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import TauCeti.RingTheory.Length

/-!
# Invariance and vanishing of the order of vanishing

For a Noetherian domain `R` of Krull dimension at most one with fraction field `K`, Mathlib's
`Ring.ordFrac R : K →*₀ ℤᵐ⁰` extends the order of vanishing `Ring.ord R x = length (R ⧸ (x))` to
the fraction field. This file records that the order of vanishing is transported by ring
isomorphisms, and that the order of a nonzero element of `R` is trivial
exactly when that element is a unit: `R ⧸ (x)` is the zero ring exactly when `(x)` is the unit
ideal. Mathlib has the forward direction, `Ring.ordFrac_of_isUnit`; the converse is what reads
"`f` has order zero at a codimension-one point" as "`f` is a unit at that point".

## Main results

* `TauCeti.Ring.ord_ringEquiv` and `TauCeti.Ring.ordFrac_map_of_ringEquiv`: the order of vanishing
  is invariant under ring isomorphisms, also on fraction fields;
* `TauCeti.Ring.ord_eq_zero_iff`: `Ring.ord R x = 0` exactly when `x` is a unit;
* `TauCeti.Ring.isUnit_iff_ordFrac_one`: `x` is a unit exactly when `Ring.ordFrac R x = 1`; this
  extends Mathlib's `Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` to Noetherian domains
  of dimension at most one.
-/

public section

namespace TauCeti

namespace Ring

open scoped nonZeroDivisors

section RingEquiv

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- The order of vanishing is invariant under ring isomorphisms: `σ : R ≃+* R'` induces a
`σ`-semilinear bijection `R ⧸ (x) → R' ⧸ (σ x)`, hence an isomorphism of the lattices of
submodules, which have the same length. -/
@[simp]
theorem ord_ringEquiv (σ : R ≃+* R') (x : R) : Ring.ord R' (σ x) = Ring.ord R x := by
  let e := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {σ x}) σ (by simp [Ideal.map_span])
  let f : (R ⧸ Ideal.span {x}) →ₛₗ[(σ : R →+* R')] (R' ⧸ Ideal.span {σ x}) :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun r q ↦ by
        induction q using Submodule.Quotient.induction_on
        simp [e, Algebra.smul_def] }
  rw [Ring.ord, Ring.ord, f.length_eq_of_bijective e.bijective]

/-- The order of vanishing, as a homomorphism to `ℤᵐ⁰`, is invariant under ring isomorphisms. -/
@[simp]
theorem ordMonoidWithZeroHom_ringEquiv [Nontrivial R] [Nontrivial R'] (σ : R ≃+* R') (x : R) :
    Ring.ordMonoidWithZeroHom R' (σ x) = Ring.ordMonoidWithZeroHom R x := by
  have hmem : σ x ∈ R'⁰ ↔ x ∈ R⁰ := by
    rw [← MulEquivClass.map_nonZeroDivisors σ, Submonoid.mem_map_iff_mem σ.injective]
  by_cases hx : x ∈ R⁰
  · rw [Ring.ordMonoidWithZeroHom_eq_ord hx, Ring.ordMonoidWithZeroHom_eq_ord (hmem.mpr hx),
      ord_ringEquiv]
  · rw [Ring.ordMonoidWithZeroHom_eq_zero hx, Ring.ordMonoidWithZeroHom_eq_zero (hmem.not.mpr hx)]

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsDomain R'] [IsNoetherianRing R'] [Ring.KrullDimLE 1 R']
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K']

/-- The order of vanishing on fraction fields is invariant under ring isomorphisms: if
`σ : R ≃+* R'` and `τ : K →+* K'` are compatible with the inclusions into the fraction fields, then
`ordFrac R' (τ k) = ordFrac R k`. -/
theorem ordFrac_map_of_ringEquiv (σ : R ≃+* R') (τ : K →+* K')
    (h : ∀ a, τ (algebraMap R K a) = algebraMap R' K' (σ a)) (k : K) :
    Ring.ordFrac R' (τ k) = Ring.ordFrac R k := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rw [map_div₀, h, h, map_div₀, map_div₀, Ring.ordFrac_eq_ord _ ha, Ring.ordFrac_eq_ord _ hb0,
    Ring.ordFrac_eq_ord _ (by simpa using ha), Ring.ordFrac_eq_ord _ (by simpa using hb0),
    ordMonoidWithZeroHom_ringEquiv, ordMonoidWithZeroHom_ringEquiv]

end RingEquiv

variable {R : Type*} [CommRing R]

/-- The order of vanishing of a ring element is zero exactly when the element is a unit: the
quotient `R ⧸ (x)` is trivial exactly when `(x)` is the unit ideal. -/
theorem ord_eq_zero_iff (x : R) : Ring.ord R x = 0 ↔ IsUnit x := by
  rw [Ring.ord, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top]

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- In a Noetherian domain of dimension at most one, an element is a unit exactly when its order
of vanishing in the fraction field is trivial. This extends Mathlib's
`Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` from discrete valuation rings to the
local rings at the codimension-one points of an arbitrary locally Noetherian integral scheme. -/
theorem isUnit_iff_ordFrac_one {x : R} : IsUnit x ↔ Ring.ordFrac R (algebraMap R K x) = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hnz : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
  rw [Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R hnz hn.symm, ← ord_eq_zero_iff,
    ← hn, ← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one, Nat.cast_eq_zero, Nat.cast_eq_zero]

end Ring

end TauCeti
