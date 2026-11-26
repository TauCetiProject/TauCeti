/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Specialization
public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Basic
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The orbit–cone correspondence as an order isomorphism

Order the torus orbits of the analytic realization of a regular fan by `O ≤ O'` when
`O ⊆ closure O'`. On the orbit space with its quotient topology this is the specialization
preorder, since the orbit projection of a continuous action is open
(`TauCeti.specializes_iff_orbit_subset_closure_orbit`). The orbit–cone correspondence
`TauCeti.Toric.Fan.coneEquivOrbitRelQuotient` reverses it: `τ ≤ σ` exactly when the orbit of `σ`
lies in the closure of the orbit of `τ` (`TauCeti.Toric.Fan.analyticConeOrbit_subset_closure_iff`).
So the correspondence is an order isomorphism from the cones onto the order dual of the orbits.

The closure relation is antisymmetric on these orbits, because each orbit is the orbit of a cone
and inclusion of cones is antisymmetric. This is not formal: for an irrational linear flow on the
real torus `ℝ² / ℤ²` every orbit is dense, so any two orbits lie in each other's closures. Here
antisymmetry is equivalent to the orbit space being `T0`, which makes the preorder a partial order.

## Main results

* `TauCeti.Toric.Fan.orbit_eq_of_subset_closure_of_subset_closure`: two torus orbits each in the
  closure of the other are equal.
* `TauCeti.Toric.Fan.t0Space_orbitRelQuotient`: the orbit space of the analytic realization is
  `T0`.
* `TauCeti.Toric.Fan.coneOrderIsoOrbitRelQuotient`: the orbit–cone correspondence as an order
  isomorphism from the cones onto the order dual of the orbits with their specialization order.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Theorem 3.2.6.
-/

public section

open Set Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- **The closure order on torus orbits is antisymmetric.** For a regular fan, two torus orbits
of the analytic realization each contained in the closure of the other are equal. With
reflexivity and transitivity of `O ⊆ closure O'` this makes the closure relation a partial order
on the orbits. -/
theorem orbit_eq_of_subset_closure_of_subset_closure
    (q q' : MulAction.orbitRel.Quotient (ComplexTorus N) (Φ.analyticRealization hΦ))
    (h : q.orbit ⊆ closure q'.orbit) (h' : q'.orbit ⊆ closure q.orbit) : q = q' := by
  obtain ⟨σ, rfl⟩ := (Φ.coneEquivOrbitRelQuotient hΦ).surjective q
  obtain ⟨τ, rfl⟩ := (Φ.coneEquivOrbitRelQuotient hΦ).surjective q'
  rw [orbit_coneEquivOrbitRelQuotient, orbit_coneEquivOrbitRelQuotient] at h h'
  rw [le_antisymm ((Φ.analyticConeOrbit_subset_closure_iff hΦ τ σ).1 h')
    ((Φ.analyticConeOrbit_subset_closure_iff hΦ σ τ).1 h)]

/-- The orbit space of the analytic realization of a regular fan is `T0`: inseparable orbits lie
in each other's closures, hence are equal. -/
instance t0Space_orbitRelQuotient :
    T0Space (MulAction.orbitRel.Quotient (ComplexTorus N) (Φ.analyticRealization hΦ)) :=
  t0Space_iff_inseparable _ |>.2 fun q q' hqq' ↦
    Φ.orbit_eq_of_subset_closure_of_subset_closure hΦ q q'
      (specializes_iff_orbit_subset_closure_orbit.1 hqq'.specializes')
      (specializes_iff_orbit_subset_closure_orbit.1 hqq'.specializes)

/-- **The orbit–cone correspondence reverses the closure order.** For a regular fan, the bijection
`coneEquivOrbitRelQuotient` is an order isomorphism from the cones onto the order dual of the
torus orbits with their specialization order, in which `O ≤ O'` when `O ⊆ closure O'`. -/
noncomputable def coneOrderIsoOrbitRelQuotient :
    Φ.cones ≃o (Specialization
      (MulAction.orbitRel.Quotient (ComplexTorus N) (Φ.analyticRealization hΦ)))ᵒᵈ where
  toEquiv := (Φ.coneEquivOrbitRelQuotient hΦ).trans (Specialization.toEquiv.trans OrderDual.toDual)
  map_rel_iff' {σ τ} := by
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply,
      OrderDual.toDual_le_toDual, Specialization.toEquiv_le_toEquiv,
      specializes_iff_orbit_subset_closure_orbit, orbit_coneEquivOrbitRelQuotient,
      orbit_coneEquivOrbitRelQuotient]
    exact Φ.analyticConeOrbit_subset_closure_iff hΦ τ σ

/-- The order isomorphism sends a cone to the orbit of its distinguished point. -/
@[simp]
theorem coneOrderIsoOrbitRelQuotient_apply (σ : Φ.cones) :
    Φ.coneOrderIsoOrbitRelQuotient hΦ σ =
      OrderDual.toDual (Specialization.toEquiv (Φ.coneEquivOrbitRelQuotient hΦ σ)) :=
  (rfl)

end TauCeti.Toric.Fan
