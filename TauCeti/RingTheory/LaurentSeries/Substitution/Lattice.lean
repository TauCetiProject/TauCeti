/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Lattice
public import TauCeti.RingTheory.LaurentSeries.Substitution.Coordinate

/-!
# Coordinate substitution and the `X`-adic topology

Over a commutative ring `R`, the substitution automorphism `TauCeti.LaurentSeries.substAlgEquiv φ`
of a formal coordinate `φ = X v`, with `v` a unit power series, sends `Xᵃ p` to `Xᵃ (vᵃ p(φ))`,
with `vᵃ p(φ)` again a power series. Hence it preserves every lattice `Xᵃ R⟦X⟧` of Laurent
series, in particular the power series (`a = 0`), and so does its inverse, the substitution of
`φ⁻¹`. As these lattices form a basis of neighbourhoods of zero for the `X`-adic topology on
`R⸨X⸩ = HahnModule ℤ R R`, with the coefficients discrete, each substitution is continuous for
this topology.

## Main results

* `TauCeti.LaurentSeries.substAlgEquiv_mem_lattice_iff`: `σ_φ f ∈ Xᵃ R⟦X⟧ ↔ f ∈ Xᵃ R⟦X⟧`.
* `TauCeti.LaurentSeries.continuous_substAlgEquiv`: `σ_φ` is continuous for the `X`-adic topology.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries PowerSeries Filter

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommRing R]

/-- Substitution of a formal coordinate preserves and reflects every lattice `Xᵃ R⟦X⟧`. For
`a = 0`: a Laurent series is a power series exactly when its substitution is. -/
theorem substAlgEquiv_mem_lattice_iff (φ : FormalCoordinate R) {a : ℤ} {f : R⸨X⸩} :
    substAlgEquiv φ f ∈ lattice R R a ↔ f ∈ lattice R R a := by
  have key (φ : FormalCoordinate R) {f : R⸨X⸩} (hf : f ∈ lattice R R a) :
      substAlgEquiv φ f ∈ lattice R R a := by
    obtain ⟨v, hv⟩ := φ.exists_unit_toPowerSeries_eq_X_mul
    obtain ⟨p, rfl⟩ := mem_lattice_iff_exists.mp hf
    rw [map_mul, substAlgEquiv_single_of_eq_X_mul φ hv, substAlgEquiv_coe, mul_assoc,
      ← PowerSeries.coe_mul]
    exact mem_lattice_iff_exists.mpr ⟨_, rfl⟩
  refine ⟨fun h ↦ ?_, key φ⟩
  simpa [← substAlgEquiv_symm] using key φ⁻¹ h

/-- Substitution of a formal coordinate is continuous for the `X`-adic topology on
`R⸨X⸩ = HahnModule ℤ R R`, in which the lattices `Xᵃ R⟦X⟧` form a basis of neighbourhoods of
zero. Its inverse, the substitution of `φ⁻¹`, is continuous too, so `σ_φ` is a homeomorphism. -/
theorem continuous_substAlgEquiv (φ : FormalCoordinate R) :
    Continuous fun f : _root_.HahnModule ℤ R R ↦
      _root_.HahnModule.of R (substAlgEquiv φ ((_root_.HahnModule.of R).symm f)) := by
  let F : _root_.HahnModule ℤ R R →+ _root_.HahnModule ℤ R R :=
    { toFun := fun f ↦ _root_.HahnModule.of R (substAlgEquiv φ ((_root_.HahnModule.of R).symm f))
      map_zero' := by simp
      map_add' := fun f g ↦ by simp }
  refine continuous_of_continuousAt_zero F ?_
  rw [ContinuousAt, map_zero]
  refine ((HahnModule.hasBasis_nhds_zero_lattice R R).tendsto_iff
    (HahnModule.hasBasis_nhds_zero_lattice R R)).mpr fun a _ ↦ ⟨a, trivial, fun f hf ↦ ?_⟩
  rw [SetLike.mem_coe, ← Equiv.apply_symm_apply (_root_.HahnModule.of R) f,
    HahnModule.of_mem_lattice_iff] at hf
  simpa [F] using (substAlgEquiv_mem_lattice_iff φ).mpr hf

end TauCeti.LaurentSeries
