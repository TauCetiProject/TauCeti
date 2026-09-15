/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Automorphism
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# The automorphism group acting on Riemann–Roch spaces

An `F`-automorphism `σ` of `F'` permutes the places of `F' / k`, and hence the divisors of
`F' / k`. Because `σ` moves the valuation at a place to the valuation at the moved place, it
carries the Riemann–Roch space `L(D)` onto `L(σ • D)`. The two spaces are therefore isomorphic
over the constants, so the dimension `ℓ(D)` is constant on the orbit of `D`.

Together with the invariance of the degree, this says that `deg` and `ℓ` are constant on
automorphism orbits of divisors.

## Main definitions

* `TauCeti.riemannRochSpaceEquivSmul`: the isomorphism `L(D) ≃ₗ[k] L(σ • D)` induced by `σ`.

## Main results

* `TauCeti.mem_riemannRochSpace_smul_iff` and `TauCeti.riemannRochSpace_map_smul`: `σ` carries
  `L(D)` onto `L(σ • D)`, pointwise and as a submodule;
* `TauCeti.Divisor.dim_smul`: `ℓ(σ • D) = ℓ(D)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4 for Riemann–Roch spaces and Section III.5 for the automorphism action on places.
* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser, 2006,
  Chapter 9, for automorphism groups of function fields.
-/

public section

namespace TauCeti

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (σ : F' ≃ₐ[F] F') (D : Divisor k F')

/-- **`σ f` lies in `L(σ • D)` exactly when `f` lies in `L(D)`**: `σ` moves the valuation at a
place to the valuation at the moved place, where the bound imposed by `σ • D` is the one `D`
imposed before. -/
@[simp]
theorem mem_riemannRochSpace_smul_iff {f : F'} :
    (∀ P, P.valuation (σ f) ≤ WithZero.exp (D.coeff (σ⁻¹ • P))) ↔
      f ∈ riemannRochSpace D := by
  rw [mem_riemannRochSpace_iff]
  constructor
  · intro h P
    have hP := h (σ • P)
    simpa only [Place.valuation_smul_apply, AlgebraicGeometry.WeilDivisor.coeff_smul,
      inv_smul_smul] using hP
  · intro h Q
    have hQ := h (σ⁻¹ • Q)
    rwa [Place.valuation_smul, AlgEquiv.aut_inv, AlgEquiv.symm_symm] at hQ

/-- **An automorphism carries `L(D)` onto `L(σ • D)`**, as a `k`-submodule of `F'`. -/
theorem riemannRochSpace_map_smul :
    (riemannRochSpace D).map (AlgEquiv.restrictScalars k σ).toLinearMap =
      riemannRochSpace (σ • D) := by
  ext g
  simp only [Submodule.mem_map, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_restrictScalars]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_riemannRochSpace_iff]
    simpa only [AlgebraicGeometry.WeilDivisor.coeff_smul] using
      (mem_riemannRochSpace_smul_iff σ D).mpr hf
  · intro hg
    exact ⟨σ.symm g, (mem_riemannRochSpace_smul_iff σ D).mp (by
      simpa only [mem_riemannRochSpace_iff, AlgebraicGeometry.WeilDivisor.coeff_smul,
        AlgEquiv.apply_symm_apply] using hg), by simp⟩

/-- **The isomorphism of Riemann–Roch spaces induced by an automorphism**: `σ` restricts to a
`k`-linear isomorphism `L(D) ≃ L(σ • D)`. -/
noncomputable def riemannRochSpaceEquivSmul :
    riemannRochSpace D ≃ₗ[k] riemannRochSpace (σ • D) :=
  LinearEquiv.ofSubmodules (AlgEquiv.restrictScalars k σ).toLinearEquiv _ _
    (riemannRochSpace_map_smul σ D)

@[simp]
theorem riemannRochSpaceEquivSmul_apply (f : riemannRochSpace D) :
    (riemannRochSpaceEquivSmul σ D f : F') = σ (f : F') := by
  rw [riemannRochSpaceEquivSmul, LinearEquiv.ofSubmodules_apply]
  rfl

@[simp]
theorem riemannRochSpaceEquivSmul_symm_apply (f : riemannRochSpace (σ • D)) :
    ((riemannRochSpaceEquivSmul σ D).symm f : F') = σ.symm (f : F') := by
  rw [riemannRochSpaceEquivSmul, LinearEquiv.ofSubmodules_symm_apply]
  rfl

namespace Divisor

/-- **The dimension `ℓ(D)` is invariant under the automorphism group**: an automorphism
identifies `L(D)` with `L(σ • D)` over the constants. -/
@[simp]
theorem dim_smul : (σ • D).dim = D.dim := by
  rw [dim_def, dim_def]
  exact ((riemannRochSpaceEquivSmul σ D).finrank_eq).symm

end Divisor

end TauCeti
