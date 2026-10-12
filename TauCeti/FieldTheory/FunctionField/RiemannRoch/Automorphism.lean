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
* `TauCeti.apply_eq_self_of_mem_riemannRochSpace_of_degree_lt_card`: an automorphism fixing more
  rational places than the degree of a fixed divisor acts trivially on its Riemann–Roch space;
* `TauCeti.Divisor.dim_smul`: `ℓ(σ • D) = ℓ(D)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4 for Riemann–Roch spaces and Section III.5 for the automorphism action on places.
* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser, 2006,
  Chapter 9, for automorphism groups of function fields.
-/

public section

namespace TauCeti

open AlgebraicGeometry

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (σ : F' ≃ₐ[F] F') (D : Divisor k F')

/-- **`σ f` lies in `L(σ • D)` exactly when `f` lies in `L(D)`**: `σ` moves the valuation at a
place to the valuation at the moved place, where the bound imposed by `σ • D` is the one `D`
imposed before. -/
@[simp high]
theorem mem_riemannRochSpace_smul_iff {f : F'} :
    σ f ∈ riemannRochSpace (σ • D) ↔ f ∈ riemannRochSpace D := by
  simp only [mem_riemannRochSpace_iff, AlgebraicGeometry.WeilDivisor.coeff_smul]
  constructor
  · intro h P
    simpa only [Place.valuation_smul_apply, inv_smul_smul] using h (σ • P)
  · intro h Q
    have hQ := h (σ⁻¹ • Q)
    rwa [Place.valuation_smul, AlgEquiv.aut_inv, AlgEquiv.symm_symm] at hQ

/-- **An automorphism carries `L(D)` onto `L(σ • D)`**, as a `k`-submodule of `F'`. -/
@[simp]
theorem riemannRochSpace_map_smul :
    (riemannRochSpace D).map (AlgEquiv.restrictScalars k σ).toLinearMap =
      riemannRochSpace (σ • D) := by
  ext g
  simp only [Submodule.mem_map, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_restrictScalars]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact (mem_riemannRochSpace_smul_iff σ D).mpr hf
  · intro hg
    exact ⟨σ.symm g, (mem_riemannRochSpace_smul_iff σ D).mp (by rwa [AlgEquiv.apply_symm_apply]),
      by simp⟩

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

/-- **An automorphism fixing enough rational places fixes a Riemann–Roch space pointwise.** Let
`σ` fix the divisor `D`, and let `T` be a finite set of rational places outside the support of
`D`, each fixed by `σ`. If `deg D < #T`, then `σ z = z` for every `z ∈ L(D)`. -/
theorem apply_eq_self_of_mem_riemannRochSpace_of_degree_lt_card (hF : IsFunctionField k F')
    {σ : F' ≃ₐ[F] F'} {D : Divisor k F'} (hD : σ • D = D) {T : Finset (Place k F')}
    (hT : ∀ Q ∈ T, Q.degree = 1 ∧ σ • Q = Q ∧ D.coeff Q = 0)
    (hdeg : Divisor.degree D < T.card) {z : F'} (hz : z ∈ riemannRochSpace D) : σ z = z := by
  classical
  have hσz : σ z ∈ riemannRochSpace D := by
    simpa only [hD] using (mem_riemannRochSpace_smul_iff σ D).mpr hz
  have hw : σ z - z ∈ riemannRochSpace D := (riemannRochSpace D).sub_mem hσz hz
  by_contra hne
  have hw0 : σ z - z ≠ 0 := sub_ne_zero.mpr hne
  -- The difference vanishes at every place of `T`, so it lies in `L(D - ∑_{Q ∈ T} Q)`.
  have hmem : σ z - z ∈ riemannRochSpace (D - WeilDivisor.ofFinset T) := by
    refine (mem_riemannRochSpace_iff_neg_le_ord hw0).mpr fun Q ↦ ?_
    by_cases hQ : Q ∈ T
    · obtain ⟨hQdeg, hQσ, hQD⟩ := hT Q hQ
      have hzQ : z ∈ Q.integers := by
        simpa [hQD] using mem_riemannRochSpace_iff.mp hz Q
      have hpos := (Q.valuation_lt_one_iff_ord_pos hw0).mp
        (Place.valuation_apply_sub_lt_one_of_smul_eq_of_degree_eq_one σ Q hQσ hQdeg hzQ)
      simp only [WeilDivisor.coeff_sub, WeilDivisor.coeff_ofFinset, hQ, ite_true, hQD]
      omega
    · simpa [hQ] using (mem_riemannRochSpace_iff_neg_le_ord hw0).mp hw Q
  have hdegT : Divisor.degree (WeilDivisor.ofFinset T : Divisor k F') = T.card := by
    rw [Divisor.degree_eq_weightedDegree, WeilDivisor.weightedDegree_ofFinset,
      Finset.sum_congr rfl fun Q hQ ↦ by rw [(hT Q hQ).1, Nat.cast_one]]
    simp
  have hbot := riemannRochSpace_eq_bot_of_degree_neg hF
    (D := D - WeilDivisor.ofFinset T) (by rw [Divisor.degree_sub, hdegT]; omega)
  rw [hbot, Submodule.mem_bot] at hmem
  exact hw0 hmem

namespace Divisor

/-- **The dimension `ℓ(D)` is invariant under the automorphism group**: an automorphism
identifies `L(D)` with `L(σ • D)` over the constants. -/
@[simp]
theorem dim_smul : (σ • D).dim = D.dim := by
  rw [dim_def, dim_def]
  exact ((riemannRochSpaceEquivSmul σ D).finrank_eq).symm

end Divisor

end TauCeti
