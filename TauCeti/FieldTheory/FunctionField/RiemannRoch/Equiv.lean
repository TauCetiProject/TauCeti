/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Equiv
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus

/-!
# Riemann–Roch spaces under semilinear field isomorphisms

A field isomorphism carrying one constant field onto another identifies places and divisors,
preserves residue-weighted degrees, and induces semilinear isomorphisms of Riemann–Roch spaces.
Consequently it preserves the genus. Semilinearity is essential for Frobenius: over perfect
constants Frobenius is an automorphism of the constants, not generally their identity.

Divisor transport uses `Finsupp.domCongr` along `Place.equivOfRingEquiv`; no additional divisor
carrier is introduced. These statements do not require exact constants or a function-field
hypothesis, since they identify the sets and dimensions defining the genus directly.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Sections I.4 and III.10.
-/

public section

namespace TauCeti

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k' F']
variable (σ : k ≃+* k') (τ : F ≃+* F')
  (h : ∀ c, τ (algebraMap k F c) = algebraMap k' F' (σ c))

-- Transport rules run before `Finsupp.domCongr_apply` expands the divisor reindexing.
/-- Transporting a divisor along a semilinear field isomorphism preserves its weighted degree. -/
@[simp↓]
theorem Divisor.degree_domCongr_equivOfRingEquiv (D : Divisor k F) :
    degree (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) = degree D := by
  rw [degree_apply, degree_apply, Finsupp.domCongr_apply, Finsupp.sum_equivMapDomain]
  simp only [Place.degree_equivOfRingEquiv]

/-- A semilinear field isomorphism preserves the valuation bounds defining a Riemann–Roch space. -/
@[simp↓]
theorem mem_riemannRochSpace_domCongr_equivOfRingEquiv_iff (D : Divisor k F) (z : F) :
    τ z ∈ riemannRochSpace (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) ↔
      z ∈ riemannRochSpace D := by
  simp only [mem_riemannRochSpace_iff, AlgebraicGeometry.WeilDivisor.coeff,
    Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  constructor
  · intro hz P
    simpa only [Place.valuation_equivOfRingEquiv, RingEquiv.symm_apply_apply,
      Equiv.symm_apply_apply] using hz (Place.equivOfRingEquiv σ τ h P)
  · intro hz Q
    obtain ⟨P, rfl⟩ := (Place.equivOfRingEquiv σ τ h).surjective Q
    simpa only [Place.valuation_equivOfRingEquiv, RingEquiv.symm_apply_apply,
      Equiv.symm_apply_apply] using hz P

/-- The semilinear isomorphism of Riemann–Roch spaces induced by an isomorphism of fields and
constants. Its underlying map is the restriction of `τ`. -/
noncomputable def riemannRochSpaceEquivOfRingEquiv (D : Divisor k F) :
    riemannRochSpace D ≃ₛₗ[(σ : k →+* k')]
      riemannRochSpace (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) where
  toFun z := ⟨τ z, (mem_riemannRochSpace_domCongr_equivOfRingEquiv_iff σ τ h D z).mpr z.2⟩
  invFun z := ⟨τ.symm z,
    (mem_riemannRochSpace_domCongr_equivOfRingEquiv_iff σ τ h D (τ.symm z)).mp (by
      simpa only [RingEquiv.apply_symm_apply] using z.2)⟩
  left_inv z := Subtype.ext (τ.symm_apply_apply z)
  right_inv z := Subtype.ext (τ.apply_symm_apply z)
  map_add' z w := Subtype.ext (map_add τ (z : F) (w : F))
  map_smul' c z := Subtype.ext (by
    simp only [Submodule.coe_smul, Algebra.smul_def, map_mul, h, RingEquiv.coe_toRingHom])

/-- Evaluation of the transported section is evaluation of the field isomorphism. -/
@[simp]
theorem riemannRochSpaceEquivOfRingEquiv_apply (D : Divisor k F) (z : riemannRochSpace D) :
    (riemannRochSpaceEquivOfRingEquiv σ τ h D z : F') = τ (z : F) := (rfl)

/-- Inverse transport of a section is given by the inverse field isomorphism. -/
@[simp]
theorem riemannRochSpaceEquivOfRingEquiv_symm_apply (D : Divisor k F)
    (z : riemannRochSpace (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D)) :
    ((riemannRochSpaceEquivOfRingEquiv σ τ h D).symm z : F) = τ.symm (z : F') := (rfl)

/-- Semilinear transport preserves the dimension of a Riemann–Roch space. -/
@[simp↓]
theorem Divisor.dim_domCongr_equivOfRingEquiv (D : Divisor k F) :
    dim (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) = dim D := by
  rw [dim_def, dim_def]
  have he := riemannRochSpaceEquivOfRingEquiv σ τ h D
  have hr := lift_rank_eq_of_equiv_equiv σ he.toAddEquiv σ.bijective he.map_smulₛₗ
  simpa only [Module.finrank, Cardinal.toNat_lift] using
    (congrArg Cardinal.toNat hr).symm

include σ τ h in
/-- The genus is invariant under an isomorphism carrying the constant fields onto one another.
This also preserves the junk value of the supremum when the fields are not function fields. -/
theorem genus_eq_of_ringEquiv : genus k' F' = genus k F := by
  rw [genus_def, genus_def]
  congr 1
  apply Set.ext
  intro n
  constructor
  · rintro ⟨D', rfl⟩
    obtain ⟨D, rfl⟩ := (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h)).surjective D'
    exact ⟨D, by simp only [Divisor.degree_domCongr_equivOfRingEquiv,
      Divisor.dim_domCongr_equivOfRingEquiv]⟩
  · rintro ⟨D, rfl⟩
    exact ⟨Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D, by
      simp only [Divisor.degree_domCongr_equivOfRingEquiv,
        Divisor.dim_domCongr_equivOfRingEquiv]⟩

end TauCeti
