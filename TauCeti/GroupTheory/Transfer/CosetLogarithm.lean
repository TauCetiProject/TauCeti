/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.GroupTheory.Transfer
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Coset-weighted group-ring sums and transfer logarithms

For a finite group `Γ`, a subgroup `H ≤ Γ`, and a multiplicative map `ρ : Γ →* R` into a ring `R`,
this file relates the coset-averaged weighted norm `(∑ η, ρ η.out) * (∑ p : H, f p • ρ p) *
(∑ η, ρ η.out⁻¹)` to the transfer of a homomorphism `a : H →* Multiplicative (ZMod m)` modulo any
ring homomorphism `σ : R →+* S` killing `m`.

## Main definitions and results

* `TauCeti.cosetNorm`, `TauCeti.cosetNormInv`: sums of `ρ η.out` and `ρ η.out⁻¹` over `Γ ⧸ H`.
* `TauCeti.cosetComponent`: the element `p ∈ H` with `g * x = (g • x : Γ ⧸ H).out * p`.
* `TauCeti.weightedSum`: the additive map `f ↦ ∑ g, f (c g).toAdd • ρ g` on weights `ZMod m → ℤ`.
* `TauCeti.cosetNorm_mul_sum_mul`: `(∑ ρ h) * (∑ p : H, f p • ρ p) * ρ x⁻¹` equals
  `∑ g : Γ, f (cosetComponent H g x) • ρ g`.
* `TauCeti.transfer_eq_prod_cosetComponent`: explicit formula for `MonoidHom.transfer` via
  `cosetComponent`.
* `TauCeti.map_cosetNorm_mul_weightedSum_mul_cosetNormInv`: modulo `m`, conjugating the logarithm
  of `a : H →* Multiplicative (ZMod m)` by `cosetNorm` and `cosetNormInv` yields the logarithm of
  `a.transfer`.

## Provenance

Adapted from `src/New/Congruences/FirstOrder/OnePrime.lean` (`New.Patching.cosetNorm_mul_sum_mul`,
`New.Patching.transfer_eq_prod_cosetComponent`,
`New.Patching.map_cosetNorm_mul_weightedSum_mul_cosetNormInv`) in
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset Subgroup IsComplement MulAction leftTransversals ZMod

variable {Γ R S : Type*} [Group Γ] [Fintype Γ] [Ring R] [Ring S] {m : ℕ}

/-- The weighted norm `∑ g, f (c g).toAdd • ρ g` for a homomorphism
`c : Γ →* Multiplicative (ZMod m)`, as an additive function of the weight `f : ZMod m → ℤ`. -/
def weightedSum (ρ : Γ →* R) (c : Γ →* Multiplicative (ZMod m)) : (ZMod m → ℤ) →+ R :=
  .mk' (fun f ↦ ∑ g : Γ, f (c g).toAdd • ρ g) (by simp [add_smul, sum_add_distrib])

open scoped Classical in
/-- The sum `∑ η : Γ ⧸ H, ρ η.out` over chosen left coset representatives of `H` in `Γ`. -/
noncomputable def cosetNorm (ρ : Γ →* R) (H : Subgroup Γ) : R :=
  ∑ η : Γ ⧸ H, ρ η.out

open scoped Classical in
/-- The sum `∑ η : Γ ⧸ H, ρ η.out⁻¹` over inverses of chosen left coset representatives. -/
noncomputable def cosetNormInv (ρ : Γ →* R) (H : Subgroup Γ) : R :=
  ∑ η : Γ ⧸ H, ρ η.out⁻¹

/-- The unique element `p ∈ H` satisfying `g * x = (g • x : Γ ⧸ H).out * p`. -/
noncomputable def cosetComponent (H : Subgroup Γ) (g x : Γ) : H :=
  ⟨(g • x : Γ ⧸ H).out⁻¹ * (g * x), QuotientGroup.eq.mp (g • x : Γ ⧸ H).out_eq⟩

/-- For a weight `f : H → ℤ` and `x : Γ`, the product
`cosetNorm ρ H * (∑ p : H, f p • ρ p) * ρ x⁻¹` equals
`∑ g : Γ, f (cosetComponent H g x) • ρ g`. -/
theorem cosetNorm_mul_sum_mul (ρ : Γ →* R) {H : Subgroup Γ} [Fintype H] (f : H → ℤ) (x : Γ) :
    cosetNorm ρ H * (∑ p : H, f p • ρ p) * ρ x⁻¹ =
      ∑ g : Γ, f (cosetComponent H g x) • ρ g := by
  classical
  have component_eq (η : Γ ⧸ H) (p : H) : cosetComponent H (η.out * p * x⁻¹) x = p := by
    simp [cosetComponent]
  rw [cosetNorm, sum_mul_sum, ← sum_product', sum_mul]
  refine sum_nbij' (fun (η, p) ↦ η.out * p * x⁻¹) (fun g ↦ (↑(g * x), cosetComponent H g x))
    (by simp) (by simp) (by simp [component_eq]) (by simp [cosetComponent]) ?_
  rintro ⟨η, p⟩ -
  simp only [component_eq, map_mul, mul_smul_comm, smul_mul_assoc]

open scoped Classical in
/-- The transfer of `a : H →* A` at `g` is the product over `η : Γ ⧸ H` of
`a (cosetComponent H g η.out)`. -/
theorem transfer_eq_prod_cosetComponent {A : Type*} [CommGroup A] {H : Subgroup Γ} (a : H →* A)
    (g : Γ) :
    a.transfer g = ∏ η : Γ ⧸ H, a (cosetComponent H g η.out) := by
  have default_apply (η : Γ ⧸ H) :
      ((default : H.LeftTransversal).property.leftQuotientEquiv η : Γ) = η.out :=
    leftQuotientEquiv_apply Quotient.out_eq η
  rw [a.transfer_def (g⁻¹ • default), diff]
  congr! 3 with η
  simp [cosetComponent, smul_apply_eq_smul_apply_inv_smul, default_apply, mul_assoc]

/-- Modulo a ring homomorphism `σ : R →+* S` with `(m : S) = 0`, conjugating the `valMinAbs`
logarithm of `a : H →* Multiplicative (ZMod m)` by `cosetNorm` and `cosetNormInv` gives the
`valMinAbs` logarithm of `a.transfer`. -/
theorem map_cosetNorm_mul_weightedSum_mul_cosetNormInv (ρ : Γ →* R) {σ : R →+* S}
    (hm : (m : S) = 0) {H : Subgroup Γ} [Fintype H] (a : H →* Multiplicative (ZMod m)) :
    σ (cosetNorm ρ H * weightedSum (ρ.comp H.subtype) a valMinAbs * cosetNormInv ρ H) =
      σ (weightedSum ρ a.transfer valMinAbs) := by
  classical
  let C : (Γ → ℤ) →+ R := (Fintype.linearCombination ℤ ρ).toAddMonoidHom
  let weight (η : Γ ⧸ H) (g : Γ) : ℤ := valMinAbs (a (cosetComponent H g η.out)).toAdd
  have h_term (η : Γ ⧸ H) :
      cosetNorm ρ H * weightedSum (ρ.comp H.subtype) a valMinAbs * ρ η.out⁻¹ = C (weight η) :=
    cosetNorm_mul_sum_mul ρ (fun p ↦ valMinAbs (a p).toAdd) η.out
  have h_weights (g : Γ) :
      ((∑ η : Γ ⧸ H, weight η) g : ZMod m) = valMinAbs (a.transfer g).toAdd := by
    simp [weight, transfer_eq_prod_cosetComponent, toAdd_prod]
  choose d hd using fun g ↦ (intCast_eq_intCast_iff_dvd_sub _ _ m).mp (h_weights g)
  have h_sub : (fun g ↦ valMinAbs (a.transfer g).toAdd) = m • d + ∑ η : Γ ⧸ H, weight η :=
    funext fun g ↦ by simp [← hd g]
  have h_lhs : cosetNorm ρ H * weightedSum (ρ.comp H.subtype) a valMinAbs * cosetNormInv ρ H =
      C (∑ η : Γ ⧸ H, weight η) := by
    simp only [cosetNormInv, map_sum C, mul_sum, h_term]
  have h_rhs : weightedSum ρ a.transfer valMinAbs = C (fun g ↦ valMinAbs (a.transfer g).toAdd) :=
    rfl
  rw [h_lhs, h_rhs, h_sub, map_add, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, hm, zero_mul,
    zero_add]

end TauCeti
