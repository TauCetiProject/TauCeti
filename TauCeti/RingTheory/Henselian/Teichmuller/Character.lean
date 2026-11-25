/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Teichmuller.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Teichmüller lifts of residual characters

Let `R` be a Henselian local ring whose residue field `k` is finite, of cardinality `q`; the ring
of integers of a nonarchimedean local field is the case of interest. A *residual character* of a
monoid `Γ`, typically a group, is a homomorphism `ψ : Γ →* kˣ`. Its **Teichmüller lift**
`TauCeti.teichmullerCharacter R ψ : Γ →* Rˣ` is `ψ` followed by the Teichmüller lift
`TauCeti.teichmuller R : kˣ →* Rˣ`.

It reduces to `ψ` (`TauCeti.unitsMap_residue_comp_teichmullerCharacter`), takes values in the
`(q - 1)`-st roots of unity, and is the unique lift of `ψ` with this property
(`TauCeti.eq_teichmullerCharacter_iff`); a lift of infinite order, or of finite order divisible
by the residue characteristic, is not excluded by reducing to `ψ` alone. The lift is
multiplicative in `ψ`, sends the trivial character to the trivial character and inverses to
inverses, and has the same kernel as `ψ` (`TauCeti.ker_teichmullerCharacter`). Since
`TauCeti.teichmuller R` and `TauCeti.teichmullerCharacterHom` are injective, it preserves order
both pointwise (`TauCeti.orderOf_teichmullerCharacter_apply`) and in the character group
(`TauCeti.orderOf_teichmullerCharacter`). For a topological group `Γ` and `ψ` with open kernel it
is continuous for every topology on `Rˣ` (`TauCeti.continuous_teichmullerCharacter`), and
`TauCeti.teichmullerContinuousCharacter` bundles it as a continuous character. It does not depend
on the coefficient ring: a local homomorphism `f : R → S` carries the lift of `ψ` to the lift in
`S` of `ψ` followed by the induced map of residue fields
(`TauCeti.unitsMap_comp_teichmullerCharacter`). A surjective residual character lifts to a
character of order exactly `q - 1` (`TauCeti.orderOf_teichmullerCharacter_of_surjective`).

Every character `χ : Γ →* Rˣ` factors uniquely as `χ = ω(χ̄) · ⟨χ⟩`, the product of the
Teichmüller lift of its reduction `χ̄` and a character `⟨χ⟩ = ω(χ̄)⁻¹ χ` with values in the
principal units `1 + 𝔪` (`TauCeti.principalUnitCharacter`,
`TauCeti.teichmullerCharacter_mul_principalUnitCharacter`,
`TauCeti.eq_teichmullerCharacter_and_eq_principalUnitCharacter`). For the `p`-adic cyclotomic
character this is `χ_p = ω · ⟨χ_p⟩` with `⟨χ_p⟩` valued in `1 + pℤ_p`.

## Main definitions

* `TauCeti.teichmullerCharacter`: the Teichmüller lift `Γ →* Rˣ` of a residual character.
* `TauCeti.teichmullerContinuousCharacter`: the Teichmüller lift `Γ →ₜ* Rˣ` of a residual
  character with open kernel.
* `TauCeti.principalUnitCharacter`: the principal-unit part `⟨χ⟩ = ω(χ̄)⁻¹ χ` of a character.

## Main results

* `TauCeti.unitsMap_residue_comp_teichmullerCharacter`: the lift reduces to `ψ`.
* `TauCeti.eq_teichmullerCharacter_iff`: it is the unique lift with values in `μ_{q-1}(R)`.
* `TauCeti.ker_teichmullerCharacter`, `TauCeti.orderOf_teichmullerCharacter_apply`,
  `TauCeti.orderOf_teichmullerCharacter`: same kernel and same order as `ψ`.
* `TauCeti.continuous_teichmullerCharacter`: continuity for `ψ` with open kernel.
* `TauCeti.unitsMap_comp_teichmullerCharacter`: independence of the coefficient ring.
* `TauCeti.orderOf_teichmullerCharacter_of_surjective`: a surjective residual character lifts to
  a character of order `q - 1`.
* `TauCeti.teichmullerCharacter_mul_principalUnitCharacter`,
  `TauCeti.eq_teichmullerCharacter_and_eq_principalUnitCharacter`: the decomposition
  `χ = ω(χ̄) · ⟨χ⟩` and its uniqueness.

## References

* C. Khare and J.-P. Wintenberger, *Serre's modularity conjecture (I)*, Invent. Math. 178 (2009),
  §1.5, p. 4.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing

variable (R : Type*) [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]
  {Γ : Type*} [Monoid Γ]

/-- The **Teichmüller lift** of a residual character `ψ : Γ →* kˣ`: `ψ` followed by the
Teichmüller lift `kˣ →* Rˣ`. -/
def teichmullerCharacter (ψ : Γ →* (ResidueField R)ˣ) : Γ →* Rˣ :=
  (teichmuller R).comp ψ

variable {R}

@[simp]
theorem teichmullerCharacter_apply (ψ : Γ →* (ResidueField R)ˣ) (g : Γ) :
    teichmullerCharacter R ψ g = teichmuller R (ψ g) :=
  (rfl)

/-- The Teichmüller lift of `ψ` reduces to `ψ`. -/
theorem residue_teichmullerCharacter_apply (ψ : Γ →* (ResidueField R)ˣ) (g : Γ) :
    residue R (teichmullerCharacter R ψ g : R) = ψ g :=
  residue_teichmuller R (ψ g)

/-- The Teichmüller lift of `ψ` reduces to `ψ`, as characters. -/
@[simp]
theorem unitsMap_residue_comp_teichmullerCharacter (ψ : Γ →* (ResidueField R)ˣ) :
    (Units.map (residue R : R →* ResidueField R)).comp (teichmullerCharacter R ψ) = ψ :=
  MonoidHom.ext fun g ↦ unitsMap_residue_teichmuller R (ψ g)

/-- The Teichmüller lift takes values in the `(q - 1)`-st roots of unity. -/
theorem teichmullerCharacter_apply_pow_card_sub_one (ψ : Γ →* (ResidueField R)ˣ) (g : Γ) :
    teichmullerCharacter R ψ g ^ (Nat.card (ResidueField R) - 1) = 1 :=
  teichmuller_pow_card_sub_one R (ψ g)

/-- **Uniqueness of the Teichmüller lift**: a character `χ : Γ →* Rˣ` is the Teichmüller lift of
`ψ` exactly when it reduces to `ψ` and takes values in the `(q - 1)`-st roots of unity. -/
theorem eq_teichmullerCharacter_iff {ψ : Γ →* (ResidueField R)ˣ} {χ : Γ →* Rˣ} :
    χ = teichmullerCharacter R ψ ↔
      (∀ g, χ g ^ (Nat.card (ResidueField R) - 1) = 1) ∧
        (Units.map (residue R : R →* ResidueField R)).comp χ = ψ := by
  refine ⟨?_, fun ⟨hpow, hres⟩ ↦ MonoidHom.ext fun g ↦ ?_⟩
  · rintro rfl
    exact ⟨teichmullerCharacter_apply_pow_card_sub_one ψ,
      unitsMap_residue_comp_teichmullerCharacter ψ⟩
  · refine ((teichmuller_eq_iff R).2 ⟨hpow g, ?_⟩).symm
    simp [← hres]

variable (R) in
/-- The Teichmüller lift of the trivial character is trivial. -/
@[simp]
theorem teichmullerCharacter_one : teichmullerCharacter R (1 : Γ →* (ResidueField R)ˣ) = 1 :=
  MonoidHom.comp_one _

/-- The Teichmüller lift is multiplicative in the residual character. -/
@[simp]
theorem teichmullerCharacter_mul (ψ φ : Γ →* (ResidueField R)ˣ) :
    teichmullerCharacter R (ψ * φ) = teichmullerCharacter R ψ * teichmullerCharacter R φ :=
  MonoidHom.comp_mul _ _ _

/-- The Teichmüller lift of the inverse character is the inverse of the lift. -/
@[simp]
theorem teichmullerCharacter_inv (ψ : Γ →* (ResidueField R)ˣ) :
    teichmullerCharacter R ψ⁻¹ = (teichmullerCharacter R ψ)⁻¹ :=
  MonoidHom.comp_inv _ _

variable (R Γ) in
/-- The Teichmüller lift as a homomorphism of character groups. -/
def teichmullerCharacterHom : (Γ →* (ResidueField R)ˣ) →* (Γ →* Rˣ) :=
  MonoidHom.compHom (teichmuller R)

@[simp]
theorem teichmullerCharacterHom_apply (ψ : Γ →* (ResidueField R)ˣ) :
    teichmullerCharacterHom R Γ ψ = teichmullerCharacter R ψ :=
  (rfl)

/-- The Teichmüller lift is injective on residual characters. -/
theorem teichmullerCharacter_injective :
    Function.Injective (teichmullerCharacter R : (Γ →* (ResidueField R)ˣ) → (Γ →* Rˣ)) :=
  fun ψ φ h ↦ by
    rw [← unitsMap_residue_comp_teichmullerCharacter ψ, h,
      unitsMap_residue_comp_teichmullerCharacter]

/-- The Teichmüller lift has the same kernel as the residual character. -/
@[simp]
theorem ker_teichmullerCharacter {G : Type*} [Group G] (ψ : G →* (ResidueField R)ˣ) :
    (teichmullerCharacter R ψ).ker = ψ.ker :=
  MonoidHom.ker_comp_of_injective ψ (teichmuller R) (teichmuller_injective R)

/-- The Teichmüller lift of `ψ` has the same order as `ψ` at every element. -/
theorem orderOf_teichmullerCharacter_apply (ψ : Γ →* (ResidueField R)ˣ) (g : Γ) :
    orderOf (teichmullerCharacter R ψ g) = orderOf (ψ g) :=
  orderOf_injective (teichmuller R) (teichmuller_injective R) (ψ g)

/-- The Teichmüller lift of `ψ` has the same order as `ψ` in the group of characters. -/
@[simp]
theorem orderOf_teichmullerCharacter (ψ : Γ →* (ResidueField R)ˣ) :
    orderOf (teichmullerCharacter R ψ) = orderOf ψ :=
  orderOf_injective (teichmullerCharacterHom R Γ) teichmullerCharacter_injective ψ

/-- **Continuity of the Teichmüller lift**: for a residual character with open kernel, the lift is
continuous for every topology on `Rˣ`. -/
theorem continuous_teichmullerCharacter {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousConstSMul G G] [TopologicalSpace Rˣ] {ψ : G →* (ResidueField R)ˣ}
    (hψ : IsOpen (ψ.ker : Set G)) :
    Continuous (teichmullerCharacter R ψ) :=
  (teichmullerCharacter R ψ).continuous_of_isOpen_ker (by rwa [ker_teichmullerCharacter])

variable (R) in
/-- The Teichmüller lift of a residual character with open kernel, as a continuous character for
any topology on `Rˣ`. -/
def teichmullerContinuousCharacter {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousConstSMul G G] [TopologicalSpace Rˣ] (ψ : G →* (ResidueField R)ˣ)
    (hψ : IsOpen (ψ.ker : Set G)) : G →ₜ* Rˣ where
  toMonoidHom := teichmullerCharacter R ψ
  continuous_toFun := continuous_teichmullerCharacter hψ

@[simp]
theorem coe_teichmullerContinuousCharacter {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousConstSMul G G] [TopologicalSpace Rˣ] {ψ : G →* (ResidueField R)ˣ}
    (hψ : IsOpen (ψ.ker : Set G)) :
    (teichmullerContinuousCharacter R ψ hψ : G →* Rˣ) = teichmullerCharacter R ψ :=
  (rfl)

@[simp]
theorem teichmullerContinuousCharacter_apply {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousConstSMul G G] [TopologicalSpace Rˣ] {ψ : G →* (ResidueField R)ˣ}
    (hψ : IsOpen (ψ.ker : Set G)) (g : G) :
    teichmullerContinuousCharacter R ψ hψ g = teichmuller R (ψ g) :=
  (rfl)

/-- **Independence of the coefficient ring.** A local homomorphism `f : R → S` carries the
Teichmüller lift of `ψ` to the Teichmüller lift of `ψ` followed by the induced map of residue
fields. -/
@[simp]
theorem unitsMap_comp_teichmullerCharacter {S : Type*} [CommRing S] [HenselianLocalRing S]
    [Finite (ResidueField S)] (f : R →+* S) [IsLocalHom f] (ψ : Γ →* (ResidueField R)ˣ) :
    (Units.map (f : R →* S)).comp (teichmullerCharacter R ψ) =
      teichmullerCharacter S
        ((Units.map (ResidueField.map f : ResidueField R →* ResidueField S)).comp ψ) :=
  MonoidHom.ext fun g ↦ unitsMap_teichmuller f (ψ g)

/-- **A surjective residual character lifts to a character of order `q - 1`**: the unit group of
the finite residue field is cyclic of order `q - 1`, and a character onto it has that order. -/
theorem orderOf_teichmullerCharacter_of_surjective {ψ : Γ →* (ResidueField R)ˣ}
    (hψ : Function.Surjective ψ) :
    orderOf (teichmullerCharacter R ψ) = Nat.card (ResidueField R) - 1 := by
  have : Fintype (ResidueField R) := Fintype.ofFinite _
  rw [orderOf_teichmullerCharacter, ← Nat.card_units]
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := (ResidueField R)ˣ)
  obtain ⟨g, rfl⟩ := hψ x
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_
  · exact MonoidHom.ext fun h ↦ by simp [pow_card_eq_one']
  · rw [← orderOf_eq_card_of_forall_mem_zpowers hx]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]

/-! ### The principal-unit part of a character -/

section PrincipalUnit

variable (R) in
/-- The **principal-unit part** `⟨χ⟩ = ω(χ̄)⁻¹ χ` of a character `χ : Γ →* Rˣ`, where `ω(χ̄)` is
the Teichmüller lift of the reduction `χ̄` of `χ`. It takes values in the principal units
`1 + 𝔪` (`TauCeti.unitsMap_residue_comp_principalUnitCharacter`). -/
def principalUnitCharacter (χ : Γ →* Rˣ) : Γ →* Rˣ :=
  (teichmullerCharacter R ((Units.map (residue R : R →* ResidueField R)).comp χ))⁻¹ * χ

theorem principalUnitCharacter_apply (χ : Γ →* Rˣ) (g : Γ) :
    principalUnitCharacter R χ g =
      (teichmuller R (Units.map (residue R : R →* ResidueField R) (χ g)))⁻¹ * χ g := by
  rw [principalUnitCharacter]
  rfl

/-- **The Teichmüller decomposition of a character**: `χ = ω(χ̄) · ⟨χ⟩`. -/
@[simp]
theorem teichmullerCharacter_mul_principalUnitCharacter (χ : Γ →* Rˣ) :
    teichmullerCharacter R ((Units.map (residue R : R →* ResidueField R)).comp χ) *
      principalUnitCharacter R χ = χ := by
  rw [principalUnitCharacter]
  ext g
  simp

/-- The principal-unit part of a character reduces to the trivial character. -/
@[simp]
theorem unitsMap_residue_comp_principalUnitCharacter (χ : Γ →* Rˣ) :
    (Units.map (residue R : R →* ResidueField R)).comp (principalUnitCharacter R χ) = 1 := by
  rw [principalUnitCharacter, MonoidHom.comp_mul, MonoidHom.comp_inv,
    unitsMap_residue_comp_teichmullerCharacter, inv_mul_cancel]

/-- The principal-unit part of a character takes values in the principal units `1 + 𝔪`. -/
theorem residue_principalUnitCharacter_apply (χ : Γ →* Rˣ) (g : Γ) :
    residue R (principalUnitCharacter R χ g : R) = 1 := by
  have h := DFunLike.congr_fun (unitsMap_residue_comp_principalUnitCharacter χ) g
  rw [MonoidHom.comp_apply, MonoidHom.one_apply] at h
  simpa only [Units.coe_map, Units.val_one, MonoidHom.coe_ofClass] using congrArg Units.val h

/-- **Uniqueness of the Teichmüller decomposition**: if `χ = ω · χ'` with `ω` valued in the
`(q - 1)`-st roots of unity and `χ'` valued in the principal units, then `ω` is the Teichmüller
lift of the reduction of `χ` and `χ'` is its principal-unit part. -/
theorem eq_teichmullerCharacter_and_eq_principalUnitCharacter {χ ω χ' : Γ →* Rˣ}
    (hχ : ω * χ' = χ) (hω : ∀ g, ω g ^ (Nat.card (ResidueField R) - 1) = 1)
    (hχ' : (Units.map (residue R : R →* ResidueField R)).comp χ' = 1) :
    ω = teichmullerCharacter R ((Units.map (residue R : R →* ResidueField R)).comp χ) ∧
      χ' = principalUnitCharacter R χ := by
  have hres : (Units.map (residue R : R →* ResidueField R)).comp χ =
      (Units.map (residue R : R →* ResidueField R)).comp ω := by
    rw [← hχ, MonoidHom.comp_mul, hχ', mul_one]
  have hω' := (eq_teichmullerCharacter_iff (ψ := (Units.map (residue R : R →* ResidueField R)).comp
    χ)).2 ⟨hω, hres.symm⟩
  refine ⟨hω', ?_⟩
  rw [principalUnitCharacter, ← hω', ← hχ]
  ext g
  simp

end PrincipalUnit

end TauCeti
