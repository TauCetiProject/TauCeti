/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor.Basic
public import TauCeti.NumberTheory.LocalField.Herbrand.ArtinConductor

import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
import TauCeti.NumberTheory.LocalField.Norm.Conductor
import TauCeti.NumberTheory.LocalField.Norm.Herbrand

/-!
# The conductor and the upper numbering

Let `M/K` be a finite abelian extension of nonarchimedean local fields with group `G` and upper
ramification groups `G^v`. For a natural number `v`, the step `U(K,v)` of the unit filtration
consists of norms from `M` exactly when `G^v = 1`
(`unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot`). Hence the conductor exponent
`c(M/K)`, the least `n` with `U(K,n) ⊆ N_{M/K}(Mˣ)`, is the least `n` with `G^n = 1`, and for a
homomorphism `χ` on `G` the conductor exponent of the fixed field of `ker χ` is the Artin conductor
exponent `f(χ)`, the least `n` with `G^n ⊆ ker χ` (`conductorExponent_fixedField_ker`). This is
the dictionary between the conductor of a character of `Kˣ` cut out by local class field theory
and the Artin conductor of the corresponding character of the Galois group. Together with the
local conductor–discriminant formula
`TauCeti.LocalFieldsRamification.finsum_artinConductorExponent_eq_discriminantExponent`, it is the
local input for expressing a discriminant through the conductors of the cyclic subextensions.

## Main results

* `TauCeti.ClassFieldTheory.unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot`:
  for `M/K` abelian, `U(K,v) ⊆ N_{M/K}(Mˣ)` exactly when `G^v = 1`.
* `TauCeti.ClassFieldTheory.conductorExponent_le_iff_upperRamificationGroup_eq_bot`:
  `c(M/K) ≤ n` exactly when `G^n = 1`.
* `TauCeti.ClassFieldTheory.conductorExponent_fixedField_ker`: the conductor exponent of the
  fixed field of `ker χ` is the Artin conductor exponent of `χ`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §6 and Chapter XV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter V, §6 and Chapter VII, §11.
-/

public section

noncomputable section

open IntermediateField TauCeti.LocalFieldsRamification

namespace TauCeti.ClassFieldTheory

variable (K M : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsAbelianGalois K M]

/-- **The conductor in the upper numbering.** For a finite abelian extension `M/K` of
nonarchimedean local fields and a natural number `v`, every element of `U(K,v)` is a norm from
`M` exactly when the upper ramification group `G^v` of `M/K` is trivial. -/
theorem unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot (v : ℕ) :
    unitFiltration K v ≤ normGroup K M ↔
      upperRamificationGroup K M ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩ = ⊥ := by
  -- If `G^v = 1`, the norm maps `U(M, ψ(v))` onto `U(K,v)`. Conversely, suppose that `U(K,v)`
  -- consists of norms and that `G^v` contains an element `σ` of prime order. Let `F` be the fixed
  -- field of `⟨σ⟩`, so that `M/F` is cyclic of prime degree. The norm maps `U(F, ψ_{F/K}(v))`
  -- into `U(K,v)`, and since `M/K` is abelian an element of `Fˣ` whose norm to `K` is a norm
  -- from `M` is a norm from `M` (`comap_normUnits_normGroup`); so `U(F, ψ_{F/K}(v))` consists of
  -- norms from `M`. In prime degree this forces `Gal(M/F)^{ψ_{F/K}(v)} = 1`, while that group is
  -- `⟨σ⟩ ∩ G^v = ⟨σ⟩` by the upper numbering of a subgroup
  -- (`comap_restrictScalarsHom_upperRamificationGroup`).
  refine ⟨fun h ↦ ?_, unitFiltration_le_normGroup_of_upperRamificationGroup_eq_bot⟩
  by_contra hne
  -- An element `σ` of prime order in `G^v`, and the fixed field `F` of the group it generates.
  have := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (Finite.one_lt_card (α := upperRamificationGroup K M ⟨v, _⟩)).ne'
  have := Fact.mk hp
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  set F := fixedField (Subgroup.zpowers (σ : Gal(M/K)))
  let _ := finiteIntermediateFieldValuativeRel K M F
  let _ := finiteIntermediateFieldTopology K M F
  have := finiteIntermediateField_isNonarchimedeanLocalField K M F
  have := finiteIntermediateField_valuativeExtension K M F
  have hdeg : (Module.finrank F M).Prime := by
    rwa [finrank_fixedField_eq_card, Nat.card_zpowers, Subgroup.orderOf_coe, hσ]
  -- `σ` lies in `Gal(M/F) ∩ G^v = Gal(M/F)^{ψ_{F/K}(v)}`, so the latter is nontrivial.
  have hjump : upperRamificationGroup F M
      ⟨psiNat K F v, Nat.cast_mem_ramificationIndexDomain _⟩ ≠ ⊥ := by
    have hψ : (⟨psiNat K F v, Nat.cast_mem_ramificationIndexDomain _⟩ :
        RamificationIndexDomain) =
          inverseHerbrand K F ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩ :=
      Subtype.ext (coe_psiNat K F v)
    rw [hψ, ← comap_restrictScalarsHom_upperRamificationGroup K F M]
    intro hbot
    let τ := fixingSubgroupEquiv F ⟨σ,
      (IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (σ : Gal(M/K)))).symm ▸
        Subgroup.mem_zpowers _⟩
    have hτ : AlgEquiv.restrictScalarsHom K τ = σ :=
      AlgEquiv.ext fun x ↦ by simp [τ, coe_fixingSubgroupEquiv_apply]
    have hτmem : τ ∈
        (upperRamificationGroup K M ⟨v, Nat.cast_mem_ramificationIndexDomain v⟩).comap
          (AlgEquiv.restrictScalarsHom (S := F) K) := by
      rw [Subgroup.mem_comap, hτ]
      exact σ.2
    rw [hbot, Subgroup.mem_bot] at hτmem
    have hσ1 : σ = 1 := Subtype.ext (by rw [← hτ, hτmem, map_one, Subgroup.coe_one])
    exact hp.one_lt.ne' (by rw [← hσ, hσ1, orderOf_one])
  -- `U(F, ψ_{F/K}(v))` consists of norms from `M`, which in prime degree forces the opposite.
  refine hjump ((unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot_of_finrank_prime
    hdeg _).1 ?_)
  rw [← comap_normUnits_normGroup (K := K) F M]
  exact fun x hx ↦ h (map_normUnits_unitFiltration_psiNat_le K F v ⟨x, hx, rfl⟩)

/-- **The conductor exponent of an abelian extension in the upper numbering**: `c(M/K) ≤ n`
exactly when the upper ramification group `G^n` of `M/K` is trivial. Thus `c(M/K)` is the least
natural number `n` with `G^n = 1`. -/
theorem conductorExponent_le_iff_upperRamificationGroup_eq_bot {n : ℕ} :
    conductorExponent K M ≤ n ↔
      upperRamificationGroup K M ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ = ⊥ := by
  rw [conductorExponent_le_iff, unitFiltration_le_normGroup_iff_upperRamificationGroup_eq_bot]

/-- **The conductor of a character is its Artin conductor.** For a finite abelian extension
`M/K` of nonarchimedean local fields and a homomorphism `χ` on `Gal(M/K)`, the conductor exponent
of the fixed field of `ker χ` — the least `n` such that `U(K,n)` consists of norms from it — is
the Artin conductor exponent `f(χ)`, the least `n` with `G^n ⊆ ker χ`. -/
theorem conductorExponent_fixedField_ker {A : Type*} [MulOneClass A] (χ : Gal(M/K) →* A) :
    conductorExponent K (fixedField χ.ker) = artinConductorExponent K M χ := by
  let _ := finiteIntermediateFieldValuativeRel K M (fixedField χ.ker)
  let _ := finiteIntermediateFieldTopology K M (fixedField χ.ker)
  have := finiteIntermediateField_isNonarchimedeanLocalField K M (fixedField χ.ker)
  have := finiteIntermediateField_valuativeExtension K M (fixedField χ.ker)
  -- `Gal(F/K)^n` is the image of `G^n` under restriction, whose kernel is `Gal(M/F) = ker χ`.
  refine eq_of_forall_ge_iff fun n ↦ ?_
  rw [conductorExponent_le_iff_upperRamificationGroup_eq_bot, artinConductorExponent_le_iff,
    ← map_restrictNormalHom_upperRamificationGroup K (fixedField χ.ker) M,
    Subgroup.map_eq_bot_iff, IntermediateField.restrictNormalHom_ker,
    IntermediateField.fixingSubgroup_fixedField]

end TauCeti.ClassFieldTheory
