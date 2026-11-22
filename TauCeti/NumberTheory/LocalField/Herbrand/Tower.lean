/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Herbrand.IntegralClosure

/-!
# Transitivity of the Herbrand functions

Let `M/K` be a finite Galois extension of nonarchimedean local fields with group `G`, and let
`L` be an intermediate field Galois over `K`, so that `H = Gal(M/L)` is normal in `G` and
restriction to `L` identifies `Gal(L/K)` with `G / H`. Herbrand's theorem gives the
**transitivity of the Herbrand functions**

`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`   and   `ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`,

together with its integral form `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`.

## Main results

All declarations live in the namespace `TauCeti.LocalFieldsRamification`.

* `herbrand_tower`: `φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`, as the identity
  `herbrandOrderIso K M = (herbrandOrderIso L M).trans (herbrandOrderIso K L)` of bundled order
  isomorphisms.
* `inverseHerbrand_tower`: `ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`, as the identity of the inverse order
  isomorphisms.
* `psiNat_tower`: `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Proposition 15.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M]
  [Algebra K M] [ValuativeExtension K M]
  [IsScalarTower K L M]

/-! ### Transitivity of the Herbrand functions

Here `L/K` and `M/K` are Galois, so `M/L` is Galois as well (`IsGalois.tower_top_of_isGalois`).
Since `L` is an arbitrary field rather than an `IntermediateField K M`, instance synthesis cannot
recover `IsGalois L M` from `[IsGalois K M]` or `Module.Finite K M` from `L/K` and `M/L`; the
statements below therefore install them with `haveI`. -/

variable [IsGalois K L] [IsGalois K M]

/-- **Transitivity of the Herbrand function** in a tower `M/L/K` of Galois extensions:
`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`, as an identity of the bundled order isomorphisms of
`RamificationIndexDomain`. -/
theorem herbrand_tower :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    herbrandOrderIso K M = (herbrandOrderIso L M).trans (herbrandOrderIso K L) := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  let _ := IsScalarTower.to₁₃₄ 𝒪[K] K L M
  let _ := isDiscreteValuationRing_integralClosure K M
  let _ := isLocalHom_algebraMap_integralClosure K M
  let _ := finite_residueField_integralClosure K M
  let _ := TauCeti.isLocalRing_integralClosure_of_tower 𝒪[K] L M
  refine OrderIso.ext <| funext fun u ↦ Subtype.ext ?_
  simp only [OrderIso.trans_apply, herbrandOrderIso_apply,
    coe_herbrand_eq_herbrandFun_integralClosure K K M,
    coe_herbrand_eq_herbrandFun_integralClosure K L M,
    coe_herbrand_eq_herbrandFun_integralClosure K K L]
  exact TauCeti.IsLocalRing.herbrandFun_integralClosure_tower 𝒪[K] L u

/-- **Transitivity of the inverse Herbrand function** in a tower `M/L/K` of Galois extensions:
`ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`, as an identity of the inverse order isomorphisms. Inverting the
composite `φ_{L/K} ∘ φ_{M/L}` reverses its order. -/
theorem inverseHerbrand_tower :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    (herbrandOrderIso K M).symm =
      (herbrandOrderIso K L).symm.trans (herbrandOrderIso L M).symm := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  rw [herbrand_tower K L M, OrderIso.symm_trans]

/-- **Transitivity of the integral inverse Herbrand function**: `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`. -/
theorem psiNat_tower :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    psiNat K M = psiNat L M ∘ psiNat K L := funext fun n ↦ by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  have h : (⟨(psiNat K L n : ℝ), Nat.cast_mem_ramificationIndexDomain _⟩ :
        RamificationIndexDomain) =
      inverseHerbrand K L ⟨n, Nat.cast_mem_ramificationIndexDomain n⟩ :=
    Subtype.ext (coe_psiNat K L n)
  apply Nat.cast_injective (R := ℝ)
  rw [Function.comp_apply, coe_psiNat, coe_psiNat, h, ← herbrandOrderIso_symm_apply,
    inverseHerbrand_tower K L M, OrderIso.trans_apply, herbrandOrderIso_symm_apply,
    herbrandOrderIso_symm_apply]

end TauCeti.LocalFieldsRamification
