/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Quotient
import TauCeti.RingTheory.DiscreteValuationRing.Herbrand.IntegralClosure

/-!
# Transitivity of the Herbrand functions

Let `M/K` be a finite Galois extension of nonarchimedean local fields with group `G`, and let
`L` be an intermediate field Galois over `K`, so that `H = Gal(M/L)` is normal in `G` and
restriction to `L` identifies `Gal(L/K)` with `G / H`. Herbrand's theorem
`(G/H)_{φ_{M/L}(u)} = G_u H / H` has a **counting form**, `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`,
because `H_u = H ∩ G_u`. Both `φ_{M/K}` and `φ_{L/K} ∘ φ_{M/L}` are affine on each interval
`[m, m + 1]`, and the counting form says that their slopes `#G_{m+1} / #G_0` and
`(#H_{m+1} / #H_0) · (#(G/H)_{φ_{M/L}(m+1)} / #(G/H)_0)` agree; since both functions are the
identity on `[-1, 0]`, this gives the **transitivity of the Herbrand functions**

`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`   and   `ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`,

together with its integral form `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`.

## Main results

All declarations live in the namespace `TauCeti.LocalFieldsRamification`.

* `natCard_lowerRamificationGroupReal_herbrand_mul`: Herbrand's theorem in counting form,
  `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`.
* `lowerRamificationGroupReal_eq_of_forall_eq_of_herbrand_lt_of_le_herbrand`: the filtration of
  `L/K` is constant on `(φ_{M/L}(a), φ_{M/L}(b)]` when that of `M/K` is constant on `(a, b]`.
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

/-! ### Herbrand's theorem in counting form

Finiteness of `M/K` follows from that of `L/K` and `M/L` (`Module.Finite.trans`), but instance
synthesis cannot recover it, since `L` is not determined by `K` and `M`; the statements therefore
install `Module.Finite K M` with `haveI` rather than assuming it separately. -/

/-- **Herbrand's theorem in counting form.** For `G = Gal(M/K)`, `H = Gal(M/L)` and
`G/H = Gal(L/K)`, the orders satisfy `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`: the lower ramification
group of the quotient at `φ_{M/L}(u)` is the image of `G_u` under restriction to `L`, and the
kernel of restriction on `G_u` is `H ∩ G_u = H_u`. -/
theorem natCard_lowerRamificationGroupReal_herbrand_mul [Normal K L] [IsGalois L M] [Normal K M]
    (u : RamificationIndexDomain) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) *
        Nat.card (lowerRamificationGroupReal L M u) =
      Nat.card (lowerRamificationGroupReal K M u) := by
  have : Module.Finite K M := Module.Finite.trans L M
  rw [← map_restrictNormalHom_lowerRamificationGroupReal (K := K) (L := L) (M := M) u,
    ← MonoidHom.domRestrict_range,
    ← Subgroup.card_map_of_injective (K := lowerRamificationGroupReal L M u)
      (AlgEquiv.restrictScalarsHom_injective K),
    map_restrictScalarsHom_lowerRamificationGroupReal K M L u,
    AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M,
    ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype, ← MonoidHom.ker_domRestrict,
    mul_comm, Subgroup.card_ker_mul_card_range]

/-- Through Herbrand's theorem, the lower filtration of `L/K` is constant on the interval
`(φ_{M/L}(a), φ_{M/L}(b)]` as soon as that of `M/K` is constant on `(a, b]`. -/
theorem lowerRamificationGroupReal_eq_of_forall_eq_of_herbrand_lt_of_le_herbrand [Normal K L]
    [IsGalois L M] [Normal K M] {a b : RamificationIndexDomain} {t : ℝ}
    (ht₁ : (herbrand L M a : ℝ) < t) (ht₂ : t ≤ herbrand L M b) :
    haveI : Module.Finite K M := Module.Finite.trans L M
    (∀ s : ℝ, (a : ℝ) < s → s ≤ b →
      lowerRamificationGroupReal K M s = lowerRamificationGroupReal K M b) →
    lowerRamificationGroupReal K L t = lowerRamificationGroupReal K L (herbrand L M b) := by
  have : Module.Finite K M := Module.Finite.trans L M
  intro h
  set s : RamificationIndexDomain := ⟨t, Set.mem_Ici.2 ((herbrand L M a).property.trans ht₁.le)⟩
  -- `t = φ_{M/L}(ψ_{M/L}(t))` with `a < ψ_{M/L}(t) ≤ b`.
  have hs₁ : a < inverseHerbrand L M s := by
    rw [← inverseHerbrand_herbrand L M a]
    exact inverseHerbrand_strictMono L M (Subtype.coe_lt_coe.1 ht₁)
  have hs₂ : inverseHerbrand L M s ≤ b := by
    rw [← inverseHerbrand_herbrand L M b]
    exact (inverseHerbrand_strictMono L M).monotone (Subtype.coe_le_coe.1 ht₂)
  have ht : t = herbrand L M (inverseHerbrand L M s) := by rw [herbrand_inverseHerbrand]
  rw [ht, ← map_restrictNormalHom_lowerRamificationGroupReal,
    ← map_restrictNormalHom_lowerRamificationGroupReal, h _ hs₁ hs₂]

/-! ### Transitivity of the Herbrand functions

Here `L/K` and `M/K` are Galois, so `M/L` is Galois as well (`IsGalois.tower_top_of_isGalois`).
Since `L` is an arbitrary field rather than an `IntermediateField K M`, instance synthesis cannot
recover `IsGalois L M` from `[IsGalois K M]`; the statements below therefore install it with
`haveI` as well. -/

section Helpers

open TauCeti.IsLocalRing _root_.IsLocalRing _root_.IsDiscreteValuationRing in
/-- Internal helper sharing the integral-closure tower instance setup and the three lower
ramification group identifications `(M/K, M/L, L/K)` between `herbrand_tower` and
`tower_integralClosure_bridge`. -/
theorem withIntegralClosureTower [Module.Finite K M] {P : Prop}
    (hP : ∀ [IsScalarTower 𝒪[K] L M]
      [IsDiscreteValuationRing (integralClosure 𝒪[K] M)]
      [IsLocalHom (algebraMap 𝒪[K] (integralClosure 𝒪[K] M))]
      [Finite (ResidueField (integralClosure 𝒪[K] M))]
      [IsLocalRing (integralClosure 𝒪[K] L)],
      (∀ i : ℤ, ramificationGroup (M ≃ₐ[K] M) 𝒪[M] i =
        (ramificationGroup (M ≃ₐ[K] M) (integralClosure 𝒪[K] M) i).comap (MonoidHom.id _)) →
      (∀ i : ℤ, ramificationGroup (M ≃ₐ[L] M) 𝒪[M] i =
        (ramificationGroup (M ≃ₐ[L] M) (integralClosure 𝒪[K] M) i).comap (MonoidHom.id _)) →
      (∀ i : ℤ, ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i =
        (ramificationGroup (L ≃ₐ[K] L) (integralClosure 𝒪[K] L) i).comap (MonoidHom.id _)) →
      P) : P := by
  let _ := IsScalarTower.to₁₃₄ 𝒪[K] K L M
  let eM := TauCeti.integerRingEquivIntegralClosure K M
  have := RingEquivClass.isDiscreteValuationRing eM
  have : IsLocalHom (algebraMap 𝒪[K] (integralClosure 𝒪[K] M)) :=
    eM.toAlgHom.comp_algebraMap ▸ inferInstance
  have := Finite.of_equiv (ResidueField 𝒪[M]) (ResidueField.mapEquiv eM.toRingEquiv).toEquiv
  let _ := TauCeti.isLocalRing_integralClosure_of_tower 𝒪[K] L M
  exact hP
    (ramificationGroup_integerRing_eq_comap_integralClosure K K M)
    (ramificationGroup_integerRing_eq_comap_integralClosure K L M)
    (ramificationGroup_integerRing_eq_comap_integralClosure K K L)

end Helpers

variable [IsGalois K L] [IsGalois K M]

open TauCeti.IsLocalRing in
/-- **Transitivity of the Herbrand function** in a tower `M/L/K` of Galois extensions:
`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`, as an identity of the bundled order isomorphisms of
`RamificationIndexDomain`. -/
theorem herbrand_tower :
    haveI : Module.Finite K M := Module.Finite.trans L M
    haveI := IsGalois.tower_top_of_isGalois K L M
    herbrandOrderIso K M = (herbrandOrderIso L M).trans (herbrandOrderIso K L) := by
  have : Module.Finite K M := Module.Finite.trans L M
  have := IsGalois.tower_top_of_isGalois K L M
  refine withIntegralClosureTower K L M fun hMK hML hLK ↦ ?_
  refine OrderIso.ext <| funext fun u ↦ Subtype.ext ?_
  simp only [OrderIso.trans_apply, herbrandOrderIso_apply, coe_herbrand_eq_herbrandFun,
    herbrandFun_eq_of_ramificationGroup_eq_comap Function.bijective_id hMK,
    herbrandFun_eq_of_ramificationGroup_eq_comap Function.bijective_id hLK,
    herbrandFun_eq_of_ramificationGroup_eq_comap Function.bijective_id hML]
  exact herbrandFun_integralClosure_tower 𝒪[K] L u

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
