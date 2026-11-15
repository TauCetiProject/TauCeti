/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.Degree
public import TauCeti.NumberTheory.HeckeRing.Map.SubgroupExtension
public import TauCeti.NumberTheory.HeckeRing.Map.Submonoid

import Mathlib.Tactic.Group
import TauCeti.GroupTheory.Coset.Basic

/-!
# Transporting Hecke rings and degrees along group homomorphisms and extensions

This file completes the functoriality toolkit for abstract Hecke rings in two directions:

1. **Degree preservation** along `HeckeCoset.map`: both submonoid widening
   (`HeckeCosetModule.mapSubmonoidRingHom`) and subgroup extension under a stabilizer-coset
   transversal condition (`HeckeCosetModule.mapSubgroupRingEquiv`) preserve double-coset degrees
   (`HeckeCoset.degree`) and the degree ring homomorphism (`LeftCosetModule.deg`).
2. **Injective group homomorphisms** `φ : G →* K`: pushing `(Δ, H₁, H₂)` forward to
   `(Δ.map φ, H₁.map φ, H₂.map φ)` preserves `IsHeckeTriple`, Shimura's double-coset
   multiplicities, double-coset degrees, and the Hecke ring structure over any coefficient
   semiring `R` (`HeckeCosetModule.mapInjectiveRingEquiv`).

## Main definitions and results

* `HeckeCoset.degree_map_of_le`, `HeckeCosetModule.deg_mapSubmonoidRingHom`: submonoid widening
  preserves `HeckeCoset.degree` and `LeftCosetModule.deg`.
* `HeckeCoset.degree_mapEquivOfInf`, `HeckeCosetModule.deg_mapSubgroupRingEquiv`: subgroup
  extension preserves `HeckeCoset.degree` and `LeftCosetModule.deg`.
* `DoubleCoset.multiplicity_map_of_injective`: an injective group homomorphism preserves Shimura's
  multiplicity without finiteness assumptions.
* `IsHeckeTriple.map_of_injective`: an injective group homomorphism transports a Hecke triple to
  its image.
* `HeckeCoset.mapHom`, `HeckeCoset.mapEquivOfInjective`, `HeckeCoset.degree_mapHom_of_injective`:
  pushforward of Hecke cosets along a group homomorphism, its bijectivity and degree preservation
  under injectivity.
* `HeckeCosetModule.mapInjectiveLinearEquiv`, `HeckeCosetModule.mapInjectiveRingEquiv`,
  `HeckeCosetModule.deg_mapInjectiveRingEquiv`: the induced linear and ring isomorphisms
  `𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R` and their compatibility with `LeftCosetModule.deg`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1–3.2.
-/

public section

open Subgroup Subgroup.Commensurable DoubleCoset
open scoped Pointwise HeckeCosetModule

section DegreeCompatibility

variable {G : Type*} [Group G]

namespace HeckeCoset

variable {Δ Δ₁ Δ₂ Δ' : Submonoid G} {H₁ H₂ H H' P : Subgroup G}

/-- Widening the ambient submonoid while keeping the subgroups fixed preserves the degree of every
double coset. -/
@[simp]
theorem degree_map_of_le (hΔ : Δ₁ ≤ Δ₂) (D : HeckeCoset Δ₁ H₁ H₂) :
    (D.map hΔ le_rfl le_rfl).degree = D.degree := by
  induction D using HeckeCoset.induction with | h g => simp

/-- Extending both subgroup and submonoid under `H = H' ⊓ P` and the stabilizer-coset condition
preserves the degree of every double coset. -/
theorem degree_mapEquivOfInf (hHP : H = H' ⊓ P) (hΔ : Δ ≤ Δ') (hΔP : Δ ≤ P.toSubmonoid)
    (hsurj : ∀ δ' : Δ', ∃ u ∈ H', u * (δ' : G) ∈ Δ)
    (hstab : ∀ g : Δ, ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct (g : G) • H')
    (D : HeckeCoset Δ H H) :
    (mapEquivOfInf hHP hΔ hΔP hsurj hstab D).degree = D.degree := by
  induction D using HeckeCoset.induction with | h g =>
  rw [mapEquivOfInf_apply, map_mk, degree_mk, degree_mk, Submonoid.coe_inclusion]
  exact (Nat.card_congr (decompQuotientEquivOfInf hHP (hΔP g.2) (hstab g))).symm

end HeckeCoset

namespace HeckeCosetModule

variable (R : Type*) [Semiring R] {Δ Δ₁ Δ₂ Δ' : Submonoid G} {H H' P : Subgroup G}

/-- `mapSubmonoidRingHom` preserves the degree homomorphism `LeftCosetModule.deg`. -/
@[simp]
theorem deg_mapSubmonoidRingHom [IsHeckeTriple Δ₁ H H] [IsHeckeTriple Δ₂ H H]
    (hΔ : Δ₁ ≤ Δ₂) (f : 𝕋 Δ₁ H R) :
    LeftCosetModule.deg Δ₂ H R (mapSubmonoidRingHom R hΔ f) = LeftCosetModule.deg Δ₁ H R f := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hsingle D b => simp

/-- Precomposing `LeftCosetModule.deg` with `mapSubmonoidRingHom` recovers `LeftCosetModule.deg`. -/
@[simp]
theorem deg_comp_mapSubmonoidRingHom [IsHeckeTriple Δ₁ H H] [IsHeckeTriple Δ₂ H H]
    (hΔ : Δ₁ ≤ Δ₂) :
    (LeftCosetModule.deg Δ₂ H R).comp (mapSubmonoidRingHom R hΔ) = LeftCosetModule.deg Δ₁ H R :=
  RingHom.ext (deg_mapSubmonoidRingHom R hΔ)

/-- `mapSubgroupRingEquiv` preserves the degree homomorphism `LeftCosetModule.deg`. -/
@[simp]
theorem deg_mapSubgroupRingEquiv [IsHeckeTriple Δ H H] [IsHeckeTriple Δ' H' H']
    (hHP : H = H' ⊓ P) (hΔ : Δ ≤ Δ') (hΔP : Δ ≤ P.toSubmonoid)
    (hsurj : ∀ δ' : Δ', ∃ u ∈ H', u * (δ' : G) ∈ Δ)
    (hstab : ∀ g : Δ, ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct (g : G) • H')
    (f : 𝕋 Δ H R) :
    LeftCosetModule.deg Δ' H' R (mapSubgroupRingEquiv R hHP hΔ hΔP hsurj hstab f) =
      LeftCosetModule.deg Δ H R f := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hsingle D b =>
    rw [mapSubgroupRingEquiv_single, LeftCosetModule.deg_single, LeftCosetModule.deg_single,
      ← HeckeCoset.mapEquivOfInf_apply hHP hΔ hΔP hsurj hstab, HeckeCoset.degree_mapEquivOfInf]

/-- Precomposing `LeftCosetModule.deg` with `mapSubgroupRingEquiv` recovers
`LeftCosetModule.deg`. -/
@[simp]
theorem deg_comp_mapSubgroupRingEquiv [IsHeckeTriple Δ H H] [IsHeckeTriple Δ' H' H']
    (hHP : H = H' ⊓ P) (hΔ : Δ ≤ Δ') (hΔP : Δ ≤ P.toSubmonoid)
    (hsurj : ∀ δ' : Δ', ∃ u ∈ H', u * (δ' : G) ∈ Δ)
    (hstab : ∀ g : Δ, ∀ u ∈ H', ∃ x ∈ H, x⁻¹ * u ∈ ConjAct.toConjAct (g : G) • H') :
    (LeftCosetModule.deg Δ' H' R).comp
        ↑(mapSubgroupRingEquiv R hHP hΔ hΔP hsurj hstab) =
      LeftCosetModule.deg Δ H R :=
  RingHom.ext (deg_mapSubgroupRingEquiv R hHP hΔ hΔP hsurj hstab)

end HeckeCosetModule

end DegreeCompatibility

section InjectiveHom

variable {G K : Type*} [Group G] [Group K]

namespace DoubleCoset

private lemma decompQuotientEquivMapOfInjective_out (φ : G →* K) (hφ : Function.Injective φ)
    (H₁ H₂ : Subgroup G) (g : G) (i : DecompQuotient H₁ H₂ g) :
    (φ g)⁻¹ * (((decompQuotientEquivMapOfInjective φ hφ H₁ H₂ g i).out : K)⁻¹ *
      φ (i.out : G)) * φ g ∈ H₂.map φ := by
  have hmk :
      ((decompQuotientEquivMapOfInjective φ hφ H₁ H₂ g i).out :
          DecompQuotient (H₁.map φ) (H₂.map φ) (φ g)) =
        (Subgroup.equivMapOfInjective H₁ φ hφ i.out :
          DecompQuotient (H₁.map φ) (H₂.map φ) (φ g)) := by
    calc _ = decompQuotientEquivMapOfInjective φ hφ H₁ H₂ g i := QuotientGroup.out_eq' _
      _ = decompQuotientEquivMapOfInjective φ hφ H₁ H₂ g (i.out : DecompQuotient H₁ H₂ g) :=
        congrArg (decompQuotientEquivMapOfInjective φ hφ H₁ H₂ g) (QuotientGroup.out_eq' i).symm
      _ = _ := decompQuotientEquivMapOfInjective_mk φ hφ H₁ H₂ g i.out
  exact conj_mem_of_mk_eq (φ g) hmk

/-- **Shimura's multiplicity is invariant under an injective group homomorphism**, with no
finiteness assumptions. -/
theorem multiplicity_map_of_injective (φ : G →* K) (hφ : Function.Injective φ)
    (H₁ H₂ H₃ : Subgroup G) (g h d : G) :
    multiplicity (H₁.map φ) (H₂.map φ) (H₃.map φ) (φ g) (φ h) (φ d) =
      multiplicity H₁ H₂ H₃ g h d := by
  let eg := decompQuotientEquivMapOfInjective φ hφ H₁ H₂ g
  let eh := decompQuotientEquivMapOfInjective φ hφ H₂ H₃ h
  let c : DecompQuotient H₁ H₂ g → H₂.map φ := fun i ↦
    ⟨(φ g)⁻¹ * (((eg i).out : K)⁻¹ * φ (i.out : G)) * φ g,
      decompQuotientEquivMapOfInjective_out φ hφ H₁ H₂ g i⟩
  let epairs := Equiv.prodShear eg fun i ↦ eh.trans (MulAction.toPerm (c i))
  rw [multiplicity_def, multiplicity_def]
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv epairs fun ⟨i, j⟩ ↦ ?_)
  let q := c i • eh j
  have hprod :
      (((eg i).out : K) * φ g * ((q.out : K) * φ h) : K ⧸ (H₃.map φ)) =
        (φ ((i.out : G) * g * ((j.out : G) * h)) : K ⧸ (H₃.map φ)) := by
    rw [QuotientGroup.eq]
    have hm := (H₃.map φ).mul_mem
      (conj_mem_of_mk_eq (φ h) (QuotientGroup.mk_out_smul (c i) (eh j)))
      (decompQuotientEquivMapOfInjective_out φ hφ H₂ H₃ h j)
    dsimp only [q, c, eh, Subtype.coe_mk] at hm ⊢
    simpa only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hm
  dsimp only [epairs, Equiv.prodShear_apply, Equiv.trans_apply, MulAction.toPerm_apply]
  change
    (((i.out : G) * g * ((j.out : G) * h) : G ⧸ H₃) = (d : G ⧸ H₃)) ↔
      ((((eg i).out : K) * φ g * ((q.out : K) * φ h) : K ⧸ (H₃.map φ)) =
        (φ d : K ⧸ (H₃.map φ)))
  rw [hprod, QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul,
    Subgroup.mem_map_iff_mem hφ]

end DoubleCoset

namespace IsHeckeTriple

private lemma map_pointwise_conjAct (φ : G →* K) (x : G) (H : Subgroup G) :
    ConjAct.toConjAct (φ x) • H.map φ = (ConjAct.toConjAct x • H).map φ := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map,
    ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨x * z * x⁻¹, by simpa [mul_assoc] using hz, ?_⟩
    calc φ (x * z * x⁻¹) = φ x * φ z * (φ x)⁻¹ := by simp [mul_assoc]
      _ = y := by rw [hzy]; group
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x⁻¹ * z * x, hz, by simp [mul_assoc]⟩

/-- Pushing a Hecke triple `(Δ, H₁, H₂)` forward along an injective group homomorphism `φ : G →* K`
yields a Hecke triple `(Δ.map φ, H₁.map φ, H₂.map φ)`. -/
theorem map_of_injective {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [IsHeckeTriple Δ H₁ H₂]
    (φ : G →* K) (hφ : Function.Injective φ) :
    IsHeckeTriple (Δ.map φ) (H₁.map φ) (H₂.map φ) where
  left_le := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, IsHeckeTriple.mem_of_mem_left H₂ hx, rfl⟩
  right_le := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, IsHeckeTriple.mem_of_mem_right H₁ hx, rfl⟩
  commensurable :=
    ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr <| by
        rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
        exact (IsHeckeTriple.commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).1.relIndex_ne_zero,
      Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr <| by
        rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
        exact (IsHeckeTriple.commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).2.relIndex_ne_zero⟩
  le_commensurator_right := by
    rintro _ ⟨g, hg, rfl⟩
    have hg_comm : Subgroup.Commensurable (ConjAct.toConjAct g • H₂) H₂ :=
      IsHeckeTriple.mem_commensurator_right H₁ ⟨g, hg⟩
    rw [Subgroup.mem_toSubmonoid, commensurator_mem_iff]
    have hbridge (y : K) (L : Subgroup K) : MulAut.conj y • L = ConjAct.toConjAct y • L := by
      ext z
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv MulAut.conj,
        ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul_eq_mulAut_conj, MulAut.smul_def]
    rw [hbridge, map_pointwise_conjAct]
    exact ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr <| by
        rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
        exact hg_comm.1.relIndex_ne_zero,
      Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr <| by
        rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
        exact hg_comm.2.relIndex_ne_zero⟩

end IsHeckeTriple

namespace HeckeCoset

variable {Δ : Submonoid G} {H₁ H₂ H : Subgroup G}

/-- Push a Hecke double coset forward along a group homomorphism `φ : G →* K`. -/
def mapHom (φ : G →* K) (D : HeckeCoset Δ H₁ H₂) :
    HeckeCoset (Δ.map φ) (H₁.map φ) (H₂.map φ) :=
  Quotient.map (fun g : Δ ↦ (⟨φ g, ⟨g, g.2, rfl⟩⟩ : ↥(Δ.map φ)))
    (fun a b hab ↦ by
      obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hb⟩ := DoubleCoset.rel_iff.mp hab
      refine DoubleCoset.rel_iff.mpr ⟨φ γ₁, ⟨γ₁, hγ₁, rfl⟩, φ γ₂, ⟨γ₂, hγ₂, rfl⟩, ?_⟩
      simpa [mul_assoc] using congrArg φ hb) D

/-- Computation rule for `HeckeCoset.mapHom` on an explicit coset `mk H₁ H₂ g`. -/
@[simp]
theorem mapHom_mk (φ : G →* K) (g : Δ) :
    (mk H₁ H₂ g).mapHom φ = mk (H₁.map φ) (H₂.map φ) (⟨φ g, ⟨g, g.2, rfl⟩⟩ : ↥(Δ.map φ)) := (rfl)

/-- `HeckeCoset.mapHom` sends the identity coset to the identity coset. -/
@[simp]
theorem mapHom_one (φ : G →* K) :
    (1 : HeckeCoset Δ H H).mapHom φ = (1 : HeckeCoset (Δ.map φ) (H.map φ) (H.map φ)) := by
  rw [one_def, one_def, mapHom_mk]
  exact mk_congr_val (_root_.map_one φ)

/-- When `φ : G →* K` is injective, `HeckeCoset.mapHom φ` is bijective. -/
theorem mapHom_bijective {φ : G →* K} (hφ : Function.Injective φ) :
    Function.Bijective (mapHom (Δ := Δ) (H₁ := H₁) (H₂ := H₂) φ) := by
  refine ⟨fun D₁ D₂ hEq ↦ ?_, fun E ↦ ?_⟩
  · induction D₁ using HeckeCoset.induction with | h g₁ =>
    induction D₂ using HeckeCoset.induction with | h g₂ =>
    rw [mapHom_mk, mapHom_mk, eq_iff] at hEq
    obtain ⟨_, ⟨γ₁, hγ₁, rfl⟩, _, ⟨γ₂, hγ₂, rfl⟩, hmul⟩ :=
      mem_doubleCoset.mp (hEq ▸ mem_doubleCoset_self (H₁.map φ) (H₂.map φ) _)
    exact mk_eq_mk_of_mem (mem_doubleCoset.mpr ⟨γ₁, hγ₁, γ₂, hγ₂,
      hφ (by simpa [mul_assoc] using hmul)⟩)
  · induction E using HeckeCoset.induction with | h y =>
    obtain ⟨g, hg, hy⟩ := y.2
    refine ⟨mk H₁ H₂ ⟨g, hg⟩, ?_⟩
    rw [mapHom_mk]
    exact mk_congr_val hy

/-- Equivalence of Hecke double cosets induced by an injective group homomorphism `φ : G →* K`. -/
noncomputable def mapEquivOfInjective (φ : G →* K) (hφ : Function.Injective φ) :
    HeckeCoset Δ H₁ H₂ ≃ HeckeCoset (Δ.map φ) (H₁.map φ) (H₂.map φ) :=
  Equiv.ofBijective (mapHom φ) (mapHom_bijective hφ)

/-- `mapEquivOfInjective` computes as `HeckeCoset.mapHom`. -/
@[simp]
theorem mapEquivOfInjective_apply (φ : G →* K) (hφ : Function.Injective φ)
    (D : HeckeCoset Δ H₁ H₂) :
    mapEquivOfInjective φ hφ D = D.mapHom φ := (rfl)

/-- An injective group homomorphism preserves the degree of every double coset. -/
@[simp]
theorem degree_mapHom_of_injective {φ : G →* K} (hφ : Function.Injective φ)
    (D : HeckeCoset Δ H₁ H₂) :
    (D.mapHom φ).degree = D.degree := by
  induction D using HeckeCoset.induction with | h g =>
  rw [mapHom_mk, degree_mk, degree_mk]
  exact (Nat.card_congr (decompQuotientEquivMapOfInjective φ hφ H₁ H₂ (g : G))).symm

end HeckeCoset

namespace HeckeCosetModule

variable (R : Type*) [Semiring R] {Δ : Submonoid G} {H : Subgroup G}

/-- `R`-linear equivalence `𝕋 Δ H R ≃ₗ[R] 𝕋 (Δ.map φ) (H.map φ) R` induced by an injective group
homomorphism `φ : G →* K`. -/
noncomputable def mapInjectiveLinearEquiv (φ : G →* K) (hφ : Function.Injective φ) :
    𝕋 Δ H R ≃ₗ[R] 𝕋 (Δ.map φ) (H.map φ) R :=
  Finsupp.mapDomain.linearEquiv R R (HeckeCoset.mapEquivOfInjective φ hφ)

/-- Evaluating `mapInjectiveLinearEquiv` at `D.mapHom φ` recovers the coefficient at `D`. -/
@[simp]
theorem mapInjectiveLinearEquiv_apply_mapHom (φ : G →* K) (hφ : Function.Injective φ)
    (f : 𝕋 Δ H R) (D : HeckeCoset Δ H H) :
    mapInjectiveLinearEquiv R φ hφ f (D.mapHom φ) = f D :=
  Finsupp.mapDomain_apply_of_injective (HeckeCoset.mapHom_bijective hφ).1 f D

/-- `mapInjectiveLinearEquiv` sends each basis element to the mapped basis element. -/
@[simp]
theorem mapInjectiveLinearEquiv_single (φ : G →* K) (hφ : Function.Injective φ)
    (D : HeckeCoset Δ H H) (b : R) :
    mapInjectiveLinearEquiv R φ hφ (single R D b) = single R (D.mapHom φ) b :=
  mapDomain_single R _ D b

private lemma rep_mapHom_mem_doubleCoset (φ : G →* K) (D : HeckeCoset Δ H H) :
    (((D.mapHom φ).rep : ↥(Δ.map φ)) : K) ∈
      doubleCoset (φ (D.rep : G)) (H.map φ) (H.map φ) := by
  let w : ↥(Δ.map φ) := ⟨φ (D.rep : G), ⟨D.rep, D.rep.2, rfl⟩⟩
  have hmap : D.mapHom φ = HeckeCoset.mk (H.map φ) (H.map φ) w := by
    conv_lhs => rw [← HeckeCoset.mk_rep D, HeckeCoset.mapHom_mk]
  simpa only [hmap] using
    HeckeCoset.rep_mk_mem_doubleCoset (H₁ := H.map φ) (H₂ := H.map φ) w

/-- `mapInjectiveLinearEquiv` sends structure constants on `(Δ, H)` to structure constants on
`(Δ.map φ, H.map φ)`. -/
theorem mapInjectiveLinearEquiv_structureConstants (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
    (D₁ D₂ : HeckeCoset Δ H H) :
    mapInjectiveLinearEquiv R φ hφ (structureConstants R H H H D₁.rep D₂.rep) =
      structureConstants R (H.map φ) (H.map φ) (H.map φ)
        (D₁.mapHom φ).rep (D₂.mapHom φ).rep := by
  ext E
  obtain ⟨D, rfl⟩ := (HeckeCoset.mapHom_bijective hφ).2 E
  rw [mapInjectiveLinearEquiv_apply_mapHom, structureConstants_apply, structureConstants_apply,
    multiplicity_doubleCoset_congr_first (H.map φ) (H.map φ) (H.map φ) _ _
      (rep_mapHom_mem_doubleCoset φ D₁),
    multiplicity_doubleCoset_congr_second (H.map φ) (H.map φ) (H.map φ) _ _
      (rep_mapHom_mem_doubleCoset φ D₂),
    multiplicity_doubleCoset_congr _ _ (rep_mapHom_mem_doubleCoset φ D),
    multiplicity_map_of_injective φ hφ H H H (D₁.rep : G) (D₂.rep : G) (D.rep : G)]

/-- `mapInjectiveLinearEquiv` preserves the Hecke convolution product. -/
theorem mapInjectiveLinearEquiv_mul (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
    (f g : 𝕋 Δ H R) :
    mapInjectiveLinearEquiv R φ hφ (f * g) =
      mapInjectiveLinearEquiv R φ hφ f * mapInjectiveLinearEquiv R φ hφ g := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd _ _ ih₁ ih₂ => rw [_root_.add_mul, map_add, map_add, ih₁, ih₂, _root_.add_mul]
  | hsingle D₁ a =>
    induction g using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd _ _ ih₁ ih₂ => rw [_root_.mul_add, map_add, map_add, ih₁, ih₂, _root_.mul_add]
    | hsingle D₂ b =>
      rw [single_mul_single, map_smul, map_smul,
        mapInjectiveLinearEquiv_structureConstants R φ hφ,
        mapInjectiveLinearEquiv_single, mapInjectiveLinearEquiv_single, single_mul_single]

/-- **Injective-homomorphism isomorphism for Hecke rings**: an injective group homomorphism
`φ : G →* K` induces a ring isomorphism `𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R` over any coefficient
semiring `R`. -/
noncomputable def mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)] :
    𝕋 Δ H R ≃+* 𝕋 (Δ.map φ) (H.map φ) R :=
  { mapInjectiveLinearEquiv R φ hφ with
    map_mul' := mapInjectiveLinearEquiv_mul R φ hφ }

/-- `mapInjectiveRingEquiv` sends each basis element `single R D b` to `single R (D.mapHom φ) b`. -/
@[simp]
theorem mapInjectiveRingEquiv_single (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
    (D : HeckeCoset Δ H H) (b : R) :
    mapInjectiveRingEquiv R φ hφ (single R D b) = single R (D.mapHom φ) b :=
  mapInjectiveLinearEquiv_single R φ hφ D b

/-- The inverse of `mapInjectiveRingEquiv` sends `single R (D.mapHom φ) b` back to
`single R D b`. -/
@[simp]
theorem mapInjectiveRingEquiv_symm_single_mapHom (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
    (D : HeckeCoset Δ H H) (b : R) :
    (mapInjectiveRingEquiv R φ hφ).symm (single R (D.mapHom φ) b) = single R D b :=
  (mapInjectiveRingEquiv R φ hφ).injective (by simp)

/-- `mapInjectiveRingEquiv` preserves the degree homomorphism `LeftCosetModule.deg`. -/
@[simp]
theorem deg_mapInjectiveRingEquiv (φ : G →* K) (hφ : Function.Injective φ)
    [IsHeckeTriple Δ H H] [IsHeckeTriple (Δ.map φ) (H.map φ) (H.map φ)]
    (f : 𝕋 Δ H R) :
    LeftCosetModule.deg (Δ.map φ) (H.map φ) R (mapInjectiveRingEquiv R φ hφ f) =
      LeftCosetModule.deg Δ H R f := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hsingle D b => simp [HeckeCoset.degree_mapHom_of_injective hφ]

end HeckeCosetModule

end InjectiveHom

end
