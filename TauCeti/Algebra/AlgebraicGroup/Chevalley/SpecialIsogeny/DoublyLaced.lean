/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SpecialIsogeny.Basic
import TauCeti.Algebra.CharP.Two
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.RootString
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Characteristic-two commutator relations and simple-root determination for `B₂` and `F₄`

Over `[ExpChar A 2]`, `b2SpecialIsogenyRootSubgroup` and `f4SpecialIsogenyRootSubgroup` satisfy all
Chevalley commutator relations of the source root system. Any group homomorphism
`D.points A →* E.points A` agreeing with these maps on the positive and negative simple root
subgroups agrees with them on every root subgroup, and any endomorphism `D.points A →* D.points A`
agreeing with them on the positive and negative simple root subgroups squares to
`D.frobenius 2 1 A` on `D.elementarySubgroup A`.
-/

public section

open scoped commutatorElement

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative RootPairingIsogeny

universe v

private theorem charTwoOfExpChar (A : Type*) [CommRing A] [ExpChar A 2] : CharP A 2 :=
  (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
attribute [local instance] charTwoOfExpChar
section DoublyLacedAux
private noncomputable abbrev scD (t : DynkinType) (ht : t.Valid) := t.simplyConnectedRootDatum ht
private structure DoublyLacedIso (t : DynkinType) (ht : t.Valid) where
  iso : RootPairingIsogeny (scD t ht) (scD t ht)
  mul_self : iso * iso = smulId (scD t ht) 2
  exp_or : ∀ α, iso.exponent α = 1 ∨ iso.exponent α = 2
  σ : Equiv.Perm (Fin t.rank)
  idx_simple : ∀ i, iso.indexEquiv (t.simpleIndex ht i) = t.simpleIndex ht (σ i)
  sym : ∀ α β, iso.exponent α * (scD t ht).pairing β α = iso.exponent β * (scD t ht).pairing α β

private noncomputable abbrev partnerPt {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) (A : Type v) [CommRing A] (α : Fin t.numRoots) (u : A) : D.points A :=
  D.rootSubgroupPoints (F.iso.indexEquiv α) A
    (ofAdd (u ^ (F.iso.exponent (F.iso.indexEquiv α)).toNat))

section WithDatum
variable {t : DynkinType} {ht : t.Valid}
local notation "Φ" => scD t ht
local notation "N" => t.structureConstant ht
local notation "scOr" => structureConstant_eq_natCast_or_eq_neg_natCast
private abbrev lenAdd (F : DoublyLacedIso t ht) :=
  (Φ).length_of_root_eq_add_zsmul F.iso.exponent F.sym

private theorem cast_sc_eq_one {α β : Fin t.numRoots}
    (hsum : (Φ).root α + (Φ).root β ∈ Set.range (Φ).root) (hbot : (Φ).chainBotCoeff α β = 0)
    (A : Type*) [CommRing A] [CharP A 2] : (N α β : A) = 1 := by
  rcases scOr hsum with h | h <;> simp [h, hbot, CharTwo.neg_one_eq_one]
private theorem cast_sc_eq_zero {α β : Fin t.numRoots}
    (hsum : (Φ).root α + (Φ).root β ∈ Set.range (Φ).root) (hbot : (Φ).chainBotCoeff α β = 1)
    (A : Type*) [CommRing A] [CharP A 2] : (N α β : A) = 0 := by
  rcases scOr hsum with h | h <;> simp [h, hbot, CharTwo.two_eq_zero]
private theorem cast_div_two_eq_one {α β γ : Fin t.numRoots}
    (hαβ : (Φ).root α + (Φ).root β ∈ Set.range (Φ).root)
    (hαγ : (Φ).root α + (Φ).root γ ∈ Set.range (Φ).root) (hbot₁ : (Φ).chainBotCoeff α β = 0)
    (hbot₂ : (Φ).chainBotCoeff α γ = 1) (A : Type*) [CommRing A] [CharP A 2] :
    ((N α β * N α γ / 2 : ℤ) : A) = 1 := by
  rcases scOr hαβ with h1 | h1 <;> rcases scOr hαγ with h3 | h3 <;> rw [h1, h3, hbot₁, hbot₂] <;>
    norm_num <;> exact CharTwo.neg_one_eq_one

private theorem abs_pairing_le_two (F : DoublyLacedIso t ht) (α β : Fin t.numRoots) :
    |(Φ).pairing α β| ≤ 2 := by
  have : Module.IsReflexive ℤ (Fin t.rank → ℤ) := .of_isPerfPair (Φ).toLinearMap
  have hpi (i j) : (Φ).pairingIn ℤ i j = (Φ).pairing i j := by
    simpa using (Φ).algebraMap_pairingIn ℤ i j
  have hw := (Φ).coxeterWeightIn_le_four ℤ α β; rw [RootPairing.coxeterWeightIn, hpi, hpi] at hw
  have hs := F.sym α β; rw [abs_le]
  rcases F.exp_or α with hα | hα <;> rcases F.exp_or β with hβ | hβ <;> rw [hα, hβ] at hs <;>
    constructor <;> nlinarith

private theorem exp_partner_mul (F : DoublyLacedIso t ht) (α : Fin t.numRoots) :
    F.iso.exponent α * F.iso.exponent (F.iso.indexEquiv α) = 2 := by
  simpa using F.iso.exponent_mul_exponent_indexEquiv Φ F.mul_self α
private theorem exp_partner_eq_two (F : DoublyLacedIso t ht) {α : Fin t.numRoots}
    (h : F.iso.exponent α = 1) : F.iso.exponent (F.iso.indexEquiv α) = 2 := by
  have hm := exp_partner_mul F α; rw [h] at hm; omega
private theorem exp_partner_eq_one (F : DoublyLacedIso t ht) {α : Fin t.numRoots}
    (h : F.iso.exponent α = 2) : F.iso.exponent (F.iso.indexEquiv α) = 1 := by
  have hm := exp_partner_mul F α; rw [h] at hm; omega

private theorem not_two_nsmul_add_mem_of_exp_eq (F : DoublyLacedIso t ht) {α β : Fin t.numRoots}
    (hαβ : F.iso.exponent α = F.iso.exponent β) (h0 : (Φ).root α + (Φ).root β ≠ 0) :
    2 • (Φ).root α + (Φ).root β ∉ Set.range (Φ).root := fun ⟨γ, hγ⟩ => by
  refine (Φ).not_root_eq_add_nsmul_of_length_eq_of_two_le F.iso.exponent F.sym α β γ 2
    (F.iso.exponent_pos α) hαβ ?_ (fun hneg => h0 (by rw [hneg, add_neg_cancel])) (by omega)
    (by rw [hγ]; module)
  rcases F.exp_or α with _ | _ <;> rcases F.exp_or γ with _ | _ <;> omega

private theorem not_two_nsmul_long_add_short_mem_range (F : DoublyLacedIso t ht)
    {α β : Fin t.numRoots} (hα : F.iso.exponent α = 2) (hβ : F.iso.exponent β = 1) :
    2 • (Φ).root α + (Φ).root β ∉ Set.range (Φ).root := fun ⟨ρ, hρ⟩ =>
  absurd ((Φ).n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
    F.iso.exponent F.sym α β ρ 2 (abs_pairing_le_two F α β) hα hβ (F.exp_or ρ) (by omega)
    (by rw [hρ]; module)).left (by decide)

private theorem root_add_mem_of_two_smul_mem (F : DoublyLacedIso t ht) {α β γ : Fin t.numRoots}
    (h0 : (Φ).root α + (Φ).root β ≠ 0) (hγ : (Φ).root γ = (Φ).root β + (2 : ℤ) • (Φ).root α) :
    (Φ).root β + (Φ).root α ∈ Set.range (Φ).root := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : Module.IsReflexive ℤ (Fin t.rank → ℤ) := .of_isPerfPair (Φ).toLinearMap
  have hne : α ≠ β := fun heq => by
    subst heq; have hlen := lenAdd F α α γ 2 hγ; rw [(Φ).pairing_same] at hlen
    rcases F.exp_or α with h1 | h1 <;> rcases F.exp_or γ with h2 | h2 <;> rw [h1, h2] at hlen <;>
      omega
  have hlin := RootPairing.IsReduced.linearIndependent Φ hne
    (fun hn => h0 (by rw [hn, neg_add_cancel]))
  have htop : 2 ≤ (Φ).chainTopCoeff α β :=
    ((Φ).root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mp ⟨γ, by rw [hγ]; module⟩
  simpa only [one_nsmul] using
    ((Φ).root_add_nsmul_mem_range_iff_le_chainTopCoeff (n := 1) hlin).mpr (by omega)

private theorem partner_exponents_of_notMem (F : DoublyLacedIso t ht) {α β γ' : Fin t.numRoots}
    (h : (Φ).root α + (Φ).root β ∉ Set.range (Φ).root) (h0 : (Φ).root α + (Φ).root β ≠ 0)
    (hγ' : (Φ).root γ' = (Φ).root (F.iso.indexEquiv α) + (Φ).root (F.iso.indexEquiv β)) :
    F.iso.exponent (F.iso.indexEquiv α) = 1 ∧ F.iso.exponent (F.iso.indexEquiv β) = 1 ∧
      F.iso.exponent γ' = 2 := by
  have hw := congrArg F.iso.weightMap hγ'
  rw [map_add, F.iso.root_weightMap, F.iso.weightMap_root_indexEquiv Φ F.mul_self,
    F.iso.weightMap_root_indexEquiv Φ F.mul_self, Int.cast_id] at hw
  have hlen := lenAdd F (F.iso.indexEquiv α) (F.iso.indexEquiv β) γ' 1 (by rw [hγ']; module)
  have hs := F.sym (F.iso.indexEquiv α) (F.iso.indexEquiv β)
  rcases F.exp_or (F.iso.indexEquiv α) with hα' | hα' <;>
    rcases F.exp_or (F.iso.indexEquiv β) with hβ' | hβ' <;> rcases F.exp_or γ' with hγ'len | hγ'len
  · exact (h ⟨F.iso.indexEquiv γ', by simpa [hα', hβ', hγ'len] using hw⟩).elim
  · exact ⟨hα', hβ', hγ'len⟩
  · exact (h (root_add_mem_of_two_smul_mem F (by rwa [add_comm]) (γ := F.iso.indexEquiv γ')
      (by simpa [hα', hβ', hγ'len] using hw))).elim
  · rw [hα', hβ'] at hs; rw [hα', hβ', hγ'len] at hlen; omega
  · exact (h (add_comm ((Φ).root α) _ ▸ root_add_mem_of_two_smul_mem F h0 (γ := F.iso.indexEquiv γ')
      (by simp only [hα', hβ', hγ'len, one_smul] at hw; rw [hw]; module))).elim
  · rw [hα', hβ', hγ'len] at hlen; omega
  · rw [hα', hβ', hγ'len] at hlen; omega
  · exact (h ⟨F.iso.indexEquiv γ', smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0)
      (by simp only [hα', hβ', hγ'len] at hw; dsimp; rw [hw]; module)⟩).elim

private theorem commute_doublyLaced (D : ChevalleyDatum t ht) (F : DoublyLacedIso t ht)
    {α β : Fin t.numRoots} (h : (Φ).root α + (Φ).root β ∉ Set.range (Φ).root)
    (h0 : (Φ).root α + (Φ).root β ≠ 0) (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    Commute (partnerPt D F A α u) (partnerPt D F A β v) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  set α' := F.iso.indexEquiv α; set β' := F.iso.indexEquiv β
  have h0' : (Φ).root α' + (Φ).root β' ≠ 0 := (F.iso.root_indexEquiv_add_eq_zero_iff α β).not.mpr h0
  dsimp only [partnerPt]
  by_cases hrange : (Φ).root α' + (Φ).root β' ∈ Set.range (Φ).root
  · obtain ⟨γ', hγ'⟩ := hrange
    obtain ⟨hα', hβ', hγ'len⟩ := partner_exponents_of_notMem F h h0 hγ'
    have hbot := (Φ).chainBotCoeff_eq_one_of_short_add_short_eq_long F.iso.exponent F.sym α' β' γ'
      hα' hβ' hγ'len (hγ'.trans (add_comm _ _))
    have h2β : (Φ).root α' + 2 • (Φ).root β' ∉ Set.range (Φ).root := by
      rw [add_comm]
      exact not_two_nsmul_add_mem_of_exp_eq F (hβ'.trans hα'.symm) (by rwa [add_comm])
    rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm,
      D.commutatorElement_rootSubgroup_of_root_eq_add hγ'
        (not_two_nsmul_add_mem_of_exp_eq F (hα'.trans hβ'.symm) h0') h2β,
      cast_sc_eq_zero ⟨γ', hγ'⟩ hbot A, zero_mul, ofAdd_zero, map_one]
  · exact D.commute_rootSubgroup hrange h0' A _ _

private theorem commutatorElement_doublyLaced_of_eq_len (D : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) {α β γ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hαβ : F.iso.exponent α = F.iso.exponent β) (hβγ : F.iso.exponent β = F.iso.exponent γ)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D F A α u, partnerPt D F A β v⁆ = partnerPt D F A γ ((N α β : A) * (u * v)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  set α' := F.iso.indexEquiv α; set β' := F.iso.indexEquiv β; set γ' := F.iso.indexEquiv γ
  have hγ' : (Φ).root γ' = (Φ).root α' + (Φ).root β' :=
    smul_right_injective _ (F.iso.exponent_pos γ).ne' <| by
      have hw := congrArg F.iso.weightMap hγ
      simp only [map_add, F.iso.root_weightMap, Int.cast_id, hαβ, hβγ, ← smul_add] at hw; exact hw
  have hpe {x y} (hxy : F.iso.exponent x = F.iso.exponent y) :
      F.iso.exponent (F.iso.indexEquiv x) = F.iso.exponent (F.iso.indexEquiv y) := by
    have hx := exp_partner_mul F x; have hy := exp_partner_mul F y
    rcases F.exp_or x with h | h <;> rw [h] at hxy hx <;> rw [← hxy] at hy <;> omega
  have hα'β' := hpe hαβ; have hβ'γ' := hpe hβγ; have h0' := hγ' ▸ (Φ).ne_zero γ'
  have hbnd (δ : Fin t.numRoots) : F.iso.exponent δ ≤ 2 := by rcases F.exp_or δ with _ | _ <;> omega
  have hbot := (Φ).chainBotCoeff_eq_zero_of_add_of_length_eq F.iso.exponent F.sym α β γ
    (F.iso.exponent_pos α) (fun δ _ => hbnd δ) hβγ (hγ.trans (add_comm _ _))
  have hbot' := (Φ).chainBotCoeff_eq_zero_of_add_of_length_eq F.iso.exponent F.sym α' β' γ'
    (F.iso.exponent_pos α') (fun δ _ => hbnd δ) hβ'γ' (hγ'.trans (add_comm _ _))
  have h2β : (Φ).root α' + 2 • (Φ).root β' ∉ Set.range (Φ).root := by
    rw [add_comm]; exact not_two_nsmul_add_mem_of_exp_eq F hα'β'.symm (by rwa [add_comm])
  dsimp only [partnerPt]; rw [D.commutatorElement_rootSubgroup_of_root_eq_add hγ'
      (not_two_nsmul_add_mem_of_exp_eq F hα'β' h0') h2β,
    cast_sc_eq_one ⟨γ, hγ⟩ hbot A, cast_sc_eq_one ⟨γ', hγ'⟩ hbot' A, one_mul, one_mul,
    ← hβ'γ', ← hα'β', mul_pow]

private theorem commutatorElement_doublyLaced_of_short_short_long (D : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) {α β γ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hαlen : F.iso.exponent α = 1) (hβlen : F.iso.exponent β = 1) (hγlen : F.iso.exponent γ = 2)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D F A α u, partnerPt D F A β v⁆ = partnerPt D F A γ ((N α β : A) * (u * v)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have hbot := (Φ).chainBotCoeff_eq_one_of_short_add_short_eq_long F.iso.exponent F.sym α β γ
    hαlen hβlen hγlen (hγ.trans (add_comm _ _))
  have hp0 := (Φ).pairing_eq_zero_of_short_add_short_eq_long F.iso.exponent F.sym α β γ
    hαlen hβlen hγlen (hγ.trans (add_comm _ _))
  have hp0' : (Φ).pairing (F.iso.indexEquiv β) (F.iso.indexEquiv α) = 0 := by
    simpa [hαlen, hβlen, hp0] using F.iso.exponent_mul_pairing β α
  have hrange' : (Φ).root (F.iso.indexEquiv α) + (Φ).root (F.iso.indexEquiv β) ∉
      Set.range (Φ).root := fun ⟨ρ, hρ⟩ => by
    have hρlen := lenAdd F (F.iso.indexEquiv α) (F.iso.indexEquiv β) ρ 1 (by rw [hρ]; module)
    rcases F.exp_or ρ with h1 | h1 <;>
      rw [exp_partner_eq_two F hαlen, exp_partner_eq_two F hβlen, hp0', h1] at hρlen <;> omega
  have h0' := (F.iso.root_indexEquiv_add_eq_zero_iff α β).not.mpr (hγ ▸ (Φ).ne_zero γ)
  dsimp only [partnerPt]
  rw [commutatorElement_eq_one_iff_mul_comm.mpr ((D.commute_rootSubgroup hrange' h0' A _ _).eq),
    cast_sc_eq_zero ⟨γ, hγ⟩ hbot A, zero_mul, exp_partner_eq_one F hγlen, Int.toNat_one, pow_one,
    ofAdd_zero, map_one]

private theorem commutatorElement_doublyLaced_of_root_eq_add (D : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) {α β γ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hα : 2 • (Φ).root α + (Φ).root β ∉ Set.range (Φ).root)
    (hβ : (Φ).root α + 2 • (Φ).root β ∉ Set.range (Φ).root)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D F A α u, partnerPt D F A β v⁆ = partnerPt D F A γ ((N α β : A) * (u * v)) := by
  have no_mix {x y} (hx : F.iso.exponent x = 1) (hy : F.iso.exponent y = 2)
      (hxy : (Φ).root γ = (Φ).root x + (Φ).root y)
      (hnot : 2 • (Φ).root x + (Φ).root y ∉ Set.range (Φ).root) : False := by
    have hlen := lenAdd F x y γ 1 (by rw [hxy]; module)
    have hs := F.sym x y; rw [hx, hy] at hlen hs
    have hp : (Φ).pairing y x = -2 := by rcases F.exp_or γ with _ | _ <;> omega
    have hr := (Φ).root_reflectionPerm x y; rw [(Φ).reflection_apply_root, hp] at hr
    exact hnot ⟨(Φ).reflectionPerm x y, by rw [hr]; module⟩
  rcases F.exp_or α with hαlen | hαlen <;> rcases F.exp_or β with hβlen | hβlen
  · rcases F.exp_or γ with hγlen | hγlen
    · exact commutatorElement_doublyLaced_of_eq_len D F hγ (by omega) (by omega) A u v
    · exact commutatorElement_doublyLaced_of_short_short_long D F hγ hαlen hβlen hγlen A u v
  · exact (no_mix hαlen hβlen hγ hα).elim
  · exact (no_mix hβlen hαlen (hγ.trans (add_comm _ _)) (by rwa [add_comm])).elim
  · have hlen := lenAdd F α β γ 1 (by rw [hγ]; module); rw [hαlen, hβlen] at hlen
    have hγlen : F.iso.exponent γ = 2 := by rcases F.exp_or γ with _ | _ <;> omega
    exact commutatorElement_doublyLaced_of_eq_len D F hγ (by omega) (by omega) A u v

private theorem short_long_of_two_nsmul_add (F : DoublyLacedIso t ht) {α β γ δ : Fin t.numRoots}
    (hγ : (Φ).root γ = (Φ).root α + (Φ).root β) (hδ : (Φ).root δ = 2 • (Φ).root α + (Φ).root β) :
    F.iso.exponent α = 1 ∧ F.iso.exponent β = 2 := by
  have h0 : (Φ).root α + (Φ).root β ≠ 0 := hγ ▸ (Φ).ne_zero γ
  rcases F.exp_or α with hα | hα <;> rcases F.exp_or β with hβ | hβ
  · exact (not_two_nsmul_add_mem_of_exp_eq F (hα.trans hβ.symm) h0 ⟨δ, hδ⟩).elim
  · exact ⟨hα, hβ⟩
  · exact (not_two_nsmul_long_add_short_mem_range F hα hβ ⟨δ, hδ⟩).elim
  · exact (not_two_nsmul_add_mem_of_exp_eq F (hα.trans hβ.symm) h0 ⟨δ, hδ⟩).elim

private theorem commute_short_add_long_factors (D : ChevalleyDatum t ht) (F : DoublyLacedIso t ht)
    {β' δ' γ' : Fin t.numRoots} (hβ' : F.iso.exponent β' = 1) (hδ' : F.iso.exponent δ' = 1)
    (hγ' : F.iso.exponent γ' = 2) (hsub : (Φ).root γ' = (Φ).root δ' + (Φ).root β')
    (A : Type v) [CommRing A] (x y : Multiplicative A) :
    Commute (D.rootSubgroupPoints δ' A x) (D.rootSubgroupPoints γ' A y) := by
  refine D.commute_rootSubgroup ?_ ?_ A x y
  · rintro ⟨ρ, hρ⟩
    have hp0 := (Φ).pairing_eq_zero_of_short_add_short_eq_long F.iso.exponent F.sym β' δ' γ'
      hβ' hδ' hγ' hsub
    have hs := F.sym β' δ'; rw [hβ', hδ', hp0] at hs
    have hpadd := (Φ).pairing_eq_add_of_root_eq_add (l := δ') hsub; rw [(Φ).pairing_same] at hpadd
    have hρlen := lenAdd F δ' γ' ρ 1 (by rw [hρ]; module)
    rcases F.exp_or ρ with h1 | h1 <;> rw [hδ', hγ', h1] at hρlen <;> omega
  · intro hz
    have hlen := lenAdd F δ' δ' γ' (-2) (by rw [eq_neg_of_add_eq_zero_right hz]; module)
    rw [hγ', hδ', (Φ).pairing_same] at hlen; omega

private theorem commutatorElement_doublyLaced_of_two_nsmul_add (D : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) {α β γ δ : Fin t.numRoots}
    (hγ : (Φ).root γ = (Φ).root α + (Φ).root β) (hδ : (Φ).root δ = 2 • (Φ).root α + (Φ).root β)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D F A α u, partnerPt D F A β v⁆ = partnerPt D F A γ ((N α β : A) * (u * v)) *
      partnerPt D F A δ (((N α β * N α γ / 2 : ℤ) : A) * (u ^ 2 * v)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have hδ'z : (Φ).root δ = (Φ).root β + (2 : ℤ) • (Φ).root α := by rw [hδ]; module
  obtain ⟨hα1, hβ2⟩ := short_long_of_two_nsmul_add F hγ hδ
  obtain ⟨_, _, hδ2⟩ := (Φ).pairings_of_long_add_two_short F.iso.exponent F.sym α β δ hα1 hβ2
    (F.exp_or δ) hδ'z
  obtain ⟨γ₀, hγ₀, hγ1, hbot₁, _, hbot₂, _⟩ := (Φ).exists_short_midpoint_of_long_add_two_short
    F.iso.exponent F.sym α β δ hα1 hβ2 (F.exp_or δ) hδ'z
  rw [(Φ).root.injective (hγ₀.trans (hγ.trans (add_comm _ _)).symm)] at hγ1 hbot₂
  have hα' := exp_partner_eq_two F hα1; have hβ' := exp_partner_eq_one F hβ2
  have hγ' := exp_partner_eq_two F hγ1; have hδ' := exp_partner_eq_one F hδ2
  set α' := F.iso.indexEquiv α; set β' := F.iso.indexEquiv β
  set γ' := F.iso.indexEquiv γ; set δ' := F.iso.indexEquiv δ
  have hδ'eq : (Φ).root δ' = (Φ).root α' + (Φ).root β' :=
    smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0) <| by
      have hw := congrArg F.iso.weightMap hδ
      simp only [map_add, map_nsmul, F.iso.root_weightMap, Int.cast_id, hδ2, hα1, hβ2] at hw
      dsimp; rw [hw]; module
  have hγ'eq : (Φ).root γ' = (Φ).root α' + 2 • (Φ).root β' := by
    have hw := congrArg F.iso.weightMap hγ
    simp only [map_add, F.iso.root_weightMap, Int.cast_id, hγ1, hα1, hβ2, one_smul] at hw
    rw [hw]; module
  have hγ'z : (Φ).root γ' = (Φ).root α' + (2 : ℤ) • (Φ).root β' := by rw [hγ'eq]; module
  obtain ⟨hpα'β', _, _⟩ := (Φ).pairings_of_long_add_two_short F.iso.exponent F.sym β' α' γ'
    hβ' hα' (F.exp_or γ') hγ'z
  obtain ⟨δ₀, hδ₀, _, hbot'₁, _, hbot'₂, _⟩ := (Φ).exists_short_midpoint_of_long_add_two_short
    F.iso.exponent F.sym β' α' γ' hβ' hα' (F.exp_or γ') hγ'z
  rw [(Φ).root.injective (hδ₀.trans hδ'eq.symm)] at hbot'₂
  have h3β' : (Φ).root α' + 3 • (Φ).root β' ∉ Set.range (Φ).root := fun ⟨ρ, hρ⟩ => by
    have hρlen := lenAdd F β' α' ρ 3 (by rw [hρ]; module)
    rcases F.exp_or ρ with h1 | h1 <;> rw [hα', hβ', hpα'β', h1] at hρlen <;> omega
  have hc2' : ((-(N β' α' * N β' δ' / 2) : ℤ) : A) = 1 := by
    rw [Int.cast_neg, cast_div_two_eq_one ⟨δ', hδ'eq.trans (add_comm _ _)⟩
      ⟨γ', by rw [hγ'eq, hδ'eq]; module⟩ hbot'₁ hbot'₂ A, CharTwo.neg_one_eq_one]
  dsimp only [partnerPt]; rw [hα', hβ', hγ', hδ']; dsimp
  rw [D.commutatorElement_rootSubgroup_of_root_eq_add_two_nsmul hδ'eq hγ'eq
      (not_two_nsmul_long_add_short_mem_range F hα' hβ') h3β',
    cast_sc_eq_one ⟨γ, hγ⟩ hbot₁ A,
    cast_div_two_eq_one ⟨γ, hγ⟩ ⟨δ, by rw [hδ, hγ]; module⟩ hbot₁ hbot₂ A,
    cast_sc_eq_one ⟨δ', hδ'eq⟩ ((Φ).chainBotCoeff_eq_zero_comm.mp hbot'₁) A, hc2']
  simp only [one_mul, pow_one, mul_pow]
  exact (commute_short_add_long_factors D F hβ' hδ' hγ' (by rw [hγ'eq, hδ'eq]; module) A _ _).eq

private theorem commute_long_with_add_two_nsmul (D : ChevalleyDatum t ht) (F : DoublyLacedIso t ht)
    {α β γ δ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hδ : (Φ).root δ = (Φ).root α + 2 • (Φ).root β) (A : Type v) [CommRing A] [CharP A 2]
    (s w₁ w₂ : A) :
    Commute (partnerPt D F A α s) (partnerPt D F A γ w₁ * partnerPt D F A δ w₂) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨hβ1, hα2⟩ := short_long_of_two_nsmul_add F (hγ.trans (add_comm _ _))
    (hδ.trans (add_comm _ _))
  have h2α := not_two_nsmul_long_add_short_mem_range F hα2 hβ1
  have hind := LinearIndependent.pair_iff.mp
    ((Φ).linearIndependent_of_add_mem_range_root' (i := α) (j := β) ⟨γ, hγ⟩)
  refine Commute.mul_right ?_ ?_
  · have hsum : (Φ).root α + (Φ).root γ = 2 • (Φ).root α + (Φ).root β := by rw [hγ]; module
    refine commute_doublyLaced D F (by rwa [hsum]) (fun hz => ?_) A s w₁
    have := (hind 2 1 (by rw [hsum] at hz; linear_combination hz)).left; norm_num at this
  · have hsum : (Φ).root α + (Φ).root δ = 2 • (Φ).root γ := by rw [hδ, hγ]; module
    refine commute_doublyLaced D F (by rw [hsum]; exact (Φ).nsmul_notMem_range_root) (fun hz => ?_)
      A s w₂
    have := (hind 2 2 (by rw [hsum, hγ] at hz; linear_combination hz)).left; norm_num at this

private theorem commutatorElement_doublyLaced_of_add_two_nsmul (D : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) {α β γ δ : Fin t.numRoots}
    (hγ : (Φ).root γ = (Φ).root α + (Φ).root β) (hδ : (Φ).root δ = (Φ).root α + 2 • (Φ).root β)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D F A α u, partnerPt D F A β v⁆ = partnerPt D F A γ ((N α β : A) * (u * v)) *
      partnerPt D F A δ (((-(N β α * N β γ / 2) : ℤ) : A) * (u * v ^ 2)) := by
  have hinv : partnerPt D F A α (-u) = (partnerPt D F A α u)⁻¹ := by
    dsimp only [partnerPt]; rw [← map_inv, ← ofAdd_neg, CharTwo.neg_eq, CharTwo.neg_eq]
  have hconj : ⁅partnerPt D F A α u, partnerPt D F A β v⁆ =
      partnerPt D F A α u * ⁅partnerPt D F A β v, partnerPt D F A α (-u)⁆ *
        (partnerPt D F A α u)⁻¹ := by rw [hinv]; group
  rw [hconj, commutatorElement_doublyLaced_of_two_nsmul_add D F
      (hγ.trans (add_comm _ _)) (hδ.trans (add_comm _ _)) A v (-u),
    (commute_long_with_add_two_nsmul D F hγ hδ A u _ _).eq, mul_inv_cancel_right,
    (by rw [structureConstant_skew (ht := ht) α β, Int.cast_neg]; ring :
      (N β α : A) * (v * -u) = (N α β : A) * (u * v)),
    (by push_cast; ring : ((N β α * N β γ / 2 : ℤ) : A) * (v ^ 2 * -u) =
      ((-(N β α * N β γ / 2) : ℤ) : A) * (u * v ^ 2))]

private theorem map_rootSubgroupPoints_doublyLaced (D E : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) (A : Type v) [CommRing A] [CharP A 2]
    {xE : Fin t.numRoots → Multiplicative A →* E.points A}
    (hxE : ∀ α u, xE α (ofAdd u) = partnerPt E F A α u) (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (t.simpleIndex ht i) A u) = xE (t.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((Φ).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) A u) =
      xE ((Φ).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) u)
    (α : Fin t.numRoots) (u : Multiplicative A) : φ (D.rootSubgroupPoints α A u) = xE α u := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have hweyl (i : Fin t.rank) : φ (D.weylElement (t.simpleIndex ht i) A 1) =
      E.weylElement (t.simpleIndex ht (F.σ i)) A 1 := by
    rw [D.weylElement_def, map_mul, map_mul, Units.val_one, inv_one, Units.val_one, hpos, hneg,
      hxE, hxE]; dsimp only [partnerPt]
    rw [F.iso.indexEquiv_reflectionPerm, F.iso.exponent_reflectionPerm, F.idx_simple,
      E.weylElement_def, Units.val_one, inv_one, Units.val_one, CharTwo.neg_one_eq_one, one_pow]
  rw [← ofAdd_toAdd u, hxE, ofAdd_toAdd]
  refine (t.rationalBase ht).induction_simple_reflect α
    (p := fun γ => ∀ w : A, φ (D.rootSubgroupPoints γ A (ofAdd w)) = partnerPt E F A γ w)
    (fun γ hγ w => ?_) (fun γ j ih hj w => ?_) (toAdd u)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hγ; exact (hpos i _).trans (hxE _ w)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    rw [reflectionPerm_rationalRootSystem]
    have hconjD := D.weylElement_conj_rootSubgroupPoints i γ A w
    have hconjE := E.weylElement_conj_rootSubgroupPoints (F.σ i) (F.iso.indexEquiv γ) A
      (w ^ (F.iso.exponent (F.iso.indexEquiv γ)).toNat)
    rw [TauCeti.intCast_units_eq_one_of_charTwo, one_mul] at hconjD hconjE
    rw [← hconjD, map_mul, map_mul, map_inv, hweyl, ih]; dsimp only [partnerPt]
    rw [hconjE, ← F.idx_simple, F.iso.indexEquiv_reflectionPerm, F.iso.exponent_reflectionPerm]

private theorem comp_self_eq_frobenius_doublyLaced (D : ChevalleyDatum t ht)
    (F : DoublyLacedIso t ht) (A : Type v) [CommRing A] [ExpChar A 2]
    {xD : Fin t.numRoots → Multiplicative A →* D.points A}
    (hxD : ∀ α u, xD α (ofAdd u) = partnerPt D F A α u) (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (t.simpleIndex ht i) A u) = xD (t.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((Φ).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) A u) =
      xD ((Φ).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) : φ (φ g) = D.frobenius 2 1 A g := by
  have hall (α u) : φ (D.rootSubgroupPoints α A u) = partnerPt D F A α (toAdd u) :=
    (map_rootSubgroupPoints_doublyLaced D D F A hxD φ hpos hneg α u).trans
      (by rw [← ofAdd_toAdd u, hxD, toAdd_ofAdd])
  refine (D.elementarySubgroup_le_iff A ((φ.comp φ).eqLocus (D.frobenius 2 1 A))).mpr
    (fun α u => ?_) hg
  -- Membership in `MonoidHom.eqLocus` unfolds to pointwise equality of the two homomorphisms.
  change φ (φ (D.rootSubgroupPoints α A u)) = D.frobenius 2 1 A (D.rootSubgroupPoints α A u)
  rw [← ofAdd_toAdd u, hall, hall, toAdd_ofAdd, D.frobenius_rootSubgroupPoints, pow_one]
  dsimp only [partnerPt]; rw [F.iso.indexEquiv_apply_apply Φ F.mul_self]
  rcases F.exp_or α with h | h <;> simp [h, exp_partner_eq_two F, exp_partner_eq_one F]

end WithDatum

end DoublyLacedAux

/-! ## Type `B₂` in characteristic two -/

section B2

variable {ht : (B 2).Valid} (D E : ChevalleyDatum (B 2) ht) (A : Type v) [CommRing A] [ExpChar A 2]
local notation "ΦB2" => DynkinType.simplyConnectedRootDatum (B 2) ht
local notation "NB2" => DynkinType.structureConstant (B 2) ht
local notation "xB2" => D.b2SpecialIsogenyRootSubgroup A
local notation "xEB2" => E.b2SpecialIsogenyRootSubgroup A
local notation "eqB2" => simplyConnectedRootDatum_B 2
private noncomputable def b2DL (ht : (B 2).Valid) : DoublyLacedIso (B 2) ht where
  iso := b2SpecialIsogeny.ofEq (eqB2 ht); σ := lengthPermRankTwo
  mul_self := ofEq_mul_self _ (eqB2 ht) b2SpecialIsogeny_mul_self
  exp_or α := ofEq_exponent (eqB2 ht) b2SpecialIsogeny α ▸
    b2SpecialIsogeny_exponent_eq_one_or_eq_two α
  idx_simple i := (congrArg (· ((B 2).simpleIndex ht i))
    (ofEq_indexEquiv (eqB2 ht) b2SpecialIsogeny)).trans
      (b2SpecialIsogeny_indexEquiv_simpleIndex ht i)
  sym α β := by
    rw [ofEq_exponent (eqB2 ht) b2SpecialIsogeny, ofEq_exponent (eqB2 ht) b2SpecialIsogeny, scD,
      eqB2 ht]
    -- Expose concrete `B₂` index and lattice types on `pairing` before unfolding.
    change Fin (2 * 2 ^ 2) at α β
    change b2SpecialIsogeny.exponent α * (typeBSimplyConnectedRootDatum 2).pairing β α =
      b2SpecialIsogeny.exponent β * (typeBSimplyConnectedRootDatum 2).pairing α β
    simp only [b2SpecialIsogeny_exponent, ← RootPairing.root_coroot_eq_pairing,
      toLinearMap_typeBSimplyConnectedRootDatum]
    obtain ⟨a, rfl⟩ := b2Index_bijective.surjective α
    obtain ⟨b, rfl⟩ := b2Index_bijective.surjective β
    rw [b2SpecialIsogenyExponent_b2Index, b2SpecialIsogenyExponent_b2Index, root_b2Index,
      root_b2Index, coroot_b2Index, coroot_b2Index]; revert a b; decide
private theorem b2_pt (α : Fin (B 2).numRoots) (u : A) :
    xB2 α (ofAdd u) = partnerPt D (b2DL ht) A α u := by
  have hi : (b2DL ht).iso.indexEquiv α = b2SpecialIsogeny.indexEquiv α :=
    congrArg (· α) (ofEq_indexEquiv (eqB2 ht) b2SpecialIsogeny)
  have he (β) : (b2DL ht).iso.exponent β = b2SpecialIsogeny.exponent β :=
    ofEq_exponent (eqB2 ht) b2SpecialIsogeny β
  dsimp only [partnerPt]; rw [D.b2SpecialIsogenyRootSubgroup_ofAdd, he, hi]

/-- **Commuting root subgroups under the `B₂` exceptional isogeny.** -/
theorem commute_b2SpecialIsogenyRootSubgroup {α β : Fin (B 2).numRoots}
    (h : (ΦB2).root α + (ΦB2).root β ∉ Set.range (ΦB2).root) (h0 : (ΦB2).root α + (ΦB2).root β ≠ 0)
    (u v : A) : Commute (xB2 α (ofAdd u)) (xB2 β (ofAdd v)) := by
  simpa only [b2_pt] using commute_doublyLaced D (b2DL ht) h h0 A u v

/-- **One-factor Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_add {α β γ : Fin (B 2).numRoots}
    (hγ : (ΦB2).root γ = (ΦB2).root α + (ΦB2).root β)
    (hα : 2 • (ΦB2).root α + (ΦB2).root β ∉ Set.range (ΦB2).root)
    (hβ : (ΦB2).root α + 2 • (ΦB2).root β ∉ Set.range (ΦB2).root) (u v : A) :
    ⁅xB2 α (ofAdd u), xB2 β (ofAdd v)⁆ = xB2 γ (ofAdd ((NB2 α β : A) * (u * v))) := by
  simpa only [b2_pt] using commutatorElement_doublyLaced_of_root_eq_add D (b2DL ht) hγ hα hβ A u v

/-- **Two-factor short-first Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_two_nsmul_add
    {α β γ δ : Fin (B 2).numRoots} (hγ : (ΦB2).root γ = (ΦB2).root α + (ΦB2).root β)
    (hδ : (ΦB2).root δ = 2 • (ΦB2).root α + (ΦB2).root β) (u v : A) :
    ⁅xB2 α (ofAdd u), xB2 β (ofAdd v)⁆ = xB2 γ (ofAdd ((NB2 α β : A) * (u * v))) *
      xB2 δ (ofAdd (((NB2 α β * NB2 α γ / 2 : ℤ) : A) * (u ^ 2 * v))) := by
  simpa only [b2_pt] using commutatorElement_doublyLaced_of_two_nsmul_add D (b2DL ht) hγ hδ A u v

/-- **Two-factor long-first Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_add_two_nsmul
    {α β γ δ : Fin (B 2).numRoots} (hγ : (ΦB2).root γ = (ΦB2).root α + (ΦB2).root β)
    (hδ : (ΦB2).root δ = (ΦB2).root α + 2 • (ΦB2).root β) (u v : A) :
    ⁅xB2 α (ofAdd u), xB2 β (ofAdd v)⁆ = xB2 γ (ofAdd ((NB2 α β : A) * (u * v))) *
      xB2 δ (ofAdd (((-(NB2 β α * NB2 β γ / 2) : ℤ) : A) * (u * v ^ 2))) := by
  simpa only [b2_pt] using commutatorElement_doublyLaced_of_add_two_nsmul D (b2DL ht) hγ hδ A u v

/-- A group homomorphism `φ : D.points A →* E.points A` agreeing with
`E.b2SpecialIsogenyRootSubgroup A` on the positive and negative simple root subgroups agrees with
it on every root subgroup. -/
theorem map_rootSubgroupPoints_of_b2SpecialIsogeny_simple (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints ((B 2).simpleIndex ht i) A u) =
      xEB2 ((B 2).simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) A u) =
      xEB2 ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) u)
    (α : Fin (B 2).numRoots) (u : Multiplicative A) : φ (D.rootSubgroupPoints α A u) = xEB2 α u :=
  map_rootSubgroupPoints_doublyLaced D E (b2DL ht) A (b2_pt E A) φ hpos hneg α u

/-- An endomorphism `φ : D.points A →* D.points A` agreeing with `b2SpecialIsogenyRootSubgroup` on
the positive and negative simple root subgroups squares to `D.frobenius 2 1 A` on
`D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_b2SpecialIsogeny_simple (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints ((B 2).simpleIndex ht i) A u) =
      xB2 ((B 2).simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) A u) =
      xB2 ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) : φ (φ g) = D.frobenius 2 1 A g :=
  comp_self_eq_frobenius_doublyLaced D (b2DL ht) A (b2_pt D A) φ hpos hneg hg

end B2

/-! ## Type `F₄` in characteristic two -/

section F4
variable {ht : F4.Valid} (D E : ChevalleyDatum F4 ht) (A : Type v) [CommRing A] [ExpChar A 2]
local notation "ΦF4" => F4.simplyConnectedRootDatum ht
local notation "NF4" => F4.structureConstant ht
local notation "xF4" => D.f4SpecialIsogenyRootSubgroup A
local notation "xEF4" => E.f4SpecialIsogenyRootSubgroup A
local notation "eqF4" => simplyConnectedRootDatum_F4
private noncomputable def f4DL (ht : F4.Valid) : DoublyLacedIso F4 ht where
  iso := f4SpecialIsogeny.ofEq (eqF4 ht); σ := lengthPermF4
  mul_self := ofEq_mul_self _ (eqF4 ht) f4SpecialIsogeny_mul_self
  exp_or α := ofEq_exponent (eqF4 ht) f4SpecialIsogeny α ▸
    f4SpecialIsogeny_exponent_eq_one_or_eq_two α
  idx_simple i := (congrArg (· (F4.simpleIndex ht i))
    (ofEq_indexEquiv (eqF4 ht) f4SpecialIsogeny)).trans
      (f4SpecialIsogeny_indexEquiv_simpleIndex ht i)
  sym α β := by
    rw [ofEq_exponent (eqF4 ht) f4SpecialIsogeny, ofEq_exponent (eqF4 ht) f4SpecialIsogeny, scD,
      eqF4 ht]
    -- Expose `Fin 48` on `α, β` after transporting along `simplyConnectedRootDatum_F4`.
    change Fin 48 at α β
    rw [f4SpecialIsogeny_exponent, f4SpecialIsogeny_exponent]; exact f4Length_mul_pairing_comm α β
private theorem f4_pt (α : Fin F4.numRoots) (u : A) :
    xF4 α (ofAdd u) = partnerPt D (f4DL ht) A α u := by
  have hi : (f4DL ht).iso.indexEquiv α = f4SpecialIsogeny.indexEquiv α :=
    congrArg (· α) (ofEq_indexEquiv (eqF4 ht) f4SpecialIsogeny)
  have he (β) : (f4DL ht).iso.exponent β = f4SpecialIsogeny.exponent β :=
    ofEq_exponent (eqF4 ht) f4SpecialIsogeny β
  dsimp only [partnerPt]; rw [D.f4SpecialIsogenyRootSubgroup_ofAdd, he, hi]

/-- **Commuting root subgroups under the `F₄` exceptional isogeny.** -/
theorem commute_f4SpecialIsogenyRootSubgroup {α β : Fin F4.numRoots}
    (h : (ΦF4).root α + (ΦF4).root β ∉ Set.range (ΦF4).root) (h0 : (ΦF4).root α + (ΦF4).root β ≠ 0)
    (u v : A) : Commute (xF4 α (ofAdd u)) (xF4 β (ofAdd v)) := by
  simpa only [f4_pt] using commute_doublyLaced D (f4DL ht) h h0 A u v

/-- **One-factor Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_add {α β γ : Fin F4.numRoots}
    (hγ : (ΦF4).root γ = (ΦF4).root α + (ΦF4).root β)
    (hα : 2 • (ΦF4).root α + (ΦF4).root β ∉ Set.range (ΦF4).root)
    (hβ : (ΦF4).root α + 2 • (ΦF4).root β ∉ Set.range (ΦF4).root) (u v : A) :
    ⁅xF4 α (ofAdd u), xF4 β (ofAdd v)⁆ = xF4 γ (ofAdd ((NF4 α β : A) * (u * v))) := by
  simpa only [f4_pt] using commutatorElement_doublyLaced_of_root_eq_add D (f4DL ht) hγ hα hβ A u v

/-- **Two-factor short-first Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_two_nsmul_add
    {α β γ δ : Fin F4.numRoots} (hγ : (ΦF4).root γ = (ΦF4).root α + (ΦF4).root β)
    (hδ : (ΦF4).root δ = 2 • (ΦF4).root α + (ΦF4).root β) (u v : A) :
    ⁅xF4 α (ofAdd u), xF4 β (ofAdd v)⁆ = xF4 γ (ofAdd ((NF4 α β : A) * (u * v))) *
      xF4 δ (ofAdd (((NF4 α β * NF4 α γ / 2 : ℤ) : A) * (u ^ 2 * v))) := by
  simpa only [f4_pt] using commutatorElement_doublyLaced_of_two_nsmul_add D (f4DL ht) hγ hδ A u v

/-- **Two-factor long-first Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_add_two_nsmul
    {α β γ δ : Fin F4.numRoots} (hγ : (ΦF4).root γ = (ΦF4).root α + (ΦF4).root β)
    (hδ : (ΦF4).root δ = (ΦF4).root α + 2 • (ΦF4).root β) (u v : A) :
    ⁅xF4 α (ofAdd u), xF4 β (ofAdd v)⁆ = xF4 γ (ofAdd ((NF4 α β : A) * (u * v))) *
      xF4 δ (ofAdd (((-(NF4 β α * NF4 β γ / 2) : ℤ) : A) * (u * v ^ 2))) := by
  simpa only [f4_pt] using commutatorElement_doublyLaced_of_add_two_nsmul D (f4DL ht) hγ hδ A u v

/-- A group homomorphism `φ : D.points A →* E.points A` agreeing with
`E.f4SpecialIsogenyRootSubgroup A` on the positive and negative simple root subgroups agrees with
it on every root subgroup. -/
theorem map_rootSubgroupPoints_of_f4SpecialIsogeny_simple (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (F4.simpleIndex ht i) A u) =
      xEF4 (F4.simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) A u) =
      xEF4 ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) u)
    (α : Fin F4.numRoots) (u : Multiplicative A) : φ (D.rootSubgroupPoints α A u) = xEF4 α u :=
  map_rootSubgroupPoints_doublyLaced D E (f4DL ht) A (f4_pt E A) φ hpos hneg α u

/-- An endomorphism `φ : D.points A →* D.points A` agreeing with `f4SpecialIsogenyRootSubgroup` on
the positive and negative simple root subgroups squares to `D.frobenius 2 1 A` on
`D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_f4SpecialIsogeny_simple (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (F4.simpleIndex ht i) A u) =
      xF4 (F4.simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) A u) =
      xF4 ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) : φ (φ g) = D.frobenius 2 1 A g :=
  comp_self_eq_frobenius_doublyLaced D (f4DL ht) A (f4_pt D A) φ hpos hneg hg

end F4

end TauCeti.DynkinType.ChevalleyDatum
