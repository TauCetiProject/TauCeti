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

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Lemma 53 and Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3–12.4.
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

private noncomputable abbrev partnerPt {t : DynkinType} {ht : t.Valid}
    {Φ₀ : RootDatum (Fin t.numRoots) (Fin t.rank → ℤ) (Fin t.rank → ℤ)}
    (D : ChevalleyDatum t ht) (f : RootPairingIsogeny Φ₀ Φ₀) (A : Type v) [CommRing A]
    (α : Fin t.numRoots) (u : A) : D.points A :=
  D.rootSubgroupPoints (f.indexEquiv α) A (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat))

section WithDatum

variable {t : DynkinType} {ht : t.Valid}
  {Φ₀ : RootDatum (Fin t.numRoots) (Fin t.rank → ℤ) (Fin t.rank → ℤ)}
  {f : RootPairingIsogeny Φ₀ Φ₀}
local notation "Φ" => t.simplyConnectedRootDatum ht
local notation "N" => t.structureConstant ht
local notation "scOr" => structureConstant_eq_natCast_or_eq_neg_natCast

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

private theorem exp_partner_mul (hmul : f * f = smulId Φ₀ 2) (α : Fin t.numRoots) :
    f.exponent α * f.exponent (f.indexEquiv α) = 2 := by
  simpa using f.exponent_mul_exponent_indexEquiv Φ₀ hmul α
private theorem exp_partner_eq_two (hmul : f * f = smulId Φ₀ 2) {α : Fin t.numRoots}
    (h : f.exponent α = 1) : f.exponent (f.indexEquiv α) = 2 := by
  have hm := exp_partner_mul hmul α; rw [h] at hm; omega
private theorem exp_partner_eq_one (hmul : f * f = smulId Φ₀ 2) {α : Fin t.numRoots}
    (h : f.exponent α = 2) : f.exponent (f.indexEquiv α) = 1 := by
  have hm := exp_partner_mul hmul α; rw [h] at hm; omega

private theorem partner_exponents_of_notMem (hΦ : Φ = Φ₀) (hmul : f * f = smulId Φ₀ 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β γ' : Fin t.numRoots} (h : (Φ).root α + (Φ).root β ∉ Set.range (Φ).root)
    (h0 : (Φ).root α + (Φ).root β ≠ 0)
    (hγ' : (Φ).root γ' = (Φ).root (f.indexEquiv α) + (Φ).root (f.indexEquiv β)) :
    f.exponent (f.indexEquiv α) = 1 ∧ f.exponent (f.indexEquiv β) = 1 ∧ f.exponent γ' = 2 := by
  subst hΦ
  have := t.isReduced_simplyConnectedRootDatum ht
  have hw := congrArg f.weightMap hγ'
  rw [map_add, f.root_weightMap, f.weightMap_root_indexEquiv _ hmul,
    f.weightMap_root_indexEquiv _ hmul, Int.cast_id] at hw
  have hlen := (Φ).length_of_root_eq_add_zsmul f.exponent hsym (f.indexEquiv α) (f.indexEquiv β)
    γ' 1 (by rw [hγ']; module)
  have hs := hsym (f.indexEquiv α) (f.indexEquiv β)
  rcases hexp (f.indexEquiv α) with hα' | hα' <;>
    rcases hexp (f.indexEquiv β) with hβ' | hβ' <;> rcases hexp γ' with hγ'len | hγ'len
  · exact (h ⟨f.indexEquiv γ', by simpa [hα', hβ', hγ'len] using hw⟩).elim
  · exact ⟨hα', hβ', hγ'len⟩
  · exact (h ((Φ).root_add_mem_range_root_of_root_add_nsmul_mem (n := 2) (by omega)
      (by rwa [add_comm]) ⟨f.indexEquiv γ', by
        simp only [hα', hβ', hγ'len, one_smul] at hw; rw [hw]; module⟩)).elim
  · rw [hα', hβ'] at hs; rw [hα', hβ', hγ'len] at hlen; omega
  · exact (h (add_comm ((Φ).root α) _ ▸ (Φ).root_add_mem_range_root_of_root_add_nsmul_mem (n := 2)
      (by omega) h0 ⟨f.indexEquiv γ', by
        simp only [hα', hβ', hγ'len, one_smul] at hw; rw [hw]; module⟩)).elim
  · rw [hα', hβ', hγ'len] at hlen; omega
  · rw [hα', hβ', hγ'len] at hlen; omega
  · exact (h ⟨f.indexEquiv γ', smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0)
      (by simp only [hα', hβ', hγ'len] at hw; dsimp; rw [hw]; module)⟩).elim

private theorem commute_doublyLaced (D : ChevalleyDatum t ht) (hΦ : Φ = Φ₀)
    (hmul : f * f = smulId Φ₀ 2) (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β : Fin t.numRoots} (h : (Φ).root α + (Φ).root β ∉ Set.range (Φ).root)
    (h0 : (Φ).root α + (Φ).root β ≠ 0) (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    Commute (partnerPt D f A α u) (partnerPt D f A β v) := by
  subst hΦ
  have := t.isReduced_simplyConnectedRootDatum ht
  set α' := f.indexEquiv α; set β' := f.indexEquiv β
  have h0' : (Φ).root α' + (Φ).root β' ≠ 0 := (f.root_indexEquiv_add_eq_zero_iff α β).not.mpr h0
  dsimp only [partnerPt]
  by_cases hrange : (Φ).root α' + (Φ).root β' ∈ Set.range (Φ).root
  · obtain ⟨γ', hγ'⟩ := hrange
    obtain ⟨hα', hβ', hγ'len⟩ := partner_exponents_of_notMem rfl hmul hexp hsym h h0 hγ'
    have hbot := (Φ).chainBotCoeff_eq_one_of_short_add_short_eq_long f.exponent hsym α' β' γ'
      hα' hβ' hγ'len (hγ'.trans (add_comm _ _))
    have h2β : (Φ).root α' + 2 • (Φ).root β' ∉ Set.range (Φ).root := by
      rw [add_comm]
      exact (Φ).two_nsmul_add_notMem_range_root_of_length_eq f.exponent hsym hexp
        (hβ'.trans hα'.symm) (by rwa [add_comm])
    rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm,
      D.commutatorElement_rootSubgroup_of_root_eq_add hγ'
        ((Φ).two_nsmul_add_notMem_range_root_of_length_eq f.exponent hsym hexp
          (hα'.trans hβ'.symm) h0') h2β,
      cast_sc_eq_zero ⟨γ', hγ'⟩ hbot A, zero_mul, ofAdd_zero, map_one]
  · exact D.commute_rootSubgroup hrange h0' A _ _

private theorem commutatorElement_doublyLaced_of_eq_len (D : ChevalleyDatum t ht) (hΦ : Φ = Φ₀)
    (hmul : f * f = smulId Φ₀ 2) (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β γ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hαβ : f.exponent α = f.exponent β) (hβγ : f.exponent β = f.exponent γ)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D f A α u, partnerPt D f A β v⁆ = partnerPt D f A γ ((N α β : A) * (u * v)) := by
  subst hΦ
  have := t.isReduced_simplyConnectedRootDatum ht
  set α' := f.indexEquiv α; set β' := f.indexEquiv β; set γ' := f.indexEquiv γ
  have hγ' : (Φ).root γ' = (Φ).root α' + (Φ).root β' :=
    smul_right_injective _ (f.exponent_pos γ).ne' <| by
      have hw := congrArg f.weightMap hγ
      simp only [map_add, f.root_weightMap, Int.cast_id, hαβ, hβγ, ← smul_add] at hw; exact hw
  have hpe {x y} (hxy : f.exponent x = f.exponent y) :
      f.exponent (f.indexEquiv x) = f.exponent (f.indexEquiv y) := by
    have hx := exp_partner_mul hmul x; have hy := exp_partner_mul hmul y
    rcases hexp x with h | h <;> rw [h] at hxy hx <;> rw [← hxy] at hy <;> omega
  have hα'β' := hpe hαβ; have hβ'γ' := hpe hβγ; have h0' := hγ' ▸ (Φ).ne_zero γ'
  have hbnd (δ : Fin t.numRoots) : f.exponent δ ≤ 2 := by rcases hexp δ with _ | _ <;> omega
  have hbot := (Φ).chainBotCoeff_eq_zero_of_add_of_length_eq f.exponent hsym α β γ
    (f.exponent_pos α) (fun δ _ => hbnd δ) hβγ (hγ.trans (add_comm _ _))
  have hbot' := (Φ).chainBotCoeff_eq_zero_of_add_of_length_eq f.exponent hsym α' β' γ'
    (f.exponent_pos α') (fun δ _ => hbnd δ) hβ'γ' (hγ'.trans (add_comm _ _))
  have h2β : (Φ).root α' + 2 • (Φ).root β' ∉ Set.range (Φ).root := by
    rw [add_comm]
    exact (Φ).two_nsmul_add_notMem_range_root_of_length_eq f.exponent hsym hexp hα'β'.symm
      (by rwa [add_comm])
  dsimp only [partnerPt]; rw [D.commutatorElement_rootSubgroup_of_root_eq_add hγ'
      ((Φ).two_nsmul_add_notMem_range_root_of_length_eq f.exponent hsym hexp hα'β' h0') h2β,
    cast_sc_eq_one ⟨γ, hγ⟩ hbot A, cast_sc_eq_one ⟨γ', hγ'⟩ hbot' A, one_mul, one_mul,
    ← hβ'γ', ← hα'β', mul_pow]

private theorem commutatorElement_doublyLaced_of_short_short_long (D : ChevalleyDatum t ht)
    (hΦ : Φ = Φ₀) (hmul : f * f = smulId Φ₀ 2) (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β γ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hαlen : f.exponent α = 1) (hβlen : f.exponent β = 1) (hγlen : f.exponent γ = 2)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D f A α u, partnerPt D f A β v⁆ = partnerPt D f A γ ((N α β : A) * (u * v)) := by
  subst hΦ
  have := t.isReduced_simplyConnectedRootDatum ht
  have hbot := (Φ).chainBotCoeff_eq_one_of_short_add_short_eq_long f.exponent hsym α β γ
    hαlen hβlen hγlen (hγ.trans (add_comm _ _))
  have hp0 := (Φ).pairing_eq_zero_of_short_add_short_eq_long f.exponent hsym α β γ
    hαlen hβlen hγlen (hγ.trans (add_comm _ _))
  have hp0' : (Φ).pairing (f.indexEquiv β) (f.indexEquiv α) = 0 := by
    simpa [hαlen, hβlen, hp0] using f.exponent_mul_pairing β α
  have hrange' : (Φ).root (f.indexEquiv α) + (Φ).root (f.indexEquiv β) ∉
      Set.range (Φ).root := fun ⟨ρ, hρ⟩ => by
    have hρlen := (Φ).length_of_root_eq_add_zsmul f.exponent hsym (f.indexEquiv α) (f.indexEquiv β)
      ρ 1 (by rw [hρ]; module)
    rcases hexp ρ with h1 | h1 <;>
      rw [exp_partner_eq_two hmul hαlen, exp_partner_eq_two hmul hβlen, hp0', h1] at hρlen <;> omega
  have h0' := (f.root_indexEquiv_add_eq_zero_iff α β).not.mpr (hγ ▸ (Φ).ne_zero γ)
  dsimp only [partnerPt]
  rw [commutatorElement_eq_one_iff_mul_comm.mpr ((D.commute_rootSubgroup hrange' h0' A _ _).eq),
    cast_sc_eq_zero ⟨γ, hγ⟩ hbot A, zero_mul, exp_partner_eq_one hmul hγlen, Int.toNat_one, pow_one,
    ofAdd_zero, map_one]

private theorem commutatorElement_doublyLaced_of_root_eq_add (D : ChevalleyDatum t ht)
    (hΦ : Φ = Φ₀) (hmul : f * f = smulId Φ₀ 2) (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β γ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hα : 2 • (Φ).root α + (Φ).root β ∉ Set.range (Φ).root)
    (hβ : (Φ).root α + 2 • (Φ).root β ∉ Set.range (Φ).root)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D f A α u, partnerPt D f A β v⁆ = partnerPt D f A γ ((N α β : A) * (u * v)) := by
  subst hΦ
  have no_mix {x y} (hx : f.exponent x = 1) (hy : f.exponent y = 2)
      (hxy : (Φ).root γ = (Φ).root x + (Φ).root y)
      (hnot : 2 • (Φ).root x + (Φ).root y ∉ Set.range (Φ).root) : False := by
    have hlen := (Φ).length_of_root_eq_add_zsmul f.exponent hsym x y γ 1 (by rw [hxy]; module)
    have hs := hsym x y; rw [hx, hy] at hlen hs
    have hp : (Φ).pairing y x = -2 := by rcases hexp γ with _ | _ <;> omega
    have hr := (Φ).root_reflectionPerm x y; rw [(Φ).reflection_apply_root, hp] at hr
    exact hnot ⟨(Φ).reflectionPerm x y, by rw [hr]; module⟩
  rcases hexp α with hαlen | hαlen <;> rcases hexp β with hβlen | hβlen
  · rcases hexp γ with hγlen | hγlen
    · exact commutatorElement_doublyLaced_of_eq_len D rfl hmul hexp hsym hγ (by omega) (by omega)
        A u v
    · exact commutatorElement_doublyLaced_of_short_short_long D rfl hmul hexp hsym hγ hαlen hβlen
        hγlen A u v
  · exact (no_mix hαlen hβlen hγ hα).elim
  · exact (no_mix hβlen hαlen (hγ.trans (add_comm _ _)) (by rwa [add_comm])).elim
  · have hlen := (Φ).length_of_root_eq_add_zsmul f.exponent hsym α β γ 1 (by rw [hγ]; module)
    rw [hαlen, hβlen] at hlen
    have hγlen : f.exponent γ = 2 := by rcases hexp γ with _ | _ <;> omega
    exact commutatorElement_doublyLaced_of_eq_len D rfl hmul hexp hsym hγ (by omega) (by omega)
      A u v

private theorem commute_short_add_long_factors (D : ChevalleyDatum t ht) (hΦ : Φ = Φ₀)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {β' δ' γ' : Fin t.numRoots} (hβ' : f.exponent β' = 1) (hδ' : f.exponent δ' = 1)
    (hγ' : f.exponent γ' = 2) (hsub : (Φ).root γ' = (Φ).root δ' + (Φ).root β')
    (A : Type v) [CommRing A] (x y : Multiplicative A) :
    Commute (D.rootSubgroupPoints δ' A x) (D.rootSubgroupPoints γ' A y) := by
  subst hΦ
  refine D.commute_rootSubgroup ?_ ?_ A x y
  · rintro ⟨ρ, hρ⟩
    have hp0 := (Φ).pairing_eq_zero_of_short_add_short_eq_long f.exponent hsym β' δ' γ'
      hβ' hδ' hγ' hsub
    have hs := hsym β' δ'; rw [hβ', hδ', hp0] at hs
    have hpadd := (Φ).pairing_eq_add_of_root_eq_add (l := δ') hsub; rw [(Φ).pairing_same] at hpadd
    have hρlen := (Φ).length_of_root_eq_add_zsmul f.exponent hsym δ' γ' ρ 1 (by rw [hρ]; module)
    rcases hexp ρ with h1 | h1 <;> rw [hδ', hγ', h1] at hρlen <;> omega
  · intro hz
    have hlen := (Φ).length_of_root_eq_add_zsmul f.exponent hsym δ' δ' γ' (-2)
      (by rw [eq_neg_of_add_eq_zero_right hz]; module)
    rw [hγ', hδ', (Φ).pairing_same] at hlen; omega

private theorem commutatorElement_doublyLaced_of_two_nsmul_add (D : ChevalleyDatum t ht)
    (hΦ : Φ = Φ₀) (hmul : f * f = smulId Φ₀ 2) (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β γ δ : Fin t.numRoots}
    (hγ : (Φ).root γ = (Φ).root α + (Φ).root β) (hδ : (Φ).root δ = 2 • (Φ).root α + (Φ).root β)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D f A α u, partnerPt D f A β v⁆ = partnerPt D f A γ ((N α β : A) * (u * v)) *
      partnerPt D f A δ (((N α β * N α γ / 2 : ℤ) : A) * (u ^ 2 * v)) := by
  subst hΦ
  have := t.isReduced_simplyConnectedRootDatum ht
  have hδ'z : (Φ).root δ = (Φ).root β + (2 : ℤ) • (Φ).root α := by rw [hδ]; module
  obtain ⟨hα1, hβ2⟩ := (Φ).length_eq_one_and_eq_two_of_two_nsmul_add_mem_range_root
    f.exponent hsym hexp (hγ ▸ (Φ).ne_zero γ) ⟨δ, hδ⟩
  obtain ⟨_, _, hδ2⟩ := (Φ).pairings_of_long_add_two_short f.exponent hsym α β δ hα1 hβ2
    (hexp δ) hδ'z
  obtain ⟨γ₀, hγ₀, hγ1, hbot₁, _, hbot₂, _⟩ := (Φ).exists_short_midpoint_of_long_add_two_short
    f.exponent hsym α β δ hα1 hβ2 (hexp δ) hδ'z
  rw [(Φ).root.injective (hγ₀.trans (hγ.trans (add_comm _ _)).symm)] at hγ1 hbot₂
  have hα' := exp_partner_eq_two hmul hα1; have hβ' := exp_partner_eq_one hmul hβ2
  have hγ' := exp_partner_eq_two hmul hγ1; have hδ' := exp_partner_eq_one hmul hδ2
  set α' := f.indexEquiv α; set β' := f.indexEquiv β
  set γ' := f.indexEquiv γ; set δ' := f.indexEquiv δ
  have hδ'eq : (Φ).root δ' = (Φ).root α' + (Φ).root β' :=
    smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0) <| by
      have hw := congrArg f.weightMap hδ
      simp only [map_add, map_nsmul, f.root_weightMap, Int.cast_id, hδ2, hα1, hβ2] at hw
      dsimp; rw [hw]; module
  have hγ'eq : (Φ).root γ' = (Φ).root α' + 2 • (Φ).root β' := by
    have hw := congrArg f.weightMap hγ
    simp only [map_add, f.root_weightMap, Int.cast_id, hγ1, hα1, hβ2, one_smul] at hw
    rw [hw]; module
  have hγ'z : (Φ).root γ' = (Φ).root α' + (2 : ℤ) • (Φ).root β' := by rw [hγ'eq]; module
  obtain ⟨hpα'β', _, _⟩ := (Φ).pairings_of_long_add_two_short f.exponent hsym β' α' γ'
    hβ' hα' (hexp γ') hγ'z
  obtain ⟨δ₀, hδ₀, _, hbot'₁, _, hbot'₂, _⟩ := (Φ).exists_short_midpoint_of_long_add_two_short
    f.exponent hsym β' α' γ' hβ' hα' (hexp γ') hγ'z
  rw [(Φ).root.injective (hδ₀.trans hδ'eq.symm)] at hbot'₂
  have h3β' : (Φ).root α' + 3 • (Φ).root β' ∉ Set.range (Φ).root := fun ⟨ρ, hρ⟩ => by
    have hρlen := (Φ).length_of_root_eq_add_zsmul f.exponent hsym β' α' ρ 3 (by rw [hρ]; module)
    rcases hexp ρ with h1 | h1 <;> rw [hα', hβ', hpα'β', h1] at hρlen <;> omega
  have hc2' : ((-(N β' α' * N β' δ' / 2) : ℤ) : A) = 1 := by
    rw [Int.cast_neg, cast_div_two_eq_one ⟨δ', hδ'eq.trans (add_comm _ _)⟩
      ⟨γ', by rw [hγ'eq, hδ'eq]; module⟩ hbot'₁ hbot'₂ A, CharTwo.neg_one_eq_one]
  dsimp only [partnerPt]; rw [hα', hβ', hγ', hδ']; dsimp
  rw [D.commutatorElement_rootSubgroup_of_root_eq_add_two_nsmul hδ'eq hγ'eq
      ((Φ).two_nsmul_long_add_short_notMem_range_root f.exponent hsym hexp hα' hβ') h3β',
    cast_sc_eq_one ⟨γ, hγ⟩ hbot₁ A,
    cast_div_two_eq_one ⟨γ, hγ⟩ ⟨δ, by rw [hδ, hγ]; module⟩ hbot₁ hbot₂ A,
    cast_sc_eq_one ⟨δ', hδ'eq⟩ ((Φ).chainBotCoeff_eq_zero_comm.mp hbot'₁) A, hc2']
  simp only [one_mul, pow_one, mul_pow]
  exact (commute_short_add_long_factors D rfl hexp hsym hβ' hδ' hγ'
    (by rw [hγ'eq, hδ'eq]; module) A _ _).eq

private theorem commute_long_with_add_two_nsmul (D : ChevalleyDatum t ht) (hΦ : Φ = Φ₀)
    (hmul : f * f = smulId Φ₀ 2) (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β γ δ : Fin t.numRoots} (hγ : (Φ).root γ = (Φ).root α + (Φ).root β)
    (hδ : (Φ).root δ = (Φ).root α + 2 • (Φ).root β) (A : Type v) [CommRing A] [CharP A 2]
    (s w₁ w₂ : A) :
    Commute (partnerPt D f A α s) (partnerPt D f A γ w₁ * partnerPt D f A δ w₂) := by
  subst hΦ
  have := t.isReduced_simplyConnectedRootDatum ht
  obtain ⟨hβ1, hα2⟩ := (Φ).length_eq_one_and_eq_two_of_two_nsmul_add_mem_range_root
    f.exponent hsym hexp (hγ.trans (add_comm _ _) ▸ (Φ).ne_zero γ) ⟨δ, hδ.trans (add_comm _ _)⟩
  have h2α := (Φ).two_nsmul_long_add_short_notMem_range_root f.exponent hsym hexp hα2 hβ1
  have hind := LinearIndependent.pair_iff.mp
    ((Φ).linearIndependent_of_add_mem_range_root' (i := α) (j := β) ⟨γ, hγ⟩)
  refine Commute.mul_right ?_ ?_
  · have hsum : (Φ).root α + (Φ).root γ = 2 • (Φ).root α + (Φ).root β := by rw [hγ]; module
    refine commute_doublyLaced D rfl hmul hexp hsym (by rwa [hsum]) (fun hz => ?_) A s w₁
    have := (hind 2 1 (by rw [hsum] at hz; linear_combination hz)).left; norm_num at this
  · have hsum : (Φ).root α + (Φ).root δ = 2 • (Φ).root γ := by rw [hδ, hγ]; module
    refine commute_doublyLaced D rfl hmul hexp hsym
      (by rw [hsum]; exact (Φ).nsmul_notMem_range_root) (fun hz => ?_) A s w₂
    have := (hind 2 2 (by rw [hsum, hγ] at hz; linear_combination hz)).left; norm_num at this

private theorem commutatorElement_doublyLaced_of_add_two_nsmul (D : ChevalleyDatum t ht)
    (hΦ : Φ = Φ₀) (hmul : f * f = smulId Φ₀ 2) (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * Φ₀.pairing β α = f.exponent β * Φ₀.pairing α β)
    {α β γ δ : Fin t.numRoots}
    (hγ : (Φ).root γ = (Φ).root α + (Φ).root β) (hδ : (Φ).root δ = (Φ).root α + 2 • (Φ).root β)
    (A : Type v) [CommRing A] [CharP A 2] (u v : A) :
    ⁅partnerPt D f A α u, partnerPt D f A β v⁆ = partnerPt D f A γ ((N α β : A) * (u * v)) *
      partnerPt D f A δ (((-(N β α * N β γ / 2) : ℤ) : A) * (u * v ^ 2)) := by
  have hinv : partnerPt D f A α (-u) = (partnerPt D f A α u)⁻¹ := by
    dsimp only [partnerPt]; rw [← map_inv, ← ofAdd_neg, CharTwo.neg_eq, CharTwo.neg_eq]
  have hconj : ⁅partnerPt D f A α u, partnerPt D f A β v⁆ =
      partnerPt D f A α u * ⁅partnerPt D f A β v, partnerPt D f A α (-u)⁆ *
        (partnerPt D f A α u)⁻¹ := by rw [hinv]; group
  rw [hconj, commutatorElement_doublyLaced_of_two_nsmul_add D hΦ hmul hexp hsym
      (hγ.trans (add_comm _ _)) (hδ.trans (add_comm _ _)) A v (-u),
    (commute_long_with_add_two_nsmul D hΦ hmul hexp hsym hγ hδ A u _ _).eq, mul_inv_cancel_right,
    (by rw [structureConstant_skew (ht := ht) α β, Int.cast_neg]; ring :
      (N β α : A) * (v * -u) = (N α β : A) * (u * v)),
    (by push_cast; ring : ((N β α * N β γ / 2 : ℤ) : A) * (v ^ 2 * -u) =
      ((-(N β α * N β γ / 2) : ℤ) : A) * (u * v ^ 2))]

private theorem map_rootSubgroupPoints_doublyLaced (D E : ChevalleyDatum t ht)
    (hΦ : Φ = Φ₀) (f : RootPairingIsogeny Φ₀ Φ₀) {σ : Equiv.Perm (Fin t.rank)}
    (hidx : ∀ i, f.indexEquiv (t.simpleIndex ht i) = t.simpleIndex ht (σ i))
    (A : Type v) [CommRing A] [CharP A 2]
    {xE : Fin t.numRoots → Multiplicative A →* E.points A}
    (hxE : ∀ α u, xE α (ofAdd u) = partnerPt E f A α u)
    (hxE_weyl : ∀ α (s : Aˣ),
      xE α (ofAdd (s : A)) * xE ((Φ).reflectionPerm α α) (ofAdd (-((s⁻¹ : Aˣ) : A))) *
        xE α (ofAdd (s : A)) =
      E.weylElement (f.indexEquiv α) A (s ^ (f.exponent (f.indexEquiv α)).toNat))
    (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (t.simpleIndex ht i) A u) = xE (t.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((Φ).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) A u) =
      xE ((Φ).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i)) u)
    (α : Fin t.numRoots) (u : Multiplicative A) : φ (D.rootSubgroupPoints α A u) = xE α u := by
  subst hΦ
  have := t.isReduced_simplyConnectedRootDatum ht
  have hweyl (i : Fin t.rank) : φ (D.weylElement (t.simpleIndex ht i) A 1) =
      E.weylElement (t.simpleIndex ht (σ i)) A 1 := by
    rw [D.weylElement_def, map_mul, map_mul, hpos, hneg, hxE_weyl, one_pow, hidx]
  rw [← ofAdd_toAdd u, hxE, ofAdd_toAdd]
  refine (t.rationalBase ht).induction_simple_reflect α
    (p := fun γ => ∀ w : A, φ (D.rootSubgroupPoints γ A (ofAdd w)) = partnerPt E f A γ w)
    (fun γ hγ w => ?_) (fun γ j ih hj w => ?_) (toAdd u)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hγ; exact (hpos i _).trans (hxE _ w)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    rw [reflectionPerm_rationalRootSystem]
    have hconjD := D.weylElement_conj_rootSubgroupPoints i γ A w
    have hconjE := E.weylElement_conj_rootSubgroupPoints (σ i) (f.indexEquiv γ) A
      (w ^ (f.exponent (f.indexEquiv γ)).toNat)
    rw [TauCeti.intCast_units_eq_one_of_charTwo, one_mul] at hconjD hconjE
    rw [← hconjD, map_mul, map_mul, map_inv, hweyl, ih]; dsimp only [partnerPt]
    rw [hconjE, ← hidx, f.indexEquiv_reflectionPerm, f.exponent_reflectionPerm]

private theorem comp_self_eq_frobenius_of_map_rootSubgroupPoints (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny Φ₀ Φ₀) (A : Type v) [CommRing A] [ExpChar A 2]
    {xD : Fin t.numRoots → Multiplicative A →* D.points A}
    (hxD : ∀ α u, xD α (ofAdd u) = partnerPt D f A α u)
    (hcomp : ∀ α u, xD (f.indexEquiv α) (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)) =
      D.frobenius 2 1 A (D.rootSubgroupPoints α A (ofAdd u)))
    (φ : D.points A →* D.points A)
    (hall : ∀ α u, φ (D.rootSubgroupPoints α A u) = xD α u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) : φ (φ g) = D.frobenius 2 1 A g := by
  refine (D.elementarySubgroup_le_iff A ((φ.comp φ).eqLocus (D.frobenius 2 1 A))).mpr
    (fun α u => ?_) hg
  -- Membership in `MonoidHom.eqLocus` unfolds to pointwise equality of the two homomorphisms.
  change φ (φ (D.rootSubgroupPoints α A u)) = D.frobenius 2 1 A (D.rootSubgroupPoints α A u)
  rw [← ofAdd_toAdd u]
  exact (congrArg φ ((hall α _).trans (hxD α _))).trans ((hall _ _).trans (hcomp α (toAdd u)))

end WithDatum

end DoublyLacedAux

/-! ## Type `B₂` in characteristic two -/

section B2

variable {ht : (B 2).Valid} (D E : ChevalleyDatum (B 2) ht) (A : Type v) [CommRing A] [ExpChar A 2]
local notation "ΦB2" => DynkinType.simplyConnectedRootDatum (B 2) ht
local notation "NB2" => DynkinType.structureConstant (B 2) ht
local notation "xB2" => D.b2SpecialIsogenyRootSubgroup A
local notation "xEB2" => E.b2SpecialIsogenyRootSubgroup A

/-- **Commuting root subgroups under the `B₂` exceptional isogeny.** -/
theorem commute_b2SpecialIsogenyRootSubgroup {α β : Fin (B 2).numRoots}
    (h : (ΦB2).root α + (ΦB2).root β ∉ Set.range (ΦB2).root) (h0 : (ΦB2).root α + (ΦB2).root β ≠ 0)
    (u v : A) : Commute (xB2 α (ofAdd u)) (xB2 β (ofAdd v)) := by
  rw [D.b2SpecialIsogenyRootSubgroup_ofAdd, D.b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commute_doublyLaced D (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny_mul_self
    b2SpecialIsogeny_exponent_eq_one_or_eq_two b2SpecialIsogeny_exponent_mul_pairing_comm
    h h0 A u v

/-- **One-factor Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_add {α β γ : Fin (B 2).numRoots}
    (hγ : (ΦB2).root γ = (ΦB2).root α + (ΦB2).root β)
    (hα : 2 • (ΦB2).root α + (ΦB2).root β ∉ Set.range (ΦB2).root)
    (hβ : (ΦB2).root α + 2 • (ΦB2).root β ∉ Set.range (ΦB2).root) (u v : A) :
    ⁅xB2 α (ofAdd u), xB2 β (ofAdd v)⁆ = xB2 γ (ofAdd ((NB2 α β : A) * (u * v))) := by
  rw [D.b2SpecialIsogenyRootSubgroup_ofAdd, D.b2SpecialIsogenyRootSubgroup_ofAdd,
    D.b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_root_eq_add D (simplyConnectedRootDatum_B 2 ht)
    b2SpecialIsogeny_mul_self b2SpecialIsogeny_exponent_eq_one_or_eq_two
    b2SpecialIsogeny_exponent_mul_pairing_comm hγ hα hβ A u v

/-- **Two-factor short-first Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_two_nsmul_add
    {α β γ δ : Fin (B 2).numRoots} (hγ : (ΦB2).root γ = (ΦB2).root α + (ΦB2).root β)
    (hδ : (ΦB2).root δ = 2 • (ΦB2).root α + (ΦB2).root β) (u v : A) :
    ⁅xB2 α (ofAdd u), xB2 β (ofAdd v)⁆ = xB2 γ (ofAdd ((NB2 α β : A) * (u * v))) *
      xB2 δ (ofAdd (((NB2 α β * NB2 α γ / 2 : ℤ) : A) * (u ^ 2 * v))) := by
  rw [D.b2SpecialIsogenyRootSubgroup_ofAdd, D.b2SpecialIsogenyRootSubgroup_ofAdd,
    D.b2SpecialIsogenyRootSubgroup_ofAdd, D.b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_two_nsmul_add D (simplyConnectedRootDatum_B 2 ht)
    b2SpecialIsogeny_mul_self b2SpecialIsogeny_exponent_eq_one_or_eq_two
    b2SpecialIsogeny_exponent_mul_pairing_comm hγ hδ A u v

/-- **Two-factor long-first Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_add_two_nsmul
    {α β γ δ : Fin (B 2).numRoots} (hγ : (ΦB2).root γ = (ΦB2).root α + (ΦB2).root β)
    (hδ : (ΦB2).root δ = (ΦB2).root α + 2 • (ΦB2).root β) (u v : A) :
    ⁅xB2 α (ofAdd u), xB2 β (ofAdd v)⁆ = xB2 γ (ofAdd ((NB2 α β : A) * (u * v))) *
      xB2 δ (ofAdd (((-(NB2 β α * NB2 β γ / 2) : ℤ) : A) * (u * v ^ 2))) := by
  rw [D.b2SpecialIsogenyRootSubgroup_ofAdd, D.b2SpecialIsogenyRootSubgroup_ofAdd,
    D.b2SpecialIsogenyRootSubgroup_ofAdd, D.b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_add_two_nsmul D (simplyConnectedRootDatum_B 2 ht)
    b2SpecialIsogeny_mul_self b2SpecialIsogeny_exponent_eq_one_or_eq_two
    b2SpecialIsogeny_exponent_mul_pairing_comm hγ hδ A u v

/-- A group homomorphism `φ : D.points A →* E.points A` agreeing with
`E.b2SpecialIsogenyRootSubgroup A` on the positive and negative simple root subgroups agrees with
it on every root subgroup. -/
theorem map_rootSubgroupPoints_of_b2SpecialIsogeny_simple (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints ((B 2).simpleIndex ht i) A u) =
      xEB2 ((B 2).simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) A u) =
      xEB2 ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) u)
    (α : Fin (B 2).numRoots) (u : Multiplicative A) : φ (D.rootSubgroupPoints α A u) = xEB2 α u :=
  map_rootSubgroupPoints_doublyLaced D E (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny
    (b2SpecialIsogeny_indexEquiv_simpleIndex ht) A (E.b2SpecialIsogenyRootSubgroup_ofAdd A)
    (E.b2SpecialIsogenyRootSubgroup_weylElement A) φ hpos hneg α u

/-- An endomorphism `φ : D.points A →* D.points A` agreeing with `b2SpecialIsogenyRootSubgroup` on
the positive and negative simple root subgroups squares to `D.frobenius 2 1 A` on
`D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_b2SpecialIsogeny_simple (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints ((B 2).simpleIndex ht i) A u) =
      xB2 ((B 2).simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) A u) =
      xB2 ((ΦB2).reflectionPerm ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) : φ (φ g) = D.frobenius 2 1 A g :=
  comp_self_eq_frobenius_of_map_rootSubgroupPoints D b2SpecialIsogeny A
    (D.b2SpecialIsogenyRootSubgroup_ofAdd A) (D.b2SpecialIsogenyRootSubgroup_comp_self A) φ
    (map_rootSubgroupPoints_of_b2SpecialIsogeny_simple D D A φ hpos hneg) hg

end B2

/-! ## Type `F₄` in characteristic two -/

section F4
variable {ht : F4.Valid} (D E : ChevalleyDatum F4 ht) (A : Type v) [CommRing A] [ExpChar A 2]
local notation "ΦF4" => F4.simplyConnectedRootDatum ht
local notation "NF4" => F4.structureConstant ht
local notation "xF4" => D.f4SpecialIsogenyRootSubgroup A
local notation "xEF4" => E.f4SpecialIsogenyRootSubgroup A

/-- **Commuting root subgroups under the `F₄` exceptional isogeny.** -/
theorem commute_f4SpecialIsogenyRootSubgroup {α β : Fin F4.numRoots}
    (h : (ΦF4).root α + (ΦF4).root β ∉ Set.range (ΦF4).root) (h0 : (ΦF4).root α + (ΦF4).root β ≠ 0)
    (u v : A) : Commute (xF4 α (ofAdd u)) (xF4 β (ofAdd v)) := by
  rw [D.f4SpecialIsogenyRootSubgroup_ofAdd, D.f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commute_doublyLaced D (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny_mul_self
    f4SpecialIsogeny_exponent_eq_one_or_eq_two f4SpecialIsogeny_exponent_mul_pairing_comm
    h h0 A u v

/-- **One-factor Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_add {α β γ : Fin F4.numRoots}
    (hγ : (ΦF4).root γ = (ΦF4).root α + (ΦF4).root β)
    (hα : 2 • (ΦF4).root α + (ΦF4).root β ∉ Set.range (ΦF4).root)
    (hβ : (ΦF4).root α + 2 • (ΦF4).root β ∉ Set.range (ΦF4).root) (u v : A) :
    ⁅xF4 α (ofAdd u), xF4 β (ofAdd v)⁆ = xF4 γ (ofAdd ((NF4 α β : A) * (u * v))) := by
  rw [D.f4SpecialIsogenyRootSubgroup_ofAdd, D.f4SpecialIsogenyRootSubgroup_ofAdd,
    D.f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_root_eq_add D (simplyConnectedRootDatum_F4 ht)
    f4SpecialIsogeny_mul_self f4SpecialIsogeny_exponent_eq_one_or_eq_two
    f4SpecialIsogeny_exponent_mul_pairing_comm hγ hα hβ A u v

/-- **Two-factor short-first Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_two_nsmul_add
    {α β γ δ : Fin F4.numRoots} (hγ : (ΦF4).root γ = (ΦF4).root α + (ΦF4).root β)
    (hδ : (ΦF4).root δ = 2 • (ΦF4).root α + (ΦF4).root β) (u v : A) :
    ⁅xF4 α (ofAdd u), xF4 β (ofAdd v)⁆ = xF4 γ (ofAdd ((NF4 α β : A) * (u * v))) *
      xF4 δ (ofAdd (((NF4 α β * NF4 α γ / 2 : ℤ) : A) * (u ^ 2 * v))) := by
  rw [D.f4SpecialIsogenyRootSubgroup_ofAdd, D.f4SpecialIsogenyRootSubgroup_ofAdd,
    D.f4SpecialIsogenyRootSubgroup_ofAdd, D.f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_two_nsmul_add D (simplyConnectedRootDatum_F4 ht)
    f4SpecialIsogeny_mul_self f4SpecialIsogeny_exponent_eq_one_or_eq_two
    f4SpecialIsogeny_exponent_mul_pairing_comm hγ hδ A u v

/-- **Two-factor long-first Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_add_two_nsmul
    {α β γ δ : Fin F4.numRoots} (hγ : (ΦF4).root γ = (ΦF4).root α + (ΦF4).root β)
    (hδ : (ΦF4).root δ = (ΦF4).root α + 2 • (ΦF4).root β) (u v : A) :
    ⁅xF4 α (ofAdd u), xF4 β (ofAdd v)⁆ = xF4 γ (ofAdd ((NF4 α β : A) * (u * v))) *
      xF4 δ (ofAdd (((-(NF4 β α * NF4 β γ / 2) : ℤ) : A) * (u * v ^ 2))) := by
  rw [D.f4SpecialIsogenyRootSubgroup_ofAdd, D.f4SpecialIsogenyRootSubgroup_ofAdd,
    D.f4SpecialIsogenyRootSubgroup_ofAdd, D.f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_add_two_nsmul D (simplyConnectedRootDatum_F4 ht)
    f4SpecialIsogeny_mul_self f4SpecialIsogeny_exponent_eq_one_or_eq_two
    f4SpecialIsogeny_exponent_mul_pairing_comm hγ hδ A u v

/-- A group homomorphism `φ : D.points A →* E.points A` agreeing with
`E.f4SpecialIsogenyRootSubgroup A` on the positive and negative simple root subgroups agrees with
it on every root subgroup. -/
theorem map_rootSubgroupPoints_of_f4SpecialIsogeny_simple (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (F4.simpleIndex ht i) A u) =
      xEF4 (F4.simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) A u) =
      xEF4 ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) u)
    (α : Fin F4.numRoots) (u : Multiplicative A) : φ (D.rootSubgroupPoints α A u) = xEF4 α u :=
  map_rootSubgroupPoints_doublyLaced D E (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny
    (f4SpecialIsogeny_indexEquiv_simpleIndex ht) A (E.f4SpecialIsogenyRootSubgroup_ofAdd A)
    (E.f4SpecialIsogenyRootSubgroup_weylElement A) φ hpos hneg α u

/-- An endomorphism `φ : D.points A →* D.points A` agreeing with `f4SpecialIsogenyRootSubgroup` on
the positive and negative simple root subgroups squares to `D.frobenius 2 1 A` on
`D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_f4SpecialIsogeny_simple (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (F4.simpleIndex ht i) A u) =
      xF4 (F4.simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) A u) =
      xF4 ((ΦF4).reflectionPerm (F4.simpleIndex ht i) (F4.simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) : φ (φ g) = D.frobenius 2 1 A g :=
  comp_self_eq_frobenius_of_map_rootSubgroupPoints D f4SpecialIsogeny A
    (D.f4SpecialIsogenyRootSubgroup_ofAdd A) (D.f4SpecialIsogenyRootSubgroup_comp_self A) φ
    (map_rootSubgroupPoints_of_f4SpecialIsogeny_simple D D A φ hpos hneg) hg

end F4

end TauCeti.DynkinType.ChevalleyDatum
