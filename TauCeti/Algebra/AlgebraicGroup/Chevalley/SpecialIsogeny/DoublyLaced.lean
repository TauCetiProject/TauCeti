/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SpecialIsogeny.Basic
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString
import TauCeti.LinearAlgebra.RootSystem.Isogeny.Reflection
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.RootString
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Rational
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Characteristic-two commutator relations and Weyl determination for `B₂` and `F₄`

Over a commutative ring `A` of exponential characteristic `2`, the exceptional-isogeny
root-subgroup homomorphisms `TauCeti.DynkinType.ChevalleyDatum.b2SpecialIsogenyRootSubgroup` and
`TauCeti.DynkinType.ChevalleyDatum.f4SpecialIsogenyRootSubgroup` satisfy every Chevalley
commutator relation of the source root system, and any group homomorphism between Chevalley point
groups matching their pinned values on the positive and negative simple roots agrees with them on
all roots.

Both facts are proved uniformly from a root-datum endo-isogeny `f` with `f * f = smulId _ 2`,
exponents in `{1, 2}`, and symmetrized Cartan pairings `f.exponent α * ⟨β, α^∨⟩ =
f.exponent β * ⟨α, β^∨⟩`:

* **Commuting root pairs**: if `α + β` is neither a root nor zero, either `f(α) + f(β)` is not a
  root, or `f(α)` and `f(β)` are orthogonal short roots summing to a long root whose Chevalley
  bracket coefficient `±2` vanishes in `A`.
* **One-factor strings**: if `γ = α + β` is a root while `2α + β` and `α + 2β` are not, reflections
  exclude mixed root lengths; equal-length triangles map to equal-length triangles with unit
  structure constants mod `2`, while a short-short-to-long sum has vanishing structure constant in
  `A` and orthogonal long images whose sum has squared length `4 ∉ {1, 2}`.
* **Two-factor strings**: if `γ = α + β` and `δ = 2α + β` are roots, `α` and `γ` are short while
  `β` and `δ` are long; `f` exchanges the two steps so `δ' = α' + β'` and `γ' = α' + 2β'`, matching
  the long-first commutator formula in `A`.
* **Simple-root determination**: in characteristic `2`, `((ε : ℤˣ) : A) = 1` erases Weyl-conjugation
  signs, so `RootPairing.Base.induction_simple_reflect` transports agreement from the signed simple
  roots to every root, forcing `φ ∘ φ = frobenius 2 1` on `D.elementarySubgroup A`.

## Main results

* `commute_b2SpecialIsogenyRootSubgroup`, `commute_f4SpecialIsogenyRootSubgroup`, and the
  `commutatorElement_*SpecialIsogenyRootSubgroup_of_*` theorems: preservation of all Chevalley
  commutator relations of types `B₂` and `F₄` over `[ExpChar A 2]`.
* `map_rootSubgroupPoints_of_b2SpecialIsogeny_simple` and
  `map_rootSubgroupPoints_of_f4SpecialIsogeny_simple`: pinned simple-root values determine the
  image of every root subgroup.
* `comp_self_eq_frobenius_of_b2SpecialIsogeny_simple` and
  `comp_self_eq_frobenius_of_f4SpecialIsogeny_simple`: any endomorphism with the pinned simple-root
  values squares to `D.frobenius 2 1 A` on `D.elementarySubgroup A`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Lemma 53 and Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3–12.4.
-/

public section

open scoped commutatorElement

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative

universe v

/-! ## Uniform doubly-laced helpers in characteristic two -/

section DoublyLacedAux

private def congrIso {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {P Q : RootPairing ι R M N} (h : P = Q)
    (f : RootPairingIsogeny Q Q) : RootPairingIsogeny P P where
  weightMap := f.weightMap
  coweightMap := f.coweightMap
  indexEquiv := f.indexEquiv
  exponent := f.exponent
  exponent_pos := f.exponent_pos
  weightMap_injective := f.weightMap_injective
  coweightMap_injective := f.coweightMap_injective
  weightMap_finiteIndex := f.weightMap_finiteIndex
  coweightMap_finiteIndex := f.coweightMap_finiteIndex
  weight_coweight_transpose := by subst h; exact f.weight_coweight_transpose
  root_weightMap := by subst h; exact f.root_weightMap
  coroot_coweightMap := by subst h; exact f.coroot_coweightMap

private theorem congrIso_mul_self {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    {P Q : RootDatum ι M N} (h : P = Q) (f : RootPairingIsogeny Q Q)
    (hf : f * f = RootPairingIsogeny.smulId Q 2) :
    congrIso h f * congrIso h f = RootPairingIsogeny.smulId P 2 := by
  subst h
  exact hf

private theorem intUnits_cast_eq_one {A : Type*} [CommRing A] [CharP A 2] (ε : ℤˣ) :
    ((ε : ℤ) : A) = 1 := by
  have h2 : (2 : A) = 0 := CharP.cast_eq_zero A 2
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · push_cast
    linear_combination -h2

private theorem cast_structureConstant_eq_one {t : DynkinType} {ht : t.Valid}
    {α β : Fin t.numRoots}
    (hsum : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∈
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0)
    (A : Type*) [CommRing A] [CharP A 2] :
    (t.structureConstant ht α β : A) = 1 := by
  have h2 : (2 : A) = 0 := CharP.cast_eq_zero A 2
  rcases structureConstant_eq_natCast_or_eq_neg_natCast hsum with h | h <;>
    rw [h, hbot] <;> push_cast
  · rfl
  · linear_combination -h2

private theorem cast_structureConstant_eq_zero {t : DynkinType} {ht : t.Valid}
    {α β : Fin t.numRoots}
    (hsum : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∈
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 1)
    (A : Type*) [CommRing A] [CharP A 2] :
    (t.structureConstant ht α β : A) = 0 := by
  have h2 : (2 : A) = 0 := CharP.cast_eq_zero A 2
  rcases structureConstant_eq_natCast_or_eq_neg_natCast hsum with h | h <;>
    rw [h, hbot] <;> push_cast
  · exact h2
  · linear_combination -h2

private theorem cast_div_two_eq_one {t : DynkinType} {ht : t.Valid}
    {α β γ : Fin t.numRoots}
    (hαβ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∈
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hαγ : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ ∈
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hbot₁ : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0)
    (hbot₂ : (t.simplyConnectedRootDatum ht).chainBotCoeff α γ = 1)
    (A : Type*) [CommRing A] [CharP A 2] :
    ((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) = 1 := by
  have h2 : (2 : A) = 0 := CharP.cast_eq_zero A 2
  have h1 := structureConstant_eq_natCast_or_eq_neg_natCast hαβ
  have h3 := structureConstant_eq_natCast_or_eq_neg_natCast hαγ
  rw [hbot₁] at h1
  rw [hbot₂] at h3
  rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3 <;> rw [h1, h3] <;> norm_num
  · linear_combination -h2
  · linear_combination -h2

private theorem abs_pairing_le_two_of_sym {t : DynkinType} {ht : t.Valid}
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    (α β : Fin t.numRoots) :
    |(t.simplyConnectedRootDatum ht).pairing α β| ≤ 2 := by
  have : Module.IsReflexive ℤ (Fin t.rank → ℤ) :=
    .of_isPerfPair (t.simplyConnectedRootDatum ht).toLinearMap
  have hpi (i j : Fin t.numRoots) :
      (t.simplyConnectedRootDatum ht).pairingIn ℤ i j =
        (t.simplyConnectedRootDatum ht).pairing i j := by
    simpa using (t.simplyConnectedRootDatum ht).algebraMap_pairingIn ℤ i j
  have hw := (t.simplyConnectedRootDatum ht).coxeterWeightIn_le_four ℤ α β
  rw [RootPairing.coxeterWeightIn, hpi, hpi] at hw
  have hs := hsym α β
  rw [abs_le]
  rcases hexp α with hα | hα <;> rcases hexp β with hβ | hβ <;> rw [hα, hβ] at hs <;>
    constructor <;> nlinarith

private theorem exponent_indexEquiv_cases {t : DynkinType} {ht : t.Valid}
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2) (α : Fin t.numRoots) :
    (f.exponent α = 1 ∧ f.exponent (f.indexEquiv α) = 2 ∧
        (f.exponent (f.indexEquiv α)).toNat = 2) ∨
      (f.exponent α = 2 ∧ f.exponent (f.indexEquiv α) = 1 ∧
        (f.exponent (f.indexEquiv α)).toNat = 1) := by
  have hmul : f.exponent α * f.exponent (f.indexEquiv α) = 2 := by
    simpa using f.exponent_mul_exponent_indexEquiv (t.simplyConnectedRootDatum ht) hf α
  rcases hexp α with hα | hα
  · left
    rw [hα] at hmul
    have h' : f.exponent (f.indexEquiv α) = 2 := by omega
    exact ⟨hα, h', by simp [h']⟩
  · right
    rw [hα] at hmul
    have h' : f.exponent (f.indexEquiv α) = 1 := by omega
    exact ⟨hα, h', by simp [h']⟩

private theorem not_root_eq_add_nsmul_of_exp_eq {t : DynkinType} {ht : t.Valid}
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    (n : ℕ) {α β γ : Fin t.numRoots}
    (hαβ : f.exponent α = f.exponent β)
    (h0 : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (hn : 2 ≤ n)
    (h : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root β + (n : ℤ) • (t.simplyConnectedRootDatum ht).root α) :
    False := by
  refine (t.simplyConnectedRootDatum ht).not_root_eq_add_nsmul_of_length_eq_of_two_le
    f.exponent hsym α β γ n (f.exponent_pos α) hαβ ?_
    (fun hneg => h0 (by rw [hneg, add_neg_cancel])) hn h
  rcases hexp α with h1 | h1 <;> rcases hexp γ with h2 | h2 <;> omega

private theorem root_add_mem_of_root_add_two_smul_mem {t : DynkinType} {ht : t.Valid}
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ : Fin t.numRoots}
    (h0 : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root β + (2 : ℤ) • (t.simplyConnectedRootDatum ht).root α) :
    (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root α ∈
      Set.range (t.simplyConnectedRootDatum ht).root := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : Module.IsReflexive ℤ (Fin t.rank → ℤ) :=
    .of_isPerfPair (t.simplyConnectedRootDatum ht).toLinearMap
  have hne : α ≠ β := by
    rintro rfl
    have hlen := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul
      f.exponent hsym α α γ 2 hγ
    rw [(t.simplyConnectedRootDatum ht).pairing_same] at hlen
    rcases hexp α with h1 | h1 <;> rcases hexp γ with h2 | h2 <;> omega
  have hlin : LinearIndependent ℤ
      ![(t.simplyConnectedRootDatum ht).root α, (t.simplyConnectedRootDatum ht).root β] :=
    RootPairing.IsReduced.linearIndependent (t.simplyConnectedRootDatum ht) hne
      (fun hneg => h0 (by rw [hneg, neg_add_cancel]))
  have htop : 2 ≤ (t.simplyConnectedRootDatum ht).chainTopCoeff α β :=
    ((t.simplyConnectedRootDatum ht).root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mp
      ⟨γ, by rw [hγ]; module⟩
  simpa only [one_nsmul] using
    ((t.simplyConnectedRootDatum ht).root_add_nsmul_mem_range_iff_le_chainTopCoeff
      (n := 1) hlin).mpr (by omega)

private theorem partner_exponents_of_notMem_range {t : DynkinType} {ht : t.Valid}
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ' : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (h0 : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (hγ' : (t.simplyConnectedRootDatum ht).root γ' =
      (t.simplyConnectedRootDatum ht).root (f.indexEquiv α) +
        (t.simplyConnectedRootDatum ht).root (f.indexEquiv β)) :
    f.exponent (f.indexEquiv α) = 1 ∧ f.exponent (f.indexEquiv β) = 1 ∧ f.exponent γ' = 2 := by
  have hw : f.exponent γ' • (t.simplyConnectedRootDatum ht).root (f.indexEquiv γ') =
      f.exponent (f.indexEquiv α) • (t.simplyConnectedRootDatum ht).root α +
        f.exponent (f.indexEquiv β) • (t.simplyConnectedRootDatum ht).root β := by
    have h1 := congrArg f.weightMap hγ'
    rw [map_add, f.root_weightMap,
      f.weightMap_root_indexEquiv (t.simplyConnectedRootDatum ht) hf,
      f.weightMap_root_indexEquiv (t.simplyConnectedRootDatum ht) hf] at h1
    exact h1
  have hlen := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul
    f.exponent hsym (f.indexEquiv α) (f.indexEquiv β) γ' 1 (by rw [hγ']; module)
  have hs := hsym (f.indexEquiv α) (f.indexEquiv β)
  rcases hexp (f.indexEquiv α) with hα' | hα' <;> rcases hexp (f.indexEquiv β) with hβ' | hβ' <;>
    rcases hexp γ' with hγ'len | hγ'len
  · exfalso; exact h ⟨f.indexEquiv γ', by simp only [hα', hβ', hγ'len, one_smul] at hw; exact hw⟩
  · exact ⟨hα', hβ', hγ'len⟩
  · exfalso
    refine h (root_add_mem_of_root_add_two_smul_mem f hexp hsym
      (α := β) (β := α) (γ := f.indexEquiv γ') (by rw [add_comm]; exact h0) ?_)
    simp only [hα', hβ', hγ'len, one_smul] at hw; exact hw
  · rw [hα', hβ'] at hs; rw [hα', hβ', hγ'len] at hlen; omega
  · exfalso; rw [add_comm] at h
    refine h (root_add_mem_of_root_add_two_smul_mem f hexp hsym
      (α := α) (β := β) (γ := f.indexEquiv γ') h0 ?_)
    simp only [hα', hβ', hγ'len, one_smul] at hw; rw [hw]; module
  · rw [hα', hβ', hγ'len] at hlen; omega
  · rw [hα', hβ', hγ'len] at hlen; omega
  · exfalso; refine h ⟨f.indexEquiv γ', smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0) ?_⟩
    simp only [hα', hβ', hγ'len] at hw; dsimp; rw [hw]; module

private theorem commute_doublyLaced {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β : Fin t.numRoots}
    (h : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (h0 : (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ≠ 0)
    (A : Type v) [CommRing A] [ExpChar A 2] (u v : A) :
    Commute
      (D.rootSubgroupPoints (f.indexEquiv α) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)))
      (D.rootSubgroupPoints (f.indexEquiv β) A
        (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat))) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : CharP A 2 := (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
  set α' := f.indexEquiv α
  set β' := f.indexEquiv β
  have h0' : (t.simplyConnectedRootDatum ht).root α' +
      (t.simplyConnectedRootDatum ht).root β' ≠ 0 :=
    (f.root_indexEquiv_add_eq_zero_iff α β).not.mpr h0
  by_cases hrange : (t.simplyConnectedRootDatum ht).root α' +
      (t.simplyConnectedRootDatum ht).root β' ∈ Set.range (t.simplyConnectedRootDatum ht).root
  · obtain ⟨γ', hγ'⟩ := hrange
    have hshort := partner_exponents_of_notMem_range f hf hexp hsym h h0 hγ'
    obtain ⟨hα', hβ', hγ'len⟩ := hshort
    have h2α' : 2 • (t.simplyConnectedRootDatum ht).root α' +
        (t.simplyConnectedRootDatum ht).root β' ∉
          Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ =>
      not_root_eq_add_nsmul_of_exp_eq f hexp hsym 2 (hα'.trans hβ'.symm) h0' (by omega)
        (by rw [hρ]; module)
    have h2β' : (t.simplyConnectedRootDatum ht).root α' +
        2 • (t.simplyConnectedRootDatum ht).root β' ∉
          Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ =>
      not_root_eq_add_nsmul_of_exp_eq f hexp hsym 2 (hβ'.trans hα'.symm)
        (by rw [add_comm]; exact h0') (by omega) (by rw [hρ]; module)
    have hbot := (t.simplyConnectedRootDatum ht).chainBotCoeff_eq_one_of_short_add_short_eq_long
      f.exponent hsym α' β' γ' hα' hβ' hγ'len (hγ'.trans (add_comm _ _))
    rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm,
      D.commutatorElement_rootSubgroup_of_root_eq_add hγ' h2α' h2β',
      cast_structureConstant_eq_zero ⟨γ', hγ'⟩ hbot A, zero_mul, ofAdd_zero, map_one]
  · exact D.commute_rootSubgroup hrange h0' A _ _

private theorem commutatorElement_doublyLaced_of_eq_len {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hαβ : f.exponent α = f.exponent β) (hβγ : f.exponent β = f.exponent γ)
    (A : Type v) [CommRing A] [ExpChar A 2] (u v : A) :
    ⁅D.rootSubgroupPoints (f.indexEquiv α) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)),
      D.rootSubgroupPoints (f.indexEquiv β) A
        (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat))⁆ =
      D.rootSubgroupPoints (f.indexEquiv γ) A
        (ofAdd (((t.structureConstant ht α β : A) * (u * v)) ^
          (f.exponent (f.indexEquiv γ)).toNat)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : CharP A 2 := (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
  set α' := f.indexEquiv α
  set β' := f.indexEquiv β
  set γ' := f.indexEquiv γ
  have hγ' : (t.simplyConnectedRootDatum ht).root γ' =
      (t.simplyConnectedRootDatum ht).root α' + (t.simplyConnectedRootDatum ht).root β' := by
    apply smul_right_injective _ (f.exponent_pos γ).ne'
    have hw := congrArg f.weightMap hγ
    rw [map_add, f.root_weightMap, f.root_weightMap, f.root_weightMap, hαβ, hβγ, ← smul_add] at hw
    exact hw
  have hα'β' : f.exponent α' = f.exponent β' := by
    dsimp only [α', β']
    rcases exponent_indexEquiv_cases f hf hexp α with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
      rcases exponent_indexEquiv_cases f hf hexp β with ⟨h3, h4, _⟩ | ⟨h3, h4, _⟩ <;> omega
  have hβ'γ' : f.exponent β' = f.exponent γ' := by
    dsimp only [β', γ']
    rcases exponent_indexEquiv_cases f hf hexp β with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;>
      rcases exponent_indexEquiv_cases f hf hexp γ with ⟨h3, h4, _⟩ | ⟨h3, h4, _⟩ <;> omega
  have h0' : (t.simplyConnectedRootDatum ht).root α' +
      (t.simplyConnectedRootDatum ht).root β' ≠ 0 :=
    hγ' ▸ (t.simplyConnectedRootDatum ht).ne_zero γ'
  have h2α' : 2 • (t.simplyConnectedRootDatum ht).root α' +
      (t.simplyConnectedRootDatum ht).root β' ∉
        Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ =>
    not_root_eq_add_nsmul_of_exp_eq f hexp hsym 2 hα'β' h0' (by omega)
      (by rw [hρ]; module)
  have h2β' : (t.simplyConnectedRootDatum ht).root α' +
      2 • (t.simplyConnectedRootDatum ht).root β' ∉
        Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ =>
    not_root_eq_add_nsmul_of_exp_eq f hexp hsym 2 hα'β'.symm (by rw [add_comm]; exact h0')
      (by omega) (by rw [hρ]; module)
  have hbot : (t.simplyConnectedRootDatum ht).chainBotCoeff α β = 0 :=
    (t.simplyConnectedRootDatum ht).chainBotCoeff_eq_zero_of_add_of_length_eq f.exponent hsym
      α β γ (f.exponent_pos α) (fun δ _ => by rcases hexp δ with h | h <;> omega) hβγ
      (hγ.trans (add_comm _ _))
  have hbot' : (t.simplyConnectedRootDatum ht).chainBotCoeff α' β' = 0 :=
    (t.simplyConnectedRootDatum ht).chainBotCoeff_eq_zero_of_add_of_length_eq f.exponent hsym
      α' β' γ' (f.exponent_pos α') (fun δ _ => by rcases hexp δ with h | h <;> omega) hβ'γ'
      (hγ'.trans (add_comm _ _))
  rw [D.commutatorElement_rootSubgroup_of_root_eq_add hγ' h2α' h2β',
    cast_structureConstant_eq_one ⟨γ, hγ⟩ hbot A,
    cast_structureConstant_eq_one ⟨γ', hγ'⟩ hbot' A, one_mul, one_mul,
    ← hβ'γ', ← hα'β', mul_pow]

private theorem commutatorElement_doublyLaced_of_short_short_long {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hαlen : f.exponent α = 1) (hβlen : f.exponent β = 1) (hγlen : f.exponent γ = 2)
    (A : Type v) [CommRing A] [ExpChar A 2] (u v : A) :
    ⁅D.rootSubgroupPoints (f.indexEquiv α) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)),
      D.rootSubgroupPoints (f.indexEquiv β) A
        (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat))⁆ =
      D.rootSubgroupPoints (f.indexEquiv γ) A
        (ofAdd (((t.structureConstant ht α β : A) * (u * v)) ^
          (f.exponent (f.indexEquiv γ)).toNat)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : CharP A 2 := (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
  have hbot := (t.simplyConnectedRootDatum ht).chainBotCoeff_eq_one_of_short_add_short_eq_long
    f.exponent hsym α β γ hαlen hβlen hγlen (hγ.trans (add_comm _ _))
  have hp0 := (t.simplyConnectedRootDatum ht).pairing_eq_zero_of_short_add_short_eq_long
    f.exponent hsym α β γ hαlen hβlen hγlen (hγ.trans (add_comm _ _))
  have hp0' : (t.simplyConnectedRootDatum ht).pairing (f.indexEquiv β) (f.indexEquiv α) = 0 := by
    simpa [hαlen, hβlen, hp0] using f.exponent_mul_pairing β α
  have hα'len : f.exponent (f.indexEquiv α) = 2 := by
    rcases exponent_indexEquiv_cases f hf hexp α with ⟨_, h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · omega
  have hβ'len : f.exponent (f.indexEquiv β) = 2 := by
    rcases exponent_indexEquiv_cases f hf hexp β with ⟨_, h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · omega
  have hγ'len : (f.exponent (f.indexEquiv γ)).toNat = 1 := by
    rcases exponent_indexEquiv_cases f hf hexp γ with ⟨h1, _⟩ | ⟨_, _, h2⟩
    · omega
    · exact h2
  have hrange' : (t.simplyConnectedRootDatum ht).root (f.indexEquiv α) +
      (t.simplyConnectedRootDatum ht).root (f.indexEquiv β) ∉
        Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ => by
    have hρlen := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul f.exponent hsym
      (f.indexEquiv α) (f.indexEquiv β) ρ 1 (by rw [hρ]; module)
    rcases hexp ρ with h1 | h1 <;> rw [hα'len, hβ'len, hp0', h1] at hρlen <;> omega
  have h0' : (t.simplyConnectedRootDatum ht).root (f.indexEquiv α) +
      (t.simplyConnectedRootDatum ht).root (f.indexEquiv β) ≠ 0 :=
    (f.root_indexEquiv_add_eq_zero_iff α β).not.mpr
      (hγ ▸ (t.simplyConnectedRootDatum ht).ne_zero γ)
  rw [commutatorElement_eq_one_iff_mul_comm.mpr ((D.commute_rootSubgroup hrange' h0' A _ _).eq),
    cast_structureConstant_eq_zero ⟨γ, hγ⟩ hbot A, zero_mul, hγ'len, pow_one, ofAdd_zero, map_one]

private theorem commutatorElement_doublyLaced_of_root_eq_add {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hα : 2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (hβ : (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β ∉
      Set.range (t.simplyConnectedRootDatum ht).root)
    (A : Type v) [CommRing A] [ExpChar A 2] (u v : A) :
    ⁅D.rootSubgroupPoints (f.indexEquiv α) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)),
      D.rootSubgroupPoints (f.indexEquiv β) A
        (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat))⁆ =
      D.rootSubgroupPoints (f.indexEquiv γ) A
        (ofAdd (((t.structureConstant ht α β : A) * (u * v)) ^
          (f.exponent (f.indexEquiv γ)).toNat)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : CharP A 2 := (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
  have hlen := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul
    f.exponent hsym α β γ 1 (by rw [hγ]; module)
  have hs := hsym α β
  rcases hexp α with hαlen | hαlen <;> rcases hexp β with hβlen | hβlen
  · rcases hexp γ with hγlen | hγlen
    · exact commutatorElement_doublyLaced_of_eq_len D f hf hexp hsym hγ
        (hαlen.trans hβlen.symm) (hβlen.trans hγlen.symm) A u v
    · exact commutatorElement_doublyLaced_of_short_short_long D f hf hexp hsym
        hγ hαlen hβlen hγlen A u v
  · exfalso
    rw [hαlen, hβlen] at hlen hs
    have hp : (t.simplyConnectedRootDatum ht).pairing β α = -2 := by
      rcases hexp γ with hγlen | hγlen <;> omega
    apply hα
    refine ⟨(t.simplyConnectedRootDatum ht).reflectionPerm α β, ?_⟩
    have hr := (t.simplyConnectedRootDatum ht).root_reflectionPerm α β
    rw [(t.simplyConnectedRootDatum ht).reflection_apply_root, hp] at hr
    rw [hr]; module
  · exfalso
    have hlen' := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul
      f.exponent hsym β α γ 1 (by rw [hγ]; module)
    rw [hαlen, hβlen] at hlen' hs
    have hp : (t.simplyConnectedRootDatum ht).pairing α β = -2 := by
      rcases hexp γ with hγlen | hγlen <;> omega
    apply hβ
    refine ⟨(t.simplyConnectedRootDatum ht).reflectionPerm β α, ?_⟩
    have hr := (t.simplyConnectedRootDatum ht).root_reflectionPerm β α
    rw [(t.simplyConnectedRootDatum ht).reflection_apply_root, hp] at hr
    rw [hr]; module
  · rw [hαlen, hβlen] at hlen
    have hγlen : f.exponent γ = 2 := by rcases hexp γ with hγlen | hγlen <;> omega
    exact commutatorElement_doublyLaced_of_eq_len D f hf hexp hsym hγ
      (hαlen.trans hβlen.symm) (hβlen.trans hγlen.symm) A u v

private theorem short_long_of_two_nsmul_add {t : DynkinType} {ht : t.Valid}
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β) :
    f.exponent α = 1 ∧ f.exponent β = 2 := by
  have hbound := abs_pairing_le_two_of_sym f hexp hsym
  have h0 : (t.simplyConnectedRootDatum ht).root α +
      (t.simplyConnectedRootDatum ht).root β ≠ 0 :=
    hγ ▸ (t.simplyConnectedRootDatum ht).ne_zero γ
  have hδ'z : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root β +
        (2 : ℤ) • (t.simplyConnectedRootDatum ht).root α := by
    rw [hδ]; module
  rcases hexp α with hα | hα <;> rcases hexp β with hβ | hβ
  · exfalso
    exact not_root_eq_add_nsmul_of_exp_eq f hexp hsym 2 (hα.trans hβ.symm) h0 (by omega) hδ'z
  · exact ⟨hα, hβ⟩
  · exfalso
    have hn := (t.simplyConnectedRootDatum ht)
      |>.n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
      f.exponent hsym α β δ 2 (hbound α β) hα hβ (hexp δ) (by omega) hδ'z
    exact absurd hn.1 (by decide)
  · exfalso
    exact not_root_eq_add_nsmul_of_exp_eq f hexp hsym 2 (hα.trans hβ.symm) h0 (by omega) hδ'z

private theorem commute_short_add_long_with_two_short_add_long {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {β' δ' γ' : Fin t.numRoots}
    (hβ' : f.exponent β' = 1) (hδ' : f.exponent δ' = 1) (hγ' : f.exponent γ' = 2)
    (hsub : (t.simplyConnectedRootDatum ht).root γ' =
      (t.simplyConnectedRootDatum ht).root δ' + (t.simplyConnectedRootDatum ht).root β')
    (A : Type v) [CommRing A] (x y : Multiplicative A) :
    Commute (D.rootSubgroupPoints δ' A x) (D.rootSubgroupPoints γ' A y) := by
  have hrange : (t.simplyConnectedRootDatum ht).root δ' +
      (t.simplyConnectedRootDatum ht).root γ' ∉
        Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ => by
    have hp0 := (t.simplyConnectedRootDatum ht).pairing_eq_zero_of_short_add_short_eq_long
      f.exponent hsym β' δ' γ' hβ' hδ' hγ' hsub
    have hpβ'δ' : (t.simplyConnectedRootDatum ht).pairing β' δ' = 0 := by
      have hs' := hsym β' δ'; rw [hβ', hδ', hp0] at hs'; omega
    have hpγ'δ' : (t.simplyConnectedRootDatum ht).pairing γ' δ' = 2 := by
      have hpadd := (t.simplyConnectedRootDatum ht).pairing_eq_add_of_root_eq_add (l := δ') hsub
      rw [(t.simplyConnectedRootDatum ht).pairing_same, hpβ'δ'] at hpadd; omega
    have hρlen := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul f.exponent hsym
      δ' γ' ρ 1 (by rw [hρ]; module)
    rcases hexp ρ with h1 | h1 <;> rw [hδ', hγ', hpγ'δ', h1] at hρlen <;> omega
  have h0 : (t.simplyConnectedRootDatum ht).root δ' +
      (t.simplyConnectedRootDatum ht).root γ' ≠ 0 := fun hz => by
    have hneg : (t.simplyConnectedRootDatum ht).root γ' =
        (t.simplyConnectedRootDatum ht).root δ' +
          (-2 : ℤ) • (t.simplyConnectedRootDatum ht).root δ' := by
      rw [eq_neg_of_add_eq_zero_right hz]; module
    have hlen := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul f.exponent hsym
      δ' δ' γ' (-2) hneg
    rw [hγ', hδ', (t.simplyConnectedRootDatum ht).pairing_same] at hlen; omega
  exact D.commute_rootSubgroup hrange h0 A x y

private theorem partner_roots_of_two_nsmul_add {t : DynkinType} {ht : t.Valid}
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hα1 : f.exponent α = 1) (hβ2 : f.exponent β = 2)
    (hγ1 : f.exponent γ = 1) (hδ2 : f.exponent δ = 2) :
    (f.exponent (f.indexEquiv α) = 2 ∧ (f.exponent (f.indexEquiv α)).toNat = 2) ∧
      (f.exponent (f.indexEquiv β) = 1 ∧ (f.exponent (f.indexEquiv β)).toNat = 1) ∧
      (f.exponent (f.indexEquiv γ) = 2 ∧ (f.exponent (f.indexEquiv γ)).toNat = 2) ∧
      (f.exponent (f.indexEquiv δ) = 1 ∧ (f.exponent (f.indexEquiv δ)).toNat = 1) ∧
      (t.simplyConnectedRootDatum ht).root (f.indexEquiv δ) =
        (t.simplyConnectedRootDatum ht).root (f.indexEquiv α) +
          (t.simplyConnectedRootDatum ht).root (f.indexEquiv β) ∧
      (t.simplyConnectedRootDatum ht).root (f.indexEquiv γ) =
        (t.simplyConnectedRootDatum ht).root (f.indexEquiv α) +
          2 • (t.simplyConnectedRootDatum ht).root (f.indexEquiv β) := by
  have hα' : f.exponent (f.indexEquiv α) = 2 ∧ (f.exponent (f.indexEquiv α)).toNat = 2 := by
    rcases exponent_indexEquiv_cases f hf hexp α with ⟨_, h1, h2⟩ | ⟨h1, _⟩
    · exact ⟨h1, h2⟩
    · omega
  have hβ' : f.exponent (f.indexEquiv β) = 1 ∧ (f.exponent (f.indexEquiv β)).toNat = 1 := by
    rcases exponent_indexEquiv_cases f hf hexp β with ⟨h1, _⟩ | ⟨_, h1, h2⟩
    · omega
    · exact ⟨h1, h2⟩
  have hγ' : f.exponent (f.indexEquiv γ) = 2 ∧ (f.exponent (f.indexEquiv γ)).toNat = 2 := by
    rcases exponent_indexEquiv_cases f hf hexp γ with ⟨_, h1, h2⟩ | ⟨h1, _⟩
    · exact ⟨h1, h2⟩
    · omega
  have hδ' : f.exponent (f.indexEquiv δ) = 1 ∧ (f.exponent (f.indexEquiv δ)).toNat = 1 := by
    rcases exponent_indexEquiv_cases f hf hexp δ with ⟨h1, _⟩ | ⟨_, h1, h2⟩
    · omega
    · exact ⟨h1, h2⟩
  refine ⟨hα', hβ', hγ', hδ', ?_, ?_⟩
  · apply smul_right_injective _ (by norm_num : (2 : ℤ) ≠ 0)
    have hw := congrArg f.weightMap hδ
    rw [map_add, map_nsmul, f.root_weightMap, f.root_weightMap, f.root_weightMap,
      hδ2, hα1, hβ2] at hw
    simp only [Int.cast_id, one_smul] at hw
    dsimp; rw [hw]; module
  · have hw := congrArg f.weightMap hγ
    rw [map_add, f.root_weightMap, f.root_weightMap, f.root_weightMap, hγ1, hα1, hβ2] at hw
    simp only [Int.cast_id, one_smul] at hw
    rw [hw]; module

private theorem commutatorElement_doublyLaced_of_two_nsmul_add {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (A : Type v) [CommRing A] [ExpChar A 2] (u v : A) :
    ⁅D.rootSubgroupPoints (f.indexEquiv α) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)),
      D.rootSubgroupPoints (f.indexEquiv β) A
        (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat))⁆ =
      D.rootSubgroupPoints (f.indexEquiv γ) A
          (ofAdd (((t.structureConstant ht α β : A) * (u * v)) ^
            (f.exponent (f.indexEquiv γ)).toNat)) *
        D.rootSubgroupPoints (f.indexEquiv δ) A
          (ofAdd ((((t.structureConstant ht α β * t.structureConstant ht α γ / 2 : ℤ) : A) *
            (u ^ 2 * v)) ^ (f.exponent (f.indexEquiv δ)).toNat)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : CharP A 2 := (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
  have hbound := abs_pairing_le_two_of_sym f hexp hsym
  have hδ'z : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root β +
        (2 : ℤ) • (t.simplyConnectedRootDatum ht).root α := by
    rw [hδ]; module
  obtain ⟨hα1, hβ2⟩ := short_long_of_two_nsmul_add f hexp hsym hγ hδ
  obtain ⟨_, _, hδ2⟩ := (t.simplyConnectedRootDatum ht).pairings_of_long_add_two_short
    f.exponent hsym α β δ hα1 hβ2 (hexp δ) hδ'z
  obtain ⟨γ₀, hγ₀, hγ1, hbot₁, _, hbot₂, _⟩ :=
    (t.simplyConnectedRootDatum ht).exists_short_midpoint_of_long_add_two_short
      f.exponent hsym α β δ hα1 hβ2 (hexp δ) hδ'z
  rw [(t.simplyConnectedRootDatum ht).root.injective
    (hγ₀.trans (hγ.trans (add_comm _ _)).symm)] at hγ1 hbot₂
  obtain ⟨hα', hβ', hγ', hδ', hδ'eq, hγ'eq⟩ :=
    partner_roots_of_two_nsmul_add f hf hexp hγ hδ hα1 hβ2 hγ1 hδ2
  set α' := f.indexEquiv α; set β' := f.indexEquiv β
  set γ' := f.indexEquiv γ; set δ' := f.indexEquiv δ
  have hγ'z : (t.simplyConnectedRootDatum ht).root γ' =
      (t.simplyConnectedRootDatum ht).root α' +
        (2 : ℤ) • (t.simplyConnectedRootDatum ht).root β' :=
    by rw [hγ'eq]; module
  obtain ⟨hpα'β', _, _⟩ := (t.simplyConnectedRootDatum ht).pairings_of_long_add_two_short
    f.exponent hsym β' α' γ' hβ'.1 hα'.1 (hexp γ') hγ'z
  obtain ⟨δ₀, hδ₀, _, hbot'₁, _, hbot'₂, _⟩ :=
    (t.simplyConnectedRootDatum ht).exists_short_midpoint_of_long_add_two_short
      f.exponent hsym β' α' γ' hβ'.1 hα'.1 (hexp γ') hγ'z
  rw [(t.simplyConnectedRootDatum ht).root.injective (hδ₀.trans hδ'eq.symm)] at hbot'₂
  have h2α' : 2 • (t.simplyConnectedRootDatum ht).root α' +
      (t.simplyConnectedRootDatum ht).root β' ∉
        Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ =>
    absurd ((t.simplyConnectedRootDatum ht)
      |>.n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
      f.exponent hsym α' β' ρ 2 (hbound α' β') hα'.1 hβ'.1 (hexp ρ) (by omega)
      (by rw [hρ]; module)).1 (by decide)
  have h3β' : (t.simplyConnectedRootDatum ht).root α' +
      3 • (t.simplyConnectedRootDatum ht).root β' ∉
        Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ => by
    have hρlen := (t.simplyConnectedRootDatum ht).length_of_root_eq_add_zsmul f.exponent hsym
      β' α' ρ 3 (by rw [hρ]; module)
    rcases hexp ρ with h1 | h1 <;> rw [hα'.1, hβ'.1, hpα'β', h1] at hρlen <;> omega
  have h2 : (2 : A) = 0 := CharP.cast_eq_zero A 2
  have hc2' : ((-(t.structureConstant ht β' α' * t.structureConstant ht β' δ' / 2) : ℤ) : A) = 1 :=
    by rw [Int.cast_neg, cast_div_two_eq_one ⟨δ', hδ'eq.trans (add_comm _ _)⟩
         ⟨γ', by rw [hγ'eq, hδ'eq]; module⟩ hbot'₁ hbot'₂ A]; linear_combination -h2
  rw [hα'.2, hβ'.2, hγ'.2, hδ'.2,
    D.commutatorElement_rootSubgroup_of_root_eq_add_two_nsmul hδ'eq hγ'eq h2α' h3β',
    cast_structureConstant_eq_one ⟨γ, hγ⟩ hbot₁ A,
    cast_div_two_eq_one ⟨γ, hγ⟩ ⟨δ, by rw [hδ, hγ]; module⟩ hbot₁ hbot₂ A,
    cast_structureConstant_eq_one ⟨δ', hδ'eq⟩
      ((t.simplyConnectedRootDatum ht).chainBotCoeff_eq_zero_comm.mp hbot'₁) A, hc2']
  simp only [one_mul, pow_one, mul_pow]
  exact (commute_short_add_long_with_two_short_add_long D f hexp hsym hβ'.1 hδ'.1 hγ'.1
    (by rw [hγ'eq, hδ'eq]; module) A _ _).eq

private theorem commute_long_with_add_two_nsmul_factors {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β)
    (A : Type v) [CommRing A] [ExpChar A 2] (s w₁ w₂ : A) :
    Commute
      (D.rootSubgroupPoints (f.indexEquiv α) A (ofAdd (s ^ (f.exponent (f.indexEquiv α)).toNat)))
      (D.rootSubgroupPoints (f.indexEquiv γ) A
          (ofAdd (w₁ ^ (f.exponent (f.indexEquiv γ)).toNat)) *
        D.rootSubgroupPoints (f.indexEquiv δ) A
          (ofAdd (w₂ ^ (f.exponent (f.indexEquiv δ)).toNat))) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have hbound := abs_pairing_le_two_of_sym f hexp hsym
  obtain ⟨hβ1, hα2⟩ := short_long_of_two_nsmul_add f hexp hsym
    (hγ.trans (add_comm _ _)) (hδ.trans (add_comm _ _))
  have h2α : 2 • (t.simplyConnectedRootDatum ht).root α +
      (t.simplyConnectedRootDatum ht).root β ∉
        Set.range (t.simplyConnectedRootDatum ht).root := fun ⟨ρ, hρ⟩ =>
    absurd ((t.simplyConnectedRootDatum ht)
      |>.n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
      f.exponent hsym α β ρ 2 (hbound α β) hα2 hβ1 (hexp ρ) (by omega)
      (by rw [hρ]; module)).1 (by decide)
  have hind := LinearIndependent.pair_iff.mp
    ((t.simplyConnectedRootDatum ht).linearIndependent_of_add_mem_range_root'
      (i := α) (j := β) ⟨γ, hγ⟩)
  refine Commute.mul_right ?_ ?_
  · have hsum : (t.simplyConnectedRootDatum ht).root α +
        (t.simplyConnectedRootDatum ht).root γ =
          2 • (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β := by
      rw [hγ]; module
    refine commute_doublyLaced D f hf hexp hsym (by rwa [hsum]) (fun hz => ?_) A s w₁
    have := (hind 2 1 (by rw [hsum] at hz; linear_combination hz)).1
    norm_num at this
  · have hsum : (t.simplyConnectedRootDatum ht).root α +
        (t.simplyConnectedRootDatum ht).root δ = 2 • (t.simplyConnectedRootDatum ht).root γ := by
      rw [hδ, hγ]; module
    refine commute_doublyLaced D f hf hexp hsym
      (by rw [hsum]; exact (t.simplyConnectedRootDatum ht).nsmul_notMem_range_root)
      (fun hz => ?_) A s w₂
    have := (hind 2 2 (by rw [hsum, hγ] at hz; linear_combination hz)).1
    norm_num at this

private theorem commutatorElement_doublyLaced_of_add_two_nsmul {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hf : f * f = RootPairingIsogeny.smulId (t.simplyConnectedRootDatum ht) 2)
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (hsym : ∀ α β, f.exponent α * (t.simplyConnectedRootDatum ht).pairing β α =
      f.exponent β * (t.simplyConnectedRootDatum ht).pairing α β)
    {α β γ δ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + 2 • (t.simplyConnectedRootDatum ht).root β)
    (A : Type v) [CommRing A] [ExpChar A 2] (u v : A) :
    ⁅D.rootSubgroupPoints (f.indexEquiv α) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)),
      D.rootSubgroupPoints (f.indexEquiv β) A
        (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat))⁆ =
      D.rootSubgroupPoints (f.indexEquiv γ) A
          (ofAdd (((t.structureConstant ht α β : A) * (u * v)) ^
            (f.exponent (f.indexEquiv γ)).toNat)) *
        D.rootSubgroupPoints (f.indexEquiv δ) A
          (ofAdd ((((-(t.structureConstant ht β α * t.structureConstant ht β γ / 2) : ℤ) : A) *
            (u * v ^ 2)) ^ (f.exponent (f.indexEquiv δ)).toNat)) := by
  have : CharP A 2 := (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
  have hneg (s : A) (q : ℕ) (hq : q = 1 ∨ q = 2) : (-s) ^ q = -(s ^ q) := by
    have h2 : (2 : A) = 0 := CharP.cast_eq_zero A 2
    rcases hq with rfl | rfl
    · simp
    · linear_combination s ^ 2 * h2
  have hq (ξ : Fin t.numRoots) :
      (f.exponent (f.indexEquiv ξ)).toNat = 1 ∨ (f.exponent (f.indexEquiv ξ)).toNat = 2 := by
    rcases hexp (f.indexEquiv ξ) with h | h <;> simp [h]
  have hconj :
      ⁅D.rootSubgroupPoints (f.indexEquiv α) A
          (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)),
        D.rootSubgroupPoints (f.indexEquiv β) A
          (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat))⁆ =
      D.rootSubgroupPoints (f.indexEquiv α) A
          (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)) *
        ⁅D.rootSubgroupPoints (f.indexEquiv β) A
            (ofAdd (v ^ (f.exponent (f.indexEquiv β)).toNat)),
          D.rootSubgroupPoints (f.indexEquiv α) A
            (ofAdd ((-u) ^ (f.exponent (f.indexEquiv α)).toNat))⁆ *
        (D.rootSubgroupPoints (f.indexEquiv α) A
          (ofAdd (u ^ (f.exponent (f.indexEquiv α)).toNat)))⁻¹ := by
    rw [hneg u _ (hq α), ofAdd_neg, map_inv]
    simp only [commutatorElement_def, inv_inv]
    group
  have hc : (t.structureConstant ht β α : A) * (v * -u) =
      (t.structureConstant ht α β : A) * (u * v) := by
    rw [structureConstant_skew (ht := ht) α β, Int.cast_neg]; ring
  have hd : ((t.structureConstant ht β α * t.structureConstant ht β γ / 2 : ℤ) : A) * (v ^ 2 * -u) =
      ((-(t.structureConstant ht β α * t.structureConstant ht β γ / 2) : ℤ) : A) * (u * v ^ 2) := by
    push_cast; ring
  rw [hconj, commutatorElement_doublyLaced_of_two_nsmul_add D f hf hexp hsym
    (hγ.trans (add_comm _ _)) (hδ.trans (add_comm _ _)) A v (-u),
    (commute_long_with_add_two_nsmul_factors D f hf hexp hsym hγ hδ A u _ _).eq,
    mul_inv_cancel_right, hc, hd]

private theorem map_rootSubgroupPoints_doublyLaced {t : DynkinType} {ht : t.Valid}
    (D : ChevalleyDatum t ht) (E : ChevalleyDatum t ht)
    (f : RootPairingIsogeny (t.simplyConnectedRootDatum ht) (t.simplyConnectedRootDatum ht))
    (hexp : ∀ α, f.exponent α = 1 ∨ f.exponent α = 2)
    (σ : Equiv.Perm (Fin t.rank))
    (hσ : ∀ i, f.indexEquiv (t.simpleIndex ht i) = t.simpleIndex ht (σ i))
    (A : Type v) [CommRing A] [ExpChar A 2]
    (φ : D.points A →* E.points A)
    (hpos : ∀ i (u : A), φ (D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd u)) =
      E.rootSubgroupPoints (f.indexEquiv (t.simpleIndex ht i)) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv (t.simpleIndex ht i))).toNat)))
    (hneg : ∀ i (u : A), φ (D.rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) A (ofAdd u)) =
      E.rootSubgroupPoints (f.indexEquiv
        ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i))) A
        (ofAdd (u ^ (f.exponent (f.indexEquiv
          ((t.simplyConnectedRootDatum ht).reflectionPerm
            (t.simpleIndex ht i) (t.simpleIndex ht i)))).toNat)))
    (α : Fin t.numRoots) (u : Multiplicative A) :
    φ (D.rootSubgroupPoints α A u) =
      E.rootSubgroupPoints (f.indexEquiv α) A
        (ofAdd (toAdd u ^ (f.exponent (f.indexEquiv α)).toNat)) := by
  have := t.isReduced_simplyConnectedRootDatum ht
  have : CharP A 2 := (expChar_prime_iff (R := A) Nat.prime_two).mp ‹_›
  have h2 : (2 : A) = 0 := CharP.cast_eq_zero A 2
  have hneg_one_pow (ξ : Fin t.numRoots) : (-1 : A) ^ (f.exponent ξ).toNat = -1 := by
    rcases hexp ξ with h | h <;> simp [h]
    linear_combination h2
  have hweyl (i : Fin t.rank) :
      φ (D.weylElement (t.simpleIndex ht i) A 1) = E.weylElement (t.simpleIndex ht (σ i)) A 1 := by
    rw [D.weylElement_def, map_mul, map_mul, Units.val_one, inv_one, Units.val_one,
      hpos, hneg, f.indexEquiv_reflectionPerm, f.exponent_reflectionPerm, hσ, E.weylElement_def,
      Units.val_one, inv_one, Units.val_one, one_pow, hneg_one_pow]
  refine (t.rationalBase ht).induction_simple_reflect α
    (p := fun γ => ∀ w : A, φ (D.rootSubgroupPoints γ A (ofAdd w)) =
      E.rootSubgroupPoints (f.indexEquiv γ) A
        (ofAdd (w ^ (f.exponent (f.indexEquiv γ)).toNat)))
    (fun γ hγ w => ?_) (fun γ j ih hj w => ?_) (toAdd u)
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hγ
    exact hpos i w
  · obtain ⟨i, rfl⟩ := exists_simpleIndex_eq_of_mem_support hj
    rw [reflectionPerm_rationalRootSystem]
    have hconjD := D.weylElement_conj_rootSubgroupPoints i γ A w
    rw [intUnits_cast_eq_one, one_mul] at hconjD
    have hconjE := E.weylElement_conj_rootSubgroupPoints (σ i) (f.indexEquiv γ) A
      (w ^ (f.exponent (f.indexEquiv γ)).toNat)
    rw [intUnits_cast_eq_one, one_mul] at hconjE
    rw [← hconjD, map_mul, map_mul, map_inv, hweyl, ih, hconjE, ← hσ,
      f.indexEquiv_reflectionPerm, f.exponent_reflectionPerm]

end DoublyLacedAux

/-! ## Type `B₂` in characteristic two -/

section B2

variable {ht : (B 2).Valid} (D E : ChevalleyDatum (B 2) ht)
variable (A : Type v) [CommRing A] [ExpChar A 2]

private theorem b2_sym (α β : Fin (B 2).numRoots) :
    (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny).exponent α *
        ((B 2).simplyConnectedRootDatum ht).pairing β α =
      (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny).exponent β *
        ((B 2).simplyConnectedRootDatum ht).pairing α β := by
  have h : ∀ i j : Fin (2 * 2 ^ 2),
      b2SpecialIsogeny.exponent i * (typeBSimplyConnectedRootDatum 2).pairing j i =
        b2SpecialIsogeny.exponent j * (typeBSimplyConnectedRootDatum 2).pairing i j := by
    intro i j
    obtain ⟨a, rfl⟩ := b2Index_bijective.surjective i
    obtain ⟨b, rfl⟩ := b2Index_bijective.surjective j
    rw [b2SpecialIsogeny_exponent, b2SpecialIsogeny_exponent,
      b2SpecialIsogenyExponent_b2Index, b2SpecialIsogenyExponent_b2Index,
      ← RootPairing.root_coroot_eq_pairing, ← RootPairing.root_coroot_eq_pairing,
      toLinearMap_typeBSimplyConnectedRootDatum, toLinearMap_typeBSimplyConnectedRootDatum,
      root_b2Index, root_b2Index, coroot_b2Index, coroot_b2Index]
    revert a b; decide
  -- Unfold `(congrIso ...).exponent` to `b2SpecialIsogeny.exponent` before rewriting the datum.
  change b2SpecialIsogeny.exponent α * ((B 2).simplyConnectedRootDatum ht).pairing β α =
    b2SpecialIsogeny.exponent β * ((B 2).simplyConnectedRootDatum ht).pairing α β
  rw [simplyConnectedRootDatum_B 2 ht]
  exact h α β

private theorem b2_exp (α : Fin (B 2).numRoots) :
    (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny).exponent α = 1 ∨
      (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny).exponent α = 2 := by
  have h : ∀ i : Fin (2 * 2 ^ 2), b2SpecialIsogeny.exponent i = 1 ∨
      b2SpecialIsogeny.exponent i = 2 := fun i => by
    rw [b2SpecialIsogeny_exponent]
    exact b2SpecialIsogenyExponent_eq_one_or_eq_two i
  exact h α

/-- **Commuting root subgroups under the `B₂` exceptional isogeny.** -/
theorem commute_b2SpecialIsogenyRootSubgroup {α β : Fin (B 2).numRoots}
    (h : ((B 2).simplyConnectedRootDatum ht).root α +
        ((B 2).simplyConnectedRootDatum ht).root β ∉
      Set.range ((B 2).simplyConnectedRootDatum ht).root)
    (h0 : ((B 2).simplyConnectedRootDatum ht).root α +
        ((B 2).simplyConnectedRootDatum ht).root β ≠ 0)
    (u v : A) :
    Commute (D.b2SpecialIsogenyRootSubgroup A α (ofAdd u))
      (D.b2SpecialIsogenyRootSubgroup A β (ofAdd v)) := by
  rw [b2SpecialIsogenyRootSubgroup_ofAdd, b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commute_doublyLaced D (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny b2SpecialIsogeny_mul_self)
    b2_exp b2_sym h h0 A u v

/-- **One-factor Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_add
    {α β γ : Fin (B 2).numRoots}
    (hγ : ((B 2).simplyConnectedRootDatum ht).root γ =
      ((B 2).simplyConnectedRootDatum ht).root α + ((B 2).simplyConnectedRootDatum ht).root β)
    (hα : 2 • ((B 2).simplyConnectedRootDatum ht).root α +
        ((B 2).simplyConnectedRootDatum ht).root β ∉
      Set.range ((B 2).simplyConnectedRootDatum ht).root)
    (hβ : ((B 2).simplyConnectedRootDatum ht).root α +
        2 • ((B 2).simplyConnectedRootDatum ht).root β ∉
      Set.range ((B 2).simplyConnectedRootDatum ht).root)
    (u v : A) :
    ⁅D.b2SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.b2SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.b2SpecialIsogenyRootSubgroup A γ
        (ofAdd (((B 2).structureConstant ht α β : A) * (u * v))) := by
  simp only [b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_root_eq_add D
    (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny b2SpecialIsogeny_mul_self)
    b2_exp b2_sym hγ hα hβ A u v

/-- **Two-factor short-first Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_two_nsmul_add
    {α β γ δ : Fin (B 2).numRoots}
    (hγ : ((B 2).simplyConnectedRootDatum ht).root γ =
      ((B 2).simplyConnectedRootDatum ht).root α + ((B 2).simplyConnectedRootDatum ht).root β)
    (hδ : ((B 2).simplyConnectedRootDatum ht).root δ =
      2 • ((B 2).simplyConnectedRootDatum ht).root α + ((B 2).simplyConnectedRootDatum ht).root β)
    (u v : A) :
    ⁅D.b2SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.b2SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.b2SpecialIsogenyRootSubgroup A γ
          (ofAdd (((B 2).structureConstant ht α β : A) * (u * v))) *
        D.b2SpecialIsogenyRootSubgroup A δ
          (ofAdd (((((B 2).structureConstant ht α β *
            (B 2).structureConstant ht α γ / 2 : ℤ) : A) * (u ^ 2 * v)))) := by
  simp only [b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_two_nsmul_add D
    (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny b2SpecialIsogeny_mul_self)
    b2_exp b2_sym hγ hδ A u v

/-- **Two-factor long-first Chevalley commutator relation under the `B₂` exceptional isogeny.** -/
theorem commutatorElement_b2SpecialIsogenyRootSubgroup_of_root_eq_add_two_nsmul
    {α β γ δ : Fin (B 2).numRoots}
    (hγ : ((B 2).simplyConnectedRootDatum ht).root γ =
      ((B 2).simplyConnectedRootDatum ht).root α + ((B 2).simplyConnectedRootDatum ht).root β)
    (hδ : ((B 2).simplyConnectedRootDatum ht).root δ =
      ((B 2).simplyConnectedRootDatum ht).root α + 2 • ((B 2).simplyConnectedRootDatum ht).root β)
    (u v : A) :
    ⁅D.b2SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.b2SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.b2SpecialIsogenyRootSubgroup A γ
          (ofAdd (((B 2).structureConstant ht α β : A) * (u * v))) *
        D.b2SpecialIsogenyRootSubgroup A δ
          (ofAdd ((((-((B 2).structureConstant ht β α *
            (B 2).structureConstant ht β γ / 2) : ℤ) : A) * (u * v ^ 2)))) := by
  simp only [b2SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_add_two_nsmul D
    (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny b2SpecialIsogeny_mul_self)
    b2_exp b2_sym hγ hδ A u v

/-- **Simple-root determination for the `B₂` exceptional isogeny.** Any group homomorphism between
points of type `B₂` Chevalley data over `[ExpChar A 2]` matching `b2SpecialIsogenyRootSubgroup` on
the positive and negative simple roots matches it on every root. -/
theorem map_rootSubgroupPoints_of_b2SpecialIsogeny_simple
    (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints ((B 2).simpleIndex ht i) A u) =
      E.b2SpecialIsogenyRootSubgroup A ((B 2).simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        (((B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) A u) =
      E.b2SpecialIsogenyRootSubgroup A
        (((B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) u)
    (α : Fin (B 2).numRoots) (u : Multiplicative A) :
    φ (D.rootSubgroupPoints α A u) = E.b2SpecialIsogenyRootSubgroup A α u := by
  rw [← ofAdd_toAdd u, b2SpecialIsogenyRootSubgroup_ofAdd, ofAdd_toAdd]
  exact map_rootSubgroupPoints_doublyLaced D E
    (congrIso (simplyConnectedRootDatum_B 2 ht) b2SpecialIsogeny) b2_exp lengthPermRankTwo
    (fun i => (congrArg (⇑b2SpecialIsogeny.indexEquiv) (simpleIndex_B 2 ht i)).trans
      (((b2SpecialIsogeny_indexEquiv_apply _).trans
          (b2SpecialIsogenyIndexEquiv_typeBSimpleIndex i)).trans
        (simpleIndex_B 2 ht (lengthPermRankTwo i)).symm))
    A φ (fun i w => (hpos i (ofAdd w)).trans (E.b2SpecialIsogenyRootSubgroup_ofAdd A _ w))
    (fun i w => (hneg i (ofAdd w)).trans (E.b2SpecialIsogenyRootSubgroup_ofAdd A _ w)) α u

/-- Any endomorphism of `D.points A` matching `b2SpecialIsogenyRootSubgroup` on the signed simple
roots squares to `D.frobenius 2 1 A` on `D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_b2SpecialIsogeny_simple
    (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints ((B 2).simpleIndex ht i) A u) =
      D.b2SpecialIsogenyRootSubgroup A ((B 2).simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        (((B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) A u) =
      D.b2SpecialIsogenyRootSubgroup A
        (((B 2).simplyConnectedRootDatum ht).reflectionPerm
          ((B 2).simpleIndex ht i) ((B 2).simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) :
    φ (φ g) = D.frobenius 2 1 A g := by
  have hall := map_rootSubgroupPoints_of_b2SpecialIsogeny_simple D D A φ hpos hneg
  refine (D.elementarySubgroup_le_iff A ((φ.comp φ).eqLocus (D.frobenius 2 1 A))).mpr
    (fun α u => ?_) hg
  -- Membership in `MonoidHom.eqLocus` unfolds to pointwise equality of the two homomorphisms.
  change φ (φ (D.rootSubgroupPoints α A u)) = D.frobenius 2 1 A (D.rootSubgroupPoints α A u)
  rw [← ofAdd_toAdd u, hall, b2SpecialIsogenyRootSubgroup_ofAdd,
    hall (b2SpecialIsogeny.indexEquiv α), b2SpecialIsogenyRootSubgroup_comp_self]

end B2

/-! ## Type `F₄` in characteristic two -/

section F4

variable {ht : F4.Valid} (D E : ChevalleyDatum F4 ht)
variable (A : Type v) [CommRing A] [ExpChar A 2]

private theorem f4_sym (α β : Fin F4.numRoots) :
    (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny).exponent α *
        (F4.simplyConnectedRootDatum ht).pairing β α =
      (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny).exponent β *
        (F4.simplyConnectedRootDatum ht).pairing α β := by
  have h : ∀ i j : Fin 48,
      f4SpecialIsogeny.exponent i * f4SimplyConnectedRootDatum.pairing j i =
        f4SpecialIsogeny.exponent j * f4SimplyConnectedRootDatum.pairing i j := fun i j => by
    rw [f4SpecialIsogeny_exponent, f4SpecialIsogeny_exponent]
    exact f4Length_mul_pairing_comm i j
  -- Unfold `(congrIso ...).exponent` to `f4SpecialIsogeny.exponent` before rewriting the datum.
  change f4SpecialIsogeny.exponent α * (F4.simplyConnectedRootDatum ht).pairing β α =
    f4SpecialIsogeny.exponent β * (F4.simplyConnectedRootDatum ht).pairing α β
  rw [simplyConnectedRootDatum_F4 ht]
  exact h α β

private theorem f4_exp (α : Fin F4.numRoots) :
    (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny).exponent α = 1 ∨
      (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny).exponent α = 2 := by
  have h : ∀ i : Fin 48, f4SpecialIsogeny.exponent i = 1 ∨
      f4SpecialIsogeny.exponent i = 2 := fun i => by
    rw [f4SpecialIsogeny_exponent]
    exact f4Length_eq_one_or_eq_two i
  exact h α

/-- **Commuting root subgroups under the `F₄` exceptional isogeny.** -/
theorem commute_f4SpecialIsogenyRootSubgroup {α β : Fin F4.numRoots}
    (h : (F4.simplyConnectedRootDatum ht).root α + (F4.simplyConnectedRootDatum ht).root β ∉
      Set.range (F4.simplyConnectedRootDatum ht).root)
    (h0 : (F4.simplyConnectedRootDatum ht).root α + (F4.simplyConnectedRootDatum ht).root β ≠ 0)
    (u v : A) :
    Commute (D.f4SpecialIsogenyRootSubgroup A α (ofAdd u))
      (D.f4SpecialIsogenyRootSubgroup A β (ofAdd v)) := by
  rw [f4SpecialIsogenyRootSubgroup_ofAdd, f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commute_doublyLaced D (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny f4SpecialIsogeny_mul_self)
    f4_exp f4_sym h h0 A u v

/-- **One-factor Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_add
    {α β γ : Fin F4.numRoots}
    (hγ : (F4.simplyConnectedRootDatum ht).root γ =
      (F4.simplyConnectedRootDatum ht).root α + (F4.simplyConnectedRootDatum ht).root β)
    (hα : 2 • (F4.simplyConnectedRootDatum ht).root α + (F4.simplyConnectedRootDatum ht).root β ∉
      Set.range (F4.simplyConnectedRootDatum ht).root)
    (hβ : (F4.simplyConnectedRootDatum ht).root α + 2 • (F4.simplyConnectedRootDatum ht).root β ∉
      Set.range (F4.simplyConnectedRootDatum ht).root)
    (u v : A) :
    ⁅D.f4SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.f4SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.f4SpecialIsogenyRootSubgroup A γ
        (ofAdd ((F4.structureConstant ht α β : A) * (u * v))) := by
  simp only [f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_root_eq_add D
    (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny f4SpecialIsogeny_mul_self)
    f4_exp f4_sym hγ hα hβ A u v

/-- **Two-factor short-first Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_two_nsmul_add
    {α β γ δ : Fin F4.numRoots}
    (hγ : (F4.simplyConnectedRootDatum ht).root γ =
      (F4.simplyConnectedRootDatum ht).root α + (F4.simplyConnectedRootDatum ht).root β)
    (hδ : (F4.simplyConnectedRootDatum ht).root δ =
      2 • (F4.simplyConnectedRootDatum ht).root α + (F4.simplyConnectedRootDatum ht).root β)
    (u v : A) :
    ⁅D.f4SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.f4SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.f4SpecialIsogenyRootSubgroup A γ
          (ofAdd ((F4.structureConstant ht α β : A) * (u * v))) *
        D.f4SpecialIsogenyRootSubgroup A δ
          (ofAdd ((((F4.structureConstant ht α β *
            F4.structureConstant ht α γ / 2 : ℤ) : A) * (u ^ 2 * v)))) := by
  simp only [f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_two_nsmul_add D
    (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny f4SpecialIsogeny_mul_self)
    f4_exp f4_sym hγ hδ A u v

/-- **Two-factor long-first Chevalley commutator relation under the `F₄` exceptional isogeny.** -/
theorem commutatorElement_f4SpecialIsogenyRootSubgroup_of_root_eq_add_two_nsmul
    {α β γ δ : Fin F4.numRoots}
    (hγ : (F4.simplyConnectedRootDatum ht).root γ =
      (F4.simplyConnectedRootDatum ht).root α + (F4.simplyConnectedRootDatum ht).root β)
    (hδ : (F4.simplyConnectedRootDatum ht).root δ =
      (F4.simplyConnectedRootDatum ht).root α + 2 • (F4.simplyConnectedRootDatum ht).root β)
    (u v : A) :
    ⁅D.f4SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.f4SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.f4SpecialIsogenyRootSubgroup A γ
          (ofAdd ((F4.structureConstant ht α β : A) * (u * v))) *
        D.f4SpecialIsogenyRootSubgroup A δ
          (ofAdd ((((-(F4.structureConstant ht β α *
            F4.structureConstant ht β γ / 2) : ℤ) : A) * (u * v ^ 2)))) := by
  simp only [f4SpecialIsogenyRootSubgroup_ofAdd]
  exact commutatorElement_doublyLaced_of_add_two_nsmul D
    (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny)
    (congrIso_mul_self (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny f4SpecialIsogeny_mul_self)
    f4_exp f4_sym hγ hδ A u v

/-- **Simple-root determination for the `F₄` exceptional isogeny.** Any group homomorphism between
points of type `F₄` Chevalley data over `[ExpChar A 2]` matching `f4SpecialIsogenyRootSubgroup` on
the positive and negative simple roots matches it on every root. -/
theorem map_rootSubgroupPoints_of_f4SpecialIsogeny_simple
    (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (F4.simpleIndex ht i) A u) =
      E.f4SpecialIsogenyRootSubgroup A (F4.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((F4.simplyConnectedRootDatum ht).reflectionPerm
          (F4.simpleIndex ht i) (F4.simpleIndex ht i)) A u) =
      E.f4SpecialIsogenyRootSubgroup A
        ((F4.simplyConnectedRootDatum ht).reflectionPerm
          (F4.simpleIndex ht i) (F4.simpleIndex ht i)) u)
    (α : Fin F4.numRoots) (u : Multiplicative A) :
    φ (D.rootSubgroupPoints α A u) = E.f4SpecialIsogenyRootSubgroup A α u := by
  rw [← ofAdd_toAdd u, f4SpecialIsogenyRootSubgroup_ofAdd, ofAdd_toAdd]
  exact map_rootSubgroupPoints_doublyLaced D E
    (congrIso (simplyConnectedRootDatum_F4 ht) f4SpecialIsogeny) f4_exp lengthPermF4
    (fun i => (congrArg (⇑f4SpecialIsogeny.indexEquiv) (simpleIndex_F4 ht i)).trans
      (((f4SpecialIsogeny_indexEquiv_apply _).trans (f4SpecialIsogenyIndex_castAdd i)).trans
        (simpleIndex_F4 ht (lengthPermF4 i)).symm))
    A φ (fun i w => (hpos i (ofAdd w)).trans (E.f4SpecialIsogenyRootSubgroup_ofAdd A _ w))
    (fun i w => (hneg i (ofAdd w)).trans (E.f4SpecialIsogenyRootSubgroup_ofAdd A _ w)) α u

/-- Any endomorphism of `D.points A` matching `f4SpecialIsogenyRootSubgroup` on the signed simple
roots squares to `D.frobenius 2 1 A` on `D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_f4SpecialIsogeny_simple
    (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (F4.simpleIndex ht i) A u) =
      D.f4SpecialIsogenyRootSubgroup A (F4.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((F4.simplyConnectedRootDatum ht).reflectionPerm
          (F4.simpleIndex ht i) (F4.simpleIndex ht i)) A u) =
      D.f4SpecialIsogenyRootSubgroup A
        ((F4.simplyConnectedRootDatum ht).reflectionPerm
          (F4.simpleIndex ht i) (F4.simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) :
    φ (φ g) = D.frobenius 2 1 A g := by
  have hall := map_rootSubgroupPoints_of_f4SpecialIsogeny_simple D D A φ hpos hneg
  refine (D.elementarySubgroup_le_iff A ((φ.comp φ).eqLocus (D.frobenius 2 1 A))).mpr
    (fun α u => ?_) hg
  -- Membership in `MonoidHom.eqLocus` unfolds to pointwise equality of the two homomorphisms.
  change φ (φ (D.rootSubgroupPoints α A u)) = D.frobenius 2 1 A (D.rootSubgroupPoints α A u)
  rw [← ofAdd_toAdd u, hall, f4SpecialIsogenyRootSubgroup_ofAdd,
    hall (f4SpecialIsogeny.indexEquiv α), f4SpecialIsogenyRootSubgroup_comp_self]

end F4

end TauCeti.DynkinType.ChevalleyDatum

