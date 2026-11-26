/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.Basic
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Commutator.G2
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SpecialIsogeny.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant.G2

/-!
# Chevalley commutator relations and simple-root determination for the `G₂` exceptional isogeny

Over `[ExpChar A 3]`, `g2SpecialIsogenyRootSubgroup` satisfies all Chevalley commutator relations
of the pinned `G₂` Chevalley system. Any group homomorphism `D.points A →* E.points A` agreeing
with `g2SpecialIsogenyRootSubgroup` on the positive and negative simple root subgroups agrees with
it on all twelve root subgroups, and any endomorphism `D.points A →* D.points A` agreeing with it
on the positive and negative simple root subgroups squares to `D.frobenius 3 1 A` on
`D.elementarySubgroup A`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Lemma 53 and Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3–12.4.
-/

public section

open Multiplicative
open scoped commutatorElement

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

section G2

local notation "fI" => g2SpecialIsogenyIndex
local notation "fS" => g2SpecialIsogenySign
local notation "g2SC" => g2StructureConstant

private theorem charThreeOfExpChar (A : Type*) [CommRing A] [ExpChar A 3] : CharP A 3 :=
  (expChar_prime_iff (R := A) Nat.prime_three).mp ‹_›
attribute [local instance] charThreeOfExpChar
private abbrev g2ModThreeComm (i j : Fin 12) : Prop :=
  (g2Root i + g2Root j ∉ Set.range g2Root ∧ g2Root i + g2Root j ≠ 0) ∨
    ∃ k : Fin 12, g2Length k = 3 ∧ g2Root k = g2Root i + g2Root j ∧ (3 : ℤ) ∣ g2SC i j
private theorem g2_commute_partner_cases {α β : Fin 12}
    (h : g2Root α + g2Root β ∉ Set.range g2Root) (h0 : g2Root α + g2Root β ≠ 0) :
    g2ModThreeComm (fI α) (fI β) := by
  simp only [g2ModThreeComm, Set.mem_range, g2Root_apply, g2Length_apply,
    g2SpecialIsogenyIndex_def, g2StructureConstant_def] at *; decide +revert
private theorem g2_long_sum_partner_cases {α β γ : Fin 12} (hγ : g2Length γ = 3)
    (hadd : g2Root γ = g2Root α + g2Root β) :
    (g2Root (fI α) + g2Root (fI β) ∉ Set.range g2Root ∧ g2Root (fI α) + g2Root (fI β) ≠ 0 ∧
        (3 : ℤ) ∣ g2SC α β) ∨
      (g2Length (fI α) = 1 ∧ g2Length (fI β) = 1 ∧ g2Length (fI γ) = 1 ∧
        g2Root (fI γ) = g2Root (fI α) + g2Root (fI β) ∧
        (∃ l m : Fin 12, g2Root l = g2Root (fI α) + g2Root (fI γ) ∧
          g2Root m = g2Root (fI γ) + g2Root (fI β)) ∧
        (3 : ℤ) ∣ ((g2SC (fI α) (fI β) / 2) * 2 * (fS α : ℤ) * (fS β : ℤ) -
          (fS γ : ℤ) * g2SC α β)) := by
  simp only [Set.mem_range, g2Root_apply, g2Length_apply, g2SpecialIsogenyIndex_def,
    g2SpecialIsogenySign_def, g2StructureConstant_def] at *; decide +revert
private theorem g2_length_eq_three_of_no_two_nsmul {α β γ : Fin 12}
    (hγ : g2Root γ = g2Root α + g2Root β) (hα : 2 • g2Root α + g2Root β ∉ Set.range g2Root)
    (hβ : g2Root α + 2 • g2Root β ∉ Set.range g2Root) : g2Length γ = 3 := by
  simp only [Set.mem_range, g2Root_apply, g2Length_apply] at *; decide +revert
private theorem g2_short_pair_partner (i j k : Fin 12) (hi : g2Length i = 1) (hj : g2Length j = 1)
    (hk : g2Length k = 1) (hij : g2Root k = g2Root i + g2Root j) :
    g2Length (fI i) = 3 ∧ g2Length (fI j) = 3 ∧ g2Length (fI k) = 3 ∧
      g2Root (fI k) = g2Root (fI i) + g2Root (fI j) ∧
      (3 : ℤ) ∣ (g2SC (fI i) (fI j) * (fS i : ℤ) * (fS j : ℤ) -
        (fS k : ℤ) * (2 * (g2SC i j / 2)) ^ 3) := by
  revert i j k hi hj hk hij
  simp only [g2Root_apply, g2Length_apply, g2SpecialIsogenyIndex_def, g2SpecialIsogenySign_def,
    g2StructureConstant_def, funext_iff, Fin.forall_fin_two, Pi.add_apply]; decide
private def g2ShortLongTuples : List (Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :=
  [(0, 1, 2, 3, 4, 5), (0, 10, 9, 8, 7, 11), (2, 7, 0, 3, 5, 4), (2, 11, 9, 6, 1, 10),
   (3, 10, 6, 2, 5, 1), (3, 11, 8, 0, 4, 7), (6, 4, 3, 2, 1, 5), (6, 7, 8, 9, 10, 11),
   (8, 1, 6, 9, 11, 10), (8, 5, 3, 0, 7, 4), (9, 4, 0, 8, 11, 7), (9, 5, 2, 6, 10, 1)]
private theorem mem_g2ShortLongTuples {α β γ δ ε ζ : Fin 12}
    (hγ : g2Root γ = g2Root α + g2Root β) (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ) (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    (α, β, γ, δ, ε, ζ) ∈ g2ShortLongTuples := by
  have h1 : g2Root α + g2Root β ∈ Set.range g2Root := ⟨γ, hγ⟩
  have h2 : 2 • g2Root α + g2Root β ∈ Set.range g2Root := ⟨δ, by rw [hδ, hγ]; module⟩
  have h3 : 3 • g2Root α + g2Root β ∈ Set.range g2Root := ⟨ε, by rw [hε, hδ, hγ]; module⟩
  have h4 : 3 • g2Root α + 2 • g2Root β ∈ Set.range g2Root := ⟨ζ, by rw [hζ, hδ, hγ]; module⟩
  have hex : ∃ q ∈ g2ShortLongTuples, let (a, b, g, d, e, z) := q
      a = α ∧ b = β ∧ g2Root g = g2Root α + g2Root β ∧ g2Root d = g2Root α + g2Root g ∧
      g2Root e = g2Root α + g2Root d ∧ g2Root z = g2Root d + g2Root g := by
    clear hγ hδ hε hζ γ δ ε ζ
    simp only [g2ShortLongTuples, Set.mem_range, g2Root_apply] at h1 h2 h3 h4 ⊢; decide +revert
  obtain ⟨⟨_, _, _, _, _, _⟩, hmem, rfl, rfl, eγ, eδ, eε, eζ⟩ := hex
  obtain rfl := g2Root.injective (hγ.trans eγ.symm)
  obtain rfl := g2Root.injective (hδ.trans eδ.symm)
  obtain rfl := g2Root.injective (hε.trans eε.symm)
  exact g2Root.injective (hζ.trans eζ.symm) ▸ hmem
private theorem g2_short_long_partner : ∀ q ∈ g2ShortLongTuples,
    let (α, β, γ, δ, ε, ζ) := q; let fa := fI α; let fb := fI β; let fe := fI ε; let fz := fI ζ
    (g2Root fe = g2Root fb + g2Root fa ∧ g2Root fz = g2Root fb + g2Root fe ∧
        g2Root (fI γ) = g2Root fb + g2Root fz ∧ g2Root (fI δ) = g2Root fz + g2Root fe ∧
        (g2Length fa).toNat = 3 ∧ (g2Length fb).toNat = 1 ∧ (g2Length (fI γ)).toNat = 3 ∧
        (g2Length (fI δ)).toNat = 3 ∧ (g2Length fe).toNat = 1 ∧ (g2Length fz).toNat = 1) ∧
      (3 : ℤ) ∣ (-g2SC fb fa * (fS β : ℤ) * (fS α : ℤ) -
          (fS ε : ℤ) * (g2SC α β * (g2SC α γ / 2) * (g2SC α δ / 3))) ∧
      (3 : ℤ) ∣ (-(g2SC fb fa * (g2SC fb fe / 2)) * (fS β : ℤ) ^ 2 * (fS α : ℤ) -
          (fS ζ : ℤ) * (2 * (g2SC α β * (g2SC α γ / 2) * g2SC α β * (g2SC δ γ / 3)))) ∧
      (3 : ℤ) ∣ (-(g2SC fb fa * (g2SC fb fe / 2) * (g2SC fb fz / 3)) *
          (fS β : ℤ) ^ 3 * (fS α : ℤ) - (fS γ : ℤ) * g2SC α β ^ 3) ∧
      (3 : ℤ) ∣ ((g2SC fb fa * (g2SC fb fe / 2) * g2SC fb fa * (g2SC fz fe / 3)) *
          (fS β : ℤ) ^ 3 * (fS α : ℤ) ^ 2 - (fS δ : ℤ) * (g2SC α β * (g2SC α γ / 2)) ^ 3) := by
  simp only [g2ShortLongTuples, g2Root_apply, g2Length_apply, g2SpecialIsogenyIndex_def,
    g2SpecialIsogenySign_def, g2StructureConstant_def]; decide

private theorem g2_short_long_factors_comm : ∀ q ∈ g2ShortLongTuples,
    let (_, _, g, d, e, z) := q
    g2ModThreeComm g d ∧ g2ModThreeComm g e ∧ g2ModThreeComm g z ∧ g2ModThreeComm d e ∧
      g2ModThreeComm d z ∧ g2ModThreeComm e z ∧ g2ModThreeComm (fI e) (fI g) ∧
      g2ModThreeComm (fI e) (fI d) ∧ g2ModThreeComm (fI z) (fI g) ∧
      g2ModThreeComm (fI z) (fI d) := by
  dsimp only [g2ShortLongTuples]; simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [g2ModThreeComm, Set.mem_range, g2Root_apply, g2Length_apply,
      g2SpecialIsogenyIndex_def, g2StructureConstant_def, ne_eq, funext_iff, Fin.forall_fin_two,
      Pi.add_apply, Pi.zero_apply] <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private def g2HalfTuple (a b g d e z a' l m : Fin 12) (s : ℤ) : Prop :=
  s ^ 2 = 1 ∧ g2Length d = 1 ∧ g2Length a' = 1 ∧ g2Length g = 1 ∧ g2Length z = 3 ∧
    g2Root g = g2Root a + g2Root b ∧ g2Root d = g2Root a + g2Root g ∧
    g2Root e = g2Root a + g2Root d ∧ g2Root z = g2Root d + g2Root g ∧
    g2Root g = g2Root d + g2Root a' ∧ g2Root l = g2Root d + g2Root g ∧
    g2Root m = g2Root g + g2Root a' ∧ g2Root z = g2Root b + g2Root e ∧
    g2SC a b = s ∧ g2SC a b * (g2SC a g / 2) = 1 ∧ g2SC a b * (g2SC a g / 2) * (g2SC a d / 3) = s ∧
    2 * (g2SC a b * (g2SC a g / 2) * g2SC a b * (g2SC d g / 3)) = 2 ∧
    (3 : ℤ) ∣ (g2SC d a' / 2) * 2 - s ∧ g2SC b e = s

private def g2QuadWords {A H : Type*} [CommRing A] [Group H]
    (x : Fin 12 → Multiplicative A →* H) (a b g d e z a' : Fin 12) (s : ℤ) (u : A) : Prop :=
  x d (ofAdd u) = ⁅x a (ofAdd 1), x b (ofAdd (-u))⁆ * ⁅x a (ofAdd (-1)), x b (ofAdd (-u))⁆ ∧
    x g (ofAdd u) = ⁅x d (ofAdd ((s : A) * u)), x a' (ofAdd 1)⁆ ∧
    x e (ofAdd u) = ((x g (ofAdd (-u)) * x d (ofAdd (-(s : A) * u)))⁻¹ *
        ⁅x a (ofAdd 1), x b (ofAdd (-(s : A) * u))⁆) * ((x g (ofAdd u) *
        x d (ofAdd ((s : A) * u)))⁻¹ * ⁅x a (ofAdd 1), x b (ofAdd ((s : A) * u))⁆)⁻¹ ∧
    x z (ofAdd u) = ⁅x b (ofAdd 1), x e (ofAdd ((s : A) * u))⁆

variable {ht : G2.Valid}
local notation "ΦG2" => G2.simplyConnectedRootDatum ht
local notation "NG2" => G2.structureConstant ht

private theorem g2_sum_excluded_iff (α β : Fin G2.numRoots) :
    ((ΦG2).root α + (ΦG2).root β ∉ Set.range (ΦG2).root ∧ (ΦG2).root α + (ΦG2).root β ≠ 0) ↔
      (g2Root α + g2Root β ∉ Set.range g2Root ∧ g2Root α + g2Root β ≠ 0) :=
  and_congr (g2_add_mem_range_iff α β).not (g2_add_eq_zero_iff α β).not
private theorem commute_of_g2ModThreeComm {A H : Type*} [CommRing A] [CharP A 3] [Group H]
    (x : Fin G2.numRoots → Multiplicative A →* H)
    (hexcl : ∀ {i j}, (ΦG2).root i + (ΦG2).root j ∉ Set.range (ΦG2).root →
      (ΦG2).root i + (ΦG2).root j ≠ 0 → ∀ u v : A, Commute (x i (ofAdd u)) (x j (ofAdd v)))
    (hlong : ∀ {i j k}, g2Length k = 3 → (ΦG2).root k = (ΦG2).root i + (ΦG2).root j →
      ∀ u v : A, ⁅x i (ofAdd u), x j (ofAdd v)⁆ = x k (ofAdd ((NG2 i j : A) * (u * v))))
    {i j : Fin G2.numRoots} (h : g2ModThreeComm i j) (u v : Multiplicative A) :
    Commute (x i u) (x j v) := by
  rw [← ofAdd_toAdd u, ← ofAdd_toAdd v]
  rcases h with he | ⟨k, hk, hadd, hdvd⟩
  · obtain ⟨hr, h0⟩ := (g2_sum_excluded_iff (ht := ht) i j).mpr he; exact hexcl hr h0 _ _
  · rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm,
      hlong hk ((g2_root_add_iff i j k).mpr hadd), structureConstant_G2,
      (CharP.intCast_eq_zero_iff A 3 _).mpr hdvd, zero_mul, ofAdd_zero, map_one]
private theorem commute_rootSubgroup_of_g2ModThreeComm (D : ChevalleyDatum G2 ht) (A : Type v)
    [CommRing A] [CharP A 3] {i j : Fin G2.numRoots} (h : g2ModThreeComm i j)
    (u v : Multiplicative A) : Commute (D.rootSubgroupPoints i A u) (D.rootSubgroupPoints j A v) :=
  commute_of_g2ModThreeComm (ht := ht) (fun r => D.rootSubgroupPoints r A)
    (fun hr h0 _ _ => D.commute_rootSubgroup hr h0 A _ _)
    (fun hk hadd => D.commutatorElement_rootSubgroup_G2_of_long_sum hk hadd A) h u v

variable (D E : ChevalleyDatum G2 ht) (A : Type v) [CommRing A] [ExpChar A 3]
local notation "xG2" => D.g2SpecialIsogenyRootSubgroup A
local notation "xE" => E.g2SpecialIsogenyRootSubgroup A
private theorem xG2_eq (α : Fin G2.numRoots) (u : A) : xG2 α (ofAdd u) =
    D.rootSubgroupPoints (fI α) A (ofAdd (((fS α : ℤ) : A) * u ^ (g2Length (fI α)).toNat)) := by
  rw [D.g2SpecialIsogenyRootSubgroup_ofAdd]
  -- Expose `Fin 12` on `α` so the pinned `G₂` simp lemmas apply.
  change Fin 12 at α; simp

/-- **Commuting root subgroups under the `G₂` exceptional isogeny.** -/
theorem commute_g2SpecialIsogenyRootSubgroup {α β : Fin G2.numRoots}
    (h : (ΦG2).root α + (ΦG2).root β ∉ Set.range (ΦG2).root) (h0 : (ΦG2).root α + (ΦG2).root β ≠ 0)
    (u v : A) : Commute (xG2 α (ofAdd u)) (xG2 β (ofAdd v)) := by
  rw [xG2_eq, xG2_eq]; obtain ⟨hr, hne⟩ := (g2_sum_excluded_iff α β).mp ⟨h, h0⟩
  exact commute_rootSubgroup_of_g2ModThreeComm D A (g2_commute_partner_cases hr hne) _ _

/-- **Long-sum Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum {α β γ : Fin G2.numRoots}
    (hγ : g2Length γ = 3) (hadd : (ΦG2).root γ = (ΦG2).root α + (ΦG2).root β) (u v : A) :
    ⁅xG2 α (ofAdd u), xG2 β (ofAdd v)⁆ = xG2 γ (ofAdd ((NG2 α β : A) * (u * v))) := by
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  simp only [xG2_eq]
  rcases g2_long_sum_partner_cases hγ ((g2_root_add_iff α β γ).mp hadd) with
    ⟨hr, hne, hdvd⟩ | ⟨hfa, hfb, hfg, hadd', ⟨l, m, hl, hm⟩, hdvd⟩
  · obtain ⟨hr', hne'⟩ := (g2_sum_excluded_iff _ _).mpr ⟨hr, hne⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr ((D.commute_rootSubgroup hr' hne' A _ _).eq),
      structureConstant_G2, (CharP.intCast_eq_zero_iff A 3 _).mpr hdvd, zero_mul,
      (g2Length_g2SpecialIsogenyIndex_eq_one_iff γ).mpr hγ]; simp
  · rw [hfa, hfb, hfg, D.commutatorElement_rootSubgroup_of_g2_short_pair hfa hfb hfg
      ((g2_root_add_iff _ _ _).mpr hadd') ((g2_root_add_iff _ _ l).mpr hl)
      ((g2_root_add_iff _ _ m).mpr hm) A]
    simp only [Int.toNat_one, pow_one, h3, zero_mul, mul_zero, ofAdd_zero, map_one, mul_one]
    congr 2; rw [structureConstant_G2 ht (fI α) (fI β), structureConstant_G2]
    have hc := (CharP.intCast_eq_intCast A 3).mpr (Int.modEq_iff_dvd.mpr hdvd).symm
    push_cast at hc ⊢; linear_combination u * v * hc

/-- **One-factor Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_root_eq_add {α β γ : Fin G2.numRoots}
    (hγ : (ΦG2).root γ = (ΦG2).root α + (ΦG2).root β)
    (hα : 2 • (ΦG2).root α + (ΦG2).root β ∉ Set.range (ΦG2).root)
    (hβ : (ΦG2).root α + 2 • (ΦG2).root β ∉ Set.range (ΦG2).root) (u v : A) :
    ⁅xG2 α (ofAdd u), xG2 β (ofAdd v)⁆ = xG2 γ (ofAdd ((NG2 α β : A) * (u * v))) := by
  rw [root_simplyConnectedRootDatum_G2] at hα hβ
  exact D.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum A
    (g2_length_eq_three_of_no_two_nsmul ((g2_root_add_iff α β γ).mp hγ) hα hβ) hγ u v

/-- **Short-pair Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_pair {i j k l m : Fin G2.numRoots}
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (ΦG2).root k = (ΦG2).root i + (ΦG2).root j) (u v : A) :
    ⁅xG2 i (ofAdd u), xG2 j (ofAdd v)⁆ = xG2 k (ofAdd (((NG2 i j / 2 : ℤ) : A) * (2 * u * v))) *
      xG2 l (ofAdd (((NG2 i j / 2 * (NG2 i k / 3) : ℤ) : A) * (3 * u ^ 2 * v))) *
      xG2 m (ofAdd (-((NG2 i j / 2 * (NG2 k j / 3) : ℤ) : A) * (3 * u * v ^ 2))) := by
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  obtain ⟨hfi, hfj, hfk, hadd', hdvd⟩ :=
    g2_short_pair_partner i j k hi hj hk ((g2_root_add_iff i j k).mp hij)
  simp only [h3, zero_mul, mul_zero, ofAdd_zero, map_one, mul_one, xG2_eq, hfi, hfj, hfk]
  rw [D.commutatorElement_rootSubgroup_G2_of_long_sum hfk ((g2_root_add_iff _ _ _).mpr hadd') A]
  congr 2; rw [structureConstant_G2 ht (fI i) (fI j), structureConstant_G2]
  have hc := (CharP.intCast_eq_intCast A 3).mpr (Int.modEq_iff_dvd.mpr hdvd).symm
  push_cast at hc ⊢; linear_combination u ^ 3 * v ^ 3 * hc

/-- **Four-factor short-first Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_long
    {α β γ δ ε ζ : Fin G2.numRoots} (hγ : (ΦG2).root γ = (ΦG2).root α + (ΦG2).root β)
    (hδ : (ΦG2).root δ = (ΦG2).root α + (ΦG2).root γ)
    (hε : (ΦG2).root ε = (ΦG2).root α + (ΦG2).root δ)
    (hζ : (ΦG2).root ζ = (ΦG2).root δ + (ΦG2).root γ) (u v : A) :
    ⁅xG2 α (ofAdd u), xG2 β (ofAdd v)⁆ = xG2 γ (ofAdd ((NG2 α β : A) * (u * v))) *
      xG2 δ (ofAdd (((NG2 α β * (NG2 α γ / 2) : ℤ) : A) * (u ^ 2 * v))) *
      xG2 ε (ofAdd (((NG2 α β * (NG2 α γ / 2) * (NG2 α δ / 3) : ℤ) : A) * (u ^ 3 * v))) *
      xG2 ζ (ofAdd (((2 * (NG2 α β * (NG2 α γ / 2) * NG2 α β *
        (NG2 δ γ / 3)) : ℤ) : A) * (u ^ 3 * v ^ 2))) := by
  have r {i j k} := g2_root_add_iff (ht := ht) i j k
  have hmem := mem_g2ShortLongTuples (r.mp hγ) (r.mp hδ) (r.mp hε) (r.mp hζ)
  obtain ⟨⟨r₁, r₂, r₃, r₄, qa, qb, qg, qd, qe, qz⟩, d₁, d₂, d₃, d₄⟩ :=
    g2_short_long_partner (α, β, γ, δ, ε, ζ) hmem
  obtain ⟨_, _, _, _, _, _, ceg, ced, czg, czd⟩ :=
    g2_short_long_factors_comm (α, β, γ, δ, ε, ζ) hmem
  simp only [xG2_eq, qa, qb, qg, qd, qe, qz, pow_one]
  have mc {i j} (c : g2ModThreeComm i j) := commute_rootSubgroup_of_g2ModThreeComm D A c
  rw [D.commutatorElement_rootSubgroup_of_g2_long_short (r.mpr r₁) (r.mpr r₂) (r.mpr r₃)
      (r.mpr r₄) A, mul_assoc (_ * _),
    (((mc ceg _ _).mul_left (mc czg _ _)).mul_right ((mc ced _ _).mul_left (mc czd _ _))).eq,
    ← mul_assoc, structureConstant_G2 ht (fI β) (fI α), structureConstant_G2 ht (fI β) (fI ε),
    structureConstant_G2 ht (fI β) (fI ζ), structureConstant_G2 ht (fI ζ) (fI ε)]
  simp only [structureConstant_G2]
  have eq3 {a b : ℤ} (d : (3 : ℤ) ∣ a - b) : (a : A) = b :=
    (CharP.intCast_eq_intCast A 3).mpr (Int.modEq_iff_dvd.mpr d).symm
  have e₁ := eq3 d₁; have e₂ := eq3 d₂; have e₃ := eq3 d₃; have e₄ := eq3 d₄
  push_cast at e₁ e₂ e₃ e₄ ⊢
  refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ (by congr 2; linear_combination u ^ 3 * v ^ 3 * e₃)
    (by congr 2; linear_combination u ^ 6 * v ^ 3 * e₄))
    (by congr 2; linear_combination u ^ 3 * v * e₁))
    (by congr 2; linear_combination u ^ 3 * v ^ 2 * e₂)

private theorem commute_g2SpecialIsogeny_of_g2ModThreeComm
    {i j : Fin G2.numRoots} (hc : g2ModThreeComm i j) (w₁ w₂ : Multiplicative A) :
    Commute (xG2 i w₁) (xG2 j w₂) :=
  commute_of_g2ModThreeComm (ht := ht) xG2
    (fun hr h0 => D.commute_g2SpecialIsogenyRootSubgroup A hr h0)
    (fun hk hadd => D.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum A hk hadd) hc w₁ w₂

/-- **Four-factor long-first Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_short
    {α β γ δ ε ζ : Fin G2.numRoots} (hγ : (ΦG2).root γ = (ΦG2).root α + (ΦG2).root β)
    (hδ : (ΦG2).root δ = (ΦG2).root α + (ΦG2).root γ)
    (hε : (ΦG2).root ε = (ΦG2).root α + (ΦG2).root δ)
    (hζ : (ΦG2).root ζ = (ΦG2).root δ + (ΦG2).root γ) (u v : A) :
    ⁅xG2 β (ofAdd v), xG2 α (ofAdd u)⁆ = xG2 γ (ofAdd (-(NG2 α β : A) * (u * v))) *
      xG2 δ (ofAdd (-((NG2 α β * (NG2 α γ / 2) : ℤ) : A) * (u ^ 2 * v))) *
      xG2 ε (ofAdd (-((NG2 α β * (NG2 α γ / 2) * (NG2 α δ / 3) : ℤ) : A) * (u ^ 3 * v))) *
      xG2 ζ (ofAdd (((NG2 α β * (NG2 α γ / 2) * NG2 α β *
        (NG2 δ γ / 3) : ℤ) : A) * (u ^ 3 * v ^ 2))) := by
  have r {i j k} := g2_root_add_iff (ht := ht) i j k
  obtain ⟨cgd, cge, cgz, cde, cdz, cez, _⟩ := g2_short_long_factors_comm (α, β, γ, δ, ε, ζ)
    (mem_g2ShortLongTuples (r.mp hγ) (r.mp hδ) (r.mp hε) (r.mp hζ))
  have mc {i j} (c : g2ModThreeComm i j) := commute_g2SpecialIsogeny_of_g2ModThreeComm D A c
  rw [← commutatorElement_inv,
    D.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_long A hγ hδ hε hζ u v,
    (((mc cgz _ _).mul_left (mc cdz _ _)).mul_left (mc cez _ _)).mul_inv,
    ((mc cge _ _).mul_left (mc cde _ _)).mul_inv, (mc cgd _ _).mul_inv]
  simp only [← map_inv, ← ofAdd_neg]
  refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ (by congr 2; ring) (by congr 2; push_cast; ring))
    (by congr 2; push_cast; ring)) (by
      congr 2; push_cast; linear_combination -((NG2 α β : A) * ((NG2 α γ / 2 : ℤ) : A) *
        (NG2 α β : A) * ((NG2 δ γ / 3 : ℤ) : A) * u ^ 3 * v ^ 2) * CharP.cast_eq_zero A 3)

private theorem g2_words_of_halfTuple {H : Type*} [Group H]
    (x : Fin 12 → Multiplicative A →* H) {a b g d e z a' l m : Fin 12} {s : ℤ}
    (htup : g2HalfTuple a b g d e z a' l m s)
    (hcomm : ∀ {i j : Fin 12}, g2ModThreeComm i j → ∀ u v, Commute (x i u) (x j v))
    (hsl : ∀ t w : A, ⁅x a (ofAdd t), x b (ofAdd w)⁆ =
      x g (ofAdd ((NG2 a b : A) * (t * w))) *
        x d (ofAdd (((NG2 a b * (NG2 a g / 2) : ℤ) : A) * (t ^ 2 * w))) *
        x e (ofAdd (((NG2 a b * (NG2 a g / 2) * (NG2 a d / 3) : ℤ) : A) * (t ^ 3 * w))) *
        x z (ofAdd (((2 * (NG2 a b * (NG2 a g / 2) * NG2 a b *
          (NG2 d g / 3)) : ℤ) : A) * (t ^ 3 * w ^ 2))))
    (hsp : ∀ u : A, ⁅x d (ofAdd u), x a' (ofAdd 1)⁆ =
      x g (ofAdd (((NG2 d a' / 2 : ℤ) : A) * (2 * u * 1))) *
        x l (ofAdd (((NG2 d a' / 2 * (NG2 d g / 3) : ℤ) : A) * (3 * u ^ 2 * 1))) *
        x m (ofAdd (-((NG2 d a' / 2 * (NG2 g a' / 3) : ℤ) : A) * (3 * u * 1 ^ 2))))
    (hls : ∀ u : A, ⁅x b (ofAdd 1), x e (ofAdd u)⁆ = x z (ofAdd ((NG2 b e : A) * (1 * u))))
    (u : A) : g2QuadWords x a b g d e z a' s u := by
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  obtain ⟨hs, _, _, _, _, hγ, hδ, hε, hζ, _, _, _, _, hc1, hc2, hc3, hc4, hcsp, hcls⟩ := htup
  have hsA : (s : A) ^ 2 = 1 := by rw [← Int.cast_pow, hs, Int.cast_one]
  have hsl' (t w : A) : ⁅x a (ofAdd t), x b (ofAdd w)⁆ =
      x g (ofAdd ((s : A) * t * w)) * x d (ofAdd (t ^ 2 * w)) *
        x e (ofAdd ((s : A) * t ^ 3 * w)) * x z (ofAdd (2 * t ^ 3 * w ^ 2)) := by
    rw [hsl t w, structureConstant_G2 ht a b, structureConstant_G2 ht a g,
      structureConstant_G2 ht a d, structureConstant_G2 ht d g, hc4, hc3, hc2, hc1]
    refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_ <;> congr 2 <;> push_cast <;> ring
  obtain ⟨cgd, cge, cgz, cde, cdz, cez, _⟩ :=
    g2_short_long_factors_comm (a, b, g, d, e, z) (mem_g2ShortLongTuples hγ hδ hε hζ)
  have hadd (r : Fin 12) (w₁ w₂ : A) :
      x r (ofAdd w₁) * x r (ofAdd w₂) = x r (ofAdd (w₁ + w₂)) := by rw [← map_mul, ofAdd_add]
  refine ⟨?_, ?_, ?_, by
    rw [hls, structureConstant_G2 ht b e, hcls, one_mul]; congr 2; linear_combination -u * hsA⟩
  · rw [hsl' 1 (-u), hsl' (-1) (-u),
      (((hcomm cgz _ _).symm.mul_right (hcomm cdz _ _).symm).mul_right
        (hcomm cez _ _).symm).mul_mul_mul_comm _ _,
      ((hcomm cge _ _).symm.mul_right (hcomm cde _ _).symm).mul_mul_mul_comm _ _,
      (hcomm cgd _ _).symm.mul_mul_mul_comm _ _, hadd, hadd, hadd, hadd,
      (by ring : (s : A) * 1 * -u + (s : A) * -1 * -u = 0),
      (by linear_combination -u * h3 : (1 : A) ^ 2 * -u + (-1 : A) ^ 2 * -u = u),
      (by ring : (s : A) * 1 ^ 3 * -u + (s : A) * (-1 : A) ^ 3 * -u = 0),
      (by ring : 2 * (1 : A) ^ 3 * (-u) ^ 2 + 2 * (-1 : A) ^ 3 * (-u) ^ 2 = 0)]; simp
  · rw [hsp]; simp only [h3, zero_mul, mul_zero, ofAdd_zero, map_one, mul_one]
    congr 2; rw [structureConstant_G2 ht d a']
    have hcs := (CharP.intCast_eq_intCast A 3).mpr (Int.modEq_iff_dvd.mpr hcsp).symm
    push_cast at hcs; linear_combination -(s : A) * u * hcs - u * hsA
  · have q (w : A) : (x g (ofAdd ((s : A) * w)) * x d (ofAdd w))⁻¹ *
        ⁅x a (ofAdd 1), x b (ofAdd w)⁆ = x e (ofAdd ((s : A) * w)) * x z (ofAdd (2 * w ^ 2)) := by
      rw [hsl' 1 w]; simp only [mul_one, one_pow, one_mul]; group
    have hq₁ := q (-(s : A) * u); have hq₂ := q ((s : A) * u)
    rw [(by linear_combination -u * hsA : (s : A) * (-(s : A) * u) = -u)] at hq₁
    rw [(by linear_combination u * hsA : (s : A) * ((s : A) * u) = u)] at hq₂
    rw [hq₁, hq₂, (by ring : 2 * (-(s : A) * u) ^ 2 = 2 * ((s : A) * u) ^ 2), mul_inv_rev,
      mul_assoc, mul_inv_cancel_left, ← map_inv, ← ofAdd_neg, hadd]
    congr 2; linear_combination u * h3

private abbrev EqOnRoot (φ : D.points A →* E.points A) (r : Fin 12) : Prop :=
  ∀ w, φ (D.rootSubgroupPoints r A w) = xE r w

private theorem eq_quadruple_of_g2_half (φ : D.points A →* E.points A)
    {a b g d e z a' l m : Fin 12} {s : ℤ} (htup : g2HalfTuple a b g d e z a' l m s)
    (ha : EqOnRoot D E A φ a) (hb : EqOnRoot D E A φ b) (ha' : EqOnRoot D E A φ a') :
    EqOnRoot D E A φ g ∧ EqOnRoot D E A φ d ∧ EqOnRoot D E A φ e ∧ EqOnRoot D E A φ z := by
  have ⟨_, hd1, ha'1, hg1, hz3, hγ, hδ, hε, hζ, hij, hik, hkj, hbe, _⟩ := htup
  have ra {i j k} (h : g2Root k = g2Root i + g2Root j) := (g2_root_add_iff (ht := ht) i j k).mpr h
  have wD := g2_words_of_halfTuple (ht := ht) A (fun r : Fin 12 => D.rootSubgroupPoints r A) htup
    (fun hc => commute_rootSubgroup_of_g2ModThreeComm D A hc)
    (D.commutatorElement_rootSubgroup_of_g2_short_long (ra hγ) (ra hδ) (ra hε) (ra hζ) A)
    (fun u => D.commutatorElement_rootSubgroup_of_g2_short_pair hd1 ha'1 hg1
      (ra hij) (ra hik) (ra hkj) A u 1)
    (fun u => D.commutatorElement_rootSubgroup_G2_of_long_sum hz3 (ra hbe) A 1 u)
  have wE := g2_words_of_halfTuple (ht := ht) A (fun r : Fin 12 => xE r) htup
    (fun hc => commute_g2SpecialIsogeny_of_g2ModThreeComm E A hc)
    (E.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_long A
      (ra hγ) (ra hδ) (ra hε) (ra hζ))
    (fun u => E.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_pair (l := l) (m := m) A
      hd1 ha'1 hg1 (ra hij) u 1)
    (fun u => E.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum A hz3 (ra hbe) 1 u)
  have hd : EqOnRoot D E A φ d := fun w => by
    rw [← ofAdd_toAdd w, (wD _).1, (wE _).1]; simp only [map_mul, map_commutatorElement, ha, hb]
  have hg : EqOnRoot D E A φ g := fun w => by
    rw [← ofAdd_toAdd w, (wD _).2.1, (wE _).2.1]; simp only [map_commutatorElement, hd, ha']
  have he : EqOnRoot D E A φ e := fun w => by
    rw [← ofAdd_toAdd w, (wD _).2.2.1, (wE _).2.2.1]
    simp only [map_mul, map_inv, map_commutatorElement, hg, hd, ha, hb]
  refine ⟨hg, hd, he, fun w => ?_⟩
  rw [← ofAdd_toAdd w, (wD _).2.2.2, (wE _).2.2.2]; simp only [map_commutatorElement, hb, he]

/-- A group homomorphism `φ : D.points A →* E.points A` agreeing with
`E.g2SpecialIsogenyRootSubgroup A` on the positive and negative simple root subgroups agrees with
it on all twelve root subgroups. -/
theorem map_rootSubgroupPoints_of_g2SpecialIsogeny_simple (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (G2.simpleIndex ht i) A u) = xE (G2.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦG2).reflectionPerm (G2.simpleIndex ht i) (G2.simpleIndex ht i)) A u) =
      xE ((ΦG2).reflectionPerm (G2.simpleIndex ht i) (G2.simpleIndex ht i)) u)
    (α : Fin G2.numRoots) (u : Multiplicative A) : φ (D.rootSubgroupPoints α A u) = xE α u := by
  let eqR (s : Fin G2.numRoots) (r : Fin 12) (heq : (s : Fin 12) = r)
      (hs : ∀ w, φ (D.rootSubgroupPoints s A w) = xE s w) : EqOnRoot D E A φ r := fun w =>
    (congrArg (fun k : Fin 12 => φ (D.rootSubgroupPoints k A w)) heq.symm).trans
      ((hs w).trans (congrArg (fun k : Fin 12 => xE k w) heq))
  have h0 := eqR _ 0 ((simpleIndex_G2 ht 0).trans rfl) (hpos (0 : Fin 2))
  have h1 := eqR _ 1 ((simpleIndex_G2 ht 1).trans rfl) (hpos (1 : Fin 2))
  have h6 := eqR _ 6
    ((reflectionPerm_self_G2 ht _).trans (by rw [simpleIndex_G2]; rfl)) (hneg (0 : Fin 2))
  have h7 := eqR _ 7
    ((reflectionPerm_self_G2 ht _).trans (by rw [simpleIndex_G2]; rfl)) (hneg (1 : Fin 2))
  obtain ⟨h2, h3, h4, h5⟩ := eq_quadruple_of_g2_half D E A φ (g := 2) (d := 3) (e := 4) (z := 5)
    (l := 5) (m := 1) (s := 1)
    (by simp only [g2HalfTuple, g2Length_apply, g2Root_apply, g2StructureConstant_def]; decide)
    h0 h1 h6
  obtain ⟨h8, h9, h10, h11⟩ := eq_quadruple_of_g2_half D E A φ (g := 8) (d := 9) (e := 10) (z := 11)
    (l := 11) (m := 7) (s := -1)
    (by simp only [g2HalfTuple, g2Length_apply, g2Root_apply, g2StructureConstant_def]; decide)
    h6 h7 h0
  -- Expose `Fin 12` on `α` to dispatch the twelve roots to `h0` through `h11`.
  change Fin 12 at α
  fin_cases α <;>
    first | exact h0 u | exact h1 u | exact h2 u | exact h3 u | exact h4 u | exact h5 u |
      exact h6 u | exact h7 u | exact h8 u | exact h9 u | exact h10 u | exact h11 u

/-- An endomorphism `φ : D.points A →* D.points A` agreeing with `g2SpecialIsogenyRootSubgroup` on
the positive and negative simple root subgroups squares to `D.frobenius 3 1 A` on
`D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_g2SpecialIsogeny_simple (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (G2.simpleIndex ht i) A u) =
      xG2 (G2.simpleIndex ht i) u) (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((ΦG2).reflectionPerm (G2.simpleIndex ht i) (G2.simpleIndex ht i)) A u) =
      xG2 ((ΦG2).reflectionPerm (G2.simpleIndex ht i) (G2.simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) : φ (φ g) = D.frobenius 3 1 A g := by
  have hall := map_rootSubgroupPoints_of_g2SpecialIsogeny_simple D D A φ hpos hneg
  refine (D.elementarySubgroup_le_iff A ((φ.comp φ).eqLocus (D.frobenius 3 1 A))).mpr
    (fun α u => ?_) hg
  -- Membership in `MonoidHom.eqLocus` unfolds to pointwise equality of the two homomorphisms.
  change φ (φ (D.rootSubgroupPoints α A u)) = D.frobenius 3 1 A (D.rootSubgroupPoints α A u)
  rw [← ofAdd_toAdd u]
  exact (congrArg φ ((hall α _).trans (D.g2SpecialIsogenyRootSubgroup_ofAdd A α _))).trans
    ((hall _ _).trans (D.g2SpecialIsogenyRootSubgroup_comp_self A α (toAdd u)))

end G2

end TauCeti.DynkinType.ChevalleyDatum
