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

Over a commutative ring `A` of exponential characteristic `3`, Steinberg's exceptional
root-subgroup family `TauCeti.DynkinType.ChevalleyDatum.g2SpecialIsogenyRootSubgroup`
(`x_α(u) ↦ x_{f(α)}(ε_α u ^ q(α))` with signs `TauCeti.DynkinType.g2SpecialIsogenySign`) satisfies
every Chevalley commutator relation of the pinned `G₂` Chevalley system:

* commuting pairs (`α + β` neither a root nor `0`) map either to commuting pairs or to two short
  roots whose sum is long, where `N_{f(α), f(β)} = ±3` vanishes in characteristic `3`;
* pairs with long sum (`γ = α + β` long) either have short `α, β` (both sides `1` in
  characteristic `3`) or long `α, β` (mapped to a `G₂` short-pair commutator whose two extra
  factors carry explicit multiples of `3` and vanish in characteristic `3`);
* `G₂` short pairs (`i, j, i + j` short) map to long sums, while the two extra factors on the
  right carry multiples of `3` and vanish;
* four-factor `G₂` strings (`short_long` and `long_short`) reverse orientation under `f`,
  exchanging `short_long` on `(α, β, γ, δ, ε, ζ)` with `long_short` on
  `(f(β), f(α), f(ε), f(ζ), f(γ), f(δ))`, and the four factors pairwise commute in
  characteristic `3`.

From these commutator relations in characteristic `3`, any group homomorphism between `G₂`
Chevalley point groups matching `g2SpecialIsogenyRootSubgroup` on the four signed simple roots
(`±α₁`, `±α₂`) matches it on all twelve roots of `G₂`, and any endomorphism matching it on the
signed simple roots squares to `D.frobenius 3 1 A` on `D.elementarySubgroup A`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.commute_g2SpecialIsogenyRootSubgroup`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_g2SpecialIsogenyRootSubgroup_of_root_eq_add`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_pair`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_long`
* `TauCeti.DynkinType.ChevalleyDatum.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_short`
* `TauCeti.DynkinType.ChevalleyDatum.map_rootSubgroupPoints_of_g2SpecialIsogeny_simple`
* `TauCeti.DynkinType.ChevalleyDatum.comp_self_eq_frobenius_of_g2SpecialIsogeny_simple`

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10, Lemma 53 and Theorem 28.
* R. W. Carter, *Simple Groups of Lie Type*, §§12.3–12.4.
-/

public section

open Multiplicative
open scoped commutatorElement

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

section G2Aux

private abbrev g2ModThreeComm (i j : Fin 12) : Prop :=
  (g2Root i + g2Root j ∉ Set.range g2Root ∧ g2Root i + g2Root j ≠ 0) ∨
    ∃ k : Fin 12, g2Length k = 3 ∧ g2Root k = g2Root i + g2Root j ∧
      (3 : ℤ) ∣ g2StructureConstant i j

private theorem cast_eq_of_three_dvd (A : Type*) [CommRing A] [CharP A 3] {a b : ℤ}
    (h : (3 : ℤ) ∣ a - b) : (a : A) = (b : A) := by
  obtain ⟨m, hm⟩ := h
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  have h0 : ((a - b : ℤ) : A) = 0 := by
    rw [hm]; push_cast; rw [h3, zero_mul]
  rwa [Int.cast_sub, sub_eq_zero] at h0

private theorem g2_sc_eq (ht : G2.Valid) (i j : Fin 12) :
    G2.structureConstant ht i j = g2StructureConstant i j :=
  structureConstant_G2 ht i j

private theorem g2Root_injective : Function.Injective g2Root := by
  intro i j h
  simp only [g2Root_apply] at h
  revert i j h
  decide

private theorem g2_root_eq_add_iff {ht : G2.Valid} {α β γ : Fin G2.numRoots} :
    ((G2.simplyConnectedRootDatum ht).root γ =
        (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β) ↔
      g2Root γ = g2Root α + g2Root β := by
  simp +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
    rank, numRoots]

private theorem g2_sum_excluded_iff {ht : G2.Valid} (α β : Fin G2.numRoots) :
    ((G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β ∉
        Set.range (G2.simplyConnectedRootDatum ht).root ∧
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β ≠ 0) ↔
    (g2Root α + g2Root β ∉ Set.range g2Root ∧ g2Root α + g2Root β ≠ 0) := by
  simp +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
    rank, numRoots, Pi.zero_def]

private theorem g2_two_nsmul_notMem_iff {ht : G2.Valid} (α β : Fin G2.numRoots) :
    (2 • (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β ∉
        Set.range (G2.simplyConnectedRootDatum ht).root) ↔
      2 • g2Root α + g2Root β ∉ Set.range g2Root := by
  simp +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
    rank, numRoots]

private theorem g2SpecialIsogenyRootSubgroup_eq {ht : G2.Valid} (D : ChevalleyDatum G2 ht)
    (A : Type v) [CommRing A] [ExpChar A 3] (α : Fin G2.numRoots) (u : A) :
    D.g2SpecialIsogenyRootSubgroup A α (ofAdd u) =
      D.rootSubgroupPoints (g2SpecialIsogenyIndex α) A
        (ofAdd (((g2SpecialIsogenySign α : ℤ) : A) *
          u ^ (g2Length (g2SpecialIsogenyIndex α)).toNat)) := by
  rw [g2SpecialIsogenyRootSubgroup_ofAdd]
  have hidx : ∀ i : Fin 12, g2SpecialIsogeny.indexEquiv i = g2SpecialIsogenyIndex i :=
    g2SpecialIsogeny_indexEquiv_apply
  have hexp : ∀ i : Fin 12, g2SpecialIsogeny.exponent i = g2Length i :=
    g2SpecialIsogeny_exponent
  rw [hidx α, hexp (g2SpecialIsogenyIndex α)]

private theorem commute_rootSubgroup_of_g2ModThreeComm {ht : G2.Valid} (D : ChevalleyDatum G2 ht)
    (A : Type v) [CommRing A] [CharP A 3] {i j : Fin G2.numRoots}
    (h : g2ModThreeComm i j) (u v : Multiplicative A) :
    Commute (D.rootSubgroupPoints i A u) (D.rootSubgroupPoints j A v) := by
  rcases h with hexcl | ⟨k, hk, hadd, hdvd⟩
  · obtain ⟨hrange, h0⟩ := (g2_sum_excluded_iff i j).mpr hexcl
    exact D.commute_rootSubgroup hrange h0 A u v
  · rw [← ofAdd_toAdd u, ← ofAdd_toAdd v, commute_iff_eq,
      ← commutatorElement_eq_one_iff_mul_comm,
      D.commutatorElement_rootSubgroup_G2_of_long_sum hk
        (g2_root_eq_add_iff (γ := k).mpr hadd) A,
      structureConstant_G2,
      cast_eq_of_three_dvd A (a := g2StructureConstant i j) (b := 0) (by simpa using hdvd),
      Int.cast_zero, zero_mul, ofAdd_zero, map_one]

private theorem g2_commute_partner_cases {α β : Fin 12}
    (h : g2Root α + g2Root β ∉ Set.range g2Root) (h0 : g2Root α + g2Root β ≠ 0) :
    g2ModThreeComm (g2SpecialIsogenyIndex α) (g2SpecialIsogenyIndex β) := by
  simp only [g2ModThreeComm, Set.mem_range, g2Root_apply, g2Length_apply,
    g2SpecialIsogenyIndex_def, g2StructureConstant_def] at *
  decide +revert

private theorem g2_long_sum_partner_cases {α β γ : Fin 12} (hγ : g2Length γ = 3)
    (hadd : g2Root γ = g2Root α + g2Root β) :
    (g2Root (g2SpecialIsogenyIndex α) + g2Root (g2SpecialIsogenyIndex β) ∉ Set.range g2Root ∧
        g2Root (g2SpecialIsogenyIndex α) + g2Root (g2SpecialIsogenyIndex β) ≠ 0 ∧
        (3 : ℤ) ∣ g2StructureConstant α β) ∨
      (g2Length (g2SpecialIsogenyIndex α) = 1 ∧ g2Length (g2SpecialIsogenyIndex β) = 1 ∧
        g2Length (g2SpecialIsogenyIndex γ) = 1 ∧
        g2Root (g2SpecialIsogenyIndex γ) =
          g2Root (g2SpecialIsogenyIndex α) + g2Root (g2SpecialIsogenyIndex β) ∧
        (∃ l m : Fin 12,
          g2Root l = g2Root (g2SpecialIsogenyIndex α) + g2Root (g2SpecialIsogenyIndex γ) ∧
          g2Root m = g2Root (g2SpecialIsogenyIndex γ) + g2Root (g2SpecialIsogenyIndex β)) ∧
        (3 : ℤ) ∣
          ((g2StructureConstant (g2SpecialIsogenyIndex α) (g2SpecialIsogenyIndex β) / 2) * 2 *
              (g2SpecialIsogenySign α : ℤ) * (g2SpecialIsogenySign β : ℤ) -
            (g2SpecialIsogenySign γ : ℤ) * g2StructureConstant α β)) := by
  simp only [Set.mem_range, g2Root_apply, g2Length_apply, g2SpecialIsogenyIndex_def,
    g2SpecialIsogenySign_def, g2StructureConstant_def] at *
  decide +revert

private theorem g2_length_eq_three_of_no_two_nsmul {α β γ : Fin 12}
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hα : 2 • g2Root α + g2Root β ∉ Set.range g2Root)
    (hβ : g2Root α + 2 • g2Root β ∉ Set.range g2Root) :
    g2Length γ = 3 := by
  simp only [Set.mem_range, g2Root_apply, g2Length_apply] at *
  decide +revert

private theorem g2_short_pair_partner (i j k : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : g2Root k = g2Root i + g2Root j) :
    g2Length (g2SpecialIsogenyIndex i) = 3 ∧ g2Length (g2SpecialIsogenyIndex j) = 3 ∧
      g2Length (g2SpecialIsogenyIndex k) = 3 ∧
      g2Root (g2SpecialIsogenyIndex k) =
        g2Root (g2SpecialIsogenyIndex i) + g2Root (g2SpecialIsogenyIndex j) ∧
      (3 : ℤ) ∣
        (g2StructureConstant (g2SpecialIsogenyIndex i) (g2SpecialIsogenyIndex j) *
            (g2SpecialIsogenySign i : ℤ) * (g2SpecialIsogenySign j : ℤ) -
          (g2SpecialIsogenySign k : ℤ) * (2 * (g2StructureConstant i j / 2)) ^ 3) := by
  revert i j k hi hj hk hij
  simp only [g2Root_apply, g2Length_apply, g2SpecialIsogenyIndex_def,
    g2SpecialIsogenySign_def, g2StructureConstant_def, funext_iff, Fin.forall_fin_two,
    Pi.add_apply]
  decide

private def g2ShortLongTuples : List (Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12 × Fin 12) :=
  [(0, 1, 2, 3, 4, 5), (0, 10, 9, 8, 7, 11), (2, 7, 0, 3, 5, 4), (2, 11, 9, 6, 1, 10),
   (3, 10, 6, 2, 5, 1), (3, 11, 8, 0, 4, 7), (6, 4, 3, 2, 1, 5), (6, 7, 8, 9, 10, 11),
   (8, 1, 6, 9, 11, 10), (8, 5, 3, 0, 7, 4), (9, 4, 0, 8, 11, 7), (9, 5, 2, 6, 10, 1)]

private theorem mem_g2ShortLongTuples {α β γ δ ε ζ : Fin 12}
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    (α, β, γ, δ, ε, ζ) ∈ g2ShortLongTuples := by
  have h1 : g2Root α + g2Root β ∈ Set.range g2Root := ⟨γ, hγ⟩
  have h2 : 2 • g2Root α + g2Root β ∈ Set.range g2Root := ⟨δ, by rw [hδ, hγ]; module⟩
  have h3 : 3 • g2Root α + g2Root β ∈ Set.range g2Root := ⟨ε, by rw [hε, hδ, hγ]; module⟩
  have h4 : 3 • g2Root α + 2 • g2Root β ∈ Set.range g2Root := ⟨ζ, by rw [hζ, hδ, hγ]; module⟩
  have hex : ∃ q ∈ g2ShortLongTuples, q.1 = α ∧ q.2.1 = β ∧
      g2Root q.2.2.1 = g2Root α + g2Root β ∧
      g2Root q.2.2.2.1 = g2Root α + g2Root q.2.2.1 ∧
      g2Root q.2.2.2.2.1 = g2Root α + g2Root q.2.2.2.1 ∧
      g2Root q.2.2.2.2.2 = g2Root q.2.2.2.1 + g2Root q.2.2.1 := by
    clear hγ hδ hε hζ γ δ ε ζ
    simp only [g2ShortLongTuples, Set.mem_range, g2Root_apply] at h1 h2 h3 h4 ⊢
    decide +revert
  obtain ⟨⟨α₀, β₀, γ₀, δ₀, ε₀, ζ₀⟩, hmem, rfl, rfl, eγ, eδ, eε, eζ⟩ := hex
  obtain rfl := g2Root_injective (hγ.trans eγ.symm)
  obtain rfl := g2Root_injective (hδ.trans eδ.symm)
  obtain rfl := g2Root_injective (hε.trans eε.symm)
  obtain rfl := g2Root_injective (hζ.trans eζ.symm)
  exact hmem

private theorem permute_four_comm {G : Type*} [Group G] {e z g d : G}
    (heg : Commute e g) (hed : Commute e d) (hzg : Commute z g) (hzd : Commute z d) :
    e * z * g * d = g * d * e * z := by
  calc
    e * z * g * d = e * (z * g) * d := by group
    _ = e * (g * z) * d := by rw [hzg.eq]
    _ = (e * g) * (z * d) := by group
    _ = (g * e) * (d * z) := by rw [heg.eq, hzd.eq]
    _ = g * (e * d) * z := by group
    _ = g * (d * e) * z := by rw [hed.eq]
    _ = g * d * e * z := by group

private theorem mul_four_inv_of_commute {G : Type*} [Group G] {a b c d : G}
    (hab : Commute a b) (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) (hcd : Commute c d) :
    (a * b * c * d)⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ * d⁻¹ := by
  simp only [mul_inv_rev]
  calc
    d⁻¹ * (c⁻¹ * (b⁻¹ * a⁻¹)) = d⁻¹ * (c⁻¹ * (a⁻¹ * b⁻¹)) := by rw [hab.inv_inv.symm.eq]
    _ = d⁻¹ * ((c⁻¹ * a⁻¹) * b⁻¹) := by group
    _ = d⁻¹ * ((a⁻¹ * c⁻¹) * b⁻¹) := by rw [hac.inv_inv.symm.eq]
    _ = (d⁻¹ * a⁻¹) * (c⁻¹ * b⁻¹) := by group
    _ = (a⁻¹ * d⁻¹) * (b⁻¹ * c⁻¹) := by rw [had.inv_inv.symm.eq, hbc.inv_inv.symm.eq]
    _ = a⁻¹ * (d⁻¹ * b⁻¹) * c⁻¹ := by group
    _ = a⁻¹ * (b⁻¹ * d⁻¹) * c⁻¹ := by rw [hbd.inv_inv.symm.eq]
    _ = a⁻¹ * b⁻¹ * (d⁻¹ * c⁻¹) := by group
    _ = a⁻¹ * b⁻¹ * (c⁻¹ * d⁻¹) := by rw [hcd.inv_inv.symm.eq]
    _ = a⁻¹ * b⁻¹ * c⁻¹ * d⁻¹ := by group

private theorem collect_four_comm {G : Type*} [Group G] {g₁ d₁ e₁ z₁ g₂ d₂ e₂ z₂ : G}
    (hgd : Commute d₁ g₂) (hge : Commute e₁ g₂) (hde : Commute e₁ d₂)
    (hgz : Commute z₁ g₂) (hdz : Commute z₁ d₂) (hez : Commute z₁ e₂) :
    g₁ * d₁ * e₁ * z₁ * (g₂ * d₂ * e₂ * z₂) =
      (g₁ * g₂) * (d₁ * d₂) * (e₁ * e₂) * (z₁ * z₂) := by
  have c1 : Commute (g₂ * d₂) e₁ := hge.symm.mul_left hde.symm
  have c2 : Commute (g₂ * d₂ * e₂) z₁ := (hgz.symm.mul_left hdz.symm).mul_left hez.symm
  calc
    g₁ * d₁ * e₁ * z₁ * (g₂ * d₂ * e₂ * z₂) =
        g₁ * d₁ * e₁ * (z₁ * (g₂ * d₂ * e₂)) * z₂ := by group
    _ = g₁ * d₁ * e₁ * (g₂ * d₂ * e₂ * z₁) * z₂ := by rw [c2.symm.eq]
    _ = g₁ * d₁ * (e₁ * (g₂ * d₂)) * (e₂ * (z₁ * z₂)) := by group
    _ = g₁ * d₁ * (g₂ * d₂ * e₁) * (e₂ * (z₁ * z₂)) := by rw [c1.symm.eq]
    _ = g₁ * (d₁ * g₂) * d₂ * (e₁ * e₂) * (z₁ * z₂) := by group
    _ = (g₁ * g₂) * (d₁ * d₂) * (e₁ * e₂) * (z₁ * z₂) := by rw [hgd.eq]; group

private theorem g2_short_long_partner_roots {α β γ δ ε ζ : Fin 12}
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    g2Root (g2SpecialIsogenyIndex ε) =
        g2Root (g2SpecialIsogenyIndex β) + g2Root (g2SpecialIsogenyIndex α) ∧
      g2Root (g2SpecialIsogenyIndex ζ) =
        g2Root (g2SpecialIsogenyIndex β) + g2Root (g2SpecialIsogenyIndex ε) ∧
      g2Root (g2SpecialIsogenyIndex γ) =
        g2Root (g2SpecialIsogenyIndex β) + g2Root (g2SpecialIsogenyIndex ζ) ∧
      g2Root (g2SpecialIsogenyIndex δ) =
        g2Root (g2SpecialIsogenyIndex ζ) + g2Root (g2SpecialIsogenyIndex ε) ∧
      (g2Length (g2SpecialIsogenyIndex α)).toNat = 3 ∧
      (g2Length (g2SpecialIsogenyIndex β)).toNat = 1 ∧
      (g2Length (g2SpecialIsogenyIndex γ)).toNat = 3 ∧
      (g2Length (g2SpecialIsogenyIndex δ)).toNat = 3 ∧
      (g2Length (g2SpecialIsogenyIndex ε)).toNat = 1 ∧
      (g2Length (g2SpecialIsogenyIndex ζ)).toNat = 1 := by
  have hall : ∀ q ∈ g2ShortLongTuples,
      let α := q.1; let β := q.2.1; let γ := q.2.2.1
      let δ := q.2.2.2.1; let ε := q.2.2.2.2.1; let ζ := q.2.2.2.2.2
      g2Root (g2SpecialIsogenyIndex ε) =
          g2Root (g2SpecialIsogenyIndex β) + g2Root (g2SpecialIsogenyIndex α) ∧
        g2Root (g2SpecialIsogenyIndex ζ) =
          g2Root (g2SpecialIsogenyIndex β) + g2Root (g2SpecialIsogenyIndex ε) ∧
        g2Root (g2SpecialIsogenyIndex γ) =
          g2Root (g2SpecialIsogenyIndex β) + g2Root (g2SpecialIsogenyIndex ζ) ∧
        g2Root (g2SpecialIsogenyIndex δ) =
          g2Root (g2SpecialIsogenyIndex ζ) + g2Root (g2SpecialIsogenyIndex ε) ∧
        (g2Length (g2SpecialIsogenyIndex α)).toNat = 3 ∧
        (g2Length (g2SpecialIsogenyIndex β)).toNat = 1 ∧
        (g2Length (g2SpecialIsogenyIndex γ)).toNat = 3 ∧
        (g2Length (g2SpecialIsogenyIndex δ)).toNat = 3 ∧
        (g2Length (g2SpecialIsogenyIndex ε)).toNat = 1 ∧
        (g2Length (g2SpecialIsogenyIndex ζ)).toNat = 1 := by
    simp only [g2ShortLongTuples, g2Root_apply, g2Length_apply, g2SpecialIsogenyIndex_def]
    decide
  exact hall (α, β, γ, δ, ε, ζ) (mem_g2ShortLongTuples hγ hδ hε hζ)

private theorem g2_short_long_partner_coeffs {α β γ δ ε ζ : Fin 12}
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    (let fa := g2SpecialIsogenyIndex α; let fb := g2SpecialIsogenyIndex β
     let fe := g2SpecialIsogenyIndex ε; let fz := g2SpecialIsogenyIndex ζ
     (3 : ℤ) ∣ (-g2StructureConstant fb fa * (g2SpecialIsogenySign β : ℤ) *
         (g2SpecialIsogenySign α : ℤ) -
       (g2SpecialIsogenySign ε : ℤ) *
         (g2StructureConstant α β * (g2StructureConstant α γ / 2) *
           (g2StructureConstant α δ / 3))) ∧
     (3 : ℤ) ∣ (-(g2StructureConstant fb fa * (g2StructureConstant fb fe / 2)) *
         (g2SpecialIsogenySign β : ℤ) ^ 2 * (g2SpecialIsogenySign α : ℤ) -
       (g2SpecialIsogenySign ζ : ℤ) *
         (2 * (g2StructureConstant α β * (g2StructureConstant α γ / 2) *
           g2StructureConstant α β * (g2StructureConstant δ γ / 3)))) ∧
     (3 : ℤ) ∣ (-(g2StructureConstant fb fa * (g2StructureConstant fb fe / 2) *
           (g2StructureConstant fb fz / 3)) *
         (g2SpecialIsogenySign β : ℤ) ^ 3 * (g2SpecialIsogenySign α : ℤ) -
       (g2SpecialIsogenySign γ : ℤ) * g2StructureConstant α β ^ 3) ∧
     (3 : ℤ) ∣ ((g2StructureConstant fb fa * (g2StructureConstant fb fe / 2) *
           g2StructureConstant fb fa * (g2StructureConstant fz fe / 3)) *
         (g2SpecialIsogenySign β : ℤ) ^ 3 * (g2SpecialIsogenySign α : ℤ) ^ 2 -
       (g2SpecialIsogenySign δ : ℤ) *
         (g2StructureConstant α β * (g2StructureConstant α γ / 2)) ^ 3)) := by
  have hall : ∀ q ∈ g2ShortLongTuples,
      let α := q.1; let β := q.2.1; let γ := q.2.2.1
      let δ := q.2.2.2.1; let ε := q.2.2.2.2.1; let ζ := q.2.2.2.2.2
      let fa := g2SpecialIsogenyIndex α; let fb := g2SpecialIsogenyIndex β
      let fe := g2SpecialIsogenyIndex ε; let fz := g2SpecialIsogenyIndex ζ
      (3 : ℤ) ∣ (-g2StructureConstant fb fa * (g2SpecialIsogenySign β : ℤ) *
          (g2SpecialIsogenySign α : ℤ) -
        (g2SpecialIsogenySign ε : ℤ) *
          (g2StructureConstant α β * (g2StructureConstant α γ / 2) *
            (g2StructureConstant α δ / 3))) ∧
      (3 : ℤ) ∣ (-(g2StructureConstant fb fa * (g2StructureConstant fb fe / 2)) *
          (g2SpecialIsogenySign β : ℤ) ^ 2 * (g2SpecialIsogenySign α : ℤ) -
        (g2SpecialIsogenySign ζ : ℤ) *
          (2 * (g2StructureConstant α β * (g2StructureConstant α γ / 2) *
            g2StructureConstant α β * (g2StructureConstant δ γ / 3)))) ∧
      (3 : ℤ) ∣ (-(g2StructureConstant fb fa * (g2StructureConstant fb fe / 2) *
            (g2StructureConstant fb fz / 3)) *
          (g2SpecialIsogenySign β : ℤ) ^ 3 * (g2SpecialIsogenySign α : ℤ) -
        (g2SpecialIsogenySign γ : ℤ) * g2StructureConstant α β ^ 3) ∧
      (3 : ℤ) ∣ ((g2StructureConstant fb fa * (g2StructureConstant fb fe / 2) *
            g2StructureConstant fb fa * (g2StructureConstant fz fe / 3)) *
          (g2SpecialIsogenySign β : ℤ) ^ 3 * (g2SpecialIsogenySign α : ℤ) ^ 2 -
        (g2SpecialIsogenySign δ : ℤ) *
          (g2StructureConstant α β * (g2StructureConstant α γ / 2)) ^ 3) := by
    simp only [g2ShortLongTuples, g2SpecialIsogenyIndex_def, g2SpecialIsogenySign_def,
      g2StructureConstant_def]
    decide
  exact hall (α, β, γ, δ, ε, ζ) (mem_g2ShortLongTuples hγ hδ hε hζ)

private theorem g2_short_long_factors_comm {α β γ δ ε ζ : Fin 12}
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    g2ModThreeComm γ δ ∧ g2ModThreeComm γ ε ∧ g2ModThreeComm γ ζ ∧
      g2ModThreeComm δ ε ∧ g2ModThreeComm δ ζ ∧ g2ModThreeComm ε ζ ∧
      g2ModThreeComm (g2SpecialIsogenyIndex ε) (g2SpecialIsogenyIndex γ) ∧
      g2ModThreeComm (g2SpecialIsogenyIndex ε) (g2SpecialIsogenyIndex δ) ∧
      g2ModThreeComm (g2SpecialIsogenyIndex ζ) (g2SpecialIsogenyIndex γ) ∧
      g2ModThreeComm (g2SpecialIsogenyIndex ζ) (g2SpecialIsogenyIndex δ) := by
  have hall : ∀ q ∈ g2ShortLongTuples,
      g2ModThreeComm q.2.2.1 q.2.2.2.1 ∧ g2ModThreeComm q.2.2.1 q.2.2.2.2.1 ∧
        g2ModThreeComm q.2.2.1 q.2.2.2.2.2 ∧ g2ModThreeComm q.2.2.2.1 q.2.2.2.2.1 ∧
        g2ModThreeComm q.2.2.2.1 q.2.2.2.2.2 ∧ g2ModThreeComm q.2.2.2.2.1 q.2.2.2.2.2 ∧
        g2ModThreeComm (g2SpecialIsogenyIndex q.2.2.2.2.1) (g2SpecialIsogenyIndex q.2.2.1) ∧
        g2ModThreeComm (g2SpecialIsogenyIndex q.2.2.2.2.1) (g2SpecialIsogenyIndex q.2.2.2.1) ∧
        g2ModThreeComm (g2SpecialIsogenyIndex q.2.2.2.2.2) (g2SpecialIsogenyIndex q.2.2.1) ∧
        g2ModThreeComm (g2SpecialIsogenyIndex q.2.2.2.2.2) (g2SpecialIsogenyIndex q.2.2.2.1) := by
    dsimp only [g2ShortLongTuples]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [g2ModThreeComm, Set.mem_range, g2Root_apply, g2Length_apply,
        g2SpecialIsogenyIndex_def, g2StructureConstant_def, ne_eq, funext_iff, Fin.forall_fin_two,
        Pi.add_apply, Pi.zero_apply] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      decide
  exact hall (α, β, γ, δ, ε, ζ) (mem_g2ShortLongTuples hγ hδ hε hζ)

private theorem g2_quadruple_words {A H : Type*} [CommRing A] [CharP A 3] [Group H]
    (x : Fin G2.numRoots → Multiplicative A →* H)
    {a b g d e z a' : Fin G2.numRoots} {s : ℤ} (hs : s ^ 2 = 1)
    (hsl : ∀ t w : A, ⁅x a (ofAdd t), x b (ofAdd w)⁆ =
      x g (ofAdd ((s : A) * t * w)) * x d (ofAdd (t ^ 2 * w)) *
        x e (ofAdd ((s : A) * t ^ 3 * w)) * x z (ofAdd (2 * t ^ 3 * w ^ 2)))
    (hcgd : ∀ u v, Commute (x g u) (x d v)) (hcge : ∀ u v, Commute (x g u) (x e v))
    (hcgz : ∀ u v, Commute (x g u) (x z v)) (hcde : ∀ u v, Commute (x d u) (x e v))
    (hcdz : ∀ u v, Commute (x d u) (x z v)) (hcez : ∀ u v, Commute (x e u) (x z v))
    (hsp : ∀ u : A, ⁅x d (ofAdd u), x a' (ofAdd 1)⁆ = x g (ofAdd ((s : A) * u)))
    (hls : ∀ u : A, ⁅x b (ofAdd 1), x e (ofAdd u)⁆ = x z (ofAdd ((s : A) * u))) (u : A) :
    x d (ofAdd u) = ⁅x a (ofAdd 1), x b (ofAdd (-u))⁆ * ⁅x a (ofAdd (-1)), x b (ofAdd (-u))⁆ ∧
      x g (ofAdd u) = ⁅x d (ofAdd ((s : A) * u)), x a' (ofAdd 1)⁆ ∧
      x e (ofAdd u) =
        ((x g (ofAdd (-u)) * x d (ofAdd (-(s : A) * u)))⁻¹ *
            ⁅x a (ofAdd 1), x b (ofAdd (-(s : A) * u))⁆) *
          ((x g (ofAdd u) * x d (ofAdd ((s : A) * u)))⁻¹ *
            ⁅x a (ofAdd 1), x b (ofAdd ((s : A) * u))⁆)⁻¹ ∧
      x z (ofAdd u) = ⁅x b (ofAdd 1), x e (ofAdd ((s : A) * u))⁆ := by
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  have hsA : (s : A) ^ 2 = 1 := by rw [← Int.cast_pow, hs, Int.cast_one]
  have hadd (r : Fin G2.numRoots) (w₁ w₂ : A) :
      x r (ofAdd w₁) * x r (ofAdd w₂) = x r (ofAdd (w₁ + w₂)) := by rw [← map_mul, ofAdd_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsl 1 (-u), hsl (-1) (-u),
      collect_four_comm (hcgd _ _).symm (hcge _ _).symm (hcde _ _).symm
        (hcgz _ _).symm (hcdz _ _).symm (hcez _ _).symm,
      hadd, hadd, hadd, hadd]
    have z₁ : (s : A) * 1 * -u + (s : A) * -1 * -u = 0 := by ring
    have z₂ : 1 ^ 2 * -u + (-1 : A) ^ 2 * -u = u := by linear_combination -u * h3
    have z₃ : (s : A) * 1 ^ 3 * -u + (s : A) * (-1) ^ 3 * -u = 0 := by ring
    have z₄ : 2 * 1 ^ 3 * (-u) ^ 2 + 2 * (-1 : A) ^ 3 * (-u) ^ 2 = 0 := by ring
    rw [z₁, z₂, z₃, z₄]
    simp
  · rw [hsp]; congr 2; linear_combination -u * hsA
  · have q (w : A) : (x g (ofAdd ((s : A) * w)) * x d (ofAdd w))⁻¹ *
        ⁅x a (ofAdd 1), x b (ofAdd w)⁆ =
        x e (ofAdd ((s : A) * w)) * x z (ofAdd (2 * w ^ 2)) := by
      rw [hsl 1 w]; simp only [mul_one, one_pow, one_mul]; group
    have r₁ : (s : A) * (-(s : A) * u) = -u := by linear_combination -u * hsA
    have r₂ : (s : A) * ((s : A) * u) = u := by linear_combination u * hsA
    have hq₁ := q (-(s : A) * u); rw [r₁] at hq₁
    have hq₂ := q ((s : A) * u); rw [r₂] at hq₂
    have r₃ : 2 * (-(s : A) * u) ^ 2 = 2 * ((s : A) * u) ^ 2 := by ring
    rw [hq₁, hq₂, r₃, mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← map_inv, ← ofAdd_neg, hadd]
    congr 2; linear_combination u * h3
  · rw [hls]; congr 2; linear_combination -u * hsA

end G2Aux

section G2

variable {ht : G2.Valid} (D E : ChevalleyDatum G2 ht)
variable (A : Type v) [CommRing A] [ExpChar A 3]

/-- **Commuting root subgroups under the `G₂` exceptional isogeny.** -/
theorem commute_g2SpecialIsogenyRootSubgroup {α β : Fin G2.numRoots}
    (h : (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β ∉
      Set.range (G2.simplyConnectedRootDatum ht).root)
    (h0 : (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β ≠ 0)
    (u v : A) :
    Commute (D.g2SpecialIsogenyRootSubgroup A α (ofAdd u))
      (D.g2SpecialIsogenyRootSubgroup A β (ofAdd v)) := by
  have : CharP A 3 := (expChar_prime_iff (R := A) Nat.prime_three).mp ‹_›
  rw [g2SpecialIsogenyRootSubgroup_eq, g2SpecialIsogenyRootSubgroup_eq]
  obtain ⟨hr, hne⟩ := (g2_sum_excluded_iff α β).mp ⟨h, h0⟩
  exact commute_rootSubgroup_of_g2ModThreeComm D A (g2_commute_partner_cases hr hne) _ _

/-- **Long-sum Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum {α β γ : Fin G2.numRoots}
    (hγ : g2Length γ = 3)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (u v : A) :
    ⁅D.g2SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.g2SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.g2SpecialIsogenyRootSubgroup A γ
        (ofAdd ((G2.structureConstant ht α β : A) * (u * v))) := by
  have : CharP A 3 := (expChar_prime_iff (R := A) Nat.prime_three).mp ‹_›
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  simp only [g2SpecialIsogenyRootSubgroup_eq]
  rcases g2_long_sum_partner_cases hγ (g2_root_eq_add_iff.mp hadd) with
    ⟨hr, hne, hdvd⟩ | ⟨hfa, hfb, hfg, hadd', ⟨l, m, hl, hm⟩, hdvd⟩
  · obtain ⟨hr', hne'⟩ := (g2_sum_excluded_iff
      (g2SpecialIsogenyIndex α) (g2SpecialIsogenyIndex β)).mpr ⟨hr, hne⟩
    have hfg1 : g2Length (g2SpecialIsogenyIndex γ) = 1 :=
      (g2Length_g2SpecialIsogenyIndex_eq_one_iff γ).mpr hγ
    rw [commutatorElement_eq_one_iff_mul_comm.mpr ((D.commute_rootSubgroup hr' hne' A _ _).eq),
      structureConstant_G2,
      cast_eq_of_three_dvd A (a := g2StructureConstant α β) (b := 0) (by simpa using hdvd),
      Int.cast_zero, zero_mul, hfg1]
    simp
  · rw [hfa, hfb, hfg,
      D.commutatorElement_rootSubgroup_of_g2_short_pair hfa hfb hfg
        (g2_root_eq_add_iff.mpr hadd') (g2_root_eq_add_iff (γ := l).mpr hl)
        (g2_root_eq_add_iff (γ := m).mpr hm) A]
    simp only [Int.toNat_one, pow_one, h3, zero_mul, mul_zero, ofAdd_zero, map_one, mul_one]
    congr 2
    simp only [structureConstant_G2, g2_sc_eq]
    have hc := cast_eq_of_three_dvd A hdvd
    push_cast at hc ⊢
    linear_combination u * v * hc

/-- **One-factor Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_root_eq_add {α β γ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hα : 2 • (G2.simplyConnectedRootDatum ht).root α +
        (G2.simplyConnectedRootDatum ht).root β ∉
      Set.range (G2.simplyConnectedRootDatum ht).root)
    (hβ : (G2.simplyConnectedRootDatum ht).root α +
        2 • (G2.simplyConnectedRootDatum ht).root β ∉
      Set.range (G2.simplyConnectedRootDatum ht).root)
    (u v : A) :
    ⁅D.g2SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.g2SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.g2SpecialIsogenyRootSubgroup A γ
        (ofAdd ((G2.structureConstant ht α β : A) * (u * v))) := by
  have hα' := (g2_two_nsmul_notMem_iff α β).mp hα
  have hβ' : g2Root α + 2 • g2Root β ∉ Set.range g2Root := by
    rw [add_comm] at hβ ⊢
    exact (g2_two_nsmul_notMem_iff β α).mp hβ
  exact D.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum A
    (g2_length_eq_three_of_no_two_nsmul (g2_root_eq_add_iff.mp hγ) hα' hβ') hγ u v

/-- **Short-pair Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_pair
    {i j k l m : Fin G2.numRoots}
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hij : (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j)
    (hik : (G2.simplyConnectedRootDatum ht).root l =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root k)
    (hkj : (G2.simplyConnectedRootDatum ht).root m =
      (G2.simplyConnectedRootDatum ht).root k + (G2.simplyConnectedRootDatum ht).root j)
    (u v : A) :
    ⁅D.g2SpecialIsogenyRootSubgroup A i (ofAdd u),
        D.g2SpecialIsogenyRootSubgroup A j (ofAdd v)⁆ =
      D.g2SpecialIsogenyRootSubgroup A k
          (ofAdd (((G2.structureConstant ht i j / 2 : ℤ) : A) * (2 * u * v))) *
        D.g2SpecialIsogenyRootSubgroup A l
          (ofAdd (((G2.structureConstant ht i j / 2 *
            (G2.structureConstant ht i k / 3) : ℤ) : A) * (3 * u ^ 2 * v))) *
        D.g2SpecialIsogenyRootSubgroup A m
          (ofAdd (-((G2.structureConstant ht i j / 2 *
            (G2.structureConstant ht k j / 3) : ℤ) : A) * (3 * u * v ^ 2))) := by
  have : CharP A 3 := (expChar_prime_iff (R := A) Nat.prime_three).mp ‹_›
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  have _ := And.intro hik hkj
  simp only [h3, zero_mul, mul_zero, ofAdd_zero, map_one, mul_one]
  obtain ⟨hfi, hfj, hfk, hadd', hdvd⟩ :=
    g2_short_pair_partner i j k hi hj hk (g2_root_eq_add_iff.mp hij)
  simp only [g2SpecialIsogenyRootSubgroup_eq, hfi, hfj, hfk]
  rw [D.commutatorElement_rootSubgroup_G2_of_long_sum hfk (g2_root_eq_add_iff.mpr hadd') A]
  congr 2
  simp only [structureConstant_G2, g2_sc_eq]
  have hc := cast_eq_of_three_dvd A hdvd
  push_cast at hc ⊢
  linear_combination u ^ 3 * v ^ 3 * hc

/-- **Four-factor short-first Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_long
    {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (u v : A) :
    ⁅D.g2SpecialIsogenyRootSubgroup A α (ofAdd u),
        D.g2SpecialIsogenyRootSubgroup A β (ofAdd v)⁆ =
      D.g2SpecialIsogenyRootSubgroup A γ
          (ofAdd ((G2.structureConstant ht α β : A) * (u * v))) *
        D.g2SpecialIsogenyRootSubgroup A δ
          (ofAdd (((G2.structureConstant ht α β *
            (G2.structureConstant ht α γ / 2) : ℤ) : A) * (u ^ 2 * v))) *
        D.g2SpecialIsogenyRootSubgroup A ε
          (ofAdd (((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
            (G2.structureConstant ht α δ / 3) : ℤ) : A) * (u ^ 3 * v))) *
        D.g2SpecialIsogenyRootSubgroup A ζ
          (ofAdd (((2 * (G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
            G2.structureConstant ht α β *
              (G2.structureConstant ht δ γ / 3)) : ℤ) : A) * (u ^ 3 * v ^ 2))) := by
  have : CharP A 3 := (expChar_prime_iff (R := A) Nat.prime_three).mp ‹_›
  have hγ' := g2_root_eq_add_iff.mp hγ; have hδ' := g2_root_eq_add_iff.mp hδ
  have hε' := g2_root_eq_add_iff.mp hε; have hζ' := g2_root_eq_add_iff.mp hζ
  obtain ⟨r₁, r₂, r₃, r₄, qa, qb, qg, qd, qe, qz⟩ := g2_short_long_partner_roots hγ' hδ' hε' hζ'
  obtain ⟨d₁, d₂, d₃, d₄⟩ := g2_short_long_partner_coeffs hγ' hδ' hε' hζ'
  obtain ⟨_, _, _, _, _, _, ceg, ced, czg, czd⟩ := g2_short_long_factors_comm hγ' hδ' hε' hζ'
  simp only [g2SpecialIsogenyRootSubgroup_eq, qa, qb, qg, qd, qe, qz, pow_one]
  rw [D.commutatorElement_rootSubgroup_of_g2_long_short (g2_root_eq_add_iff.mpr r₁)
      (g2_root_eq_add_iff.mpr r₂) (g2_root_eq_add_iff.mpr r₃) (g2_root_eq_add_iff.mpr r₄) A,
    permute_four_comm (commute_rootSubgroup_of_g2ModThreeComm D A ceg _ _)
      (commute_rootSubgroup_of_g2ModThreeComm D A ced _ _)
      (commute_rootSubgroup_of_g2ModThreeComm D A czg _ _)
      (commute_rootSubgroup_of_g2ModThreeComm D A czd _ _)]
  simp only [structureConstant_G2, g2_sc_eq]
  have e₁ := cast_eq_of_three_dvd A d₁; have e₂ := cast_eq_of_three_dvd A d₂
  have e₃ := cast_eq_of_three_dvd A d₃; have e₄ := cast_eq_of_three_dvd A d₄
  push_cast at e₁ e₂ e₃ e₄ ⊢
  congr 1
  · congr 1
    · congr 1
      · congr 2; linear_combination u ^ 3 * v ^ 3 * e₃
      · congr 2; linear_combination u ^ 6 * v ^ 3 * e₄
    · congr 2; linear_combination u ^ 3 * v * e₁
  · congr 2; linear_combination u ^ 3 * v ^ 2 * e₂

private theorem commute_g2SpecialIsogeny_of_g2ModThreeComm [CharP A 3]
    {i j : Fin G2.numRoots} (hc : g2ModThreeComm i j) (w₁ w₂ : Multiplicative A) :
    Commute (D.g2SpecialIsogenyRootSubgroup A i w₁)
      (D.g2SpecialIsogenyRootSubgroup A j w₂) := by
  rw [← ofAdd_toAdd w₁, ← ofAdd_toAdd w₂]
  rcases hc with hexcl | ⟨k, hk, hadd, hdvd⟩
  · obtain ⟨hr, hne⟩ := (g2_sum_excluded_iff i j).mpr hexcl
    exact D.commute_g2SpecialIsogenyRootSubgroup A hr hne _ _
  · rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm,
      D.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum A hk
        (g2_root_eq_add_iff (γ := k).mpr hadd),
      structureConstant_G2,
      cast_eq_of_three_dvd A (a := g2StructureConstant i j) (b := 0) (by simpa using hdvd),
      Int.cast_zero, zero_mul, ofAdd_zero, map_one]

/-- **Four-factor long-first Chevalley commutator relation under the `G₂` exceptional isogeny.** -/
theorem commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_short
    {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (u v : A) :
    ⁅D.g2SpecialIsogenyRootSubgroup A β (ofAdd v),
        D.g2SpecialIsogenyRootSubgroup A α (ofAdd u)⁆ =
      D.g2SpecialIsogenyRootSubgroup A γ
          (ofAdd (-(G2.structureConstant ht α β : A) * (u * v))) *
        D.g2SpecialIsogenyRootSubgroup A δ
          (ofAdd (-((G2.structureConstant ht α β *
            (G2.structureConstant ht α γ / 2) : ℤ) : A) * (u ^ 2 * v))) *
        D.g2SpecialIsogenyRootSubgroup A ε
          (ofAdd (-((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
            (G2.structureConstant ht α δ / 3) : ℤ) : A) * (u ^ 3 * v))) *
        D.g2SpecialIsogenyRootSubgroup A ζ
          (ofAdd (((G2.structureConstant ht α β * (G2.structureConstant ht α γ / 2) *
            G2.structureConstant ht α β *
              (G2.structureConstant ht δ γ / 3) : ℤ) : A) * (u ^ 3 * v ^ 2))) := by
  have : CharP A 3 := (expChar_prime_iff (R := A) Nat.prime_three).mp ‹_›
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  obtain ⟨cgd, cge, cgz, cde, cdz, cez, _⟩ := g2_short_long_factors_comm
    (g2_root_eq_add_iff.mp hγ) (g2_root_eq_add_iff.mp hδ)
    (g2_root_eq_add_iff.mp hε) (g2_root_eq_add_iff.mp hζ)
  rw [← commutatorElement_inv,
    D.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_long A hγ hδ hε hζ u v,
    mul_four_inv_of_commute
      (commute_g2SpecialIsogeny_of_g2ModThreeComm D A cgd _ _)
      (commute_g2SpecialIsogeny_of_g2ModThreeComm D A cge _ _)
      (commute_g2SpecialIsogeny_of_g2ModThreeComm D A cgz _ _)
      (commute_g2SpecialIsogeny_of_g2ModThreeComm D A cde _ _)
      (commute_g2SpecialIsogeny_of_g2ModThreeComm D A cdz _ _)
      (commute_g2SpecialIsogeny_of_g2ModThreeComm D A cez _ _)]
  simp only [← map_inv, ← ofAdd_neg]
  congr 1
  · congr 1
    · congr 1
      · congr 2; ring
      · congr 2; push_cast; ring
    · congr 2; push_cast; ring
  · congr 2; push_cast
    linear_combination -((G2.structureConstant ht α β : A) *
      ((G2.structureConstant ht α γ / 2 : ℤ) : A) * (G2.structureConstant ht α β : A) *
      ((G2.structureConstant ht δ γ / 3 : ℤ) : A) * u ^ 3 * v ^ 2) * h3

omit [ExpChar A 3] in
private theorem g2_half_relations_rootSubgroup [CharP A 3]
    {a b g d e z a' l m : Fin 12} {s : ℤ}
    (hd1 : g2Length d = 1) (ha'1 : g2Length a' = 1) (hg1 : g2Length g = 1) (hz3 : g2Length z = 3)
    (hγ : g2Root g = g2Root a + g2Root b) (hδ : g2Root d = g2Root a + g2Root g)
    (hε : g2Root e = g2Root a + g2Root d) (hζ : g2Root z = g2Root d + g2Root g)
    (hij : g2Root g = g2Root d + g2Root a') (hik : g2Root l = g2Root d + g2Root g)
    (hkj : g2Root m = g2Root g + g2Root a') (hbe : g2Root z = g2Root b + g2Root e)
    (hc1 : g2StructureConstant a b = s)
    (hc2 : g2StructureConstant a b * (g2StructureConstant a g / 2) = 1)
    (hc3 : g2StructureConstant a b * (g2StructureConstant a g / 2) *
      (g2StructureConstant a d / 3) = s)
    (hc4 : 2 * (g2StructureConstant a b * (g2StructureConstant a g / 2) *
      g2StructureConstant a b * (g2StructureConstant d g / 3)) = 2)
    (hcsp : (3 : ℤ) ∣ (g2StructureConstant d a' / 2) * 2 - s)
    (hcls : g2StructureConstant b e = s) :
    (∀ t w : A, ⁅D.rootSubgroupPoints a A (ofAdd t), D.rootSubgroupPoints b A (ofAdd w)⁆ =
      D.rootSubgroupPoints g A (ofAdd ((s : A) * t * w)) *
        D.rootSubgroupPoints d A (ofAdd (t ^ 2 * w)) *
        D.rootSubgroupPoints e A (ofAdd ((s : A) * t ^ 3 * w)) *
        D.rootSubgroupPoints z A (ofAdd (2 * t ^ 3 * w ^ 2))) ∧
      (∀ u : A, ⁅D.rootSubgroupPoints d A (ofAdd u), D.rootSubgroupPoints a' A (ofAdd 1)⁆ =
        D.rootSubgroupPoints g A (ofAdd ((s : A) * u))) ∧
      (∀ u : A, ⁅D.rootSubgroupPoints b A (ofAdd 1), D.rootSubgroupPoints e A (ofAdd u)⁆ =
        D.rootSubgroupPoints z A (ofAdd ((s : A) * u))) := by
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  refine ⟨fun t w => ?_, fun u => ?_, fun u => ?_⟩
  · rw [D.commutatorElement_rootSubgroup_of_g2_short_long (g2_root_eq_add_iff.mpr hγ)
      (g2_root_eq_add_iff.mpr hδ) (g2_root_eq_add_iff.mpr hε) (g2_root_eq_add_iff.mpr hζ) A]
    simp only [g2_sc_eq]
    rw [hc4, hc3, hc2, hc1]
    congr 1
    · congr 1
      · congr 1
        · congr 2; ring
        · congr 2; push_cast; ring
      · congr 2; ring
    · congr 2; push_cast; ring
  · rw [D.commutatorElement_rootSubgroup_of_g2_short_pair hd1 ha'1 hg1
      (g2_root_eq_add_iff.mpr hij) (g2_root_eq_add_iff.mpr hik) (g2_root_eq_add_iff.mpr hkj) A]
    simp only [h3, zero_mul, mul_zero, ofAdd_zero, map_one, mul_one, g2_sc_eq]
    congr 2
    have hcs := cast_eq_of_three_dvd A hcsp
    push_cast at hcs
    linear_combination u * hcs
  · rw [D.commutatorElement_rootSubgroup_G2_of_long_sum hz3 (g2_root_eq_add_iff.mpr hbe) A,
      g2_sc_eq, hcls, one_mul]

private theorem g2_half_relations_specialIsogeny [CharP A 3]
    {a b g d e z a' l m : Fin 12} {s : ℤ}
    (hd1 : g2Length d = 1) (ha'1 : g2Length a' = 1) (hg1 : g2Length g = 1) (hz3 : g2Length z = 3)
    (hγ : g2Root g = g2Root a + g2Root b) (hδ : g2Root d = g2Root a + g2Root g)
    (hε : g2Root e = g2Root a + g2Root d) (hζ : g2Root z = g2Root d + g2Root g)
    (hij : g2Root g = g2Root d + g2Root a') (hik : g2Root l = g2Root d + g2Root g)
    (hkj : g2Root m = g2Root g + g2Root a') (hbe : g2Root z = g2Root b + g2Root e)
    (hc1 : g2StructureConstant a b = s)
    (hc2 : g2StructureConstant a b * (g2StructureConstant a g / 2) = 1)
    (hc3 : g2StructureConstant a b * (g2StructureConstant a g / 2) *
      (g2StructureConstant a d / 3) = s)
    (hc4 : 2 * (g2StructureConstant a b * (g2StructureConstant a g / 2) *
      g2StructureConstant a b * (g2StructureConstant d g / 3)) = 2)
    (hcsp : (3 : ℤ) ∣ (g2StructureConstant d a' / 2) * 2 - s)
    (hcls : g2StructureConstant b e = s) :
    (∀ t w : A, ⁅E.g2SpecialIsogenyRootSubgroup A a (ofAdd t),
        E.g2SpecialIsogenyRootSubgroup A b (ofAdd w)⁆ =
      E.g2SpecialIsogenyRootSubgroup A g (ofAdd ((s : A) * t * w)) *
        E.g2SpecialIsogenyRootSubgroup A d (ofAdd (t ^ 2 * w)) *
        E.g2SpecialIsogenyRootSubgroup A e (ofAdd ((s : A) * t ^ 3 * w)) *
        E.g2SpecialIsogenyRootSubgroup A z (ofAdd (2 * t ^ 3 * w ^ 2))) ∧
      (∀ u : A, ⁅E.g2SpecialIsogenyRootSubgroup A d (ofAdd u),
          E.g2SpecialIsogenyRootSubgroup A a' (ofAdd 1)⁆ =
        E.g2SpecialIsogenyRootSubgroup A g (ofAdd ((s : A) * u))) ∧
      (∀ u : A, ⁅E.g2SpecialIsogenyRootSubgroup A b (ofAdd 1),
          E.g2SpecialIsogenyRootSubgroup A e (ofAdd u)⁆ =
        E.g2SpecialIsogenyRootSubgroup A z (ofAdd ((s : A) * u))) := by
  have h3 : (3 : A) = 0 := CharP.cast_eq_zero A 3
  refine ⟨fun t w => ?_, fun u => ?_, fun u => ?_⟩
  · rw [E.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_long A
      (g2_root_eq_add_iff.mpr hγ) (g2_root_eq_add_iff.mpr hδ)
      (g2_root_eq_add_iff.mpr hε) (g2_root_eq_add_iff.mpr hζ)]
    simp only [g2_sc_eq]
    rw [hc4, hc3, hc2, hc1]
    congr 1
    · congr 1
      · congr 1
        · congr 2; ring
        · congr 2; push_cast; ring
      · congr 2; ring
    · congr 2; push_cast; ring
  · rw [E.commutatorElement_g2SpecialIsogenyRootSubgroup_of_short_pair A hd1 ha'1 hg1
      (g2_root_eq_add_iff.mpr hij) (g2_root_eq_add_iff.mpr hik) (g2_root_eq_add_iff.mpr hkj)]
    simp only [h3, zero_mul, mul_zero, ofAdd_zero, map_one, mul_one, g2_sc_eq]
    congr 2
    have hcs := cast_eq_of_three_dvd A hcsp
    push_cast at hcs
    linear_combination u * hcs
  · rw [E.commutatorElement_g2SpecialIsogenyRootSubgroup_of_long_sum A hz3
      (g2_root_eq_add_iff.mpr hbe), g2_sc_eq, hcls, one_mul]

private theorem eq_quadruple_of_g2_half [CharP A 3]
    (φ : D.points A →* E.points A)
    {a b g d e z a' l m : Fin 12} {s : ℤ} (hs : s ^ 2 = 1)
    (hd1 : g2Length d = 1) (ha'1 : g2Length a' = 1) (hg1 : g2Length g = 1) (hz3 : g2Length z = 3)
    (hγ : g2Root g = g2Root a + g2Root b) (hδ : g2Root d = g2Root a + g2Root g)
    (hε : g2Root e = g2Root a + g2Root d) (hζ : g2Root z = g2Root d + g2Root g)
    (hij : g2Root g = g2Root d + g2Root a') (hik : g2Root l = g2Root d + g2Root g)
    (hkj : g2Root m = g2Root g + g2Root a') (hbe : g2Root z = g2Root b + g2Root e)
    (hc1 : g2StructureConstant a b = s)
    (hc2 : g2StructureConstant a b * (g2StructureConstant a g / 2) = 1)
    (hc3 : g2StructureConstant a b * (g2StructureConstant a g / 2) *
      (g2StructureConstant a d / 3) = s)
    (hc4 : 2 * (g2StructureConstant a b * (g2StructureConstant a g / 2) *
      g2StructureConstant a b * (g2StructureConstant d g / 3)) = 2)
    (hcsp : (3 : ℤ) ∣ (g2StructureConstant d a' / 2) * 2 - s)
    (hcls : g2StructureConstant b e = s)
    (ha : ∀ w, φ (D.rootSubgroupPoints a A w) = E.g2SpecialIsogenyRootSubgroup A a w)
    (hb : ∀ w, φ (D.rootSubgroupPoints b A w) = E.g2SpecialIsogenyRootSubgroup A b w)
    (ha' : ∀ w, φ (D.rootSubgroupPoints a' A w) = E.g2SpecialIsogenyRootSubgroup A a' w) :
    (∀ w, φ (D.rootSubgroupPoints g A w) = E.g2SpecialIsogenyRootSubgroup A g w) ∧
      (∀ w, φ (D.rootSubgroupPoints d A w) = E.g2SpecialIsogenyRootSubgroup A d w) ∧
      (∀ w, φ (D.rootSubgroupPoints e A w) = E.g2SpecialIsogenyRootSubgroup A e w) ∧
      (∀ w, φ (D.rootSubgroupPoints z A w) = E.g2SpecialIsogenyRootSubgroup A z w) := by
  obtain ⟨cgd, cge, cgz, cde, cdz, cez, _⟩ := g2_short_long_factors_comm hγ hδ hε hζ
  obtain ⟨hslD, hspD, hlsD⟩ := g2_half_relations_rootSubgroup D A hd1 ha'1 hg1 hz3 hγ hδ hε hζ
    hij hik hkj hbe hc1 hc2 hc3 hc4 hcsp hcls
  obtain ⟨hslE, hspE, hlsE⟩ := g2_half_relations_specialIsogeny E A hd1 ha'1 hg1 hz3 hγ hδ hε hζ
    hij hik hkj hbe hc1 hc2 hc3 hc4 hcsp hcls
  let x : Fin G2.numRoots → Multiplicative A →* E.points A :=
    fun r => φ.comp (D.rootSubgroupPoints r A)
  have commX {i j : Fin 12} (hc : g2ModThreeComm i j) (u v : Multiplicative A) :
      Commute (x i u) (x j v) :=
    (commute_rootSubgroup_of_g2ModThreeComm D A hc u v).map φ
  have hslX (t₁ w₁ : A) : ⁅x a (ofAdd t₁), x b (ofAdd w₁)⁆ =
      x g (ofAdd ((s : A) * t₁ * w₁)) * x d (ofAdd (t₁ ^ 2 * w₁)) *
        x e (ofAdd ((s : A) * t₁ ^ 3 * w₁)) * x z (ofAdd (2 * t₁ ^ 3 * w₁ ^ 2)) := by
    simpa only [x, MonoidHom.comp_apply, map_commutatorElement, map_mul] using
      congrArg (⇑φ) (hslD t₁ w₁)
  have hspX (u₁ : A) : ⁅x d (ofAdd u₁), x a' (ofAdd 1)⁆ = x g (ofAdd ((s : A) * u₁)) := by
    simpa only [x, MonoidHom.comp_apply, map_commutatorElement] using congrArg (⇑φ) (hspD u₁)
  have hlsX (u₁ : A) : ⁅x b (ofAdd 1), x e (ofAdd u₁)⁆ = x z (ofAdd ((s : A) * u₁)) := by
    simpa only [x, MonoidHom.comp_apply, map_commutatorElement] using congrArg (⇑φ) (hlsD u₁)
  have wX := g2_quadruple_words x (a := a) (b := b) (g := g) (d := d) (e := e) (z := z)
    (a' := a') hs hslX (commX cgd) (commX cge) (commX cgz) (commX cde) (commX cdz) (commX cez)
    hspX hlsX
  have wE := g2_quadruple_words (E.g2SpecialIsogenyRootSubgroup A)
    (a := a) (b := b) (g := g) (d := d) (e := e) (z := z) (a' := a') hs hslE
    (commute_g2SpecialIsogeny_of_g2ModThreeComm E A cgd)
    (commute_g2SpecialIsogeny_of_g2ModThreeComm E A cge)
    (commute_g2SpecialIsogeny_of_g2ModThreeComm E A cgz)
    (commute_g2SpecialIsogeny_of_g2ModThreeComm E A cde)
    (commute_g2SpecialIsogeny_of_g2ModThreeComm E A cdz)
    (commute_g2SpecialIsogeny_of_g2ModThreeComm E A cez) hspE hlsE
  have hd (u : A) : x d (ofAdd u) = E.g2SpecialIsogenyRootSubgroup A d (ofAdd u) := by
    rw [(wX u).1, (wE u).1]; simp only [x, MonoidHom.comp_apply, ha, hb]
  have hg (u : A) : x g (ofAdd u) = E.g2SpecialIsogenyRootSubgroup A g (ofAdd u) := by
    rw [(wX u).2.1, (wE u).2.1, hd]; simp only [x, MonoidHom.comp_apply, ha']
  have he (u : A) : x e (ofAdd u) = E.g2SpecialIsogenyRootSubgroup A e (ofAdd u) := by
    rw [(wX u).2.2.1, (wE u).2.2.1, hg, hd, hg, hd]; simp only [x, MonoidHom.comp_apply, ha, hb]
  have hz (u : A) : x z (ofAdd u) = E.g2SpecialIsogenyRootSubgroup A z (ofAdd u) := by
    rw [(wX u).2.2.2, (wE u).2.2.2, he]; simp only [x, MonoidHom.comp_apply, hb]
  exact ⟨fun w => by rw [← ofAdd_toAdd w]; exact hg (toAdd w),
    fun w => by rw [← ofAdd_toAdd w]; exact hd (toAdd w),
    fun w => by rw [← ofAdd_toAdd w]; exact he (toAdd w),
    fun w => by rw [← ofAdd_toAdd w]; exact hz (toAdd w)⟩

/-- **Simple-root determination for the `G₂` exceptional isogeny.** Any group homomorphism between
points of type `G₂` Chevalley data over `[ExpChar A 3]` matching `g2SpecialIsogenyRootSubgroup` on
the positive and negative simple roots matches it on all twelve roots. -/
theorem map_rootSubgroupPoints_of_g2SpecialIsogeny_simple
    (φ : D.points A →* E.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (G2.simpleIndex ht i) A u) =
      E.g2SpecialIsogenyRootSubgroup A (G2.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((G2.simplyConnectedRootDatum ht).reflectionPerm
          (G2.simpleIndex ht i) (G2.simpleIndex ht i)) A u) =
      E.g2SpecialIsogenyRootSubgroup A
        ((G2.simplyConnectedRootDatum ht).reflectionPerm
          (G2.simpleIndex ht i) (G2.simpleIndex ht i)) u)
    (α : Fin G2.numRoots) (u : Multiplicative A) :
    φ (D.rootSubgroupPoints α A u) = E.g2SpecialIsogenyRootSubgroup A α u := by
  have : CharP A 3 := (expChar_prime_iff (R := A) Nat.prime_three).mp ‹_›
  have hs0 : G2.simpleIndex ht (0 : Fin 2) = (0 : Fin 12) := simpleIndex_G2 ht (0 : Fin 2)
  have hs1 : G2.simpleIndex ht (1 : Fin 2) = (1 : Fin 12) := simpleIndex_G2 ht (1 : Fin 2)
  have h0 : ∀ w, φ (D.rootSubgroupPoints (0 : Fin 12) A w) =
      E.g2SpecialIsogenyRootSubgroup A (0 : Fin 12) w := by simpa only [hs0] using hpos (0 : Fin 2)
  have h1 : ∀ w, φ (D.rootSubgroupPoints (1 : Fin 12) A w) =
      E.g2SpecialIsogenyRootSubgroup A (1 : Fin 12) w := by simpa only [hs1] using hpos (1 : Fin 2)
  have href (i₀ r₀ : Fin 12) (hr : g2Root r₀ = -g2Root i₀) :
      (G2.simplyConnectedRootDatum ht).reflectionPerm i₀ i₀ = r₀ := by
    apply (G2.simplyConnectedRootDatum ht).root.injective
    have h := ((G2.simplyConnectedRootDatum ht).root_reflectionPerm i₀ i₀).trans
      ((G2.simplyConnectedRootDatum ht).reflection_apply_self i₀)
    refine h.trans ?_
    simpa +instances only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root,
      rank, numRoots] using hr.symm
  have h6 : ∀ w, φ (D.rootSubgroupPoints (6 : Fin 12) A w) =
      E.g2SpecialIsogenyRootSubgroup A (6 : Fin 12) w := by
    have hr6 := href 0 6 (by simp only [g2Root_apply]; decide)
    simpa only [hs0, hr6] using hneg (0 : Fin 2)
  have h7 : ∀ w, φ (D.rootSubgroupPoints (7 : Fin 12) A w) =
      E.g2SpecialIsogenyRootSubgroup A (7 : Fin 12) w := by
    have hr7 := href 1 7 (by simp only [g2Root_apply]; decide)
    simpa only [hs1, hr7] using hneg (1 : Fin 2)
  obtain ⟨h2, h3, h4, h5⟩ := eq_quadruple_of_g2_half D E A φ
    (a := 0) (b := 1) (g := 2) (d := 3) (e := 4) (z := 5) (a' := 6) (l := 5) (m := 1) (s := 1)
    (by decide) (by simp only [g2Length_apply]; decide) (by simp only [g2Length_apply]; decide)
    (by simp only [g2Length_apply]; decide) (by simp only [g2Length_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide) h0 h1 h6
  obtain ⟨h8, h9, h10, h11⟩ := eq_quadruple_of_g2_half D E A φ
    (a := 6) (b := 7) (g := 8) (d := 9) (e := 10) (z := 11) (a' := 0) (l := 11) (m := 7) (s := -1)
    (by decide) (by simp only [g2Length_apply]; decide) (by simp only [g2Length_apply]; decide)
    (by simp only [g2Length_apply]; decide) (by simp only [g2Length_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2Root_apply]; decide) (by simp only [g2Root_apply]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide)
    (by simp only [g2StructureConstant_def]; decide) h6 h7 h0
  -- Expose `Fin 12` on `α` to dispatch the twelve roots to `h0` through `h11`.
  change Fin 12 at α
  fin_cases α
  · exact h0 u
  · exact h1 u
  · exact h2 u
  · exact h3 u
  · exact h4 u
  · exact h5 u
  · exact h6 u
  · exact h7 u
  · exact h8 u
  · exact h9 u
  · exact h10 u
  · exact h11 u

/-- Any endomorphism of `D.points A` matching `g2SpecialIsogenyRootSubgroup` on the signed simple
roots squares to `D.frobenius 3 1 A` on `D.elementarySubgroup A`. -/
theorem comp_self_eq_frobenius_of_g2SpecialIsogeny_simple
    (φ : D.points A →* D.points A)
    (hpos : ∀ i u, φ (D.rootSubgroupPoints (G2.simpleIndex ht i) A u) =
      D.g2SpecialIsogenyRootSubgroup A (G2.simpleIndex ht i) u)
    (hneg : ∀ i u, φ (D.rootSubgroupPoints
        ((G2.simplyConnectedRootDatum ht).reflectionPerm
          (G2.simpleIndex ht i) (G2.simpleIndex ht i)) A u) =
      D.g2SpecialIsogenyRootSubgroup A
        ((G2.simplyConnectedRootDatum ht).reflectionPerm
          (G2.simpleIndex ht i) (G2.simpleIndex ht i)) u)
    {g : D.points A} (hg : g ∈ D.elementarySubgroup A) :
    φ (φ g) = D.frobenius 3 1 A g := by
  have hall := map_rootSubgroupPoints_of_g2SpecialIsogeny_simple D D A φ hpos hneg
  refine (D.elementarySubgroup_le_iff A ((φ.comp φ).eqLocus (D.frobenius 3 1 A))).mpr
    (fun α u => ?_) hg
  -- Membership in `MonoidHom.eqLocus` unfolds to pointwise equality of the two homomorphisms.
  change φ (φ (D.rootSubgroupPoints α A u)) = D.frobenius 3 1 A (D.rootSubgroupPoints α A u)
  rw [← ofAdd_toAdd u, hall, g2SpecialIsogenyRootSubgroup_ofAdd,
    hall (g2SpecialIsogeny.indexEquiv α), g2SpecialIsogenyRootSubgroup_comp_self]

end G2

end TauCeti.DynkinType.ChevalleyDatum
