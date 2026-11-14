/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Finsupp.Defs
import TauCeti.Analysis.Complex.RootsOfUnity.Circle
import TauCeti.Topology.Algebra.Group.Perm
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.UnitProOrder
import TauCeti.Topology.Algebra.Group.Profinite.UnitProOrder

/-!
# Examples and counterexamples for groups of invertible pro-order

This file exercises `TauCeti.HasUnitProOrder` and `TauCeti.HasCofinalUnitProOrder` across finite,
discrete, connected, pro-`p`, and locally profinite groups, and witnesses the sharpness of the
topological hypotheses in the main theorems:

* `Multiplicative ℤ_[p]` has invertible (and cofinal invertible) pro-order in `A` if and only if
  `IsUnit (p : A)`; in particular it holds over `ℚ` and `ZMod ℓ` (`ℓ ≠ p`) and fails over
  `ZMod p`, even though its trivial subgroup `⊥` is compact and has invertible pro-order in
  `ZMod p` (failing openness).
* Finite discrete groups have invertible pro-order in `A` if and only if `IsUnit (Nat.card U : A)`,
  yet every discrete group has cofinal invertible pro-order in every semiring via `{1}`.
* The infinite discrete `2`-torsion group `Multiplicative (ℕ →₀ ZMod 2)` satisfies `IsProP 2` while
  failing `HasUnitProOrder ℚ`, showing that compactness cannot be omitted from
  `TauCeti.IsProP.hasUnitProOrder`.
* The connected compact group `Circle` satisfies `HasUnitProOrder (ZMod p) Circle`, while its
  closed subgroup of `p`-th roots of unity fails `HasUnitProOrder (ZMod p)`, showing that total
  disconnectedness cannot be omitted from `TauCeti.HasUnitProOrder.subgroup`.
* Non-normal open subgroups of infinite non-abelian profinite groups (such as
  `⟨(0 1)⟩ × ℤ_[2] ≤ S₃ × ℤ_[2]` over `ZMod 5`) inherit invertible pro-order and have invertible
  index.
-/

namespace TauCeti

/-! ### 1. `p`-adic integers over various coefficient semirings -/

example (p : ℕ) [Fact p.Prime] (A : Type*) [Semiring A] :
    HasUnitProOrder A (Multiplicative ℤ_[p]) ↔ IsUnit (p : A) :=
  hasUnitProOrder_multiplicative_padicInt_iff p A

example (p : ℕ) [Fact p.Prime] : HasUnitProOrder ℚ (Multiplicative ℤ_[p]) :=
  hasUnitProOrder_of_algebra_rat

example (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ) :
    HasUnitProOrder (ZMod ℓ) (Multiplicative ℤ_[p]) := by
  rw [hasUnitProOrder_multiplicative_padicInt_iff]
  refine isUnit_iff_ne_zero.mpr fun h0 ↦ hpℓ ?_
  exact ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp
    ((ZMod.natCast_eq_zero_iff p ℓ).mp h0)).symm

example (p : ℕ) [Fact p.Prime] : ¬ HasUnitProOrder (ZMod p) (Multiplicative ℤ_[p]) :=
  not_hasUnitProOrder_zmod_multiplicative_padicInt p

/-! ### 2 & 3. Finite discrete groups and the trivial group -/

example (A : Type*) [Semiring A] (U : Type*) [Group U] [TopologicalSpace U] [DiscreteTopology U]
    [Finite U] : HasUnitProOrder A U ↔ IsUnit (Nat.card U : A) :=
  hasUnitProOrder_iff_isUnit_card

example (p : ℕ) [Fact p.Prime] : ¬ HasUnitProOrder (ZMod p) (Multiplicative (ZMod p)) := by
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr (Fact.out : p.Prime).ne_one
  rw [hasUnitProOrder_iff_isUnit_card, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    ZMod.natCast_self]
  exact not_isUnit_zero

example (A : Type*) [Semiring A] : HasUnitProOrder A PUnit :=
  hasUnitProOrder_of_subsingleton

/-! ### 4. Compactness is essential in `IsProP.hasUnitProOrder` -/

example :
    letI : TopologicalSpace (Multiplicative (ℕ →₀ ZMod 2)) := ⊥
    IsProP 2 (Multiplicative (ℕ →₀ ZMod 2)) ∧ IsUnit (2 : ℚ) ∧
      ¬ HasUnitProOrder ℚ (Multiplicative (ℕ →₀ ZMod 2)) := by
  let _ : TopologicalSpace (Multiplicative (ℕ →₀ ZMod 2)) := ⊥
  have : DiscreteTopology (Multiplicative (ℕ →₀ ZMod 2)) := ⟨rfl⟩
  refine ⟨isProP_iff.mpr fun N x ↦ ?_, isUnit_natCast_of_ne_zero (by decide), ?_⟩
  · obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective N.toSubgroup x
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    have hv : v ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      ext n
      simp only [Finsupp.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        Finsupp.coe_zero, Pi.zero_apply]
    rw [hv, map_one]
  · rw [hasUnitProOrder_iff_isUnit_card]
    have : Infinite (ℕ →₀ ZMod 2) :=
      Infinite.of_injective (fun n : ℕ ↦ Finsupp.single n (1 : ZMod 2))
        (Finsupp.single_left_injective one_ne_zero)
    have : Infinite (Multiplicative (ℕ →₀ ZMod 2)) :=
      Infinite.of_injective Multiplicative.ofAdd Multiplicative.ofAdd.injective
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero]
    exact not_isUnit_zero

/-! ### 5. Total disconnectedness is essential in `HasUnitProOrder.subgroup` -/

example (p : ℕ) [Fact p.Prime] :
    let μp : Subgroup Circle := (powMonoidHom p : Circle →* Circle).ker
    HasUnitProOrder (ZMod p) Circle ∧ IsClosed (μp : Set Circle) ∧
      DiscreteTopology μp ∧ ¬ HasUnitProOrder (ZMod p) μp := by
  intro μp
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr (Fact.out : p.Prime).ne_one
  have hclosed : IsClosed (μp : Set Circle) := by
    have hset : (μp : Set Circle) = (fun z : Circle ↦ z ^ p) ⁻¹' {1} := rfl
    rw [hset]
    exact isClosed_singleton.preimage (continuous_pow p)
  have hbij : Function.Bijective
      (fun j : ZMod p ↦ (⟨ZMod.toCircle j, ZMod.toCircle_pow_eq_one j⟩ : μp)) :=
    ⟨fun i j h ↦ ZMod.injective_toCircle (Subtype.ext_iff.mp h), fun ⟨ζ, hζ⟩ ↦
      let ⟨j, hj⟩ := ZMod.exists_toCircle_eq_of_pow_eq_one hζ
      ⟨j, Subtype.ext hj⟩⟩
  let e : ZMod p ≃ μp := Equiv.ofBijective _ hbij
  have : Finite μp := Finite.of_equiv (ZMod p) e
  have : DiscreteTopology μp := inferInstance
  refine ⟨hasUnitProOrder_of_preconnectedSpace, hclosed, inferInstance, ?_⟩
  rw [hasUnitProOrder_iff_isUnit_card, ← Nat.card_congr e, Nat.card_zmod, ZMod.natCast_self]
  exact not_isUnit_zero

/-! ### 6, 7 & 8. `HasCofinalUnitProOrder` on discrete groups and `ℤ_[p]` -/

example (A : Type*) [Semiring A] (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    HasCofinalUnitProOrder A G :=
  hasCofinalUnitProOrder_of_discreteTopology

example (p : ℕ) [Fact p.Prime] :
    HasCofinalUnitProOrder (ZMod p) (Multiplicative (ZMod p)) ∧
      ¬ HasUnitProOrder (ZMod p) (Multiplicative (ZMod p)) := by
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr (Fact.out : p.Prime).ne_one
  refine ⟨hasCofinalUnitProOrder_of_discreteTopology, ?_⟩
  rw [hasUnitProOrder_iff_isUnit_card, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    ZMod.natCast_self]
  exact not_isUnit_zero

example (p : ℕ) [Fact p.Prime] (A : Type*) [Semiring A] :
    HasCofinalUnitProOrder A (Multiplicative ℤ_[p]) ↔ IsUnit (p : A) :=
  hasCofinalUnitProOrder_multiplicative_padicInt_iff p A

example (p : ℕ) [Fact p.Prime] :
    let B : Subgroup (Multiplicative ℤ_[p]) := ⊥
    ¬ HasCofinalUnitProOrder (ZMod p) (Multiplicative ℤ_[p]) ∧
      IsCompact (B : Set (Multiplicative ℤ_[p])) ∧
      HasUnitProOrder (ZMod p) B ∧
      ¬ IsOpen (B : Set (Multiplicative ℤ_[p])) := by
  intro B
  refine ⟨not_hasCofinalUnitProOrder_zmod_multiplicative_padicInt p, ?_,
    hasUnitProOrder_of_subsingleton, fun hopen ↦ ?_⟩
  · rw [Subgroup.coe_bot]
    exact isCompact_singleton
  · rw [Subgroup.coe_bot] at hopen
    have : DiscreteTopology (Multiplicative ℤ_[p]) :=
      discreteTopology_iff_isOpen_singleton_one.mpr hopen
    exact not_hasCofinalUnitProOrder_zmod_multiplicative_padicInt p
      hasCofinalUnitProOrder_of_discreteTopology

/-! ### 9 & 10. Closed subgroups and non-normal open subgroups of profinite groups -/

example (A : Type*) [Semiring A] (K : Type*) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [TotallyDisconnectedSpace K]
    (H : Subgroup K) (hHc : IsClosed (H : Set K)) (hK : HasUnitProOrder A K) :
    CompactSpace H ∧ TotallyDisconnectedSpace H ∧ HasUnitProOrder A H :=
  ⟨isCompact_iff_compactSpace.mp hHc.isCompact, inferInstance, hK.subgroup H⟩

example :
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let H₀ : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.closure {Equiv.swap 0 1}
    let H : OpenSubgroup (Equiv.Perm (Fin 3) × Multiplicative ℤ_[2]) :=
      (OpenSubgroup.mk H₀ (isOpen_discrete _)).prod ⊤
    HasUnitProOrder (ZMod 5) (Equiv.Perm (Fin 3) × Multiplicative ℤ_[2]) ∧
      ¬ H.toSubgroup.Normal ∧
      HasUnitProOrder (ZMod 5) H ∧
      IsUnit (H.toSubgroup.index : ZMod 5) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro H₀ H
  have hU : HasUnitProOrder (ZMod 5) (Equiv.Perm (Fin 3) × Multiplicative ℤ_[2]) := by
    rw [hasUnitProOrder_prod_iff, hasUnitProOrder_iff_isUnit_card,
      hasUnitProOrder_multiplicative_padicInt_iff, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    exact ⟨⟨⟨1, 1, by decide, by decide⟩, by decide⟩, ⟨⟨2, 3, by decide, by decide⟩, rfl⟩⟩
  have hnn : ¬ H.toSubgroup.Normal := by
    intro hnorm
    have hmem : (Equiv.swap 0 1, (1 : Multiplicative ℤ_[2])) ∈ H.toSubgroup :=
      ⟨Subgroup.subset_closure rfl, trivial⟩
    have hconj := (hnorm.conj_mem _ hmem (Equiv.swap 1 2, 1)).1
    have hle : H₀ ≤ MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3) :=
      (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
        (MulAction.mem_stabilizer_iff.mpr (by decide)))
    have hfix : (Equiv.swap 1 2 * Equiv.swap 0 1 * (Equiv.swap 1 2)⁻¹ : Equiv.Perm (Fin 3)) 2 = 2 :=
      hle hconj
    revert hfix
    decide
  exact ⟨hU, hnn, hU.openSubgroup H, hU.isUnit_index_openSubgroup H⟩

end TauCeti
