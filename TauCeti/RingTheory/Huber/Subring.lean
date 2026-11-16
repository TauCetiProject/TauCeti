/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.Basic
import TauCeti.RingTheory.Huber.RingOfDefinition

/-!
# Subrings of Huber and Tate rings

This file studies subrings `S` of a Huber or Tate ring `R`, equipped with the subspace topology:

* Every element of `S` that is power-bounded in `R` is power-bounded in `S`
  (`Subring.isPowerBounded_of_coe`).
* If `S` contains a pseudouniformiser `u` of a Huber ring `R` (even without containing `u⁻¹`), a
  subset of `S` is bounded in `S` if and only if its image is bounded in `R`
  (`Subring.isBounded_image_subtype_iff`), so an element of `S` is power-bounded in `S` iff it is
  power-bounded in `R` (`Subring.isPowerBounded_coe_iff`, `Subring.powerBoundedSubring_eq_comap`).
* If `S` contains a pseudouniformiser and its inverse, then `S` is a Tate ring
  (`Subring.isTateRing_of_isPseudoUniformizer`), and intersecting any ring of definition of `R`
  with `S` yields a ring of definition of `S` (`Subring.exists_pairOfDefinition_comap`).

## Main results

* `Subring.isPowerBounded_of_coe`: power-boundedness in `R` implies power-boundedness in `S`.
* `Subring.isBounded_image_subtype_iff`: boundedness in `S` agrees with boundedness in `R` when
  `S` contains a pseudouniformiser of `R`.
* `Subring.isPowerBounded_coe_iff`, `Subring.powerBoundedSubring_eq_comap`: `S° = R° ∩ S` when
  `S` contains a pseudouniformiser of `R`.
* `Subring.isTateRing_of_isPseudoUniformizer`: a subring containing a pseudouniformiser as a unit
  is a Tate ring.
* `Subring.exists_pairOfDefinition_comap`: intersecting a ring of definition of `R` with a Huber
  subring `S` produces a ring of definition of `S`.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace Subring

section General

variable {R : Type*} [Ring R] [TopologicalSpace R]

/-- An element of a subring that is power-bounded in the ambient ring is power-bounded in the
subring (for the subspace topology). -/
theorem isPowerBounded_of_coe (S : Subring R) {x : S} (hx : IsPowerBounded (x : R)) :
    IsPowerBounded x := by
  refine isPowerBounded_iff.mpr <|
    (S.isBounded_preimage_subtype (isPowerBounded_iff.mp hx)).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

end General

section Huber

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]

/-- **Boundedness in a subring containing a pseudouniformiser agrees with ambient boundedness.**
Let `S` be a subring of a Huber ring `R` containing a pseudouniformiser `u` of `R` (the inverse
`u⁻¹` need not lie in `S`). Then a subset `T ⊆ S` is bounded in `S` if and only if its image is
bounded in `R`. -/
theorem isBounded_image_subtype_iff (S : Subring R) (u : Rˣ) (hu : IsPseudoUniformizer u.val)
    (hmem : u.val ∈ S) {T : Set S} :
    IsBounded (Subtype.val '' T) ↔ IsBounded T := by
  refine ⟨fun h ↦ (S.isBounded_preimage_subtype h).subset (Set.subset_preimage_image _ _),
    fun hT ↦ ?_⟩
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  obtain ⟨V, hV, hVT⟩ := (TauCeti.Huber.isBounded_iff.mp hT)
    (Subtype.val ⁻¹' (P.ringOfDefinition : Set R))
    ((P.isOpen_ringOfDefinition.preimage continuous_subtype_val).mem_nhds
      P.ringOfDefinition.zero_mem)
  obtain ⟨m, hm⟩ := (isTopologicallyNilpotent_mk hmem hu.isTopologicallyNilpotent).eventually_mem
    hV |>.exists
  have hmul : ∀ t ∈ T, u.val ^ m * (t : R) ∈ P.ringOfDefinition := fun t ht ↦ by
    have h := hVT (Set.mul_mem_mul hm ht)
    simpa [Subring.coe_mul, Subring.coe_pow] using h
  rw [TauCeti.Huber.isBounded_iff]
  intro U hU
  obtain ⟨W, hW, hWP⟩ := (TauCeti.Huber.isBounded_iff.mp P.isBounded_ringOfDefinition) U hU
  refine ⟨(fun r : R ↦ r * ((u⁻¹).val ^ m)) ⁻¹' W,
    (continuous_mul_const _).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
  rintro _ ⟨w, hw, _, ⟨t, ht, rfl⟩, rfl⟩
  have hrewrite : w * (t : R) = (w * (u⁻¹).val ^ m) * (u.val ^ m * (t : R)) := by
    calc w * (t : R) = w * (((u⁻¹).val * u.val) ^ m * (t : R)) := by simp
      _ = (w * (u⁻¹).val ^ m) * (u.val ^ m * (t : R)) := by rw [mul_pow]; ring
  dsimp only
  rw [hrewrite]
  exact hWP (Set.mul_mem_mul hw (hmul t ht))

/-- In a subring `S` containing a pseudouniformiser of a Huber ring `R`, an element is
power-bounded in `S` if and only if it is power-bounded in `R`. -/
theorem isPowerBounded_coe_iff (S : Subring R) (u : Rˣ) (hu : IsPseudoUniformizer u.val)
    (hmem : u.val ∈ S) {x : S} :
    IsPowerBounded (x : R) ↔ IsPowerBounded x := by
  have hset : Set.range ((x : R) ^ · : ℕ → R) = Subtype.val '' Set.range (x ^ · : ℕ → S) := by
    rw [← Set.range_comp]
    exact congrArg Set.range <| funext fun n ↦ (SubmonoidClass.coe_pow x n).symm
  rw [isPowerBounded_iff, isPowerBounded_iff, hset, S.isBounded_image_subtype_iff u hu hmem]

/-- In a subring `S` containing a pseudouniformiser of a Huber ring `R`, the power-bounded
subring of `S` is `R° ∩ S`. -/
theorem powerBoundedSubring_eq_comap (S : Subring R) (u : Rˣ) (hu : IsPseudoUniformizer u.val)
    (hmem : u.val ∈ S) :
    powerBoundedSubring S = (powerBoundedSubring R).comap S.subtype := by
  ext x
  simp [mem_powerBoundedSubring, S.isPowerBounded_coe_iff u hu hmem]

omit [IsHuberRing R] in
/-- Intersecting any ring of definition of a ring `R` with a Huber subring `S` gives a ring of
definition of `S`. -/
theorem exists_pairOfDefinition_comap (S : Subring R) [IsHuberRing S] (P : PairOfDefinition R) :
    ∃ Q : PairOfDefinition S, Q.ringOfDefinition = P.ringOfDefinition.comap S.subtype :=
  exists_pairOfDefinition_ringOfDefinition_eq (P.ringOfDefinition.comap S.subtype)
    (P.isOpen_ringOfDefinition.preimage continuous_subtype_val)
    (S.isBounded_preimage_subtype P.isBounded_ringOfDefinition)

/-- A subring containing a pseudouniformiser as a unit is a Tate ring in its subspace topology.
The unit hypothesis says that the inverse also lies in the subring. -/
theorem isTateRing_of_isPseudoUniformizer (S : Subring R) (u : Rˣ)
    (hu : IsPseudoUniformizer u.val) (hmem : u.val ∈ S) (hinv : (u⁻¹).val ∈ S) :
    IsTateRing S := by
  let v : Sˣ := Units.mkOfMulEqOne ⟨u.val, hmem⟩ ⟨(u⁻¹).val, hinv⟩ (Subtype.ext u.val_inv)
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  exact IsTateRing.of_isOpen_isBounded (P.ringOfDefinition.comap S.subtype)
    (P.isOpen_ringOfDefinition.preimage continuous_subtype_val)
    (S.isBounded_preimage_subtype P.isBounded_ringOfDefinition)
    (isPseudoUniformizer_iff.mpr ⟨v.isUnit,
      isTopologicallyNilpotent_mk hmem hu.isTopologicallyNilpotent⟩)

end Huber

end Subring
