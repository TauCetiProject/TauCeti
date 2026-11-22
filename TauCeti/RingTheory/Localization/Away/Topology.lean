/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# The localized `(t, I)`-adic topology

The localization `R[1/t]` carries a ring topology with basic neighborhoods of zero the
additive images of `tⁿ I`. These are not extended ideals: extending an ideal would invert
the parameter and destroy the filtration. For `I = ⊤` this is the topology used to make
`R[1/t]` a Tate ring, with neighborhoods at zero the images of the powers of `(t)` in `R`.
For `I = ⊥` the topology is discrete; for a unit `t` and `I = ⊤` it is indiscrete.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §5.4, Definitions 5.4.10–5.4.11
  and §5.4.15.
-/

public section

open Filter Topology

namespace TauCeti

variable {R : Type*} [CommRing R] (t : R) (I : Ideal R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- The additive image of `tⁿ I` in the localization, without extension of ideals. -/
def localizedSubgroup (n : ℕ) : AddSubgroup S :=
  (Ideal.span {t} ^ n * I).toAddSubgroup.map (algebraMap R S).toAddMonoidHom

/-- Membership in a localized basic subgroup is represented by an element of `tⁿ I`. -/
@[simp]
theorem mem_localizedSubgroup (n : ℕ) (x : S) :
    x ∈ localizedSubgroup t I S n ↔
      ∃ a ∈ Ideal.span {t} ^ n * I, algebraMap R S a = x := Iff.rfl

/-- Equivalently, a basic subgroup consists of the images of the products `tⁿ a`, `a ∈ I`. -/
theorem mem_localizedSubgroup_iff (n : ℕ) (x : S) :
    x ∈ localizedSubgroup t I S n ↔
      ∃ a ∈ I, algebraMap R S (t ^ n * a) = x := by
  simp only [mem_localizedSubgroup, Ideal.span_singleton_pow, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨t ^ n * a, ⟨a, ha, rfl⟩, h⟩

/-- With the total ideal, the zeroth basic subgroup is the image of the base ring. -/
theorem coe_localizedSubgroup_zero_top :
    (localizedSubgroup t (⊤ : Ideal R) S 0 : Set S) = Set.range (algebraMap R S) := by
  ext x
  simp

/-- The localized subgroups decrease with the exponent. -/
theorem localizedSubgroup_antitone : Antitone (localizedSubgroup t I S) := fun _ _ h ↦
  AddSubgroup.map_mono (Ideal.mul_mono_left (Ideal.pow_le_pow_right h))

/-- Multiplication by the image of `tᵏ a` sends the `n`-th subgroup into the `(n + k)`-th. -/
theorem algebraMap_pow_mul_mul_mem_localizedSubgroup {n k : ℕ} (a : R) {x : S}
    (hx : x ∈ localizedSubgroup t I S n) :
    algebraMap R S (t ^ k * a) * x ∈ localizedSubgroup t I S (n + k) := by
  obtain ⟨b, hb, rfl⟩ := (mem_localizedSubgroup_iff t I S n x).mp hx
  refine (mem_localizedSubgroup_iff t I S (n + k) _).mpr ⟨a * b, I.mul_mem_left a hb, ?_⟩
  rw [← map_mul, pow_add]
  congr 1
  ring

/-- Each basic subgroup is closed under multiplication. -/
theorem mul_mem_localizedSubgroup {n : ℕ} {x y : S} (hx : x ∈ localizedSubgroup t I S n)
    (hy : y ∈ localizedSubgroup t I S n) : x * y ∈ localizedSubgroup t I S n := by
  obtain ⟨a, _, rfl⟩ := (mem_localizedSubgroup_iff t I S n x).mp hx
  exact localizedSubgroup_antitone t I S (Nat.le_add_right n n)
    (algebraMap_pow_mul_mul_mem_localizedSubgroup t I S a hy)

variable [IsLocalization.Away t S]

private theorem localizedSubgroupsBasis : RingSubgroupsBasis (localizedSubgroup t I S) :=
  .of_comm _
    (fun m n ↦ ⟨max m n, le_inf
      (localizedSubgroup_antitone t I S (le_max_left _ _))
      (localizedSubgroup_antitone t I S (le_max_right _ _))⟩)
    (fun n ↦ ⟨n, by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact mul_mem_localizedSubgroup t I S hx hy⟩)
    (fun x n ↦ by
      obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj t x
      refine ⟨n + k, ?_⟩
      intro y hy
      obtain ⟨b, hb, rfl⟩ := (mem_localizedSubgroup_iff t I S (n + k) y).mp hy
      apply (mem_localizedSubgroup_iff t I S n _).mpr
      refine ⟨a * b, I.mul_mem_left a hb, ?_⟩
      simp only [map_mul, map_pow, pow_add]
      rw [← ha]
      ring)

/-- The topology on `R[1/t]` whose basic neighborhoods of zero are the additive images
of `tⁿ I`. The ring `S` can be any model of this localization. -/
@[instance_reducible]
def localizedTopology : TopologicalSpace S :=
  (localizedSubgroupsBasis t I S).topology

/-- The localized filtration defines a topological ring. -/
theorem localizedTopology_isTopologicalRing :
    @IsTopologicalRing S (localizedTopology t I S) _ :=
  (localizedSubgroupsBasis t I S).toRingFilterBasis.isTopologicalRing

/-- The localized topology has a basis of open additive subgroups at zero. -/
theorem nonarchimedeanRing_localizedTopology :
    @NonarchimedeanRing S _ (localizedTopology t I S) :=
  (localizedSubgroupsBasis t I S).nonarchimedean

/-- Basic neighborhoods at any point are its cosets modulo the additive images of `tⁿ I`. -/
theorem hasBasis_nhds_localizedTopology (a : S) :
    (@nhds S (localizedTopology t I S) a).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ {b | b - a ∈ localizedSubgroup t I S n}) :=
  (localizedSubgroupsBasis t I S).hasBasis_nhds a

/-- At zero, the localized subgroups themselves form a neighborhood basis. -/
theorem hasBasis_nhds_zero_localizedTopology :
    (@nhds S (localizedTopology t I S) 0).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (localizedSubgroup t I S n : Set S)) :=
  (localizedSubgroupsBasis t I S).hasBasis_nhds_zero

/-- Each additive image of `tⁿ I` is open in the localized topology. -/
theorem isOpen_localizedSubgroup (n : ℕ) :
    IsOpen[localizedTopology t I S] (localizedSubgroup t I S n : Set S) := by
  let := localizedTopology t I S
  exact ((localizedSubgroupsBasis t I S).openAddSubgroup n).isOpen

/-- With the zero ideal, the localized topology is discrete. -/
@[simp]
theorem localizedTopology_bot : localizedTopology t (⊥ : Ideal R) S = ⊥ := by
  let := localizedTopology t (⊥ : Ideal R) S
  have : DiscreteTopology S := discreteTopology_iff_singleton_mem_nhds.mpr fun a ↦
    (hasBasis_nhds_localizedTopology t ⊥ S a).mem_iff.mpr
      ⟨0, trivial, by simp [eq_comm, sub_eq_zero]⟩
  exact DiscreteTopology.eq_bot

/-- For a unit `t` and the total ideal, the localized topology is indiscrete. -/
theorem localizedTopology_top_of_isUnit (ht : IsUnit t) :
    localizedTopology t (⊤ : Ideal R) S = ⊤ := by
  apply TopologicalSpace.ext_nhds
  intro a
  rw [nhds_top]
  apply (hasBasis_nhds_localizedTopology t ⊤ S a).eq_top_iff.mpr
  intro n _
  apply Set.eq_univ_of_forall
  intro b
  obtain ⟨c, hc⟩ := (IsLocalization.atUnit R S t ht).surjective (b - a)
  exact (mem_localizedSubgroup t ⊤ S n _).mpr
    ⟨c, by simp [Ideal.span_singleton_eq_top.mpr ht, Ideal.top_pow], hc⟩

/-- With parameter `1` and the total ideal, the localized topology is indiscrete. -/
@[simp]
theorem localizedTopology_one_top (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away (1 : R) S] : localizedTopology (1 : R) (⊤ : Ideal R) S = ⊤ :=
  localizedTopology_top_of_isUnit 1 S isUnit_one

end TauCeti
