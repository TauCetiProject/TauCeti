/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Approximation.Completion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The localized `(t, I)`-adic topology

The localization `R[1/t]` carries a ring topology with basic neighborhoods of zero the
additive images of `tⁿ I`. These are not extended ideals: extending an ideal would invert
the parameter and destroy the filtration. This topology is the coefficient topology for
polynomial solution spaces in henselian approximation.

The localization map is continuous and open. If it is injective, it is an open embedding
for the `(t, I)`-adic topology on `R`. No regularity or henselianity is needed to construct
the topology. We also give a continuity criterion for maps out of the localization and
compute the zero-ideal and unit-parameter boundaries.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §5.4, Definitions 5.4.10–5.4.11
  and §5.4.15.
-/

public section

open Filter Topology

namespace TauCeti.HenselianApproximation

variable {R : Type*} [CommRing R] (t : R) (I : Ideal R)
  (S : Type*) [CommRing S] [Algebra R S]

/-- The additive image of `tⁿ I` in the localization, without extension of ideals. -/
def localizedSubgroup (n : ℕ) : AddSubgroup S :=
  (filtrationIdeal t I n).toAddSubgroup.map (algebraMap R S).toAddMonoidHom

/-- Membership in a localized basic subgroup is represented by an element of `tⁿ I`. -/
@[simp]
theorem mem_localizedSubgroup (n : ℕ) (x : S) :
    x ∈ localizedSubgroup t I S n ↔
      ∃ a ∈ filtrationIdeal t I n, algebraMap R S a = x := Iff.rfl

/-- Equivalently, a basic subgroup consists of the images of the products `tⁿ a`, `a ∈ I`. -/
theorem mem_localizedSubgroup_iff (n : ℕ) (x : S) :
    x ∈ localizedSubgroup t I S n ↔
      ∃ a ∈ I, algebraMap R S (t ^ n * a) = x := by
  simp only [mem_localizedSubgroup, filtrationIdeal_def, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨t ^ n * a, ⟨a, ha, rfl⟩, h⟩

/-- The localized subgroups decrease with the exponent. -/
theorem localizedSubgroup_antitone : Antitone (localizedSubgroup t I S) :=
  fun _ _ h ↦ AddSubgroup.map_mono (filtrationIdeal_antitone t I h)

variable [IsLocalization.Away t S]

private theorem localizedSubgroupsBasis : RingSubgroupsBasis (localizedSubgroup t I S) :=
  .of_comm _
    (fun m n ↦ ⟨max m n, le_inf
      (localizedSubgroup_antitone t I S (le_max_left _ _))
      (localizedSubgroup_antitone t I S (le_max_right _ _))⟩)
    (fun n ↦ ⟨n, by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      obtain ⟨a, _, rfl⟩ := (mem_localizedSubgroup t I S n x).mp hx
      obtain ⟨b, hb, rfl⟩ := (mem_localizedSubgroup t I S n y).mp hy
      exact (mem_localizedSubgroup t I S n _).mpr
        ⟨a * b, (filtrationIdeal t I n).mul_mem_left a hb, map_mul _ _ _⟩⟩)
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

/-- The localization map is continuous from the `(t, I)`-adic topology. -/
@[fun_prop]
theorem continuous_algebraMap_localizedTopology :
    Continuous[ringTopology t I, localizedTopology t I S] (algebraMap R S) := by
  let := ringTopology t I
  let := localizedTopology t I S
  rw [continuous_iff_continuousAt]
  intro a
  apply (hasBasis_nhds_ringTopology t I a).tendsto_iff
    (hasBasis_nhds_localizedTopology t I S (algebraMap R S a)) |>.mpr
  intro n _
  refine ⟨n, trivial, fun b hb ↦ ?_⟩
  exact (mem_localizedSubgroup t I S n _).mpr ⟨b - a, hb, map_sub _ _ _⟩

/-- The localization map is open, even when it has a kernel. -/
theorem isOpenMap_algebraMap_localizedTopology :
    @IsOpenMap R S (ringTopology t I) (localizedTopology t I S) (algebraMap R S) := by
  let := ringTopology t I
  let := localizedTopology t I S
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨n, _, hn⟩ := (hasBasis_nhds_ringTopology t I a).mem_iff.mp (hU.mem_nhds ha)
  apply (hasBasis_nhds_localizedTopology t I S _).mem_iff.mpr
  refine ⟨n, trivial, ?_⟩
  intro b hb
  obtain ⟨c, hc, hcb⟩ := (mem_localizedSubgroup t I S n _).mp hb
  refine ⟨c + a, hn (by simpa using hc), ?_⟩
  rw [map_add, hcb, sub_add_cancel]

/-- When the localization map is injective it identifies the original ring with an open
subspace of the localized ring, with exactly its `(t, I)`-adic topology. -/
theorem isOpenEmbedding_algebraMap_localizedTopology
    (hinj : Function.Injective (algebraMap R S)) :
    @Topology.IsOpenEmbedding R S (ringTopology t I) (localizedTopology t I S)
      (algebraMap R S) := by
  let := ringTopology t I
  let := localizedTopology t I S
  exact .of_continuous_injective_isOpenMap
    (continuous_algebraMap_localizedTopology t I S) hinj
    (isOpenMap_algebraMap_localizedTopology t I S)

/-- A homomorphism out of the localization is continuous exactly when its restriction to
`R` is continuous. It suffices to test continuity on the open image of `R`. -/
theorem continuous_localizedTopology_iff {A : Type*} [TopologicalSpace A]
    [AddZeroClass A] [ContinuousAdd A] (f : S →+ A) :
    Continuous[localizedTopology t I S, _] f ↔
      Continuous[ringTopology t I, _] (f.comp (algebraMap R S).toAddMonoidHom) := by
  let := ringTopology t I
  let := localizedTopology t I S
  let := ringTopology_isTopologicalRing t I
  let := localizedTopology_isTopologicalRing t I S
  constructor
  · intro hf
    exact hf.comp (continuous_algebraMap_localizedTopology t I S)
  · intro hf
    apply continuous_of_continuousAt_zero f
    rw [ContinuousAt, map_zero]
    intro U hU
    obtain ⟨n, _, hn⟩ := (hasBasis_nhds_ringTopology t I 0).mem_iff.mp
      (hf.continuousAt.preimage_mem_nhds (by simpa using hU))
    apply (hasBasis_nhds_zero_localizedTopology t I S).mem_iff.mpr
    refine ⟨n, trivial, ?_⟩
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_localizedSubgroup t I S n x).mp hx
    exact hn (by simpa using ha)

/-- With the zero ideal, the localized topology is discrete. -/
@[simp]
theorem localizedTopology_bot : localizedTopology t (⊥ : Ideal R) S = ⊥ := by
  let := localizedTopology t (⊥ : Ideal R) S
  have : DiscreteTopology S := discreteTopology_iff_singleton_mem_nhds.mpr fun a ↦
    (hasBasis_nhds_localizedTopology t ⊥ S a).mem_iff.mpr
      ⟨0, trivial, by simp [eq_comm, sub_eq_zero]⟩
  exact DiscreteTopology.eq_bot

/-- With unit parameter and total ideal, the localized topology is indiscrete. -/
@[simp]
theorem localizedTopology_one_top [IsLocalization.Away (1 : R) S] :
    localizedTopology (1 : R) (⊤ : Ideal R) S = ⊤ := by
  apply TopologicalSpace.ext_nhds
  intro a
  rw [nhds_top]
  apply (hasBasis_nhds_localizedTopology (1 : R) ⊤ S a).eq_top_iff.mpr
  intro n _
  apply Set.eq_univ_of_forall
  intro b
  obtain ⟨k, c, hc⟩ := IsLocalization.Away.surj (1 : R) (b - a)
  apply (mem_localizedSubgroup_iff (1 : R) ⊤ S n _).mpr
  exact ⟨c, by simp, by simpa using hc.symm⟩

end TauCeti.HenselianApproximation
