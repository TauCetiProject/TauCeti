/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Approximation.Completion
public import TauCeti.RingTheory.Localization.Away.Topology

/-!
# Comparison with the localized `(t, I)`-adic topology

The localization map `R → R[1/t]` is continuous and open for the `(t, I)`-adic and
localized `(t, I)`-adic topologies. If it is injective, it is an open embedding. To test
continuity of an additive homomorphism from `R[1/t]` into a target with continuous
addition, it suffices to test its composite with the localization map.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §5.4, Definitions 5.4.10–5.4.11
  and §5.4.15.
-/

public section

open Filter Topology

namespace TauCeti.HenselianApproximation

variable {R : Type*} [CommRing R] (t : R) (I : Ideal R)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away t S]

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
  simp only [Set.mem_ofPred_eq, mem_localizedSubgroup, ← filtrationIdeal_def]
  exact ⟨b - a, hb, map_sub _ _ _⟩

/-- The localization map is open, even when it has a kernel. -/
theorem isOpenMap_algebraMap_localizedTopology :
    @IsOpenMap R S (ringTopology t I) (localizedTopology t I S) (algebraMap R S) := by
  let := ringTopology t I
  let := localizedTopology t I S
  have := ringTopology_isTopologicalRing t I
  have := localizedTopology_isTopologicalRing t I S
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero (f := algebraMap R S)]
  apply ((hasBasis_nhds_zero_localizedTopology t I S).le_basis_iff
    ((hasBasis_nhds_ringTopology t I 0).map (algebraMap R S))).mpr
  intro n _
  refine ⟨n, trivial, fun x hx ↦ ?_⟩
  rw [SetLike.mem_coe, mem_localizedSubgroup, ← filtrationIdeal_def] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, by simpa using ha, rfl⟩

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

/-- An additive homomorphism out of the localization into a space with continuous addition
is continuous exactly when its composite with the localization map is continuous. -/
theorem continuous_localizedTopology_iff {A F : Type*} [TopologicalSpace A]
    [AddZeroClass A] [ContinuousAdd A] [FunLike F S A] [AddMonoidHomClass F S A] (f : F) :
    Continuous[localizedTopology t I S, _] f ↔
      Continuous[ringTopology t I, _] (f ∘ algebraMap R S) := by
  let := ringTopology t I
  let := localizedTopology t I S
  have := localizedTopology_isTopologicalRing t I S
  constructor
  · intro hf
    exact hf.comp (continuous_algebraMap_localizedTopology t I S)
  · intro hf
    refine continuous_of_continuousAt_zero f ?_
    have h0 : Tendsto f (Filter.map (algebraMap R S) (𝓝 0)) (𝓝 (f 0)) := by
      rw [tendsto_map'_iff]
      simpa only [ContinuousAt, Function.comp_apply, map_zero] using
        hf.continuousAt (x := (0 : R))
    have hle := (isOpenMap_algebraMap_localizedTopology t I S).nhds_le 0
    rw [map_zero] at hle
    exact h0.mono_left hle

end TauCeti.HenselianApproximation
