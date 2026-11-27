/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Infinite.Basic

/-!
# Rank stabilization of the infinite Grassmannian

The map `infiniteGrassmannian.rankStabilization` shifts a plane one coordinate to the right
and adjoins the first coordinate line. It extends `finiteGrassmannian.rankStabilization`
through `finiteGrassmannian.toInfinite` and preserves the standard basepoint. Over the reals
and complexes it is a closed embedding onto the planes containing the first coordinate line,
giving the transition maps for the stable Grassmannian tower.

The stable Grassmannian construction is described in Hatcher, *Vector Bundles and K-Theory*,
§1.2. We use Mathlib's `Finsupp.lcomapDomain` for deleting the first coordinate.
-/

public section

open Set Function Topology

namespace TauCeti

namespace finiteGrassmannian

variable {𝕜 : Type*} [Field 𝕜] {k n : ℕ}

/-- Taking the preimage under deletion of the first coordinate agrees with finite rank
stabilization followed by inclusion into the infinite coordinate space. -/
theorem coe_toInfinite_rankStabilization (V : finiteGrassmannian 𝕜 k n) :
    (V.rankStabilization.toInfinite).val =
      V.toInfinite.val.comap (Finsupp.lcomapDomain (R := 𝕜) Nat.succ Nat.succ_injective) := by
  ext v
  simp only [Submodule.mem_comap, mem_toInfinite, mem_rankStabilization,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply]
  rw [← Nat.and_forall_add_one (p := fun i ↦ n + 1 ≤ i → v i = 0)]
  simp only [Nat.add_one_le_iff, Nat.not_lt_zero, false_implies, true_and, Nat.lt_succ_iff]
  exact Iff.rfl

end finiteGrassmannian

namespace infiniteGrassmannian

open finiteGrassmannian (toInfinite single_mem_toInfinite_iff)

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ}

/-- Adjoin the first coordinate line to the shift of a plane by one coordinate. -/
noncomputable def rankStabilization (V : infiniteGrassmannian 𝕜 k) :
    infiniteGrassmannian 𝕜 (k + 1) :=
  ⟨V.val.comap (Finsupp.lcomapDomain (R := 𝕜) Nat.succ Nat.succ_injective), by
    obtain ⟨n, W, rfl⟩ := exists_toInfinite_eq V
    rw [← W.coe_toInfinite_rankStabilization]
    exact W.rankStabilization.toInfinite.property⟩

/-- The stabilized plane is the inverse image of the original plane under coordinate
deletion. This is the defining equation for rewrites with the unexposed map. -/
theorem coe_rankStabilization (V : infiniteGrassmannian 𝕜 k) :
    (V.rankStabilization).val =
      V.val.comap (Finsupp.lcomapDomain (R := 𝕜) Nat.succ Nat.succ_injective) := (rfl)

/-- Rank stabilization restricts to the native finite rank stabilization at every stage. -/
@[simp]
theorem rankStabilization_toInfinite {n : ℕ} (V : finiteGrassmannian 𝕜 k n) :
    V.toInfinite.rankStabilization = V.rankStabilization.toInfinite :=
  Subtype.ext V.coe_toInfinite_rankStabilization.symm

/-- Rank stabilization is injective, since deleting the first coordinate recovers the plane. -/
theorem rankStabilization_injective :
    Injective (rankStabilization : infiniteGrassmannian 𝕜 k → _) := by
  have hsurj : Surjective (Finsupp.lcomapDomain (R := 𝕜) (M := 𝕜)
      Nat.succ Nat.succ_injective) :=
    (Finsupp.leftInverse_lcomapDomain_mapDomain Nat.succ Nat.succ_injective).surjective
  intro V W h
  apply Subtype.ext
  apply Submodule.comap_injective_of_surjective hsurj
  simpa only [coe_rankStabilization] using congrArg Subtype.val h

/-- The image of rank stabilization consists of the planes containing the first coordinate
line. -/
@[simp]
theorem range_rankStabilization :
    range (rankStabilization : infiniteGrassmannian 𝕜 k → _) =
      {W | Finsupp.single 0 1 ∈ W.val} := by
  ext W
  constructor
  · rintro ⟨V, rfl⟩
    rw [Set.mem_ofPred_eq, coe_rankStabilization, Submodule.mem_comap, Finsupp.lcomapDomain_apply,
      Finsupp.comapDomain_single_of_notMem_range (by simp : 0 ∉ range Nat.succ)]
    exact V.val.zero_mem
  · intro hW
    obtain ⟨n, U, rfl⟩ := exists_toInfinite_eq W
    rw [Set.mem_ofPred_eq] at hW
    rw [← finiteGrassmannian.toInfinite_ambientStabilization U] at hW ⊢
    obtain ⟨V, hV⟩ := (finiteGrassmannian.mem_range_rankStabilization _).2
      ((single_mem_toInfinite_iff (i := 0)).1 hW)
    exact ⟨V.toInfinite, by rw [rankStabilization_toInfinite, hV]⟩

/-- The standard coordinate plane stabilizes to the next standard coordinate plane. -/
@[simp]
theorem rankStabilization_basepoint :
    (basepoint 𝕜 k).rankStabilization = basepoint 𝕜 (k + 1) := by
  apply Subtype.ext
  ext v
  simp only [coe_rankStabilization, Submodule.mem_comap, coe_basepoint, Finsupp.mem_supported',
    mem_Iio,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, not_lt]
  rw [← Nat.and_forall_add_one (p := fun i ↦ k + 1 ≤ i → v i = 0)]
  simp only [Nat.add_one_le_iff, Nat.not_lt_zero, false_implies, true_and, Nat.lt_succ_iff]

/-- The intersection of a stabilized image with the next finite stage is the finite
stabilization of the corresponding preimage. -/
theorem preimage_toInfinite_rankStabilization_image {n : ℕ}
    {C : Set (infiniteGrassmannian 𝕜 k)} :
    (toInfinite : finiteGrassmannian 𝕜 (k + 1) (n + 1) → _) ⁻¹' (rankStabilization '' C) =
      finiteGrassmannian.rankStabilization ''
        ((toInfinite : finiteGrassmannian 𝕜 k n → _) ⁻¹' C) := by
  ext W
  constructor
  · rintro ⟨V, hV, hVW⟩
    have hW : W.toInfinite ∈ range (rankStabilization : infiniteGrassmannian 𝕜 k → _) :=
      ⟨V, hVW⟩
    rw [range_rankStabilization] at hW
    obtain ⟨U, rfl⟩ := (finiteGrassmannian.mem_range_rankStabilization W).2
      ((single_mem_toInfinite_iff (i := 0)).1 hW)
    have heq : V.rankStabilization = U.toInfinite.rankStabilization :=
      hVW.trans (rankStabilization_toInfinite U).symm
    have hU : U.toInfinite ∈ C := rankStabilization_injective heq ▸ hV
    exact ⟨U, hU, rfl⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U.toInfinite, hU, rankStabilization_toInfinite U⟩

variable [TopologicalSpace 𝕜]

/-- Rank stabilization is continuous for the finite-stage final topologies. -/
theorem continuous_rankStabilization :
    Continuous (rankStabilization : infiniteGrassmannian 𝕜 k → _) := by
  refine continuous_iff.2 fun n ↦ ?_
  exact (finiteGrassmannian.continuous_toInfinite.comp
    finiteGrassmannian.continuous_rankStabilization).congr
    (fun V ↦ (rankStabilization_toInfinite V).symm)

/-- Over the real or complex numbers, rank stabilization is a closed embedding for the
finite-stage final topology. -/
theorem isClosedEmbedding_rankStabilization {𝕜 : Type*} [RCLike 𝕜] {k : ℕ} :
    IsClosedEmbedding (rankStabilization : infiniteGrassmannian 𝕜 k → _) := by
  have hclosed : IsClosedMap (rankStabilization : infiniteGrassmannian 𝕜 k → _) := by
    intro C hC
    refine isClosed_iff.2 fun n ↦ ?_
    cases n with
    | zero =>
      let := finiteGrassmannian.isEmpty_of_lt (𝕜 := 𝕜) (Nat.zero_lt_succ k)
      exact Set.Subsingleton.isClosed (fun W _ ↦ isEmptyElim W)
    | succ n =>
      rw [preimage_toInfinite_rankStabilization_image]
      exact finiteGrassmannian.isClosedEmbedding_rankStabilization.isClosedMap _
        (hC.preimage finiteGrassmannian.continuous_toInfinite)
  exact .of_continuous_injective_isClosedMap continuous_rankStabilization
    rankStabilization_injective hclosed

end infiniteGrassmannian

end TauCeti
