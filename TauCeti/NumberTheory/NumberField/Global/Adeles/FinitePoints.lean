/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Discrete
import TauCeti.Topology.Algebra.Group.Cocompact

/-!
# Finitely many rational points in adelic compact sets

A compact set of adeles contains only finitely many elements of the diagonal number field.
Consequently, imposing a compact condition at the finite places and a uniform bound at every
infinite place gives a finite set of field elements. These statements allow adelic lattice
conditions and archimedean bounds to be used independently in counting arguments.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- A compact set of adeles contains only finitely many diagonal field elements. -/
theorem finite_preimage_algebraMap_adeleRing {s : Set 𝔸[K]} (hs : IsCompact s) :
    ((algebraMap K 𝔸[K]) ⁻¹' s).Finite := by
  let f : K → AdeleRing.principalSubgroup (𝓞 K) K :=
    fun x ↦ ⟨algebraMap K 𝔸[K] x, ⟨x, rfl⟩⟩
  have hf : Function.Injective f := fun x y h ↦
    (AdeleRing.algebraMap_injective (𝓞 K) K) (congrArg Subtype.val h)
  exact ((AdeleRing.principalSubgroup (𝓞 K) K).finite_preimage_coe_of_isCompact hs).preimage
    (f := f) hf.injOn

/-- A compact condition at the finite places and a bound at every infinite place cut out
finitely many elements of a number field. No integrality condition is required. -/
theorem finite_setOf_infinitePlace_le_and_finiteAdele_mem {s : Set 𝔸ᶠ[K]}
    (hs : IsCompact s) (B : ℝ) :
    {x : K | (∀ w : InfinitePlace K, w x ≤ B) ∧ algebraMap K 𝔸ᶠ[K] x ∈ s}.Finite := by
  let t : Set (InfiniteAdeleRing K) := {a | ∀ w, ‖a w‖ ≤ B}
  have ht : IsCompact t := by
    refine isCompact_pi_infinite
      (s := fun w : InfinitePlace K ↦ {a : w.Completion | ‖a‖ ≤ B}) fun w ↦ ?_
    have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
    have hset : {a : w.Completion | ‖a‖ ≤ B} =
        InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall 0 B := by
      ext a
      rw [Set.mem_ofPred_eq, Set.mem_preimage, mem_closedBall_zero_iff,
        hi.norm_map_of_map_zero (map_zero _)]
    rw [hset]
    exact hi.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 B)
  have h := finite_preimage_algebraMap_adeleRing (ht.prod hs)
  apply h.subset
  intro x hx
  exact ⟨fun w ↦ by
    simpa only [AdeleRing.algebraMap_fst_apply, InfiniteAdeleRing.algebraMap_apply,
      ← InfinitePlace.Completion.algebraMap_apply_eq_coe,
      InfinitePlace.Completion.norm_algebraMap] using hx.1 w,
    by simpa only [AdeleRing.algebraMap_snd_def] using hx.2⟩

/-- A compact condition on finite adelic vectors and coordinate bounds at all infinite places
cut out finitely many rational vectors. -/
theorem finite_setOf_infinitePlace_le_and_finiteAdele_vector_mem
    {ι : Type*} [Finite ι] {s : Set (ι → 𝔸ᶠ[K])} (hs : IsCompact s) (B : ℝ) :
    {x : ι → K | (∀ i (w : InfinitePlace K), w (x i) ≤ B) ∧
      (fun i ↦ algebraMap K 𝔸ᶠ[K] (x i)) ∈ s}.Finite := by
  have h (i : ι) := finite_setOf_infinitePlace_le_and_finiteAdele_mem
    (hs.image (continuous_apply i)) B
  refine (Set.Finite.pi' h).subset fun x hx i ↦ ⟨hx.1 i, ?_⟩
  exact ⟨_, hx.2, rfl⟩

end TauCeti.GlobalNumberFields
