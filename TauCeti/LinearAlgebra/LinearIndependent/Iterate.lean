/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independent initial segments of an orbit

For any map `F : V → V` on a finite-dimensional vector space and a nonzero vector `v`, the orbit
`v, F v, F² v, …` cannot stay linearly independent forever. Its longest independent initial
segment `v, F v, …, Fⁿ v` therefore spans the next iterate `Fⁿ⁺¹ v`. No linearity of `F` is
assumed, so this applies to semilinear maps, such as Frobenius-semilinear ones.

For an injective `σ`-semilinear endomorphism `Φ` with `σ` surjective, the resulting linear
relation on `v, Φ v, …, Φⁿ⁺¹ v` must have nonzero constant term on `v`
(`LinearMap.exists_minimal_orbit_relation`), since otherwise `Φ` could be factored out by
injectivity.

## Main results

* `Function.exists_linearIndependent_iterate_mem_span`: some initial segment `v, …, Fⁿ v` of the
  orbit is linearly independent and spans `Fⁿ⁺¹ v`.
* `LinearMap.exists_minimal_orbit_relation`: for an injective semilinear endomorphism `Φ` with `σ`
  surjective, `Φⁿ⁺¹ v` satisfies a relation in `v, …, Φⁿ v` with nonzero coefficient at `v`.
-/

public section

open Function Submodule Module

namespace Function

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- For a map `F` and a nonzero vector `v` of a finite-dimensional space, some initial segment
`v, F v, …, Fⁿ v` of the orbit is linearly independent and spans `Fⁿ⁺¹ v`. -/
theorem exists_linearIndependent_iterate_mem_span [FiniteDimensional K V] (F : V → V) {v : V}
    (hv : v ≠ 0) :
    ∃ n, LinearIndependent K (fun i : Fin (n + 1) ↦ F^[i] v) ∧
      F^[n + 1] v ∈ span K (Set.range fun i : Fin (n + 1) ↦ F^[i] v) := by
  classical
  have key (m : ℕ) (h : ∀ j < m, F^[j] v ∉ span K (Set.range fun i : Fin j ↦ F^[i] v)) :
      LinearIndependent K (fun i : Fin m ↦ F^[i] v) := by
    induction m with
    | zero => exact linearIndependent_empty_type
    | succ m ih =>
      have hsnoc : (fun i : Fin (m + 1) ↦ F^[i] v) =
          Fin.snoc (fun i : Fin m ↦ F^[i] v) (F^[m] v) := by
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
      rw [hsnoc, linearIndependent_finSnoc]
      exact ⟨ih fun j hj ↦ h j (by omega), h m (by omega)⟩
  have hex : ∃ m, F^[m] v ∈ span K (Set.range fun i : Fin m ↦ F^[i] v) := by
    by_contra! h
    have := LinearIndependent.fintype_card_le_finrank (key (finrank K V + 1) fun j _ ↦ h j)
    simp at this
  obtain ⟨m, hm, hmin⟩ : ∃ m, F^[m] v ∈ span K (Set.range fun i : Fin m ↦ F^[i] v) ∧
      ∀ j < m, F^[j] v ∉ span K (Set.range fun i : Fin j ↦ F^[i] v) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ Nat.find_min hex hj⟩
  obtain _ | n := m
  · simp [hv] at hm
  · exact ⟨n, key _ hmin, hm⟩

end Function

namespace LinearMap

/-- For an injective `σ`-semilinear endomorphism `Φ` of a finite-dimensional vector space with `σ`
surjective, any nonzero vector `v₀` admits a longest linearly independent orbit segment
`v₀, Φ v₀, …, Φⁿ v₀` whose next iterate `Φⁿ⁺¹ v₀` satisfies a linear relation with nonzero
coefficient at `v₀`. -/
theorem exists_minimal_orbit_relation {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {σ : K →+* K} [RingHomSurjective σ]
    {Φ : V →ₛₗ[σ] V} (hΦ : Injective Φ) {v₀ : V} (hv₀ : v₀ ≠ 0) :
    ∃ (n : ℕ) (a : Fin (n + 1) → K),
      LinearIndependent K (fun i : Fin (n + 1) ↦ Φ^[i.val] v₀) ∧
      Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0 ∧
      a 0 ≠ 0 := by
  obtain ⟨n, hli, hmem⟩ := Function.exists_linearIndependent_iterate_mem_span (K := K) Φ hv₀
  have hneg : -Φ^[n + 1] v₀ ∈ span K (Set.range fun i : Fin (n + 1) ↦ Φ^[i.val] v₀) :=
    Submodule.neg_mem _ hmem
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hneg
  obtain ⟨c, hc⟩ := hneg
  let a : Fin (n + 1) → K := fun i ↦ c i
  have hrel : Φ^[n + 1] v₀ + ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ = 0 := by
    rw [Finsupp.sum_fintype c (fun i x ↦ x • Φ^[i.val] v₀) (fun i ↦ zero_smul K _)] at hc
    rw [show (∑ i, a i • Φ^[i.val] v₀) = ∑ i, c i • Φ^[i.val] v₀ from rfl, hc, add_neg_cancel]
  refine ⟨n, a, hli, hrel, fun ha0 ↦ ?_⟩
  -- If `a 0 = 0`, pulling `a j.succ` back along `σ` gives a shorter relation by injectivity of `Φ`.
  have hsplit : ∑ i : Fin (n + 1), a i • Φ^[i.val] v₀ =
      ∑ j : Fin n, a j.succ • Φ^[j.val + 1] v₀ := by
    rw [Fin.sum_univ_succ, ha0, zero_smul, zero_add]
    simp [Fin.val_succ]
  choose b hb using fun j : Fin n ↦ RingHomSurjective.is_surjective (σ := σ) (a j.succ)
  have hΦeq : Φ (Φ^[n] v₀ + ∑ j : Fin n, b j • Φ^[j.val] v₀) = 0 := by
    rw [map_add, map_sum, ← iterate_succ_apply' Φ]
    have hsum : (∑ j : Fin n, Φ (b j • Φ^[j.val] v₀)) =
        ∑ j : Fin n, a j.succ • Φ^[j.val + 1] v₀ :=
      Finset.sum_congr rfl fun j _ ↦ by
        rw [map_smulₛₗ, hb j, ← iterate_succ_apply' Φ]
    rw [hsum, ← hsplit]
    exact hrel
  have hinner := hΦ (hΦeq.trans (map_zero Φ).symm)
  let c' : Fin (n + 1) → K := Fin.snoc b 1
  have hsum' : ∑ i : Fin (n + 1), c' i • Φ^[i.val] v₀ = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [c', Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, one_smul]
    rw [add_comm, hinner]
  simpa [c'] using Fintype.linearIndependent_iff.1 hli c' hsum' (Fin.last n)

end LinearMap
