/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# Finite evaluation tests for polynomial subspaces

A finite-dimensional subspace of multivariate polynomials over a field is separated by
finitely many evaluations. The evaluation points can be chosen in any box with infinite
sides. In particular, one finite set tests all polynomials with a prescribed total degree
bound, rather than depending on the coefficients of the polynomial being tested.

Applied to homogeneous Taylor components, these tests give finitely many fixed directions
that detect ambient order at every center.
-/

public section

open MvPolynomial

namespace Submodule

variable {σ K : Type*} [Field K]

/-- Finitely many evaluations in a box with infinite sides detect zero in a
finite-dimensional polynomial subspace. -/
theorem exists_finset_eq_zero_iff_forall_eval_eq_zero (V : Submodule K (MvPolynomial σ K))
    [Module.Finite K V] (s : σ → Set K) (hs : ∀ i, (s i).Infinite) :
    ∃ T : Finset (σ → K), (↑T : Set (σ → K)) ⊆ Set.pi Set.univ s ∧
      ∀ p ∈ V, p = 0 ↔ ∀ v ∈ T, eval v p = 0 := by
  classical
  let e (v : Set.pi Set.univ s) : V →ₗ[K] K :=
    (aeval v.1).toLinearMap.comp V.subtype
  obtain ⟨t, ht⟩ := Finset.exists_inf_le fun v ↦ LinearMap.ker (e v)
  refine ⟨t.image Subtype.val, ?_, fun p hp ↦ ⟨?_, ?_⟩⟩
  · intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · rintro rfl v _
    exact map_zero _
  · intro h
    have hmem : (⟨p, hp⟩ : V) ∈ t.inf (fun v ↦ LinearMap.ker (e v)) := by
      refine Submodule.mem_finsetInf.mpr fun v hv ↦ ?_
      exact h v.1 (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    exact funext_set s hs fun v hv ↦ ht ⟨v, hv⟩ hmem

end Submodule

namespace TauCeti

variable {σ K : Type*} [Field K] [Finite σ]

/-- A fixed finite set in a box with infinite sides tests zero for every polynomial
of total degree at most `D`. -/
theorem exists_finset_eq_zero_iff_forall_eval_eq_zero_of_totalDegree_le (D : ℕ)
    (s : σ → Set K) (hs : ∀ i, (s i).Infinite) :
    ∃ T : Finset (σ → K), (↑T : Set (σ → K)) ⊆ Set.pi Set.univ s ∧
      ∀ p : MvPolynomial σ K, p.totalDegree ≤ D →
        (p = 0 ↔ ∀ v ∈ T, eval v p = 0) := by
  obtain ⟨T, hT, h⟩ :=
    (restrictTotalDegree σ K D).exists_finset_eq_zero_iff_forall_eval_eq_zero s hs
  exact ⟨T, hT, fun p hp ↦ h p ((mem_restrictTotalDegree σ D p).2 hp)⟩

end TauCeti
