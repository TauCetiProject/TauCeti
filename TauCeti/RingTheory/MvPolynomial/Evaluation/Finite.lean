/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Finite evaluation tests for polynomial submodules

A finitely generated submodule of multivariate polynomials over an integral domain is
separated by finitely many evaluations. The evaluation points can be chosen in any box with
infinite sides. In particular, one finite set tests all polynomials with a prescribed total
degree bound, rather than depending on the coefficients of the polynomial being tested.

The proof passes to the fraction field, where the span of the submodule is
finite-dimensional, so the kernels of the evaluation maps have a finite subintersection.
-/

public section

open MvPolynomial

namespace Submodule

variable {σ R : Type*} [CommRing R] [IsDomain R]

/-- Finitely many evaluations in a box with infinite sides detect zero in a
finitely generated submodule of polynomials over an integral domain. -/
theorem exists_finset_eq_zero_iff_forall_eval_eq_zero (V : Submodule R (MvPolynomial σ R))
    [Module.Finite R V] (s : σ → Set R) (hs : ∀ i, (s i).Infinite) :
    ∃ T : Finset (σ → R), (↑T : Set (σ → R)) ⊆ Set.pi Set.univ s ∧
      ∀ p ∈ V, p = 0 ↔ ∀ v ∈ T, eval v p = 0 := by
  classical
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type _) (_ : Field K) (_ : Algebra R K), FaithfulSMul R K :=
    ⟨FractionRing R, inferInstance, inferInstance, inferInstance⟩
  let φ : MvPolynomial σ R →ₗ[R] MvPolynomial σ K :=
    (MvPolynomial.mapAlgHom (Algebra.ofId R K)).toLinearMap
  let W := span K (V.map φ : Set (MvPolynomial σ K))
  have : Module.Finite K W :=
    Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp ‹_›).map φ).span
  let e (v : Set.pi Set.univ s) : W →ₗ[K] K :=
    (aeval (algebraMap R K ∘ v.1)).toLinearMap.comp W.subtype
  have he (v : σ → R) (p : MvPolynomial σ R) :
      eval (algebraMap R K ∘ v) (φ p) = algebraMap R K (eval v p) := by
    simp [φ, eval_map, ← aeval_def, aeval_algebraMap_apply]
  obtain ⟨t, ht⟩ := Finset.exists_inf_le fun v ↦ LinearMap.ker (e v)
  refine ⟨t.image Subtype.val, by simp, fun p hp ↦ ⟨by rintro rfl; simp, fun h ↦ ?_⟩⟩
  have hmem : (⟨φ p, subset_span (mem_map_of_mem hp)⟩ : W) ∈
      t.inf fun v ↦ LinearMap.ker (e v) :=
    mem_finsetInf.mpr fun v hv ↦ by
      simp [e, he, h v.1 (Finset.mem_image.mpr ⟨v, hv, rfl⟩)]
  exact funext_set s hs fun v hv ↦ by simpa [e, he] using ht ⟨v, hv⟩ hmem

end Submodule

namespace TauCeti

variable {σ R : Type*} [CommRing R] [IsDomain R] [Finite σ]

/-- A fixed finite set in a box with infinite sides tests zero for every polynomial
of total degree at most `D` over an integral domain. -/
theorem exists_finset_eq_zero_iff_forall_eval_eq_zero_of_totalDegree_le (D : ℕ)
    (s : σ → Set R) (hs : ∀ i, (s i).Infinite) :
    ∃ T : Finset (σ → R), (↑T : Set (σ → R)) ⊆ Set.pi Set.univ s ∧
      ∀ p : MvPolynomial σ R, p.totalDegree ≤ D →
        (p = 0 ↔ ∀ v ∈ T, eval v p = 0) := by
  obtain ⟨T, hT, h⟩ :=
    (restrictTotalDegree σ R D).exists_finset_eq_zero_iff_forall_eval_eq_zero s hs
  exact ⟨T, hT, fun p hp ↦ h p ((mem_restrictTotalDegree σ D p).2 hp)⟩

end TauCeti
