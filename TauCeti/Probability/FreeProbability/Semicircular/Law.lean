/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.FreeProbability.Law.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Basic

/-!
# The law of a semicircular element

Let `φ` be a positive linear functional on a C⋆-algebra `A` and `a` a selfadjoint element of `A`.
The element `a` is semicircular of variance `v ≥ 0` for `φ` exactly when its law `μ_a` is the
centred semicircle law `semicircleReal 0 v`, the measure with density `(2π v)⁻¹ √(4v - t²)` on
`[-2√v, 2√v]` for `v > 0` and the Dirac mass at `0` for `v = 0`. Both are determined by their
moments, which agree. More generally, `μ_a = semicircleReal c v` if and only if `a - c • 1` is
semicircular of variance `v`, equivalently if and only if `φ 1 = 1`, `φ a = c`, `κ₂(a, a) = v`,
and `κ_n(a, …, a) = 0` for `n ≥ 3`.

Every variance `v ≥ 0` is realized: in the commutative C⋆-algebra `C([-2√v, 2√v], ℂ)` with
integration against the semicircle law, the coordinate function is semicircular of variance `v`.

## Main results

* `PositiveLinearMap.law_eq_semicircleReal_iff` — for selfadjoint `a`, `μ_a = semicircleReal 0 v`
  if and only if `a` is semicircular of variance `v`.
* `PositiveLinearMap.law_smul_add_algebraMap_of_isSemicircular` — affine images `r • a + c • 1` of
  a semicircular element have law `semicircleReal c (r ^ 2 * v)`.
* `PositiveLinearMap.law_eq_semicircleReal_iff_isSemicircular_sub` and
  `PositiveLinearMap.law_eq_semicircleReal_iff_freeCumulant` — characterization of general
  centre/variance semicircle laws `semicircleReal c v` via `a - c • 1` and via free cumulants.
* `TauCeti.isSemicircular_integralPositiveLinearMap_semicircleReal` — a commutative
  realization of a semicircular element of any variance `v ≥ 0`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 2 and 11.
-/

public section

open Finset MeasureTheory NNReal TauCeti TauCeti.Probability
open scoped ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {a : A}

/-- *The law of a semicircular element*: a selfadjoint element `a` of a C⋆-algebra has the centred
semicircle law of variance `v` with respect to `φ` if and only if it is semicircular of variance
`v` for `φ`. -/
theorem law_eq_semicircleReal_iff (ha : IsSelfAdjoint a) (v : ℝ≥0) :
    law φ a = semicircleReal 0 v ↔ IsSemicircular φ.toLinearMap a ((v : ℝ) : ℂ) := by
  rw [eq_comm, eq_law_iff_forall_integral_pow ha isCompact_Icc
      (by simpa only [zero_sub, zero_add, Set.ofPred_mem_eq] using
        mem_ae_iff.1 (ae_mem_Icc_semicircleReal 0 v)),
    isSemicircular_iff_apply_pow]
  refine forall_congr' fun n => ?_
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [eq_comm]

/-- An affine image `r • a + c • 1` of a selfadjoint semicircular element of variance `v` has the
semicircle law `semicircleReal c (r ^ 2 * v)`. -/
theorem law_smul_add_algebraMap_of_isSemicircular (ha : IsSelfAdjoint a) {v : ℝ≥0}
    (h : IsSemicircular φ.toLinearMap a ((v : ℝ) : ℂ)) (r c : ℝ) :
    law φ (r • a + algebraMap ℝ A c) = semicircleReal c (Real.toNNReal (r ^ 2) * v) := by
  have hfun : (fun x : ℝ => r * x + c) = fun x => c + r * x := by
    ext x; ring
  rw [law_smul_add_algebraMap φ ha r c, (law_eq_semicircleReal_iff φ ha v).2 h, hfun,
    map_affine_semicircleReal, mul_zero, add_zero]

/-- Shifting a selfadjoint semicircular element of variance `v` by `c • 1` yields the semicircle
law `semicircleReal c v`. -/
theorem law_add_algebraMap_of_isSemicircular (ha : IsSelfAdjoint a) {v : ℝ≥0}
    (h : IsSemicircular φ.toLinearMap a ((v : ℝ) : ℂ)) (c : ℝ) :
    law φ (a + algebraMap ℝ A c) = semicircleReal c v := by
  simpa using law_smul_add_algebraMap_of_isSemicircular φ ha h 1 c

/-- A selfadjoint element `a` has the semicircle law `semicircleReal c v` of centre `c` and
variance `v` if and only if `a - c • 1` is semicircular of variance `v`. -/
theorem law_eq_semicircleReal_iff_isSemicircular_sub (ha : IsSelfAdjoint a) (c : ℝ) (v : ℝ≥0) :
    law φ a = semicircleReal c v ↔
      IsSemicircular φ.toLinearMap (a - algebraMap ℝ A c) ((v : ℝ) : ℂ) := by
  have hc : IsSelfAdjoint (algebraMap ℝ A c) := by
    simp [IsSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  have ha' : IsSelfAdjoint (a - algebraMap ℝ A c) := ha.sub hc
  refine ⟨fun hlaw => (law_eq_semicircleReal_iff φ ha' v).1 ?_, fun hsub => ?_⟩
  · have hsub_eq : a - algebraMap ℝ A c = (1 : ℝ) • a + algebraMap ℝ A (-c) := by
      simp [sub_eq_add_neg]
    have hfun : (fun x : ℝ => 1 * x + -c) = fun x => -c + 1 * x := by
      ext x; ring
    rw [hsub_eq, law_smul_add_algebraMap φ ha 1 (-c), hlaw, hfun, map_affine_semicircleReal]
    simp
  · simpa using law_add_algebraMap_of_isSemicircular φ ha' hsub c

/-- A selfadjoint element `a` of a C⋆-algebra has the semicircle law `semicircleReal c v` of
centre `c` and variance `v` with respect to `φ` if and only if `φ 1 = 1`, `φ a = c`, and the higher
free cumulants of `a` satisfy `κ₂(a, a) = v` and `κ_n(a, …, a) = 0` for `n ≥ 3`. -/
theorem law_eq_semicircleReal_iff_freeCumulant (ha : IsSelfAdjoint a) (c : ℝ) (v : ℝ≥0) :
    law φ a = semicircleReal c v ↔
      φ 1 = 1 ∧ φ a = c ∧
        ∀ n : ℕ, 2 ≤ n →
          freeCumulant φ.toLinearMap (fun _ : Fin n => a) univ =
            if n = 2 then ((v : ℝ) : ℂ) else 0 := by
  rw [law_eq_semicircleReal_iff_isSemicircular_sub φ ha c v]
  have hshift : a - algebraMap ℝ A c = a + algebraMap ℂ A (-(c : ℂ)) := by
    rw [sub_eq_add_neg, map_neg, IsScalarTower.algebraMap_apply ℝ ℂ A]
    rfl
  refine ⟨fun h => ⟨h.apply_one, ?_, fun n hn => ?_⟩, fun ⟨h1, hmean, hκ⟩ => ?_⟩
  · have h0 := h.apply_self
    rw [hshift, map_add, Algebra.algebraMap_eq_smul_one, map_smul] at h0
    have h1' : φ.toLinearMap 1 = 1 := h.apply_one
    rw [h1', smul_eq_mul, mul_one, add_neg_eq_zero] at h0
    exact h0
  · have h1lt : 1 < #(univ : Finset (Fin n)) := by simp; omega
    have hcum := (isSemicircular_iff_freeCumulant_const h.apply_one).1 h n (by omega)
    rwa [hshift, freeCumulant_add_algebraMap φ.toLinearMap _ h.apply_one _ h1lt] at hcum
  · refine (isSemicircular_iff_freeCumulant_const h1).2 fun n hn => ?_
    rcases lt_or_ge n 2 with hn1 | hn2
    · obtain rfl : n = 1 := by omega
      have huniv : (univ : Finset (Fin 1)) = {0} := by decide
      have h1' : φ.toLinearMap 1 = 1 := h1
      have hmean' : φ.toLinearMap a = c := hmean
      rw [huniv, freeCumulant_singleton, hshift, map_add, Algebra.algebraMap_eq_smul_one, map_smul,
        h1', hmean']
      simp
    · have h1lt : 1 < #(univ : Finset (Fin n)) := by simp; omega
      rw [hshift, freeCumulant_add_algebraMap φ.toLinearMap _ h1 _ h1lt, hκ n hn2]

end PositiveLinearMap

namespace TauCeti

/-- *Semicircular elements of every variance exist*: in the commutative C⋆-algebra of complex
continuous functions on `K = [-2√v, 2√v]`, with the state given by integration against the
semicircle law of variance `v`, the coordinate function `x ↦ x` is semicircular of variance `v`. -/
theorem isSemicircular_integralPositiveLinearMap_semicircleReal (v : ℝ≥0) :
    IsSemicircular (ContinuousMap.integralPositiveLinearMap ((semicircleReal 0 v).comap
        ((↑) : Set.Icc (-(2 * √(v : ℝ))) (2 * √(v : ℝ)) → ℝ))).toLinearMap
      ((ContinuousMap.restrict (Set.Icc (-(2 * √(v : ℝ))) (2 * √(v : ℝ)))
        (ContinuousMap.id ℝ)).realToRCLike ℂ) ((v : ℝ) : ℂ) :=
  (PositiveLinearMap.law_eq_semicircleReal_iff _ (ContinuousMap.isSelfAdjoint_realToRCLike ℂ) v).1
    (PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
      (by simpa only [zero_sub, zero_add, Set.ofPred_mem_eq] using
        mem_ae_iff.1 (ae_mem_Icc_semicircleReal 0 v)))

end TauCeti
