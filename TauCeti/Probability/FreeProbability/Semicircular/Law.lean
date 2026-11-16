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
moments, which agree. Together with the cumulant characterization of semicircular elements, this
identifies the semicircle law, the free cumulant sequence `κ₂ = v`, `κ_n = 0` for `n ≠ 2`, and the
moment sequence `v ^ k * catalan k`.

Every variance `v ≥ 0` is realized: in the commutative C⋆-algebra `C([-2√v, 2√v], ℂ)` with
integration against the semicircle law, the coordinate function is semicircular of variance `v`.

## Main results

* `PositiveLinearMap.law_eq_semicircleReal_iff`,
  `PositiveLinearMap.law_eq_semicircleReal_iff_isSemicircular_sub_algebraMap` — for selfadjoint
  `a`, `μ_a = semicircleReal 0 v` (respectively `semicircleReal m v`) if and only if `a`
  (respectively `a - m`) is semicircular of variance `v`.
* `PositiveLinearMap.law_eq_semicircleReal_iff_freeCumulant` — characterization of
  `law φ a = semicircleReal m v` by normalisation, mean `m`, variance `v`, and vanishing higher free
  cumulants.
* `PositiveLinearMap.law_smul_add_algebraMap_of_law_eq_semicircleReal`,
  `PositiveLinearMap.law_add_algebraMap_of_law_eq_semicircleReal` — affine rescaling and scalar
  shifts of elements with semicircle law.
* `TauCeti.isSemicircular_integralPositiveLinearMap_semicircleReal` — a commutative
  realization of a semicircular element of any variance `v ≥ 0`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 2 and 3.
-/

public section

open MeasureTheory NNReal TauCeti TauCeti.Probability
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

/-- A selfadjoint element `a` has the semicircle law `semicircleReal m v` of centre `m` and
variance `v` if and only if the centred element `a - algebraMap ℝ A m` is semicircular of variance
`v`. -/
theorem law_eq_semicircleReal_iff_isSemicircular_sub_algebraMap (ha : IsSelfAdjoint a) (m : ℝ)
    (v : ℝ≥0) :
    law φ a = semicircleReal m v ↔
      IsSemicircular φ.toLinearMap (a - algebraMap ℝ A m) ((v : ℝ) : ℂ) := by
  have ha' : IsSelfAdjoint (a - algebraMap ℝ A m) := ha.sub ((IsSelfAdjoint.all m).algebraMap A)
  have hsub : a - algebraMap ℝ A m = (1 : ℝ) • a + algebraMap ℝ A (-m) := by
    simp [sub_eq_add_neg]
  rw [← law_eq_semicircleReal_iff φ ha' v]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hsub, law_smul_add_algebraMap φ ha 1 (-m), h]
    simpa [add_comm] using map_affine_semicircleReal m (-m) 1 v
  · have hadd : a = (1 : ℝ) • (a - algebraMap ℝ A m) + algebraMap ℝ A m := by simp
    rw [hadd, law_smul_add_algebraMap φ ha' 1 m, h]
    simpa [add_comm] using map_affine_semicircleReal 0 m 1 v

/-- *Free cumulant characterization of the semicircle law `semicircleReal m v`*: a selfadjoint
element `a` has law `semicircleReal m v` if and only if `φ 1 = 1`, `φ a = m`, `κ₂(a, a) = v`, and
all higher free cumulants `κ_n(a, …, a)` (`n > 2`) vanish. -/
theorem law_eq_semicircleReal_iff_freeCumulant (ha : IsSelfAdjoint a) (m : ℝ) (v : ℝ≥0) :
    law φ a = semicircleReal m v ↔
      φ 1 = 1 ∧ φ a = m ∧ ∀ n : ℕ, 2 ≤ n →
        freeCumulant φ.toLinearMap (fun _ : Fin n => a) Finset.univ =
          if n = 2 then ((v : ℝ) : ℂ) else 0 := by
  rw [law_eq_semicircleReal_iff_isSemicircular_sub_algebraMap φ ha m v,
    IsScalarTower.algebraMap_apply ℝ ℂ A m]
  exact ⟨fun h => ⟨h.apply_one,
      (isSemicircular_sub_algebraMap_iff_freeCumulant_const h.apply_one).1 h⟩,
    fun ⟨hφ, h⟩ => (isSemicircular_sub_algebraMap_iff_freeCumulant_const hφ).2 h⟩

/-- *Affine transport of semicircle laws*: if `a` has law `semicircleReal m v` (which forces `a` to
be selfadjoint), then `r • a + algebraMap ℝ A c` has law
`semicircleReal (c + r * m) (Real.toNNReal (r ^ 2) * v)`. -/
theorem law_smul_add_algebraMap_of_law_eq_semicircleReal {m : ℝ} {v : ℝ≥0}
    (h : law φ a = semicircleReal m v) (r c : ℝ) :
    law φ (r • a + algebraMap ℝ A c) =
      semicircleReal (c + r * m) (Real.toNNReal (r ^ 2) * v) := by
  have ha : IsSelfAdjoint a := by
    by_contra hna
    have h0 := congrArg (· Set.univ) ((law_of_not_isSelfAdjoint φ hna).symm.trans h)
    simp at h0
  rw [law_smul_add_algebraMap φ ha r c, h]
  simpa [add_comm] using map_affine_semicircleReal m c r v

/-- Shifting an element with semicircle law `semicircleReal m v` by a real scalar `c` gives law
`semicircleReal (c + m) v`. -/
theorem law_add_algebraMap_of_law_eq_semicircleReal {m : ℝ} {v : ℝ≥0}
    (h : law φ a = semicircleReal m v) (c : ℝ) :
    law φ (a + algebraMap ℝ A c) = semicircleReal (c + m) v := by
  simpa using law_smul_add_algebraMap_of_law_eq_semicircleReal φ h 1 c

/-- Shifting an element with semicircle law `semicircleReal m v` by a real scalar `c` embedded via
`algebraMap ℂ A` gives law `semicircleReal (c + m) v`. -/
theorem law_add_algebraMap_ofReal_of_law_eq_semicircleReal {m : ℝ} {v : ℝ≥0}
    (h : law φ a = semicircleReal m v) (c : ℝ) :
    law φ (a + algebraMap ℂ A (c : ℂ)) = semicircleReal (c + m) v := by
  have hc : (c : ℂ) = algebraMap ℝ ℂ c := rfl
  rw [hc, ← IsScalarTower.algebraMap_apply ℝ ℂ A c]
  exact law_add_algebraMap_of_law_eq_semicircleReal φ h c

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
