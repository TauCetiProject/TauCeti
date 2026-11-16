/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Order criteria in C⋆-algebras via the continuous functional calculus

In a unital C⋆-algebra `A`, positivity and scalar multiples in the spectral order can be tested by
norm inequalities after star-congruence: if `0 ≤ a`, `0 ≤ b`, `0 ≤ K`, and
`‖z * b * star z‖ ≤ K * ‖z * a * star z‖` for all `z : A`, then `b ≤ K • a` (Lance, Lemma 2.7).
This spectral-order criterion is the C⋆-algebraic core of Paschke's inequality for bounded module
maps between Hilbert C⋆-modules.

## Main declarations

* `CStarAlgebra.le_smul_of_norm_conjugate_le`: norm-conjugation criterion `b ≤ K • a` for positive
  elements `a` and `b` in a unital C⋆-algebra.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 2.7.
-/

public section

open Filter Topology Ring

namespace CStarAlgebra

/-- In a unital C⋆-algebra (Lance, Lemma 2.7), if `0 ≤ a`, `0 ≤ b`, `0 ≤ K`, and
`‖z * b * star z‖ ≤ K * ‖z * a * star z‖` for every `z : A`, then `b ≤ K • a`. -/
theorem le_smul_of_norm_conjugate_le {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a b : A} {K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hnorm : ∀ z : A, ‖z * b * star z‖ ≤ K * ‖z * a * star z‖) : b ≤ K • a := by
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hcont : Continuous (fun ε : ℝ ↦ K • a + (K * ε) • (1 : A)) := by fun_prop
  refine le_of_tendsto_of_tendsto (b := 𝓝[>] (0 : ℝ)) tendsto_const_nhds
    (by simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  set d : A := a + algebraMap ℝ A ε
  have hd : IsStrictlyPositive d :=
    IsStrictlyPositive.nonneg_add ha (isStrictlyPositive_algebraMap hε)
  have hconj (x : A) : CFC.sqrt d⁻¹ʳ * x * star (CFC.sqrt d⁻¹ʳ) = CFC.conjSqrt d⁻¹ʳ x := by
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, CFC.conjSqrt_apply]
  have hsb_le : CFC.conjSqrt d⁻¹ʳ b ≤ K • (1 : A) := by
    rw [← Algebra.algebraMap_eq_smul_one,
      ← CStarAlgebra.norm_le_iff_le_algebraMap _ hK (by simpa using CFC.conjSqrt_le_conjSqrt hb),
      ← hconj b]
    refine (hnorm _).trans ?_
    rw [hconj a]
    refine mul_le_of_le_one_right hK <| (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (by simpa using CFC.conjSqrt_le_conjSqrt ha)).mpr ?_
    exact (CFC.conjSqrt_le_conjSqrt (le_add_of_nonneg_right (algebraMap_nonneg A hε.le))).trans_eq
      (CFC.conjSqrt_ringInverse_self d hd)
  calc b = CFC.conjSqrt d (CFC.conjSqrt d⁻¹ʳ b) := (CFC.conjSqrt_conjSqrt_ringInverse d b hd).symm
    _ ≤ CFC.conjSqrt d (K • 1) := CFC.conjSqrt_le_conjSqrt hsb_le
    _ = K • a + (K * ε) • (1 : A) := by
        rw [map_smul, CFC.conjSqrt_one d hd.nonneg, smul_add, Algebra.algebraMap_eq_smul_one,
          smul_smul]

end CStarAlgebra
