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
    (hnorm : ∀ z : A, ‖z * b * star z‖ ≤ K * ‖z * a * star z‖) :
    b ≤ K • a := by
  have hε_bound : ∀ ε : ℝ, 0 < ε → b ≤ K • a + (K * ε) • (1 : A) := by
    intro ε hε
    set d : A := a + algebraMap ℝ A ε
    have hd : IsStrictlyPositive d :=
      IsStrictlyPositive.nonneg_add ha (isStrictlyPositive_algebraMap hε)
    set s : A := CFC.sqrt d⁻¹ʳ
    have hs_sa : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
    have hconj (x : A) : s * x * star s = CFC.conjSqrt d⁻¹ʳ x := by
      rw [hs_sa, CFC.conjSqrt_apply]
    have hsa_nonneg : 0 ≤ CFC.conjSqrt d⁻¹ʳ a := by
      simpa using CFC.conjSqrt_le_conjSqrt (c := d⁻¹ʳ) ha
    have hsb_nonneg : 0 ≤ CFC.conjSqrt d⁻¹ʳ b := by
      simpa using CFC.conjSqrt_le_conjSqrt (c := d⁻¹ʳ) hb
    have hsa_le_one : CFC.conjSqrt d⁻¹ʳ a ≤ 1 :=
      (CFC.conjSqrt_le_conjSqrt (le_add_of_nonneg_right (algebraMap_nonneg A hε.le))).trans_eq
        (CFC.conjSqrt_ringInverse_self d hd)
    have hsa_norm : ‖CFC.conjSqrt d⁻¹ʳ a‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hsa_nonneg).mpr hsa_le_one
    have hsb_le : CFC.conjSqrt d⁻¹ʳ b ≤ K • (1 : A) := by
      rw [← Algebra.algebraMap_eq_smul_one,
        ← CStarAlgebra.norm_le_iff_le_algebraMap _ hK hsb_nonneg, ← hconj b]
      exact (hnorm s).trans (by rw [hconj a]; exact mul_le_of_le_one_right hK hsa_norm)
    calc b = CFC.conjSqrt d (CFC.conjSqrt d⁻¹ʳ b) :=
          (CFC.conjSqrt_conjSqrt_ringInverse d b hd).symm
      _ ≤ CFC.conjSqrt d (K • 1) := CFC.conjSqrt_le_conjSqrt hsb_le
      _ = K • d := by rw [map_smul, CFC.conjSqrt_one d hd.nonneg]
      _ = K • a + (K * ε) • (1 : A) := by
          rw [smul_add, Algebra.algebraMap_eq_smul_one, smul_smul]
  have : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hcont : Continuous (fun ε : ℝ ↦ K • a + (K * ε) • (1 : A)) := by fun_prop
  have htendsto :
      Tendsto (fun ε : ℝ ↦ K • a + (K * ε) • (1 : A)) (𝓝[>] 0) (𝓝 (K • a)) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htendsto ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using hε_bound ε hε

end CStarAlgebra
