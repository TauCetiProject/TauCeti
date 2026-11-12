/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
import Mathlib.Analysis.Real.Sqrt
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Real

/-!
# Real Spin elements as products of unit vectors

Over a field in which `2` is invertible, every element of a Spin group is a product of an even
number of vectors of nonzero norm (`CliffordAlgebra.exists_even_length_list_of_spinGroup`). Over
`ℝ` each of these vectors can be rescaled to norm `1` or `-1`. The positive scalar collected in
front of the rescaled product is then forced to be `1`: the Clifford norm of the Spin element is
`1`, while that of the rescaled product is the product `±1` of the rescaled norms. So every real
Spin element is a product of an even number of vectors of norm `±1` whose norms multiply to `1`;
in signature `(p, q)` these are products of unit vectors of the two kinds, with an even number of
each.

Conversely every such product lies in the Spin group (`CliffordAlgebra.prod_map_ι_mem_spinGroup`).
This description is the input for connectedness arguments, which move the factors of such a
product independently inside the level sets `Q = 1` and `Q = -1`.

## Main results

* `CliffordAlgebra.exists_normalized_list_of_spinGroup`: every element of the Spin group of a real
  quadratic form is a product of an even number of vectors of norm `±1` whose norms multiply to
  `1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

namespace CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}

/-- **Real Spin elements are products of unit vectors.** Every element of the Spin group of a real
quadratic form is the Clifford product of an even number of vectors of norm `1` or `-1` whose
norms multiply to `1`. -/
theorem exists_normalized_list_of_spinGroup (x : spinGroup Q) :
    ∃ l : List V, (∀ v ∈ l, Q v = 1 ∨ Q v = -1) ∧ Even l.length ∧ (l.map Q).prod = 1 ∧
      (x : CliffordAlgebra Q) = (l.map (ι Q)).prod := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨l, hl, hlen, hx⟩ := exists_even_length_list_of_spinGroup x
  have hl0 : ∀ v ∈ l, Q v ≠ 0 := fun v hv ↦ (hl v hv).ne_zero
  set L := l.map fun v ↦ (√|Q v|)⁻¹ • v
  set c := (l.map fun v ↦ √|Q v|).prod
  have hL : ∀ v ∈ L, Q v = 1 ∨ Q v = -1 := by
    simpa only [L, List.forall_mem_map] using
      fun v hv ↦ QuadraticMap.map_inv_sqrt_abs_smul_eq_one_or_neg_one (hl0 v hv)
  have hLlen : Even L.length := by rwa [List.length_map]
  have hc : 0 < c := List.prod_pos fun r hr ↦ by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    exact Real.sqrt_pos.mpr (abs_pos.mpr (hl0 v hv))
  have hxL : (x : CliffordAlgebra Q) = c • (L.map (ι Q)).prod := by
    rw [prod_map_ι_smul, smul_smul, ← List.prod_map_mul, List.prod_eq_one, one_smul, hx]
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (abs_pos.mpr (hl0 v hv))).ne'
  -- The norms of the rescaled vectors multiply to `s` with `s * s = 1`, and comparing Clifford
  -- norms gives `c * c * s = 1`. As `c > 0`, both `s` and `c` are `1`.
  set s := (L.map Q).prod
  have hss : s * s = 1 := by
    rw [← List.prod_map_mul]
    refine List.prod_eq_one fun r hr ↦ ?_
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rcases hL v hv with h | h <;> rw [h] <;> norm_num
  have hcs : c * c * s = 1 := by
    apply algebraMap_injective Q
    have h := spinGroup.coe_star_mul_self x
    rw [hxL, star_smul, smul_mul_smul_comm, star_prod_map_ι_mul_prod_map_ι, hLlen.neg_one_pow,
      one_mul, Algebra.smul_def, ← map_mul] at h
    rw [h, map_one]
  have hs : s = 1 := by
    rcases mul_self_eq_one_iff.mp hss with h | h
    · exact h
    · rw [h] at hcs
      nlinarith
  have hc1 : c = 1 := by
    rw [hs, mul_one] at hcs
    nlinarith
  exact ⟨L, hL, hLlen, hs, by rw [hxL, hc1, one_smul]⟩

end CliffordAlgebra
