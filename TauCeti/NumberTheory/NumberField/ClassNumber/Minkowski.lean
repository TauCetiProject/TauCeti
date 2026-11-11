/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.RingTheory.ClassGroup.HeightOneSpectrum

/-!
# Small prime ideals generate the class group

The classes of prime ideals of norm at most the Minkowski bound generate the class group of
any number field. The bound may be replaced by a larger real number, allowing a numerical
upper bound to supply the generators for a class-group presentation.

The proof uses Mathlib's `NumberField.exists_ideal_in_class_of_norm_le` and the prime-support
criterion `ClassGroup.mk0_mem_closure_of_count_eq`: every prime factor of a small integral
ideal has norm at most that of the ideal.

## References

* W. Stein, *Algebraic Number Theory, a Computational Approach*, §7.3, Lemma 7.3.1.
* K. Conrad, *Class group calculations by Minkowski bound*, §1.
-/

public section

open IsDedekindDomain
open scoped NumberField nonZeroDivisors Real

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Minkowski's class-group generation bound.** The classes of nonzero prime ideals of norm
at most `B` generate the class group whenever `B` is at least the Minkowski bound.

In particular, the exact Minkowski bound can be used by taking `hB := le_rfl`. -/
theorem closure_classGroupMk_image_absNorm_le_eq_top {B : ℝ}
    (hB : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ((Nat.factorial (Module.finrank ℚ K) : ℝ) /
        (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        Real.sqrt |NumberField.discr K|) ≤ B) :
    Subgroup.closure (HeightOneSpectrum.classGroupMk ''
      {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ B}) = ⊤ := by
  refine top_unique fun C _ ↦ ?_
  obtain ⟨I, rfl, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  have hI0 := nonZeroDivisors.coe_ne_zero I
  refine ClassGroup.mk0_mem_closure_of_count_eq K 1 fun v hv ↦ ?_
  rw [Units.val_one, map_one, FractionalIdeal.count_one,
    FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero]
  by_contra hc
  have hd : v.asIdeal ∣ (I : Ideal (𝓞 K)) :=
    (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hc
  have hn : Ideal.absNorm v.asIdeal ≤ Ideal.absNorm (I : Ideal (𝓞 K)) :=
    Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hd))
  exact hv ((Nat.cast_le.mpr hn).trans (hI.trans hB))

end TauCeti.NumberField
