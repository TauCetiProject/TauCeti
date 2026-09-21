/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Norm

/-!
# Products of normalized absolute values over finite completions

For an extension of number fields `L/K`, the canonical map `K_v → L_w` raises normalized
absolute values to the local degree `[L_w : K_v]`. Taking the product over `w ∣ v` raises
the norm to the global degree `[L : K]`. This is the finite-place input to the idele norm
formula for extension of scalars.

## Main results

* `TauCeti.prod_norm_adicCompletionExtension_eq_norm_pow`: the product of the normalized
  absolute values of the images in all completions above a finite place.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdicCompletionExtension

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

attribute [local instance] Fintype.ofFinite in
/-- The product of the normalized absolute values of the images of `x ∈ K_v` in all the
completions above `v` is `‖x‖ ^ [L : K]`. This includes `x = 0`. -/
@[simp↓]
theorem prod_norm_adicCompletionExtension_eq_norm_pow
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    ∏ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        ‖v.adicCompletionExtension K L w.1 x‖ =
      ‖x‖ ^ Module.finrank K L := by
  simp_rw [norm_adicCompletionExtension]
  rw [Finset.prod_pow_eq_pow_sum, sum_finrank_adicCompletion_eq_finrank]

end TauCeti
