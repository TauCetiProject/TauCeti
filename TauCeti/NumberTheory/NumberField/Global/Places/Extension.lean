/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic

/-!
# Normalized absolute values under extension of finite completions

For an extension of number fields `L/K` and finite places `w ∣ v`, the canonical map
`K_v → L_w` raises normalized absolute values to the local degree:

`‖algebraMap K_v L_w x‖ = ‖x‖ ^ [L_w : K_v]`.

These are the residue-cardinality normalizations used in the product formula. In particular,
the map need not preserve the norm. Taking the product over `w ∣ v` raises the norm to the
global degree `[L : K]`. This is the finite-place input to the idele norm formula for extension
of scalars.

Mathlib's `NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap` supplies the
formula on `K`, with exponent `e(w/v) * f(w/v)`. Here it extends to the whole completion and
uses `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion` to identify that exponent
with the local degree. The product formula uses `TauCeti.sum_finrank_adicCompletion_eq_finrank`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdicCompletionExtension

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The normalized absolute value of the image in `L_w` is the normalized absolute value in
`K_v` raised to the local degree `[L_w : K_v]`. No Galois hypothesis is needed. -/
theorem norm_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    ‖algebraMap (v.adicCompletion K) (w.adicCompletion L) x‖ =
      ‖x‖ ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  rw [finrank_adicCompletion v w]
  refine congrFun ((v.denseRange_algebraMap K).equalizer
    (continuous_norm.comp ?_) (continuous_norm.pow _) ?_) x
  · rw [algebraMap_adicCompletionExtensionAlgebra]
    exact continuous_adicCompletionExtension K L v w
  · funext a
    simp only [Function.comp_apply, Pi.pow_apply, algebraMap_adicCompletionExtensionAlgebra,
      algebraMap_adicCompletion, Algebra.algebraMap_self_apply, adicCompletionExtension_coe]
    simpa only [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.embedding_apply] using
      FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap v w a

attribute [local instance] Fintype.ofFinite in
/-- The product of the normalized absolute values of the images of `x ∈ K_v` in all the
completions above `v` is `‖x‖ ^ [L : K]`. This includes `x = 0`. -/
theorem prod_norm_algebraMap_adicCompletion (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    ∏ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        ‖algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x‖ =
      ‖x‖ ^ Module.finrank K L := by
  simp_rw [norm_algebraMap_adicCompletion]
  rw [Finset.prod_pow_eq_pow_sum, sum_finrank_adicCompletion_eq_finrank]

end TauCeti.GlobalNumberFields
