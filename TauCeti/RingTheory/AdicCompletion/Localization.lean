/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LocalizedModule.Regular
public import TauCeti.RingTheory.AdicCompletion.Exactness
import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Principal-adic completion of localization sequences

Suppose `f : M →ₗ[R] N` is localization at `S`, `r` is regular on `M`, and
every denominator is regular on `M / rM`. Then the sequence

`0 → M̂ → N̂ → (N / range f)^hat → 0`

is short exact for `(r)`-adic completion. There are no Noetherian or finite-module
hypotheses. Even injectivity of `f` is unnecessary: regularity modulo `rⁿ` makes
all its reductions injective, so its completion is injective.

For `S = {1, s, s², …}`, the hypotheses are exactly regularity of the pair
`(r, s)` (without a nonzero-quotient condition). In localization/completion
comparisons this is the reason the localization cokernel has no `r`-torsion;
regularity is proved before invoking exactness of completion.

Surjectivity of the completed quotient map is Mathlib's `AdicCompletion.map_surjective`.
The two results here supply injectivity and middle exactness on the native
`AdicCompletion` carrier.

## References

* Douglas–Francis–Henriques–Hill, *Topological Modular Forms*, Chapter 12, §8.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (S : Submonoid R)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) [IsLocalizedModule S f] {r : R}

/-- Completion of a localization map is injective if `r` is regular on the
source and all denominators are regular modulo `r`. No injectivity of the
uncompleted map is assumed. -/
theorem map_span_singleton_injective_of_isLocalizedModule (hr : IsSMulRegular M r)
    (hS : ∀ s : S, IsSMulRegular (QuotSMulTop r M) (s : R)) :
    Function.Injective (map (Ideal.span {r}) f) := by
  apply map_injective_of_reduceModIdeal_injective
  intro n
  rw [Ideal.span_singleton_pow]
  have hSn (s : S) : IsSMulRegular (QuotSMulTop (r ^ n) M) (s : R) := by
    have hpair : RingTheory.Sequence.IsWeaklyRegular M [r, (s : R)] := by
      rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
        RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      exact ⟨hr, hS s⟩
    simpa only [pow_one] using hpair.isSMulRegular_quotSMulTop_pow n 1
  have hinj := IsLocalizedModule.quotSMulTop_map_injective S f hSn
  -- Transport from the quotient by `rⁿ M` to the quotient by the ideal `(rⁿ)`.
  -- `reduceModIdeal` and `Ideal.mapQSMulTop` induce the same map on these quotients.
  have h := congrArg DFunLike.coe (QuotSMulTop.map_comp_quotEquivOfEq (r ^ n) f)
  rw [LinearMap.coe_comp, LinearMap.coe_comp] at h
  have hmap : ⇑(((Ideal.span {r ^ n}).mapQSMulTop f).restrictScalars R) =
      ⇑(f.reduceModIdeal (Ideal.span {r ^ n})) := by
    funext q
    induction q using Submodule.Quotient.induction_on with | H m =>
      simp only [LinearMap.restrictScalars_apply, Ideal.mapQSMulTop_mk,
        LinearMap.reduceModIdeal_apply]
  rw [hmap] at h
  exact (h ▸ hinj.comp (LinearEquiv.injective _)).of_comp

/-- Principal-adic completion is exact at the localized module when the
parameter is regular on the source and denominators are regular modulo it.
Together with `map_span_singleton_injective_of_isLocalizedModule` and
`map_surjective`, this gives a short exact completed localization sequence. -/
theorem map_span_singleton_exact_of_isLocalizedModule (hr : IsSMulRegular M r)
    (hS : ∀ s : S, IsSMulRegular (QuotSMulTop r M) (s : R)) :
    Function.Exact (map (Ideal.span {r}) f)
      (map (Ideal.span {r}) (LinearMap.range f).mkQ) :=
  map_span_singleton_exact_of_isSMulRegular (LinearMap.exact_map_mkQ_range f)
    (LinearMap.range f).mkQ_surjective
    (IsLocalizedModule.isSMulRegular_quotient_range S f hr hS)

end AdicCompletion
