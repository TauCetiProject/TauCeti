/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Trace
public import TauCeti.RingTheory.DedekindDomain.Different.Semilocal
import TauCeti.RingTheory.DedekindDomain.Different.Basic

/-!
# The different ideal localizes at a completion

Let `L/K` be an extension of number fields, `v` a finite place of `K` and `w` a finite place of
`L` above `v`, with completed integer rings `𝒪_v ⊆ 𝒪_w`. Then the different of `𝒪 L / 𝒪 K`
generates the different of the local extension `𝒪_w / 𝒪_v`:

`𝔇(𝒪 L / 𝒪 K) · 𝒪_w = 𝔇(𝒪_w / 𝒪_v)`.

The trace dual of the global extension spans the trace dual of the completed extension. This
comparison gives the equality of different ideals, and lets results about the global different be
used at each completed place. The semilocal decomposition relates the global trace pairing to the
local pairings.

This is the completion counterpart of `TauCeti.span_traceDual_one_eq_traceDual_one`,
`TauCeti.extended_dual_one_eq_dual_one`, and `TauCeti.map_differentIdeal_eq_differentIdeal` in
`TauCeti/RingTheory/DedekindDomain/Different/Localization.lean`, specializing the abstract
semilocal comparison in `TauCeti/RingTheory/DedekindDomain/Different/Semilocal.lean`.

The completion comparison equations are used with both places explicit: their left-hand sides
determine `w` but not the base place `v`, so they are not simplification rules.

## Main results

All in the namespace `IsDedekindDomain.HeightOneSpectrum`, as they take the place `v` first:

* `sum_trace_mul_smul_algebraMap_eq`: a trace-dual expansion of `L` over `K` remains one of `L_w`
  over `K_v`.
* `span_traceDual_one_eq_traceDual_one_adicCompletionIntegers`: the local trace dual is spanned by
  the global one.
* `extended_dual_one_eq_dual_one_adicCompletionIntegers`: the same statement for fractional
  ideals, as the extension of the global trace dual along `𝒪 L → 𝒪_w`.
* `map_differentIdeal_eq_differentIdeal_adicCompletionIntegers`: the different ideal commutes
  with completion.
* `differentIdeal_integralSemilocal`: the different, extended to the integral semilocal algebra
  `𝒪_v ⊗[𝒪 K] 𝒪 L` and read through `TauCeti.integralSemilocalEquiv`, is the product of the local
  differents at the places above `v`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter III, Proposition (2.2).
* [J.-P. Serre, *Corps locaux*][serre1968], Chapter III, §4, Proposition 10.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct NumberField AdicCompletionExtension Valued nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

open TauCeti

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]
  {L : Type*} [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The place `w`, as an index of the semilocal decomposition at `v`. -/
private abbrev placeAbove : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} :=
  ⟨w, inferInstance⟩

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{L/K}(x bᵢ) yᵢ` for every
`x ∈ L`, then `z = ∑ᵢ Tr_{L_w/K_v}(z bᵢ) yᵢ` for every `z ∈ L_w`. -/
theorem sum_trace_mul_smul_algebraMap_eq {ι : Type*} [Fintype ι] (b y : ι → L)
    (h : ∀ x : L, ∑ i, Algebra.trace K L (x * b i) • y i = x) (z : w.adicCompletion L) :
    ∑ i, Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) (b i)) • algebraMap L (w.adicCompletion L) (y i) =
      z := by
  simpa [semilocalEquiv_tmul] using
    (semilocalEquiv L v).sum_trace_mul_smul_eq b y h (placeAbove v w) z

/-- **The local trace dual is spanned by the global one.** The trace dual of `𝒪_w` over `𝒪_v` is
the `𝒪_w`-span of the image in `L_w` of the trace dual of `𝒪 L` over `𝒪 K`. -/
theorem span_traceDual_one_eq_traceDual_one_adicCompletionIntegers :
    Submodule.span (w.adicCompletionIntegers L)
        (algebraMap L (w.adicCompletion L) ''
          Submodule.traceDual (𝒪 K) K (1 : Submodule (𝒪 L) L)) =
      Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)) := by
  have : IsScalarTower (𝒪 K) (v.adicCompletionIntegers K) (v.adicCompletion K) :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply (𝒪 K) K (v.adicCompletion K),
        ValuationSubring.algebraMap_apply, algebraMap_adicCompletionIntegers_apply,
        algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]
  exact (semilocalEquiv L v).span_traceDual_one_eq_traceDual_one_of_semilocal
    (integralSemilocalEquiv L v) (fun u ↦ algebraMap L (u.1.adicCompletion L))
    (fun u ↦ algebraMap (𝒪 L) (u.1.adicCompletionIntegers L))
    semilocalEquiv_tmul integralSemilocalEquiv_tmul
    (fun u x ↦ (algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers u.1 x).symm)
    (placeAbove v w)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace dual of
`𝒪 L` over `𝒪 K` to `𝒪_w` gives the trace dual of `𝒪_w` over `𝒪_v`. -/
theorem extended_dual_one_eq_dual_one_adicCompletionIntegers :
    (FractionalIdeal.dual (𝒪 K) K (1 : FractionalIdeal (𝒪 L)⁰ L)).extended (w.adicCompletion L)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (FaithfulSMul.algebraMap_injective (𝒪 L) (w.adicCompletionIntegers L))) =
      FractionalIdeal.dual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : FractionalIdeal (w.adicCompletionIntegers L)⁰ (w.adicCompletion L)) :=
  (algebraMap L (w.adicCompletion L)).extended_dual_one_eq_dual_one_of_span_eq
    (algebraMap (𝒪 L) (w.adicCompletionIntegers L))
    (FaithfulSMul.algebraMap_injective (𝒪 L) (w.adicCompletionIntegers L))
    (fun x ↦ (algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers w x).symm)
    (span_traceDual_one_eq_traceDual_one_adicCompletionIntegers v w)

/-- **The different commutes with completion.** The different ideal of `𝒪 L` over `𝒪 K` generates
in `𝒪_w` the different ideal of `𝒪_w` over `𝒪_v`. -/
theorem map_differentIdeal_eq_differentIdeal_adicCompletionIntegers :
    (differentIdeal (𝒪 K) (𝒪 L)).map (algebraMap (𝒪 L) (w.adicCompletionIntegers L)) =
      differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  (algebraMap (𝒪 L) (w.adicCompletionIntegers L))
    |>.map_differentIdeal_eq_differentIdeal_of_extended_eq
      (K := K) (L := L) (K' := v.adicCompletion K) (L₀ := w.adicCompletion L)
      (FaithfulSMul.algebraMap_injective (𝒪 L) (w.adicCompletionIntegers L))
      (extended_dual_one_eq_dual_one_adicCompletionIntegers v w)

/-- **The different of the integral semilocal algebra, read componentwise.** Extend the different
of `𝒪 L` over `𝒪 K` to the integral semilocal algebra `𝒪_v ⊗[𝒪 K] 𝒪 L` and transport it along the
integral semilocal decomposition `𝒪_v ⊗[𝒪 K] 𝒪 L ≃ ∏_{w ∣ v} 𝒪_w`: the result is the product of
the differents of the local extensions `𝒪_w / 𝒪_v`. The tensor product is not a domain, so the
left-hand side is the extended ideal rather than a different ideal of its own. -/
theorem differentIdeal_integralSemilocal :
    ((differentIdeal (𝒪 K) (𝒪 L)).map
        (Algebra.TensorProduct.includeRight :
          𝒪 L →ₐ[𝒪 K] v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L)).map
        (integralSemilocalEquiv L v) =
      Ideal.pi fun u ↦
        differentIdeal (v.adicCompletionIntegers K) (u.1.adicCompletionIntegers L) :=
  (integralSemilocalEquiv L v).map_differentIdeal_semilocal
    (fun u ↦ let _ := u.2; algebraMap (𝒪 L) (u.1.adicCompletionIntegers L))
    integralSemilocalEquiv_tmul
    fun u ↦ let _ := u.2; map_differentIdeal_eq_differentIdeal_adicCompletionIntegers v u.1

end IsDedekindDomain.HeightOneSpectrum
