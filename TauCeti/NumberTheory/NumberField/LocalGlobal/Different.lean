/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Integers
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.NormTrace
public import TauCeti.RingTheory.DedekindDomain.Different.DualFamily

/-!
# The different ideal localizes at a completion

Let `L/K` be an extension of number fields, `v` a finite place of `K` and `w` a finite place of
`L` above `v`, with completed integer rings `𝒪_v ⊆ 𝒪_w`. Then the different of `𝒪 L / 𝒪 K`
generates the different of the local extension `𝒪_w / 𝒪_v`:

`𝔇(𝒪 L / 𝒪 K) · 𝒪_w = 𝔇(𝒪_w / 𝒪_v)`.

The comparison is made on the trace duals, which the different inverts. The semilocal
decomposition `K_v ⊗[K] L ≃ ∏_{w' ∣ v} L_{w'}` computes the trace of `K_v ⊗[K] L` as the sum of
the local traces, so an element of `L_w` placed in the `w`-component pairs with a global element
exactly as it does in `L_w`.

* The image of the global trace dual lies in the local one: an element of `𝒪_w`, placed in the
  `w`-component, comes from `𝒪_v ⊗[𝒪 K] 𝒪 L` by the integral semilocal decomposition, on which
  the pairing with the global trace dual takes values in `𝒪_v`.
* Conversely, `𝒪 L` is a finite projective `𝒪 K`-module, so it carries a finite trace-dual
  family `x = ∑ᵢ Tr(x bᵢ) yᵢ` with `bᵢ ∈ 𝒪 L` and `yᵢ` in the global trace dual. This identity
  is `K`-linear, so it passes to `K_v ⊗[K] L` and then to the `w`-component, where it writes every
  element `z` of the local trace dual as `z = ∑ᵢ Tr_{L_w/K_v}(z bᵢ) yᵢ` with coefficients in
  `𝒪_v`.

The equality of trace duals then passes to fractional ideals, and to the different ideals by
inversion.

This is the completion counterpart of `TauCeti.span_traceDual_one_eq_traceDual_one`,
`TauCeti.extended_dual_one_eq_dual_one`, and `TauCeti.map_differentIdeal_eq_differentIdeal` in
`TauCeti/RingTheory/DedekindDomain/Different/Localization.lean`; the trace-dual comparison and
the names follow that formal localization result.

## Main results

* `TauCeti.sum_trace_mul_smul_algebraMap_eq`: a trace-dual expansion of `L` over `K` remains one
  of `L_w` over `K_v`.
* `TauCeti.span_traceDual_one_eq_traceDual_one_adicCompletionIntegers`: the local trace dual is
  spanned by the global one.
* `TauCeti.extended_dual_one_eq_dual_one_adicCompletionIntegers`: the same statement for
  fractional ideals, as the extension of the global trace dual along `𝒪 L → 𝒪_w`.
* `TauCeti.map_differentIdeal_eq_differentIdeal_adicCompletionIntegers`: the different ideal
  commutes with completion.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter III, Proposition (2.2).
* [J.-P. Serre, *Corps locaux*][serre1968], Chapter III, §4, Proposition 10.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct NumberField AdicCompletionExtension Valued nonZeroDivisors

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]
  {L : Type*} [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K)) (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The place `w`, as an index of the semilocal decomposition at `v`. -/
private abbrev placeAbove : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} :=
  ⟨w, inferInstance⟩

/-- The trace pairing and scalar multiplication commute with extension from `K` to `K_v`. -/
private theorem trace_tmul_mul_smul (a : v.adicCompletion K) (x b y : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((a ⊗ₜ x) * (1 ⊗ₜ b)) • ((1 : v.adicCompletion K) ⊗ₜ[K] y) =
      a ⊗ₜ[K] (Algebra.trace K L (x * b) • y) := by
  have ha : a ⊗ₜ[K] (x * b) = a • ((1 : v.adicCompletion K) ⊗ₜ[K] (x * b)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul,
    Algebra.trace_baseChange_tmul]
  simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a,
    ← Algebra.smul_def, TensorProduct.smul_tmul]

/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{L/K}(x bᵢ) yᵢ` for every
`x ∈ L`, then `z = ∑ᵢ Tr_{L_w/K_v}(z bᵢ) yᵢ` for every `z ∈ L_w`. -/
theorem sum_trace_mul_smul_algebraMap_eq {ι : Type*} [Fintype ι] (b y : ι → L)
    (h : ∀ x : L, ∑ i, Algebra.trace K L (x * b i) • y i = x) (z : w.adicCompletion L) :
    ∑ i, Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) (b i)) • algebraMap L (w.adicCompletion L) (y i) =
      z := by
  classical
  -- The expansion is `K`-linear, so it holds in `K_v ⊗[K] L`.
  have hF (ξ : v.adicCompletion K ⊗[K] L) :
      ∑ i, Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) (ξ * (1 ⊗ₜ b i)) •
        ((1 : v.adicCompletion K) ⊗ₜ[K] y i) = ξ := by
    induction ξ using TensorProduct.induction_on with
    | zero => simp
    | add ξ η hξ hη =>
      conv_rhs => rw [← hξ, ← hη]
      simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
    | tmul a x =>
      conv_rhs => rw [← h x, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact trace_tmul_mul_smul v a x (b i) (y i)
  -- Place `z` in the `w`-component and read off that component.
  have h' := congrArg (fun ξ ↦ semilocalEquiv L v ξ (placeAbove v w))
    (hF ((semilocalEquiv L v).symm (Pi.single (placeAbove v w) z)))
  simp only [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, semilocalEquiv_tmul, map_one, one_mul,
    trace_semilocalEquiv_symm_single_mul] at h'
  exact h'

/-- A global integer, viewed in `L_w`, is the image of its image in `𝒪_w`. -/
private theorem algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (x : 𝒪 L) :
    algebraMap L (w.adicCompletion L) (algebraMap (𝒪 L) L x) =
      algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
        (algebraMap (𝒪 L) (w.adicCompletionIntegers L) x) := by
  rw [ValuationSubring.algebraMap_apply, algebraMap_adicCompletionIntegers_apply,
    algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]

/-- On the image of `𝒪_v ⊗[𝒪 K] 𝒪 L`, the trace pairing with an element of the global trace dual
takes values in `𝒪_v`. -/
private theorem trace_integralSemilocalToField_mul_mem {d : L}
    (hd : d ∈ Submodule.traceDual (𝒪 K) K (1 : Submodule (𝒪 L) L))
    (t : v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        (integralSemilocalToField L v t * (1 ⊗ₜ d)) ∈
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).range := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu =>
    rw [map_add, add_mul, map_add]
    exact add_mem ht hu
  | tmul a x =>
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨x, rfl⟩)
    refine ⟨a * algebraMap (𝒪 K) (v.adicCompletionIntegers K) r, ?_⟩
    rw [trace_integralSemilocalToField_tmul_mul, mul_comm (x : L),
      ← Algebra.traceForm_apply, ← hr]
    simp only [map_mul, ValuationSubring.algebraMap_apply,
      algebraMap_adicCompletionIntegers_apply, algebraMap_adicCompletion,
      Function.comp_apply, Algebra.algebraMap_self_apply]

/-- The image in `L_w` of an element of the trace dual of `𝒪 L` over `𝒪 K` lies in the trace dual
of `𝒪_w` over `𝒪_v`. -/
private theorem algebraMap_mem_traceDual_adicCompletionIntegers {d : L}
    (hd : d ∈ Submodule.traceDual (𝒪 K) K (1 : Submodule (𝒪 L) L)) :
    algebraMap L (w.adicCompletion L) d ∈
      Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)) := by
  classical
  rw [Submodule.mem_traceDual]
  intro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  -- Lift `z`, placed in the `w`-component, to the integral scalar extension.
  obtain ⟨t, ht⟩ := (integralSemilocalEquiv L v).surjective (Pi.single (placeAbove v w) z)
  have hξ : integralSemilocalToField L v t =
      (semilocalEquiv L v).symm (Pi.single (placeAbove v w)
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) z)) := by
    rw [AlgEquiv.eq_symm_apply, integralSemilocalEquiv_fieldCompatibility, ht]
    funext w'
    obtain rfl | hw' := eq_or_ne w' (placeAbove v w)
    · simp
    · simp [Pi.single_eq_of_ne hw']
  rw [Algebra.traceForm_apply, mul_comm, ← trace_semilocalEquiv_symm_single_mul, ← hξ]
  exact trace_integralSemilocalToField_mul_mem v hd t

/-- **The local trace dual is spanned by the global one.** The trace dual of `𝒪_w` over `𝒪_v` is
the `𝒪_w`-span of the image in `L_w` of the trace dual of `𝒪 L` over `𝒪 K`. -/
@[simp] theorem span_traceDual_one_eq_traceDual_one_adicCompletionIntegers :
    Submodule.span (w.adicCompletionIntegers L)
        (algebraMap L (w.adicCompletion L) ''
          Submodule.traceDual (𝒪 K) K (1 : Submodule (𝒪 L) L)) =
      Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun z hz ↦ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact algebraMap_mem_traceDual_adicCompletionIntegers v w hd
  -- Expand `z` along a trace-dual family of the projective `𝒪 K`-module `𝒪 L`.
  have := Module.finitePresentation_of_finite (𝒪 K) (𝒪 L)
  have : Module.Projective (𝒪 K) (𝒪 L) := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, b, y, hy, hb⟩ := exists_sum_trace_mul_smul_eq (𝒪 K) K (L := L) (B := 𝒪 L)
  rw [← sum_trace_mul_smul_algebraMap_eq v w (fun i ↦ algebraMap (𝒪 L) L (b i)) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr
    ⟨_, (algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers w (b i)).symm⟩)
  rw [Algebra.traceForm_apply] at hc
  rw [← hc, algebraMap_smul]
  exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)

/-- **Trace duals commute with completion**, as fractional ideals: extending the trace dual of
`𝒪 L` over `𝒪 K` to `𝒪_w` gives the trace dual of `𝒪_w` over `𝒪_v`. -/
@[simp] theorem extended_dual_one_eq_dual_one_adicCompletionIntegers :
    (FractionalIdeal.dual (𝒪 K) K (1 : FractionalIdeal (𝒪 L)⁰ L)).extended (w.adicCompletion L)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (FaithfulSMul.algebraMap_injective (𝒪 L) (w.adicCompletionIntegers L))) =
      FractionalIdeal.dual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : FractionalIdeal (w.adicCompletionIntegers L)⁰ (w.adicCompletion L)) := by
  have hmap : IsLocalization.map (S := L) (w.adicCompletion L)
      (algebraMap (𝒪 L) (w.adicCompletionIntegers L))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective (𝒪 L) (w.adicCompletionIntegers L))) =
      algebraMap L (w.adicCompletion L) := by
    refine IsFractionRing.ringHom_ext (A := 𝒪 L) fun x ↦ ?_
    rw [IsLocalization.map_eq, algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers]
  have hdual : ((FractionalIdeal.dual (𝒪 K) K (1 : FractionalIdeal (𝒪 L)⁰ L)) : Set L) =
      Submodule.traceDual (𝒪 K) K (1 : Submodule (𝒪 L) L) := by
    ext x
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_extended_eq_span, hmap, hdual,
    FractionalIdeal.coe_dual_one]
  exact span_traceDual_one_eq_traceDual_one_adicCompletionIntegers v w

/-- **The different commutes with completion.** The different ideal of `𝒪 L` over `𝒪 K` generates
in `𝒪_w` the different ideal of `𝒪_w` over `𝒪_v`. -/
@[simp] theorem map_differentIdeal_eq_differentIdeal_adicCompletionIntegers :
    (differentIdeal (𝒪 K) (𝒪 L)).map (algebraMap (𝒪 L) (w.adicCompletionIntegers L)) =
      differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  rw [← FractionalIdeal.coeIdeal_inj (K := w.adicCompletion L),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := L) (w.adicCompletion L)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective (𝒪 L) (w.adicCompletionIntegers L))),
    ← FractionalIdeal.extendedHom'_apply, coeIdeal_differentIdeal (𝒪 K) K L (𝒪 L),
    coeIdeal_differentIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L)
      (w.adicCompletionIntegers L), map_inv₀, FractionalIdeal.extendedHom'_apply,
    extended_dual_one_eq_dual_one_adicCompletionIntegers v w]

end TauCeti
