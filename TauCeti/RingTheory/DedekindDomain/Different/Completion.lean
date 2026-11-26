/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Multiplicity
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Semilocal
public import TauCeti.RingTheory.DedekindDomain.Different.Discriminant
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import TauCeti.RingTheory.DedekindDomain.Different.Semilocal
import TauCeti.RingTheory.NormTrace.Pi

/-!
# The trace-dual different under adic completion

Let `R ⊆ B` be Dedekind domains with fraction fields `K ⊆ L`, with `B` the integral closure of `R`
in the finite separable extension `L / K`, and `w ∣ v` height-one primes. With no finiteness or
separability hypothesis on residue fields, the complementary module, different ideal and exponent,
complementary-module length, and discriminant valuation all commute with passing to `𝒪_w / 𝒪_v` in
`L_w / K_v`. All `HeightOneSpectrum` declarations use `open scoped AdicCompletionExtension`, which
provides the completed algebra structures and scoped finiteness, integral-closure, and separability
instances.

## Main results

* `sum_trace_adicCompletion_mul_smul_eq`, `traceDual_one_adicCompletionIntegers_eq_span`,
  `dual_one_adicCompletionIntegers_eq_extended`: trace-dual expansions and complementary module.
* `differentIdeal_adicCompletionIntegers_eq_map`, `differentIdeal_adicCompletionIntegersSemilocal`,
  `multiplicity_differentIdeal_adicCompletionIntegers`,
  `differentIdeal_adicCompletionIntegers_eq_maximalIdeal_pow`: completed different ideal & exponent.
* `length_traceDual_adicCompletionIntegers_quotient`, `ord_discr_adicCompletionIntegers`,
  `TauCeti.length_traceDual_adicCompletionIntegers_quotient_eq`,
  `Module.Basis.ord_discr_adicCompletionIntegers_eq`: length and discriminant invariance.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §§3–4.
* J. Neukirch, *Algebraic Number Theory*, Chapter III, Proposition (2.2).
-/

public section
noncomputable section

open TauCeti IsDedekindDomain TensorProduct
open scoped AdicCompletionExtension nonZeroDivisors

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  [IsIntegralClosure B R L] [Module.IsTorsionFree R B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

private abbrev primeAbove : {u : HeightOneSpectrum B // u.asIdeal.LiesOver v.asIdeal} :=
  ⟨w, inferInstance⟩

omit [Module.IsTorsionFree R B] in
/-- **Trace-dual expansions pass to completions.** If `x = ∑ᵢ Tr_{L/K}(x bᵢ) yᵢ` for every `x ∈ L`,
then `z = ∑ᵢ Tr_{L_w/K_v}(z bᵢ) yᵢ` for every `z ∈ L_w`. -/
theorem sum_trace_adicCompletion_mul_smul_eq {ι : Type*} [Fintype ι] (b y : ι → L)
    (h : ∀ x : L, ∑ i, Algebra.trace K L (x * b i) • y i = x) (z : w.adicCompletion L) :
    ∑ i, Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
        (z * algebraMap L (w.adicCompletion L) (b i)) • algebraMap L (w.adicCompletion L) (y i) =
      z := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Module.IsTorsionFree R B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R B)
  simpa [adicCompletionSemilocalEquiv_tmul] using
    (v.adicCompletionSemilocalEquiv K B L).sum_trace_mul_smul_eq b y h (primeAbove v w) z

omit [Module.IsTorsionFree R B] in
/-- **The completed complementary module is spanned by the global one** (with arbitrary residue
fields): `Submodule.traceDual 𝒪_v K_v 1` is the `𝒪_w`-span of `Submodule.traceDual R K 1`. -/
theorem traceDual_one_adicCompletionIntegers_eq_span :
    Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)) =
      Submodule.span (w.adicCompletionIntegers L)
        (algebraMap L (w.adicCompletion L) '' Submodule.traceDual R K (1 : Submodule B L)) := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Module.IsTorsionFree R B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R B)
  exact ((v.adicCompletionSemilocalEquiv K B L).span_traceDual_one_eq_traceDual_one_of_semilocal
    (v.adicCompletionIntegersSemilocalEquiv K B L)
    (fun u ↦ algebraMap L (u.val.adicCompletion L))
    (fun u ↦ algebraMap B (u.val.adicCompletionIntegers L))
    (fun a x u ↦ v.adicCompletionSemilocalEquiv_tmul a x u)
    (fun a x u ↦ v.adicCompletionIntegersSemilocalEquiv_tmul a x u)
    (fun u x ↦ (u.val.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers x).symm)
    (primeAbove v w)).symm

omit [Module.IsTorsionFree R B] in
/-- **The fractional-ideal trace dual of the ring of integers commutes with adic completion**: the
trace dual of `B` over `R` (`1`) extends to the trace dual of `𝒪_w` over `𝒪_v`. -/
theorem dual_one_adicCompletionIntegers_eq_extended :
    haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
    FractionalIdeal.dual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : FractionalIdeal (w.adicCompletionIntegers L)⁰ (w.adicCompletion L)) =
      (FractionalIdeal.dual R K (1 : FractionalIdeal B⁰ L)).extended (w.adicCompletion L)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))) := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  have : Module.IsTorsionFree R B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R B)
  exact ((v.adicCompletionSemilocalEquiv K B L).extended_dual_one_eq_dual_one_of_semilocal
    (v.adicCompletionIntegersSemilocalEquiv K B L)
    (fun u ↦ algebraMap L (u.val.adicCompletion L))
    (fun u ↦ algebraMap B (u.val.adicCompletionIntegers L))
    (fun a x u ↦ v.adicCompletionSemilocalEquiv_tmul a x u)
    (fun a x u ↦ v.adicCompletionIntegersSemilocalEquiv_tmul a x u)
    (fun u x ↦ (u.val.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers x).symm)
    (primeAbove v w)
    (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))).symm

include K L in
/-- **The different ideal commutes with adic completion** (with arbitrary residue fields):
`𝔇(𝒪_w / 𝒪_v) = 𝔇(B / R) · 𝒪_w`. -/
theorem differentIdeal_adicCompletionIntegers_eq_map :
    differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      (differentIdeal R B).map (algebraMap B (w.adicCompletionIntegers L)) := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  exact ((v.adicCompletionSemilocalEquiv K B L).map_differentIdeal_eq_differentIdeal_of_semilocal
    (v.adicCompletionIntegersSemilocalEquiv K B L)
    (fun u ↦ algebraMap L (u.val.adicCompletion L))
    (fun u ↦ algebraMap B (u.val.adicCompletionIntegers L))
    (fun a x u ↦ v.adicCompletionSemilocalEquiv_tmul a x u)
    (fun a x u ↦ v.adicCompletionIntegersSemilocalEquiv_tmul a x u)
    (fun u x ↦ (u.val.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers x).symm)
    (primeAbove v w)
    (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))).symm

/-- **The different of the integral semilocal algebra, read componentwise.** Extending
`differentIdeal R B` to `𝒪_v ⊗[R] B` and transporting along `adicCompletionIntegersSemilocalEquiv`
yields the product of the completed different ideals above `v`. -/
theorem differentIdeal_adicCompletionIntegersSemilocal :
    haveI : Module.Finite R B := IsIntegralClosure.finite R K L B
    ((differentIdeal R B).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] v.adicCompletionIntegers K ⊗[R] B)).map
        (v.adicCompletionIntegersSemilocalEquiv K B L) =
      Ideal.pi fun u ↦
        differentIdeal (v.adicCompletionIntegers K) (u.val.adicCompletionIntegers L) := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  exact (v.adicCompletionIntegersSemilocalEquiv K B L).map_differentIdeal_semilocal
    (fun u ↦ algebraMap B (u.val.adicCompletionIntegers L))
    (fun a x u ↦ v.adicCompletionIntegersSemilocalEquiv_tmul a x u)
    fun u ↦ (differentIdeal_adicCompletionIntegers_eq_map (K := K) (L := L) v u.val).symm

include K L in
/-- **Completion preserves the different exponent**: the multiplicity of the maximal ideal of `𝒪_w`
in `𝔇(𝒪_w / 𝒪_v)` equals the multiplicity of `w` in `𝔇(B / R)`. -/
@[simp]
theorem multiplicity_differentIdeal_adicCompletionIntegers :
    multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        (differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) =
      multiplicity w.asIdeal (differentIdeal R B) := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  rw [differentIdeal_adicCompletionIntegers_eq_map (K := K) (L := L) v w]
  exact w.multiplicity_map_adicCompletionIntegers (differentIdeal R B)
    (differentIdeal_ne_bot_of_isSeparable (K := K) (L := L))

include K L in
/-- **The completed different ideal as a power of the maximal ideal.** -/
theorem differentIdeal_adicCompletionIntegers_eq_maximalIdeal_pow :
    differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^
        multiplicity w.asIdeal (differentIdeal R B) := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  rw [← multiplicity_differentIdeal_adicCompletionIntegers (K := K) (L := L) v w]
  exact (differentIdeal _ _).eq_maximalIdeal_pow_multiplicity
    (differentIdeal_ne_bot_of_isSeparable (R := v.adicCompletionIntegers K)
      (K := v.adicCompletion K) (L := w.adicCompletion L))

/-- **Completed complementary-module length formula**: `length 𝒪_v (C_w / 𝒪_w) = d(w ∣ v) * f`. -/
theorem length_traceDual_adicCompletionIntegers_quotient :
    Module.length (v.adicCompletionIntegers K)
        ((Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
            (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L))) ⧸
          (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)).comap
            (Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
              (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L))).subtype) =
      (multiplicity w.asIdeal (differentIdeal R B) : ℕ∞) * w.asIdeal.inertiaDeg R := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  rw [length_traceDual_quotient_eq_multiplicity_mul_finrank,
    multiplicity_differentIdeal_adicCompletionIntegers (K := K) (L := L) v w,
    finrank_residueField_adicCompletionIntegers (K := K) (L := L) v w]

include K L in
/-- **Completed discriminant valuation formula**: `Ring.ord 𝒪_v (discr 𝒪_v b) = d(w ∣ v) * f`. -/
theorem ord_discr_adicCompletionIntegers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) :
    Ring.ord (v.adicCompletionIntegers K) (Algebra.discr (v.adicCompletionIntegers K) b) =
      (multiplicity w.asIdeal (differentIdeal R B) : ℕ∞) * w.asIdeal.inertiaDeg R := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  rw [ord_discr_eq_multiplicity_mul_finrank (v.adicCompletion K) (w.adicCompletion L) b,
    multiplicity_differentIdeal_adicCompletionIntegers (K := K) (L := L) v w,
    finrank_residueField_adicCompletionIntegers (K := K) (L := L) v w]

end IsDedekindDomain.HeightOneSpectrum

section DiscreteValuationRing

open IsDiscreteValuationRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
  [IsIntegralClosure B A L] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]
  [Algebra.IsSeparable K L]

/-- **Completing a DVR extension preserves the complementary-module length.** -/
theorem TauCeti.length_traceDual_adicCompletionIntegers_quotient_eq [FiniteDimensional K L] :
    Module.length ((maximalIdeal A).adicCompletionIntegers K)
        ((Submodule.traceDual ((maximalIdeal A).adicCompletionIntegers K)
            ((maximalIdeal A).adicCompletion K)
            (1 : Submodule ((maximalIdeal B).adicCompletionIntegers L)
              ((maximalIdeal B).adicCompletion L))) ⧸
          (1 : Submodule ((maximalIdeal B).adicCompletionIntegers L)
              ((maximalIdeal B).adicCompletion L)).comap
            (Submodule.traceDual ((maximalIdeal A).adicCompletionIntegers K)
              ((maximalIdeal A).adicCompletion K)
              (1 : Submodule ((maximalIdeal B).adicCompletionIntegers L)
                ((maximalIdeal B).adicCompletion L))).subtype) =
      Module.length A ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype) := by
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  rw [(maximalIdeal A).length_traceDual_adicCompletionIntegers_quotient (K := K) (L := L)
      (maximalIdeal B), length_traceDual_quotient_eq_multiplicity_mul_finrank,
    TauCeti.IsDiscreteValuationRing.asIdeal_maximalIdeal,
    TauCeti.IsLocalRing.inertiaDeg_maximalIdeal]

include K L in
/-- **Completing a DVR extension preserves the discriminant valuation.** -/
theorem _root_.Module.Basis.ord_discr_adicCompletionIntegers_eq {ι ι' : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι A B)
    (b' : Module.Basis ι' ((maximalIdeal A).adicCompletionIntegers K)
      ((maximalIdeal B).adicCompletionIntegers L)) :
    Ring.ord ((maximalIdeal A).adicCompletionIntegers K)
        (Algebra.discr ((maximalIdeal A).adicCompletionIntegers K) b') =
      Ring.ord A (Algebra.discr A b) := by
  have : Module.Finite A B := .of_basis b
  have := IsIntegralClosure.isLocalization A K L B
  have : FiniteDimensional K L := .of_basis (b.localizationLocalization K A⁰ L)
  rw [(maximalIdeal A).ord_discr_adicCompletionIntegers (K := K) (L := L) (maximalIdeal B) b',
    ord_discr_eq_multiplicity_mul_finrank K L b,
    TauCeti.IsDiscreteValuationRing.asIdeal_maximalIdeal,
    TauCeti.IsLocalRing.inertiaDeg_maximalIdeal]

end DiscreteValuationRing

end
