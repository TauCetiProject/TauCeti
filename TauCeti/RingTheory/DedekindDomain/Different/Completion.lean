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
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.RingTheory.DedekindDomain.Different.DualFamily
import TauCeti.RingTheory.NormTrace.BaseChange

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
  classical
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  have hF (ξ : v.adicCompletion K ⊗[K] L) :
      ∑ i, Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) (ξ * (1 ⊗ₜ b i)) •
        ((1 : v.adicCompletion K) ⊗ₜ[K] y i) = ξ := by
    induction ξ using TensorProduct.inductionOn with
    | add _ _ hξ hη =>
      conv_rhs => rw [← hξ, ← hη]
      simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
    | tmul a x =>
      conv_rhs => rw [← h x, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have ha : a ⊗ₜ[K] (x * b i) = a • ((1 : v.adicCompletion K) ⊗ₜ[K] (x * b i)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, map_smul, Algebra.trace_baseChange_tmul]
      simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one, mul_comm a,
        ← Algebra.smul_def, TensorProduct.smul_tmul]
  simpa [adicCompletionSemilocalEquiv_tmul, trace_adicCompletionSemilocalEquiv_symm_single_mul]
    using congrArg (fun ξ ↦ v.adicCompletionSemilocalEquiv K B L ξ (primeAbove v w))
      (hF ((v.adicCompletionSemilocalEquiv K B L).symm (Pi.single (primeAbove v w) z)))

omit [Module.IsTorsionFree R B] in
private theorem algebraMap_mem_traceDual_adicCompletionIntegers {d : L}
    (hd : d ∈ Submodule.traceDual R K (1 : Submodule B L)) :
    algebraMap L (w.adicCompletion L) d ∈
      Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
        (1 : Submodule (w.adicCompletionIntegers L) (w.adicCompletion L)) := by
  classical
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  rw [Submodule.mem_traceDual]; rintro _ hz
  obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
  obtain ⟨t, ht⟩ :=
    (v.adicCompletionIntegersSemilocalEquiv K B L).surjective (Pi.single (primeAbove v w) z)
  have hξ : v.adicCompletionIntegersSemilocalToField K B L t =
      (v.adicCompletionSemilocalEquiv K B L).symm (Pi.single (primeAbove v w)
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) z)) := by
    rw [AlgEquiv.eq_symm_apply, adicCompletionIntegersSemilocalEquiv_fieldCompatibility, ht]
    funext w'; obtain rfl | hw' := eq_or_ne w' (primeAbove v w) <;> simp [Pi.single_eq_of_ne, *]
  rw [Algebra.traceForm_apply, mul_comm,
    ← v.trace_adicCompletionSemilocalEquiv_symm_single_mul (B := B) w, ← hξ]
  clear ht hξ
  induction t using TensorProduct.inductionOn with
  | add _ _ hx hy => rw [map_add, add_mul, map_add]; exact add_mem hx hy
  | tmul a x =>
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨x, rfl⟩)
    refine ⟨a * algebraMap R (v.adicCompletionIntegers K) r, ?_⟩
    rw [trace_adicCompletionIntegersSemilocalToField_tmul_mul, mul_comm (algebraMap B L x),
      ← Algebra.traceForm_apply, ← hr]
    simp [ValuationSubring.algebraMap_apply, algebraMap_adicCompletionIntegers_apply]

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
  have := Module.finitePresentation_of_finite R B
  have : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.mpr fun _ ⟨d, hd, h⟩ ↦
    h ▸ algebraMap_mem_traceDual_adicCompletionIntegers v w hd)
  obtain ⟨n, b, y, hy, hb⟩ := exists_sum_trace_mul_smul_eq R K (L := L) (B := B)
  rw [← sum_trace_adicCompletion_mul_smul_eq v w (fun i ↦ algebraMap B L (b i)) y hb z]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  obtain ⟨c, hc⟩ := Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr
    ⟨_, (w.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers (b i)).symm⟩)
  rw [Algebra.traceForm_apply] at hc; rw [← hc, algebraMap_smul]
  exact Submodule.smul_of_tower_mem _ c (Submodule.subset_span ⟨y i, hy i, rfl⟩)

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
  have hmap : IsLocalization.map (S := L) (w.adicCompletion L)
      (algebraMap B (w.adicCompletionIntegers L))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))) =
      algebraMap L (w.adicCompletion L) := IsFractionRing.ringHom_ext (A := B) fun x ↦ by
    rw [IsLocalization.map_eq, algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers]
  have hdual : ((FractionalIdeal.dual R K (1 : FractionalIdeal B⁰ L)) : Set L) =
      Submodule.traceDual R K (1 : Submodule B L) := Set.ext fun x ↦ by
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coeToSubmodule_dual_one]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_dual_one,
    FractionalIdeal.coeToSubmodule_extended_eq_span, hmap, hdual]
  exact traceDual_one_adicCompletionIntegers_eq_span v w

include K L in
/-- **The different ideal commutes with adic completion** (with arbitrary residue fields):
`𝔇(𝒪_w / 𝒪_v) = 𝔇(B / R) · 𝒪_w`. -/
theorem differentIdeal_adicCompletionIntegers_eq_map :
    differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      (differentIdeal R B).map (algebraMap B (w.adicCompletionIntegers L)) := by
  have : Module.Finite R B := IsIntegralClosure.finite R K L B
  rw [← FractionalIdeal.coeIdeal_inj (K := w.adicCompletion L),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := L) (w.adicCompletion L)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective B (w.adicCompletionIntegers L))),
    ← FractionalIdeal.extendedHom'_apply, coeIdeal_differentIdeal R K L B,
    coeIdeal_differentIdeal (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L)
      (w.adicCompletionIntegers L), map_inv₀, FractionalIdeal.extendedHom'_apply,
    dual_one_adicCompletionIntegers_eq_extended v w]

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
  let f : B →+* ∀ u : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal},
      u.val.adicCompletionIntegers L :=
    (v.adicCompletionIntegersSemilocalEquiv K B L).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] _).toRingHom
  have hcomp (u : {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal}) :
      ((differentIdeal R B).map f).map (Pi.evalRingHom _ u) =
        differentIdeal (v.adicCompletionIntegers K) (u.val.adicCompletionIntegers L) := by
    rw [Ideal.map_map, differentIdeal_adicCompletionIntegers_eq_map (K := K) (L := L) v u.val]
    congr 1; ext x; simp [f]
  have hf : ((differentIdeal R B).map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] v.adicCompletionIntegers K ⊗[R] B)).map
      (v.adicCompletionIntegersSemilocalEquiv K B L) = (differentIdeal R B).map f :=
    Ideal.map_map (Algebra.TensorProduct.includeRight : B →ₐ[R] _).toRingHom
      (v.adicCompletionIntegersSemilocalEquiv K B L).toRingEquiv.toRingHom
  have hI : (differentIdeal R B).map f =
      Ideal.pi (Ideal.piOrderIso ((differentIdeal R B).map f)) :=
    SetLike.coe_injective <| by
      conv_lhs => rw [← Ideal.piOrderIso.symm_apply_apply ((differentIdeal R B).map f)]
      exact (Ideal.coe_piOrderIso_symm_apply _).trans (Set.ext fun _ ↦ by simp [Ideal.mem_pi])
  rw [hf, hI]
  refine congrArg Ideal.pi (funext fun u ↦ ?_)
  rw [← Ideal.map_evalRingHom_pi (I := Ideal.piOrderIso ((differentIdeal R B).map f)) u, ← hI,
    hcomp u]

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
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (w.adicCompletionIntegers L)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (differentIdeal_ne_bot_of_isSeparable (R := v.adicCompletionIntegers K)
      (K := v.adicCompletion K) (L := w.adicCompletion L)) hϖ
  rw [← multiplicity_differentIdeal_adicCompletionIntegers (K := K) (L := L) v w, hn,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance)]

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
