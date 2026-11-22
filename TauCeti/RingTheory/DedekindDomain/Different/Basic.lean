/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The different ideal

This file supplies general lemmas about trace-dual fractional ideals. The coercion result connects
the fractional-ideal and submodule trace duals, allowing submodule results such as localization to
be transferred to fractional ideals. The elementwise descriptions of the trace dual of `S` and of
the different ideal, each as the inverse of the other, are what read the different off valuations
and transport it along automorphisms and compatible ring equivalences. The different of the identity
extension is the unit ideal, which is used to compute the relative discriminant of the identity
extension. The trace criterion `TauCeti.dvd_differentIdeal_iff_forall_intTrace_mem` decides when an
`I * Q = p · B` divides the different ideal of an extension of Dedekind domains.
The multiplicity lemmas express divisibility by powers of an ideal and Dedekind's universal
`e - 1` bound as bounds on the different exponent.
For finite separable fraction-field extensions, the different is nonzero. When it is principal,
membership in the trace dual is tested by multiplication by a generator, and division by that
generator identifies `S` with its trace dual. This equivalence feeds the length computation of
the complementary-module quotient. Finally, `FractionalIdeal.dualEquiv` packages
`FractionalIdeal.dual` as an involutive permutation of the invertible fractional ideals.
-/

public section

open Module

open scoped nonZeroDivisors

namespace TauCeti

section Multiplicity

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- The characteristic property of the multiplicity of a proper ideal `P` of `B` in the different
ideal, such as the different exponent at a prime: `P ^ n` divides the different ideal exactly when
`n` is at most that multiplicity. -/
theorem pow_dvd_differentIdeal_iff_le_multiplicity {P : Ideal B} (hP : P ≠ ⊤) {n : ℕ} :
    P ^ n ∣ differentIdeal A B ↔ n ≤ multiplicity P (differentIdeal A B) :=
  (FiniteMultiplicity.of_not_isUnit (mt Ideal.isUnit_iff.mp hP)
    differentIdeal_ne_bot).pow_dvd_iff_le_multiplicity

/-- **Dedekind's different theorem, first part, as a bound on the exponent**: the multiplicity of
a prime `P` of `B` in the different ideal is at least `e - 1`, where `e` is the ramification index
of `P` over `A`. -/
theorem ramificationIdx_sub_one_le_multiplicity_differentIdeal (P : Ideal B) [P.IsPrime] :
    P.ramificationIdx A - 1 ≤ multiplicity P (differentIdeal A B) := by
  by_cases hp : P.under A = ⊥
  · simp [Ideal.eq_bot_of_under_eq_bot hp]
  have := (Ideal.IsPrime.under A P).isMaximal hp
  rw [← pow_dvd_differentIdeal_iff_le_multiplicity A Ideal.IsPrime.ne_top',
    ← Ideal.ramificationIdx'_eq_ramificationIdx (P.under A) P hp]
  exact pow_sub_one_dvd_differentIdeal A P _ hp
    (Ideal.dvd_iff_le.mpr (Ideal.le_pow_ramificationIdx' (p := P.under A) (P := P)))

end Multiplicity

universe uR uS uK uL

variable {R : Type uR} {S : Type uS} {K : Type uK} {L : Type uL}
variable [CommRing R] [CommRing S] [Field K] [Field L]
variable [Algebra R S] [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L]
variable [IsScalarTower R K L] [IsScalarTower R S L]
variable [IsDomain R]
variable [IsFractionRing R K] [IsFractionRing S L]
variable [IsIntegrallyClosed R] [IsIntegralClosure S R L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

namespace FractionalIdeal

/-- Over a domain, the fractional-ideal trace dual of one coerces to the submodule trace dual. -/
@[simp]
theorem coe_dual_one_of_isDomain [IsDomain S] :
    (↑(FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Submodule S L) =
      Submodule.traceDual R K (1 : Submodule S L) := by
  ext x
  simp [FractionalIdeal.dual]

end FractionalIdeal

omit [IsFractionRing S L] in
/-- **The trace dual of `S` is the inverse of the different ideal, elementwise**: an element of
`L` has integral traces against `S` exactly when it multiplies the different ideal of `S / R`
into `S`. -/
theorem mem_traceDual_one_iff_forall_mem_differentIdeal [IsDedekindDomain S]
    [IsTorsionFree R S] {x : L} :
    x ∈ Submodule.traceDual R K (1 : Submodule S L) ↔
      ∀ y ∈ differentIdeal R S, x * algebraMap S L y ∈ (1 : Submodule S L) := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  rw [← FractionalIdeal.coeToSubmodule_dual_one (A := R) (K := K),
    FractionalIdeal.mem_coeToSubmodule,
    ← inv_inv (FractionalIdeal.dual R K _),
    FractionalIdeal.mem_inv_iff (inv_ne_zero (FractionalIdeal.dual_ne_zero R K one_ne_zero)),
    ← coeIdeal_differentIdeal (A := R) (K := K) (L := L)]
  refine ⟨fun h y hy ↦ ?_, fun h w hw ↦ ?_⟩
  · exact Submodule.mem_one.mpr
      ((FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hy)))
  · obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hw
    exact (FractionalIdeal.mem_one_iff _).mpr (Submodule.mem_one.mp (h y hy))

include K L in
omit [IsFractionRing S L] in
/-- The different is nonzero when the chosen fraction-field extension is finite separable. -/
theorem differentIdeal_ne_bot_of_isSeparable [IsDedekindDomain S] [IsTorsionFree R S] :
    differentIdeal R S ≠ ⊥ := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L),
    coeIdeal_differentIdeal (K := K)]
  simp

include K in
/-- A generator of the different has nonzero image in the separable fraction-field extension. -/
theorem algebraMap_ne_zero_of_differentIdeal_eq_span
    [IsDedekindDomain S] [IsTorsionFree R S] {δ : S}
    (hδ : differentIdeal R S = Ideal.span {δ}) : algebraMap S L δ ≠ 0 := by
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective S L)]
  rintro rfl
  exact differentIdeal_ne_bot_of_isSeparable (K := K) (L := L) (by simpa using hδ)

omit [IsFractionRing S L] in
/-- For a principal different, membership in the complementary module is tested by
multiplication by its generator. -/
theorem mem_traceDual_one_iff_mul_of_differentIdeal_eq_span
    [IsDedekindDomain S] [IsTorsionFree R S] {δ : S}
    (hδ : differentIdeal R S = Ideal.span {δ}) {x : L} :
    x ∈ Submodule.traceDual R K (1 : Submodule S L) ↔
      x * algebraMap S L δ ∈ (1 : Submodule S L) := by
  rw [mem_traceDual_one_iff_forall_mem_differentIdeal, hδ]
  refine ⟨fun h ↦ h δ (Ideal.subset_span (Set.mem_singleton δ)), fun h y hy ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hy
  simpa [map_mul, mul_comm, mul_left_comm, Algebra.smul_def] using
    (1 : Submodule S L).smul_mem b h

/-- Division by a generator of the different identifies the integral closure with its
complementary module. -/
noncomputable def equivTraceDualOfDifferentIdealEqSpan
    [IsDedekindDomain S] [IsTorsionFree R S] {δ : S}
    (hδ : differentIdeal R S = Ideal.span {δ}) :
    S ≃ₗ[S] Submodule.traceDual R K (1 : Submodule S L) := by
  have hδL := algebraMap_ne_zero_of_differentIdeal_eq_span (K := K) (L := L) hδ
  let f : S →ₗ[S] Submodule.traceDual R K (1 : Submodule S L) :=
    { toFun := fun b ↦ ⟨algebraMap S L b / algebraMap S L δ,
        (mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hδ).mpr (by
          rw [div_mul_cancel₀ _ hδL]
          exact Submodule.mem_one.mpr ⟨b, rfl⟩)⟩
      map_add' := fun b c ↦ Subtype.ext (by simp [add_div])
      map_smul' := fun b c ↦ Subtype.ext (by simp [Algebra.smul_def, mul_div_assoc]) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro b c h
    exact IsFractionRing.injective S L ((div_left_inj₀ hδL).mp
      (congrArg Subtype.val h))
  · intro x
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp
      ((mem_traceDual_one_iff_mul_of_differentIdeal_eq_span hδ).mp x.property)
    exact ⟨b, Subtype.ext (by simp only [f, LinearMap.coe_mk, AddHom.coe_mk, hb,
      mul_div_cancel_right₀ _ hδL])⟩

/-- The complementary-module equivalence divides each integral element by the chosen
generator of the different. -/
@[simp]
theorem equivTraceDualOfDifferentIdealEqSpan_apply
    [IsDedekindDomain S] [IsTorsionFree R S] {δ : S}
    (hδ : differentIdeal R S = Ideal.span {δ}) (b : S) :
    (equivTraceDualOfDifferentIdealEqSpan (K := K) (L := L) hδ b : L) =
      algebraMap S L b / algebraMap S L δ := (rfl)

/-- The inverse complementary-module equivalence multiplies by the chosen generator
of the different. -/
@[simp]
theorem equivTraceDualOfDifferentIdealEqSpan_symm_apply
    [IsDedekindDomain S] [IsTorsionFree R S] {δ : S}
    (hδ : differentIdeal R S = Ideal.span {δ})
    (x : Submodule.traceDual R K (1 : Submodule S L)) :
    algebraMap S L ((equivTraceDualOfDifferentIdealEqSpan (K := K) (L := L) hδ).symm x) =
      (x : L) * algebraMap S L δ := by
  have h := congrArg Subtype.val
    ((equivTraceDualOfDifferentIdealEqSpan (K := K) (L := L) hδ).apply_symm_apply x)
  rw [equivTraceDualOfDifferentIdealEqSpan_apply] at h
  exact (div_eq_iff (algebraMap_ne_zero_of_differentIdeal_eq_span (K := K) hδ)).mp h

omit [IsFractionRing S L] in
/-- **The different ideal is the inverse of the trace dual of `S`, elementwise**: an element of
`S` lies in the different ideal of `S / R` exactly when it multiplies the trace dual of `S` into
`S`. -/
theorem mem_differentIdeal_iff_forall_mem_traceDual [IsDedekindDomain S] [IsTorsionFree R S]
    {y : S} :
    y ∈ differentIdeal R S ↔
      ∀ x ∈ Submodule.traceDual R K (1 : Submodule S L), x * algebraMap S L y ∈
        (1 : Submodule S L) := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  refine ⟨fun hy x hx ↦ ?_, fun h ↦ ?_⟩
  · have hmem : algebraMap S L y ∈ 1 / Submodule.traceDual R K (1 : Submodule S L) := by
      rw [← coeSubmodule_differentIdeal (A := R) (K := K)]
      exact ⟨y, hy, rfl⟩
    rw [mul_comm]
    exact Submodule.mem_div_iff_forall_mul_mem.mp hmem x hx
  · have hmem : algebraMap S L y ∈ IsLocalization.coeSubmodule L (differentIdeal R S) := by
      rw [coeSubmodule_differentIdeal (A := R) (K := K)]
      exact Submodule.mem_div_iff_forall_mul_mem.mpr fun x hx ↦ mul_comm x _ ▸ h x hx
    obtain ⟨y', hy', hyy'⟩ := hmem
    rwa [← IsFractionRing.injective S L hyy']

omit [IsDomain R] [IsFractionRing R K] [IsFractionRing S L] [IsIntegrallyClosed R]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- **The trace dual of `S` is stable under the automorphisms of `L / K`**: an automorphism maps
`S` onto itself and preserves the trace of `L / K`. -/
@[simp]
theorem apply_mem_traceDual_one_iff {σ : Gal(L/K)} {x : L} :
    σ x ∈ Submodule.traceDual R K (1 : Submodule S L) ↔
      x ∈ Submodule.traceDual R K (1 : Submodule S L) := by
  suffices h : ∀ (τ : Gal(L/K)) (z : L), z ∈ Submodule.traceDual R K (1 : Submodule S L) →
      τ z ∈ Submodule.traceDual R K (1 : Submodule S L) from
    ⟨fun hx ↦ by simpa using h σ⁻¹ _ hx, h σ x⟩
  refine fun τ z hz ↦ Submodule.mem_traceDual.mpr fun a ha ↦ ?_
  obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
  -- `Tr (τ z · b) = Tr (τ (z · τ⁻¹ b)) = Tr (z · τ⁻¹ b)`, and `τ⁻¹ b` lies in `S`
  rw [Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv τ.symm, map_mul,
    AlgEquiv.symm_apply_apply, ← AlgEquiv.coe_toAlgHom,
    ← algebraMap_galRestrict'_apply R S S (τ.symm : L →ₐ[K] L)]
  exact Submodule.mem_traceDual.mp hz _ (Submodule.mem_one.mpr ⟨_, rfl⟩)

omit [IsFractionRing S L] in
/-- **The different ideal is stable under the automorphisms of `L / K`**, acting on `S` through
their restrictions `galRestrict`. -/
@[simp]
theorem galRestrict_apply_mem_differentIdeal_iff [IsDedekindDomain S] [IsTorsionFree R S]
    {σ : Gal(L/K)} {y : S} :
    galRestrict R K L S σ y ∈ differentIdeal R S ↔ y ∈ differentIdeal R S := by
  suffices h : ∀ (τ : Gal(L/K)) (z : S), z ∈ differentIdeal R S →
      galRestrict R K L S τ z ∈ differentIdeal R S from
    ⟨fun hy ↦ by simpa [← MulEquiv.map_mul] using h σ⁻¹ _ hy, h σ y⟩
  refine fun τ z hz ↦ (mem_differentIdeal_iff_forall_mem_traceDual (K := K) (L := L)).mpr
    fun x hx ↦ ?_
  -- `x · τ z = τ (τ⁻¹ x · z)`, where `τ⁻¹ x` lies in the trace dual
  have hmul := (mem_differentIdeal_iff_forall_mem_traceDual (K := K) (L := L)).mp hz (τ.symm x)
    (apply_mem_traceDual_one_iff.mpr hx)
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp hmul
  refine Submodule.mem_one.mpr ⟨galRestrict R K L S τ b, ?_⟩
  rw [algebraMap_galRestrict_apply, hb, map_mul, AlgEquiv.apply_symm_apply,
    algebraMap_galRestrict_apply]

section TraceCriterion

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

/-- **The trace criterion for divisibility of the different ideal.** If `I * Q = p · B` for a
nonzero ideal `p` of `A`, then `I` divides `differentIdeal A B` exactly when the integral trace
carries the complement `Q` into `p`.

This upgrades Mathlib's one-way `not_dvd_differentIdeal_of_intTrace_notMem` to an equivalence.
The converse direction adapts the argument that Mathlib runs inline in
`pow_sub_one_dvd_differentIdeal_aux` and `dvd_differentIdeal_of_not_isSeparable`
(`Mathlib/RingTheory/DedekindDomain/Different.lean`, Andrew Yang). -/
theorem dvd_differentIdeal_iff_forall_intTrace_mem
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} (hp : p ≠ ⊥) (I Q : Ideal B) (hIQ : I * Q = Ideal.map (algebraMap A B) p) :
    I ∣ differentIdeal A B ↔ ∀ x ∈ Q, Algebra.intTrace A B x ∈ p := by
  refine ⟨fun hdvd x hx ↦ ?_, fun htr ↦ ?_⟩
  · by_contra hx'
    exact not_dvd_differentIdeal_of_intTrace_notMem A I Q hIQ x hx hx' hdvd
  let K := FractionRing A
  let L := FractionRing B
  have hp' : Ideal.map (algebraMap A B) p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have hQ : Q ≠ ⊥ := fun h ↦ hp' (by rw [← hIQ, h, Ideal.mul_bot])
  have hI : I ≠ ⊥ := fun h ↦ hp' (by rw [← hIQ, h, Ideal.bot_mul])
  -- `I⁻¹ = Q / p · B` as fractional ideals of `B`
  have hIinv : ((I : FractionalIdeal B⁰ L))⁻¹ = Q / p.map (algebraMap A B) := by
    apply inv_involutive.injective
    simp only [← hIQ, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
    rw [div_self (by simpa), mul_one, inv_inv]
  rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) hI, hIinv,
    Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coeToSubmodule,
    FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
  rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coeToSubmodule_one,
    ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
    FractionalIdeal.mem_coeToSubmodule, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
  simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hx
  intro y hy'
  obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
  obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
  have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
    rw [← Algebra.algebraMap_intTrace (A := A)]
    exact ⟨Algebra.intTrace A B z, htr z hz, rfl⟩
  rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']

end TraceCriterion

variable {D : Type*} [CommRing D] [IsDedekindDomain D]

/-- The different ideal of the identity extension of a Dedekind domain is the unit ideal. -/
@[simp]
theorem differentIdeal_self : differentIdeal D D = ⊤ := by
  -- `1` generates `D` over itself, so the derivative `1` of its minimal polynomial `X - 1` lies in
  -- the different ideal.
  have h := aeval_derivative_mem_differentIdeal D (FractionRing D) (FractionRing D) (1 : D)
    (Subsingleton.elim _ _)
  rwa [← map_one (algebraMap D D),
    minpoly.eq_X_sub_C_of_algebraMap_inj _ (FaithfulSMul.algebraMap_injective D D),
    Polynomial.derivative_X_sub_C, map_one, ← Ideal.eq_top_iff_one] at h

section Extension

variable {R S K L R' S' K' L' : Type*}
  [CommRing R] [CommRing S] [Field K] [Field L]
  [Algebra R S] [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [IsDomain R] [IsFractionRing R K] [IsFractionRing S L]
  [IsIntegrallyClosed R] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing R'] [CommRing S'] [Field K'] [Field L']
  [Algebra R' S'] [Algebra R' K'] [Algebra K' L'] [Algebra R' L'] [Algebra S' L']
  [IsScalarTower R' K' L'] [IsScalarTower R' S' L']
  [IsDomain R'] [IsFractionRing R' K'] [IsFractionRing S' L']
  [IsIntegrallyClosed R'] [IsIntegralClosure S' R' L']
  [FiniteDimensional K' L'] [Algebra.IsSeparable K' L']

/-- **Extending the fractional-ideal trace dual of one from a fraction-field span**: if an injective
ring map `f : S →+* S'` induces a fraction-field map `g : L →+* L'` sending the complementary module
of `S / R` to a spanning set of the complementary module of `S' / R'`, then `dual R K 1` extends
to `dual R' K' 1`. -/
theorem extended_dual_one_eq_dual_one_of_span
    [IsDomain S] [IsDomain S']
    (f : S →+* S') (hf : Function.Injective f) (g : L →+* L')
    (hgf : ∀ s : S, g (algebraMap S L s) = algebraMap S' L' (f s))
    (hspan : Submodule.traceDual R' K' (1 : Submodule S' L') =
      Submodule.span S' (g '' Submodule.traceDual R K (1 : Submodule S L))) :
    (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)).extended L'
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf) =
      FractionalIdeal.dual R' K' (1 : FractionalIdeal S'⁰ L') := by
  have hmap : IsLocalization.map (S := L) L' f
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf) = g :=
    IsFractionRing.ringHom_ext (A := S) fun x ↦ by
      rw [IsLocalization.map_eq, hgf]
  have hdual : ((FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Set L) =
      Submodule.traceDual R K (1 : Submodule S L) := Set.ext fun x ↦ by
    rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coeToSubmodule,
      FractionalIdeal.coe_dual_one_of_isDomain]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_extended_eq_span,
    hmap, hdual, FractionalIdeal.coe_dual_one_of_isDomain]
  exact hspan.symm

/-- **Extending the different ideal from the extended trace dual**: whenever `dual R K 1` extends
along an injective ring map `f : S →+* S'` to `dual R' K' 1`, the different ideal
`differentIdeal R S` pushes forward to `differentIdeal R' S'`. -/
theorem map_differentIdeal_eq_of_extended_dual_one_eq
    [IsDedekindDomain S] [Module.IsTorsionFree R S]
    [IsDedekindDomain S'] [Module.IsTorsionFree R' S']
    {f : S →+* S'} (hf : Function.Injective f)
    (hext : (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)).extended L'
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf) =
      FractionalIdeal.dual R' K' (1 : FractionalIdeal S'⁰ L')) :
    (differentIdeal R S).map f = differentIdeal R' S' := by
  rw [← FractionalIdeal.coeIdeal_inj (K := L'),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := L) L'
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf),
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal R K L S,
    coeIdeal_differentIdeal R' K' L' S',
    map_inv₀, FractionalIdeal.extendedHom'_apply, hext]

end Extension

end TauCeti

namespace RingEquiv

variable {A₁ K₁ B₁ L₁ A₂ K₂ B₂ L₂ : Type*}
  [CommRing A₁] [Field K₁] [CommRing B₁] [Field L₁]
  [Algebra A₁ K₁] [Algebra B₁ L₁] [Algebra A₁ B₁] [Algebra K₁ L₁] [Algebra A₁ L₁]
  [IsScalarTower A₁ K₁ L₁] [IsScalarTower A₁ B₁ L₁]
  [CommRing A₂] [Field K₂] [CommRing B₂] [Field L₂]
  [Algebra A₂ K₂] [Algebra B₂ L₂] [Algebra A₂ B₂] [Algebra K₂ L₂] [Algebra A₂ L₂]
  [IsScalarTower A₂ K₂ L₂] [IsScalarTower A₂ B₂ L₂]
  (eA : A₁ ≃+* A₂) (eK : K₁ ≃+* K₂) (eB : B₁ ≃+* B₂) (eL : L₁ ≃+* L₂)
  (hAK : ∀ a, eK (algebraMap A₁ K₁ a) = algebraMap A₂ K₂ (eA a))
  (hBL : ∀ b, eL (algebraMap B₁ L₁ b) = algebraMap B₂ L₂ (eB b))
  (hKL : (algebraMap K₂ L₂).comp eK.toRingHom = eL.toRingHom.comp (algebraMap K₁ L₁))

include eA eK eB hAK hBL hKL in
/-- **Compatible ring equivalences of integral towers transport membership in the complementary
module.** -/
theorem mem_traceDual_one_iff_of_equiv (z : L₁) :
    z ∈ Submodule.traceDual A₁ K₁ (1 : Submodule B₁ L₁) ↔
      eL z ∈ Submodule.traceDual A₂ K₂ (1 : Submodule B₂ L₂) := by
  have htr (u : L₁) : eK (Algebra.trace K₁ L₁ u) = Algebra.trace K₂ L₂ (eL u) := by
    rw [Algebra.trace_eq_of_equiv_equiv eK eL hKL, RingEquiv.apply_symm_apply]
  have hrange (t : K₁) : t ∈ (algebraMap A₁ K₁).range ↔ eK t ∈ (algebraMap A₂ K₂).range :=
    ⟨fun ⟨a, ha⟩ ↦ ⟨eA a, by rw [← ha, hAK]⟩,
      fun ⟨a, ha⟩ ↦ ⟨eA.symm a, eK.injective (by rw [hAK, eA.apply_symm_apply, ha])⟩⟩
  simp only [Submodule.mem_traceDual, Submodule.mem_one, forall_exists_index,
    forall_apply_eq_imp_iff, Algebra.traceForm_apply]
  exact ⟨fun h b ↦ by
      have hb := (hrange _).mp (h (eB.symm b))
      rwa [htr, map_mul, hBL, eB.apply_symm_apply] at hb,
    fun h b ↦ (hrange _).mpr (by rw [htr, map_mul, hBL]; exact h (eB b))⟩

variable [IsDomain A₁] [IsIntegrallyClosed A₁] [IsDedekindDomain B₁] [IsFractionRing A₁ K₁]
  [Module.IsTorsionFree A₁ B₁] [IsIntegralClosure B₁ A₁ L₁] [FiniteDimensional K₁ L₁]
  [Algebra.IsSeparable K₁ L₁]
  [IsDomain A₂] [IsIntegrallyClosed A₂] [IsDedekindDomain B₂] [IsFractionRing A₂ K₂]
  [Module.IsTorsionFree A₂ B₂] [IsIntegralClosure B₂ A₂ L₂] [FiniteDimensional K₂ L₂]
  [Algebra.IsSeparable K₂ L₂]

include eA eK eL hAK hBL hKL in
/-- **Compatible ring equivalences of integral closures transport membership in the different
ideal.** -/
theorem mem_differentIdeal_iff_of_equiv (y : B₁) :
    y ∈ differentIdeal A₁ B₁ ↔ eB y ∈ differentIdeal A₂ B₂ := by
  rw [TauCeti.mem_differentIdeal_iff_forall_mem_traceDual (K := K₁) (L := L₁),
    TauCeti.mem_differentIdeal_iff_forall_mem_traceDual (K := K₂) (L := L₂)]
  refine ⟨fun hy z' hz' ↦ ?_, fun hy z hz ↦ ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hy (eL.symm z') <|
      (eA.mem_traceDual_one_iff_of_equiv eK eB eL hAK hBL hKL _).mpr
        (by rwa [eL.apply_symm_apply]))
    exact Submodule.mem_one.mpr ⟨eB b, by
      have hb' := congrArg eL hb; rwa [hBL, map_mul, eL.apply_symm_apply, hBL] at hb'⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hy (eL z) <|
      (eA.mem_traceDual_one_iff_of_equiv eK eB eL hAK hBL hKL z).mp hz)
    exact Submodule.mem_one.mpr ⟨eB.symm b, eL.injective (by rw [hBL, eB.apply_symm_apply, hb,
      map_mul, hBL])⟩

include eA eK eL hAK hBL hKL in
/-- **Compatible ring equivalences of integral closures transport the different ideal.** -/
theorem map_differentIdeal_of_equiv :
    (differentIdeal A₁ B₁).map (eB : B₁ →+* B₂) = differentIdeal A₂ B₂ := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective (eB : B₁ →+* B₂) (by simpa using eB.surjective)]
  exact ⟨fun ⟨x, hx, hxy⟩ ↦
      hxy ▸ (eA.mem_differentIdeal_iff_of_equiv eK eB eL hAK hBL hKL x).mp hx,
    fun hy ↦ ⟨eB.symm y, (eA.mem_differentIdeal_iff_of_equiv eK eB eL hAK hBL hKL _).mpr
      (by rwa [eB.apply_symm_apply]), eB.apply_symm_apply y⟩⟩

end RingEquiv

namespace FractionalIdeal

section DualEquiv

variable (R K : Type*) {S L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [CommRing S] [IsDedekindDomain S] [Algebra R L] [Algebra R S]
  [Algebra S L] [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing S L]
  [IsIntegralClosure S R L]

/-- In a finite separable extension of fraction fields of Dedekind domains, the trace dual
`FractionalIdeal.dual` restricts to an involutive permutation of `(FractionalIdeal S⁰ L)ˣ`. -/
noncomputable def dualEquiv : Equiv.Perm (FractionalIdeal S⁰ L)ˣ where
  toFun I := Units.mk0 (dual R K (I : FractionalIdeal S⁰ L)) (dual_ne_zero R K I.ne_zero)
  invFun I := Units.mk0 (dual R K (I : FractionalIdeal S⁰ L)) (dual_ne_zero R K I.ne_zero)
  left_inv I := Units.ext (dual_dual R K (I : FractionalIdeal S⁰ L))
  right_inv I := Units.ext (dual_dual R K (I : FractionalIdeal S⁰ L))

/-- Coercion of `FractionalIdeal.dualEquiv` to `FractionalIdeal S⁰ L` is `FractionalIdeal.dual`. -/
@[simp]
theorem coe_dualEquiv (I : (FractionalIdeal S⁰ L)ˣ) :
    ((dualEquiv R K I : (FractionalIdeal S⁰ L)ˣ) : FractionalIdeal S⁰ L) =
      dual R K (I : FractionalIdeal S⁰ L) :=
  (rfl)

/-- `FractionalIdeal.dualEquiv` is its own inverse. -/
@[simp]
theorem dualEquiv_symm :
    (dualEquiv R K : Equiv.Perm (FractionalIdeal S⁰ L)ˣ).symm = dualEquiv R K :=
  (rfl)

/-- Applying `FractionalIdeal.dualEquiv` twice is the identity. -/
@[simp]
theorem dualEquiv_dualEquiv (I : (FractionalIdeal S⁰ L)ˣ) :
    dualEquiv R K (dualEquiv R K I) = I :=
  (dualEquiv R K).symm_apply_apply I

/-- The trace dual of an invertible fractional ideal `I` is the inverse different `dualEquiv R K 1`
times `I⁻¹`. -/
theorem dualEquiv_eq_mul_inv (I : (FractionalIdeal S⁰ L)ˣ) :
    dualEquiv R K I = dualEquiv R K 1 * I⁻¹ :=
  Units.ext <| by
    rw [Units.val_mul, coe_dualEquiv, coe_dualEquiv, Units.val_one, Units.val_inv_eq_inv_val,
      dual_eq_mul_inv]

/-- The trace dual of `I⁻¹` is the inverse different `dualEquiv R K 1` times `I`. -/
theorem dualEquiv_inv (I : (FractionalIdeal S⁰ L)ˣ) :
    dualEquiv R K I⁻¹ = dualEquiv R K 1 * I := by
  rw [dualEquiv_eq_mul_inv, inv_inv]

/-- Multiplying `dualEquiv R K I` on the right by `I` yields the inverse different
`dualEquiv R K 1`. -/
theorem dualEquiv_mul_self (I : (FractionalIdeal S⁰ L)ˣ) :
    dualEquiv R K I * I = dualEquiv R K 1 := by
  rw [dualEquiv_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- Multiplying `I` on the right by `dualEquiv R K I` yields the inverse different
`dualEquiv R K 1`. -/
theorem self_mul_dualEquiv (I : (FractionalIdeal S⁰ L)ˣ) :
    I * dualEquiv R K I = dualEquiv R K 1 := by
  rw [mul_comm, dualEquiv_mul_self]

/-- The quotient of the trace duals of `J` and `I` is `I / J`. -/
@[simp]
theorem dualEquiv_div_dualEquiv (J I : (FractionalIdeal S⁰ L)ˣ) :
    dualEquiv R K J / dualEquiv R K I = I / J := by
  rw [dualEquiv_eq_mul_inv R K J, dualEquiv_eq_mul_inv R K I, mul_div_mul_comm, div_self', one_mul,
    inv_div_inv]

end DualEquiv

end FractionalIdeal

end
