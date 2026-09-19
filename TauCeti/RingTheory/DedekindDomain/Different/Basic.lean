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
be transferred to fractional ideals. The elementwise description of the trace dual of `S` as the
inverse of the different ideal is what reads the different off valuations. The identity-extension
trace-dual theorem gives the unit different, which is used to compute the relative discriminant of
the identity extension. The trace criterion `TauCeti.dvd_differentIdeal_iff_forall_intTrace_mem`
decides when an ideal `I` with `I * Q = p · B` divides the different ideal of an extension of
Dedekind domains.
-/

public section

open Module

open scoped nonZeroDivisors

namespace TauCeti

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
  -- Rewriting through `FractionalIdeal.coe_mk` directly requires Mathlib's transparency override.
  -- Extensionality reduces the coercion equality to the definitionally equal membership predicates.
  change x ∈ FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) ↔ _
  have h : (1 : FractionalIdeal S⁰ L) ≠ 0 := one_ne_zero
  simp [FractionalIdeal.dual, h]
  -- In the nonzero branch, `dual` stores the trace-dual submodule itself; only its proof field is
  -- discarded by the coercion, so the two remaining membership predicates are definitionally equal.
  rfl

end FractionalIdeal

/-- **The trace dual of `S` is the inverse of the different ideal, elementwise**: an element of
`L` has integral traces against `S` exactly when it multiplies the different ideal of `S / R`
into `S`. -/
theorem mem_traceDual_one_iff_forall_mem_differentIdeal [IsDedekindDomain S]
    [IsTorsionFree R S] {x : L} :
    x ∈ Submodule.traceDual R K (1 : Submodule S L) ↔
      ∀ y ∈ differentIdeal R S, x * algebraMap S L y ∈ (1 : Submodule S L) := by
  rw [← FractionalIdeal.coe_dual_one (A := R) (K := K), FractionalIdeal.mem_coe,
    ← inv_inv (FractionalIdeal.dual R K _),
    FractionalIdeal.mem_inv_iff (inv_ne_zero (FractionalIdeal.dual_ne_zero R K one_ne_zero)),
    ← coeIdeal_differentIdeal (A := R) (K := K) (L := L)]
  refine ⟨fun h y hy ↦ ?_, fun h w hw ↦ ?_⟩
  · exact Submodule.mem_one.mpr
      ((FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hy)))
  · obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hw
    exact (FractionalIdeal.mem_one_iff _).mpr (Submodule.mem_one.mp (h y hy))

section TraceCriterion

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

/-- **The trace criterion for divisibility of the different ideal.** If `I * Q = p · B` for a
nonzero ideal `p` of `A`, then `I` divides `differentIdeal A B` exactly when the integral trace
carries the complement `Q` into `p`.

This upgrades Mathlib's one-way `not_dvd_differentIdeal_of_intTrace_not_mem` to an equivalence.
The converse direction adapts the argument that Mathlib runs inline in
`pow_sub_one_dvd_differentIdeal_aux` and `dvd_differentIdeal_of_not_isSeparable`
(`Mathlib/RingTheory/DedekindDomain/Different.lean`, Andrew Yang). -/
theorem dvd_differentIdeal_iff_forall_intTrace_mem
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} (hp : p ≠ ⊥) (I Q : Ideal B) (hIQ : I * Q = Ideal.map (algebraMap A B) p) :
    I ∣ differentIdeal A B ↔ ∀ x ∈ Q, Algebra.intTrace A B x ∈ p := by
  refine ⟨fun hdvd x hx ↦ ?_, fun htr ↦ ?_⟩
  · by_contra hx'
    exact not_dvd_differentIdeal_of_intTrace_not_mem A I Q hIQ x hx hx' hdvd
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
  rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
  rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
    ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
    FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
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

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The trace dual of the unit submodule is the unit submodule for the identity extension of a
domain to its fraction field. -/
@[simp]
theorem traceDual_one_fractionRing_self :
    letI : Algebra (FractionRing A) (FractionRing A) :=
      FractionRing.liftAlgebra A (FractionRing A)
    Submodule.traceDual A (FractionRing A) (1 : Submodule A (FractionRing A)) = 1 := by
  let _ : Algebra (FractionRing A) (FractionRing A) :=
    FractionRing.liftAlgebra A (FractionRing A)
  have htrace (x : FractionRing A) : Algebra.trace (FractionRing A) (FractionRing A) x = x := by
    have htrace' := @Algebra.trace_eq_of_equiv_equiv
      (FractionRing A) (FractionRing A) (FractionRing A) (FractionRing A)
      _ _ _ _ (Algebra.id (FractionRing A))
      (FractionRing.liftAlgebra A (FractionRing A)) (RingEquiv.refl _) (RingEquiv.refl _) ?_ x
    · simpa [Algebra.trace_self_apply] using htrace'.symm
    · ext y
      -- The compatibility goal is definitionally the identity algebra map after
      -- reducing the two identity equivalences and the lifted algebra wrapper.
      change algebraMap (FractionRing A) (FractionRing A) y = y
      rw [FractionRing.algebraMap_liftAlgebra]
      exact IsLocalization.lift_id y
  apply le_antisymm
  · intro x hx
    have hx' := (@Submodule.mem_traceDual A (FractionRing A) (FractionRing A) A
      _ _ _ _ _ _ _ (FractionRing.liftAlgebra A (FractionRing A)) _ _ _).mp hx 1 (by simp)
    rw [Submodule.mem_one]
    exact (by simpa [Algebra.traceForm_apply, htrace x] using hx')
  · intro x hx
    rw [Submodule.mem_traceDual]
    intro y hy
    rw [Submodule.mem_one] at hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    refine ⟨x * y, ?_⟩
    rw [Algebra.traceForm_apply, htrace]
    simp

variable {D : Type*} [CommRing D] [IsDedekindDomain D]

/-- The different ideal of the identity extension of a Dedekind domain is the unit ideal. -/
@[simp]
theorem differentIdeal_self : differentIdeal D D = ⊤ := by
  let _ : Algebra (FractionRing D) (FractionRing D) :=
    FractionRing.liftAlgebra D (FractionRing D)
  rw [differentIdeal]
  -- Unfolding `differentIdeal` and its coercion exposes the quotient's ambient
  -- submodule while retaining the comap by `Algebra.linearMap`.
  change Submodule.comap (Algebra.linearMap D (FractionRing D))
    (1 / (Submodule.traceDual D (FractionRing D) 1)) = ⊤
  rw [traceDual_one_fractionRing_self]
  -- This is a coercion bridge: the unfolded different uses submodule division,
  -- while the available normalization lemmas for division apply to fractional ideals.
  rw [show (1 / (1 : Submodule D (FractionRing D))) =
      (↑((1 : FractionalIdeal D⁰ (FractionRing D)) / 1) : Submodule D (FractionRing D)) by
    rw [FractionalIdeal.coe_div one_ne_zero, FractionalIdeal.coe_one]]
  rw [FractionalIdeal.div_one, FractionalIdeal.coe_one]
  ext x
  simp [Submodule.mem_one]

end TauCeti

end
