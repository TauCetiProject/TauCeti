/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# Extension of ideal classes and principalization criteria

Mathlib's computation of `ClassGroup.extendedHom` on fractional ideals uses the canonical
fraction fields, and Mathlib's `ClassGroup.extendedHom_eq_one_of_forall_isPrincipal` gives one
implication between principalization of ideals and triviality of `ClassGroup.extendedHom`.

This file supplies:

* `ClassGroup.extendedHom_mk_of_isFractionRing`: evaluation of `ClassGroup.extendedHom` on a
  fractional ideal over arbitrary fraction fields;
* `ClassGroup.extendedHom_eq_map_comp_extendedHom`: factorization of `ClassGroup.extendedHom`
  along an injective algebra homomorphism without a `IsScalarTower` assumption;
* `ClassGroup.map_mk0_eq_one_iff`, `ClassGroup.map_eq_one_iff_forall_isPrincipal`,
  `ClassGroup.extendedHom_mk0_eq_one_iff`, `ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal`,
  and `ClassGroup.extendedHom_eq_one_iff_forall_fractionalIdeal_isPrincipal`: equivalences between
  triviality of induced class-group maps and principality of extended integral or fractional
  ideals.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

section Domains

variable {R B C K L : Type*} [CommRing R] [IsDomain R]
  [CommRing B] [IsDomain B] [Algebra R B] [Module.IsTorsionFree R B]

/-- Equal injective ring homomorphisms induce equal maps on class groups. -/
theorem map_congr {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    {f g : A →+* B} (hfg : f = g) (hf : Function.Injective f) (hg : Function.Injective g) :
    map f hf = map g hg := by
  subst hfg
  rfl

/-- `ClassGroup.extendedHom R B` is `ClassGroup.map` applied to `algebraMap R B`. -/
theorem extendedHom_eq_map (R B : Type*) [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.IsTorsionFree R B] :
    extendedHom R B = map (algebraMap R B) (FaithfulSMul.algebraMap_injective R B) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H α => exact (extendedHom_quotientMk R B α).trans (map_quotientMk _ _ α).symm

/-- Factorization of `ClassGroup.extendedHom` through an injective `R`-algebra homomorphism
`f : B →ₐ[R] C`, without requiring an intermediate `Algebra B C` instance. -/
theorem extendedHom_eq_map_comp_extendedHom [CommRing C] [IsDomain C] [Algebra R C]
    [Module.IsTorsionFree R C] (f : B →ₐ[R] C) (hf : Function.Injective f) :
    (map (f : B →+* C) hf).comp (extendedHom R B) = extendedHom R C := by
  rw [extendedHom_eq_map R B, extendedHom_eq_map R C]
  ext x
  exact (map_map (algebraMap R B) (FaithfulSMul.algebraMap_injective R B) (f : B →+* C) hf x).trans
    (DFunLike.congr_fun (map_congr f.comp_algebraMap _ _) x)

/-- Pointwise form of `ClassGroup.extendedHom_eq_map_comp_extendedHom`. -/
theorem extendedHom_eq_map_comp_extendedHom_apply [CommRing C] [IsDomain C] [Algebra R C]
    [Module.IsTorsionFree R C] (f : B →ₐ[R] C) (hf : Function.Injective f) (x : ClassGroup R) :
    map (f : B →+* C) hf (extendedHom R B x) = extendedHom R C x :=
  DFunLike.congr_fun (extendedHom_eq_map_comp_extendedHom f hf) x

variable [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra B L] [IsFractionRing B L]

/-- Extension of an ideal class can be computed using any choices of fraction fields. -/
theorem extendedHom_mk_of_isFractionRing (I : (FractionalIdeal R⁰ K)ˣ) :
    extendedHom R B (mk K I) = mk L
      (Units.map (FractionalIdeal.extendedHom L B :
        FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom I) := by
  have h (J : FractionalIdeal R⁰ K) :
      FractionalIdeal.extendedHom (FractionRing B) B
          (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R) J) =
        FractionalIdeal.canonicalEquiv B⁰ L (FractionRing B)
          (FractionalIdeal.extendedHom L B J) := by
    obtain ⟨a, A, _, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
    simp only [map_mul, FractionalIdeal.canonicalEquiv_spanSingleton,
      FractionalIdeal.canonicalEquiv_coeIdeal, FractionalIdeal.extendedHom_spanSingleton,
      FractionalIdeal.extendedHom_coeIdeal_eq_map]
    simp only [IsFractionRing.map, map_inv₀]
    -- The proof argument introduced by canonicalEquiv_spanSingleton requires unfolding
    -- Submonoid membership beyond the transparency used by rw.
    erw [IsLocalization.map_eq, IsLocalization.map_eq, IsLocalization.map_eq,
      IsLocalization.map_eq]
    rfl
  rw [← mk_canonicalEquiv K (FractionRing R) I, extendedHom_mk,
    ← mk_canonicalEquiv L (FractionRing B)]
  apply congrArg (mk (FractionRing B))
  apply Units.ext
  exact h I

/-- The extended class of an invertible fractional ideal is trivial if and only if the extended
fractional ideal is principal. -/
theorem extendedHom_mk_eq_one_iff_of_isFractionRing (I : (FractionalIdeal R⁰ K)ˣ) :
    extendedHom R B (mk K I) = 1 ↔
      (FractionalIdeal.extendedHom L B (I : FractionalIdeal R⁰ K) :
        Submodule B L).IsPrincipal := by
  rw [extendedHom_mk_of_isFractionRing (K := K) (L := L), mk_eq_one_iff]
  rfl

end Domains

section DedekindDomain

variable {A B K L : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]

/-- A nonzero integral ideal becomes principal along an injective ring homomorphism `f : A →+* B`
of Dedekind domains if and only if its class lies in the kernel of `ClassGroup.map f hf`. -/
theorem map_mk0_eq_one_iff (f : A →+* B) (hf : Function.Injective f) (I : (Ideal A)⁰) :
    map f hf (mk0 I) = 1 ↔ (I.1.map f).IsPrincipal := by
  rw [map_mk0, mk0_eq_one_iff]

/-- **Principalization criterion for `ClassGroup.map`.** For an injective ring homomorphism
`f : A →+* B` of Dedekind domains, the induced map on class groups is trivial if and only if every
ideal of `A` extends to a principal ideal of `B`. -/
theorem map_eq_one_iff_forall_isPrincipal (f : A →+* B) (hf : Function.Injective f) :
    map f hf = 1 ↔ ∀ I : Ideal A, (I.map f).IsPrincipal := by
  constructor
  · intro h I
    rcases eq_or_ne I ⊥ with rfl | hI
    · rw [Ideal.map_bot]
      exact bot_isPrincipal
    · exact (map_mk0_eq_one_iff f hf ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩).mp
        (DFunLike.congr_fun h _)
  · intro h
    ext x
    obtain ⟨I, rfl⟩ := mk0_surjective x
    exact (map_mk0_eq_one_iff f hf I).mpr (h I.1)

variable (A B) [Algebra A B] [Module.IsTorsionFree A B]

/-- A nonzero integral ideal becomes principal in an extension of Dedekind domains if and only if
its class lies in the kernel of `ClassGroup.extendedHom A B`. -/
theorem extendedHom_mk0_eq_one_iff (I : (Ideal A)⁰) :
    extendedHom A B (mk0 I) = 1 ↔ (I.1.map (algebraMap A B)).IsPrincipal := by
  rw [extendedHom_eq_map A B]
  exact map_mk0_eq_one_iff (algebraMap A B) (FaithfulSMul.algebraMap_injective A B) I

/-- **Principalization criterion for `ClassGroup.extendedHom` on ideals.** In an injective
extension `A → B` of Dedekind domains, `ClassGroup.extendedHom A B` is trivial if and only if
every ideal of `A` extends to a principal ideal of `B`. This upgrades Mathlib's
`ClassGroup.extendedHom_eq_one_of_forall_isPrincipal` to an equivalence. -/
theorem extendedHom_eq_one_iff_forall_isPrincipal :
    extendedHom A B = 1 ↔ ∀ I : Ideal A, (I.map (algebraMap A B)).IsPrincipal := by
  rw [extendedHom_eq_map A B]
  exact map_eq_one_iff_forall_isPrincipal (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

/-- **Principalization criterion for `ClassGroup.extendedHom` on fractional ideals.** In an
injective extension `A → B` of Dedekind domains with fraction fields `K` and `L`,
`ClassGroup.extendedHom A B` is trivial if and only if every fractional ideal of `A` extends to a
principal `B`-submodule of `L`. -/
theorem extendedHom_eq_one_iff_forall_fractionalIdeal_isPrincipal (K L : Type*)
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] :
    extendedHom A B = 1 ↔
      ∀ I : FractionalIdeal A⁰ K,
        (FractionalIdeal.extendedHom L B I : Submodule B L).IsPrincipal := by
  constructor
  · intro h I
    obtain rfl | ⟨u, rfl⟩ := GroupWithZero.eq_zero_or_unit I
    · rw [map_zero, FractionalIdeal.coeToSubmodule_zero]
      exact bot_isPrincipal
    · exact (extendedHom_mk_eq_one_iff_of_isFractionRing (K := K) (L := L) u).mp
        (DFunLike.congr_fun h _)
  · intro h
    ext x
    exact ClassGroup.induction K
      (fun u ↦ (extendedHom_mk_eq_one_iff_of_isFractionRing (K := K) (L := L) u).mpr (h u)) x

end DedekindDomain

end ClassGroup
