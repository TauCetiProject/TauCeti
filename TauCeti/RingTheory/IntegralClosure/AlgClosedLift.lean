/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation criterion for integrality and lifting along integral maps

This file provides two small lemmas connecting integral ring homomorphisms, valuation subrings,
and homomorphisms into algebraically closed fields:

* TauCeti.isIntegralElem_of_forall_valuationSubring: an element of a field L belonging to
  every valuation subring of L that contains the image of a ring homomorphism  : A →+* L is
  integral over .
* TauCeti.exists_algHom_comp_eq_of_isIntegral: given an integral k-algebra homomorphism
  φ : A →ₐ[k] C and a k-algebra homomorphism ψ : A →ₐ[k] L into an algebraically closed
  field L with RingHom.ker φ ≤ RingHom.ker ψ, there exists χ : C →ₐ[k] L with
  χ.comp φ = ψ.
* TauCeti.exists_ringHom_comp_eq_of_isIntegral: the ring-homomorphism specialization.

## References

* grh-lean, https://github.com/lsernau/grh-lean (commit
  72fead102f663d5c7a407964a13dc0cf9d977207), file
  src/Lib/Cohomology/PointClass/NoetherNormalization.lean (declarations
  New.Variety.isIntegralElem_of_valuationSubring and
  New.Variety.exists_algHom_comp_eq_of_integral); Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti

/-- An element of a field L that lies in every valuation subring containing the image of a ring
homomorphism  : A →+* L is integral over . -/
theorem isIntegralElem_of_forall_valuationSubring {A L : Type*} [CommRing A] [Field L]
    {f : A →+* L} {x : L}
    (h : ∀ V : ValuationSubring L, (∀ a : A, f a ∈ V) → x ∈ V) :
    f.IsIntegralElem x := by
  let : Algebra A L := f.toAlgebra
  refine (integralClosure A L).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge ?_
  simpa using fun V hV ↦ h V fun a ↦ hV isIntegral_algebraMap

/-- Let φ : A →ₐ[k] C be an integral k-algebra homomorphism and ψ : A →ₐ[k] L a k-algebra
homomorphism into an algebraically closed field L whose kernel contains that of φ. Then ψ
factors through φ as χ.comp φ = ψ for some χ : C →ₐ[k] L. -/
theorem exists_algHom_comp_eq_of_isIntegral {k A C L : Type*} [CommRing k] [CommRing A]
    [CommRing C] [Field L] [Algebra k A] [Algebra k C] [Algebra k L] [IsAlgClosed L]
    {φ : A →ₐ[k] C} {ψ : A →ₐ[k] L} (hφ_int : φ.IsIntegral)
    (h_ker : RingHom.ker φ ≤ RingHom.ker ψ) :
    ∃ χ : C →ₐ[k] L, χ.comp φ = ψ := by
  algebraize [φ.toRingHom, RingHom.kerLift ψ.toRingHom]
  have h_prime : (RingHom.ker ψ.toRingHom).IsPrime := RingHom.ker_isPrime ψ.toRingHom
  obtain ⟨q, -, hq_prime, hq⟩ :
      ∃ q ≥ (⊥ : Ideal C), q.IsPrime ∧ q.comap (algebraMap A C) = RingHom.ker ψ.toRingHom :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker ψ.toRingHom) (⊥ : Ideal C) h_ker
  have : q.LiesOver (RingHom.ker ψ.toRingHom) := ⟨hq.symm⟩
  have h_alg : Algebra.IsAlgebraic (A ⧸ RingHom.ker ψ.toRingHom) (C ⧸ q) :=
    (Algebra.IsIntegral.tower_top A).isAlgebraic
  have : Module.IsTorsionFree (A ⧸ RingHom.ker ψ.toRingHom) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (RingHom.kerLift_injective ψ.toRingHom)
  have : Module.IsTorsionFree (A ⧸ RingHom.ker ψ.toRingHom) (C ⧸ q) :=
    FaithfulSMul.to_isTorsionFree (A ⧸ RingHom.ker ψ.toRingHom) (C ⧸ q)
  let χ : C ⧸ q →ₐ[A ⧸ RingHom.ker ψ.toRingHom] L := IsAlgClosed.lift
  have h_lift (a : A) : χ (Ideal.Quotient.mk q (φ a)) = ψ a :=
    χ.commutes (Ideal.Quotient.mk (RingHom.ker ψ.toRingHom) a)
  refine ⟨{ χ.toRingHom.comp (Ideal.Quotient.mk q) with
    commutes' := fun r ↦ by
      change χ (Ideal.Quotient.mk q (algebraMap k C r)) = algebraMap k L r
      rw [← φ.commutes r, h_lift, ψ.commutes r] },
    AlgHom.ext h_lift⟩

/-- Let φ : A →+* C be an integral ring homomorphism and ψ : A →+* L a ring homomorphism into
an algebraically closed field L with RingHom.ker φ ≤ RingHom.ker ψ. Then ψ factors through
φ as χ.comp φ = ψ for some χ : C →+* L. -/
theorem exists_ringHom_comp_eq_of_isIntegral {A C L : Type*} [CommRing A] [CommRing C]
    [Field L] [IsAlgClosed L] {φ : A →+* C} {ψ : A →+* L} (hφ_int : φ.IsIntegral)
    (h_ker : RingHom.ker φ ≤ RingHom.ker ψ) :
    ∃ χ : C →+* L, χ.comp φ = ψ := by
  obtain ⟨χ, hχ⟩ := exists_algHom_comp_eq_of_isIntegral (k := ℤ)
    (φ := φ.toIntAlgHom) (ψ := ψ.toIntAlgHom) hφ_int h_ker
  exact ⟨χ.toRingHom, RingHom.ext fun a ↦ AlgHom.congr_fun hχ a⟩

end TauCeti
