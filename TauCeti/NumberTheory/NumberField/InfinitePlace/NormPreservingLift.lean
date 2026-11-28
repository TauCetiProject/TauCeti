/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Norms of complex conjugates over a subfield

An automorphism of `ℂ` can be replaced by a base-field-linear automorphism without changing
any of the resulting complex norms if and only if it preserves the infinite place on the base.
In particular, bounds on the norms of all conjugates over an imaginary quadratic field are
also bounds for the norms of all conjugates under arbitrary field automorphisms of `ℂ`.

The imaginary quadratic case is `New.Parameters.exists_algEquiv_norm_eq` in
`grh/src/New/Derivatives/Vacuum/IntegralVacuum.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open NumberField

namespace RingEquiv

/-- An automorphism of `ℂ` has the same norms on all elements as a `K`-algebra automorphism
exactly when its restriction and the structural embedding of `K` induce the same infinite
place. The replacement can be the original automorphism or its composite with complex
conjugation. -/
theorem exists_algEquiv_complex_norm_eq_iff {K : Type*} [Field K] [Algebra K ℂ]
    (σ : ℂ ≃+* ℂ) : (∃ τ : ℂ ≃ₐ[K] ℂ, ∀ z, ‖τ z‖ = ‖σ z‖) ↔
      InfinitePlace.mk (σ.toRingHom.comp (algebraMap K ℂ)) =
        InfinitePlace.mk (algebraMap K ℂ) := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine InfinitePlace.ext _ _ fun x ↦ ?_
    simpa only [InfinitePlace.apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, τ.commutes] using (hτ (algebraMap K ℂ x)).symm
  · intro h
    rcases InfinitePlace.mk_eq_iff.mp h with hσ | hσ
    · have hfix (x : K) : σ (algebraMap K ℂ x) = algebraMap K ℂ x :=
        RingHom.congr_fun hσ x
      exact ⟨AlgEquiv.ofRingEquiv hfix, fun _ ↦ rfl⟩
    · have hfix (x : K) : (σ.trans starRingAut) (algebraMap K ℂ x) = algebraMap K ℂ x := by
        simpa only [RingEquiv.trans_apply, starRingAut_apply, ComplexEmbedding.conjugate_coe_eq,
          starRingEnd_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom] using
          RingHom.congr_fun hσ x
      refine ⟨AlgEquiv.ofRingEquiv hfix, fun z ↦ ?_⟩
      simpa only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, starRingAut_apply,
        starRingEnd_apply] using Complex.norm_conj (σ z)

/-- If the base field has only one infinite place, a single base-field-linear automorphism
matches the norms of a given complex field automorphism on every complex number. -/
theorem exists_algEquiv_complex_norm_eq {K : Type*} [Field K] [Algebra K ℂ]
    [Subsingleton (InfinitePlace K)] (σ : ℂ ≃+* ℂ) :
    ∃ τ : ℂ ≃ₐ[K] ℂ, ∀ z, ‖τ z‖ = ‖σ z‖ :=
  σ.exists_algEquiv_complex_norm_eq_iff.mpr (Subsingleton.elim _ _)

end RingEquiv
