/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.NoetherianDescent
public import TauCeti.RingTheory.Localization.FinitePresentation

/-!
# Spreading finite étale algebras from a localization

Every finite étale algebra over `M⁻¹R` is the base change of a finite étale algebra over
`R[1/s]` for one `s ∈ M`. In particular, a finite étale algebra over `Rₚ` spreads to a
principal open neighbourhood of `p`. Neither `R` nor the localization is required to be
Noetherian, and the algebra is allowed to be zero.

We first take a finite étale model over a finitely generated subring of `M⁻¹R`, using
`Algebra.Etale.exists_subalgebra_fg_of_finite`. Finite presentation factors that subring's
inclusion through a principal localization. Base change of the model gives the result.
This supplies the affine existence step in spreading finite étale covers from a local scheme;
it does not assert gluing or uniqueness on a larger open.

## References

* [Stacks Project, Lemma 10.143.3](https://stacks.math.columbia.edu/tag/00U2)
* [Stacks Project, Lemma 32.20.4](https://stacks.math.columbia.edu/tag/0EY3)
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti.Algebra

/-- A finite étale algebra over a localization descends to a principal localization at a
single element of the denominator submonoid. For `M = p.primeCompl`, this is a finite étale
model on a principal open neighbourhood of `p`. -/
theorem exists_etale_finite_algEquiv_tensorProduct_localizationAway
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (B : Type*) [CommRing B] [Algebra S B] [Algebra.Etale S B] [Module.Finite S B]
    (M : Submonoid R) [IsLocalization M S] :
    ∃ s : M, ∃ (Bₛ : Type u) (_ : CommRing Bₛ) (_ : Algebra (Localization.Away (s : R)) Bₛ),
      Algebra.Etale (Localization.Away (s : R)) Bₛ ∧
      Module.Finite (Localization.Away (s : R)) Bₛ ∧
      letI := (IsLocalization.Away.lift (S := Localization.Away (s : R)) (s : R)
        (g := algebraMap R S) (IsLocalization.map_units S s)).toAlgebra
      Nonempty (B ≃ₐ[S] S ⊗[Localization.Away (s : R)] Bₛ) := by
  refine exists_etale_finite_algEquiv_tensorProduct_of_factorization
    (fun s : M ↦ Localization.Away (s : R))
    (fun s ↦ IsLocalization.Away.lift (S := Localization.Away (s : R)) (s : R)
      (g := algebraMap R S) (IsLocalization.map_units S s)) ?_ B
  intro P _ _ g
  -- Lift the initial ring to the universe of the localization diagram.
  let f := (algebraMap ℤ P).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
  have hf : f.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
      (.of_bijective ULift.ringEquiv.bijective)
  obtain ⟨s, φ, -, hφ⟩ := f.exists_factorization_localizationAway hf M
    ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom) g (by ext; simp [f])
  exact ⟨s, φ, hφ⟩

end TauCeti.Algebra
