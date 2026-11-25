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
inclusion through a principal localization. Base change of the model gives the result, first
at a stage `R[1/∏ s]` of the filtered presentation `Submonoid.localizationAwayRingCocone`
(`TauCeti.Algebra.exists_etale_finite_algEquiv_tensorProduct_localizationAwayRingCocone`) and
then at the single denominator `∏ s`.
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

/-- A finite étale algebra over a localization `M⁻¹R` descends to a stage `R[1/∏ s]` of the
filtered presentation `Submonoid.localizationAwayRingCocone`, for some finite set `s` of
denominators, along the leg of that presentation. -/
theorem exists_etale_finite_algEquiv_tensorProduct_localizationAwayRingCocone
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (B : Type*) [CommRing B] [Algebra S B] [Algebra.Etale S B] [Module.Finite S B]
    (M : Submonoid R) [IsLocalization M S] :
    ∃ s : Finset M, ∃ (Bₛ : Type u) (_ : CommRing Bₛ)
      (_ : Algebra (M.localizationAwayDiagram.obj s) Bₛ),
      Algebra.Etale (M.localizationAwayDiagram.obj s) Bₛ ∧
      Module.Finite (M.localizationAwayDiagram.obj s) Bₛ ∧
      letI : Algebra (M.localizationAwayDiagram.obj s) S :=
        ((M.localizationAwayRingCocone S).ι.app s).hom.toAlgebra
      Nonempty (B ≃ₐ[S] S ⊗[M.localizationAwayDiagram.obj s] Bₛ) := by
  refine exists_etale_finite_algEquiv_tensorProduct_of_factorization
    (fun s : Finset M ↦ M.localizationAwayDiagram.obj s)
    (fun s ↦ ((M.localizationAwayRingCocone S).ι.app s).hom) ?_ B
  intro P _ _ g
  -- Lift the initial ring to the universe of the localization diagram.
  let f := (algebraMap ℤ P).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
  have hf : f.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
      (.of_bijective ULift.ringEquiv.bijective)
  obtain ⟨s, φ, -, hφ⟩ := f.exists_factorization_localizationAwayRingCocone hf M
    ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom) g (by ext; simp [f])
  exact ⟨s, φ, hφ⟩

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
  obtain ⟨s, Bₛ, _, _, hét, hfin, he⟩ :=
    exists_etale_finite_algEquiv_tensorProduct_localizationAwayRingCocone (S := S) B M
  let t : M := ⟨∏ x ∈ s, (x : R), M.prod_mem fun x _ ↦ x.property⟩
  -- The stage at `s` is `R[1/∏ s]`, and its leg is the canonical lift, as an `R`-algebra map.
  have key : ∀ (A : CommAlgCat.{u} R), A = .of R (Localization.Away (t : R)) →
      ∀ (ℓ : A →+* S), ℓ.comp (algebraMap R A) = algebraMap R S →
      ∀ [Algebra A Bₛ], Algebra.Etale A Bₛ → Module.Finite A Bₛ →
      (letI := ℓ.toAlgebra; Nonempty (B ≃ₐ[S] S ⊗[A] Bₛ)) →
      ∃ (_ : Algebra (Localization.Away (t : R)) Bₛ),
        Algebra.Etale (Localization.Away (t : R)) Bₛ ∧
        Module.Finite (Localization.Away (t : R)) Bₛ ∧
        letI := (IsLocalization.Away.lift (S := Localization.Away (t : R)) (t : R)
          (g := algebraMap R S) (IsLocalization.map_units S t)).toAlgebra
        Nonempty (B ≃ₐ[S] S ⊗[Localization.Away (t : R)] Bₛ) := by
    rintro A rfl ℓ hℓ _ hét hfin he
    obtain rfl : ℓ = IsLocalization.Away.lift (S := Localization.Away (t : R)) (t : R)
        (g := algebraMap R S) (IsLocalization.map_units S t) :=
      IsLocalization.ringHom_ext (Submonoid.powers (t : R))
        (hℓ.trans (IsLocalization.Away.lift_comp _ _).symm)
    exact ⟨_, hét, hfin, he⟩
  exact ⟨t, Bₛ, ‹_›, key _ (M.localizationAwayDiagram_obj s) _
    (M.localizationAwayRingCocone_ι_app_comp_algebraMap S s) hét hfin he⟩

end TauCeti.Algebra
