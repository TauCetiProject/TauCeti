/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.FinitePresentation
public import TauCeti.Algebra.Module.AuslanderReiten.ProjectiveSummand
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra
import TauCeti.RingTheory.Artinian.FiniteLength

/-!
# The Auslander-Reiten translate through Matlis duality

Let `A` be an algebra over a commutative ring `R` and `E` an `R`-module, with
`D_R = Hom_R(-, E)`. For a projective presentation `p₁ : P₁ → P₀` of a left `A`-module `M`, the
Auslander-Reiten translate is the left `A`-module `τ M = D_R (Tr p₁)`, the Matlis dual of the
transpose `TauCeti.AuslanderReitenTranspose p₁`. This file transports the properties of the
transpose through `D_R`:

* for minimal presentations, `D_R (Tr p₁)` does not depend on the presentation, for any `R` and `E`;

and, for an Artin `R`-algebra `A` with `E` an injective hull of `R ⧸ J(R)`:

* `D_R (Tr p₁)` is finitely generated;
* it vanishes exactly when `M` is projective;
* it has no nonzero injective retract when the kernel of `p₁` is superfluous, for instance for a
  minimal presentation: the dual of an injective retract is a projective retract of `Tr p₁`
  (`TauCeti.IsInjectiveEnvelope.exists_retract_matlisDual_of_retract`), and `Tr p₁` has none.

The last property makes `D_R (Tr p₁)` the representative without injective summands of its class
modulo injectives.

## Main results

* `TauCeti.IsMinimalProjectivePresentation.nonempty_linearEquiv_matlisDual_auslanderReitenTranspose`
* `TauCeti.IsInjectiveEnvelope.finite_matlisDual_auslanderReitenTranspose`
* `TauCeti.IsMinimalProjectivePresentation.subsingleton_matlisDual_auslanderReitenTranspose_iff`
* `TauCeti.IsSuperfluous.subsingleton_of_retract_matlisDual_auslanderReitenTranspose`

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.1.
-/

public section

namespace TauCeti

universe u v w t

open MatlisDual

section Independence

variable {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E] {A : Type*} [Ring A]
  [Algebra R A] {M : Type*} [AddCommGroup M] [Module A M]
  {P₀ P₁ Q₀ Q₁ : Type*} [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M} {q₁ : Q₁ →ₗ[A] Q₀} {q₀ : Q₀ →ₗ[A] M}

/-- **The translate does not depend on the minimal presentation**: for two minimal presentations
of `M`, the Matlis duals of their transposes are isomorphic left `A`-modules. -/
theorem IsMinimalProjectivePresentation.nonempty_linearEquiv_matlisDual_auslanderReitenTranspose
    (h : IsMinimalProjectivePresentation p₁ p₀) (h' : IsMinimalProjectivePresentation q₁ q₀) :
    Nonempty (MatlisDual R E (AuslanderReitenTranspose p₁) ≃ₗ[A]
      MatlisDual R E (AuslanderReitenTranspose q₁)) :=
  (h.nonempty_linearEquiv_auslanderReitenTranspose h').map fun e ↦ congrOp e.symm

end Independence

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type t} [Ring A] [Algebra R A]
  [Module.Finite R A]

section Finite

variable {P₀ P₁ : Type*} [AddCommMonoid P₀] [Module A P₀] [AddCommMonoid P₁] [Module A P₁]
  [Module.Finite A P₁] [Module.Projective A P₁]

/-- The translate of a presentation with finite projective source is finitely generated. -/
theorem IsInjectiveEnvelope.finite_matlisDual_auslanderReitenTranspose (hf : IsInjectiveEnvelope f)
    (p₁ : P₁ →ₗ[A] P₀) : Module.Finite A (MatlisDual R E (AuslanderReitenTranspose p₁)) :=
  hf.finite_matlisDual_of_finite_op

end Finite

section Vanishing

variable {M : Type*} [AddCommGroup M] [Module A M] {P₀ P₁ : Type*} [AddCommGroup P₀]
  [Module A P₀] [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁]
  {p₁ : P₁ →ₗ[A] P₀} {p₀ : P₀ →ₗ[A] M}

/-- **The translate vanishes exactly on the projective modules**: for a minimal presentation of
`M` with finite source, `D_R (Tr p₁)` is zero exactly when `M` is projective. -/
theorem IsMinimalProjectivePresentation.subsingleton_matlisDual_auslanderReitenTranspose_iff
    (hf : IsInjectiveEnvelope f) (h : IsMinimalProjectivePresentation p₁ p₀) :
    Subsingleton (MatlisDual R E (AuslanderReitenTranspose p₁)) ↔ Module.Projective A M := by
  have : Module.Projective A P₁ := h.projective
  rw [hf.subsingleton_matlisDual_iff (isFiniteLength_of_finite_trans R Aᵐᵒᵖ _),
    h.subsingleton_auslanderReitenTranspose_iff_projective]

end Vanishing

section InjectiveRetract

variable {P₀ P₁ : Type*} [AddCommMonoid P₀] [Module A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]
  {p₁ : P₁ →ₗ[A] P₀}

/-- **The translate has no injective summand**: if the kernel of `p₁` is superfluous, as for a
minimal presentation, every injective retract of `D_R (Tr p₁)` is zero. Its dual would be a
projective retract of `Tr p₁`. -/
theorem IsSuperfluous.subsingleton_of_retract_matlisDual_auslanderReitenTranspose
    (h : IsSuperfluous (LinearMap.ker p₁)) (hf : IsInjectiveEnvelope f) {I : Type w}
    [AddCommGroup I] [Module R I] [Module A I] [IsScalarTower R A I] [Module.Injective A I]
    [Small.{w} A] (r : MatlisDual R E (AuslanderReitenTranspose p₁) →ₗ[A] I)
    (s : I →ₗ[A] MatlisDual R E (AuslanderReitenTranspose p₁)) (hrs : r ∘ₗ s = LinearMap.id) :
    Subsingleton I := by
  have : Module.Finite A (MatlisDual R E (AuslanderReitenTranspose p₁)) :=
    hf.finite_matlisDual_auslanderReitenTranspose p₁
  have : Module.Finite A I := Module.Finite.of_surjective r fun x ↦ ⟨s x, by
    simpa using LinearMap.congr_fun hrs x⟩
  obtain ⟨r', s', hrs'⟩ := hf.exists_retract_matlisDual_of_retract
    (isFiniteLength_of_finite_trans R Aᵐᵒᵖ _) r s hrs
  have : Module.Projective Aᵐᵒᵖ (MatlisDual R E I) := hf.moduleProjective_op_matlisDual_of_injective
  have := h.subsingleton_of_retract_auslanderReitenTranspose r' s' hrs'
  exact (hf.subsingleton_matlisDual_iff (isFiniteLength_of_finite_trans R A I)).1 this

end InjectiveRetract

end TauCeti
