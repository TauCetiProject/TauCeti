/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Envelope.AdicCompletion
public import TauCeti.RingTheory.Artinian.LocalRing
public import TauCeti.RingTheory.MatlisDuality.Complete

/-!
# Matlis duality over the completion of a Noetherian local ring

Let `R` be a Noetherian local ring (not assumed complete) with maximal ideal `𝔪`, residue field `κ`,
and `𝔪`-adic completion `R̂ = AdicCompletion 𝔪 R`, and let `ι : κ →ₗ[R] E` be an injective envelope
of `κ` over `R`. Because every element of `E` is annihilated by a power of `𝔪`, `E` carries the
canonical `R̂`-module structure `TauCeti.AdicCompletion.torsionModule`.

By `TauCeti.IsInjectiveEnvelope.adicCompletion` (from
`TauCeti/Algebra/Module/Injective/Envelope/AdicCompletion.lean`), `E` is an injective envelope of
the residue field of the complete Noetherian local ring `R̂`. Applying complete-ring Matlis duality
over `R̂` then establishes the finiteness/Artinian criteria and evaluation equivalences between
Artinian `R`-modules and finitely generated `R̂`-modules (Stacks Project Remark 47.7.9, Tag 0EGL),
with no finiteness hypothesis on `κ`:
* An `R̂`-module `N` is finitely generated over `R̂` if and only if `Hom_{R̂}(N, E)` is Artinian
  over `R` (`TauCeti.IsInjectiveEnvelope.finite_adicCompletion_iff_isArtinian_linearMap`),
  and evaluation gives `N ≃ₗ[R̂] ((N →ₗ[R̂] E) →ₗ[R] E)`
  (`TauCeti.IsInjectiveEnvelope.evalEquivOfFiniteOverAdicCompletion`).
* Conversely, for an Artinian `R`-module `M`, `Hom_R(M, E)` is finitely generated over `R̂` and
  evaluation gives `M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R̂] E)`
  (`TauCeti.IsInjectiveEnvelope.adicCompletionEvalEquivOfIsArtinian`).
* For a finitely generated `R`-module `N`, `AdicCompletion.torsionLiftEquiv` identifies
  `Hom_{R̂}(N̂, E)` with `Hom_R(N, E)` (`TauCeti/RingTheory/AdicCompletion/Torsion.lean`),
  identifying the double Matlis dual of `N` with its `𝔪`-adic completion:
  `N̂ ≃ₗ[R̂] ((N →ₗ[R] E) →ₗ[R] E)`
  (`TauCeti.IsInjectiveEnvelope.adicCompletionEquivDoubleDualOfFinite`).

## References

* [Stacks Project, Proposition 47.7.8](https://stacks.math.columbia.edu/tag/08Z9) and
  [Remark 47.7.9](https://stacks.math.columbia.edu/tag/0EGL).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

universe u v w

open IsLocalRing LinearMap

namespace TauCeti.IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι) [Small.{v} R]

include hι

section FiniteOverCompletion

variable (N : Type w) [AddCommGroup N] [Module (_root_.AdicCompletion (maximalIdeal R) R) N]

/-- For a finitely generated `R̂`-module `N`, the completion-linear Matlis dual `Hom_{R̂}(N, E)` is
Artinian over `R`. -/
@[stacks 0EGL]
theorem isArtinian_linearMap_of_finite_adicCompletion
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.isArtinian
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
  let e : ((Fin n → A) →ₗ[A] E) ≃ₗ[A] (Fin n → E) := LinearEquiv.piRing A E (Fin n) A
  let j : (N →ₗ[A] E) →ₗ[R] (Fin n → E) := (e.toLinearMap ∘ₗ f.lcomp A E).restrictScalars R
  exact isArtinian_of_injective j (e.injective.comp (lcomp_injective_of_surjective f hf))

/-- An `R̂`-module `N` is finitely generated over `R̂` if and only if its completion-linear Matlis
dual `Hom_{R̂}(N, E)` is Artinian over `R`. -/
theorem finite_adicCompletion_iff_isArtinian_linearMap :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N ↔
      IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  refine ⟨fun _ ↦ hι.isArtinian_linearMap_of_finite_adicCompletion N, fun hArt ↦ ?_⟩
  have : IsArtinian A (N →ₗ[A] E) := isArtinian_of_tower R hArt
  exact hι.adicCompletion.finite_iff_isArtinian_linearMap N |>.mpr ‹_›

/-- Evaluation identifies a finitely generated `R̂`-module `N` with the `R`-linear Matlis dual of
its completion-linear Matlis dual `Hom_{R̂}(N, E)`. -/
@[stacks 0EGL]
def evalEquivOfFiniteOverAdicCompletion
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.isArtinian_linearMap_of_finite_adicCompletion N
  exact hι.adicCompletion.evalEquivOfFinite N ≪≫ₗ
    AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent
      (maximalIdeal R).fg_of_isNoetherianRing
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R))

@[simp]
theorem evalEquivOfFiniteOverAdicCompletion_apply_apply
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] (x : N)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    hι.evalEquivOfFiniteOverAdicCompletion N x f = f x := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.isArtinian_linearMap_of_finite_adicCompletion N
  simp [evalEquivOfFiniteOverAdicCompletion]

@[simp]
theorem evalEquivOfFiniteOverAdicCompletion_symm_apply_apply
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
         (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    f ((hι.evalEquivOfFiniteOverAdicCompletion N).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : IsScalarTower R (_root_.AdicCompletion (maximalIdeal R) R) E :=
    AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  simpa only [evalEquivOfFiniteOverAdicCompletion_apply_apply] using
    congrArg (fun ψ : (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfFiniteOverAdicCompletion N).apply_symm_apply φ)

/-- Naturality of `evalEquivOfFiniteOverAdicCompletion` with respect to `R̂`-linear maps. -/
theorem evalEquivOfFiniteOverAdicCompletion_comp
    {N₁ : Type*} [AddCommGroup N₁] [Module (_root_.AdicCompletion (maximalIdeal R) R) N₁]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module (_root_.AdicCompletion (maximalIdeal R) R) N₂]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N₂]
    (φ : N₁ →ₗ[_root_.AdicCompletion (maximalIdeal R) R] N₂) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    (hι.evalEquivOfFiniteOverAdicCompletion N₂).toLinearMap.comp φ =
      (((φ.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E).restrictScalars R).lcomp
        (_root_.AdicCompletion (maximalIdeal R) R) E).comp
        (hι.evalEquivOfFiniteOverAdicCompletion N₁).toLinearMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  ext x g
  simp [lcomp_apply']

end FiniteOverCompletion

section ArtinianOverBase

variable (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M]

/-- Over a Noetherian local ring `R`, evaluation identifies an Artinian `R`-module `M` with the
completion-linear Matlis dual of its finite `R̂`-module dual `Hom_R(M, E)`. -/
@[stacks 0EGL]
def adicCompletionEvalEquivOfIsArtinian :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : IsScalarTower R A E := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  let := AdicCompletion.torsionModule
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M))
  have : IsScalarTower R A M := AdicCompletion.torsionModule_isScalarTower
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M))
  have : IsArtinian A M :=
    (AdicCompletion.isArtinian_torsionModule_iff _).mpr ‹_›
  let eHom : (M →ₗ[A] E) ≃ₗ[A] (M →ₗ[R] E) :=
    AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent
      (maximalIdeal R).fg_of_isNoetherianRing
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M))
  (hι.adicCompletion.evalEquivOfIsArtinian M ≪≫ₗ LinearEquiv.congrLeft E A eHom).restrictScalars R

@[simp]
theorem adicCompletionEvalEquivOfIsArtinian_apply_apply (m : M) (f : M →ₗ[R] E) :
    hι.adicCompletionEvalEquivOfIsArtinian M m f = f m := by
  simp [adicCompletionEvalEquivOfIsArtinian]

@[simp]
theorem adicCompletionEvalEquivOfIsArtinian_symm_apply_apply
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)
    (f : M →ₗ[R] E) :
    f ((hι.adicCompletionEvalEquivOfIsArtinian M).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [adicCompletionEvalEquivOfIsArtinian_apply_apply] using
    congrArg
      (fun ψ : (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E ↦ ψ f)
      ((hι.adicCompletionEvalEquivOfIsArtinian M).apply_symm_apply φ)

/-- Naturality of `adicCompletionEvalEquivOfIsArtinian` with respect to `R`-linear maps. -/
theorem adicCompletionEvalEquivOfIsArtinian_comp
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁] [IsArtinian R M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [IsArtinian R M₂]
    (φ : M₁ →ₗ[R] M₂) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    (hι.adicCompletionEvalEquivOfIsArtinian M₂).toLinearMap.comp φ =
      ((φ.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E).lcomp R E).comp
        (hι.adicCompletionEvalEquivOfIsArtinian M₁).toLinearMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext m g
  simp [lcomp_apply']

end ArtinianOverBase

section DoubleDualCompletion

variable (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- Over any Noetherian local ring `R`, the double Matlis dual `Hom_R(Hom_R(N, E), E)` of a
finitely generated `R`-module `N` is canonically `R̂`-linearly isomorphic to the `𝔪`-adic completion
`AdicCompletion (maximalIdeal R) N`. -/
@[stacks 0EGL]
def adicCompletionEquivDoubleDualOfFinite :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    _root_.AdicCompletion (maximalIdeal R) N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[R] E) →ₗ[R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : IsScalarTower R A E := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.isArtinian_linearMap_of_finite N
  exact hι.adicCompletion.evalEquivOfFinite (_root_.AdicCompletion (maximalIdeal R) N) ≪≫ₗ
    LinearEquiv.congrLeft E A (AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent).symm ≪≫ₗ
    AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent
      (maximalIdeal R).fg_of_isNoetherianRing
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := N →ₗ[R] E))

/-- Applying `adicCompletionEquivDoubleDualOfFinite` evaluates the completed lift of `f` at `z`; on
`AdicCompletion.of (maximalIdeal R) N x` this simplifies further to `f x` via
`torsionLiftEquiv_apply_of`. -/
@[simp]
theorem adicCompletionEquivDoubleDualOfFinite_apply_apply
    (z : _root_.AdicCompletion (maximalIdeal R) N) (f : N →ₗ[R] E) :
    hι.adicCompletionEquivDoubleDualOfFinite N z f =
      AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent f z := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.isArtinian_linearMap_of_finite N
  simp [adicCompletionEquivDoubleDualOfFinite]

@[simp]
theorem adicCompletionEquivDoubleDualOfFinite_symm_apply_apply
    (φ : (N →ₗ[R] E) →ₗ[R] E) (f : N →ₗ[R] E) :
    AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent f
      ((hι.adicCompletionEquivDoubleDualOfFinite N).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  simpa only [adicCompletionEquivDoubleDualOfFinite_apply_apply] using
    congrArg (fun ψ : (N →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.adicCompletionEquivDoubleDualOfFinite N).apply_symm_apply φ)

/-- Naturality of `adicCompletionEquivDoubleDualOfFinite` with respect to `R`-linear maps, using
the induced completion map `AdicCompletion.map`. -/
theorem adicCompletionEquivDoubleDualOfFinite_comp
    {N₁ : Type*} [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (φ : N₁ →ₗ[R] N₂) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    (hι.adicCompletionEquivDoubleDualOfFinite N₂).toLinearMap.comp
      (_root_.AdicCompletion.map (maximalIdeal R) φ) =
      ((φ.lcomp R E).lcomp (_root_.AdicCompletion (maximalIdeal R) R) E).comp
        (hι.adicCompletionEquivDoubleDualOfFinite N₁).toLinearMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  refine _root_.AdicCompletion.linearMap_ext_of_finite (maximalIdeal R) fun x ↦ ?_
  ext g
  simp [_root_.AdicCompletion.map_of, lcomp_apply']

end DoubleDualCompletion

end IsInjectiveEnvelope

end TauCeti
