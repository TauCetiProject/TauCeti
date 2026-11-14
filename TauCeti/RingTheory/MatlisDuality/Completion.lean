/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Hom
public import TauCeti.RingTheory.AdicCompletion.Injective
public import TauCeti.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.MatlisDuality.Finite

/-!
# Matlis duality over the completion of a Noetherian local ring

Let `R` be a Noetherian local ring (not assumed complete) with maximal ideal `𝔪`, residue field `κ`,
and `𝔪`-adic completion `R̂ = AdicCompletion 𝔪 R`, and let `ι : κ →ₗ[R] E` be an injective envelope
of `κ` over `R`. Because every element of `E` is annihilated by a power of `𝔪`, `E` carries the
canonical `R̂`-module structure `TauCeti.AdicCompletion.torsionModule`.

By `TauCeti.AdicCompletion.torsionModule_injective`, `E` is injective over `R̂`. Composing `ι` with
the canonical identification `ResidueField R̂ ≃ₐ[R] κ`
(`TauCeti.AdicCompletion.residueFieldAlgEquiv`) exhibits `E` as an injective envelope of the
residue field of the complete Noetherian local ring `R̂`
(`TauCeti.IsInjectiveEnvelope.adicCompletion`, Stacks Project Tag 08Z8).

Applying complete-ring Matlis duality over `R̂` then establishes the exact duality and evaluation
biduality between Artinian `R`-modules and finitely generated `R̂`-modules (Stacks Project Remark
47.7.9, Tag 0EGL), with no finiteness hypothesis on `κ`:
* Both contravariant functors `Hom_R(-, E)` and `Hom_{R̂}(-, E)` are exact.
* An `R̂`-module `N` is finitely generated over `R̂` if and only if `Hom_{R̂}(N, E)` is Artinian
  over `R`, and evaluation gives `N ≃ₗ[R̂] ((N →ₗ[R̂] E) →ₗ[R] E)`
  (`TauCeti.IsInjectiveEnvelope.evalEquivAdicCompletionOfFinite`).
* Conversely, for an Artinian `R`-module `M`, `Hom_R(M, E)` is finitely generated over `R̂` and
  evaluation gives `M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R̂] E)`
  (`TauCeti.IsInjectiveEnvelope.adicCompletionEvalEquivOfArtinian`).
* For a finitely generated `R`-module `N`, `Hom_{R̂}(N̂, E) ≃ₗ[R̂] Hom_R(N, E)` and
  `Hom_{R̂}(R̂ ⊗[R] N, E) ≃ₗ[R̂] Hom_R(N, E)`, identifying the double Matlis dual of `N` with its
  `𝔪`-adic completion: `N̂ ≃ₗ[R̂] ((N →ₗ[R] E) →ₗ[R] E)`
  (`TauCeti.IsInjectiveEnvelope.adicCompletionEquivDoubleDualOfFinite`).

## References

* [Stacks Project, Lemma 47.7.7](https://stacks.math.columbia.edu/tag/08Z8),
  [Proposition 47.7.8](https://stacks.math.columbia.edu/tag/08Z9), and
  [Remark 47.7.9](https://stacks.math.columbia.edu/tag/0EGL).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

universe u v w z

open IsLocalRing LinearMap TensorProduct

namespace TauCeti.IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

/-- An injective envelope `ι : ResidueField R →ₗ[R] E` lifted across
`ResidueField R̂ ≃ₐ[R] ResidueField R` to an `R̂`-linear embedding of `ResidueField R̂` into `E`. -/
def adicCompletionResidueMap :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    ResidueField (_root_.AdicCompletion (maximalIdeal R) R)
      →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have hres : ∀ y : ResidueField (_root_.AdicCompletion (maximalIdeal R) R),
      y ∈ (maximalIdeal R).primaryComponent _ := fun y ↦ by
    refine ((maximalIdeal R).primaryComponent_mem _ y).mpr ⟨1, ?_⟩
    rw [pow_one, Submodule.mem_torsionBySet_iff]
    rintro ⟨m, hm⟩
    have hm' : algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) m ∈
        maximalIdeal (_root_.AdicCompletion (maximalIdeal R) R) := by
      rw [_root_.AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ hm
    rw [← algebraMap_smul (_root_.AdicCompletion (maximalIdeal R) R), Algebra.smul_def,
      ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr hm', zero_mul]
  exact (AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent
    (maximalIdeal R).fg_of_isNoetherianRing hres).symm
      (ι ∘ₗ (AdicCompletion.residueFieldAlgEquiv R).symm.toLinearMap)

@[simp]
theorem adicCompletionResidueMap_apply
    (y : ResidueField (_root_.AdicCompletion (maximalIdeal R) R)) :
    hι.adicCompletionResidueMap y = ι ((AdicCompletion.residueFieldAlgEquiv R).symm y) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  simp [adicCompletionResidueMap]

section CompletionHomAdjunction

variable (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N]

include hι

/-- For a finitely generated `R`-module `N` over a Noetherian local ring `R`, restriction along
`AdicCompletion.of` gives an `R̂`-linear isomorphism `Hom_{R̂}(N̂, E) ≃ₗ[R̂] Hom_R(N, E)`. -/
def adicCompletionLinearMapEquiv :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    (_root_.AdicCompletion (maximalIdeal R) N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)
      ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R] (N →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact (AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent).symm

@[simp]
theorem adicCompletionLinearMapEquiv_apply
    (g : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         _root_.AdicCompletion (maximalIdeal R) N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)
    (x : N) :
    hι.adicCompletionLinearMapEquiv N g x = g (_root_.AdicCompletion.of (maximalIdeal R) N x) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact AdicCompletion.torsionLiftEquiv_symm_apply hι.mem_primaryComponent g x

@[simp]
theorem adicCompletionLinearMapEquiv_symm_apply_of (f : N →ₗ[R] E) (x : N) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    (hι.adicCompletionLinearMapEquiv N).symm f (_root_.AdicCompletion.of (maximalIdeal R) N x) =
      f x :=
  AdicCompletion.torsionLiftEquiv_apply_of hι.mem_primaryComponent f x

/-- For a finitely generated `R`-module `N` over a Noetherian local ring `R`, the tensor-Hom
comparison `Hom_{R̂}(R̂ ⊗[R] N, E) ≃ₗ[R̂] Hom_R(N, E)` built via
`TauCeti.AdicCompletion.ofTensorProductEquiv`. -/
def tensorAdicCompletionLinearMapEquiv :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    (_root_.AdicCompletion (maximalIdeal R) R ⊗[R] N
        →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)
      ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R] (N →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact (AdicCompletion.torsionTensorLiftEquiv hι.mem_primaryComponent).symm

@[simp]
theorem tensorAdicCompletionLinearMapEquiv_apply
    (g : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         _root_.AdicCompletion (maximalIdeal R) R ⊗[R] N
           →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)
    (x : N) :
    hι.tensorAdicCompletionLinearMapEquiv N g x = g (1 ⊗ₜ x) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact AdicCompletion.torsionTensorLiftEquiv_symm_apply hι.mem_primaryComponent g x

@[simp]
theorem tensorAdicCompletionLinearMapEquiv_symm_apply_tmul (f : N →ₗ[R] E)
    (a : _root_.AdicCompletion (maximalIdeal R) R) (x : N) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    (hι.tensorAdicCompletionLinearMapEquiv N).symm f (a ⊗ₜ x) = a • f x :=
  AdicCompletion.torsionTensorLiftEquiv_apply_tmul hι.mem_primaryComponent f a x

end CompletionHomAdjunction

variable [Small.{v} R]

include hι

/-- Over a Noetherian local ring `R`, an injective envelope `E` of `ResidueField R` is also an
injective envelope of `ResidueField R̂` over `R̂ = AdicCompletion (maximalIdeal R) R`. -/
@[stacks 08Z8]
theorem adicCompletion :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsInjectiveEnvelope hι.adicCompletionResidueMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.moduleInjective
  refine ⟨AdicCompletion.torsionModule_injective hι.mem_primaryComponent, ?_, ?_⟩
  · intro y₁ y₂ hy
    rw [adicCompletionResidueMap_apply, adicCompletionResidueMap_apply] at hy
    exact (AdicCompletion.residueFieldAlgEquiv R).symm.injective (hι.injective hy)
  · rw [← AdicCompletion.isEssential_restrictScalars_torsionModule_iff hι.mem_primaryComponent]
    have hrange : (range hι.adicCompletionResidueMap).restrictScalars R = range ι := by
      ext x
      simp only [Submodule.restrictScalars_mem, mem_range, adicCompletionResidueMap_apply]
      exact ⟨fun ⟨y, hy⟩ ↦ ⟨(AdicCompletion.residueFieldAlgEquiv R).symm y, hy⟩,
        fun ⟨z, hz⟩ ↦ ⟨AdicCompletion.residueFieldAlgEquiv R z, by simpa using hz⟩⟩
    rw [hrange]
    exact hι.isEssential_range

section Exactness

/-- The Matlis dual `Hom_R(-, E)` valued in `R̂`-modules is exact on every exact pair of
`R`-modules. -/
theorem exact_lcomp_adicCompletion {P Q M : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [AddCommGroup M] [Module R M]
    {f : P →ₗ[R] Q} {g : Q →ₗ[R] M} (hfg : Function.Exact f g) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Function.Exact (g.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E)
      (f.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.moduleInjective
  exact hfg.lcomp_of_moduleInjective (_root_.AdicCompletion (maximalIdeal R) R) E

/-- The completion-linear Matlis dual `Hom_{R̂}(-, E)` is exact on every exact pair of
`R̂`-modules. -/
theorem exact_adicCompletion_lcomp {P Q M : Type*} [AddCommGroup P]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) P]
    [AddCommGroup Q] [Module (_root_.AdicCompletion (maximalIdeal R) R) Q]
    [AddCommGroup M] [Module (_root_.AdicCompletion (maximalIdeal R) R) M]
    {f : P →ₗ[_root_.AdicCompletion (maximalIdeal R) R] Q}
    {g : Q →ₗ[_root_.AdicCompletion (maximalIdeal R) R] M}
    (hfg : Function.Exact f g) :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Function.Exact (g.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E)
      (f.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.adicCompletion.moduleInjective
  exact hfg.lcomp_of_moduleInjective (_root_.AdicCompletion (maximalIdeal R) R) E

end Exactness

section FiniteOverCompletion

variable (N : Type w) [AddCommGroup N] [Module (_root_.AdicCompletion (maximalIdeal R) R) N]

/-- For a finitely generated `R̂`-module `N`, the completion-linear Matlis dual `Hom_{R̂}(N, E)` is
Artinian over `R̂`. -/
theorem isArtinian_adicCompletion_linearMap_of_finite
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsArtinian (_root_.AdicCompletion (maximalIdeal R) R)
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact hι.adicCompletion.isArtinian_linearMap_of_finite N

/-- For a finitely generated `R̂`-module `N`, the completion-linear Matlis dual `Hom_{R̂}(N, E)` is
Artinian over `R`. -/
@[stacks 0EGL]
theorem isArtinian_linearMap_adicCompletion_of_finite
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
  refine ⟨fun _ ↦ hι.isArtinian_linearMap_adicCompletion_of_finite N, fun hArt ↦ ?_⟩
  have : IsArtinian A (N →ₗ[A] E) := isArtinian_of_tower R hArt
  exact hι.adicCompletion.finite_iff_isArtinian_linearMap N |>.mpr ‹_›

/-- Evaluation identifies a finitely generated `R̂`-module `N` with the `R`-linear Matlis dual of
its completion-linear Matlis dual `Hom_{R̂}(N, E)`. -/
@[stacks 0EGL]
def evalEquivAdicCompletionOfFinite
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
    N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.isArtinian_linearMap_adicCompletion_of_finite N
  exact hι.adicCompletion.evalEquivOfFinite N ≪≫ₗ
    AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent
      (maximalIdeal R).fg_of_isNoetherianRing
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R))

@[simp]
theorem evalEquivAdicCompletionOfFinite_apply_apply
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] (x : N)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    hι.evalEquivAdicCompletionOfFinite N x f = f x := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.isArtinian_linearMap_adicCompletion_of_finite N
  simp [evalEquivAdicCompletionOfFinite]

@[simp]
theorem evalEquivAdicCompletionOfFinite_symm_apply_apply
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
         (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    f ((hι.evalEquivAdicCompletionOfFinite N).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : IsScalarTower R (_root_.AdicCompletion (maximalIdeal R) R) E :=
    AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  simpa only [evalEquivAdicCompletionOfFinite_apply_apply] using
    congrArg (fun ψ : (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivAdicCompletionOfFinite N).apply_symm_apply φ)

end FiniteOverCompletion

section ArtinianOverBase

variable (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M]

/-- Over a Noetherian local ring `R`, evaluation identifies an Artinian `R`-module `M` with the
completion-linear Matlis dual of its finite `R̂`-module dual `Hom_R(M, E)`. -/
@[stacks 0EGL]
def adicCompletionEvalEquivOfArtinian :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : IsScalarTower R A E := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  let := AdicCompletion.torsionModule (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R)
    (M := M))
  have : IsScalarTower R A M := AdicCompletion.torsionModule_isScalarTower
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M))
  have : IsArtinian A M :=
    (AdicCompletion.isArtinian_torsionModule_iff _).mpr ‹_›
  let eHom : (M →ₗ[A] E) ≃ₗ[A] (M →ₗ[R] E) :=
    AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent
      (maximalIdeal R).fg_of_isNoetherianRing
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M))
  exact (hι.adicCompletion.evalEquivOfArtinian M ≪≫ₗ
    LinearEquiv.congrLeft E A eHom).restrictScalars R

@[simp]
theorem adicCompletionEvalEquivOfArtinian_apply_apply (m : M) (f : M →ₗ[R] E) :
    hι.adicCompletionEvalEquivOfArtinian M m f = f m := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have : IsScalarTower R A E := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  let := AdicCompletion.torsionModule (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R)
    (M := M))
  have : IsScalarTower R A M := AdicCompletion.torsionModule_isScalarTower
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M))
  have : IsArtinian A M :=
    (AdicCompletion.isArtinian_torsionModule_iff _).mpr ‹_›
  simp [adicCompletionEvalEquivOfArtinian]

@[simp]
theorem adicCompletionEvalEquivOfArtinian_symm_apply_apply
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
         (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E)
    (f : M →ₗ[R] E) :
    f ((hι.adicCompletionEvalEquivOfArtinian M).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [adicCompletionEvalEquivOfArtinian_apply_apply] using
    congrArg
      (fun ψ : (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E ↦ ψ f)
      ((hι.adicCompletionEvalEquivOfArtinian M).apply_symm_apply φ)

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
  let eA : (_root_.AdicCompletion (maximalIdeal R) N →ₗ[A] E) ≃ₗ[A] (N →ₗ[R] E) :=
    hι.adicCompletionLinearMapEquiv N
  exact hι.adicCompletion.evalEquivOfFinite (_root_.AdicCompletion (maximalIdeal R) N) ≪≫ₗ
    LinearEquiv.congrLeft E A eA ≪≫ₗ
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
  simp [adicCompletionEquivDoubleDualOfFinite, adicCompletionLinearMapEquiv]

end DoubleDualCompletion

section Complete

variable [IsAdicComplete (maximalIdeal R) R]

/-- Over a complete Noetherian local ring, evaluation into the double Matlis dual is bijective on
any product `M × P` of a finitely generated module `M` and an Artinian module `P` (such as
`R × E`, which is neither finite nor Artinian when `dim R ≥ 1`). -/
theorem bijective_applyₗ_prod_of_finite_of_artinian
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (P : Type z) [AddCommGroup P] [Module R P] [IsArtinian R P] :
    Function.Bijective (applyₗ : (M × P) →ₗ[R] ((M × P) →ₗ[R] E) →ₗ[R] E) :=
  bijective_applyₗ_prod_iff.mpr ⟨hι.bijective_applyₗ_of_finite M, hι.bijective_applyₗ_of_artinian P⟩

end Complete

end IsInjectiveEnvelope

end TauCeti
