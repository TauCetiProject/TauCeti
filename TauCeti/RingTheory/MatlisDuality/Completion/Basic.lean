/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.Complete
public import TauCeti.RingTheory.MatlisDuality.Completion.Envelope
import TauCeti.Algebra.Module.Dual.Bidual
import TauCeti.RingTheory.AdicCompletion.Small
import TauCeti.RingTheory.Artinian.LocalRing

/-!
# General Matlis duality over the completion

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪`, residue field `κ`, and
`𝔪`-adic completion `R̂`, and let `ι : κ →ₗ[R] E` be an injective envelope of `κ` with `E : Type v`
and `[Small.{v} R]`. This file establishes the general Matlis duality between Artinian `R`-modules
and finitely generated `R̂`-modules without assuming that `R` is complete or that `κ` is finite.

Over an arbitrary Noetherian local ring `R`, the canonical `R̂`-module structure on `E` makes `E`
an injective envelope of the residue field of `R̂` (`TauCeti.IsInjectiveEnvelope.adicCompletion`,
in `TauCeti/RingTheory/MatlisDuality/Completion/Envelope.lean`, under `[Small.{v} R]`). Applying
complete Matlis duality over `R̂` and the identification of `R`-linear and `R̂`-linear maps on
`𝔪`-power-torsion modules then yields the anti-equivalence between Artinian `R`-modules and finite
`R̂`-modules, and identifies the double Matlis dual `Hom_R(Hom_R(N, E), E)` of any finite
`R`-module `N` with its `𝔪`-adic completion `AdicCompletion 𝔪 N`
(`TauCeti.IsInjectiveEnvelope.adicCompletionEquivBidualOfFinite`).

The bundled categorical functors `matlisDualAdicCompletion` and `matlisDualOfAdicCompletion` live
in `TauCeti/Algebra/Category/ModuleCat/MatlisDuality/Completion.lean` and do not require
`[Small.{v} R]`, whereas their exactness (`PreservesFiniteColimits`, `PreservesHomology`) and the
restricted anti-equivalence `TauCeti.IsInjectiveEnvelope.adicCompletionMatlisDuality` require
`[Small.{v} R]`.

## Main results

Assuming `[Small.{v} R]` for `E : Type v`:

* `TauCeti.IsInjectiveEnvelope.isArtinian_adicCompletion_linearMap_of_finite`,
  `TauCeti.IsInjectiveEnvelope.isArtinian_adicCompletion_linearMap_iff_finite`,
  `TauCeti.IsInjectiveEnvelope.evalEquivAdicCompletionOfIsArtinian`, and
  `TauCeti.IsInjectiveEnvelope.evalEquivOfFiniteAdicCompletion`: Matlis duality between Artinian
  `R`-modules and finite `R̂`-modules over any Noetherian local ring.
* `TauCeti.IsInjectiveEnvelope.adicCompletionEquivBidualOfFinite`: for any finite `R`-module `N`,
  `AdicCompletion 𝔪 N ≃ₗ[R̂] Hom_R(Hom_R(N, E), E)`, intertwining `AdicCompletion.of` with
  evaluation and `AdicCompletion.map` with double precomposition.

## References

* The Stacks Project, Proposition 47.7.8 and Remark 47.7.9, Tags 08Z9 and 0EGL.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 3.2.13.
-/

public section

noncomputable section

open IsLocalRing LinearMap

namespace TauCeti

universe u v w z

namespace IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

section CompletionDuality

variable [Small.{v} R]

/-! ### General Matlis duality between Artinian `R`-modules and finite `R̂`-modules -/

/-- The Matlis dual `Hom_{R̂}(N, E)` of any finitely generated `R̂`-module is an Artinian
`R`-module. -/
theorem isArtinian_adicCompletion_linearMap_of_finite (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.adicCompletion.isArtinian_linearMap_of_finite N
  exact (AdicCompletion.isArtinian_iff_of_primaryComponent
    (maximalIdeal R).fg_of_isNoetherianRing
    ((maximalIdeal R).mem_primaryComponent_linearMap_of_finite hι.mem_primaryComponent)).mp
    inferInstance

/-- Over any Noetherian local ring `R`, the Matlis dual `Hom_{R̂}(N, E)` of an `R̂`-module `N` is
Artinian over `R` iff `N` is finitely generated over `R̂`. -/
theorem isArtinian_adicCompletion_linearMap_iff_finite (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsArtinian R (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) ↔
      Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  refine ⟨fun _ ↦ ?_, fun _ ↦ hι.isArtinian_adicCompletion_linearMap_of_finite N⟩
  have : IsArtinian (_root_.AdicCompletion (maximalIdeal R) R)
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :=
    isArtinian_of_tower R inferInstance
  exact (hι.adicCompletion.finite_iff_isArtinian_linearMap N).mpr this

/-- **General Matlis biduality for Artinian `R`-modules**: over any Noetherian local ring `R`
(assuming `[Small.{v} R]` for `E : Type v`), evaluation identifies an Artinian `R`-module `M` with
`Hom_{R̂}(Hom_R(M, E), E)`. -/
def evalEquivAdicCompletionOfIsArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  have hfg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
  letI := AdicCompletion.torsionModule
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M) hfg)
  haveI : IsArtinian (_root_.AdicCompletion (maximalIdeal R) R) M :=
    (AdicCompletion.isArtinian_iff_of_primaryComponent hfg
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M) hfg)).mpr inferInstance
  let eHom : (M →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) ≃ₗ[_root_.AdicCompletion
      (maximalIdeal R) R] (M →ₗ[R] E) :=
    AdicCompletion.restrictScalarsEquivOfPrimaryComponent hfg
      (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M) hfg)
  exact ((hι.adicCompletion.evalEquivOfIsArtinian M).trans
    (eHom.arrowCongr (LinearEquiv.refl _ E))).restrictScalars R

@[simp]
theorem evalEquivAdicCompletionOfIsArtinian_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivAdicCompletionOfIsArtinian M m f = f m := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  let := AdicCompletion.torsionModule
    (mem_primaryComponent_maximalIdeal_of_isArtinian (R := R) (M := M)
      (maximalIdeal R).fg_of_isNoetherianRing)
  simp [evalEquivAdicCompletionOfIsArtinian]

@[simp]
theorem evalEquivAdicCompletionOfIsArtinian_symm_apply_apply (M : Type w) [AddCommGroup M]
    [Module R M] [IsArtinian R M]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivAdicCompletionOfIsArtinian M).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [evalEquivAdicCompletionOfIsArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E ↦ ψ f)
      ((hι.evalEquivAdicCompletionOfIsArtinian M).apply_symm_apply φ)

/-- **General Matlis biduality for finite `R̂`-modules**: over any Noetherian local ring `R`
(assuming `[Small.{v} R]` for `E : Type v`), evaluation identifies a finitely generated `R̂`-module
`N` with `Hom_R(Hom_{R̂}(N, E), E)`. -/
def evalEquivOfFiniteAdicCompletion (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact (hι.adicCompletion.evalEquivOfFinite N).trans
    (AdicCompletion.restrictScalarsEquivOfPrimaryComponent
      (maximalIdeal R).fg_of_isNoetherianRing
      ((maximalIdeal R).mem_primaryComponent_linearMap_of_finite hι.mem_primaryComponent))

@[simp]
theorem evalEquivOfFiniteAdicCompletion_apply_apply (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] (x : N)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    hι.evalEquivOfFiniteAdicCompletion N x f = f x := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simp [evalEquivOfFiniteAdicCompletion]

@[simp]
theorem evalEquivOfFiniteAdicCompletion_symm_apply_apply (N : Type w) [AddCommGroup N]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N]
    (φ : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E)
    (f : letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) :
    f ((hι.evalEquivOfFiniteAdicCompletion N).symm φ) = φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [evalEquivOfFiniteAdicCompletion_apply_apply] using
    congrArg (fun ψ : (N →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfFiniteAdicCompletion N).apply_symm_apply φ)

/-- Over any Noetherian local ring, `Hom_R(-, E)` is bijective on morphisms into an Artinian
`R`-module, valued in `R̂`-linear maps between Matlis duals. -/
theorem bijective_lcomp_adicCompletion_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type z) [AddCommGroup N] [Module R N] [IsArtinian R N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Function.Bijective (fun f : M →ₗ[R] N ↦
      f.lcomp (_root_.AdicCompletion (maximalIdeal R) R) E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact bijective_lcomp_of_evalEquiv (_root_.AdicCompletion (maximalIdeal R) R)
    (hι.evalEquivAdicCompletionOfIsArtinian N)
    (hι.evalEquivAdicCompletionOfIsArtinian_apply_apply N)

/-- Over any Noetherian local ring, `Hom_{R̂}(-, E)` is bijective on morphisms into a finite
`R̂`-module, valued in `R`-linear maps between Matlis duals. -/
theorem bijective_lcomp_of_finite_adicCompletion (M : Type w) [AddCommGroup M]
    [Module (_root_.AdicCompletion (maximalIdeal R) R) M]
    (N : Type z) [AddCommGroup N] [Module (_root_.AdicCompletion (maximalIdeal R) R) N]
    [Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Function.Bijective (fun f : M →ₗ[_root_.AdicCompletion (maximalIdeal R) R] N ↦
      f.lcomp R E) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  exact bijective_lcomp_of_evalEquiv R
    (hι.evalEquivOfFiniteAdicCompletion N) (hι.evalEquivOfFiniteAdicCompletion_apply_apply N)

/-! ### Double Matlis dual of a finite module as its completion -/

/-- **The double Matlis dual of a finite module is its `𝔪`-adic completion.** For any finitely
generated module `N` over a Noetherian local ring `R` (assuming `[Small.{v} R]` for `E : Type v`),
there is a canonical `R̂`-linear isomorphism `AdicCompletion 𝔪 N ≃ₗ[R̂] Hom_R(Hom_R(N, E), E)`
intertwining `AdicCompletion.of` with evaluation (`adicCompletionEquivBidualOfFinite_of`). -/
def adicCompletionEquivBidualOfFinite (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    _root_.AdicCompletion (maximalIdeal R) N ≃ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      ((N →ₗ[R] E) →ₗ[R] E) := by
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  let eLift := (AdicCompletion.torsionLiftEquiv (I := maximalIdeal R) (N := N)
    hι.mem_primaryComponent).restrictScalars R
  exact (hι.evalEquivOfFiniteAdicCompletion (_root_.AdicCompletion (maximalIdeal R) N)).trans
    (eLift.symm.congrLeft E (_root_.AdicCompletion (maximalIdeal R) R))

/-- Evaluation of `adicCompletionEquivBidualOfFinite` applies the canonical lift of `f` to the
completed element. -/
@[simp]
theorem adicCompletionEquivBidualOfFinite_apply_apply (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] (y : _root_.AdicCompletion (maximalIdeal R) N) (f : N →ₗ[R] E) :
    hι.adicCompletionEquivBidualOfFinite N y f =
      AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent f y := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simp [adicCompletionEquivBidualOfFinite]

/-- On the image of `N` in `AdicCompletion 𝔪 N`, `adicCompletionEquivBidualOfFinite` agrees with
the Matlis evaluation map `LinearMap.applyₗ`. -/
@[simp]
theorem adicCompletionEquivBidualOfFinite_of (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] (x : N) :
    hι.adicCompletionEquivBidualOfFinite N (_root_.AdicCompletion.of (maximalIdeal R) N x) =
      applyₗ x := by
  ext f
  simp

/-- The inverse of `adicCompletionEquivBidualOfFinite` sends the evaluation functional `applyₗ x`
to `AdicCompletion.of 𝔪 N x`. -/
@[simp]
theorem adicCompletionEquivBidualOfFinite_symm_applyₗ (N : Type w) [AddCommGroup N] [Module R N]
    [Module.Finite R N] (x : N) :
    (hι.adicCompletionEquivBidualOfFinite N).symm (applyₗ x) =
      _root_.AdicCompletion.of (maximalIdeal R) N x := by
  rw [LinearEquiv.symm_apply_eq, hι.adicCompletionEquivBidualOfFinite_of]

@[simp]
theorem adicCompletionEquivBidualOfFinite_symm_apply_apply (N : Type w) [AddCommGroup N]
    [Module R N] [Module.Finite R N] (φ : (N →ₗ[R] E) →ₗ[R] E) (f : N →ₗ[R] E) :
    AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent f
        ((hι.adicCompletionEquivBidualOfFinite N).symm φ) =
      φ f := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simpa only [adicCompletionEquivBidualOfFinite_apply_apply] using
    congrArg (fun ψ : (N →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.adicCompletionEquivBidualOfFinite N).apply_symm_apply φ)

/-- `adicCompletionEquivBidualOfFinite` intertwines `AdicCompletion.map` with double
precomposition. -/
@[simp]
theorem adicCompletionEquivBidualOfFinite_map {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {N : Type z} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (y : _root_.AdicCompletion (maximalIdeal R) M) :
    hι.adicCompletionEquivBidualOfFinite N (_root_.AdicCompletion.map (maximalIdeal R) f y) =
      (f.lcomp R E).lcomp R E (hι.adicCompletionEquivBidualOfFinite M y) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext g
  simp only [adicCompletionEquivBidualOfFinite_apply_apply, LinearMap.lcomp_apply]
  let lhs : _root_.AdicCompletion (maximalIdeal R) M →ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      E :=
    (AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent g).comp
      (_root_.AdicCompletion.map (maximalIdeal R) f)
  let rhs : _root_.AdicCompletion (maximalIdeal R) M →ₗ[_root_.AdicCompletion (maximalIdeal R) R]
      E :=
    AdicCompletion.torsionLiftEquiv hι.mem_primaryComponent (g.comp f)
  exact LinearMap.congr_fun
    (AdicCompletion.linearMap_ext_of_finite (maximalIdeal R) (g₁ := lhs) (g₂ := rhs) fun x ↦ by
      simp [lhs, rhs, _root_.AdicCompletion.map_of]) y

end CompletionDuality

end IsInjectiveEnvelope

end TauCeti
