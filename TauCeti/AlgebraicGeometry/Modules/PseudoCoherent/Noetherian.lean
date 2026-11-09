/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.PseudoCoherent.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType

/-!
# Pseudo-coherent sheaves on locally Noetherian schemes

On a locally Noetherian scheme, a quasi-coherent module of finite type is pseudo-coherent.
Together with finite presentation of pseudo-coherent sheaves, this identifies pseudo-coherence
with finite presentation, or, for quasi-coherent sheaves, with finite type. Thus coherent
modules can be used with the local finite free resolutions defining pseudo-coherence.

On an affine Noetherian scheme there is a global resolution by finite free sheaves. The
resolution is not required to terminate: neither regularity nor finite projective dimension
is assumed.

## References

* The Stacks Project, Lemma 15.66.17 (Tag 066E), pseudo-coherence over a Noetherian ring.
* The Stacks Project, Section 36.10 (Tag 08E4), pseudo-coherent complexes on schemes.

The construction uses `TauCeti.Huber.IsPseudoCoherentOver.of_isNoetherianRing` and
`AlgebraicGeometry.Scheme.Modules.hasFiniteFreeResolution_tilde` to sheafify the algebraic
resolution.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A quasi-coherent module of finite type on an affine Noetherian scheme has a global
resolution by finite free sheaves, possibly unbounded to the left. -/
theorem hasFiniteFreeResolution_of_isAffine [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : F.HasFiniteFreeResolution := by
  let N := F.restrict X.isoSpec.inv
  have : N.IsQuasicoherent := inferInstance
  have : N.IsFiniteType := inferInstance
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X, ⊤) (moduleSpecΓFunctor.obj N) := N.finite_moduleSpecΓ
  have hN : N.HasFiniteFreeResolution :=
    (hasFiniteFreeResolution_tilde
      (M := moduleSpecΓFunctor.obj N)
      TauCeti.Huber.IsPseudoCoherentOver.of_isNoetherianRing).of_iso
        (asIso N.fromTildeΓ)
  exact (hN.restrict X.isoSpec.hom).of_iso
    (((restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).app F).symm ≪≫
      (restrictFunctorCongr X.isoSpec.hom_inv_id).app F ≪≫ restrictFunctorId.app F)

/-- On a locally Noetherian scheme, every quasi-coherent module of finite type is
pseudo-coherent. No quasi-compactness or separatedness hypothesis is needed. -/
theorem isPseudoCoherent_of_isLocallyNoetherian (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : F.IsPseudoCoherent := by
  apply isPseudoCoherent_iff.mpr
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : IsAffine U.toScheme := hU
  exact ⟨U, hxU, hasFiniteFreeResolution_of_isAffine (F.restrict U.ι)⟩

/-- On a locally Noetherian scheme, pseudo-coherence is equivalent to finite presentation
as a sheaf of modules; quasi-coherence is part of the conclusion, not an extra hypothesis. -/
@[simp]
theorem isPseudoCoherent_iff_isFinitePresentation (F : X.Modules) :
    F.IsPseudoCoherent ↔ F.IsFinitePresentation := by
  refine ⟨fun h ↦ h.isFinitePresentation, fun h ↦ ?_⟩
  have := h
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  exact isPseudoCoherent_of_isLocallyNoetherian F

/-- A quasi-coherent module on a locally Noetherian scheme is pseudo-coherent exactly when
it is of finite type. The quasi-coherence hypothesis is essential. -/
theorem isPseudoCoherent_iff_isFiniteType (F : X.Modules) [F.IsQuasicoherent] :
    F.IsPseudoCoherent ↔ F.IsFiniteType := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h.isFinitePresentation
    exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  · have := h
    exact isPseudoCoherent_of_isLocallyNoetherian F

end

end AlgebraicGeometry.Scheme.Modules
