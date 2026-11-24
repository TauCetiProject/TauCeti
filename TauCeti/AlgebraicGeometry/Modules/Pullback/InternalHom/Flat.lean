/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Flat
import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Coherence
import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Restriction
import TauCeti.CategoryTheory.Monoidal.Closed.Presentation
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.InternalHom.Quasicoherent

/-!
# Flat pullback of internal Hom

The canonical internal-Hom comparison is invertible along a flat scheme morphism when its
source sheaf is finitely presented; the target sheaf is arbitrary. Both schemes are arbitrary; no
local freeness or Noetherian hypothesis is required.

A finite presentation expresses internal Hom as a kernel between internal Homs from finite free
sheaves. Flat pullback preserves this kernel, since it is exact, and the finite free comparisons are
invertible by duality. Source naturality identifies the induced kernel isomorphism with the
canonical comparison, rather than defining another base-change map.

The affine-base calculation globalizes by restricting to the preimages of affine opens.
Restriction commutes with internal Hom, and composition coherence identifies the local
comparisons with the restrictions of the canonical comparison.

The kernel comparison uses
`CategoryTheory.Functor.ihomComparison_isIso_of_cokernel_of_naturality`.
The canonical internal-Hom comparison uses the oplax tensor comparison of module pullback.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_presentation`:
  invertibility from a finite global presentation, without an affineness hypothesis;
* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_isAffine`:
  invertibility for finitely presented sources over an affine base;
* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app`:
  invertibility for finitely presented sources on arbitrary schemes.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory Limits MonoidalClosed

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]

/-- A finite global presentation of the source makes the canonical internal-Hom comparison
invertible under flat pullback, for every target, without assuming the base affine. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_presentation
    (M N : Y.Modules)
    (P : M.Presentation) [P.IsFinite] :
    IsIso ((pullbackIhomComparison M f).app N) := by
  let F := Scheme.Modules.pullback f
  let A : Y.Modules := SheafOfModules.free P.relations.I
  let B : Y.Modules := SheafOfModules.free P.generators.I
  let a : A ⟶ B := P.relations.π ≫ kernel.ι P.generators.π
  let b : B ⟶ M := P.generators.π
  have w : a ≫ b = 0 := by
    -- `Y.Modules` is the category `SheafOfModules Y.ringCatSheaf`, and
    -- `(freeHomEquiv _).symm P.relations.s` is definitionally `P.relations.π`.
    -- Thus `P.isColimit` is exactly the cokernel presentation of `a, b` above.
    exact (fun {c : CokernelCofork a} (_ : IsColimit c) ↦ c.condition) P.isColimit
  have hp : IsColimit (CokernelCofork.ofπ b w) := P.isColimit
  have : P.generators.IsFiniteType := ‹P.IsFinite›.isFiniteType_generators
  have : P.relations.IsFiniteType := ‹P.IsFinite›.isFiniteType_relations
  have : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have freeComparison (I : Type u) [Finite I] :
      IsIso (pullbackIhomComparison (SheafOfModules.free (R := Y.ringCatSheaf) I) f) := by
    let L : Y.Modules := SheafOfModules.free I
    let : ExactPairing L L := Scheme.Modules.exactPairingFree Y I
    exact isIso_pullbackIhomComparison_of_exactPairing (M := L) (f := f) (D := L)
  have := freeComparison P.generators.I
  have := freeComparison P.relations.I
  apply F.ihomComparison_isIso_of_cokernel_of_naturality a b w hp N
    ((pullbackIhomComparison A f).app N) ((pullbackIhomComparison B f).app N)
    ((pullbackIhomComparison M f).app N)
  · exact (pullback_map_pre_app_comp_pullbackIhomComparison_app f a N).symm
  · exact (pullback_map_pre_app_comp_pullbackIhomComparison_app f b N).symm

/-- Over an affine base, flat pullback commutes with internal Hom from a finitely presented
sheaf into any sheaf of modules. The source scheme is arbitrary. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_isAffine
    [IsAffine Y]
    (M N : Y.Modules) [M.IsFinitePresentation] :
    IsIso ((pullbackIhomComparison M f).app N) := by
  obtain ⟨P, hP⟩ := Scheme.Modules.exists_isFinite_presentation_of_isAffine M
  have : P.IsFinite := hP
  exact f.isIso_pullbackIhomComparison_app_of_presentation M N P

/-- Flat pullback commutes with internal Hom from a finitely presented module sheaf into any
module sheaf. Neither scheme needs to be affine or Noetherian. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app
    (M N : Y.Modules) [M.IsFinitePresentation] :
    IsIso ((pullbackIhomComparison M f).app N) := by
  refine (Scheme.Modules.isIso_iff_of_isOpenCover
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.hom) _).mpr
      fun V ↦ ?_
  have : IsAffine V.val := V.property
  have := V.val.isIso_pullbackIhomComparison_app M N
  have := (f ∣_ V.val).isIso_pullbackIhomComparison_app_of_isAffine
    ((Scheme.Modules.pullback V.val.ι).obj M) ((Scheme.Modules.pullback V.val.ι).obj N)
  have h := ((f ∣_ V.val).isIso_pullbackIhomComparison_app_comp_iff V.val.ι M N).mpr
    inferInstance
  rw [morphismRestrict_ι] at h
  have := (f ⁻¹ᵁ V.val).isIso_pullbackIhomComparison_app
    ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
  exact ((f ⁻¹ᵁ V.val).ι.isIso_pullbackIhomComparison_app_comp_iff f M N).mp h

end

end TauCeti.AlgebraicGeometry
