/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.InternalHom.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Flat
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
import TauCeti.AlgebraicGeometry.Modules.InternalHom.Quasicoherent

/-!
# Flat pullback of internal Hom on an affine base

The canonical internal-Hom comparison is invertible along a flat scheme morphism when its
source sheaf is finitely presented, its target sheaf is quasicoherent, and the base scheme is
affine. The scheme mapping to that base is arbitrary. No local freeness or Noetherian hypothesis
is required.

A finite presentation expresses internal Hom as a kernel between internal Homs from finite free
sheaves. Flat pullback preserves this quasicoherent kernel, and the finite free comparisons are
invertible by duality. Source naturality identifies the induced kernel isomorphism with the
canonical comparison, rather than defining another base-change map.

The kernel comparison follows `CategoryTheory.Functor.ihomComparison_isIso_of_cokernel`.
Here the canonical comparison uses the oplax tensor comparison of pullback: pullback on all
module sheaves is not assumed to be lax monoidal.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_presentation`:
  invertibility from a finite global presentation, without an affineness hypothesis;
* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_isAffine`:
  invertibility for finitely presented sources over an affine base.

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
invertible under flat pullback into a quasicoherent target, without assuming the base affine. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_presentation
    (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (P : M.Presentation) [P.IsFinite] :
    IsIso ((pullbackIhomComparison M f).app N) := by
  let F := Scheme.Modules.pullback f
  let A : Y.Modules := SheafOfModules.free P.relations.I
  let B : Y.Modules := SheafOfModules.free P.generators.I
  let a : A ⟶ B := P.relations.π ≫ kernel.ι P.generators.π
  let b : B ⟶ M := P.generators.π
  have w : a ≫ b = 0 := by
    -- Use the presentation cocone's condition through the category of scheme modules.
    exact (fun {c : CokernelCofork a} (_ : IsColimit c) ↦ c.condition) P.isColimit
  have hp : IsColimit (CokernelCofork.ofπ b w) := P.isColimit
  have : P.generators.IsFiniteType := ‹P.IsFinite›.isFiniteType_generators
  have : P.relations.IsFiniteType := ‹P.IsFinite›.isFiniteType_relations
  have : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have freeComparison (I : Type u) [Finite I] :
      IsIso (pullbackIhomComparison (SheafOfModules.free (R := Y.ringCatSheaf) I) f) :=
    @isIso_pullbackIhomComparison_of_exactPairing X Y
      (SheafOfModules.free (R := Y.ringCatSheaf) I) inferInstance f
      (SheafOfModules.free (R := Y.ringCatSheaf) I) inferInstance
      (Scheme.Modules.exactPairingFree Y I)
  have := freeComparison P.generators.I
  have := freeComparison P.relations.I
  have : PreservesLimit (parallelPair ((pre a).app N) 0) F :=
    f.preservesKernel_pullback_of_flat ((pre a).app N)
  let k := KernelFork.ofι ((pre b).app N)
    (pre_app_comp_pre_app_eq_zero a b w N)
  let hk := KernelFork.mapIsLimit k
    (isLimitKernelForkPreOfIsColimit a b w hp N) F
  let hq := CokernelCofork.mapIsColimit _ hp F
  let ht := isLimitKernelForkPreOfIsColimit (F.map a) (F.map b)
    (by simp [← F.map_comp, w]) hq (F.obj N)
  have naturality {A B : Y.Modules} [A.IsQuasicoherent] [B.IsQuasicoherent]
      (g : A ⟶ B) :
      (pullbackIhomComparison B f).app N ≫ (pre (F.map g)).app (F.obj N) =
        F.map ((pre g).app N) ≫ (pullbackIhomComparison A f).app N :=
    (pullback_map_pre_app_comp_pullbackIhomComparison_app f g N).symm
  let e := KernelFork.mapIsoOfIsLimit hk ht
    (Arrow.isoMk (asIso ((pullbackIhomComparison _ f).app N))
      (asIso ((pullbackIhomComparison _ f).app N)) (naturality a))
  have he : e.hom = (pullbackIhomComparison M f).app N := by
    apply Fork.IsLimit.hom_ext ht
    exact (KernelFork.mapOfIsLimit_ι _ ht _).trans (naturality b).symm
  rw [← he]
  infer_instance

/-- Over an affine base, flat pullback commutes with internal Hom from a finitely presented
sheaf into a quasicoherent sheaf. The source scheme is arbitrary. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_pullbackIhomComparison_app_of_isAffine
    [IsAffine Y]
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsQuasicoherent] :
    letI := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
    IsIso ((pullbackIhomComparison M f).app N) := by
  let := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation M
  obtain ⟨P, hP⟩ := Scheme.Modules.exists_isFinite_presentation_of_isAffine M
  have : P.IsFinite := hP
  exact f.isIso_pullbackIhomComparison_app_of_presentation M N P

end

end TauCeti.AlgebraicGeometry
