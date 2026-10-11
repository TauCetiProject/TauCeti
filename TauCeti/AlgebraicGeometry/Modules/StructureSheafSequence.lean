/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Affine
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# The structure-sheaf sequence of a dominant morphism

For a quasi-compact, scheme-theoretically dominant morphism `f : X ⟶ Y`, the map
`𝒪_Y → f_* 𝒪_X` is injective. Together with its cokernel it forms a short exact sequence
of sheaves of modules. If `f` is affine, the cokernel is quasicoherent.

For a normalization this cokernel measures the failure of regular functions on the
normalization to descend. Its exact sequence is the input to the cohomological comparison
between a curve and its normalization. Quasi-compactness suffices for injectivity, and no
finiteness or Noetherian hypothesis is imposed on the affine cokernel result.

The sequence is Mathlib's `ShortComplex.cokernelSequence`, and its first map is Mathlib's
`SheafOfModules.unitToPushforwardObjUnit`. No additional quotient or exactness notion is used.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise IV.1.8 (the normalization sequence).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a quasi-compact scheme-theoretically dominant morphism, pullback of regular functions
is a monomorphism of sheaves of modules. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.mono_unitToPushforwardObjUnit
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f] :
    Mono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply _root_.PresheafOfModules.mono_of_injective
  intro U
  -- The component of the module-sheaf unit is the structure-presheaf map `f.app`.
  exact f.app_injective U.unop

/-- The structure sheaf, its direct image, and their quotient form a short exact sequence
for every quasi-compact scheme-theoretically dominant morphism. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.shortExact_structureSheafSequence
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f] :
    (ShortComplex.cokernelSequence
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).ShortExact := by
  -- Unfold the standard sequence to expose its object projections for typeclass inference.
  dsimp only [ShortComplex.cokernelSequence]
  exact { exact := ShortComplex.cokernelSequence_exact _ }

/-- For an affine morphism the quotient of the direct image of the structure sheaf by the
image of the base's structure sheaf is quasicoherent. Injectivity is not required. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isQuasicoherent_cokernel_unitToPushforwardObjUnit
    [IsAffineHom f] :
    (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).IsQuasicoherent := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf X
  have h := isQuasicoherent_pushforward_of_isAffineHom f (SheafOfModules.unit X.ringCatSheaf)
  have : ((SheafOfModules.pushforward f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent := by
    simpa only [Scheme.Modules.pushforward] using h
  exact Scheme.Modules.isQuasicoherent_cokernel _

end

end TauCeti
