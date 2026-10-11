/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Normalization.Basic
public import TauCeti.AlgebraicGeometry.Modules.StructureSheafSequence

/-!
# The structure-sheaf sequence of relative normalization

The relative normalization of a quasi-compact, quasi-separated, scheme-theoretically dominant
morphism is scheme-theoretically dominant over the target. Its map on structure sheaves is
therefore injective, even when the target is nonreduced.

For `ν = f.fromNormalization`, the standard sequence
`ShortComplex.cokernelSequence (SheafOfModules.unitToPushforwardObjUnit ν.toRingCatSheafHom)`
is short exact by `ν.shortExact_structureSheafSequence`; its third term is quasicoherent
because `ν` is integral, hence affine. These assertions require neither finiteness of the
normalization nor a Noetherian target. The cokernel is the sheaf-theoretic defect term used
in the comparison of a curve with its normalization; its local computation at nodes is a
separate question.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise IV.1.8 (the normalization sequence).
* The Stacks Project, Tag 035H (relative normalization).
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- Relative normalization of a scheme-theoretically dominant morphism is
scheme-theoretically dominant over the target. In particular, its structure-sheaf map is
injective and its cokernel sequence is short exact. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_fromNormalization
    [IsSchemeTheoreticallyDominant f] : IsSchemeTheoreticallyDominant f.fromNormalization := by
  constructor
  apply eq_bot_iff.mpr
  calc f.fromNormalization.ker ≤ (f.toNormalization ≫ f.fromNormalization).ker :=
      Scheme.Hom.le_ker_comp _ _
    _ = ⊥ := by rw [f.toNormalization_fromNormalization, f.ker_eq_bot]

end TauCeti
