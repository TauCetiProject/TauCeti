/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Presentation
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Presentation

/-!
# Pullback of tensor products from an affine base

For a morphism `f : X ⟶ Y` with affine target `Y`, the canonical comparison
`f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` is an isomorphism whenever either factor is quasicoherent.
The other factor is an arbitrary sheaf of modules. No flatness or finiteness assumption is
required. The comparison is the tensor map of the existing oplax monoidal pullback, so its
associativity and unit compatibilities are retained. These affine statements are the local input
for the same comparison over an arbitrary target
(`Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent` in
`TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent`).

The strong symmetric monoidal pullback on quasicoherent sheaves is packaged in
`TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal`.

## References

* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)

open _root_.AlgebraicGeometry.Scheme.Modules

/-- Pullback from an affine base preserves a tensor product with a quasicoherent left factor.
The right factor need not be quasicoherent. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ_of_isAffine
    (M N : Y.Modules)
    [M.IsQuasicoherent] : IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) := by
  obtain ⟨P⟩ := M.nonempty_presentation_of_isAffine
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  exact P.isIso_pullback_δ f.toRingCatSheafHom N

/-- Pullback from an affine base preserves a tensor product with a quasicoherent right factor.
The left factor need not be quasicoherent. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ_right_of_isAffine
    (M N : Y.Modules)
    [N.IsQuasicoherent] : IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) := by
  obtain ⟨P⟩ := N.nonempty_presentation_of_isAffine
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  exact P.isIso_pullback_δ_right f.toRingCatSheafHom M

end

end AlgebraicGeometry

end TauCeti
