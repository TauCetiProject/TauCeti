/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Simple-coroot coordinates for the type-B spin construction

The numbered simple coroots are coordinate evaluation cocharacters on the full weight lattice.
This calculation is shared by the integral spin carrier and the generated group, without
requiring either carrier construction.

The proof follows `TauCeti.Algebra.Lie.E7.Minuscule.Root.Coordinates`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

namespace TauCeti.TypeBSpinCarrier

/-- The coordinate evaluation cocharacter represents the named simple coroot. -/
theorem cocharEquiv_symm_coroot_simpleIndex (n : ℕ)
    (ht : (DynkinType.B (n + 1)).Valid) (i : Fin (n + 1)) :
    SplitTorus.cocharEquiv.symm
        (((DynkinType.B (n + 1)).simplyConnectedRootDatum ht).coroot
          ((DynkinType.B (n + 1)).simpleIndex ht i)) =
      (Finsupp.applyAddHom i).toMultiplicative := by
  -- Fix the evaluation lattice explicitly: the rank of B (n + 1) is n + 1.
  have heval := SplitTorus.cocharEquiv_applyAddHom (σ := Fin (n + 1)) i
  exact SplitTorus.cocharEquiv.symm_apply_eq.mpr
    (((DynkinType.B (n + 1)).coroot_simpleIndex ht i).trans heval.symm)

end TauCeti.TypeBSpinCarrier
