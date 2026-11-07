/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Smoothness of symmetric algebras

The symmetric algebra of a finite free module is a polynomial algebra in finitely many
variables (`SymmetricAlgebra.equivMvPolynomial`), hence a smooth algebra: formally smooth and
finitely presented. This is the smoothness input for the affine group schemes whose coordinate
algebras are symmetric algebras, such as the additive group `𝔾ₐ` with coordinate algebra
`SymmetricAlgebra R R`.
-/

public section

namespace TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The symmetric algebra of a finite free module is smooth: it is the polynomial algebra on a
basis. -/
instance instSmooth [Module.Free R M] [Module.Finite R M] :
    Algebra.Smooth R (SymmetricAlgebra R M) :=
  letI : Algebra.Smooth R (MvPolynomial (Module.Free.ChooseBasisIndex R M) R) :=
    ⟨inferInstance, inferInstance⟩
  Algebra.Smooth.of_equiv (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis R M)).symm

end TauCeti.SymmetricAlgebra
