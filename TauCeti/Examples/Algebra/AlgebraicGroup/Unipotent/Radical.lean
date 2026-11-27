/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Characteristic

/-!
# Checks for unipotent radicals

The defining Hopf ideal of the unipotent radical `R_u(G)` cuts out `R_u(G)` as a closed subgroup
of `G`, so larger ideals give smaller subgroups: the zero ideal gives `R_u(G) = G` and the
augmentation ideal gives `R_u(G) = 1`. Over any field `k`:

* the radical ideal of `𝔾_a` is zero, so `R_u(𝔾_a) = 𝔾_a`;
* the radical ideal of `GL_n` is the augmentation ideal, so `R_u(GL_n) = 1`;
* the radical ideal of `SL_n` is the augmentation ideal, so `R_u(SL_n) = 1`; for `n = 2` this
  holds in every characteristic although `SL₂` contains the non-normal one-dimensional unipotent
  subgroup `U₂`: maximality is among normal subgroups;
* the radical ideal of `Sp₂ₘ` is the augmentation ideal, so `R_u(Sp₂ₘ) = 1`.

The last three are the pseudo-reductivity of reductive groups,
`TauCeti.reductiveCommHopfAlgProperty.pseudoReductive`, applied to the reductivity of `GL_n`,
`SL_n` and `Sp₂ₘ` over every field.
-/

public section

namespace TauCeti.Examples

open FiniteTypeCommHopfAlgCat

variable (k : Type) [Field k]

/-- The radical ideal of `𝔾_a` is zero: `R_u(𝔾_a) = 𝔾_a`. -/
example :
    unipotentRadicalDefiningIdeal (FiniteTypeCommHopfAlgCat.of k (SymmetricAlgebra k k)) = ⊥ :=
  (unipotentRadicalDefiningIdeal_eq_bot_iff _).mpr
    ⟨AdditiveGroup.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k,
      AdditiveGroup.smoothUnipotentCommHopfAlgProperty_coordinateHopfAlgebra k⟩

/-- The radical ideal of `GL_n` is the augmentation ideal: `R_u(GL_n) = 1`. -/
example (n : ℕ) :
    unipotentRadicalDefiningIdeal (GeneralLinear.finiteTypeCoordinateHopfAlgebra k n) =
      HopfIdeal.augmentation k (GeneralLinear.finiteTypeCoordinateHopfAlgebra k n) :=
  (GeneralLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n).pseudoReductive
    |>.unipotentRadicalDefiningIdeal_eq_augmentation

/-- The radical ideal of `SL_n` is the augmentation ideal: `R_u(SL_n) = 1`, in every
characteristic; in particular for `SL₂`. -/
example (n : ℕ) :
    unipotentRadicalDefiningIdeal (SpecialLinear.finiteTypeCoordinateHopfAlgebra k n) =
      HopfIdeal.augmentation k (SpecialLinear.finiteTypeCoordinateHopfAlgebra k n) :=
  (SpecialLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n).pseudoReductive
    |>.unipotentRadicalDefiningIdeal_eq_augmentation

/-- The radical ideal of `Sp₂ₘ` is the augmentation ideal: `R_u(Sp₂ₘ) = 1`. -/
example (m : ℕ) :
    unipotentRadicalDefiningIdeal (Symplectic.finiteTypeCoordinateHopfAlgebra k m) =
      HopfIdeal.augmentation k (Symplectic.finiteTypeCoordinateHopfAlgebra k m) :=
  (Symplectic.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k m).pseudoReductive
    |>.unipotentRadicalDefiningIdeal_eq_augmentation

end TauCeti.Examples
