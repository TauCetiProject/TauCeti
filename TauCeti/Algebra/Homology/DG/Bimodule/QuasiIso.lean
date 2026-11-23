/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Category
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso

/-!
# Quasi-isomorphisms of DG bimodules from homotopy inverses

A morphism of DG `(A, B)`-bimodules whose underlying chain map has an inverse up to homotopy is a
quasi-isomorphism of the underlying DG right `B`-modules
(`TauCeti.DGBimoduleCat.isQuasiIso_forgetToRightModuleCat_map_of_homotopyInverse`). It is the
right-module criterion `TauCeti.DGRightModuleCat.isQuasiIso_of_homotopyInverse` applied to the
forgotten morphism: the inverse and the homotopies need only be linear over the ground ring.

The statement is phrased on the bundled bimodules, with their own differentials. The module
structures of the forgotten right modules are then those carried by the bundled objects, and no
instance search on their carriers is needed when it is applied to concrete bimodules.

## References

* B. Keller, *Deriving DG categories*, Section 3.
-/

public section

open CategoryTheory

namespace TauCeti.DGBimoduleCat

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- **A morphism of DG bimodules with a homotopy inverse is a quasi-isomorphism** of the
underlying DG right modules. The inverse `g` and the homotopies `K` and `L`, with
`g ∘ φ = 1 + d K + K d` and `φ ∘ g = 1 + d L + L d`, need only be linear over the ground ring,
and `g` must commute with the differentials. -/
theorem isQuasiIso_forgetToRightModuleCat_map_of_homotopyInverse
    {X Y : DGBimoduleCat.{uR, uA, uB, uM} hA hB} (φ : X ⟶ Y) (g : Y →ₗ[R] X) (K : X →ₗ[R] X)
    (L : Y →ₗ[R] Y) (hg : ∀ y, X.differential (g y) = g (Y.differential y))
    (hK : ∀ x, g (φ x) = x + X.differential (K x) + K (X.differential x))
    (hL : ∀ y, φ (g y) = y + Y.differential (L y) + L (Y.differential y)) :
    DGRightModuleCat.IsQuasiIso (forgetToRightModuleCat.map φ) :=
  DGRightModuleCat.isQuasiIso_of_homotopyInverse (forgetToRightModuleCat.map φ) g K L hg hK hL

end TauCeti.DGBimoduleCat
