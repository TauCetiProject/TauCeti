/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.DerivationOfEnd
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# The adjoint action on a symmetric algebra

Let `L` be a Lie algebra over a commutative ring `R`. The adjoint endomorphism `y ↦ ⁅x, y⁆`
extends uniquely from `L` to a derivation of its symmetric algebra `S(L)`, and these extensions
preserve brackets. This file specialises `TauCeti.SymmetricAlgebra.derivationOfEnd` to
`LieAlgebra.ad` and registers the resulting Lie-module structure of `L` on `S(L)`, so that the
generic Lie-module API applies: `LieModule.toEnd R L S(L)` is the adjoint representation of `L`
on the underlying module of `S(L)`, and `TauCeti.UniversalEnvelopingAlgebra.representation R L S(L)`
is its extension to an algebra homomorphism out of `U(L)`.

On a product of symmetric generators the action differentiates one factor at a time, so it
preserves each homogeneous degree; and it is natural in `L`. Both facts are inherited from
`derivationOfEnd`.

## Main definitions and results

* `TauCeti.SymmetricAlgebra.adjointDerivation`: the Lie homomorphism from `L` to derivations of
  `S(L)`, with `TauCeti.SymmetricAlgebra.adjointDerivation_ι` its value `ι ⁅x, y⁆` on a
  generator `ι y`.
* `TauCeti.SymmetricAlgebra.instLieRingModule`, `TauCeti.SymmetricAlgebra.instLieModule`: `S(L)`
  is a Lie module over `L` through the adjoint derivations, with
  `TauCeti.SymmetricAlgebra.lie_eq_adjointDerivation` identifying the bracket.
* `TauCeti.SymmetricAlgebra.map_apply_adjointDerivation`: naturality under Lie homomorphisms.
* `TauCeti.SymmetricAlgebra.adjointDerivation_mem_homogeneousSubmodule`: the action preserves
  each homogeneous degree.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "S" => SymmetricAlgebra R L
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoint action of `L` on its symmetric algebra, by derivations: `x` acts by the
derivation extending `LieAlgebra.ad R L x`. -/
noncomputable def adjointDerivation : L →ₗ⁅R⁆ Derivation R S S :=
  (derivationOfEnd R L).comp (LieAlgebra.ad R L)

/-- The adjoint derivation of `x` is the derivation induced by the endomorphism `ad x`. -/
theorem adjointDerivation_apply (x : L) :
    adjointDerivation R L x = derivationOfEnd R L (LieAlgebra.ad R L x) :=
  (rfl)

/-- The adjoint derivation sends a symmetric generator `ι y` to `ι ⁅x, y⁆`. -/
@[simp]
theorem adjointDerivation_ι (x y : L) :
    adjointDerivation R L x (ι R L y) = ι R L ⁅x, y⁆ := by
  rw [adjointDerivation_apply, derivationOfEnd_ι, LieAlgebra.ad_apply]

/-- The symmetric algebra of `L` is a Lie ring module over `L` through the adjoint derivations. -/
noncomputable instance instLieRingModule : LieRingModule L S :=
  LieRingModule.compLieHom S (adjointDerivation R L)

/-- The symmetric algebra of `L` is a Lie module over `L` through the adjoint derivations. -/
noncomputable instance instLieModule : LieModule R L S :=
  LieModule.compLieHom S (adjointDerivation R L)

/-- The bracket of `x : L` with `p ∈ S(L)` is the adjoint derivation of `x` applied to `p`. -/
@[simp]
theorem lie_eq_adjointDerivation (x : L) (p : S) : ⁅x, p⁆ = adjointDerivation R L x p :=
  (rfl)

section Naturality

variable {L} {L' : Type w} [LieRing L'] [LieAlgebra R L']

/-- The symmetric-algebra map induced by a Lie homomorphism intertwines the adjoint derivations. -/
theorem map_apply_adjointDerivation (f : L →ₗ⁅R⁆ L') (x : L) (p : S) :
    map R f.toLinearMap (adjointDerivation R L x p) =
      adjointDerivation R L' (f x) (map R f.toLinearMap p) := by
  rw [adjointDerivation_apply, adjointDerivation_apply]
  exact map_apply_derivationOfEnd R f.toLinearMap (LinearMap.ext fun y => by simp) p

end Naturality

/-- Every adjoint derivation preserves each homogeneous submodule of the symmetric algebra. -/
theorem adjointDerivation_mem_homogeneousSubmodule (x : L) {n : ℕ} {p : S}
    (hp : p ∈ homogeneousSubmodule R L n) :
    adjointDerivation R L x p ∈ homogeneousSubmodule R L n := by
  rw [adjointDerivation_apply]
  exact derivationOfEnd_mem_homogeneousSubmodule R L (LieAlgebra.ad R L x) hp

end TauCeti.SymmetricAlgebra
