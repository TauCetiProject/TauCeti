/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Free
public import Mathlib.Algebra.Module.Rat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.Rat

/-!
# Lie algebras over `ℚ`-algebras are quotients of Lie algebras free as modules

Over a commutative `ℚ`-algebra `R`, every `R`-Lie algebra `L` is the image of a Lie algebra that is
free as an `R`-module. The cover is the base change to `R` of the free Lie algebra over `ℚ` on the
underlying set of `L`; it is free because every `ℚ`-module is. Freeness is the hypothesis of the
Poincaré–Birkhoff–Witt theorem, so such covers reduce statements about arbitrary Lie algebras to
the free-module case.

## Main definitions and results

* `TauCeti.FreeLieCover`: the base change `R ⊗[ℚ] FreeLieAlgebra ℚ L`, a Lie algebra over `R`
  that is free as an `R`-module (this is found by instance search, from `Module.Free.tensor`).
* `TauCeti.exists_lieHom_surjective_freeLieCover`: a surjective `R`-Lie homomorphism from
  `FreeLieCover R L` onto `L`.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- The free Lie algebra over `ℚ` on the underlying set of `L`, extended to the `ℚ`-algebra `R`. -/
abbrev FreeLieCover (R L : Type*) [CommRing R] [Algebra ℚ R] := R ⊗[ℚ] FreeLieAlgebra ℚ L

variable (R L : Type*) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

/-- **Every Lie algebra over a `ℚ`-algebra is the image of a Lie algebra free as a module**: there
is a surjective `R`-Lie homomorphism from `FreeLieCover R L` onto `L`. -/
theorem exists_lieHom_surjective_freeLieCover :
    ∃ π : FreeLieCover R L →ₗ⁅R⁆ L, Function.Surjective π := by
  let _ : Module ℚ L := Module.compHom L (algebraMap ℚ R)
  have _ : IsScalarTower ℚ R L := ⟨fun q r l => by
    -- The rational action on `L` is by definition the action through `algebraMap ℚ R`.
    change (q • r) • l = (algebraMap ℚ R q) • (r • l)
    rw [Algebra.smul_def, mul_smul]⟩
  let _ : LieAlgebra ℚ L := { lie_smul := fun q x y => TauCeti.lie_rat_smul q x y }
  let φ : FreeLieAlgebra ℚ L →ₗ⁅ℚ⁆ L := FreeLieAlgebra.lift ℚ id
  refine ⟨φ.liftBaseChange R, fun y => ⟨1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ y, ?_⟩⟩
  rw [LieHom.liftBaseChange_tmul, one_smul]
  exact FreeLieAlgebra.lift_of_apply id y

end TauCeti
