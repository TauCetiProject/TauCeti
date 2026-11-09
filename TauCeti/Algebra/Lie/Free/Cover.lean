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

namespace TauCeti

open scoped TensorProduct

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
  let f : R →ₗ[R] (FreeLieAlgebra ℚ L →ₗ[ℚ] L) :=
    { toFun := fun r => (LinearMap.lsmul R L r).restrictScalars ℚ ∘ₗ φ.toLinearMap
      map_add' := fun r s => by ext; simp
      map_smul' := fun a r => by ext; simp [mul_smul] }
  let π₀ : FreeLieCover R L →ₗ[R] L := TensorProduct.AlgebraTensorModule.lift f
  have hπ₀ (r : R) (x : FreeLieAlgebra ℚ L) : π₀ (r ⊗ₜ[ℚ] x) = r • φ x := rfl
  -- The bracket instance of the base change is not syntactically the one `add_lie` expects,
  -- so the additivity facts below are stated with it and proved by unification.
  have hadd_left (a b t' : FreeLieCover R L) :
      π₀ ⁅a + b, t'⁆ = π₀ ⁅a, t'⁆ + π₀ ⁅b, t'⁆ := by
    rw [← map_add]; exact congrArg π₀ (add_lie a b t')
  have hadd_right (t a b : FreeLieCover R L) :
      π₀ ⁅t, a + b⁆ = π₀ ⁅t, a⁆ + π₀ ⁅t, b⁆ := by
    rw [← map_add]; exact congrArg π₀ (lie_add t a b)
  have hlie : ∀ t t' : FreeLieCover R L, π₀ ⁅t, t'⁆ = ⁅π₀ t, π₀ t'⁆ := by
    intro t t'
    induction t using TensorProduct.inductionOn with
    | tmul r x =>
      induction t' using TensorProduct.inductionOn with
      | tmul r' x' =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul]
        simp only [hπ₀, LieHom.map_lie, smul_lie, lie_smul, mul_smul]
        exact smul_comm _ _ _
      | add a b ha hb => rw [hadd_right, map_add, lie_add, ha, hb]
    | add a b ha hb => rw [hadd_left, map_add, add_lie, ha, hb]
  refine ⟨{ π₀ with map_lie' := fun {t t'} => hlie t t' }, fun y => ?_⟩
  refine ⟨1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ y, ?_⟩
  -- The bundled Lie homomorphism has `π₀` as its underlying function.
  change π₀ (1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ y) = y
  rw [hπ₀, one_smul]
  exact FreeLieAlgebra.lift_of_apply id y

end TauCeti
