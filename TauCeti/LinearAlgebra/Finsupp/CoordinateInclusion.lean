/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Order.Interval.Set.Fin
public import TauCeti.LinearAlgebra.ExtendByZero

/-!
# Inclusion of finite coordinate spaces into finitely supported functions

For a semiring `R`, the coordinate inclusion `Finsupp.coordinateInclusion` embeds `Fin n → R`
into `ℕ →₀ R`, with range the functions supported on `Set.Iio n`. It commutes with extension by
zero between finite coordinate spaces.
These maps realize finite coordinate stages inside the countable coordinate space.
-/

public section

namespace Finsupp

open Set

variable {R : Type*} [Semiring R]

/-- The coordinate inclusion `R^n → ℕ →₀ R`, sending the `i`-th coordinate vector to the
`i`-th coordinate vector. -/
noncomputable def coordinateInclusion (n : ℕ) : (Fin n → R) →ₗ[R] (ℕ →₀ R) :=
  Finsupp.lmapDomain R R Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm.toLinearMap

@[simp]
theorem coordinateInclusion_single (n : ℕ) (i : Fin n) (a : R) :
    coordinateInclusion n (Pi.single i a) = Finsupp.single (i : ℕ) a := by
  simp [coordinateInclusion]

@[simp]
theorem coordinateInclusion_apply_val {n : ℕ} (v : Fin n → R) (i : Fin n) :
    coordinateInclusion n v i = v i := by
  simp [coordinateInclusion, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

theorem coordinateInclusion_apply_of_le {n : ℕ} (v : Fin n → R) {i : ℕ} (hi : n ≤ i) :
    coordinateInclusion n v i = 0 := by
  simp only [coordinateInclusion, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simpa [Fin.range_val] using hi)

theorem coordinateInclusion_injective (n : ℕ) :
    Function.Injective (coordinateInclusion (R := R) n) :=
  (Finsupp.mapDomain_injective Fin.val_injective).comp
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm.injective

/-- The image of the coordinate inclusion of `R^n` consists of the finitely supported functions
vanishing from coordinate `n` on. -/
theorem range_coordinateInclusion (n : ℕ) :
    LinearMap.range (coordinateInclusion (R := R) n) = Finsupp.supported R R (Iio n) := by
  simpa [coordinateInclusion, LinearMap.range_comp, Fin.range_val] using
    Finsupp.lmapDomain_supported R R (Fin.val : Fin n → ℕ) univ

/-- The coordinate inclusions are compatible with the inclusions `R^m → R^n` onto the first
coordinates. -/
@[simp]
theorem coordinateInclusion_comp_extendByZero_castLE {m n : ℕ} (h : m ≤ n) :
    coordinateInclusion (R := R) n ∘ₗ Function.ExtendByZero.linearMap R R (Fin.castLE h) =
      coordinateInclusion m := by
  refine LinearMap.pi_ext fun i a ↦ ?_
  simp [Function.ExtendByZero.linearMap_single R (Fin.castLE_injective h)]

end Finsupp
