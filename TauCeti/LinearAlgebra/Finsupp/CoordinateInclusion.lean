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

The coordinate inclusion `Finsupp.coordinateInclusion` embeds `Fin n → 𝕜` into `ℕ →₀ 𝕜`,
with range the functions supported on `Set.Iio n`. It commutes with extension by zero
between finite coordinate spaces.
These maps realize finite coordinate stages inside the countable coordinate space.
-/

public section

namespace Finsupp

open Set

variable {𝕜 : Type*} [Field 𝕜]

/-- The coordinate inclusion `𝕜^n → ℕ →₀ 𝕜`, sending the `i`-th coordinate vector to the
`i`-th coordinate vector. -/
noncomputable def coordinateInclusion (n : ℕ) : (Fin n → 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  Finsupp.lmapDomain 𝕜 𝕜 Fin.val ∘ₗ (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin n)).symm.toLinearMap

@[simp]
theorem coordinateInclusion_single (n : ℕ) (i : Fin n) (a : 𝕜) :
    coordinateInclusion n (Pi.single i a) = Finsupp.single (i : ℕ) a := by
  simp [coordinateInclusion]

@[simp]
theorem coordinateInclusion_apply_val {n : ℕ} (v : Fin n → 𝕜) (i : Fin n) :
    coordinateInclusion n v i = v i := by
  simp [coordinateInclusion, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

theorem coordinateInclusion_apply_of_le {n : ℕ} (v : Fin n → 𝕜) {i : ℕ} (hi : n ≤ i) :
    coordinateInclusion n v i = 0 := by
  simp only [coordinateInclusion, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simpa [Fin.range_val] using hi)

theorem coordinateInclusion_injective (n : ℕ) :
    Function.Injective (coordinateInclusion (𝕜 := 𝕜) n) :=
  (Finsupp.mapDomain_injective Fin.val_injective).comp
    (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin n)).symm.injective

/-- The image of the coordinate inclusion of `𝕜^n` consists of the finitely supported functions
vanishing from coordinate `n` on. -/
theorem range_coordinateInclusion (n : ℕ) :
    LinearMap.range (coordinateInclusion (𝕜 := 𝕜) n) = Finsupp.supported 𝕜 𝕜 (Iio n) := by
  simpa [coordinateInclusion, LinearMap.range_comp, Fin.range_val] using
    Finsupp.lmapDomain_supported 𝕜 𝕜 (Fin.val : Fin n → ℕ) univ

/-- The coordinate inclusions are compatible with the inclusions `𝕜^m → 𝕜^n` onto the first
coordinates. -/
@[simp]
theorem coordinateInclusion_comp_extendByZero_castLE {m n : ℕ} (h : m ≤ n) :
    coordinateInclusion (𝕜 := 𝕜) n ∘ₗ Function.ExtendByZero.linearMap 𝕜 𝕜 (Fin.castLE h) =
      coordinateInclusion m := by
  refine LinearMap.pi_ext fun i a ↦ ?_
  simp [Function.ExtendByZero.linearMap_single 𝕜 (Fin.castLE_injective h)]

end Finsupp
