/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne

/-!
# Algebra of the logarithmic unit coordinates

Mathlib's `NumberField.mixedEmbedding.fundamentalCone.expMapBasis` parametrizes the positive
orthant of `realSpace K` by `z ↦ e^(z_{w₀}) ∏_i |η_i|^(z_i)`, where `η_i` runs over the fundamental
system of units `NumberField.Units.fundSystem K`. It is the exponential of a linear change of
coordinates, so it turns addition and scalar multiplication of coordinates into the coordinatewise
product and powers of positive vectors. It maps the points with integral coordinates and vanishing
`w₀`-coordinate to the vectors of absolute values of the units, so multiplying a positive vector by
the absolute values of a unit translates its coordinates.

## Main results

* `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_add`: `expMapBasis (z + z')` is the
  coordinatewise product of `expMapBasis z` and `expMapBasis z'`.
* `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_smul`: `expMapBasis (c • z)` is the
  coordinatewise `c`-th power of `expMapBasis z`.
* `NumberField.mixedEmbedding.fundamentalCone.expMapBasis_intCoord`: the integral point with
  coordinates `c_i` is the vector of absolute values of the unit `∏_i η_i ^ c_i`.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem

namespace NumberField.mixedEmbedding.fundamentalCone

variable {K : Type*} [Field K] [NumberField K]

/-- `expMapBasis` turns the addition of coordinates into the coordinatewise product. -/
theorem expMapBasis_add (z z' : realSpace K) :
    expMapBasis (z + z') = expMapBasis z * expMapBasis z' := by
  rw [expMapBasis_apply, expMapBasis_apply, expMapBasis_apply, map_add, expMap_add]

/-- `expMapBasis` turns the scaling of coordinates by `c` into the coordinatewise `c`-th power. -/
theorem expMapBasis_smul (c : ℝ) (z : realSpace K) :
    expMapBasis (c • z) = expMapBasis z ^ c := by
  rw [expMapBasis_apply, expMapBasis_apply, map_smul, expMap_smul]

open scoped Classical in
/-- The point of `realSpace K` with `w₀`-coordinate `0` and coordinate `c w` at every other
infinite place `w`: the integral points of the coordinates of `expMapBasis` in the hyperplane
`z_{w₀} = 0`, as an additive homomorphism. -/
noncomputable def intCoord : ({w : InfinitePlace K // w ≠ w₀} → ℤ) →+ realSpace K where
  toFun c w := if h : w = w₀ then 0 else (c ⟨w, h⟩ : ℝ)
  map_zero' := by
    ext w
    by_cases h : w = w₀ <;> simp [h]
  map_add' c c' := by
    ext w
    by_cases h : w = w₀ <;> simp [h]

@[simp]
theorem intCoord_apply_w₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℤ) : intCoord c w₀ = 0 := by
  simp [intCoord]

@[simp]
theorem intCoord_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℤ)
    (w : {w : InfinitePlace K // w ≠ w₀}) : intCoord c w = c w := by
  simp [intCoord, w.2]

open scoped Classical in
/-- The integral point `intCoord c` of the coordinates of `expMapBasis` is mapped to the vector of
absolute values of the unit `∏_i η_i ^ c_i`, where `η_i` runs over the fundamental system of
units. -/
theorem expMapBasis_intCoord (c : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    expMapBasis (intCoord c) =
      fun w ↦ w ((∏ i, fundSystem K (equivFinRank.symm i) ^ c i : (𝓞 K)ˣ) : K) := by
  -- Mathlib has no `coe_prod` for the coercion `(𝓞 K)ˣ → K`, so we write it as a bundled monoid
  -- hom (by definition, as Mathlib's `NumberField.Units.coe_zpow` does) to use `map_prod`.
  let φ : (𝓞 K)ˣ →* K := (Units.coeHom K).comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
  have hφ (x : (𝓞 K)ˣ) : (x : K) = φ x := rfl
  ext w
  rw [expMapBasis_apply', intCoord_apply_w₀, Real.exp_zero, one_smul, hφ, map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [intCoord_apply, Real.rpow_intCast, map_zpow, map_zpow₀, ← hφ]

end NumberField.mixedEmbedding.fundamentalCone
