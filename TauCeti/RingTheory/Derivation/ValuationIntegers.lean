/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Valuation.Integers

/-!
# Restricting derivations to rings of integers

Let `O` be a ring of integers for a valuation `v` on a commutative ring `K`, in the sense of
`Valuation.Integers`, so that `O` embeds into `K` with image the elements of valuation at most
`1`. A derivation `D` of `K` that maps elements of valuation at most `1` to elements of valuation
at most `1` maps the image of `O` into itself, so it restricts to a derivation of `O`. For instance
a derivation of a valued field preserving its valuation ring restricts to that ring, so
uniqueness statements for derivations of the valuation ring pass to such derivations of the field.

## Main definitions

* `Derivation.restrictIntegers`: the restriction to `O` of a derivation of `K` preserving `O`.

## Main results

* `Derivation.algebraMap_restrictIntegers`: the restriction agrees with `D` on `O`.
-/

public section

namespace Derivation

variable {R K Γ₀ O : Type*} [CommRing R] [CommRing K] [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} [CommRing O] [Algebra O K] [Algebra R K]

/-- The values on `O` of a derivation of `K` preserving `O`, as elements of `O`. -/
private noncomputable def restrictIntegersFun (D : Derivation R K K) (hv : v.Integers O)
    (hD : ∀ x, v x ≤ 1 → v (D x) ≤ 1) (x : O) : O :=
  (hv.exists_of_le_one (hD _ (hv.map_le_one x))).choose

private theorem algebraMap_restrictIntegersFun (D : Derivation R K K) (hv : v.Integers O)
    (hD : ∀ x, v x ≤ 1 → v (D x) ≤ 1) (x : O) :
    algebraMap O K (restrictIntegersFun D hv hD x) = D (algebraMap O K x) :=
  (hv.exists_of_le_one (hD _ (hv.map_le_one x))).choose_spec

variable [Algebra R O] [IsScalarTower R O K]

/-- The restriction to a ring of integers `O` of a derivation of `K` mapping elements of valuation
at most `1` to elements of valuation at most `1`. -/
noncomputable def restrictIntegers (D : Derivation R K K) (hv : v.Integers O)
    (hD : ∀ x, v x ≤ 1 → v (D x) ≤ 1) : Derivation R O O where
  toFun := restrictIntegersFun D hv hD
  map_add' x y := hv.hom_inj (by simp only [algebraMap_restrictIntegersFun, map_add])
  map_smul' r x := hv.hom_inj (by
    simp only [algebraMap_restrictIntegersFun, RingHom.id_apply, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, leibniz, map_algebraMap, mul_zero, add_zero])
  map_one_eq_zero' := hv.hom_inj (by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, algebraMap_restrictIntegersFun, map_one,
      map_one_eq_zero, map_zero])
  leibniz' x y := hv.hom_inj (by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, algebraMap_restrictIntegersFun, map_mul, leibniz,
      map_add, smul_eq_mul])

/-- The restriction of `D` to the ring of integers agrees with `D`. -/
@[simp]
theorem algebraMap_restrictIntegers (D : Derivation R K K) (hv : v.Integers O)
    (hD : ∀ x, v x ≤ 1 → v (D x) ≤ 1) (x : O) :
    algebraMap O K (D.restrictIntegers hv hD x) = D (algebraMap O K x) :=
  algebraMap_restrictIntegersFun D hv hD x

end Derivation
