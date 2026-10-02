/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic

/-!
# The rank-two dyadic generators `u^{(2)}(2^k)` and `v^{(2)}(2^k)`

On `(ℤ/2^k)²` this file constructs the two finite quadratic modules

```text
u:  q(x) = x₁x₂ / 2^k,            b(x, y) = (x₁y₂ + y₁x₂) / 2^k,
v:  q(x) = (x₁² + x₁x₂ + x₂²) / 2^k,  b(x, y) = (2x₁y₁ + x₁y₂ + y₁x₂ + 2x₂y₂) / 2^k.
```

For `k ≥ 1` these are **Nikulin's rank-two dyadic generators** `u^{(2)}(2^k)` and `v^{(2)}(2^k)`.
In the half-norm convention they are the discriminant forms of the `2`-adic lattices with Gram
matrices `2^k·!![0,1;1,0]` and `2^k·!![2,1;1,2]`: the pairing matrix of each is the inverse Gram
matrix of the unscaled lattice divided by `2^k`, and the inverse of `!![2,1;1,2]` is congruent to
`!![2,1;1,2]` over `ℤ₂`, because its determinant `3` is a `2`-adic unit. Together with the cyclic
generators `q_θ^{(p)}(p^k)` they generate every nondegenerate finite quadratic module under
orthogonal sum; at `p = 2` the two rank-two forms are needed because a `2`-adic lattice of
type II need not be diagonalizable.

Both forms are presented as compositions of a `ℤ/2^k`-valued quadratic map with the injection
`ZMod.toRatAddCircle` of `ℤ/2^k` into `ℚ/ℤ`, so their values are honest residues and no lifting
argument is needed. Both are nondegenerate for every `k`: for `u` pairing with the two coordinate
vectors recovers the coordinates, and for `v` it recovers `2x₁ + x₂` and `x₁ + 2x₂`, which
determine `x` because `3` is a unit modulo `2^k`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.dyadicU`: the finite quadratic module `u^{(2)}(2^k)`.
* `TauCeti.FiniteQuadraticModule.dyadicV`: the finite quadratic module `v^{(2)}(2^k)`.
* `TauCeti.FiniteQuadraticModule.isNondegenerate_dyadicU` and
  `TauCeti.FiniteQuadraticModule.isNondegenerate_dyadicV`: both are nondegenerate.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8 for the
  generators, in particular Proposition 1.8.1.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable (k : ℕ)

/-! ## `u^{(2)}(2^k)` -/

/-- The group `(ℤ/2^k)²` with quadratic form `q(x) = x₁x₂ / 2^k` and pairing
`b(x, y) = (x₁y₂ + y₁x₂) / 2^k`. For `k ≥ 1` this is **Nikulin's dyadic generator**
`u^{(2)}(2^k)`, the discriminant form of the `2`-adic lattice with Gram matrix
`2^k·!![0,1;1,0]`, the hyperbolic plane scaled by `2^k`. -/
@[expose] noncomputable def dyadicU : FiniteQuadraticModule :=
  ofQuadraticMap <| (ZMod.toRatAddCircle (2 ^ k)).toIntLinearMap.compQuadraticMap
    (QuadraticMap.linMulLin
      (AddMonoidHom.fst (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap
      (AddMonoidHom.snd (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap)

/-- The quadratic form of `u^{(2)}(2^k)` is `x ↦ x₁x₂ / 2^k`. -/
@[simp]
theorem dyadicU_quadratic (x : ZMod (2 ^ k) × ZMod (2 ^ k)) :
    (dyadicU k).quadratic x = ZMod.toRatAddCircle (2 ^ k) (x.1 * x.2) := (rfl)

/-- The pairing of `u^{(2)}(2^k)` is `(x, y) ↦ (x₁y₂ + y₁x₂) / 2^k`. -/
@[simp]
theorem dyadicU_pairing (x y : ZMod (2 ^ k) × ZMod (2 ^ k)) :
    (dyadicU k).toFiniteBilinearModule.pairing x y =
      ZMod.toRatAddCircle (2 ^ k) (x.1 * y.2 + y.1 * x.2) := by
  unfold dyadicU
  rw [ofQuadraticMap_pairing, QuadraticMap.polar]
  simp only [LinearMap.compQuadraticMap_apply, QuadraticMap.linMulLin_apply,
    AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, Prod.fst_add,
    Prod.snd_add, ← map_sub]
  congr 1
  ring

/-- **`u^{(2)}(2^k)` is nondegenerate**: pairing with the two coordinate vectors recovers the
two coordinates. -/
theorem isNondegenerate_dyadicU : (dyadicU k).IsNondegenerate := by
  -- The carrier of `dyadicU k` is `(ℤ/2^k)²` only after unfolding, so the radical is computed on
  -- elements of `(ℤ/2^k)²` and transported by definitional unfolding at the end.
  have key : ∀ x : ZMod (2 ^ k) × ZMod (2 ^ k),
      (dyadicU k).toFiniteBilinearModule.pairing x = 0 → x = 0 := fun x hx ↦ by
    -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
    have h₁ : (dyadicU k).toFiniteBilinearModule.pairing x (1, 0) = 0 := DFunLike.congr_fun hx _
    have h₂ : (dyadicU k).toFiniteBilinearModule.pairing x (0, 1) = 0 := DFunLike.congr_fun hx _
    rw [dyadicU_pairing, ZMod.toRatAddCircle_eq_zero] at h₁ h₂
    simp only [mul_zero, one_mul, zero_add, mul_one, zero_mul, add_zero] at h₁ h₂
    exact Prod.ext h₂ h₁
  exact (FiniteBilinearModule.isNondegenerate_iff_injective _).2
    ((injective_iff_map_eq_zero _).2 key)

/-! ## `v^{(2)}(2^k)` -/

/-- The group `(ℤ/2^k)²` with quadratic form `q(x) = (x₁² + x₁x₂ + x₂²) / 2^k` and pairing
`b(x, y) = (2x₁y₁ + x₁y₂ + y₁x₂ + 2x₂y₂) / 2^k`. For `k ≥ 1` this is **Nikulin's dyadic
generator** `v^{(2)}(2^k)`, the discriminant form of the `2`-adic lattice with Gram matrix
`2^k·!![2,1;1,2]`. -/
@[expose] noncomputable def dyadicV : FiniteQuadraticModule :=
  ofQuadraticMap <| (ZMod.toRatAddCircle (2 ^ k)).toIntLinearMap.compQuadraticMap
    (QuadraticMap.linMulLin
        (AddMonoidHom.fst (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap
        (AddMonoidHom.fst (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap +
      QuadraticMap.linMulLin
        (AddMonoidHom.fst (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap
        (AddMonoidHom.snd (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap +
      QuadraticMap.linMulLin
        (AddMonoidHom.snd (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap
        (AddMonoidHom.snd (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap)

/-- The quadratic form of `v^{(2)}(2^k)` is `x ↦ (x₁² + x₁x₂ + x₂²) / 2^k`. -/
@[simp]
theorem dyadicV_quadratic (x : ZMod (2 ^ k) × ZMod (2 ^ k)) :
    (dyadicV k).quadratic x = ZMod.toRatAddCircle (2 ^ k) (x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2) := by
  unfold dyadicV
  rw [ofQuadraticMap_quadratic]
  simp only [LinearMap.compQuadraticMap_apply, add_apply, QuadraticMap.linMulLin_apply,
    AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, sq]

/-- The pairing of `v^{(2)}(2^k)` is `(x, y) ↦ (2x₁y₁ + x₁y₂ + y₁x₂ + 2x₂y₂) / 2^k`. -/
@[simp]
theorem dyadicV_pairing (x y : ZMod (2 ^ k) × ZMod (2 ^ k)) :
    (dyadicV k).toFiniteBilinearModule.pairing x y =
      ZMod.toRatAddCircle (2 ^ k) (2 * x.1 * y.1 + x.1 * y.2 + y.1 * x.2 + 2 * x.2 * y.2) := by
  unfold dyadicV
  rw [ofQuadraticMap_pairing, QuadraticMap.polar]
  simp only [LinearMap.compQuadraticMap_apply, add_apply, QuadraticMap.linMulLin_apply,
    AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd, Prod.fst_add,
    Prod.snd_add, ← map_sub]
  congr 1
  ring

/-- **`v^{(2)}(2^k)` is nondegenerate**: pairing with the two coordinate vectors recovers
`2x₁ + x₂` and `x₁ + 2x₂`, which determine `x` because `3` is a unit modulo `2^k`. -/
theorem isNondegenerate_dyadicV : (dyadicV k).IsNondegenerate := by
  -- The carrier of `dyadicV k` is `(ℤ/2^k)²` only after unfolding, so the radical is computed on
  -- elements of `(ℤ/2^k)²` and transported by definitional unfolding at the end.
  have key : ∀ x : ZMod (2 ^ k) × ZMod (2 ^ k),
      (dyadicV k).toFiniteBilinearModule.pairing x = 0 → x = 0 := fun x hx ↦ by
    -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
    have h₁ : (dyadicV k).toFiniteBilinearModule.pairing x (1, 0) = 0 := DFunLike.congr_fun hx _
    have h₂ : (dyadicV k).toFiniteBilinearModule.pairing x (0, 1) = 0 := DFunLike.congr_fun hx _
    rw [dyadicV_pairing, ZMod.toRatAddCircle_eq_zero] at h₁ h₂
    have h3 : IsUnit (3 : ZMod (2 ^ k)) := by
      have := (ZMod.isUnit_iff_coprime 3 (2 ^ k)).2 (Nat.Coprime.pow_right _ (by norm_num))
      exact_mod_cast this
    have hx₁ : x.1 = 0 := h3.mul_right_eq_zero.1 (by linear_combination 2 * h₁ - h₂)
    have hx₂ : x.2 = 0 := by linear_combination h₁ - 2 * hx₁
    exact Prod.ext hx₁ hx₂
  exact (FiniteBilinearModule.isNondegenerate_iff_injective _).2
    ((injective_iff_map_eq_zero _).2 key)

end TauCeti.FiniteQuadraticModule
