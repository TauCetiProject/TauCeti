/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Cyclic

/-!
# The dyadic cyclic generators `q_θ^{(2)}(2^k)`

For `k ≥ 1` and an integer `θ`, this file constructs the cyclic group `ℤ/2^k` with

```text
q(x) = θx² / 2^{k+1},   b(x, y) = θxy / 2^k.
```

For odd `θ`, this is Nikulin's dyadic cyclic generator `q_θ^{(2)}(2^k)`. In the half-norm
convention it is the discriminant form of the `2`-adic lattice of rank one with Gram matrix
`(θ·2^k)`, and it is one of the generators of Nikulin's classification of nondegenerate finite
quadratic modules, alongside the odd-primary cyclic forms and the two forms `u^{(2)}(2^k)`,
`v^{(2)}(2^k)` on `(ℤ/2^k)²`. For even `θ`, it is the degenerate extension of the same formula.

This file constructs it from the cyclic presentation `TauCeti.FiniteQuadraticModule.cyclic`
and proves it nondegenerate exactly for odd `θ` (Nikulin, Proposition 1.8.1).

## Main declarations

* `TauCeti.FiniteQuadraticModule.dyadicCyclic`: the finite quadratic module `q_θ^{(2)}(2^k)`.
* `TauCeti.FiniteQuadraticModule.isNondegenerate_dyadicCyclic_iff`: it is nondegenerate exactly
  when `θ` is odd.
* `TauCeti.FiniteQuadraticModule.dyadicCyclicBilinearIsometryOfModEq`: coefficient congruence
  modulo `2^k` gives a bilinear isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8 for the
  generators, in particular Proposition 1.8.1.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

/-! ## The generator -/

section

variable (k : ℕ) [NeZero k] (θ : ℤ)

/-- The cyclic group `ℤ/2^k`, for `k ≥ 1`, with quadratic form `q(x) = θx² / 2^{k+1}` and
pairing `b(x, y) = θxy / 2^k`. For odd `θ`, this is **Nikulin's dyadic cyclic generator**
`q_θ^{(2)}(2^k)`, the discriminant form of the rank-one `2`-adic lattice with Gram matrix
`(θ·2^k)`. For even `θ`, it is the degenerate extension of the same formula. It is nondegenerate
exactly when `θ` is odd. -/
@[expose] noncomputable def dyadicCyclic : FiniteQuadraticModule :=
  cyclic (2 ^ k) (((θ / 2 ^ (k + 1) : ℚ)) : AddCircle (1 : ℚ))
    (by
      -- `(2^k)² · θ / 2^{k+1} = 2^{k-1}θ` is an integer because `k ≥ 1`.
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
      refine AddCircle.zsmul_coe_eq_zero (c := 2 ^ j * θ) ?_
      push_cast
      field_simp
      ring)
    (by
      refine AddCircle.zsmul_coe_eq_zero (c := θ) ?_
      push_cast
      field_simp
      ring)

/-- The quadratic form of `q_θ^{(2)}(2^k)` on the reduction of an integer `j` is
`θj² / 2^{k+1}`. -/
@[simp]
theorem dyadicCyclic_quadratic_intCast (j : ℤ) :
    (dyadicCyclic k θ).quadratic (j : ZMod (2 ^ k)) =
      ((θ * j ^ 2 / 2 ^ (k + 1) : ℚ) : AddCircle (1 : ℚ)) := by
  unfold dyadicCyclic
  rw [cyclic_quadratic, cyclicMap_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  push_cast
  ring_nf

/-- The pairing of `q_θ^{(2)}(2^k)` on the reductions of integers `i` and `j` is
`θij / 2^k`. -/
@[simp]
theorem dyadicCyclic_pairing_intCast (i j : ℤ) :
    (dyadicCyclic k θ).toFiniteBilinearModule.pairing (i : ZMod (2 ^ k)) (j : ZMod (2 ^ k)) =
      ((θ * i * j / 2 ^ k : ℚ) : AddCircle (1 : ℚ)) := by
  unfold dyadicCyclic
  rw [cyclic_pairing, polar_cyclicMap_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  congr 1
  push_cast
  field_simp
  ring

/-- **`q_θ^{(2)}(2^k)` is nondegenerate exactly when `θ` is odd.** For even `θ` the nonzero
element `2^{k-1}` lies in the radical. -/
@[simp]
theorem isNondegenerate_dyadicCyclic_iff : (dyadicCyclic k θ).IsNondegenerate ↔ Odd θ := by
  refine ⟨fun h ↦ ?_, fun hθ ↦ ?_⟩
  · by_contra hodd
    obtain ⟨s, rfl⟩ := Int.not_odd_iff_even.1 hodd
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne k)
    have hx : ((2 ^ j : ℤ) : ZMod (2 ^ (j + 1))) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hd
      push_cast at hd
      have hle := Int.le_of_dvd (by positivity) hd
      rw [pow_succ] at hle
      linarith [pow_pos (zero_lt_two : (0 : ℤ) < 2) j]
    have hpair : (dyadicCyclic (j + 1) (s + s)).toFiniteBilinearModule.pairing
        ((2 ^ j : ℤ) : ZMod (2 ^ (j + 1))) = 0 := by
      have hval : ∀ i : ℤ, (dyadicCyclic (j + 1) (s + s)).toFiniteBilinearModule.pairing
          ((2 ^ j : ℤ) : ZMod (2 ^ (j + 1))) (i : ZMod (2 ^ (j + 1))) = 0 := fun i ↦ by
        rw [dyadicCyclic_pairing_intCast]
        exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨s * i, by push_cast; field_simp; ring⟩
      refine AddMonoidHom.ext fun y ↦ ?_
      obtain ⟨i, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ (j + 1)) y
      -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
      exact hval i
    exact hx (FiniteBilinearModule.IsNondegenerate.injective _ h (hpair.trans (map_zero _).symm))
  · have hcop : IsCoprime ((2 : ℤ) ^ k) θ := by
      obtain ⟨t, rfl⟩ := hθ
      exact IsCoprime.pow_left ⟨-t, 1, by ring⟩
    refine (FiniteBilinearModule.isNondegenerate_iff_injective _).2
      ((injective_iff_map_eq_zero _).2 fun x hx ↦ ?_)
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) x
    have h : (dyadicCyclic k θ).toFiniteBilinearModule.pairing (j : ZMod (2 ^ k))
        ((1 : ℤ) : ZMod (2 ^ k)) = 0 :=
      -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
      DFunLike.congr_fun hx _
    rw [dyadicCyclic_pairing_intCast] at h
    -- The vanishing criterion takes an integer numerator and a natural denominator.
    have hdiv : (((θ * j : ℤ) : ℚ) / ((2 ^ k : ℕ) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      simpa only [Int.cast_mul, Int.cast_one, mul_one, Nat.cast_pow, Nat.cast_ofNat] using h
    rw [AddCircle.coe_intCast_div_natCast_eq_zero_iff (NeZero.ne _)] at hdiv
    push_cast at hdiv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd j (2 ^ k)).2
      (by exact_mod_cast hcop.dvd_of_dvd_mul_left hdiv)

end

/-- Congruent coefficients modulo `2^k` give cyclic bilinear forms related by the
identity on their cyclic group. The quadratic coefficient need only agree modulo
`2^k`, since this statement concerns the polar pairing. -/
noncomputable def dyadicCyclicBilinearIsometryOfModEq {k : ℕ} [NeZero k] {θ η : ℤ}
    (h : θ ≡ η [ZMOD (2 ^ k : ℕ)]) :
    FiniteBilinearModule.Isometry (dyadicCyclic k θ).toFiniteBilinearModule
      (dyadicCyclic k η).toFiniteBilinearModule := by
  let g : FiniteBilinearModule.Hom (dyadicCyclic k θ).toFiniteBilinearModule
      (dyadicCyclic k η).toFiniteBilinearModule :=
    { toAddMonoidHom := AddMonoidHom.id (ZMod (2 ^ k))
      map_pairing' := fun x y ↦ by
        -- Evaluate the identity homomorphism on the concrete cyclic carrier.
        change (dyadicCyclic k η).toFiniteBilinearModule.pairing x y =
          (dyadicCyclic k θ).toFiniteBilinearModule.pairing x y
        obtain ⟨a, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) x
        obtain ⟨b, rfl⟩ := ZMod.intCast_surjective (n := 2 ^ k) y
        rw [dyadicCyclic_pairing_intCast, dyadicCyclic_pairing_intCast]
        have hvalue (s : ℤ) :
            ((s * a * b / 2 ^ k : ℚ) : AddCircle (1 : ℚ)) =
              ZMod.toRatAddCircle (2 ^ k) ((s * a * b : ℤ) : ZMod (2 ^ k)) := by
          rw [ZMod.toRatAddCircle_intCast]
          simp only [Int.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [hvalue η, hvalue θ]
        congr 1
        push_cast
        rw [(ZMod.intCast_eq_intCast_iff η θ (2 ^ k)).mpr h.symm] }
  exact g.toIsometry (by exact Function.bijective_id)

end TauCeti.FiniteQuadraticModule
