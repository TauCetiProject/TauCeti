/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Cyclic

/-!
# The odd cyclic generators `q_θ^{(p)}(p^k)`

For an odd natural number `m` and an integer `θ`, this file constructs the cyclic group `ℤ/m`
with pairing and quadratic form

```text
b(x, y) = θxy / m,   q(x) = θ(m + 1)x² / (2m).
```

Since `m` is odd, `(m + 1) / 2` is an integer inverse of `2` modulo `m`, so `2q(x) = b(x, x)` and
`q` takes values in the `m`-torsion of `ℚ/ℤ`. It is the only quadratic form on `ℤ/m` with polar
form `b`, because two such forms differ by an additive map `d` with `2d = 0`, and `2` is invertible
on a group of odd order. The naive half-norm `θx² / (2m)` is not well defined modulo `m` when `θ` is
odd, and the factor `m + 1` repairs it without changing the pairing.

For an odd prime `p`, `k ≥ 1` and `θ` prime to `p`, the module on `ℤ/p^k` is **Nikulin's odd
cyclic generator** `q_θ^{(p)}(p^k)`, the discriminant form of the rank-one `p`-adic lattice with
Gram matrix `(θ·p^k)`. (The natural generator of that discriminant group has pairing value
`θ⁻¹/p^k`, and `θ⁻¹ = θ·(θ⁻¹)²` lies in the square class of `θ`.) Nikulin's classification of
nondegenerate finite quadratic modules writes the odd-primary part of every such module as an
orthogonal sum of these. The form is nondegenerate exactly when `θ` is prime to `m`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.oddCyclic`: the finite quadratic module on `ℤ/m`, `m` odd, with
  pairing `θxy / m`.
* `TauCeti.FiniteQuadraticModule.oddCyclic_quadratic_intCast` and
  `TauCeti.FiniteQuadraticModule.oddCyclic_pairing_intCast`: its values on integers.
* `TauCeti.FiniteQuadraticModule.isNondegenerate_oddCyclic_iff`: it is nondegenerate exactly when
  `m` and `θ` are coprime.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8 for the
  generators, in particular Proposition 1.8.1.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

variable (m : ℕ) (hm : Odd m) (θ : ℤ)

/-- The cyclic group `ℤ/m`, for odd `m`, with pairing `b(x, y) = θxy / m` and quadratic form
`q(x) = θ(m + 1)x² / (2m)`, the unique quadratic form with polar `b`. For `m = p^k` with `p` an odd
prime, `k ≥ 1` and `θ` prime to `p`, this is **Nikulin's odd cyclic generator**
`q_θ^{(p)}(p^k)`, the discriminant form of the rank-one `p`-adic lattice with Gram matrix
`(θ·p^k)`. It is nondegenerate exactly when `θ` is prime to `m`. -/
@[expose] noncomputable def oddCyclic : FiniteQuadraticModule :=
  haveI : NeZero m := ⟨hm.pos.ne'⟩
  cyclic m (((θ * (m + 1) / (2 * m) : ℚ)) : AddCircle (1 : ℚ))
    (by
      -- `m² · θ(m + 1) / (2m) = θm(t + 1)` for `m = 2t + 1`.
      obtain ⟨t, rfl⟩ := hm
      refine AddCircle.zsmul_coe_eq_zero (c := θ * (2 * t + 1) * (t + 1)) ?_
      push_cast
      field_simp
      ring)
    (by
      refine AddCircle.zsmul_coe_eq_zero (c := θ * (m + 1)) ?_
      have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.pos.ne'
      push_cast
      field_simp)

/-- The quadratic form of `oddCyclic m hm θ` on the reduction of an integer `j` is
`θ(m + 1)j² / (2m)`. -/
@[simp]
theorem oddCyclic_quadratic_intCast (j : ℤ) :
    (oddCyclic m hm θ).quadratic (j : ZMod m) =
      ((θ * (m + 1) * j ^ 2 / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  unfold oddCyclic
  rw [cyclic_quadratic, cyclicMap_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul]
  push_cast
  ring_nf

/-- The pairing of `oddCyclic m hm θ` on the reductions of integers `i` and `j` is `θij / m`. -/
@[simp]
theorem oddCyclic_pairing_intCast (i j : ℤ) :
    (oddCyclic m hm θ).toFiniteBilinearModule.pairing (i : ZMod m) (j : ZMod m) =
      ((θ * i * j / m : ℚ) : AddCircle (1 : ℚ)) := by
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.pos.ne'
  unfold oddCyclic
  rw [cyclic_pairing, polar_cyclicMap_intCast, ← AddCircle.coe_zsmul, zsmul_eq_mul, ← sub_eq_zero,
    ← AddCircle.coe_sub]
  -- The two representatives differ by the integer `θij`.
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨θ * i * j, by push_cast; field_simp; ring⟩

/-- The odd cyclic pairing is multiplication of residue classes followed by the rational-circle
character. -/
@[simp low]
theorem oddCyclic_pairing (x y : ZMod m) :
    (oddCyclic m hm θ).toFiniteBilinearModule.pairing x y =
      ZMod.toRatAddCircle m ((θ : ZMod m) * x * y) := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective y
  rw [oddCyclic_pairing_intCast]
  simpa only [Int.cast_mul] using (ZMod.toRatAddCircle_intCast m (θ * i * j)).symm

/-- The odd cyclic quadratic form is the rational-circle character of `θx²/2`, with division
by `2` performed using its integer inverse `(m + 1) / 2` modulo `m`. -/
@[simp low]
theorem oddCyclic_quadratic (x : ZMod m) :
    (oddCyclic m hm θ).quadratic x =
      ZMod.toRatAddCircle m ((θ : ZMod m) * (((m + 1) / 2 : ℕ) : ZMod m) * x ^ 2) := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective x
  have hhalf : 2 * ((m + 1) / 2) = m + 1 := by
    obtain ⟨k, rfl⟩ := hm
    omega
  have hhalfq : 2 * (((m + 1) / 2 : ℕ) : ℚ) = m + 1 := by
    exact_mod_cast hhalf
  have hr := ZMod.toRatAddCircle_intCast m (θ * (((m + 1) / 2 : ℕ) : ℤ) * j ^ 2)
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow] at hr
  rw [oddCyclic_quadratic_intCast, hr]
  congr 1
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.pos.ne'
  field_simp
  rw [← hhalfq]
  ring

/-- **`oddCyclic m hm θ` is nondegenerate exactly when `θ` is prime to `m`.** If `d > 1` divides
both, the nonzero element `m / d` lies in the radical. -/
@[simp]
theorem isNondegenerate_oddCyclic_iff :
    (oddCyclic m hm θ).IsNondegenerate ↔ IsCoprime (m : ℤ) θ := by
  have hm0 : (m : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hm.pos.ne'
  refine ⟨fun h ↦ ?_, fun hθ ↦ ?_⟩
  · -- Write `m = dm'` and `θ = dθ'` with `d = gcd(m, θ)`; then `m'` pairs integrally with all.
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hd
    obtain ⟨m', hm'⟩ := Int.gcd_dvd_left (m : ℤ) θ
    obtain ⟨θ', hθ'⟩ := Int.gcd_dvd_right (m : ℤ) θ
    set d := Int.gcd (m : ℤ) θ
    have hd0 : (d : ℤ) ≠ 0 := by
      intro h0
      exact hm0 (by rw [hm', h0, zero_mul])
    have hm'pos : 0 < m' := by
      have : 0 < (d : ℤ) * m' := by rw [← hm']; exact_mod_cast hm.pos
      exact pos_of_mul_pos_right this (by positivity)
    have hx : ((m' : ℤ) : ZMod m) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hdvd
      have hle := Int.le_of_dvd hm'pos hdvd
      have hd2 : (2 : ℤ) ≤ d := by
        have : (d : ℤ) ≠ 1 := by exact_mod_cast hd
        omega
      nlinarith
    have hval : ∀ i : ℤ, (oddCyclic m hm θ).toFiniteBilinearModule.pairing
        ((m' : ℤ) : ZMod m) (i : ZMod m) = 0 := fun i ↦ by
      rw [oddCyclic_pairing_intCast]
      have hmq : (m : ℚ) = (d : ℚ) * m' := by exact_mod_cast hm'
      have hθq : (θ : ℚ) = (d : ℚ) * θ' := by exact_mod_cast hθ'
      have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
      have hm'q : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'pos.ne'
      exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨θ' * i, by
        rw [hmq, hθq, zsmul_eq_mul]; push_cast; field_simp⟩
    have hpair : (oddCyclic m hm θ).toFiniteBilinearModule.pairing ((m' : ℤ) : ZMod m) = 0 := by
      refine AddMonoidHom.ext fun y ↦ ?_
      obtain ⟨i, rfl⟩ := ZMod.intCast_surjective (n := m) y
      -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
      exact hval i
    exact hx (FiniteBilinearModule.IsNondegenerate.injective _ h (hpair.trans (map_zero _).symm))
  · refine (FiniteBilinearModule.isNondegenerate_iff_injective _).2
      ((injective_iff_map_eq_zero _).2 fun x hx ↦ ?_)
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective (n := m) x
    have h : (oddCyclic m hm θ).toFiniteBilinearModule.pairing (j : ZMod m)
        ((1 : ℤ) : ZMod m) = 0 :=
      -- The zero character evaluates to `0`; `AddMonoidHom.zero_apply` holds by `rfl`.
      DFunLike.congr_fun hx _
    rw [oddCyclic_pairing_intCast] at h
    -- The vanishing criterion takes an integer numerator and a natural denominator.
    have hdiv : (((θ * j : ℤ) : ℚ) / (m : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      simpa only [Int.cast_mul, Int.cast_one, mul_one] using h
    rw [AddCircle.coe_intCast_div_natCast_eq_zero_iff hm.pos.ne'] at hdiv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd j m).2 (hθ.dvd_of_dvd_mul_left hdiv)

end TauCeti.FiniteQuadraticModule
