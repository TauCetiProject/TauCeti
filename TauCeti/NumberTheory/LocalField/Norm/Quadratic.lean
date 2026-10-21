/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Basic
public import TauCeti.RingTheory.Norm.Quadratic

/-!
# Unit norms of a quadratic extension in an integral basis

Let `L/K` be a quadratic extension of nonarchimedean local fields, and let `(1, ω)` be a basis
of the ring of integers `𝒪[L]` over `𝒪[K]`. Put `T = Tr(ω)` and `N = N(ω)`. Both lie in
`𝒪[K]`, and the norm of `X + Y ω` is the binary form `X² + T X Y + N Y²`. This file shows that
the elements of `K` of valuation zero that are norms from `L` are exactly the elements

```text
u² (1 + T t + N t²)    and    u² (N + T t + t²),    u ∈ 𝒪[K]ˣ, t ∈ 𝒪[K]
```

of valuation zero: they are the norms of `u + u t ω` and of `u t + u ω`, and every norm of
valuation zero is the norm of a unit of `𝒪[L]` one of whose two coordinates is a unit.

The basis must be a basis of the maximal order `𝒪[L]`, not of a suborder such as
`𝒪[K][√a]`, which in residue characteristic two is in general strictly smaller. The theorem
holds in every residue characteristic and for ramified and unramified `L/K` alike. It reduces
the unit part of the norm group of `L/K` to the unit values of one binary quadratic form over
`𝒪[K]`, which is how the norm index of a quadratic extension is computed by hand. For a
uniformizer `a` the Eisenstein basis `(1, √a)` has `T = 0` and `N = -a`, and the first family is
the description `u² (1 - a t²)` of `TauCeti.mem_quadraticNormSubgroup_iff_of_isUniformizer`.

## Main results

* `Module.Basis.norm_coe_eq_of_integerRing`: the norm of an integer is the norm form of the
  basis `(1, ω)` at its coordinates.
* `Module.Basis.exists_norm_eq_iff_of_integerRing`: the unit norms are exactly the two
  families above.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace Module.Basis

/-- The binary form `x² + x y T + y² N` takes values in an ideal `I` at coordinates in `I`. -/
private lemma normForm_mem_of_mem {R : Type*} [CommRing R] {I : Ideal R} {x y : R} (hx : x ∈ I)
    (hy : y ∈ I) (T N : R) : x ^ 2 + x * y * T + y ^ 2 * N ∈ I := by
  rw [show x ^ 2 + x * y * T + y ^ 2 * N = x * (x + y * T) + y * (y * N) by ring]
  exact add_mem (I.mul_mem_right _ hx) (I.mul_mem_right _ hy)

/-- Dividing a binary form by the square of a unit coordinate `u`: the value
`p u² + T u y + q y²` is `u² (p + T t + q t²)` for `t = y u⁻¹`. -/
private lemma unit_sq_mul {R : Type*} [CommRing R] (u : Rˣ) (p q T y : R) :
    p * u ^ 2 + T * u * y + q * y ^ 2 = u ^ 2 * (p + T * (y * ↑u⁻¹) + q * (y * ↑u⁻¹) ^ 2) := by
  linear_combination (-(T * u * y) - q * y ^ 2 * (u * ↑u⁻¹ + 1)) * u.mul_inv

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **The norm form of an integral basis `(1, ω)`.** For a basis `B` of `𝒪[L]` over `𝒪[K]`
with `B 0 = 1` and `ω = B 1`, the field norm of `w = x + y ω ∈ 𝒪[L]` is
`x² + x y Tr(ω) + y² N(ω)`. -/
theorem norm_coe_eq_of_integerRing (B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L]) (hB : B 0 = 1)
    (w : 𝒪[L]) :
    Algebra.norm K (w : L) = (B.repr w 0 : K) ^ 2 +
      B.repr w 0 * B.repr w 1 * Algebra.trace K L (B 1 : L) +
        (B.repr w 1 : K) ^ 2 * Algebra.norm K (B 1 : L) := by
  rw [← coe_norm_integerRing, B.norm_eq_of_apply_zero_eq_one hB, ← coe_trace_integerRing,
    ← coe_norm_integerRing]
  push_cast
  ring

/-- **Unit norms in an integral basis** (O'Meara §63A). Let `B` be a basis of `𝒪[L]` over
`𝒪[K]` with `B 0 = 1`, and write `ω = B 1`, `T = Tr(ω)` and `N = N(ω)`. An element `b` of `K`
of valuation zero is a norm from `L` exactly when `b = u² (1 + T t + N t²)` or
`b = u² (N + T t + t²)` for a unit `u` and an element `t` of `𝒪[K]`. -/
theorem exists_norm_eq_iff_of_integerRing (B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L])
    (hB : B 0 = 1) {b : K} (hb : valuation K b = 1) :
    (∃ z : L, Algebra.norm K z = b) ↔
      ∃ (u : 𝒪[K]ˣ) (t : 𝒪[K]),
        b = (u : K) ^ 2 * (1 + Algebra.trace K L (B 1 : L) * t +
          Algebra.norm K (B 1 : L) * (t : K) ^ 2) ∨
        b = (u : K) ^ 2 * (Algebra.norm K (B 1 : L) + Algebra.trace K L (B 1 : L) * t +
          (t : K) ^ 2) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  -- Work with the trace `T` and norm `N` of `ω` in `𝒪[K]`.
  simp only [← coe_trace_integerRing, ← coe_norm_integerRing]
  set T := Algebra.trace 𝒪[K] 𝒪[L] (B 1)
  set N := Algebra.norm 𝒪[K] (B 1)
  constructor
  · rintro ⟨z, rfl⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hb
    -- A norm of valuation zero is the norm of a unit `w` of `𝒪[L]`.
    have hzv : valuation L z = 1 := by
      have hN : Algebra.normUnits K (Units.mk0 z hz0) ∈ unitFiltration K 0 := by
        rw [mem_unitFiltration_zero, Algebra.coe_normUnits, Units.val_mk0, hb]
      simpa using (mem_unitFiltration_zero _).mp (normUnits_mem_unitFiltration_zero_iff.mp hN)
    obtain ⟨w, rfl⟩ : ∃ w : 𝒪[L], (w : L) = z :=
      ⟨⟨z, (Valuation.mem_integer_iff _ _).mpr hzv.le⟩, rfl⟩
    rw [← coe_norm_integerRing] at hb ⊢
    have hunit : IsUnit (Algebra.norm 𝒪[K] w) :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation K))).mpr hb
    set x := B.repr w 0
    set y := B.repr w 1
    have hbw : Algebra.norm 𝒪[K] w = x ^ 2 + x * y * T + y ^ 2 * N :=
      B.norm_eq_of_apply_zero_eq_one hB w
    -- One coordinate of `w` is a unit, since otherwise its norm lies in the maximal ideal.
    -- Dividing by that coordinate gives one of the two families.
    by_cases hx : IsUnit x
    · obtain ⟨u, hu⟩ := hx
      rw [← hu] at hbw
      refine ⟨u, y * ↑u⁻¹, Or.inl ?_⟩
      exact_mod_cast (show Algebra.norm 𝒪[K] w =
          u ^ 2 * (1 + T * (y * ↑u⁻¹) + N * (y * ↑u⁻¹) ^ 2) by
        linear_combination hbw + unit_sq_mul u 1 N T y)
    by_cases hy : IsUnit y
    · obtain ⟨u, hu⟩ := hy
      rw [← hu] at hbw
      refine ⟨u, x * ↑u⁻¹, Or.inr ?_⟩
      exact_mod_cast (show Algebra.norm 𝒪[K] w =
          u ^ 2 * (N + T * (x * ↑u⁻¹) + (x * ↑u⁻¹) ^ 2) by
        linear_combination hbw + unit_sq_mul u N 1 T x)
    rw [hbw] at hunit
    exact absurd hunit ((mem_maximalIdeal _).mp (normForm_mem_of_mem
      ((mem_maximalIdeal x).mpr hx) ((mem_maximalIdeal y).mpr hy) T N))
  · -- The norms of `u + u t ω` and of `u t + u ω`.
    have hnorm (v : Fin 2 → 𝒪[K]) : Algebra.norm K (B.equivFun.symm v : L) =
        ((v 0 ^ 2 + v 0 * v 1 * T + v 1 ^ 2 * N : 𝒪[K]) : K) := by
      rw [B.norm_coe_eq_of_integerRing hB, ← coe_trace_integerRing, ← coe_norm_integerRing]
      simp only [← B.equivFun_apply, LinearEquiv.apply_symm_apply, T, N]
      push_cast
      ring
    rintro ⟨u, t, rfl | rfl⟩
    exacts [⟨B.equivFun.symm ![(u : 𝒪[K]), u * t], by rw [hnorm]; push_cast; ring⟩,
      ⟨B.equivFun.symm ![u * t, (u : 𝒪[K])], by rw [hnorm]; push_cast; ring⟩]

end Module.Basis
