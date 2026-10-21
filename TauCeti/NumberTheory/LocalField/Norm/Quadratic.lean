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

* `Module.Basis.exists_norm_eq_iff_of_integerRing`: the unit norms are exactly the two
  families above.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

open ValuativeRel IsLocalRing TauCeti

namespace Module.Basis

/-- Dividing a binary form by the square of a unit coordinate `u`: the value
`p u² + T u y + q y²` is `u² (p + T t + q t²)` for `t = y u⁻¹`. -/
private lemma unit_sq_mul {R : Type*} [CommRing R] (u : Rˣ) (p q T y : R) :
    p * u ^ 2 + T * u * y + q * y ^ 2 = u ^ 2 * (p + T * (y * ↑u⁻¹) + q * (y * ↑u⁻¹) ^ 2) := by
  linear_combination (-(T * u * y) - q * y ^ 2 * (u * ↑u⁻¹ + 1)) * u.mul_inv

/-- A unit value of the binary form `x² + x y T + y² N` over a local ring lies in one of the
families `u² (1 + T t + N t²)` and `u² (N + T t + t²)`. One of `x` and `y` is a unit, since
otherwise the value lies in the maximal ideal, and dividing by its square gives the family. -/
private lemma exists_eq_of_isUnit_normForm {R : Type*} [CommRing R] [IsLocalRing R] {x y : R}
    (T N : R) (h : IsUnit (x ^ 2 + x * y * T + y ^ 2 * N)) :
    ∃ (u : Rˣ) (t : R), x ^ 2 + x * y * T + y ^ 2 * N = u ^ 2 * (1 + T * t + N * t ^ 2) ∨
      x ^ 2 + x * y * T + y ^ 2 * N = u ^ 2 * (N + T * t + t ^ 2) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    exact ⟨u, y * ↑u⁻¹, Or.inl (by linear_combination unit_sq_mul u 1 N T y)⟩
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    exact ⟨u, x * ↑u⁻¹, Or.inr (by linear_combination unit_sq_mul u N 1 T x)⟩
  refine absurd h ((mem_maximalIdeal _).mp ?_)
  rw [show x ^ 2 + x * y * T + y ^ 2 * N = x * (x + y * T) + y * (y * N) by ring]
  exact add_mem (Ideal.mul_mem_right _ _ ((mem_maximalIdeal x).mpr hx))
    (Ideal.mul_mem_right _ _ ((mem_maximalIdeal y).mpr hy))

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

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
    -- A norm of valuation zero is the norm of a unit `w` of `𝒪[L]`.
    obtain ⟨w, rfl⟩ : ∃ w : 𝒪[L], (w : L) = z :=
      ⟨⟨z, (Valuation.mem_integer_iff _ _).mpr (valuation_norm_eq_one_iff.mp hb).le⟩, rfl⟩
    rw [← coe_norm_integerRing] at hb ⊢
    have hunit : IsUnit (Algebra.norm 𝒪[K] w) :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation K))).mpr hb
    rw [B.norm_eq_of_apply_zero_eq_one hB w] at hunit ⊢
    obtain ⟨u, t, h | h⟩ := exists_eq_of_isUnit_normForm T N hunit
    exacts [⟨u, t, Or.inl (by exact_mod_cast h)⟩, ⟨u, t, Or.inr (by exact_mod_cast h)⟩]
  · -- The norms of `u + u t ω` and of `u t + u ω`.
    have hnorm (v : Fin 2 → 𝒪[K]) : Algebra.norm K (B.equivFun.symm v : L) =
        ((v 0 ^ 2 + v 0 * v 1 * T + v 1 ^ 2 * N : 𝒪[K]) : K) := by
      rw [← coe_norm_integerRing, B.norm_eq_of_apply_zero_eq_one hB]
      simp only [← B.equivFun_apply, LinearEquiv.apply_symm_apply, T, N]
    rintro ⟨u, t, rfl | rfl⟩
    exacts [⟨B.equivFun.symm ![(u : 𝒪[K]), u * t], by rw [hnorm]; push_cast; ring⟩,
      ⟨B.equivFun.symm ![u * t, (u : 𝒪[K])], by rw [hnorm]; push_cast; ring⟩]

end Module.Basis
