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
  have : Algebra.IsQuadraticExtension 𝒪[K] 𝒪[L] :=
    ⟨by rw [Module.finrank_eq_card_basis B, Fintype.card_fin]⟩
  have hw : w = algebraMap 𝒪[K] 𝒪[L] (B.repr w 0) + algebraMap 𝒪[K] 𝒪[L] (B.repr w 1) * B 1 := by
    conv_lhs => rw [← B.sum_repr w]
    simp [Fin.sum_univ_two, hB, Algebra.smul_def, mul_comm]
  conv_lhs => rw [hw]
  rw [← coe_norm_integerRing, Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul,
    ← coe_trace_integerRing, ← coe_norm_integerRing]
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
  -- The integer with coordinates `v`, whose norm is the norm form at `v`.
  have hnorm (v : Fin 2 → 𝒪[K]) : Algebra.norm K (B.equivFun.symm v : L) =
      (v 0 : K) ^ 2 + v 0 * v 1 * Algebra.trace K L (B 1 : L) +
        (v 1 : K) ^ 2 * Algebra.norm K (B 1 : L) := by
    have hv (i : Fin 2) : B.repr (B.equivFun.symm v) i = v i := by
      rw [← B.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [norm_coe_eq_of_integerRing B hB, hv, hv]
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp [← hz] at hb
    -- A norm of valuation zero is the norm of a unit `w` of `𝒪[L]`.
    have hzv : valuation L z = 1 := by
      have hN : Algebra.normUnits K (Units.mk0 z hz0) ∈ unitFiltration K 0 := by
        rw [mem_unitFiltration_zero, Algebra.coe_normUnits, Units.val_mk0, hz, hb]
      simpa using (mem_unitFiltration_zero _).mp (normUnits_mem_unitFiltration_zero_iff.mp hN)
    obtain ⟨w, rfl⟩ : ∃ w : 𝒪[L], (w : L) = z :=
      ⟨⟨z, (Valuation.mem_integer_iff _ _).mpr hzv.le⟩, rfl⟩
    have hbw := norm_coe_eq_of_integerRing B hB w
    set x := B.repr w 0
    set y := B.repr w 1
    rw [hz, ← coe_trace_integerRing, ← coe_norm_integerRing] at hbw
    norm_cast at hbw
    have hunit : IsUnit (x ^ 2 + x * y * Algebra.trace 𝒪[K] 𝒪[L] (B 1) +
        y ^ 2 * Algebra.norm 𝒪[K] (B 1)) :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation K))).mpr (by rwa [hbw] at hb)
    -- One coordinate of `w` is a unit, since otherwise its norm lies in the maximal ideal.
    -- Dividing by that coordinate gives one of the two families.
    by_cases hx : IsUnit x
    · obtain ⟨u, hu⟩ := hx
      refine ⟨u, y * ↑u⁻¹, Or.inl ?_⟩
      have hy : y = y * ↑u⁻¹ * u := by simp [mul_assoc]
      generalize y * ↑u⁻¹ = t at hy ⊢
      rw [hbw, ← hu, hy, ← coe_trace_integerRing, ← coe_norm_integerRing]
      push_cast
      ring
    by_cases hy : IsUnit y
    · obtain ⟨u, hu⟩ := hy
      refine ⟨u, x * ↑u⁻¹, Or.inr ?_⟩
      have hx' : x = x * ↑u⁻¹ * u := by simp [mul_assoc]
      generalize x * ↑u⁻¹ = t at hx' ⊢
      rw [hbw, ← hu, hx', ← coe_trace_integerRing, ← coe_norm_integerRing]
      push_cast
      ring
    have hx' : x ∈ maximalIdeal 𝒪[K] := (mem_maximalIdeal x).mpr hx
    have hy' : y ∈ maximalIdeal 𝒪[K] := (mem_maximalIdeal y).mpr hy
    refine absurd hunit ((mem_maximalIdeal _).mp ?_)
    exact add_mem (add_mem (Ideal.pow_mem_of_mem _ hx' 2 two_pos)
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hx')))
      (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hy' 2 two_pos))
  · rintro ⟨u, t, h | h⟩
    · refine ⟨B.equivFun.symm ![(u : 𝒪[K]), u * t], ?_⟩
      rw [hnorm, h]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    · refine ⟨B.equivFun.symm ![u * t, (u : 𝒪[K])], ?_⟩
      rw [hnorm, h]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring

end Module.Basis
