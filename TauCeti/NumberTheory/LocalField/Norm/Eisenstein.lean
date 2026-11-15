/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.Quadratic
public import TauCeti.NumberTheory.LocalField.Norm.Quadratic
public import TauCeti.RingTheory.Norm.LocalRing

/-!
# Unit norms in an Eisenstein quadratic basis

Let `ω` be an integral root of `X² + t X + c`, with `t` in the maximal ideal and `c` a
uniformizer. In the maximal-order basis `(1, ω)`, the norm of `x + y ω` is
`x² - t x y + c y²`. It is a unit exactly when `x` is a unit, because its residue is `x²`.
Consequently the field norms of valuation zero have the single-family description
`u² (1 - t v + c v²)`, with `u ∈ 𝒪[K]ˣ` and `v ∈ 𝒪[K]`.

The coordinates belong to the full ring of integers. In particular this applies to ramified
quadratic extensions whose integral Eisenstein generator is a translated and scaled square
root, where the linear coefficient `t` need not vanish.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsQuadraticExtension K L]
  {t c : 𝒪[K]} {ω : 𝒪[L]}

/-- The norm in the maximal-order Eisenstein basis is `x² - t x y + c y²`. -/
theorem norm_eq_eisensteinQuadraticBasis (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0)
    (w : 𝒪[L]) :
    Algebra.norm K (w : L) =
      ((eisensteinQuadraticBasis ht hc hω).repr w 0 : K) ^ 2 -
        (t : K) * ((eisensteinQuadraticBasis ht hc hω).repr w 0 : K) *
          ((eisensteinQuadraticBasis ht hc hω).repr w 1 : K) +
        (c : K) * ((eisensteinQuadraticBasis ht hc hω).repr w 1 : K) ^ 2 := by
  have h := congrArg ((↑) : 𝒪[K] → K)
    ((eisensteinQuadraticBasis ht hc hω).norm_eq_of_apply_zero_eq_one
      (eisensteinQuadraticBasis_zero ht hc hω) w)
  simp only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow,
    coe_norm_integerRing, coe_trace_integerRing,
    trace_eisensteinQuadraticBasis_one ht hc hω,
    norm_eisensteinQuadraticBasis_one ht hc hω] at h
  rw [h]
  ring

/-- An integral element has unit norm in an Eisenstein quadratic extension exactly when its
first coordinate in the native maximal-order basis is a unit. -/
theorem isUnit_norm_iff_eisensteinQuadraticBasis_repr_zero
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0)
    (w : 𝒪[L]) :
    IsUnit (Algebra.norm 𝒪[K] w) ↔
      IsUnit ((eisensteinQuadraticBasis ht hc hω).repr w 0) := by
  have hT : Algebra.trace 𝒪[K] 𝒪[L] (eisensteinQuadraticBasis ht hc hω 1) = -t := by
    apply Subtype.val_injective
    simpa only [coe_trace_integerRing, Subring.coe_neg] using
      trace_eisensteinQuadraticBasis_one ht hc hω
  have hN : Algebra.norm 𝒪[K] (eisensteinQuadraticBasis ht hc hω 1) = c := by
    apply Subtype.val_injective
    simpa only [coe_norm_integerRing] using norm_eisensteinQuadraticBasis_one ht hc hω
  exact (eisensteinQuadraticBasis ht hc hω).isUnit_norm_iff_repr_zero_of_mem_maximalIdeal
    (eisensteinQuadraticBasis_zero ht hc hω) (by rw [hT]; exact neg_mem ht)
    (by rw [hN]; exact (mem_maximalIdeal c).mpr hc.not_isUnit) w

/-- The field norms of valuation zero in an Eisenstein quadratic extension are exactly
`u² (1 - t v + c v²)` with `u` an integral unit and `v` integral. -/
theorem exists_norm_eq_iff_of_eisensteinQuadraticBasis
    (ht : t ∈ 𝓂[K]) (hc : Irreducible c)
    (hω : ω ^ 2 + algebraMap 𝒪[K] 𝒪[L] t * ω + algebraMap 𝒪[K] 𝒪[L] c = 0)
    {b : K} (hb : valuation K b = 1) :
    (∃ z : L, Algebra.norm K z = b) ↔
      ∃ (u : 𝒪[K]ˣ) (v : 𝒪[K]),
        b = (u : K) ^ 2 * (1 - (t : K) * v + (c : K) * (v : K) ^ 2) := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  let B := eisensteinQuadraticBasis ht hc hω
  have hnorm (w : 𝒪[L]) : Algebra.norm K (w : L) =
      (B.repr w 0 : K) ^ 2 - (t : K) * (B.repr w 0 : K) * (B.repr w 1 : K) +
        (c : K) * (B.repr w 1 : K) ^ 2 := norm_eq_eisensteinQuadraticBasis ht hc hω w
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl, hunit⟩ := exists_integerRing_eq_and_isUnit_norm hb
    have hu : IsUnit (B.repr w 0) :=
      (isUnit_norm_iff_eisensteinQuadraticBasis_repr_zero ht hc hω w).mp hunit
    obtain ⟨u, hu⟩ := hu
    refine ⟨u, B.repr w 1 * ↑u⁻¹, ?_⟩
    rw [hnorm, ← hu]
    push_cast
    have hinv : (↑u⁻¹ : K) = (u : K)⁻¹ :=
      map_units_inv (Subring.subtype 𝒪[K]) u
    rw [hinv]
    have hu0 : (u : K) ≠ 0 := (u.isUnit.map (Subring.subtype 𝒪[K])).ne_zero
    field_simp
  · rintro ⟨u, v, rfl⟩
    apply (B.exists_norm_eq_iff_of_integerRing (eisensteinQuadraticBasis_zero ht hc hω)
      hb).mpr
    refine ⟨u, v, Or.inl ?_⟩
    rw [trace_eisensteinQuadraticBasis_one, norm_eisensteinQuadraticBasis_one]
    ring

end TauCeti
