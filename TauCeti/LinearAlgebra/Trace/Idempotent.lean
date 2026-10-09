/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace

import TauCeti.LinearAlgebra.Trace.Exchange

import Mathlib.LinearAlgebra.PID

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# The trace of an endomorphism whose square is a multiple of itself

An endomorphism `f` of a finite-dimensional vector space satisfying `f * f = a • f` is a scaled
projection: when `a ≠ 0` the endomorphism `a⁻¹ • f` is idempotent with the same range as `f`, so
the trace of `f` is `a` times the dimension of that range. The degenerate case `a = 0` obeys the
same formula, because then `f` squares to zero, hence is nilpotent and traceless.

This is the standard device for pinning down the scalar in an *essential idempotence* identity
`c * c = a • c` in a finite-dimensional algebra: compute the trace of multiplication by `c` in
two ways, once from the identity and once from a basis. Mathlib has the idempotent case
(`LinearMap.IsProj.trace`, together with `IsIdempotentElem.isProj_range`); this file removes the
normalisation, which is exactly what makes the identity usable when the scalar is the unknown.

## Main statements

* `TauCeti.LinearMap.trace_mul_eq_mul_trace_restrict_range`: if `c * c = a • c` and `f` commutes
  with `c`, then `trace (c * f) = a * trace (f|range c)`. Taking `c` to be the action of a
  quasi-idempotent of a group algebra computes the character of its image.
* `TauCeti.LinearMap.trace_mul_add_mul_trace_restrict_ker`: the complementary kernel character
  formula `trace (c * f) + a * trace (f|ker c) = a * trace f`, including `a = 0`.
* `TauCeti.LinearMap.two_mul_trace_restrict_ker_one_add`,
  `TauCeti.LinearMap.three_mul_trace_restrict_ker_one_add_add_sq`: character formulas for the
  kernels of the order-two and order-three averaging operators.
* `TauCeti.LinearMap.trace_eq_mul_finrank_range`: if `f * f = a • f`, then
  `trace f = a * finrank (range f)`, the case `f = 1` of the previous statement.
* `TauCeti.LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one`: for an involution `σ`,
  `2 dim ker (1 + σ) = dim M - tr σ`, applying the above to `f = 1 + σ`, whose square is `2 f`.
* `TauCeti.LinearMap.three_mul_finrank_ker_one_add_add_sq_of_pow_three_eq_one`: for `υ ^ 3 = 1`,
  `3 dim ker (1 + υ + υ²) = 2 dim M - tr υ - tr υ²`, applying it to `f = 1 + υ + υ²`, whose square
  is `3 f`.

These two dimension formulas need no hypothesis on the characteristic: when `2`, respectively `3`,
vanishes in `K`, the essentially idempotent `f` is nilpotent and both sides are zero.
-/

public section

namespace TauCeti

open Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- **The trace of a map commuting with an essentially idempotent endomorphism.** If the square
of `c` is `a • c` and `f` commutes with `c`, so that `f` preserves the range of `c`, then the trace
of `c * f` is `a` times the trace of `f` on the range of `c`.

For `a ≠ 0` this says that `a⁻¹ • c` is a projection onto `range c` commuting with `f`; for
`a = 0` both sides vanish, because `c * f` then squares to zero. -/
theorem LinearMap.trace_mul_eq_mul_trace_restrict_range {c f : Module.End K M} {a : K}
    (hc : c * c = a • c) (hcf : Commute c f)
    (hf : ∀ x ∈ _root_.LinearMap.range c, f x ∈ _root_.LinearMap.range c :=
      fun _ ⟨y, hy⟩ => ⟨f y, by rw [← hy, ← Module.End.mul_apply, hcf.eq, Module.End.mul_apply]⟩) :
    _root_.LinearMap.trace K M (c * f) =
      a * _root_.LinearMap.trace K (_root_.LinearMap.range c) (f.restrict hf) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_mul]
    refine IsNilpotent.eq_zero (_root_.LinearMap.isNilpotent_trace_of_isNilpotent ⟨2, ?_⟩)
    rw [pow_two, hcf.symm.mul_mul_mul_comm, hc, zero_smul, zero_mul]
  · -- `a⁻¹ • c` fixes the range of `c` pointwise, so on that range `a⁻¹ • c * f` is `f`
    have hfix : ∀ x ∈ _root_.LinearMap.range c, (a⁻¹ • c) x = x := fun _ ⟨y, hy⟩ => by
      rw [← hy, LinearMap.smul_apply, ← Module.End.mul_apply, hc, LinearMap.smul_apply, smul_smul,
        inv_mul_cancel₀ ha, one_smul]
    have hmem : ∀ x, (a⁻¹ • c * f) x ∈ _root_.LinearMap.range c := fun x =>
      ⟨a⁻¹ • f x, by rw [map_smul, Module.End.mul_apply, LinearMap.smul_apply]⟩
    have hres : (a⁻¹ • c * f).restrict (fun x _ => hmem x) = f.restrict hf :=
      LinearMap.ext fun x => Subtype.ext <| by
        rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, Module.End.mul_apply,
          hfix _ (hf x x.2)]
    have htrace := _root_.LinearMap.trace_restrict_eq_of_forall_mem _ (a⁻¹ • c * f) hmem
    rw [hres, smul_mul_assoc, map_smul, smul_eq_mul] at htrace
    rw [htrace, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- If `c² = a c` and `c` commutes with `f`, then `tr(c f) + a tr(f|ker c) = a tr(f)`.
This computes the character of the kernel of a scaled projection without choosing a complement.
The identity also holds when `a = 0`. -/
theorem LinearMap.trace_mul_add_mul_trace_restrict_ker {c f : Module.End K M} {a : K}
    (hc : c * c = a • c) (hcf : Commute c f)
    (hf : ∀ x ∈ _root_.LinearMap.ker c, f x ∈ _root_.LinearMap.ker c := fun x hx ↦ by
      rw [_root_.LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcf.eq, Module.End.mul_apply, hx, map_zero]) :
    _root_.LinearMap.trace K M (c * f) +
      a * _root_.LinearMap.trace K (_root_.LinearMap.ker c) (f.restrict hf) =
        a * _root_.LinearMap.trace K M f := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using trace_mul_eq_mul_trace_restrict_range hc hcf
  let d := a • (1 : Module.End K M) - c
  have hd : d * d = a • d := by
    dsimp [d]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      hc, smul_sub, smul_smul]
    abel
  have hdf : Commute d f := (Commute.one_left f).smul_left a |>.sub_left hcf
  have hr : _root_.LinearMap.range d = _root_.LinearMap.ker c := by
    apply le_antisymm
    · rw [_root_.LinearMap.range_le_ker_iff]
      dsimp [d]
      rw [← Module.End.mul_eq_comp, mul_sub, mul_smul_comm, mul_one, hc, sub_self]
    · intro x hx
      refine ⟨a⁻¹ • x, ?_⟩
      simp [d, _root_.LinearMap.mem_ker.mp hx, smul_smul, ha]
  have h := trace_mul_eq_mul_trace_restrict_range hd hdf
  rw [_root_.LinearMap.trace_restrict_congr hr _ _ hf] at h
  dsimp [d] at h
  rw [sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul, smul_eq_mul] at h
  linear_combination -h

/-- For an involution `σ` commuting with `f`, twice the trace of `f` on its negative eigenspace
equals `tr f - tr(σ f)`. -/
theorem LinearMap.two_mul_trace_restrict_ker_one_add {σ f : End K M} (hσ : σ ^ 2 = 1)
    (hσf : Commute σ f)
    (hf : ∀ x ∈ _root_.LinearMap.ker (1 + σ), f x ∈ _root_.LinearMap.ker (1 + σ) :=
      fun x hx ↦ by
        rw [_root_.LinearMap.mem_ker] at hx ⊢
        rw [← Module.End.mul_apply, ((Commute.one_left f).add_left hσf).eq,
          Module.End.mul_apply, hx, map_zero]) :
    2 * _root_.LinearMap.trace K (_root_.LinearMap.ker (1 + σ)) (f.restrict hf) =
      _root_.LinearMap.trace K M f - _root_.LinearMap.trace K M (σ * f) := by
  have hc : (1 + σ) * (1 + σ) = (2 : K) • (1 + σ) := by
    rw [Algebra.smul_def, map_ofNat]
    linear_combination (norm := noncomm_ring) hσ
  have h := trace_mul_add_mul_trace_restrict_ker hc ((Commute.one_left f).add_left hσf) hf
  rw [add_mul, one_mul, map_add] at h
  linear_combination h

/-- If the order-three averaging operator `1 + υ + υ²` commutes with `f`, three times the trace
of `f` on its kernel equals `2 tr f - tr(υ f) - tr(υ² f)`. -/
theorem LinearMap.three_mul_trace_restrict_ker_one_add_add_sq {υ f : End K M}
    (hυ : υ ^ 3 = 1) (hcf : Commute (1 + υ + υ ^ 2) f)
    (hf : ∀ x ∈ _root_.LinearMap.ker (1 + υ + υ ^ 2), f x ∈
      _root_.LinearMap.ker (1 + υ + υ ^ 2) := fun x hx ↦ by
        rw [_root_.LinearMap.mem_ker] at hx ⊢
        rw [← Module.End.mul_apply, hcf.eq, Module.End.mul_apply, hx, map_zero]) :
    3 * _root_.LinearMap.trace K (_root_.LinearMap.ker (1 + υ + υ ^ 2)) (f.restrict hf) =
      2 * _root_.LinearMap.trace K M f - _root_.LinearMap.trace K M (υ * f) -
        _root_.LinearMap.trace K M (υ ^ 2 * f) := by
  have hc : (1 + υ + υ ^ 2) * (1 + υ + υ ^ 2) = (3 : K) • (1 + υ + υ ^ 2) := by
    rw [Algebra.smul_def, map_ofNat]
    linear_combination (norm := noncomm_ring) 2 * hυ + υ * hυ
  have h := trace_mul_add_mul_trace_restrict_ker hc hcf hf
  rw [add_mul, add_mul, one_mul, map_add, map_add] at h
  linear_combination h

/-- **The trace of an essentially idempotent endomorphism.** If the square of `f` is `a • f`,
then the trace of `f` is `a` times the dimension of the range of `f`.

For `a ≠ 0` this says that `a⁻¹ • f` is a projection onto `range f`; for `a = 0` both sides
vanish, because `f` then squares to zero. -/
theorem LinearMap.trace_eq_mul_finrank_range {f : M →ₗ[K] M} {a : K} (hf : f * f = a • f) :
    _root_.LinearMap.trace K M f = a * (finrank K (_root_.LinearMap.range f) : K) := by
  have h := trace_mul_eq_mul_trace_restrict_range hf (Commute.one_right f)
  have hone : ∀ h : ∀ x ∈ _root_.LinearMap.range f, (1 : Module.End K M) x ∈
      _root_.LinearMap.range f, (1 : Module.End K M).restrict h = 1 := fun _ =>
    LinearMap.ext fun x => Subtype.ext <| by
      rw [LinearMap.coe_restrict_apply, Module.End.one_apply, Module.End.one_apply]
  rwa [mul_one, hone, _root_.LinearMap.trace_one] at h

/-- **The trace of an involution determines its `-1`-eigenspace**: if `σ ^ 2 = 1`, then
`2 dim ker (1 + σ) = dim M - tr σ` in `K`. -/
theorem LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one {σ : End K M} (hσ : σ ^ 2 = 1) :
    2 * (finrank K (_root_.LinearMap.ker (1 + σ)) : K) =
      finrank K M - _root_.LinearMap.trace K M σ := by
  have h := two_mul_trace_restrict_ker_one_add hσ (Commute.one_right σ) (fun _ hx ↦ hx)
  have hres : (1 : End K M).restrict (fun _ hx ↦ hx) =
      (1 : End K (_root_.LinearMap.ker (1 + σ))) := rfl
  simpa only [hres, _root_.LinearMap.trace_one, mul_one] using h

/-- **The traces of an order-three map determine the kernel of `1 + υ + υ²`**: if `υ ^ 3 = 1`,
then `3 dim ker (1 + υ + υ²) = 2 dim M - tr υ - tr υ²` in `K`. -/
theorem LinearMap.three_mul_finrank_ker_one_add_add_sq_of_pow_three_eq_one {υ : End K M}
    (hυ : υ ^ 3 = 1) :
    3 * (finrank K (_root_.LinearMap.ker (1 + υ + υ ^ 2)) : K) =
      2 * finrank K M - _root_.LinearMap.trace K M υ - _root_.LinearMap.trace K M (υ ^ 2) := by
  have h := three_mul_trace_restrict_ker_one_add_add_sq hυ
    (Commute.one_right _) (fun _ hx ↦ hx)
  have hres : (1 : End K M).restrict (fun _ hx ↦ hx) =
      (1 : End K (_root_.LinearMap.ker (1 + υ + υ ^ 2))) := rfl
  simpa only [hres, _root_.LinearMap.trace_one, mul_one] using h

end TauCeti
