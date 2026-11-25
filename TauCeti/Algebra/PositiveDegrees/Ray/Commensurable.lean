/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Ray.Basic

/-!
# Commensurable degrees on supported rays

In an additive group with unique division, an allowed degree lies on a supported ray if
a natural multiple of it equals a positive natural multiple of an actual ray degree.
Two allowed lattice vectors related by such an equation lie on a unique common supported
ray when the first is nonzero. In particular, this holds for two allowed positive multiples
of a nonzero vector, which can itself be outside the allowed monoid.

Adapted from `Mei/Algebra/PositiveDegrees/Ray/Commensurable.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti

variable {N : Type*} [AddCommGroup N] {d : PositiveDegrees N}

namespace SupportedRay

/-- In an additive group with unique division, a vector with a positive natural multiple on a
supported ray is a positive integer multiple of the primitive generator, regardless of its own
monoid membership. -/
theorem exists_pos_zsmul_generator_of_nsmul_mem_rayDegrees [HasUniqueDiv N]
    {w : SupportedRay d} {n : N} {p : ℕ} (h : p • n ∈ w.rayDegrees) :
    ∃ a : ℤ, 0 < a ∧ n = a • w.generator := by
  obtain ⟨-, b, hb, heq⟩ := mem_rayDegrees.mp h
  exact w.isPrimitive.exists_pos_zsmul_of_nsmul_eq_zsmul hb heq

/-- In an additive group with unique division, an allowed vector lies on a supported ray when
a natural multiple of it equals a positive natural multiple of an actual degree on that ray. -/
theorem mem_rayDegrees_of_nsmul_eq_nsmul [HasUniqueDiv N] {w : SupportedRay d}
    {n m : N} (hn : n ∈ w.rayDegrees) (hm : m ∈ d.monoid)
    {p q : ℕ} (hq : 0 < q) (h : p • m = q • n) : m ∈ w.rayDegrees := by
  have hm' : p • m ∈ w.rayDegrees := h ▸ nsmul_mem_rayDegrees hn hq
  exact mem_rayDegrees.mpr ⟨hm, exists_pos_zsmul_generator_of_nsmul_mem_rayDegrees hm'⟩

end SupportedRay

/-- Two allowed lattice vectors lie on a unique common supported ray when the first is nonzero
and a natural multiple of the second equals a positive natural multiple of the first. -/
theorem PositiveDegrees.existsUnique_supportedRay_of_nsmul_eq_nsmul [Module.Free ℤ N]
    (d : PositiveDegrees N) {x y : N} (hx : x ∈ d.monoid) (hy : y ∈ d.monoid)
    (hx0 : x ≠ 0) {p q : ℕ} (hq : 0 < q) (h : p • y = q • x) :
    ∃! w : SupportedRay d, x ∈ w.rayDegrees ∧ y ∈ w.rayDegrees := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  obtain ⟨w, hw⟩ := d.exists_supportedRay hx hx0
  have hw' := SupportedRay.mem_rayDegrees_of_nsmul_eq_nsmul hw hy hq h
  exact ⟨w, ⟨hw, hw'⟩, fun _ hv => SupportedRay.eq_of_mem_rayDegrees hv.1 hw⟩

/-- Two allowed positive multiples of a nonzero lattice vector lie on a unique common supported
ray, even if the original vector is outside the allowed monoid. -/
theorem PositiveDegrees.existsUnique_supportedRay_nsmul_mem_rayDegrees [Module.Free ℤ N]
    (d : PositiveDegrees N) {n : N} (hn : n ≠ 0) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpm : p • n ∈ d.monoid) (hqm : q • n ∈ d.monoid) :
    ∃! w : SupportedRay d, p • n ∈ w.rayDegrees ∧ q • n ∈ w.rayDegrees := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  exact d.existsUnique_supportedRay_of_nsmul_eq_nsmul hpm hqm (smul_ne_zero hp.ne' hn) hq
    (smul_comm p q n)

end TauCeti
