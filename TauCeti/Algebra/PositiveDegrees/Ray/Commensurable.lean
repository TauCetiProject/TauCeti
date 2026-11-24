/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Ray.Basic

/-!
# Commensurable degrees on supported rays

Positive natural multiples preserve the actual degrees of a supported ray. In an additive
group with unique division, an allowed degree with a positive multiple on the ray is itself
on that ray. In a free integer lattice this gives a unique common supported ray for any
two allowed positive multiples of a nonzero vector. The vector itself can fail to be allowed.

Adapted from `Mei/Algebra/PositiveDegrees/Ray/Commensurable.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti

variable {N : Type*} [AddCommGroup N] {d : PositiveDegrees N}

namespace SupportedRay

/-- A positive natural multiple of an actual ray degree remains an actual ray degree. -/
theorem nsmul_mem_rayDegrees {w : SupportedRay d} {n : N} (hn : n ∈ w.rayDegrees) {p : ℕ}
    (hp : 0 < p) : p • n ∈ w.rayDegrees := by
  obtain ⟨hmem, a, ha, rfl⟩ := mem_rayDegrees.mp hn
  refine mem_rayDegrees.mpr ⟨d.monoid.nsmul_mem hmem p, (p : ℤ) * a, mul_pos ?_ ha, ?_⟩
  · exact_mod_cast hp
  · rw [mul_smul, natCast_zsmul]

/-- If a positive multiple of a vector is an actual ray degree, then the vector is a positive
integer multiple of the primitive generator, regardless of its own monoid membership. -/
theorem exists_pos_zsmul_generator_of_nsmul_mem_rayDegrees [HasUniqueDiv N]
    {w : SupportedRay d} {n : N} {p : ℕ} (h : p • n ∈ w.rayDegrees) :
    ∃ a : ℤ, 0 < a ∧ n = a • w.generator := by
  have hp : p ≠ 0 := by
    rintro rfl
    exact w.zero_notMem_rayDegrees (by simpa only [zero_nsmul] using h)
  obtain ⟨-, b, hb, heq⟩ := mem_rayDegrees.mp h
  lift b to ℕ using hb.le
  rw [natCast_zsmul] at heq
  obtain ⟨a, ha⟩ := (w.isPrimitive.exists_eq_nsmul_iff_dvd b p).mp ⟨n, heq.symm⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [ha] at hb
  refine ⟨a, by exact_mod_cast Nat.pos_of_ne_zero ha0, ?_⟩
  rw [natCast_zsmul]
  apply nsmul_right_injective hp
  change p • n = p • (a • w.generator)
  rwa [smul_smul, ← ha]

/-- An allowed degree commensurable with an actual ray degree lies on the same ray. -/
theorem mem_rayDegrees_of_nsmul_eq_nsmul [HasUniqueDiv N] {w : SupportedRay d}
    {n m : N} (hn : n ∈ w.rayDegrees) (hm : m ∈ d.monoid)
    {p q : ℕ} (hq : 0 < q) (h : p • m = q • n) : m ∈ w.rayDegrees := by
  have hm' : p • m ∈ w.rayDegrees := h ▸ nsmul_mem_rayDegrees hn hq
  exact mem_rayDegrees.mpr ⟨hm, exists_pos_zsmul_generator_of_nsmul_mem_rayDegrees hm'⟩

end SupportedRay

/-- Two allowed positive multiples of a nonzero lattice vector lie on a unique common supported
ray, even if the original vector is outside the allowed monoid. -/
theorem PositiveDegrees.existsUnique_supportedRay_nsmul_mem_rayDegrees [Module.Free ℤ N]
    (d : PositiveDegrees N) {n : N} (hn : n ≠ 0) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hpm : p • n ∈ d.monoid) (hqm : q • n ∈ d.monoid) :
    ∃! w : SupportedRay d, p • n ∈ w.rayDegrees ∧ q • n ∈ w.rayDegrees := by
  let : HasUniqueDiv N := .of_isTorsionFree ℤ N
  obtain ⟨w, hw⟩ := d.exists_supportedRay hpm (smul_ne_zero hp.ne' hn)
  have hw' : q • n ∈ w.rayDegrees :=
    SupportedRay.mem_rayDegrees_of_nsmul_eq_nsmul hw hqm hq
      (by rw [smul_smul, smul_smul, mul_comm])
  exact ⟨w, ⟨hw, hw'⟩, fun _ hv => SupportedRay.eq_of_mem_rayDegrees hv.1 hw⟩

end TauCeti
