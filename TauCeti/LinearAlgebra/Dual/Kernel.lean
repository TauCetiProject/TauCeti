/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The kernel of a contracted pair of functionals

Contracting two linear functionals at a vector outside their common kernel
adds the line through that vector to the common kernel.

Adapted from `Mei/LinearAlgebra/Dual/Kernel.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The kernel of two functionals contracted at a vector outside their common kernel
is their common kernel plus the span of that vector. -/
theorem ker_apply_smul_sub_apply_smul (f g : V →ₗ[K] K) {v : V}
    (hv : v ∉ f.ker ⊓ g.ker) :
    (f v • g - g v • f).ker = (f.ker ⊓ g.ker) ⊔ K ∙ v := by
  have step (f g : V →ₗ[K] K) (hf : f v ≠ 0) :
      (f v • g - g v • f).ker ≤ (f.ker ⊓ g.ker) ⊔ K ∙ v := by
    intro x hx
    have he : f v * g x = g v * f x := by
      simpa only [mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        sub_eq_zero] using hx
    have hw : x - (f x / f v) • v ∈ f.ker ⊓ g.ker := by
      constructor
      · simp [mem_ker, hf]
      · apply mem_ker.mpr
        rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero, div_mul_eq_mul_div]
        exact (eq_div_iff hf).mpr (by simpa only [mul_comm] using he)
    have hl : (f x / f v) • v ∈ K ∙ v := Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self v)
    exact Submodule.mem_sup.mpr ⟨_, hw, _, hl, sub_add_cancel _ _⟩
  apply le_antisymm
  · by_cases hf : f v = 0
    · have hg : g v ≠ 0 := fun hg => hv ⟨hf, hg⟩
      intro x hx
      have hx' : x ∈ (g v • f - f v • g).ker := by
        have he := mem_ker.mp hx
        apply mem_ker.mpr
        simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] using
          (sub_eq_zero.mp he).symm
      simpa only [inf_comm] using step g f hg hx'
    · exact step f g hf
  · refine sup_le (fun x hx => ?_) (Submodule.span_le.mpr ?_)
    · apply mem_ker.mpr
      simp [mem_ker.mp hx.1, mem_ker.mp hx.2]
    · rintro x (rfl : x = v)
      simp [mem_ker, mul_comm]

end LinearMap
