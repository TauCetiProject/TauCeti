/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Determinants of endomorphisms trivial modulo a line

If every difference `v - f v` lies in the line spanned by a nonzero vector `x`, then
`f x = det(f) • x`. Thus the determinant character is the normal character for the
action on polynomial functions of an element fixing a hyperplane pointwise.

The calculation uses the rank-one instance of the Weinstein–Aronszajn identity
`LinearMap.det_one_add_comp_comm`.
-/

public section

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If an endomorphism is the identity modulo a line, its action on that line is
multiplication by its determinant. -/
theorem apply_eq_det_smul_of_sub_mem_span (f : V →ₗ[K] V) {x : V} (hx : x ≠ 0)
    (hf : ∀ v, v - f v ∈ K ∙ x) : f x = LinearMap.det f • x := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hx
  let ψ := φ.comp (f - 1)
  have hfx (v : V) : f v - v = ψ v • x := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hf v)
    have hv : f v - v = -c • x := by rw [neg_smul, hc, neg_sub]
    simp only [ψ, LinearMap.comp_apply, LinearMap.sub_apply, one_apply_eq_self, hv,
      map_smul, hφ, smul_eq_mul, mul_one]
  have hrepr : f = 1 + (LinearMap.toSpanSingleton K V x).comp ψ := by
    ext v
    rw [LinearMap.add_apply, one_apply_eq_self, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply]
    rw [← hfx v, add_sub_cancel]
  have hd : LinearMap.det f = 1 + ψ x := by
    rw [hrepr, det_one_add_comp_comm]
    simp
  rw [hd, add_smul, one_smul, ← hfx x, add_sub_cancel]

end LinearMap
