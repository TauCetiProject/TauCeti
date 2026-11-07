/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Top-degree alternating forms and hyperplanes

Let `V` be a vector space of dimension `n + 1`, let `f` be a covector and `v` a vector with
`f v = 1`, so that `V = K v ⊕ ker f`. A top-degree alternating form `ω` on `V` is determined by
the interior product `ι_v ω` restricted to the hyperplane `ker f`: a basis `b` of `ker f` extends
to the basis `(v, b₀, …, b_(n-1))` of `V`, on which `ω` takes the value `(ι_v ω)(b)`. Hence `ω`
vanishes exactly when this restriction does
(`AlternatingMap.curryLeft_compLinearMap_subtype_eq_zero_iff`). For a nonzero vector `v`
some covector takes the value `1` at `v`, so a top-degree form `ω` with `ι_v ω = 0` vanishes
(`AlternatingMap.eq_zero_of_curryLeft_eq_zero`).

These are the steps from a top wedge power to nondegeneracy: a two-form with a nonzero vector in
its kernel has vanishing top power, and the top-degree form `α ∧ (dα)ⁿ` on a space of dimension
`2 n + 1` is determined by `(dα)ⁿ` on the hyperplane `ker α`.
-/

public section

open Module

namespace AlternatingMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ}

/-- **A top-degree form is determined by an interior product on a hyperplane.** On a space of
dimension `n + 1`, let `f v = 1`. A top-degree alternating form `ω` vanishes exactly when the
interior product `ι_v ω` vanishes on the hyperplane `ker f`. -/
theorem curryLeft_compLinearMap_subtype_eq_zero_iff (hn : finrank K V = n + 1)
    (ω : V [⋀^Fin (n + 1)]→ₗ[K] K) {f : Dual K V} {v : V} (hv : f v = 1) :
    (ω.curryLeft v).compLinearMap (LinearMap.ker f).subtype = 0 ↔ ω = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, zero_compLinearMap]⟩
  have hf : f ≠ 0 := fun hf ↦ by simp [hf] at hv
  have hker : finrank K (LinearMap.ker f) = n := by
    have := Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  -- A basis of `ker f`, extended by `v` to a basis of `V`.
  set b := Module.finBasisOfFinrankEq K (LinearMap.ker f) hker
  set c := Basis.mkFinCons v b
    (fun a x hx hax ↦ by simpa [hv, LinearMap.mem_ker.1 hx] using congrArg f hax)
    (fun z ↦ ⟨-f z, by simp [hv]⟩)
  rw [← map_basis_eq_zero_iff c, Basis.coe_mkFinCons]
  -- `ω` evaluated on the extended basis is `ι_v ω` evaluated on the basis of `ker f`.
  have h' := congrArg (fun g : (LinearMap.ker f) [⋀^Fin n]→ₗ[K] K ↦ g b) h
  simp only [compLinearMap_apply, curryLeft_apply_apply, zero_apply] at h'
  -- `Matrix.vecCons` is `Fin.cons`.
  exact h'

/-- **A top-degree form with a nonzero vector in its kernel vanishes.** On a space of dimension
`n + 1`, if `ι_v ω = 0` for a nonzero vector `v`, then the top-degree alternating form `ω` is
zero. -/
theorem eq_zero_of_curryLeft_eq_zero (hn : finrank K V = n + 1) (ω : V [⋀^Fin (n + 1)]→ₗ[K] K)
    {v : V} (hv : v ≠ 0) (hω : ω.curryLeft v = 0) : ω = 0 := by
  obtain ⟨f, hf⟩ := Projective.exists_dual_eq_one K hv
  rw [← curryLeft_compLinearMap_subtype_eq_zero_iff hn ω hf, hω, zero_compLinearMap]

end AlternatingMap
