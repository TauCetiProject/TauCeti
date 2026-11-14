/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Unipotent isometries of anisotropic forms

Let `f` be an isometry of a bilinear form `B` on a module `M`. If `f` fixes a vector `u` and
translates a vector `v` by `u`, that is `f u = u` and `f v = v + u`, then comparing `B (f u) (f v)`
with `B u v` shows that `u` is isotropic, `B u u = 0`
(`TauCeti.BilinForm.IsIsometry.apply_self_eq_zero_of_apply_eq_add`). A unipotent endomorphism
`f ≠ 1`, one for which `f - 1` is nilpotent, always has such a pair with `u ≠ 0`: if `(f - 1)ⁿ`
is the last nonzero power, take `u = (f - 1)ⁿ v ≠ 0` and replace `v` by `(f - 1)ⁿ⁻¹ v`. Hence an
anisotropic form, for instance an inner product, has no unipotent isometry other than the identity
(`TauCeti.BilinForm.IsIsometry.eq_one_of_isNilpotent_sub_one`). No symmetry of `B` and no
finiteness of `M` is needed.

For example the shear `(q, p) ↦ (q + p, p)` of `ℝ²` preserves the area form `dq ∧ dp` but preserves
no inner product.

## Main results

* `TauCeti.BilinForm.IsIsometry.apply_self_eq_zero_of_apply_eq_add`: if an isometry `f` of `B`
  satisfies `f u = u` and `f v = v + u`, then `B u u = 0`.
* `TauCeti.BilinForm.IsIsometry.eq_one_of_isNilpotent_sub_one`: a unipotent isometry of an
  anisotropic form is the identity.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm.IsIsometry

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : BilinForm R M} {f : M →ₗ[R] M}

/-- If an isometry `f` of `B` fixes `u` and translates `v` by `u`, then `u` is isotropic for `B`.
-/
theorem apply_self_eq_zero_of_apply_eq_add (hf : IsIsometry B f) {u v : M} (hu : f u = u)
    (hv : f v = v + u) : B u u = 0 := by
  have h := hf.apply u v
  rw [hu, hv, map_add] at h
  simpa using h

/-- A unipotent isometry of an anisotropic bilinear form is the identity: if `B x x = 0` only for
`x = 0`, `f` preserves `B` and `f - 1` is nilpotent, then `f = 1`. -/
theorem eq_one_of_isNilpotent_sub_one (hB : B.toQuadraticMap.Anisotropic) (hf : IsIsometry B f)
    (hn : IsNilpotent (f - 1)) : f = 1 := by
  -- If `(f - 1)ⁿ⁺² = 0`, then every `u = (f - 1)ⁿ⁺¹ v` is fixed by `f`, and `f` translates
  -- `(f - 1)ⁿ v` by `u`, so `u` is isotropic, hence zero.
  have step (n : ℕ) (h : (f - 1) ^ (n + 2) = 0) : (f - 1) ^ (n + 1) = 0 := by
    ext v
    have hf_eq (x : M) : f x = x + (f - 1) x := by simp
    refine hB _ ?_
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    refine hf.apply_self_eq_zero_of_apply_eq_add (v := ((f - 1) ^ n) v) ?_ ?_
    · rw [hf_eq, ← mul_apply_eq_comp, ← pow_succ', h, LinearMap.zero_apply, add_zero]
    · rw [hf_eq, ← mul_apply_eq_comp, ← pow_succ']
  have descend (n : ℕ) (h : (f - 1) ^ (n + 1) = 0) : (f - 1) ^ 1 = 0 := by
    induction n with
    | zero => exact h
    | succ n ih => exact ih (step n h)
  obtain ⟨k, hk⟩ := hn
  have h1 := descend k (by rw [pow_succ, hk, zero_mul])
  rwa [pow_one, sub_eq_zero] at h1

end BilinForm.IsIsometry

end TauCeti
