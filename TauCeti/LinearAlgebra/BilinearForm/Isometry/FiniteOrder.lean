/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Isometries of finite order fixing a coisotropic subspace

Let `B` be a bilinear form on a module `M` in which `n • v = 0` with `n : ℕ` nonzero forces `v = 0`
(`HasUniqueDiv M`), e.g. any `ℚ`- or `ℝ`-vector space, and let `L` be a submodule containing its
`B`-orthogonal, `B.orthogonal L ≤ L`; for a symplectic form this says that `L` is coisotropic, and
a Lagrangian subspace is the main example. This file proves that an isometry `f` of `B` which fixes
`L` pointwise and has finite order is the identity
(`LinearMap.IsOrthogonal.eq_one_of_isOfFinOrder`).

Write `N = f - 1`. For `n ∈ L` and any `v`, `B n (N v) = B (f n) (f v) - B n v = 0`, so `N` maps
`M` into `B.orthogonal L ≤ L`, which `N` kills; hence `N² = 0` and `f ^ k = 1 + k N` for every
`k`. If `f ^ m = 1` with `m ≠ 0`, then `m N = 0`, and `N = 0` by `HasUniqueDiv M`.

The geometric use is a symplectic toric manifold: the differential at `x` of an element of the
stabilizer of `x` is a linear symplectic map fixing the orbit tangent space, which is Lagrangian
when the action is locally free at `x`, and it has finite order since that stabilizer is finite.

## Main results

* `LinearMap.IsOrthogonal.eq_one_of_isOfFinOrder`: an isometry of finite order fixing pointwise a
  submodule that contains its orthogonal is the identity.
-/

public section

namespace LinearMap.IsOrthogonal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [HasUniqueDiv M]
  {B : LinearMap.BilinForm R M} {f : Module.End R M} {L : Submodule R M}

/-- **Isometries of finite order fixing a coisotropic subspace are trivial.** Let `B` be a bilinear
form on a module in which `n • v = 0` with `n : ℕ` nonzero forces `v = 0` (`HasUniqueDiv`), e.g.
any `ℚ`- or `ℝ`-vector space, and `L` a submodule containing its `B`-orthogonal. An isometry of `B`
of finite order which fixes every vector of `L` is the identity. -/
theorem eq_one_of_isOfFinOrder (hf : B.IsOrthogonal f) (hL : B.orthogonal L ≤ L)
    (hfL : ∀ v ∈ L, f v = v) (hfin : IsOfFinOrder f) : f = 1 := by
  -- `f v - v` is `B`-orthogonal to `L`, hence lies in `L` and is fixed by `f`.
  have hmem (v : M) : f v - v ∈ L := hL fun n hn ↦ by
    rw [map_sub, ← hf n v, hfL n hn, sub_self]
  have hpow (k : ℕ) (v : M) : (f ^ k) v = v + k • (f v - v) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_add, map_nsmul, hfL _ (hmem v)]
      module
  obtain ⟨m, hm, hfm⟩ := hfin.exists_pow_eq_one
  ext v
  have h := hpow m v
  rw [hfm, one_apply_eq_self, left_eq_add, nsmul_eq_zero_iff_right hm.ne', sub_eq_zero] at h
  exact h

end LinearMap.IsOrthogonal
