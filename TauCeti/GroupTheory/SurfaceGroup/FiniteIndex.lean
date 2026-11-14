/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Schreier
public import TauCeti.GroupTheory.SurfaceGroup.Free

/-!
# Finite-index subgroups of surface groups with boundary

Let `Σ` be one of the surface groups `S±(g, m + 1)` of `TauCeti.GroupTheory.SurfaceGroup.Basic`,
with nonempty boundary and Euler characteristic `χ`, and let `H ≤ Σ` be a subgroup of finite
index `n`. Since `Σ` is free of rank `1 - χ` (`TauCeti.GroupTheory.SurfaceGroup.Free`), Schreier's
index formula `rank H - 1 = n * (rank Σ - 1)` (`Subgroup.rank_sub_one_eq_index_mul_rank_sub_one`,
which applies to `Σ` directly) becomes

`rank H = 1 - n * χ`.

By the Nielsen–Schreier theorem (Mathlib's `Subgroup.isFreeGroupOfIsFreeGroup`, in
`Mathlib.GroupTheory.FreeGroup.NielsenSchreier`) `H` is free, so it is free of rank `1 - n * χ`.
Topologically, `H` is the fundamental group of the `n`-sheeted cover of the surface corresponding
to `H`, a compact surface with nonempty boundary whose Euler characteristic is `n * χ`.

## Main results

* `TauCeti.SurfaceGroup.Orientable.rank_eq_one_sub_index_mul_eulerChar` and
  `TauCeti.SurfaceGroup.Nonorientable.rank_eq_one_sub_index_mul_eulerChar`: a subgroup of finite
  index `n` of `S⁺(g, m + 1)`, respectively `S⁻(g, m + 1)`, has rank `1 - n * χ`.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*, J. Algebra 248
  (2002), Section 8, Proposition 8.3 and Corollary 8.4 (Schreier's formula).
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.1,
  Definition 5.1 (the Euler characteristic of a compact surface).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, §1.3, Proposition 1.32 (the number of sheets of a cover is the
  index of its fundamental group), and §2.2, Exercise 22 (an `n`-sheeted cover multiplies the
  Euler characteristic by `n`).
-/

public section

namespace TauCeti

namespace SurfaceGroup

variable {g m : ℕ}

namespace Orientable

/-- **Schreier's formula for orientable surface groups with boundary.** A subgroup `H` of finite
index `n` of `S⁺(g, m + 1)` has rank `1 - n * χ`, where `χ = 1 - 2g - m` is the Euler
characteristic of the surface. -/
theorem rank_eq_one_sub_index_mul_eulerChar (H : Subgroup (Orientable g (m + 1))) [H.FiniteIndex] :
    (Group.rank H : ℤ) = 1 - H.index * eulerChar g (m + 1) := by
  linear_combination H.rank_sub_one_eq_index_mul_rank_sub_one +
    H.index * rank_eq_one_sub_eulerChar g m

end Orientable

namespace Nonorientable

/-- **Schreier's formula for nonorientable surface groups with boundary.** A subgroup `H` of
finite index `n` of `S⁻(g, m + 1)` has rank `1 - n * χ`, where `χ = 1 - g - m` is the Euler
characteristic of the surface. -/
theorem rank_eq_one_sub_index_mul_eulerChar (H : Subgroup (Nonorientable g (m + 1)))
    [H.FiniteIndex] : (Group.rank H : ℤ) = 1 - H.index * eulerChar g (m + 1) := by
  linear_combination H.rank_sub_one_eq_index_mul_rank_sub_one +
    H.index * rank_eq_one_sub_eulerChar g m

end Nonorientable

end SurfaceGroup

end TauCeti
