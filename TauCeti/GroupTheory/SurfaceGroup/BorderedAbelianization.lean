/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Rank
public import TauCeti.GroupTheory.SurfaceGroup.Free

/-!
# Abelianizations of surface groups with boundary

A surface group with nonempty boundary is free (`TauCeti.GroupTheory.SurfaceGroup.Free`), so its
abelianization is free abelian, and its rank is the rank of the group. For the orientable surface
group `S⁺(g, m + 1)` the classes of `a₁, …, a_g, b₁, …, b_g, p₁, …, p_m` form a basis, so the rank
is `2g + m`; for the nonorientable surface group `S⁻(g, m + 1)` the classes of
`c₁, …, c_g, p₁, …, p_m` form a basis, so the rank is `g + m`. In both cases the rank is `1 - χ`,
where `χ` is the Euler characteristic of the surface.

The bases are `(TauCeti.SurfaceGroup.Orientable.freeBasis g m).abelianizationBasis` and
`(TauCeti.SurfaceGroup.Nonorientable.freeBasis g m).abelianizationBasis`, and the abelianizations
are free `ℤ`-modules by `TauCeti.instModuleFreeAbelianization`.

## Main results

* `TauCeti.SurfaceGroup.Orientable.finrank_abelianization` and
  `TauCeti.SurfaceGroup.Nonorientable.finrank_abelianization`: the abelianizations of
  `S⁺(g, m + 1)` and `S⁻(g, m + 1)` have rank `2g + m` and `g + m`.
* `TauCeti.SurfaceGroup.Orientable.finrank_abelianization_eq_one_sub_eulerChar` and
  `TauCeti.SurfaceGroup.Nonorientable.finrank_abelianization_eq_one_sub_eulerChar`: in both cases
  the rank is `1 - χ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Section 1.2, p. 42 (the abelianization of a free group is free
  abelian on the same basis).
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.1,
  Definition 5.1 (the Euler characteristic of a compact surface with boundary).
-/

public section

namespace TauCeti

namespace SurfaceGroup

namespace Orientable

variable (g m : ℕ)

/-- The abelianization of the orientable surface group `S⁺(g, m + 1)` has rank `2g + m`. A basis is
`(freeBasis g m).abelianizationBasis`, the classes of `a₁, …, a_g, b₁, …, b_g, p₁, …, p_m`. -/
@[simp]
theorem finrank_abelianization :
    Module.finrank ℤ (Additive (Group.Abelianization (Orientable g (m + 1)))) = 2 * g + m := by
  rw [finrank_abelianization_eq_rank, rank_eq]

/-- **The abelianization of an orientable surface group with boundary has rank `1 - χ`.** The
abelianization of `S⁺(g, m + 1)`, which is free abelian (`TauCeti.instModuleFreeAbelianization`),
has rank `1 - χ`, where `χ = 1 - 2g - m` is the Euler characteristic of the surface. -/
theorem finrank_abelianization_eq_one_sub_eulerChar :
    (Module.finrank ℤ (Additive (Group.Abelianization (Orientable g (m + 1)))) : ℤ) =
      1 - eulerChar g (m + 1) := by
  rw [finrank_abelianization_eq_rank, rank_eq_one_sub_eulerChar]

end Orientable

namespace Nonorientable

variable (g m : ℕ)

/-- The abelianization of the nonorientable surface group `S⁻(g, m + 1)` has rank `g + m`. A basis
is `(freeBasis g m).abelianizationBasis`, the classes of `c₁, …, c_g, p₁, …, p_m`. -/
@[simp]
theorem finrank_abelianization :
    Module.finrank ℤ (Additive (Group.Abelianization (Nonorientable g (m + 1)))) = g + m := by
  rw [finrank_abelianization_eq_rank, rank_eq]

/-- **The abelianization of a nonorientable surface group with boundary has rank `1 - χ`.** The
abelianization of `S⁻(g, m + 1)`, which is free abelian (`TauCeti.instModuleFreeAbelianization`),
has rank `1 - χ`, where `χ = 1 - g - m` is the Euler characteristic of the surface. -/
theorem finrank_abelianization_eq_one_sub_eulerChar :
    (Module.finrank ℤ (Additive (Group.Abelianization (Nonorientable g (m + 1)))) : ℤ) =
      1 - eulerChar g (m + 1) := by
  rw [finrank_abelianization_eq_rank, rank_eq_one_sub_eulerChar]

end Nonorientable

end SurfaceGroup

end TauCeti
