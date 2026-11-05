/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Sqrt
public import TauCeti.Analysis.Complex.SlitPlane
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Slit-plane nodes in Carlson duplication

Carlson's duplication transformation replaces each node `x` by `(x + λ) / 4`, where
`λ = √x √y + √y √z + √z √x` uses principal square roots. The new nodes lie strictly in the
slit plane, even if one original node is zero. The factorization
`x + λ = (√x + √y) (√x + √z)` also respects principal complex powers: the two factors have
positive real parts, so their arguments add without crossing the branch cut.

These results place the transformed nodes in the domain of the slit-plane convergence and
holomorphy API and split their principal powers over the factorization without a branch
correction. The theorem for one node applies to the other two by permutation. The hypotheses
are weaker than requiring
all three original nodes in `slitPlane ∪ {0}` with at most one zero: it suffices that each
of the pairs `(x, y)` and `(x, z)` contains a slit-plane node.

## References

* NIST DLMF §19.26, especially 19.26.18.
* B. C. Carlson, *Computing elliptic integrals by duplication*, Numer. Math. 33 (1979), 1–16.
-/

public section

namespace Complex

private theorem duplication_node_eq (x y z : ℂ) :
    (x + (sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x)) / 4 =
      ((sqrt x + sqrt y) / 2) * ((sqrt x + sqrt z) / 2) := by
  have hx := sq_sqrt x
  linear_combination -hx / 4

/-- A duplicated Carlson node lies in the slit plane if each square-root sum has an input
in the slit plane. In particular this holds on the Carlson domain, including a zero node. -/
theorem carlson_duplication_node_mem_slitPlane {x y z : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) (hxz : x ∈ slitPlane ∨ z ∈ slitPlane) :
    (x + (sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x)) / 4 ∈ slitPlane := by
  rw [duplication_node_eq]
  apply TauCeti.mul_mem_slitPlane_of_re_pos
  · simpa only [div_ofNat_re, add_re] using half_pos ((sqrt_add_sqrt_re_pos_iff x y).mpr hxy)
  · simpa only [div_ofNat_re, add_re] using half_pos ((sqrt_add_sqrt_re_pos_iff x z).mpr hxz)

/-- Principal powers split across the factorization of a duplicated Carlson node, with no
branch correction. In particular, `w = -1/2` gives the inverse square root of the duplicated
node. -/
theorem carlson_duplication_node_cpow {x y z : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) (hxz : x ∈ slitPlane ∨ z ∈ slitPlane) (w : ℂ) :
    ((x + (sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x)) / 4) ^ w =
      ((sqrt x + sqrt y) / 2) ^ w * ((sqrt x + sqrt z) / 2) ^ w := by
  rw [duplication_node_eq]
  apply TauCeti.mul_cpow_of_re_pos
  · simpa only [div_ofNat_re, add_re] using half_pos ((sqrt_add_sqrt_re_pos_iff x y).mpr hxy)
  · simpa only [div_ofNat_re, add_re] using half_pos ((sqrt_add_sqrt_re_pos_iff x z).mpr hxz)

end Complex
