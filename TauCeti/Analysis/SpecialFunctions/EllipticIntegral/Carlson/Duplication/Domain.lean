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
`λ = √x √y + √y √z + √z √x` uses principal square roots; this parameter is
`Complex.carlsonDuplicationLambda`. The new nodes lie strictly in the slit plane, even if one
original node is zero. The factorization `x + λ = (√x + √y) (√x + √z)` also respects principal
complex powers: the two factors have positive real parts, so their arguments add without
crossing the branch cut.

These results place the transformed nodes in the domain of the slit-plane convergence and
holomorphy API and split their principal powers over the factorization without a branch
correction. The theorem for one node applies to the other two by permutation, using the
symmetry of the parameter. The hypotheses are weaker than requiring all three original nodes
in `slitPlane ∪ {0}` with at most one zero: it suffices that each of the pairs `(x, y)` and
`(x, z)` contains a slit-plane node.

The parameter and factorization follow Bastiaan J Braams' Apache-2.0 `lean-codes`,
`Carlson/Elliptic/Addition.lean` (commit `2b8cba1`), specifically `dupLambda` and
`add_dupLambda`. The domain argument here also includes zero nodes.

## References

* NIST DLMF §19.26, especially 19.26.18.
* B. C. Carlson, *Computing elliptic integrals by duplication*, Numer. Math. 33 (1979), 1–16.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Chapter 9, §9.6.
-/

public section

namespace Complex

/-- Carlson's duplication parameter `√x √y + √y √z + √z √x`, with principal complex square
roots. -/
noncomputable def carlsonDuplicationLambda (x y z : ℂ) : ℂ :=
  sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x

/-- The defining formula for Carlson's duplication parameter. -/
theorem carlsonDuplicationLambda_def (x y z : ℂ) :
    carlsonDuplicationLambda x y z = sqrt x * sqrt y + sqrt y * sqrt z + sqrt z * sqrt x :=
  (rfl)

/-- The duplication parameter is unchanged by interchanging its first two nodes. -/
theorem carlsonDuplicationLambda_comm_left (x y z : ℂ) :
    carlsonDuplicationLambda x y z = carlsonDuplicationLambda y x z := by
  simp only [carlsonDuplicationLambda_def]
  ring

/-- The duplication parameter is unchanged by interchanging its last two nodes. -/
theorem carlsonDuplicationLambda_comm_right (x y z : ℂ) :
    carlsonDuplicationLambda x y z = carlsonDuplicationLambda x z y := by
  simp only [carlsonDuplicationLambda_def]
  ring

/-- Factorization of a shifted node into sums of principal square roots. -/
theorem add_carlsonDuplicationLambda (x y z : ℂ) :
    x + carlsonDuplicationLambda x y z = (sqrt x + sqrt y) * (sqrt x + sqrt z) := by
  have hx := sq_sqrt x
  rw [carlsonDuplicationLambda_def]
  linear_combination -hx

private theorem duplication_node_eq (x y z : ℂ) :
    (x + carlsonDuplicationLambda x y z) / 4 =
      ((sqrt x + sqrt y) / 2) * ((sqrt x + sqrt z) / 2) := by
  rw [add_carlsonDuplicationLambda]
  ring

/-- A shifted node lies in the slit plane if each square-root sum in its factorization has an
input in the slit plane. -/
theorem add_carlsonDuplicationLambda_mem_slitPlane (x : ℂ) {y z : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) (hxz : x ∈ slitPlane ∨ z ∈ slitPlane) :
    x + carlsonDuplicationLambda x y z ∈ slitPlane := by
  rw [add_carlsonDuplicationLambda]
  apply TauCeti.mul_mem_slitPlane_of_re_pos
  · simpa only [add_re] using (sqrt_add_sqrt_re_pos_iff x y).mpr hxy
  · simpa only [add_re] using (sqrt_add_sqrt_re_pos_iff x z).mpr hxz

/-- A duplicated Carlson node lies in the slit plane if each square-root sum has an input
in the slit plane. In particular this holds on the Carlson domain, including a zero node. -/
theorem carlson_duplication_node_mem_slitPlane (x : ℂ) {y z : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) (hxz : x ∈ slitPlane ∨ z ∈ slitPlane) :
    (x + carlsonDuplicationLambda x y z) / 4 ∈ slitPlane := by
  simpa only [ofReal_ofNat] using TauCeti.div_ofReal_mem_slitPlane
    (add_carlsonDuplicationLambda_mem_slitPlane x hxy hxz) (by norm_num : (0 : ℝ) < 4)

/-- Principal powers split across the factorization of a duplicated Carlson node, with no
branch correction. In particular, `w = -1/2` gives the inverse square root of the duplicated
node. -/
theorem carlson_duplication_node_cpow (x : ℂ) {y z : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) (hxz : x ∈ slitPlane ∨ z ∈ slitPlane) (w : ℂ) :
    ((x + carlsonDuplicationLambda x y z) / 4) ^ w =
      ((sqrt x + sqrt y) / 2) ^ w * ((sqrt x + sqrt z) / 2) ^ w := by
  rw [duplication_node_eq]
  apply TauCeti.mul_cpow_of_re_pos
  · simpa only [div_ofNat_re, add_re] using half_pos ((sqrt_add_sqrt_re_pos_iff x y).mpr hxy)
  · simpa only [div_ofNat_re, add_re] using half_pos ((sqrt_add_sqrt_re_pos_iff x z).mpr hxz)

end Complex
