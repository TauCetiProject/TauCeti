/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.SlitPlane
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The slit-plane domain of Carlson duplication

Carlson's duplication parameter is `λ = √x √y + √y √z + √z √x`, using principal
square roots. The factorization `x + λ = (√x + √y)(√x + √z)` shows that the
new nodes `(x + λ)/4`, `(y + λ)/4`, `(z + λ)/4` lie strictly in the slit plane
when the original nodes belong to `slitPlane ∪ {0}` with at most one zero.
Thus duplication removes a possible zero node and does not cross the branch cut.
This is the domain control needed to apply holomorphy and convergence of Carlson's
integrals to the duplicated arguments.

The membership criterion is stated using only the two conditions actually needed:
at least one of `x, y`, and at least one of `x, z`, must lie in the slit plane.
The other nodes need not be restricted, since every principal square root has
nonnegative real part. Permuting the arguments gives the other two nodes.

The parameter and factorization follow Bastiaan J Braams' Apache-2.0 `lean-codes`,
`Carlson/Elliptic/Addition.lean` (commit `2b8cba1`), specifically `dupLambda` and
`add_dupLambda`. The domain argument here also includes zero nodes.

## References

* NIST *Digital Library of Mathematical Functions*, §19.26, <https://dlmf.nist.gov/19.26>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Chapter 9, §9.6.
-/

public section

namespace Complex

/-- Carlson's duplication parameter, with principal complex square roots. -/
noncomputable def carlsonDuplicationLambda (x y z : ℂ) : ℂ :=
  x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) +
    y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) + z ^ (1 / 2 : ℂ) * x ^ (1 / 2 : ℂ)

/-- The defining formula for Carlson's duplication parameter. -/
theorem carlsonDuplicationLambda_def (x y z : ℂ) :
    carlsonDuplicationLambda x y z = x ^ (1 / 2 : ℂ) * y ^ (1 / 2 : ℂ) +
      y ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) + z ^ (1 / 2 : ℂ) * x ^ (1 / 2 : ℂ) := (rfl)

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
    x + carlsonDuplicationLambda x y z =
      (x ^ (1 / 2 : ℂ) + y ^ (1 / 2 : ℂ)) *
        (x ^ (1 / 2 : ℂ) + z ^ (1 / 2 : ℂ)) := by
  have hs : (x ^ (1 / 2 : ℂ)) ^ 2 = x := by simp
  rw [carlsonDuplicationLambda_def]
  linear_combination -hs

/-- A shifted node lies in the slit plane if each square-root sum in its
factorization has at least one slit-plane summand. In particular this covers every
node of an admissible Carlson triple, including a zero node. -/
theorem add_carlsonDuplicationLambda_mem_slitPlane {x y z : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) (hxz : x ∈ slitPlane ∨ z ∈ slitPlane) :
    x + carlsonDuplicationLambda x y z ∈ slitPlane := by
  rw [add_carlsonDuplicationLambda]
  exact TauCeti.mul_mem_slitPlane_of_re_pos
    (cpow_half_add_cpow_half_re_pos hxy) (cpow_half_add_cpow_half_re_pos hxz)

/-- The scaled node used in Carlson duplication lies strictly in the slit plane.
The same criterion applies to the other nodes after permuting the inputs. -/
theorem add_carlsonDuplicationLambda_div_four_mem_slitPlane {x y z : ℂ}
    (hxy : x ∈ slitPlane ∨ y ∈ slitPlane) (hxz : x ∈ slitPlane ∨ z ∈ slitPlane) :
    (x + carlsonDuplicationLambda x y z) / 4 ∈ slitPlane := by
  exact TauCeti.div_ofReal_mem_slitPlane
    (add_carlsonDuplicationLambda_mem_slitPlane hxy hxz) (by norm_num : (0 : ℝ) < 4)

end Complex
