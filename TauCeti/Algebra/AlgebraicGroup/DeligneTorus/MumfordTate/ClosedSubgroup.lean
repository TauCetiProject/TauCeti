/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Kernel
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Classification

/-!
# The Mumford–Tate group as a closed subgroup scheme

Let `G` be an affine group over `ℚ` with coordinate Hopf algebra `H`, and let `h : S → G_ℝ` be a
homomorphism from the Deligne torus. The Mumford–Tate ideal of `h` cuts out a closed subgroup
scheme `MT(h)` of `G = Spec H` (`TauCeti.DeligneTorus.mumfordTateClosedSubgroup`). Closed
subgroup schemes of `Spec H` correspond to Hopf ideals of `H`, reversing inclusions
(`TauCeti.CommHopfAlgCat.hopfIdealOrderIsoClosedSubgroup`), so the minimality of the Mumford–Tate
ideal becomes minimality of `MT(h)`: it is contained in a closed subgroup scheme `P` of `G`
exactly when the Hopf ideal of `P` consists of rational functions vanishing on `h(S)`, that is,
exactly when `h` factors through the real extension of `P`.

## Main declarations

* `TauCeti.DeligneTorus.mumfordTateClosedSubgroup h`: the Mumford–Tate group as a closed subgroup
  scheme of `Spec H`.
* `TauCeti.DeligneTorus.mumfordTateClosedSubgroup_le_quotientClosedSubgroup_iff`: `MT(h)` lies in
  the closed subgroup cut out by a Hopf ideal `I` exactly when `I` lies in the rational coordinate
  kernel `K_h`.
* `TauCeti.DeligneTorus.mumfordTateClosedSubgroup_le_iff`: **minimality**; `MT(h)` lies in a
  closed subgroup scheme `P` exactly when `h` factors through the real extension of `P`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, Theorem 2.14, proof of (a), p. 30, and
  the aside after Definition 2.16, p. 31.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat

namespace TauCeti.DeligneTorus

variable {H : _root_.CommHopfAlgCat.{0} ℚ}

/-- **The Mumford–Tate group as a closed subgroup scheme** of `G = Spec H`: the closed subgroup
scheme cut out by the Mumford–Tate ideal of `h`. It is the smallest closed subgroup scheme of `G`
through whose real extension `h` factors (`TauCeti.DeligneTorus.mumfordTateClosedSubgroup_le_iff`).
-/
noncomputable def mumfordTateClosedSubgroup
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of ℚ)).obj (Opposite.op H)) :=
  quotientClosedSubgroup H (mumfordTateHopfIdeal h)

/-- `MT(h)` is the closed subgroup scheme cut out by the Mumford–Tate ideal. -/
theorem mumfordTateClosedSubgroup_def
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mumfordTateClosedSubgroup h = quotientClosedSubgroup H (mumfordTateHopfIdeal h) :=
  (rfl)

/-- The Hopf ideal recovered from `MT(h)` by the classification of closed subgroup schemes is the
Mumford–Tate ideal. -/
@[simp↓]
theorem hopfIdealOrderIsoClosedSubgroup_symm_apply_mumfordTateClosedSubgroup
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    (hopfIdealOrderIsoClosedSubgroup H).symm (mumfordTateClosedSubgroup h) =
      OrderDual.toDual (mumfordTateHopfIdeal h) := by
  rw [mumfordTateClosedSubgroup_def,
    hopfIdealOrderIsoClosedSubgroup_symm_apply_quotientClosedSubgroup]

/-- `MT(h)` lies in the closed subgroup scheme cut out by a Hopf ideal `I` exactly when every
function in `I` vanishes on `h(S)`. -/
@[simp]
theorem mumfordTateClosedSubgroup_le_quotientClosedSubgroup_iff
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S} {I : HopfIdeal ℚ H} :
    mumfordTateClosedSubgroup h ≤ quotientClosedSubgroup H I ↔
      I.toIdeal ≤ rationalCoordinateKernel h := by
  rw [mumfordTateClosedSubgroup_def, quotientClosedSubgroup_le_iff,
    le_mumfordTateHopfIdeal_iff_toIdeal_le_rationalCoordinateKernel]

/-- **Minimality of the Mumford–Tate group scheme.** `MT(h)` is contained in a closed subgroup
scheme `P` of `G` exactly when `h` factors through the real extension of `P`: when `h` kills the
real extension of the Hopf ideal of `P`. -/
theorem mumfordTateClosedSubgroup_le_iff
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S}
    {P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of ℚ)).obj (Opposite.op H))} :
    mumfordTateClosedSubgroup h ≤ P ↔
      (baseChangeHopfIdeal (K := ℝ)
        (OrderDual.ofDual ((hopfIdealOrderIsoClosedSubgroup H).symm P))).toIdeal ≤
        RingHom.ker h.hom.toAlgHom.toRingHom := by
  conv_lhs => rw [← hopfIdealOrderIsoClosedSubgroup_apply_symm_apply H P]
  rw [mumfordTateClosedSubgroup_def, quotientClosedSubgroup_le_iff, le_mumfordTateHopfIdeal_iff]

/-- **Minimality of the Mumford–Tate group scheme, rational form.** `MT(h)` is contained in a
closed subgroup scheme `P` of `G` exactly when the Hopf ideal of `P` lies in the rational
coordinate kernel `K_h`. -/
theorem mumfordTateClosedSubgroup_le_iff_le_rationalCoordinateKernel
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S}
    {P : ClosedSubgroupScheme
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of ℚ)).obj (Opposite.op H))} :
    mumfordTateClosedSubgroup h ≤ P ↔
      (OrderDual.ofDual ((hopfIdealOrderIsoClosedSubgroup H).symm P)).toIdeal ≤
        rationalCoordinateKernel h := by
  conv_lhs => rw [← hopfIdealOrderIsoClosedSubgroup_apply_symm_apply H P]
  exact mumfordTateClosedSubgroup_le_quotientClosedSubgroup_iff

end TauCeti.DeligneTorus
