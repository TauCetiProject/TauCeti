/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.Connected.Descent
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Connected

/-!
# Geometric connectedness of Mumford–Tate groups

Let `G` be an affine group over `ℚ` and `h : S → G_ℝ` a homomorphism from the Deligne torus. Its
Mumford–Tate group `MT(h)` (`TauCeti.DeligneTorus.mumfordTateHopfIdeal`) is the smallest closed
`ℚ`-subgroup of `G` through whose real extension `h` factors. This file proves that `MT(h)` is
geometrically connected when `MT(h)` (not necessarily `G`) is of finite type; no polarization is
assumed. For `G = GL(V)` this is the connectedness of the Mumford–Tate group of a rational Hodge
structure.

Since `MT(h)` is cut out by the Hopf-ideal contraction of the largest Hopf ideal contained in the
kernel of the coordinate map of `h`, this is the case of a single homomorphism
from the geometrically connected group `S` of
`geometricallyConnectedCommHopfAlgProperty_quotient_contractHopfIdeal_commonKernelHopfIdeal`
(in `TauCeti.CommHopfAlgCat`), which descends the identity component of `MT(h)_{ℚ^alg}` to `ℚ`
and shows by minimality that it is all of `MT(h)`.

## Main declarations

* `TauCeti.DeligneTorus.geometricallyConnectedCommHopfAlgProperty_quotient_mumfordTateHopfIdeal`:
  the Mumford–Tate group is geometrically connected, when it is of finite type.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), §3, pp. 24–25.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 (the identity component) and
  Appendix A (Galois descent).
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat
open scoped TensorProduct

namespace TauCeti.DeligneTorus

/-- **The Mumford–Tate group is geometrically connected.** For an affine group `G` over `ℚ` and a
homomorphism `h : S → G_ℝ` from the Deligne torus whose Mumford–Tate group `MT(h)` is of finite
type, `MT(h)` is geometrically connected. No polarization is needed. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_mumfordTateHopfIdeal
    {H : _root_.CommHopfAlgCat.{0} ℚ} (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S)
    [Algebra.FiniteType ℚ (quotient H (mumfordTateHopfIdeal h))] :
    geometricallyConnectedCommHopfAlgProperty ℚ (quotient H (mumfordTateHopfIdeal h)) := by
  rw [mumfordTateHopfIdeal_def] at *
  exact geometricallyConnectedCommHopfAlgProperty_quotient_contractHopfIdeal_commonKernelHopfIdeal
    (fun _ : Unit ↦ h) fun _ ↦
      Algebra.WeilRestriction.geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup
        (k := ℝ) (B := ℂ)

end TauCeti.DeligneTorus
