/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The `2`-torsion of the group of points of a Weierstrass curve

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`. In that normal form negation is `-(x, y) = (x, -y)`, so a point is its own
negative exactly when `y = 0`, and the `2`-torsion of `W(K)` is the origin together with the
points `(x, 0)` at the roots of `f`.

The counting statement `card_ker_nsmul_two` is what turns a root count into a torsion count. It
is one side of the archimedean local-image formula of explicit `2`-descent, which reads
`#(im μ_v) = #E(ℝ)[2] / 2` at a real place.

## Main statements

* `WeierstrassCurve.Affine.ker_nsmul_two_eq_insert_range`: the doubling kernel consists of the
  origin and the points `(x, 0)` at the roots of `f`.
* `WeierstrassCurve.Affine.card_ker_nsmul_two`: `#W(K)[2]` is the number of roots of `f` in `K`,
  plus one for the origin.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, at `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean` lines 806-868 — the `2`-torsion section, which sits after
the range that `TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean` ported.

The archimedean local-image count of explicit `2`-descent needs this torsion count.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

variable {K : Type*} [Field K] (W : Affine K) [W.IsCharNeTwoNF] [W.IsElliptic]

/-- The affine point `(x, 0)` at a root `x` of the Weierstrass cubic in characteristic
different from two normal form. -/
def pointOfRoot (x : {x : K // W.f.eval x = 0}) : W.Point :=
  .some x 0 (W.nonsingular_of_eval_f_eq_zero x.property)

/-- The point at a root of the Weierstrass cubic has that root as its `x`-coordinate and
zero as its `y`-coordinate. -/
theorem pointOfRoot_eq_some (x : {x : K // W.f.eval x = 0}) :
    W.pointOfRoot x = .some x 0 (W.nonsingular_of_eval_f_eq_zero x.property) := (rfl)

variable [DecidableEq K]

/-- In characteristic different from two normal form, the doubling kernel consists of the
origin and the points `(x, 0)` at the roots of the Weierstrass cubic. -/
theorem ker_nsmul_two_eq_insert_range :
    ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point) =
      insert 0 (Set.range W.pointOfRoot) := by
  have h2F : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two W)
  ext P
  constructor
  · intro hP
    cases P with
    | zero => exact Set.mem_insert _ _
    | some x y h =>
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hP
      obtain rfl := y_eq_zero_of_order_two h2F h hP
      have hx : W.f.eval x = 0 := by
        simpa using (W.equation_iff_eval_f_eq_sq x 0).mp h.1
      exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · intro hP
    rcases Set.mem_insert_iff.mp hP with rfl | ⟨x, rfl⟩
    · exact zero_mem _
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, two_nsmul]
      exact Point.add_self_of_Y_eq (by rw [negY_of_isCharNeTwoNF, neg_zero])

/-- The `2`-torsion of `W(K)` has one more element than `f` has roots in `K`. -/
theorem card_ker_nsmul_two : Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker =
    Nat.card {x : K // W.f.eval x = 0} + 1 := by
  have hfin : Finite {x : K | W.f.eval x = 0} :=
    Set.Finite.to_subtype (Polynomial.finite_setOfPred_isRoot W.f_ne_zero)
  have hinj : Function.Injective W.pointOfRoot := by
    intro a b hab
    rw [pointOfRoot_eq_some, pointOfRoot_eq_some, Point.some.injEq] at hab
    exact Subtype.ext hab.1
  calc Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker
      = ((nsmulAddMonoidHom (α := W.Point) 2).ker : Set W.Point).ncard := Nat.card_coe_set_eq _
    _ = (insert 0 (Set.range W.pointOfRoot)).ncard :=
        congrArg Set.ncard (ker_nsmul_two_eq_insert_range W)
    _ = (Set.range W.pointOfRoot).ncard + 1 := Set.ncard_insert_of_notMem (by
      intro ⟨x, hx⟩
      rw [pointOfRoot_eq_some] at hx
      exact Point.some_ne_zero _ hx)
    _ = Nat.card {x : K // W.f.eval x = 0} + 1 := by
        rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]

end Affine

end WeierstrassCurve

end
