/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Supersingular

/-!
# The height-two bound for elliptic Weierstrass curves

For an elliptic Weierstrass curve over any commutative ring and any prime `p`, every height ideal
from `I₃` onward of its formal group is the unit ideal. Equivalently, Landweber's `v₂` is a unit
modulo `(p, v₁)`. All subsequent height quotients therefore vanish. The statements concern
families, including rings with nilpotents and the zero ring; they impose no characteristic
assumption on the coefficient ring.

The all-prime field-height bound (`WeierstrassCurve.height_formalGroup_le_two`), together with
detection of a proper height ideal on a maximal-ideal quotient
(`FormalGroup.heightIdeal_eq_top_iff_forall_height_lt`), gives the family-level result at every
prime `p` (including `2` and `3`). This supplies the height-two unit condition for Landweber
exactness; it does not assert the separate regularity of `p` and `v₁` for an arbitrary family.

## Main results

* `WeierstrassCurve.heightIdeal_formalGroup_eq_top`: for an elliptic curve `W` over any
  commutative ring `R` and any prime `p`, `(formalGroup W).heightIdeal p n = ⊤` for all `n ≥ 3`.
* `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup`: for an elliptic curve `W` over any
  commutative ring `R` and any prime `p`, Landweber's `v₂` is a unit modulo `I₂(formalGroup W)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7 and V.3.1.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire
  Bourbaki 1005 (2009), §3.2.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    {p n : ℕ}

/-- For an elliptic Weierstrass curve over any commutative ring and any prime `p`, every height
ideal from `I₃` onward of its formal group is the unit ideal. This holds over arbitrary
commutative coefficient rings. -/
theorem heightIdeal_formalGroup_eq_top (hp : p.Prime) (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  apply ((formalGroup W).heightIdeal_eq_top_iff_forall_height_lt hp (by omega)).mpr
  intro K _ _ f
  rw [← map_formalGroup]
  exact (W.map f).height_formalGroup_le_two.trans_lt (by exact_mod_cast (by omega : 2 < n))

/-- For an elliptic Weierstrass curve over any commutative ring and any prime `p`, Landweber's
`v₂` of its formal group is a unit modulo `(p, v₁)`. This is the height-two unit condition, with
no regularity assumption on the coefficient ring. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) :=
  ((formalGroup W).isUnit_mk_coeff_nsmulSeries_iff hp 2).mpr
    (W.heightIdeal_formalGroup_eq_top hp le_rfl)

end WeierstrassCurve
