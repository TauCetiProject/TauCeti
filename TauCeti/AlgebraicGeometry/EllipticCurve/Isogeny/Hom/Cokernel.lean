/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import TauCeti.GroupTheory.Index.Quotient

/-!
# The torsion correction to an isogeny's cokernel

Let `f : E₁ → E₂` be a nonzero morphism of elliptic curves. Its dual shows that `f` reflects
torsion: the inverse image of `E₂(F)tors` is exactly `E₁(F)tors`. Consequently the cokernel on
points and the cokernel modulo torsion satisfy

`#coker(f) · #E₁(F)tors = #coker(f_free) · #E₂(F)tors · #ker(f)`.

Here the cokernel modulo torsion is expressed as the index of the image in
`E₂(F)/E₂(F)tors`; the map from `E₁(F)` has the same image as the induced map from its quotient
by torsion. This avoids choosing bases or splittings of the Mordell–Weil groups.

The kernel is finite for every nonzero morphism. When the source torsion is finite (in particular,
when the source is finitely generated), division gives the rational cokernel/kernel ratio
`#coker(f) / #ker(f)`. When the target is finitely generated, the cokernel is finite too:
its image contains `deg(f) · E₂(F)`.

This is the torsion factor in the kernel/cokernel proof of Cassels' isogeny invariance of the
BSD quotient. The regulator, period, local, and Tate–Shafarevich factors are not treated here.
No characteristic-zero or separability hypothesis is needed.

## Main results

* `TauCeti.Isogeny.Hom.comap_torsion_pointMapHom`: a nonzero morphism reflects torsion.
* `TauCeti.Isogeny.Hom.ker_pointMapHom_le_torsion` and
  `TauCeti.Isogeny.Hom.finite_ker_pointMapHom`: the kernel is torsion and finite, without
  a finite-generation assumption.
* `TauCeti.Isogeny.Hom.finiteIndex_range_pointMapHom`: finiteness of the rational cokernel
  when the target group is finitely generated.
* `TauCeti.Isogeny.Hom.index_range_mul_card_torsion`: the cross-multiplied correction formula.
* `TauCeti.Isogeny.Hom.index_range_div_card_ker`: the cokernel/kernel ratio
  `#coker(f) / #ker(f)`, in `ℚ`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.6, for the dual-isogeny identity.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199, for the arithmetic application.
-/

public section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (f : Hom W₁ W₂)

/-- A nonzero morphism of elliptic curves has exactly the torsion points as the inverse image
of the target's torsion subgroup. -/
@[simp]
theorem comap_torsion_pointMapHom (hf : f ≠ 0) :
    (AddCommGroup.torsion W₂.Point).comap f.pointMapHom = AddCommGroup.torsion W₁.Point := by
  refine le_antisymm ?_ (AddCommGroup.le_comap_torsion f.pointMapHom)
  intro P hP
  have h := f.dual.pointMapHom.isOfFinAddOrder hP
  rw [pointMapHom_apply, pointMapHom_apply, dual_pointMap_pointMap] at h
  exact h.of_nsmul ((f.degree_eq_zero_iff).not.mpr hf)

/-- Every point in the kernel of a nonzero morphism is torsion. -/
theorem ker_pointMapHom_le_torsion (hf : f ≠ 0) :
    f.pointMapHom.ker ≤ AddCommGroup.torsion W₁.Point := by
  rw [← f.comap_torsion_pointMapHom hf]
  exact AddMonoidHom.ker_le_comap _ _

/-- The kernel on points of a nonzero morphism is finite, as its fibre over zero. -/
theorem finite_ker_pointMapHom (hf : f ≠ 0) : Finite f.pointMapHom.ker := by
  apply Set.finite_coe_iff.mpr
  refine (finite_setOf_pointMap_eq hf 0).subset ?_
  intro P hP
  simpa only [SetLike.mem_coe, AddMonoidHom.mem_ker, pointMapHom_apply,
    Set.mem_ofPred_eq] using hP

/-- The cokernel on rational points is finite if the target group is finitely generated:
the image contains all `deg(f)`-multiples, by the dual identity. -/
theorem finiteIndex_range_pointMapHom [AddGroup.FG W₂.Point] (hf : f ≠ 0) :
    f.pointMapHom.range.FiniteIndex := by
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg W₂.Point
    ((f.degree_eq_zero_iff).not.mpr hf)
  refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom f.degree).range) ?_
  rintro P ⟨Q, rfl⟩
  refine ⟨f.dual.pointMap Q, ?_⟩
  simp only [pointMapHom_apply, pointMap_dual_pointMap, nsmulAddMonoidHom_apply]

/-- The correction between the full cokernel index and the image index modulo torsion.
The cross-multiplied identity needs no finite-generation or finiteness hypothesis. -/
theorem index_range_mul_card_torsion (hf : f ≠ 0) :
    f.pointMapHom.range.index * Nat.card (AddCommGroup.torsion W₁.Point) =
      (f.pointMapHom.range.map (QuotientAddGroup.mk' (AddCommGroup.torsion W₂.Point))).index *
        Nat.card (AddCommGroup.torsion W₂.Point) * Nat.card f.pointMapHom.ker := by
  simpa only [f.comap_torsion_pointMapHom hf] using
    (TauCeti.index_range_mul_card_comap (f := f.pointMapHom)
      (S := AddCommGroup.torsion W₂.Point))

/-- The rational cokernel/kernel ratio `#coker(f) / #ker(f)` equals the image index modulo torsion
times the ratio of target to source torsion orders. Only the source torsion subgroup needs to be
finite; in particular, finite generation of the source suffices. If the target is finitely
generated, `finiteIndex_range_pointMapHom` makes the cokernel index a positive integer. -/
theorem index_range_div_card_ker [Finite (AddCommGroup.torsion W₁.Point)] (hf : f ≠ 0) :
    (f.pointMapHom.range.index : ℚ) / Nat.card f.pointMapHom.ker =
      (f.pointMapHom.range.map (QuotientAddGroup.mk' (AddCommGroup.torsion W₂.Point))).index *
        (Nat.card (AddCommGroup.torsion W₂.Point) : ℚ) /
          Nat.card (AddCommGroup.torsion W₁.Point) := by
  have := f.finite_ker_pointMapHom hf
  have hT : (Nat.card (AddCommGroup.torsion W₁.Point) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hK : (Nat.card f.pointMapHom.ker : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  apply (div_eq_div_iff hK hT).mpr
  exact_mod_cast f.index_range_mul_card_torsion hf

end TauCeti.Isogeny.Hom
