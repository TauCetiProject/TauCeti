/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
import TauCeti.AlgebraicGeometry.GroupScheme.KilledByRank
import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion

/-!
# The subgroup divisor of a point of exact order

For a point `P` of an elliptic curve `E/S`, the divisor `[P] + ⋯ + [NP]` is finite locally
free of rank `N`. If `P` has exact order `N` in the sense of Drinfeld, this divisor is a
commutative subgroup scheme. Deligne's rank theorem therefore kills the entire subgroup by
`N`, including its infinitesimal points, and gives its scheme-theoretic containment in `E[N]`.

The rank computation does not require exact order. The killing statement holds over arbitrary,
possibly nonreduced bases and is an equality of scheme morphisms. Containment in `E[N]` is stated
as an inclusion of ideal sheaves, so the existing closed-subscheme factorization API applies
directly.

This annihilation result is intrinsic to the subgroup divisor and its rank. It applies directly
to the subgroup-divisor formulation of exact order, independently of generator schemes or a
comparison with full sets of sections.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.4 and 1.12.
* `FiniteFlatCommGroupScheme.pow_eq_one_of_finrank`: Deligne's theorem for finite locally free
  commutative group schemes.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}
  (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (N : ℕ)

/-- The divisor of the first `N` positive multiples of a point is finite over the base. -/
instance isFinite_multiplesDivisor :
    IsFinite ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) := by
  rw [multiplesDivisor_eq_pointsDivisor]; infer_instance

/-- The divisor of the first `N` positive multiples of a point is flat over the base. -/
instance flat_multiplesDivisor :
    Flat ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) := by
  rw [multiplesDivisor_eq_pointsDivisor]; infer_instance

/-- The divisor of the first `N` positive multiples of a point is locally of finite
presentation over the base. Together with finiteness and flatness, this makes it finite
locally free. -/
instance locallyOfFinitePresentation_multiplesDivisor :
    LocallyOfFinitePresentation ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) := by
  rw [multiplesDivisor_eq_pointsDivisor]; infer_instance

/-- The divisor `[P] + ⋯ + [NP]` has constant rank `N`, whether or not `P` has exact order. -/
@[simp]
theorem finrank_multiplesDivisor :
    ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap).finrank = fun _ ↦ N := by
  induction N with
  | zero =>
    funext s
    rw [multiplesDivisor_zero, Scheme.Hom.finrank_eq_zero_iff_notMem_range]
    rintro ⟨x, -⟩
    exact isEmptyElim (α := (⊤ : E.carrier.IdealSheafData).subscheme) x
  | succ N ih =>
    have hsec := Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
      (f := E.structureMap)
      (P ^ (N + 1)).left (Over.w (P ^ (N + 1)))
    have := (P ^ (N + 1)).left.isClosedImmersion_of_comp_eq_id (f := E.structureMap) (Over.w _)
    have : IsFinite ((E.multiplesDivisor P N *
        Scheme.Hom.ker (Y := E.carrier) (P ^ (N + 1)).left).subschemeι ≫ E.structureMap) := by
      rw [← multiplesDivisor_succ]; infer_instance
    rw [multiplesDivisor_succ,
      (E.isRelativeEffectiveCartier_multiplesDivisor P N).finrank_mul_subschemeι_comp hsec,
      ih, Scheme.Hom.finrank_ker_comp_eq_one_of_comp_eq_id _ (f := E.structureMap) (Over.w _)]
    rfl

variable {P N}

/-- Multiplication by `N` kills the entire subgroup divisor of a point of exact order `N`,
scheme-theoretically, including all its infinitesimal points. -/
theorem IsOfExactOrder.subschemeι_comp_mulBy (h : E.IsOfExactOrder P N) :
    (E.multiplesDivisor P N).subschemeι ≫ (E.mulBy N).left =
      (E.multiplesDivisor P N).subschemeι ≫ E.structureMap ≫ E.zero := by
  let i : Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
      Over.mk E.structureMap := Over.homMk (E.multiplesDivisor P N).subschemeι
  have : IsClosedImmersion i.left := by
    simpa only [i, Over.homMk_left] using
      (inferInstanceAs (IsClosedImmersion (E.multiplesDivisor P N).subschemeι))
  have hgrp : ∃ grp : GrpObj (Over.mk
      ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap)), let := grp; IsMonHom i := by
    rw [GroupScheme.exists_grpObj_isMonHom_iff_ker_le i]
    simpa only [i, Over.homMk_left, Scheme.IdealSheafData.ker_subschemeι, one_left]
      using isOfExactOrder_iff.mp h
  obtain ⟨grp, hi⟩ := hgrp
  let := grp
  let := hi
  have : Mono i := Over.mono_of_mono_left i
  let G : FiniteFlatCommGroupScheme S :=
    { carrier := (E.multiplesDivisor P N).subscheme
      structureMap := (E.multiplesDivisor P N).subschemeι ≫ E.structureMap
      grp := grp
      comm := isCommMonObj_of_mono i
      finite := inferInstance
      flat := inferInstance
      locallyOfFinitePresentation := inferInstance }
  have hid : (𝟙 G.toOver) ^ N = 1 :=
    G.pow_eq_one_of_finrank (fun s ↦ congrFun (finrank_multiplesDivisor P N) s) _
  have hiN : i ≫ E.mulBy N = 1 := by
    rw [comp_mulBy, zpow_natCast]
    simpa only [pow_comp, Category.id_comp, one_comp] using congrArg (fun x ↦ x ≫ i) hid
  simpa only [Over.comp_left, hom_one_left, i, Over.homMk_left, Over.mk_hom, Category.assoc]
    using congrArg Over.Hom.left hiN

/-- The subgroup divisor of a point of exact order `N` is contained in `E[N]` as a closed
subscheme. The order on ideal sheaves reverses containment of their closed subschemes. -/
theorem IsOfExactOrder.ker_torsionι_le (h : E.IsOfExactOrder P N) :
    (E.torsionι N).left.ker ≤ E.multiplesDivisor P N := by
  let i : Over.mk ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) ⟶
      Over.mk E.structureMap := Over.homMk (E.multiplesDivisor P N).subschemeι
  let j := torsionLift i (Over.OverMorphism.ext h.subschemeι_comp_mulBy)
  have hj := j.left.le_ker_comp (E.torsionι N).left
  simpa only [← Over.comp_left, j, torsionLift_torsionι, i, Over.homMk_left,
    Scheme.IdealSheafData.ker_subschemeι] using hj

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
