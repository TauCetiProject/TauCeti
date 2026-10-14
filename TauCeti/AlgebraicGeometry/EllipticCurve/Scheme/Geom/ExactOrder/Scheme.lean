/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Locus
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite

/-!
# The scheme of points of exact order `N`

Let `E` be an elliptic curve over a scheme `S`. The exact-order locus `E.exactOrderLocus N` is an
ideal sheaf on `E` whose closed subscheme carries the universal point of exact order `N`. This file
regards that closed subscheme as a scheme over `S`, the **exact-order scheme**
`E.exactOrderScheme N`, and shows that it represents the points of exact order `N` on base changes
of `E`: for a scheme `T` over `S` and a base change `E'` of `E` along `T ⟶ S`, the `T`-points of
`E'` of exact order `N`, in the sense of Drinfeld, are the morphisms `T ⟶ E.exactOrderScheme N`
over `S` (`EllipticCurveGeom.exactOrderPointsEquivOfIsPullback`). No hypothesis is placed on `S`,
which may be nonreduced, and `N` need not be invertible on it.

A point of exact order `N` is killed by `N`, so the exact-order scheme lies in the `N`-torsion
`E[N]` (`EllipticCurveGeom.exactOrderSchemeι_comp_mulBy`). As a closed subscheme of `E[N]`, it is
finite over `S` for `N ≠ 0` (`EllipticCurveGeom.isFinite_exactOrderScheme_hom`). This is the form
in which points of exact order `N` relatively represent the moduli problem `[Γ₁(N)]` of Katz and
Mazur, by a scheme finite over the base.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exactOrderScheme E N`: the closed subscheme of `E`
  cut out by the exact-order locus, as a scheme over `S`, with its inclusion
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exactOrderSchemeι E N` into `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exactOrderPointsEquivOfIsPullback`: the points of
  exact order `N` of a base change of `E` along `T ⟶ S` are the morphisms from `T` to the
  exact-order scheme.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exactOrderSchemeι_comp_mulBy`: multiplication by
  `N` kills the exact-order scheme.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFinite_exactOrderScheme_hom`: for `N ≠ 0`, the
  exact-order scheme is finite over `S`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, 1.6.2 (the closed locus of points of exact order `N`), 3.2 and 3.6.0 (`[Γ₁(N)]` is
  relatively representable and finite).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (N : ℕ)

/-- The **exact-order scheme** of `E`: the closed subscheme of `E` cut out by the exact-order locus
`E.exactOrderLocus N`, as a scheme over `S`. Its points with values in a scheme `T` over `S` are
the points of exact order `N` of the base change of `E` to `T`
(`exactOrderPointsEquivOfIsPullback`). -/
noncomputable abbrev exactOrderScheme : Over S :=
  Over.mk ((E.exactOrderLocus N).subschemeι ≫ E.structureMap)

/-- The inclusion of the exact-order scheme in `E`, a closed immersion. -/
noncomputable def exactOrderSchemeι : E.exactOrderScheme N ⟶ Over.mk E.structureMap :=
  Over.homMk (E.exactOrderLocus N).subschemeι

/-- The inclusion of the exact-order scheme in `E` is the inclusion of the closed subscheme of the
exact-order locus. -/
@[simp]
theorem exactOrderSchemeι_left :
    (E.exactOrderSchemeι N).left = (E.exactOrderLocus N).subschemeι :=
  (rfl)

/-- The inclusion of the exact-order scheme in `E` is a closed immersion. -/
instance isClosedImmersion_exactOrderSchemeι_left :
    IsClosedImmersion (E.exactOrderSchemeι N).left := by
  rw [exactOrderSchemeι_left]
  infer_instance

/-- The inclusion of the exact-order scheme in `E` is a monomorphism. -/
instance mono_exactOrderSchemeι : Mono (E.exactOrderSchemeι N) :=
  Over.mono_of_mono_left _

variable {E N}

/-! ### Points of exact order `N` on base changes -/

section BaseChange

variable {T : Over S} {E' : EllipticCurveGeom T.left} {g : E'.carrier ⟶ E.carrier}
  (hg : IsPullback g E'.structureMap E.structureMap T.hom) (h0 : E'.zero ≫ g = T.hom ≫ E.zero)

variable (N) in
/-- **The exact-order scheme represents points of exact order `N`** (Katz–Mazur, 1.6.2). Let `T`
be a scheme over `S` and `g : E' ⟶ E` a morphism of elliptic curves lying over `T ⟶ S`, forming a
pullback square with the structure morphisms and carrying the zero section of `E'` to that of `E`;
for instance `E'` is the base change `E_T`. Then the `T`-points of `E'` of exact order `N` are the
morphisms `T ⟶ E.exactOrderScheme N` over `S`: a point `P` corresponds to the morphism whose image
in `E` is `P ≫ g` (`exactOrderPointsEquivOfIsPullback_apply_left_comp`). -/
noncomputable def exactOrderPointsEquivOfIsPullback :
    {P : 𝟙_ (Over T.left) ⟶ Over.mk E'.structureMap // E'.IsOfExactOrder P N} ≃
      (T ⟶ E.exactOrderScheme N) where
  toFun P := Over.homMk
    (IsClosedImmersion.lift (E.exactOrderLocus N).subschemeι (P.1.left ≫ g) (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (isOfExactOrder_iff_exactOrderLocus_le_ker_comp hg h0 P.1 N).mp P.2))
    (by simp [hg.w])
  invFun y := ⟨Over.homMk (hg.lift (y ≫ E.exactOrderSchemeι N).left (𝟙 T.left)
      (by simpa using Over.w (y ≫ E.exactOrderSchemeι N))) (by simp), by
    -- the image of `y` in `E` factors through the closed subscheme of the exact-order locus
    rw [isOfExactOrder_iff_exactOrderLocus_le_ker_comp hg h0]
    simp only [Over.homMk_left, hg.lift_fst, Over.comp_left, exactOrderSchemeι_left]
    exact (Scheme.IdealSheafData.ker_subschemeι _).symm.le.trans (y.left.le_ker_comp _)⟩
  left_inv P := by
    ext1
    ext1
    refine hg.hom_ext ?_ (by simp)
    simp
  right_inv y := (cancel_mono (E.exactOrderSchemeι N)).mp <| by
    ext1
    simp

/-- The morphism to the exact-order scheme of a point `P` of exact order `N` of `E'`, followed by
the inclusion in `E`, is `P ≫ g`. -/
@[reassoc (attr := simp)]
theorem exactOrderPointsEquivOfIsPullback_apply_left_comp
    (P : {P : 𝟙_ (Over T.left) ⟶ Over.mk E'.structureMap // E'.IsOfExactOrder P N}) :
    (exactOrderPointsEquivOfIsPullback N hg h0 P).left ≫ (E.exactOrderLocus N).subschemeι =
      P.1.left ≫ g := by
  simp [exactOrderPointsEquivOfIsPullback]

/-- The point of exact order `N` of `E'` attached to a morphism `y` from `T` to the exact-order
scheme lies over the image of `y` in `E`. -/
@[reassoc (attr := simp)]
theorem exactOrderPointsEquivOfIsPullback_symm_apply_left_comp (y : T ⟶ E.exactOrderScheme N) :
    ((exactOrderPointsEquivOfIsPullback N hg h0).symm y).1.left ≫ g =
      (y ≫ E.exactOrderSchemeι N).left :=
  hg.lift_fst _ _ _

end BaseChange

/-! ### The exact-order scheme lies in `E[N]` -/

variable (E N) in
/-- **The exact-order scheme lies in the `N`-torsion**: multiplication by `N` kills the inclusion
of the exact-order scheme in `E`, scheme-theoretically. Equivalently
(`EllipticCurveGeom.exists_comp_torsionι_iff`), the inclusion factors through `E[N]`. -/
@[reassoc]
theorem exactOrderSchemeι_comp_mulBy : E.exactOrderSchemeι N ≫ E.mulBy N = 1 := by
  -- the inclusion is the image in `E` of the universal point of exact order `N`, a point of the
  -- base change of `E` to the exact-order scheme itself
  have hg := E.isPullback_baseChange (E.exactOrderScheme N).hom
  have h0 : (E.baseChange (E.exactOrderScheme N).hom).zero ≫
      (E.baseChangeIso (E.exactOrderScheme N).hom).hom ≫ pullback.fst _ _ =
        (E.exactOrderScheme N).hom ≫ E.zero := by
    simp
  let P := (exactOrderPointsEquivOfIsPullback N hg h0).symm (𝟙 _)
  have hP : P.1 ≫ (E.baseChange _).mulBy N = 1 := P.2.comp_mulBy_eq_one
  ext1
  have hι := exactOrderPointsEquivOfIsPullback_symm_apply_left_comp hg h0 (𝟙 _)
  rw [Category.id_comp] at hι
  rw [Over.comp_left, ← hι, Category.assoc, ← mulBy_left_comp_of_isPullback hg h0,
    ← Category.assoc, ← Over.comp_left, hP, hom_one_left, hom_one_left]
  simp

variable (E N) in
/-- **The exact-order scheme is finite** over `S` for `N ≠ 0`: it is a closed subscheme of the
`N`-torsion `E[N]`, which is finite over `S`. -/
instance isFinite_exactOrderScheme_hom [NeZero N] : IsFinite (E.exactOrderScheme N).hom := by
  let j := E.torsionLift (E.exactOrderSchemeι N) (E.exactOrderSchemeι_comp_mulBy N)
  have hj : j.left ≫ (E.torsionι N).left = (E.exactOrderSchemeι N).left := by
    rw [← Over.comp_left, torsionLift_torsionι]
  have : IsClosedImmersion (j.left ≫ (E.torsionι N).left) := hj ▸ inferInstance
  have : IsClosedImmersion j.left := .of_comp_isClosedImmersion j.left (E.torsionι N).left
  have := E.isFinite_torsion_hom (n := N) (by exact_mod_cast NeZero.ne N)
  rw [← Over.w j]
  infer_instance

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
