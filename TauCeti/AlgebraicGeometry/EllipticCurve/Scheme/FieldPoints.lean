/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed

/-!
# Field points of the elliptic curve of a Weierstrass equation

Let `W` be an elliptic Weierstrass curve over a field `K` and let `E = toEllipticCurveGeom W` be
the elliptic curve over `Spec K` given by its projective model, with its scheme-theoretic group law
(`EllipticCurveGeom.grpObj`). This file identifies the group of points of `E` with values in the
base `Spec K` with the group `W.toAffine.Point` of Mathlib, and reads multiplication by an integer
`[n] : E ⟶ E` (`EllipticCurveGeom.mulBy`) on these points: it is `P ↦ n • P`.

Through this dictionary the equation-level theory of torsion points applies to the scheme
morphism `[n]`. The points of `E` killed by `[n]` are the `n`-torsion points of `W`, so there are
finitely many of them for `n ≠ 0`, and exactly `n.natAbs ^ 2` of them over a separably closed field
in which `n` is invertible. When `W` has infinitely many points over `K`, as over a separably
closed field, `[n]` is not the zero endomorphism for `n ≠ 0`, since the `n`-torsion is finite.

## Main definitions

* `WeierstrassCurve.toEllipticCurveGeomPointsMulEquiv W`: the isomorphism between the group of
  points of `toEllipticCurveGeom W` with values in `Spec K` and `Multiplicative W.toAffine.Point`.

## Main results

* `WeierstrassCurve.toAdd_toEllipticCurveGeomPointsMulEquiv` and
  `WeierstrassCurve.toEllipticCurveGeomPointsMulEquiv_symm_apply_left`: the isomorphism is the
  dictionary `projModelPointsEquiv` of sections of the projective model.
* `WeierstrassCurve.toAdd_toEllipticCurveGeomPointsMulEquiv_comp_mulBy`: multiplication by `n`
  on points of `toEllipticCurveGeom W` is multiplication by `n` on `W.toAffine.Point`.
* `WeierstrassCurve.comp_mulBy_eq_one_iff`: a point is killed by `[n]` exactly when the
  corresponding point of `W` is `n`-torsion.
* `WeierstrassCurve.finite_comp_mulBy_eq_one`: for `n ≠ 0`, finitely many points are killed by
  `[n]`.
* `WeierstrassCurve.natCard_comp_mulBy_eq_one`: over a separably closed field in which `n` is
  invertible, `n.natAbs ^ 2` points are killed by `[n]`.
* `WeierstrassCurve.toEllipticCurveGeom_mulBy_ne_one`: when `W` has infinitely many points over
  `K`, for instance over a separably closed field, `[n]` is not the zero endomorphism for `n ≠ 0`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

section Points

variable [DecidableEq K]

/-- **The group of points of the elliptic curve of `W` over a field.** For an elliptic Weierstrass
curve `W` over a field `K`, the points of the elliptic curve `toEllipticCurveGeom W` with values in
the base `Spec K`, with its group law `EllipticCurveGeom.grpObj`, form a group isomorphic to the
group `W.toAffine.Point` of Mathlib. It is the isomorphism `projModelPointsMulEquiv` of the group
of points of the projective model, transported along the identification
`toEllipticCurveGeomOverIso` of group schemes. -/
noncomputable def toEllipticCurveGeomPointsMulEquiv :
    (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap) ≃*
      Multiplicative W.toAffine.Point :=
  (Hom.mulEquivCongrRight (toEllipticCurveGeomOverIso W) _).trans W.projModelPointsMulEquiv

/-- The point of `W` corresponding to a point `x` of `toEllipticCurveGeom W` over `Spec K` is the
point corresponding under `projModelPointsEquiv` to the section `x.left` of the projective model,
read through `toEllipticCurveGeomIso`. -/
@[simp]
theorem toAdd_toEllipticCurveGeomPointsMulEquiv
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap) :
    (W.toEllipticCurveGeomPointsMulEquiv x).toAdd =
      W.projModelPointsEquiv ⟨x.left ≫ (toEllipticCurveGeomIso W).hom, by simpa using x.w⟩ := by
  -- `Hom.mulEquivCongrRight` is composition with `(toEllipticCurveGeomOverIso W).hom`; its `simps`
  -- lemma is stated on the carrier of a `MonCat` object, so it does not rewrite a morphism
  have h : Hom.mulEquivCongrRight (toEllipticCurveGeomOverIso W) _ x =
      x ≫ (toEllipticCurveGeomOverIso W).hom :=
    rfl
  rw [toEllipticCurveGeomPointsMulEquiv, MulEquiv.trans_apply, h, toAdd_projModelPointsMulEquiv]
  simp

/-- The point of `toEllipticCurveGeom W` over `Spec K` corresponding to a point `P` of `W` is the
section of the projective model corresponding to `P` under `projModelPointsEquiv`, read through
`toEllipticCurveGeomIso`. -/
@[simp]
theorem toEllipticCurveGeomPointsMulEquiv_symm_apply_left (P : Multiplicative W.toAffine.Point) :
    (W.toEllipticCurveGeomPointsMulEquiv.symm P).left =
      (W.projModelPointsEquiv.symm P.toAdd).1 ≫ (toEllipticCurveGeomIso W).inv := by
  -- the inverse of `Hom.mulEquivCongrRight` is composition with
  -- `(toEllipticCurveGeomOverIso W).inv`; its `simps` lemma is stated on the carrier of a `MonCat`
  -- object, so it does not rewrite a morphism
  have h : (Hom.mulEquivCongrRight (toEllipticCurveGeomOverIso W) _).symm
      (W.projModelPointsMulEquiv.symm P) =
        W.projModelPointsMulEquiv.symm P ≫ (toEllipticCurveGeomOverIso W).inv :=
    rfl
  rw [toEllipticCurveGeomPointsMulEquiv, MulEquiv.symm_trans_apply, h, Over.comp_left,
    projModelPointsMulEquiv_symm_apply_left, toEllipticCurveGeomOverIso_inv_left]

/-- **Multiplication by `n` on field points.** Through `toEllipticCurveGeomPointsMulEquiv`,
multiplication by an integer `n` on the elliptic curve `toEllipticCurveGeom W` sends the point
corresponding to `P` to the point corresponding to `n • P`. -/
theorem toAdd_toEllipticCurveGeomPointsMulEquiv_comp_mulBy
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap) (n : ℤ) :
    (W.toEllipticCurveGeomPointsMulEquiv (x ≫ (toEllipticCurveGeom W).mulBy n)).toAdd =
      n • (W.toEllipticCurveGeomPointsMulEquiv x).toAdd := by
  rw [EllipticCurveGeom.comp_mulBy, map_zpow, toAdd_zpow]

/-- A point of `toEllipticCurveGeom W` with values in `Spec K` is killed by multiplication by `n`
exactly when the corresponding point of `W` is an `n`-torsion point. -/
theorem comp_mulBy_eq_one_iff
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap) (n : ℤ) :
    x ≫ (toEllipticCurveGeom W).mulBy n = 1 ↔
      n • (W.toEllipticCurveGeomPointsMulEquiv x).toAdd = 0 := by
  rw [← toAdd_toEllipticCurveGeomPointsMulEquiv_comp_mulBy, toAdd_eq_zero,
    MulEquiv.map_eq_one_iff]

end Points

-- The points of `toEllipticCurveGeom W` killed by `[n]` correspond to the `n`-torsion points of
-- `W`.
private noncomputable def killedByMulByEquiv [DecidableEq K] (n : ℤ) :
    {x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap //
      x ≫ (toEllipticCurveGeom W).mulBy n = 1} ≃ {P : W.toAffine.Point | n • P = 0} :=
  (W.toEllipticCurveGeomPointsMulEquiv.toEquiv.trans Multiplicative.toAdd).subtypeEquiv fun x ↦
    W.comp_mulBy_eq_one_iff x n

/-- For a nonzero integer `n`, only finitely many points of `toEllipticCurveGeom W` with values in
`Spec K` are killed by multiplication by `n`. -/
theorem finite_comp_mulBy_eq_one {n : ℤ} (hn : n ≠ 0) :
    Finite {x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap //
      x ≫ (toEllipticCurveGeom W).mulBy n = 1} := by
  classical
  have := W.finite_torsionBy hn
  exact .of_equiv _ ((W.killedByMulByEquiv n).trans
    (Equiv.subtypeEquivRight fun P ↦ (Submodule.mem_torsionBy_iff _ _).symm)).symm

/-- **The field points of `E[n]`.** Over a separably closed field `K` in which the integer `n` is
invertible, exactly `n.natAbs ^ 2` points of `toEllipticCurveGeom W` with values in `Spec K` are
killed by multiplication by `n`. -/
theorem natCard_comp_mulBy_eq_one [IsSepClosed K] {n : ℤ} (hn : (n : K) ≠ 0) :
    Nat.card {x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap //
      x ≫ (toEllipticCurveGeom W).mulBy n = 1} = n.natAbs ^ 2 := by
  classical
  rw [Nat.card_congr (W.killedByMulByEquiv n), W.toAffine.natCard_setOf_zsmul_eq_zero hn]

/-- **Multiplication by a nonzero integer is not the zero endomorphism** of the elliptic curve
`toEllipticCurveGeom W`, when `W` has infinitely many points over `K`: only finitely many of them
are `n`-torsion. This holds over every separably closed field
(`WeierstrassCurve.Affine.infinite_point`). -/
theorem toEllipticCurveGeom_mulBy_ne_one [Infinite W.toAffine.Point] {n : ℤ} (hn : n ≠ 0) :
    (toEllipticCurveGeom W).mulBy n ≠ 1 := by
  classical
  intro h
  have := W.finite_comp_mulBy_eq_one hn
  -- every point is killed by `[n]`, so `W` has finitely many points
  have : Finite (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk (toEllipticCurveGeom W).structureMap) :=
    .of_injective (fun x ↦ (⟨x, by rw [h, MonObj.comp_one]⟩ :
      {x // x ≫ (toEllipticCurveGeom W).mulBy n = 1})) fun _ _ ↦ congrArg Subtype.val
  have : Finite W.toAffine.Point :=
    .of_equiv _ (W.toEllipticCurveGeomPointsMulEquiv.toEquiv.trans Multiplicative.toAdd)
  exact not_finite W.toAffine.Point

end WeierstrassCurve
