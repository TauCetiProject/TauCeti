/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange

/-!
# Galois actions on elliptic-curve points

Let `W` be a Weierstrass curve over a field `F`. An `F`-algebra equivalence `K ≃ₐ[F] L`
acts on the coordinates of the points of `W` after base change from `F` to `K` and `L`.
Mathlib's `WeierstrassCurve.Affine.Point.map` already gives the underlying additive map. This
file packages that map as an additive equivalence and, when `K = L`, as the Galois action on
points. Restricting the equivalence to `N`-torsion gives the corresponding finite-level action.
Both actions are bundled as monoid homomorphisms into the additive automorphism group, viewed
multiplicatively so composition has the usual action order.

The finite-level action is the input needed to state Galois equivariance of the Weil pairing.
Over a finite base field, the distinguished Galois automorphism is Frobenius, so the same action
also supplies the point-side representation used in the Hasse-bound argument.

## Main definitions

* `WeierstrassCurve.Affine.Point.mapEquiv`: transport of points along an algebra equivalence.
* `TauCeti.pointGaloisAction`: the Galois action on points.
* `TauCeti.torsionGaloisAction`: its restriction to `N`-torsion.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 and V.1.
-/

public section

open scoped WeierstrassCurve

namespace WeierstrassCurve.Affine.Point

variable {F K L M : Type*} [Field F] [Field K] [Field L] [Field M]
  [DecidableEq K] [DecidableEq L] [DecidableEq M]
  [Algebra F K] [Algebra F L] [Algebra F M] (W : _root_.WeierstrassCurve F) [W.IsElliptic]

/-- **Transport of elliptic-curve points along an algebra equivalence.** This is Mathlib's
additive point map, with inverse induced by the inverse algebra equivalence. -/
noncomputable def mapEquiv (e : K ≃ₐ[F] L) :
    (W⁄K).toAffine.Point ≃+ (W⁄L).toAffine.Point where
  toFun := Point.map e.toAlgHom
  invFun := Point.map e.symm.toAlgHom
  left_inv P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · simp only [Point.map_some]
      congr <;> exact e.symm_apply_apply _
  right_inv P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · simp only [Point.map_some]
      congr <;> exact e.apply_symm_apply _
  map_add' := map_add (Point.map e.toAlgHom)

omit [W.IsElliptic] in
@[simp]
theorem mapEquiv_apply (e : K ≃ₐ[F] L) (P : (W⁄K).toAffine.Point) :
    mapEquiv W e P = Point.map e.toAlgHom P :=
  by rw [mapEquiv]; rfl

omit [W.IsElliptic] in
@[simp]
theorem mapEquiv_symm_apply (e : K ≃ₐ[F] L) (P : (W⁄L).toAffine.Point) :
    (mapEquiv W e).symm P = Point.map e.symm.toAlgHom P :=
  by rw [mapEquiv]; rfl

omit [W.IsElliptic] in
@[simp]
theorem mapEquiv_refl : mapEquiv W (AlgEquiv.refl : K ≃ₐ[F] K) = AddEquiv.refl _ := by
  ext P
  exact Point.map_id P

omit [W.IsElliptic] in
@[simp]
theorem mapEquiv_trans (e : K ≃ₐ[F] L) (f : L ≃ₐ[F] M) :
    mapEquiv W (e.trans f) = (mapEquiv W e).trans (mapEquiv W f) := by
  ext P
  exact (Point.map_map e.toAlgHom f.toAlgHom P).symm

omit [W.IsElliptic] in
@[simp]
theorem mapEquiv_symm (e : K ≃ₐ[F] L) :
    (mapEquiv W e).symm = mapEquiv W e.symm :=
  by
    ext P
    rw [mapEquiv_symm_apply, mapEquiv_apply]

omit [W.IsElliptic] in
@[simp]
theorem mapEquiv_some (e : K ≃ₐ[F] L) {x y : K}
    (h : (W⁄K).toAffine.Nonsingular x y) :
    mapEquiv W e (.some x y h) =
      .some (e.toAlgHom x) (e.toAlgHom y)
        ((W.toAffine.baseChange_nonsingular (f := e.toAlgHom) e.toAlgHom.injective x y).mpr h) := by
  rw [mapEquiv_apply, Point.map_some]

end WeierstrassCurve.Affine.Point

namespace TauCeti

open WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K]
  (W : _root_.WeierstrassCurve F) [W.IsElliptic]

/-- **The Galois action on the points of an elliptic curve.** An `F`-automorphism of
`K` acts by applying it to both affine coordinates and fixes the point at infinity. -/
noncomputable def pointGaloisAction :
    (K ≃ₐ[F] K) →* Multiplicative (AddAut ((W⁄K).toAffine.Point)) where
  toFun e := Multiplicative.ofAdd (Affine.Point.mapEquiv W e)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro P
    change Affine.Point.mapEquiv W (1 : K ≃ₐ[F] K) P = P
    rw [Affine.Point.mapEquiv_apply]
    rcases P with _ | ⟨x, y, h⟩ <;> rfl
  map_mul' e f := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro P
    change Affine.Point.mapEquiv W (e * f) P =
      Affine.Point.mapEquiv W e (Affine.Point.mapEquiv W f P)
    rw [Affine.Point.mapEquiv_apply, Affine.Point.mapEquiv_apply,
      Affine.Point.mapEquiv_apply]
    exact (Affine.Point.map_map f.toAlgHom e.toAlgHom P).symm

omit [W.IsElliptic] in
@[simp]
theorem pointGaloisAction_apply (e : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) :
    Multiplicative.toAdd (pointGaloisAction W e) P = Affine.Point.map e.toAlgHom P :=
  by
    rw [pointGaloisAction]
    change Affine.Point.mapEquiv W e P = Affine.Point.map e.toAlgHom P
    rw [Affine.Point.mapEquiv_apply]

omit [W.IsElliptic] in
@[simp]
theorem pointGaloisAction_apply_some (e : K ≃ₐ[F] K) {x y : K}
    (h : (W⁄K).toAffine.Nonsingular x y) :
    Multiplicative.toAdd (pointGaloisAction W e) (.some x y h) =
      .some (e.toAlgHom x) (e.toAlgHom y)
        ((W.toAffine.baseChange_nonsingular (f := e.toAlgHom) e.toAlgHom.injective x y).mpr h) :=
  by rw [pointGaloisAction_apply, Affine.Point.map_some]

/-- **The Galois action on `N`-torsion.** This is the restriction of
`pointGaloisAction` to the subgroup killed by `N`. -/
noncomputable def torsionGaloisAction (N : ℤ) :
    (K ≃ₐ[F] K) →*
      Multiplicative (AddAut (AddSubgroup.torsionBy ((W⁄K).toAffine.Point) N)) where
  toFun e := Multiplicative.ofAdd ((Affine.Point.mapEquiv W e).torsionByCongr N)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro P
    apply Subtype.ext
    change ↑(((Affine.Point.mapEquiv W (1 : K ≃ₐ[F] K)).torsionByCongr N) P) = P.1
    rw [AddEquiv.torsionByCongr_apply_coe, Affine.Point.mapEquiv_apply]
    rcases P.1 with _ | ⟨x, y, h⟩ <;> rfl
  map_mul' e f := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro P
    apply Subtype.ext
    rw [toAdd_ofAdd, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, AddAut.add_apply]
    simp only [AddEquiv.torsionByCongr_apply_coe, Affine.Point.mapEquiv_apply]
    exact (Affine.Point.map_map f.toAlgHom e.toAlgHom P.1).symm

omit [W.IsElliptic] in
@[simp]
theorem torsionGaloisAction_apply_coe (N : ℤ) (e : K ≃ₐ[F] K)
    (P : AddSubgroup.torsionBy (W⁄K).toAffine.Point N) :
    ((Multiplicative.toAdd (torsionGaloisAction W N e) P :
      AddSubgroup.torsionBy (W⁄K).toAffine.Point N) : (W⁄K).toAffine.Point) =
      Multiplicative.toAdd (pointGaloisAction W e) P :=
  by
    rw [torsionGaloisAction, pointGaloisAction]
    change ↑(((Affine.Point.mapEquiv W e).torsionByCongr N) P) =
      Affine.Point.mapEquiv W e P
    rw [AddEquiv.torsionByCongr_apply_coe]

omit [W.IsElliptic] in
@[simp]
theorem torsionGaloisAction_apply_mk (N : ℤ) (e : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) (hP : P ∈ AddSubgroup.torsionBy (W⁄K).toAffine.Point N) :
    Multiplicative.toAdd (torsionGaloisAction W N e) ⟨P, hP⟩ =
      ⟨Affine.Point.map e.toAlgHom P, by
        apply (Submodule.mem_torsionBy_iff _ _).mpr
        rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp hP, map_zero]⟩ :=
  by
    rw [torsionGaloisAction]
    change ((Affine.Point.mapEquiv W e).torsionByCongr N) ⟨P, hP⟩ =
      ⟨Affine.Point.map e.toAlgHom P, _⟩
    apply Subtype.ext
    rw [AddEquiv.torsionByCongr_apply_coe, Affine.Point.mapEquiv_apply]

end TauCeti

end
