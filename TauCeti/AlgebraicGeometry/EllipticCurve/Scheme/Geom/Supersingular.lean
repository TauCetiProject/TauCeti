/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite
import TauCeti.AlgebraicGeometry.RationalPoint.Geometric

/-!
# Supersingular elliptic curves over a field

An elliptic curve `E` over a field `K` is **supersingular at `p`** when the finite group scheme
`E[p]` is connected (`EllipticCurveGeom.IsSupersingular`). For `p` the characteristic of `K` this
is the connected case of the connected–étale dichotomy of `E[p]`: the curve is supersingular when
`E[p]` is infinitesimal, and ordinary otherwise. The definition is intrinsic to the group scheme
and uses no Weierstrass equation.

`E[p]` is finite over `K` for `p ≠ 0`, with the rational point `0`. Such a scheme is connected
exactly when it has a single point, and then that point is `0`, whose residue field is `K`; so
`E[p]` is connected exactly when it has no point with values in an algebraically closed field
other than `0` (`EllipticCurveGeom.isSupersingular_iff_of_isPullback`). These points are read on
any elliptic curve `E'` over an algebraically closed field `Ω` which is a base change of `E`.

For the curve of an elliptic Weierstrass equation `W`, the base change of its projective model to
the algebraic closure of `K` is the projective model of `W` there, and the points of `E[p]` with
values in it are the `p`-torsion points of `W` over the algebraic closure. Hence `E[p]` is connected
exactly when `W` is supersingular at `p` in the sense of `WeierstrassCurve.IsSupersingular`
(`WeierstrassCurve.isSupersingular_toEllipticCurveGeom_iff`). The comparison holds over imperfect
fields too: both sides read the points over an algebraic closure, as they must. Over `𝔽₂(t)` the
curve `y² + xy = x³ + t` is ordinary, and its point `(0, √t)` of order two is defined only over
the purely inseparable extension `𝔽₂(√t)`; there `E[2]` has two points, so it is not connected.

For `p = 0` the definition is the connectedness of `E[0] = E`, which holds, while no curve is
supersingular at `0` in the sense of `WeierstrassCurve.IsSupersingular`; the comparison needs
`p ≠ 0`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsSupersingular`: `E[p]` is connected.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isSupersingular_iff_of_isPullback`: for `p ≠ 0`,
  `E` is supersingular at `p` if and only if `E'[p]` has no point with values in `Ω` other than
  zero, for a base change `E'` of `E` to an algebraically closed field `Ω`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isSupersingular_iff_of_isAlgClosed`: the case
  where `K` itself is algebraically closed.
* `WeierstrassCurve.isSupersingular_toEllipticCurveGeom_iff`: for `p ≠ 0`, the elliptic curve of
  an elliptic Weierstrass equation `W` is supersingular at `p` if and only if `W` is.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {K : Type u} [Field K]

/-- **A supersingular elliptic curve over a field.** An elliptic curve `E` over a field `K` is
supersingular at `p` when the finite group scheme `E[p]` is connected. For `p` the characteristic
of `K` this says that `E[p]` is infinitesimal. For `p ≠ 0` it says that `E[p]` has no nonzero point
over an algebraically closed field (`isSupersingular_iff_of_isPullback`); for the curve of a
Weierstrass equation it is supersingularity in the sense of `WeierstrassCurve.IsSupersingular`
(`WeierstrassCurve.isSupersingular_toEllipticCurveGeom_iff`). -/
def IsSupersingular (p : ℕ) (E : EllipticCurveGeom (Spec (.of K))) : Prop :=
  ConnectedSpace (E.torsion p).X.left

/-- An elliptic curve `E` over a field is supersingular at `p` exactly when `E[p]` is connected. -/
theorem isSupersingular_iff {p : ℕ} {E : EllipticCurveGeom (Spec (.of K))} :
    E.IsSupersingular p ↔ ConnectedSpace (E.torsion p).X.left :=
  Iff.rfl

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] {E : EllipticCurveGeom (Spec (.of K))}
  {E' : EllipticCurveGeom (Spec (.of Ω))} {g : E'.carrier ⟶ E.carrier}

/-- **Supersingularity is read on geometric points.** Let `E'` be the base change of an elliptic
curve `E` over `K` to an algebraically closed field `Ω` over `K`, through a morphism `g : E' ⟶ E`
forming a pullback square over `Spec Ω ⟶ Spec K` and carrying zero to zero. For `p ≠ 0`, `E` is
supersingular at `p` if and only if the only point of `E'[p]` with values in `Ω` is zero. -/
theorem isSupersingular_iff_of_isPullback
    (hg : IsPullback g E'.structureMap E.structureMap
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (h0 : E'.zero ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ E.zero) {p : ℕ}
    (hp : p ≠ 0) :
    E.IsSupersingular p ↔ ∀ y : 𝟙_ (Over (Spec (.of Ω))) ⟶ (E'.torsion p).X, y = 1 := by
  have : IsFinite (E.torsion p).X.hom := E.isFinite_torsion_hom (by exact_mod_cast hp)
  have hs : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ (E.torsion p).X).left ≫ (E.torsion p).X.hom = 𝟙 _ :=
    Over.w _
  rw [isSupersingular_iff,
    Scheme.Hom.connectedSpace_iff_forall_eq_comp_of_isAlgClosed (Ω := Ω) _ hs]
  set q := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  -- `E'[p]` is the base change of `E[p]` along `q`, through `t`
  set t := torsionMap p hg h0
  have ht : IsPullback t (E'.torsion p).X.hom (E.torsion p).X.hom q := isPullback_torsionMap p hg h0
  -- `t` carries the zero point of `E'[p]` to the zero point of `E[p]`
  have h1 := one_left_torsionMap (p : ℤ) hg h0
  refine ⟨fun h y ↦ Over.OverMorphism.ext (ht.hom_ext ?_ ?_), fun h a ha ↦ ?_⟩
  · rw [h1]
    exact h _ (by rw [Category.assoc, ht.w, ← Category.assoc, Over.w y]; simp)
  · simp only [Over.w]
  · -- `a` is the image under `t` of the point of `E'[p]` it defines, which is zero
    have hy := h (Over.homMk (ht.lift a (𝟙 _) (by simpa using ha)) (by simp))
    rw [← h1, ← ht.lift_fst a (𝟙 _) (by simpa using ha), ← hy]
    simp [t]

/-- **Supersingularity over an algebraically closed field.** For `p ≠ 0`, an elliptic curve `E`
over an algebraically closed field `K` is supersingular at `p` if and only if the only point of
`E[p]` with values in `K` is zero. -/
theorem isSupersingular_iff_of_isAlgClosed [IsAlgClosed K] {p : ℕ} (hp : p ≠ 0) :
    E.IsSupersingular p ↔ ∀ y : 𝟙_ (Over (Spec (.of K))) ⟶ (E.torsion p).X, y = 1 := by
  have hq : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  exact isSupersingular_iff_of_isPullback (g := 𝟙 _) (by rw [hq]; exact IsPullback.of_id_fst)
    (by simp) hp

end TauCeti.AlgebraicGeometry.EllipticCurveGeom

namespace WeierstrassCurve

open TauCeti.AlgebraicGeometry

variable {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **The comparison of the two notions of supersingularity.** For an elliptic Weierstrass curve
`W` over a field `K` and `p ≠ 0`, the elliptic curve of the projective model of `W` is
supersingular at `p`, that is `E[p]` is connected, if and only if `W` is supersingular at `p`, that
is `W` has no nonzero `p`-torsion point over the algebraic closure of `K`. -/
theorem isSupersingular_toEllipticCurveGeom_iff {p : ℕ} (hp : p ≠ 0) :
    (toEllipticCurveGeom W).IsSupersingular p ↔ W.IsSupersingular p := by
  classical
  let φ := algebraMap K (AlgebraicClosure K)
  rw [EllipticCurveGeom.isSupersingular_iff_of_isPullback
    (W.isPullback_toEllipticCurveGeomIso_hom_projModelBaseChange φ)
    (W.zero_toEllipticCurveGeomIso_hom_projModelBaseChange φ) hp, isSupersingular_iff_forall]
  -- the points of `E[p]` over the algebraic closure are the `p`-torsion points of `W` there
  let e := (W.map φ).toEllipticCurveGeomTorsionPointsMulEquiv p
  refine ⟨fun h P hP ↦ ?_, fun h y ↦ e.injective ?_⟩
  · have := congrArg (fun y ↦ (e y).toAdd.val)
      (h (e.symm (.ofAdd ⟨P, AddSubgroup.torsionBy.nsmul_iff.mpr hP⟩)))
    simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, map_one, toAdd_one,
      ZeroMemClass.coe_zero] at this
    exact this
  · rw [map_one]
    exact Multiplicative.toAdd.injective
      (Subtype.ext (h _ (AddSubgroup.torsionBy.nsmul_iff.mp (e y).toAdd.property)))

end WeierstrassCurve
