/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel

/-!
# The `n`-torsion of an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S`, with its group law (`EllipticCurveGeom.grpObj`),
and let `n` be an integer. The `n`-torsion `E[n]` of `E` is the scheme-theoretic kernel of
multiplication by `n`, `[n] : E ⟶ E` (`EllipticCurveGeom.mulBy`): the kernel of the homomorphism
`Grp.ofHom (E.mulBy n)` of group schemes over `S`, constructed in `TauCeti.GroupScheme`. It is a
group scheme over `S`, with a homomorphism `E[n] ⟶ E` of group schemes over `S`
(`EllipticCurveGeom.torsionι`).

On underlying schemes, `E[n]` is the fibre of `[n]` over the zero section, so its inclusion into `E`
is a closed immersion. Its points with values in any `Z` over `S` are the points of `E` with values
in `Z` killed by `[n]`, as a group. Its formation commutes with arbitrary base change: a pointed
morphism of elliptic curves `E' ⟶ E` forming a pullback square over a morphism of bases
`S' ⟶ S` induces a morphism `E'[n] ⟶ E[n]` forming a pullback square over `S' ⟶ S`.

Nothing here asserts that `E[n]` is finite or flat over `S`: for `n ≠ 0` it is finite locally
free of rank `n²`, which rests on the finiteness and flatness of `[n]`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsion E n`: the `n`-torsion `E[n]`, a group
  object of `Over S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionι E n`: its inclusion `E[n] ⟶ E`, a
  homomorphism of group schemes over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionLift`: the point of `E[n]` given by a point
  of `E` killed by `[n]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionPointsMulEquiv`: the points of `E[n]` with
  values in `Z` are the kernel of `[n]` on the points of `E` with values in `Z`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionMap`: the morphism `E'[n] ⟶ E[n]` induced
  by a base change square of elliptic curves.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isPullback_torsion`: `E[n]` is the fibre of `[n]`
  over the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isCommMonObj_torsion`: `E[n]` is a commutative group
  scheme over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isClosedImmersion_torsionι_left`: `E[n] ⟶ E` is a
  closed immersion; consequently `E[n]` is proper over `S`
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isProper_torsion_hom`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isPullback_torsionMap`: the `n`-torsion commutes
  with base change.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (n : ℤ)

/-! ### The `n`-torsion as a kernel -/

/-- **The `n`-torsion `E[n]` of an elliptic curve** `E` over a scheme `S`: the scheme-theoretic
kernel of multiplication by `n`, as a group object of `Over S`. -/
noncomputable def torsion : Grp (Over S) :=
  kernel (Grp.ofHom (E.mulBy n))

/-- The inclusion `E[n] ⟶ E` of the `n`-torsion of `E`, a morphism of `Over S`. -/
noncomputable def torsionι : (E.torsion n).X ⟶ Over.mk E.structureMap :=
  (kernel.ι (Grp.ofHom (E.mulBy n))).hom.hom

/-- The inclusion of the `n`-torsion is a homomorphism of group schemes over `S`. -/
instance isMonHom_torsionι : IsMonHom (E.torsionι n) :=
  (kernel.ι (Grp.ofHom (E.mulBy n))).hom.isMonHom_hom

/-- The inclusion of the `n`-torsion is a monomorphism. -/
instance mono_torsionι : Mono (E.torsionι n) :=
  GroupScheme.mono_kernel_ι_hom _

/-- **The `n`-torsion is commutative.** Its group law is the restriction of that of `E`. -/
instance isCommMonObj_torsion : IsCommMonObj (E.torsion n).X :=
  GroupScheme.isCommMonObj_kernel _

/-- Multiplication by `n` kills the `n`-torsion. -/
@[reassoc]
theorem torsionι_mulBy : E.torsionι n ≫ E.mulBy n = 1 :=
  GroupScheme.kernel_ι_comp_hom _

/-- The inclusion of the `n`-torsion, as a point of `E` with values in `E[n]`, is killed by `n`. -/
@[simp]
theorem torsionι_zpow : E.torsionι n ^ n = 1 := by
  rw [← comp_mulBy, torsionι_mulBy]

/-- Every point of `E` with values in `Z` that factors through the `n`-torsion is killed by
`n`. -/
@[simp]
theorem comp_torsionι_zpow {Z : Over S} (y : Z ⟶ (E.torsion n).X) :
    (y ≫ E.torsionι n) ^ n = 1 := by
  rw [← GrpObj.comp_zpow, torsionι_zpow, comp_one]

section Points

variable {E n} {Z : Over S}

/-- The point of the `n`-torsion `E[n]` given by a point `x` of `E` with values in `Z` which is
killed by multiplication by `n`. -/
noncomputable def torsionLift (x : Z ⟶ Over.mk E.structureMap) (hx : x ≫ E.mulBy n = 1) :
    Z ⟶ (E.torsion n).X :=
  GroupScheme.kernelLift x hx

/-- The point `torsionLift x hx` of `E[n]` maps to `x` in `E`. -/
@[reassoc (attr := simp)]
theorem torsionLift_torsionι (x : Z ⟶ Over.mk E.structureMap) (hx : x ≫ E.mulBy n = 1) :
    torsionLift x hx ≫ E.torsionι n = x :=
  GroupScheme.kernelLift_ι _ _

/-- Two points of the `n`-torsion `E[n]` agree if their images in `E` do. -/
theorem torsion_hom_ext {y y' : Z ⟶ (E.torsion n).X}
    (h : y ≫ E.torsionι n = y' ≫ E.torsionι n) : y = y' :=
  GroupScheme.kernel_hom_ext h

/-- A point of `E` with values in `Z` lies in the `n`-torsion `E[n]` exactly when it is killed by
multiplication by `n`. -/
theorem exists_comp_torsionι_iff (x : Z ⟶ Over.mk E.structureMap) :
    (∃ y : Z ⟶ (E.torsion n).X, y ≫ E.torsionι n = x) ↔ x ≫ E.mulBy n = 1 :=
  ⟨by rintro ⟨y, rfl⟩; simp, fun hx ↦ ⟨torsionLift x hx, by simp⟩⟩

variable (E n Z)

/-- **The points of `E[n]`.** The points of the `n`-torsion `E[n]` with values in `Z` form the
kernel of multiplication by `n` on the group of points of `E` with values in `Z`. This is
`TauCeti.GroupScheme.kernelPointsMulEquiv` for the kernel `E[n]` of `[n]`. -/
noncomputable def torsionPointsMulEquiv :
    (Z ⟶ (E.torsion n).X) ≃* (IsMonHom.monoidHom (E.mulBy n) Z).ker :=
  GroupScheme.kernelPointsMulEquiv _ Z

/-- A point of `E[n]` corresponds to its image in `E`. -/
@[simp]
theorem coe_torsionPointsMulEquiv_apply (y : Z ⟶ (E.torsion n).X) :
    (E.torsionPointsMulEquiv n Z y : Z ⟶ Over.mk E.structureMap) = y ≫ E.torsionι n :=
  GroupScheme.coe_kernelPointsMulEquiv_apply _ _ y

/-- The point of `E[n]` corresponding to a point `x` of `E` killed by `[n]` maps to `x` in `E`. -/
@[simp]
theorem torsionPointsMulEquiv_symm_apply_torsionι
    (x : (IsMonHom.monoidHom (E.mulBy n) Z).ker) :
    (E.torsionPointsMulEquiv n Z).symm x ≫ E.torsionι n = x := by
  rw [← coe_torsionPointsMulEquiv_apply, MulEquiv.apply_symm_apply]

end Points

/-! ### Underlying schemes -/

/-- **`E[n]` is the fibre of `[n]` over the zero section.** On underlying schemes, the square
formed by the inclusion `E[n] ⟶ E`, the structure morphism of `E[n]`, multiplication by `n` and the
zero section of `E` is a pullback square. -/
theorem isPullback_torsion :
    IsPullback (E.torsionι n).left (E.torsion n).X.hom (E.mulBy n).left E.zero :=
  (GroupScheme.isPullback_kernel_hom _).map (Over.forget S)

/-- The inclusion `E[n] ⟶ E` lies over `S`. -/
@[reassoc (attr := simp)]
theorem torsionι_left_structureMap :
    (E.torsionι n).left ≫ E.structureMap = (E.torsion n).X.hom :=
  Over.w (E.torsionι n)

/-- **The `n`-torsion is a closed subscheme.** The inclusion `E[n] ⟶ E` is a closed immersion,
being the base change of the zero section of the separated morphism `E ⟶ S`. -/
instance isClosedImmersion_torsionι_left : IsClosedImmersion (E.torsionι n).left := by
  have : IsClosedImmersion (E.zero ≫ E.structureMap) := by
    rw [zero_comp_structureMap]
    infer_instance
  have : IsClosedImmersion E.zero := .of_comp E.zero E.structureMap
  exact MorphismProperty.of_isPullback (E.isPullback_torsion n).flip this

/-- The `n`-torsion of an elliptic curve is proper over the base. -/
instance isProper_torsion_hom : IsProper (E.torsion n).X.hom := by
  rw [← torsionι_left_structureMap]
  infer_instance

/-! ### Base change -/

section BaseChange

variable {S' : Scheme.{u}} {E} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0

/-- The morphism `E'[n] ⟶ E[n]` induced by a morphism `g : E' ⟶ E` of elliptic curves lying over
`f : S' ⟶ S`, forming a pullback square with the structure morphisms and carrying the zero section
of `E'` to that of `E`. It is the restriction of `g` (`torsionMap_torsionι`). -/
noncomputable def torsionMap : (E'.torsion n).X.left ⟶ (E.torsion n).X.left :=
  (E.isPullback_torsion n).lift ((E'.torsionι n).left ≫ g) ((E'.torsion n).X.hom ≫ f) (by
    simp [← mulBy_left_comp_of_isPullback hg h0, (E'.isPullback_torsion n).w_assoc, h0])

/-- The morphism `E'[n] ⟶ E[n]` is the restriction of `g`. -/
@[reassoc (attr := simp)]
theorem torsionMap_torsionι : torsionMap n hg h0 ≫ (E.torsionι n).left = (E'.torsionι n).left ≫ g :=
  IsPullback.lift_fst _ _ _ _

/-- The morphism `E'[n] ⟶ E[n]` lies over `f`. -/
@[reassoc (attr := simp)]
theorem torsionMap_hom : torsionMap n hg h0 ≫ (E.torsion n).X.hom = (E'.torsion n).X.hom ≫ f :=
  IsPullback.lift_snd _ _ _ _

/-- **The `n`-torsion commutes with base change.** For a morphism `g : E' ⟶ E` of elliptic curves
lying over `f : S' ⟶ S`, forming a pullback square with the structure morphisms and carrying the
zero section of `E'` to that of `E`, the square formed by the induced morphism `E'[n] ⟶ E[n]`, the
structure morphisms of `E'[n]` and `E[n]` and `f` is a pullback square: `E'[n]` is the base change
of `E[n]` along `f`. -/
theorem isPullback_torsionMap :
    IsPullback (torsionMap n hg h0) (E'.torsion n).X.hom (E.torsion n).X.hom f := by
  refine IsPullback.of_isLimit' ⟨by simp⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ (E'.isPullback_torsion n).lift
      (hg.lift (s.fst ≫ (E.torsionι n).left) s.snd (by simp [s.condition]))
      s.snd ?_) ?_ ?_ ?_)
  · -- the point of `E'` given by `s` is killed by `[n]`, as its image in `E` is
    refine hg.hom_ext ?_ (by simp)
    simp [mulBy_left_comp_of_isPullback hg h0, (E.isPullback_torsion n).w, reassoc_of% s.condition,
      h0]
  · intro s
    refine (E.isPullback_torsion n).hom_ext ?_ ?_
    · simp
    · simp [s.condition]
  · intro s
    simp
  · intro s m h₁ h₂
    refine (E'.isPullback_torsion n).hom_ext ?_ (by simpa using h₂)
    refine hg.hom_ext ?_ ?_
    · simp [← h₁]
    · simp [← h₂]

end BaseChange

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
