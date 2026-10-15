/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Hom
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.Data.ZMod.MonoidHomEquiv

/-!
# The `n`-torsion of an elliptic curve over a scheme

Let `E` be an elliptic curve over a scheme `S`, with its group law (`EllipticCurveGeom.grpObj`),
and let `n` be an integer. The `n`-torsion `E[n]` of `E` is the scheme-theoretic kernel of
multiplication by `n`, `[n] : E ⟶ E` (`EllipticCurveGeom.mulBy`): the kernel of the homomorphism
`Grp.ofHom (E.mulBy n)` of group schemes over `S`, constructed in `TauCeti.GroupScheme`. It is a
group scheme over `S`, with a homomorphism `E[n] ⟶ E` of group schemes over `S`
(`EllipticCurveGeom.torsionι`). The construction specializes `TauCeti.GroupScheme.torsion` to
`E.toCommGrp`.

On underlying schemes, `E[n]` is the fibre of `[n]` over the zero section, so its inclusion into `E`
is a closed immersion. Its points with values in any `Z` over `S` are the points of `E` with values
in `Z` killed by `[n]`, as a group. Its formation commutes with arbitrary base change: a pointed
morphism of elliptic curves `E' ⟶ E` forming a pullback square over a morphism of bases
`S' ⟶ S` induces a morphism `E'[n] ⟶ E[n]` forming a pullback square over `S' ⟶ S`.

Multiplication transitions `E[mn] ⟶ E[n]` and inclusions `E[m] ⟶ E[mn]` specialize the
commutative group-scheme API. Their identity and composition laws include transports between
equal indices, supplying the coherence of torsion towers.

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
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionPointsEquiv`: the points `x` of `E` with
  values in `Z` with `x ^ n = 1` are the points of `E[n]` with values in `Z`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionMap`: the morphism `E'[n] ⟶ E[n]` induced
  by a base change square of elliptic curves.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionPairHom E N`: the universal pair of points
  of `E[N]`, the homomorphism `(ℤ/Nℤ)² →* E(E[N] ×_S E[N])` sending `(a, b)` to `aP + bQ`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsion_eq_kernel`: `E[n]` is the kernel of the
  integer `n` of the endomorphism ring of `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isPullback_torsion`: `E[n]` is the fibre of `[n]`
  over the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isCommMonObj_torsion`: `E[n]` is a commutative group
  scheme over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isClosedImmersion_torsionι_left`: `E[n] ⟶ E` is a
  closed immersion; consequently `E[n]` is proper over `S`
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isProper_torsion_hom`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.ker_torsionι_left`: as a closed subscheme of `E`,
  `E[n]` is the inverse image `[n]⁻¹[0]` of the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.locallyOfFinitePresentation_torsion_hom`: `E[n]` is
  locally of finite presentation over `S`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isPullback_torsionMap`: the `n`-torsion commutes
  with base change.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isPullback_torsionMap_torsionι` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.ker_torsionι_left_of_isPullback`: `E'[n]` is the
  inverse image of `E[n]` under `E' ⟶ E`, as a closed subscheme.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_comp_torsionPairHom`: for `N ≠ 0`,
  `E[N] ×_S E[N]` represents homomorphisms `(ℤ/Nℤ)² →* E(Z)`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

section Torsion

variable (n : ℤ)

/-! ### The `n`-torsion as a kernel -/

/-- **The `n`-torsion `E[n]` of an elliptic curve** `E` over a scheme `S`: the scheme-theoretic
kernel of multiplication by `n`, as a group object of `Over S`. -/
noncomputable def torsion : Grp (Over S) :=
  GroupScheme.torsion E.toCommGrp n

/-- **The `n`-torsion is the kernel of the endomorphism `n`.** The `n`-torsion of `E` is the kernel
of the image in `Grp (Over S)` of the integer `n` of the endomorphism ring `End E.toCommGrp`. -/
theorem torsion_eq_kernel :
    E.torsion n = kernel ((CommGrp.forget₂Grp (Over S)).map (n : End E.toCommGrp)) := by
  rw [torsion, GroupScheme.torsion_eq_kernel]

/-- The inclusion `E[n] ⟶ E` of the `n`-torsion of `E`, a morphism of `Over S`. -/
noncomputable def torsionι : (E.torsion n).X ⟶ Over.mk E.structureMap :=
  GroupScheme.torsionι E.toCommGrp n

/-- The inclusion of the `n`-torsion is a homomorphism of group schemes over `S`. -/
instance isMonHom_torsionι : IsMonHom (E.torsionι n) :=
  GroupScheme.isMonHom_torsionι E.toCommGrp n

/-- The inclusion of the `n`-torsion is a monomorphism. -/
instance mono_torsionι : Mono (E.torsionι n) :=
  GroupScheme.mono_torsionι E.toCommGrp n

/-- **The `n`-torsion is commutative.** Its group law is the restriction of that of `E`. -/
instance isCommMonObj_torsion : IsCommMonObj (E.torsion n).X :=
  GroupScheme.isCommMonObj_torsion E.toCommGrp n

/-- Multiplication by `n` kills the `n`-torsion. -/
@[reassoc]
theorem torsionι_mulBy : E.torsionι n ≫ E.mulBy n = 1 := by
  rw [comp_mulBy]
  exact GroupScheme.torsionι_zpow E.toCommGrp n

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
  GroupScheme.torsionLift x (by simpa only [comp_mulBy] using hx)

/-- The point `torsionLift x hx` of `E[n]` maps to `x` in `E`. -/
@[reassoc (attr := simp)]
theorem torsionLift_torsionι (x : Z ⟶ Over.mk E.structureMap) (hx : x ≫ E.mulBy n = 1) :
    torsionLift x hx ≫ E.torsionι n = x :=
  GroupScheme.torsionLift_ι _ _

/-- Two points of the `n`-torsion `E[n]` agree if their images in `E` do. -/
theorem torsion_hom_ext {y y' : Z ⟶ (E.torsion n).X}
    (h : y ≫ E.torsionι n = y' ≫ E.torsionι n) : y = y' :=
  GroupScheme.torsion_hom_ext E.toCommGrp h

/-- A point of `E` with values in `Z` lies in the `n`-torsion `E[n]` exactly when it is killed by
multiplication by `n`. -/
theorem exists_comp_torsionι_iff (x : Z ⟶ Over.mk E.structureMap) :
    (∃ y : Z ⟶ (E.torsion n).X, y ≫ E.torsionι n = x) ↔ x ≫ E.mulBy n = 1 :=
  ⟨by rintro ⟨y, rfl⟩; simp, fun hx ↦ ⟨torsionLift x hx, by simp⟩⟩

variable (E n Z)

/-- **The points of `E[n]`.** The points of the `n`-torsion `E[n]` with values in `Z` form the
kernel of multiplication by `n` on the group of points of `E` with values in `Z`. This specializes
`TauCeti.GroupScheme.torsionPointsMulEquiv`, identifying multiplication by `n` with `n`-th powers.
-/
noncomputable def torsionPointsMulEquiv :
    (Z ⟶ (E.torsion n).X) ≃* (IsMonHom.monoidHom (E.mulBy n) Z).ker :=
  (GroupScheme.torsionPointsMulEquiv E.toCommGrp n Z).trans <| MulEquiv.subgroupCongr <|
    congrArg MonoidHom.ker <| MonoidHom.ext fun x ↦ (E.comp_mulBy x n).symm

/-- A point of `E[n]` corresponds to its image in `E`. -/
@[simp]
theorem coe_torsionPointsMulEquiv_apply (y : Z ⟶ (E.torsion n).X) :
    (E.torsionPointsMulEquiv n Z y : Z ⟶ Over.mk E.structureMap) = y ≫ E.torsionι n :=
  GroupScheme.coe_torsionPointsMulEquiv_apply E.toCommGrp n Z y

/-- The point of `E[n]` corresponding to a point `x` of `E` killed by `[n]` maps to `x` in `E`. -/
@[simp]
theorem torsionPointsMulEquiv_symm_apply_torsionι
    (x : (IsMonHom.monoidHom (E.mulBy n) Z).ker) :
    (E.torsionPointsMulEquiv n Z).symm x ≫ E.torsionι n = x := by
  rw [← coe_torsionPointsMulEquiv_apply, MulEquiv.apply_symm_apply]

/-- The points `x` of `E` with values in `Z` with `x ^ n = 1` are the points of `E[n]` with values
in `Z`. This is `torsionPointsMulEquiv`, with the kernel of `[n]` written as a subtype. -/
noncomputable def torsionPointsEquiv :
    {x : Z ⟶ Over.mk E.structureMap // x ^ n = 1} ≃ (Z ⟶ (E.torsion n).X) :=
  (Equiv.subtypeEquivRight fun x ↦ by
    rw [MonoidHom.mem_ker, IsMonHom.monoidHom_apply, comp_mulBy]).trans
    (E.torsionPointsMulEquiv n Z).symm.toEquiv

/-- The point of `E[n]` corresponding to a point `x` of `E` with `x ^ n = 1` maps to `x` in `E`. -/
@[simp]
theorem torsionPointsEquiv_apply_torsionι (x : {x : Z ⟶ Over.mk E.structureMap // x ^ n = 1}) :
    E.torsionPointsEquiv n Z x ≫ E.torsionι n = x :=
  E.torsionPointsMulEquiv_symm_apply_torsionι n Z _

/-- A point of `E[n]` corresponds to its image in `E`. -/
@[simp]
theorem coe_torsionPointsEquiv_symm_apply (y : Z ⟶ (E.torsion n).X) :
    ((E.torsionPointsEquiv n Z).symm y : Z ⟶ Over.mk E.structureMap) = y ≫ E.torsionι n :=
  E.coe_torsionPointsMulEquiv_apply n Z y

end Points

/-! ### Underlying schemes -/

/-- **`E[n]` is the fibre of `[n]` over the zero section.** On underlying schemes, the square
formed by the inclusion `E[n] ⟶ E`, the structure morphism of `E[n]`, multiplication by `n` and the
zero section of `E` is a pullback square. -/
theorem isPullback_torsion :
    IsPullback (E.torsionι n).left (E.torsion n).X.hom (E.mulBy n).left E.zero :=
  by simpa [torsion, torsionι, ← mulBy_eq_zpow] using
    (GroupScheme.isPullback_torsionι E.toCommGrp n).map (Over.forget S)

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

/-- **`E[n]` is the inverse image of the zero section under `[n]`**: the ideal sheaf of the closed
subscheme `E[n]` of `E` is the inverse image along `[n]` of the ideal sheaf of the zero section. -/
theorem ker_torsionι_left :
    (E.torsionι n).left.ker = E.zero.ker.comap (E.mulBy n).left := by
  have := E.zero.isClosedImmersion_of_comp_eq_id E.zero_comp
  exact Scheme.IdealSheafData.ker_eq_comap_of_isPullback _ (E.isPullback_torsion n)

/-- The `n`-torsion of an elliptic curve is proper over the base. -/
instance isProper_torsion_hom : IsProper (E.torsion n).X.hom := by
  rw [← torsionι_left_structureMap]
  infer_instance

/-- **The `n`-torsion is locally of finite presentation** over `S`: `E[n]` is the base change of
`[n]` along the zero section. -/
instance locallyOfFinitePresentation_torsion_hom :
    LocallyOfFinitePresentation (E.torsion n).X.hom :=
  MorphismProperty.of_isPullback (E.isPullback_torsion n) inferInstance

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

/-- **`E'[n]` is the inverse image of `E[n]`.** For a morphism `g : E' ⟶ E` of elliptic curves
forming a pullback square over `f : S' ⟶ S` and carrying the zero section of `E'` to that of `E`,
the square formed by the induced morphism `E'[n] ⟶ E[n]`, the two inclusions and `g` is a pullback
square. -/
theorem isPullback_torsionMap_torsionι :
    IsPullback (torsionMap n hg h0) (E'.torsionι n).left (E.torsionι n).left g :=
  .of_bot (by simpa using isPullback_torsionMap n hg h0) (torsionMap_torsionι n hg h0) hg

/-- **The ideal sheaf of `E[n]` commutes with base change**: for a morphism `g : E' ⟶ E` of
elliptic curves forming a pullback square over `f : S' ⟶ S` and carrying the zero section of `E'`
to that of `E`, the ideal sheaf of `E'[n]` is the inverse image along `g` of that of `E[n]`. -/
theorem ker_torsionι_left_of_isPullback :
    (E'.torsionι n).left.ker = (E.torsionι n).left.ker.comap g :=
  Scheme.IdealSheafData.ker_eq_comap_of_isPullback _ (isPullback_torsionMap_torsionι n hg h0).flip

end BaseChange

/-! ### Pairs of points of `E[N]` -/

section Pairs

open MonoidalCategory CartesianMonoidalCategory

variable (N : ℕ) [NeZero N]

/-- **The universal pair of points of `E[N]`.** The homomorphism `(ℤ/Nℤ)² →* E(E[N] ×_S E[N])`
sending `(a, b)` to `aP + bQ`, where `P` and `Q` are the two projections
`E[N] ×_S E[N] ⟶ E[N]` followed by the inclusion of `E[N]` into `E`. Every homomorphism
`(ℤ/Nℤ)² →* E(Z)`, for `Z` over `S`, factors uniquely through it
(`existsUnique_comp_torsionPairHom`). -/
noncomputable def torsionPairHom : Multiplicative (ZMod N × ZMod N) →*
    ((E.torsion N).X ⊗ (E.torsion N).X ⟶ Over.mk E.structureMap) :=
  (zmodProdMonoidHomEquiv N _).symm
    (⟨fst _ _ ≫ E.torsionι N, by rw [← zpow_natCast, comp_torsionι_zpow]⟩,
      ⟨snd _ _ ≫ E.torsionι N, by rw [← zpow_natCast, comp_torsionι_zpow]⟩)

/-- The universal pair of points of `E[N]` sends `(a, b)` to `aP + bQ`. -/
@[simp]
theorem torsionPairHom_ofAdd (a b : ZMod N) :
    E.torsionPairHom N (.ofAdd (a, b)) =
      (fst _ _ ≫ E.torsionι N) ^ a.val * (snd _ _ ≫ E.torsionι N) ^ b.val :=
  zmodProdMonoidHomEquiv_symm_apply _ _ _

/-- The universal pair of points of `E[N]` sends `(1, 0)` to the first projection `P`. -/
theorem torsionPairHom_ofAdd_one_zero :
    E.torsionPairHom N (.ofAdd (1, 0)) = fst _ _ ≫ E.torsionι N :=
  (coe_zmodProdMonoidHomEquiv_apply_fst _).symm.trans <| by
    rw [torsionPairHom, Equiv.apply_symm_apply]

/-- The universal pair of points of `E[N]` sends `(0, 1)` to the second projection `Q`. -/
theorem torsionPairHom_ofAdd_zero_one :
    E.torsionPairHom N (.ofAdd (0, 1)) = snd _ _ ≫ E.torsionι N :=
  (coe_zmodProdMonoidHomEquiv_apply_snd _).symm.trans <| by
    rw [torsionPairHom, Equiv.apply_symm_apply]

/-- **`E[N] ×_S E[N]` represents homomorphisms from `(ℤ/Nℤ)²`.** Every homomorphism
`φ : (ℤ/Nℤ)² →* E(Z)`, for `Z` over `S`, is `a ↦ x ≫ torsionPairHom E N a` for a unique point `x`
of `E[N] ×_S E[N]` with values in `Z`, namely the pair of points of `E[N]` given by `φ (1, 0)` and
`φ (0, 1)`. -/
theorem existsUnique_comp_torsionPairHom {Z : Over S}
    (φ : Multiplicative (ZMod N × ZMod N) →* (Z ⟶ Over.mk E.structureMap)) :
    ∃! x : Z ⟶ (E.torsion N).X ⊗ (E.torsion N).X, ∀ a, x ≫ E.torsionPairHom N a = φ a := by
  let e := zmodProdMonoidHomEquiv N (Z ⟶ Over.mk E.structureMap)
  let P := E.torsionPointsEquiv N Z ⟨(e φ).1, by rw [zpow_natCast]; exact (e φ).1.2⟩
  let Q := E.torsionPointsEquiv N Z ⟨(e φ).2, by rw [zpow_natCast]; exact (e φ).2.2⟩
  refine ⟨lift P Q, fun a ↦ ?_, fun x hx ↦ ?_⟩
  · -- write `a = (a₁, a₂)`, so that `φ a = φ (1, 0) ^ a₁ * φ (0, 1) ^ a₂`
    obtain ⟨⟨a₁, a₂⟩, rfl⟩ : ∃ p : ZMod N × ZMod N, Multiplicative.ofAdd p = a := ⟨a.toAdd, rfl⟩
    have hφ := zmodProdMonoidHomEquiv_symm_apply (e φ) a₁ a₂
    rw [e.symm_apply_apply] at hφ
    rw [hφ]
    simp [P, Q, MonObj.comp_mul, MonObj.comp_pow]
  · refine CartesianMonoidalCategory.hom_ext _ _ (torsion_hom_ext ?_) (torsion_hom_ext ?_)
    · simpa [P, e, -torsionPairHom_ofAdd, torsionPairHom_ofAdd_one_zero] using hx (.ofAdd (1, 0))
    · simpa [Q, e, -torsionPairHom_ofAdd, torsionPairHom_ofAdd_zero_one] using hx (.ofAdd (0, 1))

end Pairs

end Torsion

/-! ### Transitions between torsion levels -/

section Transitions

variable (m n : ℤ)

/-- Multiplication by `m` restricted to `E[mn]`, with values in `E[n]`. -/
noncomputable def torsionMulBy : (E.torsion (m * n)).X ⟶ (E.torsion n).X :=
  GroupScheme.torsionMulBy E.toCommGrp m n

/-- The transition `E[mn] ⟶ E[n]` sends a torsion point to its multiple by `m`. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_torsionι :
    E.torsionMulBy m n ≫ E.torsionι n = E.torsionι (m * n) ≫ E.mulBy m :=
  by
    rw [comp_mulBy]
    exact GroupScheme.torsionMulBy_torsionι E.toCommGrp m n

/-- On schemes, the torsion transition is the restriction of multiplication by `m`. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_left_torsionι :
    (E.torsionMulBy m n).left ≫ (E.torsionι n).left =
      (E.torsionι (m * n)).left ≫ (E.mulBy m).left :=
  congrArg Over.Hom.left (E.torsionMulBy_torsionι m n)

/-- The torsion transition is a homomorphism of group schemes. -/
instance isMonHom_torsionMulBy : IsMonHom (E.torsionMulBy m n) :=
  GroupScheme.isMonHom_torsionMulBy E.toCommGrp m n

/-- Multiplication by one on torsion is the identity, after identifying `1 * n` with `n`. -/
@[simp]
theorem torsionMulBy_one :
    E.torsionMulBy 1 n = eqToHom (congrArg (fun k ↦ (E.torsion k).X) (one_mul n)) :=
  GroupScheme.torsionMulBy_one E.toCommGrp n

/-- Successive torsion transitions multiply their indices, with the associativity transport. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_comp (l : ℤ) :
    E.torsionMulBy l (m * n) ≫ E.torsionMulBy m n =
      eqToHom (congrArg (fun k ↦ (E.torsion k).X) (mul_assoc l m n).symm) ≫
        E.torsionMulBy (l * m) n :=
  GroupScheme.torsionMulBy_comp E.toCommGrp m n l

/-- The inclusion of `E[m]` in `E[mn]`. -/
noncomputable def torsionInclusion : (E.torsion m).X ⟶ (E.torsion (m * n)).X :=
  GroupScheme.torsionInclusion E.toCommGrp m n

/-- The inclusion between torsion levels preserves the underlying point of `E`. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_torsionι :
    E.torsionInclusion m n ≫ E.torsionι (m * n) = E.torsionι m :=
  GroupScheme.torsionInclusion_torsionι E.toCommGrp m n

/-- On schemes, inclusions between torsion levels preserve the point of `E`. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_left_torsionι :
    (E.torsionInclusion m n).left ≫ (E.torsionι (m * n)).left = (E.torsionι m).left :=
  congrArg Over.Hom.left (E.torsionInclusion_torsionι m n)

/-- The inclusion between torsion levels is a monomorphism. -/
instance mono_torsionInclusion : Mono (E.torsionInclusion m n) :=
  GroupScheme.mono_torsionInclusion E.toCommGrp m n

/-- The inclusion between torsion levels is a homomorphism of group schemes. -/
instance isMonHom_torsionInclusion : IsMonHom (E.torsionInclusion m n) :=
  GroupScheme.isMonHom_torsionInclusion E.toCommGrp m n

/-- The inclusion between torsion levels is a closed immersion. -/
instance isClosedImmersion_torsionInclusion_left :
    IsClosedImmersion (E.torsionInclusion m n).left := by
  have : IsClosedImmersion
      ((E.torsionInclusion m n).left ≫ (E.torsionι (m * n)).left) := by
    rw [← Over.comp_left, torsionInclusion_torsionι]
    infer_instance
  exact .of_comp _ (E.torsionι (m * n)).left

/-- Inclusion into the same torsion level is the identity, after identifying `m * 1` with `m`. -/
@[simp]
theorem torsionInclusion_one :
    E.torsionInclusion m 1 = eqToHom (congrArg (fun k ↦ (E.torsion k).X) (mul_one m).symm) :=
  GroupScheme.torsionInclusion_one E.toCommGrp m

/-- Successive torsion inclusions multiply their indices, with the associativity transport. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_comp (l : ℤ) :
    E.torsionInclusion m n ≫ E.torsionInclusion (m * n) l =
      E.torsionInclusion m (n * l) ≫
        eqToHom (congrArg (fun k ↦ (E.torsion k).X) (mul_assoc m n l).symm) :=
  GroupScheme.torsionInclusion_comp E.toCommGrp m n l

/-- The transition kills the included `m`-torsion. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_torsionMulBy :
    E.torsionInclusion m n ≫ E.torsionMulBy m n = 1 :=
  GroupScheme.torsionInclusion_torsionMulBy E.toCommGrp m n

/-- The torsion transition is the base change of multiplication by `m` on `E`. -/
theorem isPullback_torsionMulBy :
    IsPullback (E.torsionι (m * n)).left (E.torsionMulBy m n).left
      (E.mulBy m).left (E.torsionι n).left := by
  simpa [torsion, torsionι, torsionMulBy, ← mulBy_eq_zpow] using
    (GroupScheme.isPullback_torsionMulBy E.toCommGrp m n).map (Over.forget S)

/-- The torsion transition is locally of finite presentation, even when `m = 0`. -/
instance locallyOfFinitePresentation_torsionMulBy_left :
    LocallyOfFinitePresentation (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) inferInstance

/-- The kernel of `E[mn] ⟶ E[n]` is precisely the included `E[m]`, scheme-theoretically. -/
theorem isPullback_torsionInclusion :
    IsPullback (E.torsionInclusion m n).left (E.torsion m).X.hom
      (E.torsionMulBy m n).left (1 : Over.mk (𝟙 S) ⟶ (E.torsion n).X).left := by
  convert! (GroupScheme.isPullback_torsionInclusion E.toCommGrp m n).map (Over.forget S)
    using 1

section BaseChange

variable {S' : Scheme.{u}} {E} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- Inclusions between torsion levels commute with arbitrary base change. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_left_comp_torsionMap :
    (E'.torsionInclusion m n).left ≫ torsionMap (m * n) hg h0 =
      torsionMap m hg h0 ≫ (E.torsionInclusion m n).left := by
  apply (E.isPullback_torsion (m * n)).hom_ext
  · simp
  · simp [Over.w]

/-- Torsion transitions commute with arbitrary base change. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_left_comp_torsionMap :
    (E'.torsionMulBy m n).left ≫ torsionMap n hg h0 =
      torsionMap (m * n) hg h0 ≫ (E.torsionMulBy m n).left := by
  apply (E.isPullback_torsion n).hom_ext
  · simp [mulBy_left_comp_of_isPullback hg h0]
  · simp [Over.w]

end BaseChange

end Transitions

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
