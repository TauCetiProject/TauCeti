/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.LegendreNormalForm
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel

/-!
# The fine moduli scheme of Legendre structures

Let `B` be a scheme. Following Katz and Mazur (KM 2.2.9 and 4.6.2), a **Legendre structure** on an
object `X = (E/S)` of `Ell/B` (`ModuliProblem.LegendreData X`) consists of:
1. a naive `[Γ(2)]`-structure `level` on `E/S`, i.e. a homomorphism `(ℤ/2ℤ)² →* E(S)` injective on
   every fibre, determined by the `2`-torsion points `P = level (1, 0)` and `Q = level (0, 1)`;
2. a nowhere-vanishing invariant differential `differential` on `E/S` such that in the Weierstrass
   coordinates normalized by `x(P) = 0` and `dx / (2y + a₁x + a₃) = differential`, the
   `x`-coordinate of `Q` equals `1` (`X.curve.adaptedXCoord ... differential = 1`).

Whereas `[Γ(2)]` alone is not rigid (`[-1]` fixes every `2`-torsion point), `[-1]` negates the
invariant differential, so pairing `[Γ(2)]` with the normalized differential rigidifies the moduli
problem. More strongly, the **Legendre moduli problem** `ModuliProblem.legendre B` over `Ell/B` is
represented (`ModuliProblem.legendreRepresentableBy B`) by the **universal Legendre curve over `B`**
(`EllObj.universalLegendre B`), namely

`Y² = X(X - 1)(X - λ)`

over `B × Spec ℤ[1/2][λ, 1/λ(λ - 1)]` equipped with its `2`-torsion basis `(0, 0)`, `(1, 0)` and
canonical differential `dX / 2Y`. Consequently `ModuliProblem.legendre B` is rigid
(`ModuliProblem.isRigid_legendre B`). Its base `B × Spec ℤ[1/2][λ, 1/λ(λ - 1)]` is affine over `B`,
and affine when `B` is (`EllObj.isAffineHom_prodCurve_structureMap`,
`EllObj.isAffine_prodCurve_base`). Over `B = Spec ℤ[1/2]` this is the characteristic-away-from-`2`
rigidifier complementing `[Γ(3)]` (`ModuliProblem.gammaNaiveThreeRepresentableBy`) in Katz and
Mazur's representability theorem for affine rigid moduli problems (KM 4.7.0).

## Main definitions

* `TauCeti.AlgebraicGeometry.UniversalLegendre.curveGeomStructure`: the universal naive
  `[Γ(2)]`-structure over `Spec ℤ[1/2][λ, 1/λ(λ - 1)]`, injective on every fibre
  (`UniversalLegendre.isFiberwiseInjective_curveGeomStructure`).
* `TauCeti.AlgebraicGeometry.EllObj.prodCurveDifferential`: pullback of an invariant differential
  from `C` to `EllObj.prodCurve B C`.
* `TauCeti.AlgebraicGeometry.EllObj.universalLegendre B`: the universal Legendre curve over `B` in
  `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.LegendreData`: Legendre structures on an object of
  `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.legendre B`: the Legendre moduli problem over `Ell/B`
  (`ModuliProblem.legendreEquiv`), with forgetful morphism
  `ModuliProblem.legendreToGammaNaiveTwo B` to `[Γ(2)]`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.legendreRepresentableBy B`: representability of
  `ModuliProblem.legendre B` by `EllObj.universalLegendre B`.

## Main results

* `TauCeti.AlgebraicGeometry.EllObj.existsUnique_hom_universalLegendre`: the universal property of
  `EllObj.universalLegendre B` in `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.legendreEquiv_legendreRepresentableBy_homEquiv`: the
  Legendre structure attached to an arrow `k : X ⟶ EllObj.universalLegendre B` is the pullback of
  `ModuliProblem.universalLegendreData B` along `k`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_legendre`: `ModuliProblem.legendre B` is rigid.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.9, 4.6.2, and 4.7.0.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry MonObj

namespace TauCeti.AlgebraicGeometry

open WeierstrassCurve UniversalLegendre

namespace UniversalLegendre

/-! ### The universal naive `[Γ(2)]`-structure over `Spec ℤ[1/2][λ, 1/λ(λ - 1)]` -/

/-- **The universal naive `[Γ(2)]`-structure.** The homomorphism `(ℤ/2ℤ)² →* curveGeom(M)`, for
`M = Spec ℤ[1/2][λ, 1/λ(λ - 1)]`, sending `(1, 0)` and `(0, 1)` to `(0, 0)` and `(1, 0)`. -/
noncomputable def curveGeomStructure :
    Multiplicative (ZMod 2 × ZMod 2) →*
      (𝟙_ (Over (Spec (.of (ULift.{u} UniversalLegendre.Ring)))) ⟶
        Over.mk curveGeom.structureMap) :=
  (zmodProdMonoidHomEquiv 2 _).symm
    (⟨firstPointHom, by
        rw [← zpow_ofNat, curveGeom.zpow_eq_one_iff_left_comp_mulBy_left]
        exact firstPointHom_left_comp_mulBy_two_left⟩,
      ⟨secondPointHom, by
        rw [← zpow_ofNat, curveGeom.zpow_eq_one_iff_left_comp_mulBy_left]
        exact secondPointHom_left_comp_mulBy_two_left⟩)

/-- `curveGeomStructure` sends `(1, 0)` to `firstPointHom`. -/
@[simp]
theorem curveGeomStructure_ofAdd_one_zero :
    curveGeomStructure.{u} (.ofAdd (1, 0)) = firstPointHom := by
  rw [← coe_zmodProdMonoidHomEquiv_apply_fst, curveGeomStructure, Equiv.apply_symm_apply]

/-- `curveGeomStructure` sends `(0, 1)` to `secondPointHom`. -/
@[simp]
theorem curveGeomStructure_ofAdd_zero_one :
    curveGeomStructure.{u} (.ofAdd (0, 1)) = secondPointHom := by
  rw [← coe_zmodProdMonoidHomEquiv_apply_snd, curveGeomStructure, Equiv.apply_symm_apply]

/-- `curveGeomStructure` is injective on every fibre. -/
theorem isFiberwiseInjective_curveGeomStructure :
    curveGeom.IsFiberwiseInjective curveGeomStructure.{u} := by
  refine EllipticCurveGeom.isFiberwiseInjective_zmod_two_prod_iff.mpr ?_
  rw [curveGeomStructure_ofAdd_one_zero, curveGeomStructure_ofAdd_zero_one]
  exact ⟨firstPointHom_left_ne_zero, secondPointHom_left_ne_zero,
    secondPointHom_left_ne_firstPointHom_left⟩

end UniversalLegendre

namespace EllObj

/-! ### Invariant differentials on `prodCurve` and the universal Legendre curve in `Ell/B` -/

variable (B : Scheme.{u})

/-- The invariant differential on `prodCurve B C` pulled back from an invariant differential `ω` on
`C` along the second projection. -/
noncomputable def prodCurveDifferential {M : Scheme.{u}} {C : EllipticCurveGeom M}
    (ω : C.InvariantDifferential) : (prodCurve B C).curve.InvariantDifferential :=
  C.invariantDifferentialPullback (isPullback_prodCurveProj B C) (zero_prodCurveProj B C) ω

/-- `prodCurveDifferential B ω` is the pullback of `ω` along `prodCurveProj B C`. -/
theorem prodCurveDifferential_def {M : Scheme.{u}} {C : EllipticCurveGeom M}
    (ω : C.InvariantDifferential) :
    prodCurveDifferential B ω =
      C.invariantDifferentialPullback (isPullback_prodCurveProj B C) (zero_prodCurveProj B C) ω :=
  (rfl)

/-- Pulling `prodCurveDifferential B ω` back along an arrow `k : X ⟶ prodCurve B C` agrees with
pulling `ω` back along the classifying pair `homProdCurveEquiv X k`. -/
theorem invariantDifferentialPullback_prodCurveDifferential {M : Scheme.{u}}
    {C : EllipticCurveGeom M} {X : EllObj B} (k : X ⟶ prodCurve B C)
    (ω : C.InvariantDifferential) :
    (prodCurve B C).curve.invariantDifferentialPullback k.isPullback k.zero_total
        (prodCurveDifferential B ω) =
      C.invariantDifferentialPullback (homProdCurveEquiv X k).2.1
        (homProdCurveEquiv X k).2.2 ω := by
  rw [prodCurveDifferential_def, EllipticCurveGeom.invariantDifferentialPullback_comp]
  exact C.invariantDifferentialPullback_congr
    (homProdCurveEquiv_apply_fst k).symm (homProdCurveEquiv_apply_snd k).symm _ _ _ _ ω

/-- **The universal Legendre curve over `B`**: the Legendre curve `Y² = X(X - 1)(X - λ)` pulled back
to `B × Spec ℤ[1/2][λ, 1/λ(λ - 1)]` along the second projection, as an object of `Ell/B` through the
first projection. -/
noncomputable abbrev universalLegendre : EllObj B :=
  prodCurve B curveGeom.{u}

variable {B} {X : EllObj B}

/-- **The universal property of `universalLegendre B` in `Ell/B`.** Let `X = (E/S)` be an object of
`Ell/B`, `P` and `Q` two `S`-points of `E` killed by `2` that miss the zero section everywhere, and
`ω` an invariant differential on `E/S` with `adaptedXCoord = 1`. Then there is a unique arrow
`k : X ⟶ universalLegendre B` of `Ell/B` pulling `(0, 0)`, `(1, 0)` and `dX / 2Y` back to `P`, `Q`
and `ω`. -/
theorem existsUnique_hom_universalLegendre
    (P Q : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) (hP₂ : P ^ 2 = 1) (hQ₂ : Q ^ 2 = 1)
    (hP₀ : ∀ s, P.left s ≠ X.curve.zero s) (hQ₀ : ∀ s, Q.left s ≠ X.curve.zero s)
    (ω : X.curve.InvariantDifferential)
    (hω : X.curve.adaptedXCoord (EllipticCurveGeom.left_comp_structureMap P)
      (EllipticCurveGeom.left_comp_structureMap Q) hP₀ hQ₀ ω = 1) :
    ∃! k : X ⟶ universalLegendre B,
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B firstPointHom) = P ∧
        EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B secondPointHom) = Q ∧
        (universalLegendre B).curve.invariantDifferentialPullback k.isPullback k.zero_total
          (prodCurveDifferential B curveGeomDifferential) = ω := by
  have h₂ (R : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) (hR : R ^ 2 = 1) :
      R.left ≫ (X.curve.mulBy 2).left = X.curve.zero :=
    (X.curve.zpow_eq_one_iff_left_comp_mulBy_left R 2).mp (by rwa [zpow_ofNat])
  refine (homProdCurveEquiv X).existsUnique_congr_left.mpr ?_
  obtain ⟨⟨f, g⟩, ⟨hg, h₀, hgP, hgQ, hgω⟩, huniq⟩ :=
    X.curve.existsUnique_legendreNormalForm_curveGeom (EllipticCurveGeom.left_comp_structureMap P)
      (EllipticCurveGeom.left_comp_structureMap Q) hP₀ hQ₀ (h₂ P hP₂) (h₂ Q hQ₂) ω hω
  refine ⟨⟨(f, g), hg, h₀⟩, ⟨(pointsPullback_prodCurvePoint_eq_iff _ _ _).mpr ?_,
    (pointsPullback_prodCurvePoint_eq_iff _ _ _).mpr ?_, ?_⟩,
    fun fg hfg ↦ Subtype.ext (huniq _ ⟨fg.2.1, fg.2.2, ?_, ?_, ?_⟩)⟩
  · rw [Equiv.apply_symm_apply]
    exact hgP
  · rw [Equiv.apply_symm_apply]
    exact hgQ
  · rw [invariantDifferentialPullback_prodCurveDifferential]
    refine (curveGeom.invariantDifferentialPullback_congr ?_ ?_ _ _ hg h₀
      curveGeomDifferential).trans hgω
    · exact congrArg (Prod.fst ∘ Subtype.val) ((homProdCurveEquiv X).apply_symm_apply _)
    · exact congrArg (Prod.snd ∘ Subtype.val) ((homProdCurveEquiv X).apply_symm_apply _)
  · simpa using (pointsPullback_prodCurvePoint_eq_iff _ _ _).mp hfg.1
  · simpa using (pointsPullback_prodCurvePoint_eq_iff _ _ _).mp hfg.2.1
  · have hω' := hfg.2.2
    rw [invariantDifferentialPullback_prodCurveDifferential] at hω'
    refine (curveGeom.invariantDifferentialPullback_congr ?_ ?_ fg.2.1 fg.2.2 _ _
      curveGeomDifferential).trans hω'
    · exact (congrArg (Prod.fst ∘ Subtype.val) ((homProdCurveEquiv X).apply_symm_apply fg)).symm
    · exact (congrArg (Prod.snd ∘ Subtype.val) ((homProdCurveEquiv X).apply_symm_apply fg)).symm

end EllObj

namespace ModuliProblem

open EllObj

/-! ### Legendre structures and the Legendre moduli problem -/

variable {B : Scheme.{u}}

/-- **A Legendre structure on an object `X = (E/S)` of `Ell/B`** (Katz–Mazur 2.2.9, 4.6.2): a naive
`[Γ(2)]`-structure `level` on `E/S` together with a nowhere-vanishing invariant differential
`differential` on `E/S` such that the `differential`-adapted `x`-coordinate of the `2`-torsion basis
`(level (1, 0), level (0, 1))` equals `1`. -/
@[ext]
structure LegendreData (X : EllObj B) : Type (u + 1) where
  /-- The underlying naive `[Γ(2)]`-structure `(P, Q)` on `E/S`. -/
  level : (gammaNaive B 2).obj (op X)
  /-- The nowhere-vanishing invariant differential `ω` on `E/S`. -/
  differential : X.curve.InvariantDifferential
  /-- In Weierstrass coordinates normalized by `x(P) = 0` and `dx / (2y + a₁x + a₃) = ω`, the
  `x`-coordinate of `Q` equals `1`. -/
  adaptedXCoord_eq_one :
    X.curve.adaptedXCoord
      (EllipticCurveGeom.left_comp_structureMap ((naiveLevelEquiv X level).1 (.ofAdd (1, 0))))
      (EllipticCurveGeom.left_comp_structureMap ((naiveLevelEquiv X level).1 (.ofAdd (0, 1))))
      (EllipticCurveGeom.isFiberwiseInjective_zmod_two_prod_iff.mp (naiveLevelEquiv X level).2).1
      (EllipticCurveGeom.isFiberwiseInjective_zmod_two_prod_iff.mp
        (naiveLevelEquiv X level).2).2.1
      differential = 1

-- Projection helpers for the two basis sections of a naive `[Γ(2)]`-structure.
private noncomputable abbrev gammaTwoFst (X : EllObj B) (α : (gammaNaive B 2).obj (op X)) :
    𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap :=
  (naiveLevelEquiv X α).1 (.ofAdd (1, 0))

private noncomputable abbrev gammaTwoSnd (X : EllObj B) (α : (gammaNaive B 2).obj (op X)) :
    𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap :=
  (naiveLevelEquiv X α).1 (.ofAdd (0, 1))

private theorem gammaTwoFst_ne_zero (X : EllObj B) (α : (gammaNaive B 2).obj (op X)) (s : X.base) :
    (gammaTwoFst X α).left s ≠ X.curve.zero s :=
  (EllipticCurveGeom.isFiberwiseInjective_zmod_two_prod_iff.mp (naiveLevelEquiv X α).2).1 s

private theorem gammaTwoSnd_ne_zero (X : EllObj B) (α : (gammaNaive B 2).obj (op X)) (s : X.base) :
    (gammaTwoSnd X α).left s ≠ X.curve.zero s :=
  (EllipticCurveGeom.isFiberwiseInjective_zmod_two_prod_iff.mp (naiveLevelEquiv X α).2).2.1 s

/-- Pullback of a `LegendreData` along an arrow `f : X ⟶ Y` of `Ell/B`. -/
noncomputable def LegendreData.pullback {X Y : EllObj B} (f : X ⟶ Y) (d : LegendreData Y) :
    LegendreData X where
  level := (gammaNaive B 2).map f.op d.level
  differential := Y.curve.invariantDifferentialPullback f.isPullback f.zero_total d.differential
  adaptedXCoord_eq_one := by
    have hPf : (gammaTwoFst X ((gammaNaive B 2).map f.op d.level)).left ≫ f.total =
        f.base ≫ (gammaTwoFst Y d.level).left := by
      simp only [gammaTwoFst, naiveLevelEquiv_map, MonoidHom.comp_apply]
      exact EllipticCurveGeom.pointsPullback_left_comp f.isPullback f.zero_total _
    have hQf : (gammaTwoSnd X ((gammaNaive B 2).map f.op d.level)).left ≫ f.total =
        f.base ≫ (gammaTwoSnd Y d.level).left := by
      simp only [gammaTwoSnd, naiveLevelEquiv_map, MonoidHom.comp_apply]
      exact EllipticCurveGeom.pointsPullback_left_comp f.isPullback f.zero_total _
    have hx := Y.curve.appTop_adaptedXCoord_of_isPullback f.isPullback f.zero_total
      (EllipticCurveGeom.left_comp_structureMap (gammaTwoFst Y d.level))
      (EllipticCurveGeom.left_comp_structureMap (gammaTwoSnd Y d.level))
      (gammaTwoFst_ne_zero Y d.level) (gammaTwoSnd_ne_zero Y d.level)
      (EllipticCurveGeom.left_comp_structureMap _)
      (EllipticCurveGeom.left_comp_structureMap _)
      (gammaTwoFst_ne_zero X _) (gammaTwoSnd_ne_zero X _)
      hPf hQf d.differential
    rw [d.adaptedXCoord_eq_one, map_one] at hx
    exact hx.symm

/-- The underlying naive `[Γ(2)]`-structure of `d.pullback f` is the pullback of `d.level`. -/
@[simp]
theorem LegendreData.pullback_level {X Y : EllObj B} (f : X ⟶ Y) (d : LegendreData Y) :
    (d.pullback f).level = (gammaNaive B 2).map f.op d.level :=
  (rfl)

/-- The invariant differential of `d.pullback f` is the pullback of `d.differential`. -/
@[simp]
theorem LegendreData.pullback_differential {X Y : EllObj B} (f : X ⟶ Y) (d : LegendreData Y) :
    (d.pullback f).differential =
      Y.curve.invariantDifferentialPullback f.isPullback f.zero_total d.differential :=
  (rfl)

/-- Pulling back a `LegendreData` along the identity arrow is the identity. -/
@[simp]
theorem LegendreData.pullback_id {X : EllObj B} (d : LegendreData X) :
    d.pullback (𝟙 X) = d := by
  ext : 1
  · simp
  · simp only [pullback_differential]
    exact (X.curve.invariantDifferentialPullback_congr (EllObj.id_base X) (EllObj.id_total X)
      _ _ (IsPullback.id_horiz X.curve.structureMap) (by simp) d.differential).trans
      (X.curve.invariantDifferentialPullback_id d.differential)

/-- Pulling back a `LegendreData` along a composition is the composition of pullbacks. -/
theorem LegendreData.pullback_comp {X Y Z : EllObj B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : LegendreData Z) :
    d.pullback (f ≫ g) = (d.pullback g).pullback f := by
  ext : 1
  · simp
  · simp only [pullback_differential]
    rw [EllipticCurveGeom.invariantDifferentialPullback_comp]

variable (B)

/-- **The Legendre moduli problem** over `Ell/B` (Katz–Mazur 4.6.2), assigning to an object `X` of
`Ell/B` the type `LegendreData X` of Legendre structures on `X` (`legendreEquiv`) and pulling back
structures along arrows of `Ell/B` via `LegendreData.pullback` (`legendreEquiv_map`). -/
noncomputable def legendre : ModuliProblem B where
  obj X := LegendreData X.unop
  map f := TypeCat.ofHom (LegendreData.pullback f.unop)
  map_id _ := ConcreteCategory.hom_ext _ _ fun d ↦ d.pullback_id
  map_comp f g := ConcreteCategory.hom_ext _ _ fun d ↦ d.pullback_comp g.unop f.unop

variable {B}

/-- The Legendre structures on an object `X` of `Ell/B` are the terms of `LegendreData X`. -/
noncomputable def legendreEquiv (X : EllObj B) :
    (legendre B).obj (op X) ≃ LegendreData X :=
  Equiv.refl _

/-- The pullback of a Legendre structure along an arrow `f` of `Ell/B` is
`LegendreData.pullback f`. -/
@[simp]
theorem legendreEquiv_map {X Y : EllObj B} (f : X ⟶ Y) (α : (legendre B).obj (op Y)) :
    legendreEquiv X ((legendre B).map f.op α) = (legendreEquiv Y α).pullback f :=
  (rfl)

variable (B) in
/-- The forgetful morphism of moduli problems `legendre B ⟶ gammaNaive B 2` retaining the
underlying naive `[Γ(2)]`-structure. -/
noncomputable def legendreToGammaNaiveTwo : legendre B ⟶ gammaNaive B 2 where
  app _ := TypeCat.ofHom LegendreData.level

/-- `legendreToGammaNaiveTwo B` sends a Legendre structure to its underlying naive
`[Γ(2)]`-structure. -/
@[simp]
theorem legendreToGammaNaiveTwo_app_apply (X : EllObj B) (α : (legendre B).obj (op X)) :
    (legendreToGammaNaiveTwo B).app (op X) α = (legendreEquiv X α).level :=
  (rfl)

/-! ### Representability and rigidity of `legendre B` -/

variable (B)

-- The universal naive `[Γ(2)]`-structure on `universalLegendre B`.
private noncomputable def universalLegendreLevel :
    (gammaNaive B 2).obj (op (universalLegendre B)) :=
  (naiveLevelEquiv _).symm
    ⟨(EllipticCurveGeom.pointsPullback (isPullback_prodCurveProj B curveGeom)
        (zero_prodCurveProj B curveGeom)).comp curveGeomStructure,
      isFiberwiseInjective_curveGeomStructure.pointsPullback _ _⟩

/-- **The universal Legendre structure** on `universalLegendre B`, given by the `2`-torsion basis
`((0, 0), (1, 0))` and the canonical Weierstrass differential `dX / 2Y`. -/
noncomputable def universalLegendreData : LegendreData (universalLegendre B) where
  level := universalLegendreLevel B
  differential := prodCurveDifferential B curveGeomDifferential
  adaptedXCoord_eq_one := by
    have hPf : (gammaTwoFst (universalLegendre B) (universalLegendreLevel B)).left ≫
        prodCurveProj B curveGeom = prod.snd ≫ firstPointHom.left := by
      simp [gammaTwoFst, universalLegendreLevel, curveGeomStructure_ofAdd_one_zero]
    have hQf : (gammaTwoSnd (universalLegendre B) (universalLegendreLevel B)).left ≫
        prodCurveProj B curveGeom = prod.snd ≫ secondPointHom.left := by
      simp [gammaTwoSnd, universalLegendreLevel, curveGeomStructure_ofAdd_zero_one]
    have hx := curveGeom.appTop_adaptedXCoord_of_isPullback
      (isPullback_prodCurveProj B curveGeom) (zero_prodCurveProj B curveGeom)
      (Over.w firstPointHom) (Over.w secondPointHom)
      firstPointHom_left_ne_zero secondPointHom_left_ne_zero
      (EllipticCurveGeom.left_comp_structureMap _)
      (EllipticCurveGeom.left_comp_structureMap _)
      (gammaTwoFst_ne_zero _ _) (gammaTwoSnd_ne_zero _ _)
      hPf hQf curveGeomDifferential
    rw [adaptedXCoord_curveGeom, map_one] at hx
    exact hx.symm

variable {B}

private theorem universalLegendreData_differential :
    (universalLegendreData B).differential = prodCurveDifferential B curveGeomDifferential :=
  (rfl)

private theorem naiveLevelEquiv_pullback_universalLegendreData_fst {X : EllObj B}
    (k : X ⟶ universalLegendre B) :
    (naiveLevelEquiv X ((universalLegendreData B).pullback k).level).1 (.ofAdd (1, 0)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B firstPointHom) := by
  simp [universalLegendreData, universalLegendreLevel, curveGeomStructure_ofAdd_one_zero,
    prodCurvePoint_def]

private theorem naiveLevelEquiv_pullback_universalLegendreData_snd {X : EllObj B}
    (k : X ⟶ universalLegendre B) :
    (naiveLevelEquiv X ((universalLegendreData B).pullback k).level).1 (.ofAdd (0, 1)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B secondPointHom) := by
  simp [universalLegendreData, universalLegendreLevel, curveGeomStructure_ofAdd_zero_one,
    prodCurvePoint_def]

private theorem existsUnique_hom_of_legendreData {X : EllObj B} (d : LegendreData X) :
    ∃! k : X ⟶ universalLegendre B,
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B firstPointHom) = gammaTwoFst X d.level ∧
        EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B secondPointHom) = gammaTwoSnd X d.level ∧
        (universalLegendre B).curve.invariantDifferentialPullback k.isPullback k.zero_total
          (prodCurveDifferential B curveGeomDifferential) = d.differential :=
  existsUnique_hom_universalLegendre (gammaTwoFst X d.level) (gammaTwoSnd X d.level)
    (by rw [gammaTwoFst, ← map_pow]; exact map_one _)
    (by rw [gammaTwoSnd, ← map_pow]; exact map_one _)
    (gammaTwoFst_ne_zero X d.level) (gammaTwoSnd_ne_zero X d.level)
    d.differential d.adaptedXCoord_eq_one

private theorem bijective_pullback_universalLegendreData (X : EllObj B) :
    Function.Bijective fun k : X ⟶ universalLegendre B ↦
      (universalLegendreData B).pullback k := by
  constructor
  · intro k k' h
    have hP := congrArg (fun d ↦ (naiveLevelEquiv X d.level).1 (.ofAdd (1, 0))) h
    have hQ := congrArg (fun d ↦ (naiveLevelEquiv X d.level).1 (.ofAdd (0, 1))) h
    have hω := congrArg LegendreData.differential h
    dsimp only at hP hQ hω
    rw [naiveLevelEquiv_pullback_universalLegendreData_fst,
      naiveLevelEquiv_pullback_universalLegendreData_fst] at hP
    rw [naiveLevelEquiv_pullback_universalLegendreData_snd,
      naiveLevelEquiv_pullback_universalLegendreData_snd] at hQ
    rw [LegendreData.pullback_differential, LegendreData.pullback_differential,
      universalLegendreData_differential] at hω
    exact (existsUnique_hom_of_legendreData ((universalLegendreData B).pullback k')).unique
      ⟨hP.trans (naiveLevelEquiv_pullback_universalLegendreData_fst k').symm,
        hQ.trans (naiveLevelEquiv_pullback_universalLegendreData_snd k').symm,
        hω.trans (by rw [LegendreData.pullback_differential, universalLegendreData_differential])⟩
      ⟨(naiveLevelEquiv_pullback_universalLegendreData_fst k').symm,
        (naiveLevelEquiv_pullback_universalLegendreData_snd k').symm,
        by rw [LegendreData.pullback_differential, universalLegendreData_differential]⟩
  · intro d
    obtain ⟨k, ⟨hkP, hkQ, hkω⟩, -⟩ := existsUnique_hom_of_legendreData d
    refine ⟨k, LegendreData.ext ?_ hkω⟩
    refine (naiveLevelEquiv X).injective (Subtype.ext ?_)
    refine (zmodProdMonoidHomEquiv 2 _).injective (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · rw [coe_zmodProdMonoidHomEquiv_apply_fst, coe_zmodProdMonoidHomEquiv_apply_fst,
        naiveLevelEquiv_pullback_universalLegendreData_fst, hkP]
    · rw [coe_zmodProdMonoidHomEquiv_apply_snd, coe_zmodProdMonoidHomEquiv_apply_snd,
        naiveLevelEquiv_pullback_universalLegendreData_snd, hkQ]

private theorem bijective_map_universalLegendreData (X : EllObj B) :
    Function.Bijective fun k : X ⟶ universalLegendre B ↦
      (legendre B).map k.op
        ((legendreEquiv (universalLegendre B)).symm (universalLegendreData B)) :=
  bijective_pullback_universalLegendreData X

variable (B)

/-- **The universal Legendre curve is a fine moduli scheme for Legendre structures** (Katz–Mazur
4.6.2). The Legendre moduli problem `legendre B` over `Ell/B` is represented by
`EllObj.universalLegendre B` over `B × Spec ℤ[1/2][λ, 1/λ(λ - 1)]`, by pulling back
`universalLegendreData B` (`legendreEquiv_legendreRepresentableBy_homEquiv`). -/
noncomputable def legendreRepresentableBy :
    (legendre B).RepresentableBy (universalLegendre B) where
  homEquiv := Equiv.ofBijective _ (bijective_map_universalLegendreData _)
  homEquiv_comp f k := by
    rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, op_comp]
    exact (legendre B).map_comp_apply k.op f.op
      ((legendreEquiv (universalLegendre B)).symm (universalLegendreData B))

variable {B}

/-- The Legendre structure attached to an arrow `k : X ⟶ EllObj.universalLegendre B` is the
pullback of `universalLegendreData B` along `k`. -/
@[simp]
theorem legendreEquiv_legendreRepresentableBy_homEquiv {X : EllObj B}
    (k : X ⟶ universalLegendre B) :
    legendreEquiv X ((legendreRepresentableBy B).homEquiv k) =
      (universalLegendreData B).pullback k :=
  (rfl)

/-- The naive `[Γ(2)]`-structure of `(legendreRepresentableBy B).homEquiv k` sends `(1, 0)` to the
pullback along `k` of `firstPointHom`. -/
theorem naiveLevelEquiv_legendreRepresentableBy_homEquiv_fst {X : EllObj B}
    (k : X ⟶ universalLegendre B) :
    (naiveLevelEquiv X (legendreEquiv X ((legendreRepresentableBy B).homEquiv k)).level).1
        (.ofAdd (1, 0)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B firstPointHom) :=
  naiveLevelEquiv_pullback_universalLegendreData_fst k

/-- The naive `[Γ(2)]`-structure of `(legendreRepresentableBy B).homEquiv k` sends `(0, 1)` to the
pullback along `k` of `secondPointHom`. -/
theorem naiveLevelEquiv_legendreRepresentableBy_homEquiv_snd {X : EllObj B}
    (k : X ⟶ universalLegendre B) :
    (naiveLevelEquiv X (legendreEquiv X ((legendreRepresentableBy B).homEquiv k)).level).1
        (.ofAdd (0, 1)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B secondPointHom) :=
  naiveLevelEquiv_pullback_universalLegendreData_snd k

/-- The invariant differential of `(legendreRepresentableBy B).homEquiv k` is the pullback along
`k` of `prodCurveDifferential B curveGeomDifferential`. -/
theorem legendreEquiv_legendreRepresentableBy_homEquiv_differential {X : EllObj B}
    (k : X ⟶ universalLegendre B) :
    (legendreEquiv X ((legendreRepresentableBy B).homEquiv k)).differential =
      (universalLegendre B).curve.invariantDifferentialPullback k.isPullback k.zero_total
        (prodCurveDifferential B curveGeomDifferential) :=
  (rfl)

variable (B) in
/-- **The Legendre moduli problem is rigid** (Katz–Mazur 2.2.9, 4.6.2): since `legendre B` is
representable in `Ell/B`, no non-identity automorphism of an elliptic curve `E/S` over the identity
of `S` fixes a Legendre structure. -/
theorem isRigid_legendre : (legendre B).IsRigid :=
  isRigid_of_representableBy (legendreRepresentableBy B)

end ModuliProblem

end TauCeti.AlgebraicGeometry
