/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.LevelThreeNormalForm
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The fine moduli scheme of naive full level-three structures

Let `B` be a scheme. The **universal level-three normal form over `B`**
(`EllObj.universalLevelThree B`) is the object of `Ell/B` given by the level-three normal form

`Y² + 3μXY + (μ³ - 1)Y = X³`

over `B × Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`, with its basis `(0, 0)`,
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the `3`-torsion (`EllObj.prodCurvePoint` of
`UniversalLevelThree.firstPointHom` and `UniversalLevelThree.secondPointHom`). It classifies
elliptic curves with two sections `P` and `Q` which are killed by `3`, miss the zero section, and
such that `Q` is neither `P` nor `-P` over any point of the base: for such a triple `(E/S, P, Q)`
there is exactly one arrow `(E/S) ⟶ EllObj.universalLevelThree B` of `Ell/B` pulling the universal
basis back to `(P, Q)` (`EllObj.existsUnique_hom_universalLevelThree`). This is the universal
property `EllipticCurveGeom.existsUnique_levelThreeNormalForm_curveGeom`, read in `Ell/B` through
`EllObj.homProdCurveEquiv`.

These conditions on `(P, Q)` say exactly that the homomorphism `(ℤ/3ℤ)² →* E(S)` sending `(a, b)`
to `aP + bQ` is injective on every fibre
(`EllipticCurveGeom.isFiberwiseInjective_zmod_three_prod_iff`), that is, that `(P, Q)` is a naive
`[Γ(3)]`-structure on `E`. Hence the naive moduli problem `[Γ(3)]` over `Ell/B` is represented by
the universal level-three normal form (`ModuliProblem.gammaNaiveThreeRepresentableBy`): its base
`B × Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is the fine moduli scheme of naive full level three over `B`.
It is affine over `B`, and affine when `B` is (`EllObj.isAffineHom_prodCurve_structureMap` and
`EllObj.isAffine_prodCurve_base`), and smooth of relative dimension `1` over `B`
(`EllObj.smoothOfRelativeDimension_one_universalLevelThree_structureMap`) because
`ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is standard smooth of relative dimension `1` over `ℤ`. No hypothesis
on `B` is needed: a naive `[Γ(3)]`-structure can only exist over a base on which `3` is invertible,
and the coefficient ring already contains `1/3`. Over `B = Spec ℤ[1/3]` this is the affine
universal family of naive full level three of Katz and Mazur (KM 2.2.11), one of the two
rigidifiers through which they prove that a relatively representable, affine, rigid moduli problem
is representable (KM 4.7.0).

## Main definitions

* `TauCeti.AlgebraicGeometry.UniversalLevelThree.curveGeomStructure`: the universal naive
  `[Γ(3)]`-structure over `Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`, given by the universal basis; it is
  injective on every fibre (`UniversalLevelThree.isFiberwiseInjective_curveGeomStructure`).
* `TauCeti.AlgebraicGeometry.EllObj.universalLevelThree B`: the universal level-three normal form
  over `B`, as an object of `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveThreeRepresentableBy B`: the naive moduli
  problem `[Γ(3)]` over `Ell/B` is represented by `EllObj.universalLevelThree B`.

## Main results

* `WeierstrassCurve.UniversalLevelThree.isStandardSmoothOfRelativeDimension_one_ring` and
  `TauCeti.AlgebraicGeometry.EllObj.smoothOfRelativeDimension_one_universalLevelThree_structureMap`:
  the universal level-three base ring is standard smooth of relative dimension `1` over `ℤ`, and
  `EllObj.universalLevelThree B` is smooth of relative dimension `1` over `B`.
* `TauCeti.AlgebraicGeometry.EllObj.existsUnique_hom_universalLevelThree`: the universal property
  of the universal level-three normal form in `Ell/B`.
* `ModuliProblem.naiveLevelEquiv_gammaNaiveThreeRepresentableBy_homEquiv_fst` and
  `ModuliProblem.naiveLevelEquiv_gammaNaiveThreeRepresentableBy_homEquiv_snd`: the naive
  `[Γ(3)]`-structure attached to an arrow `k` is the pullback of the universal basis along `k`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.10 and 2.2.11 (naive level-three structures as
  rigidifiers) and Chapter 4.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry MonObj

namespace WeierstrassCurve.UniversalLevelThree

/-! ### Smoothness of relative dimension one of the universal level-three ring -/

-- The standard étale pair `(X² + X + 1, 3)` presenting `ℤ[1/3, ζ₃]` over `ℤ`:
-- `(2X + 1)(-2X - 1) + 4(X² + X + 1) = 3`.
@[simps]
private noncomputable def cyclotomicThreePair : StandardEtalePair ℤ where
  f := Polynomial.X ^ 2 + Polynomial.X + 1
  monic_f := by monicity!
  g := Polynomial.C 3
  cond := ⟨-(2 * Polynomial.X + 1), Polynomial.C 4, 1, by simp; ring⟩

private abbrev CyclotomicPoly : Type := MvPolynomial (Fin 1) cyclotomicThreePair.Ring

private abbrev ModelRing : Type :=
  Localization.Away (MvPolynomial.X 0 ^ 3 - 1 : CyclotomicPoly)

private noncomputable def rootOfUnityRingHom : cyclotomicThreePair.Ring →+* Ring :=
  have hE : (levelThreeNormalForm parameter).IsElliptic := curve_eq ▸ inferInstance
  let h := (isElliptic_levelThreeNormalForm_iff parameter).mp hE
  (cyclotomicThreePair.lift rootOfUnity
    ⟨by simpa using rootOfUnity_sq_add_rootOfUnity_add_one,
      by simpa [map_ofNat] using h.1⟩).toRingHom

@[simp]
private theorem rootOfUnityRingHom_X :
    rootOfUnityRingHom cyclotomicThreePair.X = rootOfUnity :=
  cyclotomicThreePair.lift_X _ _

private noncomputable def modelToRing : ModelRing →+* Ring :=
  have hE : (levelThreeNormalForm parameter).IsElliptic := curve_eq ▸ inferInstance
  let h := (isElliptic_levelThreeNormalForm_iff parameter).mp hE
  IsLocalization.Away.lift (MvPolynomial.X 0 ^ 3 - 1 : CyclotomicPoly)
    (g := MvPolynomial.eval₂Hom rootOfUnityRingHom ![parameter]) (by simpa using h.2)

private noncomputable def ringToModel : Ring →+* ModelRing :=
  let cHom : cyclotomicThreePair.Ring →+* ModelRing :=
    (algebraMap CyclotomicPoly ModelRing).comp MvPolynomial.C
  have h3S : IsUnit (3 : ModelRing) := by
    have h3P : IsUnit (3 : cyclotomicThreePair.Ring) := by
      simpa [map_ofNat] using cyclotomicThreePair.hasMap_X.2
    simpa [map_ofNat] using h3P.map cHom
  have hμS : IsUnit (algebraMap CyclotomicPoly ModelRing (MvPolynomial.X 0) ^ 3 - 1) := by
    rw [← map_pow, ← map_one (algebraMap CyclotomicPoly ModelRing), ← map_sub]
    exact IsLocalization.Away.algebraMap_isUnit (S := ModelRing) _
  have hζS : cHom cyclotomicThreePair.X ^ 2 + cHom cyclotomicThreePair.X + 1 = 0 := by
    have hζP : cyclotomicThreePair.X ^ 2 + cyclotomicThreePair.X + 1 = 0 := by
      simpa using cyclotomicThreePair.hasMap_X.1
    simpa using congrArg cHom hζP
  lift ((isElliptic_levelThreeNormalForm_iff _).mpr ⟨h3S, hμS⟩).isUnit hζS

-- Identify `Localization.Away (μ³ - 1)` over `cyclotomicThreePair.Ring[μ]` with `Ring`.
private noncomputable def modelAlgEquiv : ModelRing ≃ₐ[ℤ] Ring := by
  refine AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom modelToRing ringToModel ?_ ?_) (fun _ ↦ by simp)
  · ext <;> simp [modelToRing, ringToModel]
  · apply IsLocalization.ringHom_ext (.powers (MvPolynomial.X 0 ^ 3 - 1 : CyclotomicPoly))
    refine MvPolynomial.ringHom_ext' ?_ (Fin.forall_fin_one.mpr ?_)
    · let cHom : cyclotomicThreePair.Ring →+* ModelRing :=
        (algebraMap CyclotomicPoly ModelRing).comp MvPolynomial.C
      have hlr := cyclotomicThreePair.hom_ext
        (f := { ringToModel.comp (modelToRing.comp cHom) with commutes' := fun _ ↦ by simp })
        (g := { cHom with commutes' := fun _ ↦ by simp })
        (by simp [cHom, modelToRing, ringToModel])
      exact congrArg AlgHom.toRingHom hlr
    · simp [modelToRing, ringToModel]

/-- The universal level-three coefficient ring `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is standard smooth of
relative dimension `1` over `ℤ`: it is `ℤ[1/3, ζ₃][μ]` localized away from `μ³ - 1`, over the
standard étale `ℤ`-algebra `ℤ[1/3, ζ₃]`. -/
instance isStandardSmoothOfRelativeDimension_one_ring :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ Ring := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 ℤ cyclotomicThreePair.Ring :=
    (Algebra.IsStandardEtale.nonempty_standardEtalePresentation
      (R := ℤ) (S := cyclotomicThreePair.Ring)).some
      |>.toSubmersivePresentation.isStandardSmoothOfRelativeDimension
      (by simp [Algebra.Presentation.dimension])
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 CyclotomicPoly ModelRing :=
    .localization_away (MvPolynomial.X 0 ^ 3 - 1 : CyclotomicPoly)
  have : Algebra.IsStandardSmoothOfRelativeDimension (1 + 0) ℤ CyclotomicPoly :=
    .trans 0 1 ℤ cyclotomicThreePair.Ring CyclotomicPoly
  have hS : Algebra.IsStandardSmoothOfRelativeDimension (0 + (1 + 0)) ℤ ModelRing :=
    .trans (1 + 0) 0 ℤ CyclotomicPoly ModelRing
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ ModelRing := by simpa using hS
  exact .of_algEquiv 1 modelAlgEquiv

/-- The base `Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` of the universal level-three normal form is smooth of
relative dimension `1` over `Spec ℤ`, the terminal scheme. -/
instance smoothOfRelativeDimension_one_terminal_from :
    SmoothOfRelativeDimension 1 (terminal.from (Spec (.of (ULift.{u} Ring)))) := by
  let f : ULift.{u} ℤ →+* ULift.{u} Ring :=
    ULift.ringEquiv.symm.toRingHom.comp ((algebraMap ℤ Ring).comp ULift.ringEquiv.toRingHom)
  have hf : f.IsStandardSmoothOfRelativeDimension 1 := by
    have h₁ := RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (ULift.ringEquiv : ULift.{u} Ring ≃+* Ring).symm
    have h₂ : (algebraMap ℤ Ring).IsStandardSmoothOfRelativeDimension 1 :=
      (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance
    have h₃ := RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    dsimp only [f]
    simpa using h₁.comp (h₂.comp h₃)
  have : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom f)) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hf)
  have e := specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal
  rw [terminal.hom_ext (terminal.from _) (Spec.map (CommRingCat.ofHom f) ≫ e.hom)]
  have hcomp : SmoothOfRelativeDimension (1 + 0) (Spec.map (CommRingCat.ofHom f) ≫ e.hom) :=
    inferInstance
  simpa using hcomp

end WeierstrassCurve.UniversalLevelThree

namespace TauCeti.AlgebraicGeometry

open WeierstrassCurve UniversalLevelThree

namespace UniversalLevelThree

/-! ### The universal naive `[Γ(3)]`-structure over `Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` -/

/-- **The universal naive `[Γ(3)]`-structure.** The homomorphism `(ℤ/3ℤ)² →* curveGeom(M)`, for
`M = Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`, sending `(1, 0)` and `(0, 1)` to the basis points `(0, 0)`
and `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the `3`-torsion. -/
noncomputable def curveGeomStructure :
    Multiplicative (ZMod 3 × ZMod 3) →*
      (𝟙_ (Over (Spec (.of (ULift.{u} UniversalLevelThree.Ring)))) ⟶
        Over.mk curveGeom.structureMap) :=
  (zmodProdMonoidHomEquiv 3 _).symm
    (⟨firstPointHom, by
        rw [← zpow_ofNat, curveGeom.zpow_eq_one_iff_left_comp_mulBy_left]
        exact firstPointHom_left_comp_mulBy_three_left⟩,
      ⟨secondPointHom, by
        rw [← zpow_ofNat, curveGeom.zpow_eq_one_iff_left_comp_mulBy_left]
        exact secondPointHom_left_comp_mulBy_three_left⟩)

/-- The universal naive `[Γ(3)]`-structure sends `(1, 0)` to the point `(0, 0)`. -/
@[simp]
theorem curveGeomStructure_ofAdd_one_zero :
    curveGeomStructure.{u} (.ofAdd (1, 0)) = firstPointHom := by
  rw [← coe_zmodProdMonoidHomEquiv_apply_fst, curveGeomStructure, Equiv.apply_symm_apply]

/-- The universal naive `[Γ(3)]`-structure sends `(0, 1)` to the point
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`. -/
@[simp]
theorem curveGeomStructure_ofAdd_zero_one :
    curveGeomStructure.{u} (.ofAdd (0, 1)) = secondPointHom := by
  rw [← coe_zmodProdMonoidHomEquiv_apply_snd, curveGeomStructure, Equiv.apply_symm_apply]

/-- The universal naive `[Γ(3)]`-structure is injective on every fibre: the universal basis is a
naive `[Γ(3)]`-structure on `curveGeom`. -/
theorem isFiberwiseInjective_curveGeomStructure :
    curveGeom.IsFiberwiseInjective curveGeomStructure.{u} := by
  refine EllipticCurveGeom.isFiberwiseInjective_zmod_three_prod_iff.mpr ?_
  rw [curveGeomStructure_ofAdd_one_zero, curveGeomStructure_ofAdd_zero_one]
  exact ⟨firstPointHom_left_ne_zero, secondPointHom_left_ne_zero,
    fun s ↦ ⟨secondPointHom_left_ne_firstPointHom_left s,
      secondPointHom_left_ne_firstPointHom_left_neg s⟩⟩

end UniversalLevelThree

namespace EllObj

/-! ### The universal level-three normal form in `Ell/B` -/

variable (B : Scheme.{u})

/-- **The universal level-three normal form over `B`**: the level-three normal form
`Y² + 3μXY + (μ³ - 1)Y = X³`, pulled back to `B × Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` along the second
projection, as an object of `Ell/B` through the first projection. Its basis of the `3`-torsion is
`prodCurvePoint B firstPointHom`, `prodCurvePoint B secondPointHom`. -/
noncomputable abbrev universalLevelThree : EllObj B :=
  prodCurve B curveGeom.{u}

/-- The universal level-three normal form over `B` has structure morphism smooth of relative
dimension `1` over `B`. -/
instance smoothOfRelativeDimension_one_universalLevelThree_structureMap :
    SmoothOfRelativeDimension 1 (universalLevelThree B).structureMap :=
  MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' _ _).flip inferInstance

variable {B} {X : EllObj B}

/-- **The universal property of the universal level-three normal form in `Ell/B`.** Let
`X = (E/S)` be an object of `Ell/B` and `P`, `Q` two `S`-points of `E` killed by `3` which miss the
zero section, and such that `Q` is neither `P` nor `-P` over any point of `S`. Then there is
exactly one arrow `k : X ⟶ universalLevelThree B` of `Ell/B` along which the basis points
`(0, 0)` and `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` pull back to `P` and `Q`. -/
theorem existsUnique_hom_universalLevelThree
    (P Q : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) (hP₃ : P ^ 3 = 1) (hQ₃ : Q ^ 3 = 1)
    (hP₀ : ∀ s, P.left s ≠ X.curve.zero s) (hQ₀ : ∀ s, Q.left s ≠ X.curve.zero s)
    (hQP : ∀ s, Q.left s ≠ P.left s ∧ Q.left s ≠ (P.left ≫ X.curve.neg) s) :
    ∃! k : X ⟶ universalLevelThree B,
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B firstPointHom) = P ∧
        EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B secondPointHom) = Q := by
  have h₃ (R : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap) (hR : R ^ 3 = 1) :
      R.left ≫ (X.curve.mulBy 3).left = X.curve.zero :=
    (X.curve.zpow_eq_one_iff_left_comp_mulBy_left R 3).mp (by rwa [zpow_ofNat])
  -- arrows into `universalLevelThree B` are the classifying pairs of the level-three normal form
  refine (homProdCurveEquiv X).existsUnique_congr_left.mpr ?_
  obtain ⟨⟨f, g⟩, ⟨hg, h₀, hgP, hgQ⟩, huniq⟩ :=
    X.curve.existsUnique_levelThreeNormalForm_curveGeom (EllipticCurveGeom.left_comp_structureMap P)
      (EllipticCurveGeom.left_comp_structureMap Q) hP₀ hQ₀ (h₃ P hP₃) (h₃ Q hQ₃) hQP
  refine ⟨⟨(f, g), hg, h₀⟩, ⟨(pointsPullback_prodCurvePoint_eq_iff _ _ _).mpr ?_,
    (pointsPullback_prodCurvePoint_eq_iff _ _ _).mpr ?_⟩, fun fg hfg ↦ Subtype.ext (huniq _
      ⟨fg.2.1, fg.2.2, ?_, ?_⟩)⟩
  · rw [Equiv.apply_symm_apply]
    exact hgP
  · rw [Equiv.apply_symm_apply]
    exact hgQ
  · simpa using (pointsPullback_prodCurvePoint_eq_iff _ _ _).mp hfg.1
  · simpa using (pointsPullback_prodCurvePoint_eq_iff _ _ _).mp hfg.2

end EllObj

namespace ModuliProblem

open EllObj

/-! ### Representability of the naive moduli problem `[Γ(3)]` -/

variable (B : Scheme.{u})

-- The universal naive `[Γ(3)]`-structure on the universal level-three normal form over `B`: its
-- basis `((0, 0), (-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ)))`.
private noncomputable def universalStructure :
    (gammaNaive B 3).obj (op (universalLevelThree B)) :=
  (naiveLevelEquiv _).symm
    ⟨(EllipticCurveGeom.pointsPullback (isPullback_prodCurveProj B curveGeom)
        (zero_prodCurveProj B curveGeom)).comp curveGeomStructure,
      isFiberwiseInjective_curveGeomStructure.pointsPullback _ _⟩

variable {B}

-- The pullback of the universal naive `[Γ(3)]`-structure along an arrow `k` sends `(1, 0)` to the
-- pullback of the point `(0, 0)` along `k`.
private theorem naiveLevelEquiv_map_universalStructure_fst {X : EllObj B}
    (k : X ⟶ universalLevelThree B) :
    (naiveLevelEquiv X ((gammaNaive B 3).map k.op (universalStructure B))).1 (.ofAdd (1, 0)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B firstPointHom) := by
  simp [universalStructure, curveGeomStructure_ofAdd_one_zero, prodCurvePoint_def]

-- The pullback of the universal naive `[Γ(3)]`-structure along an arrow `k` sends `(0, 1)` to the
-- pullback of the second basis point along `k`.
private theorem naiveLevelEquiv_map_universalStructure_snd {X : EllObj B}
    (k : X ⟶ universalLevelThree B) :
    (naiveLevelEquiv X ((gammaNaive B 3).map k.op (universalStructure B))).1 (.ofAdd (0, 1)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B secondPointHom) := by
  simp [universalStructure, curveGeomStructure_ofAdd_zero_one, prodCurvePoint_def]

-- The two points of a naive `[Γ(3)]`-structure satisfy the conditions of the universal property of
-- the universal level-three normal form.
private theorem existsUnique_hom_of_isFiberwiseInjective {X : EllObj B}
    {φ : Multiplicative (ZMod 3 × ZMod 3) →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)}
    (hφ : X.curve.IsFiberwiseInjective φ) :
    ∃! k : X ⟶ universalLevelThree B,
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B firstPointHom) = φ (.ofAdd (1, 0)) ∧
        EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
          (prodCurvePoint B secondPointHom) = φ (.ofAdd (0, 1)) := by
  obtain ⟨h₁, h₂, h₃⟩ := EllipticCurveGeom.isFiberwiseInjective_zmod_three_prod_iff.mp hφ
  exact existsUnique_hom_universalLevelThree _ _ (by rw [← map_pow]; exact map_one φ)
    (by rw [← map_pow]; exact map_one φ) h₁ h₂ h₃

-- Pulling back the universal naive `[Γ(3)]`-structure is a bijection from arrows into the
-- universal level-three normal form.
private theorem bijective_map_universalStructure (X : EllObj B) :
    Function.Bijective fun k : X ⟶ universalLevelThree B ↦
      (gammaNaive B 3).map k.op (universalStructure B) := by
  constructor
  · -- two arrows pulling back the same structure pull back the universal basis to the same points
    intro k k' h
    have hα := (naiveLevelEquiv X ((gammaNaive B 3).map k'.op (universalStructure B))).2
    have hP := congrArg (fun α ↦ (naiveLevelEquiv X α).1 (.ofAdd (1, 0))) h
    have hQ := congrArg (fun α ↦ (naiveLevelEquiv X α).1 (.ofAdd (0, 1))) h
    simp only [naiveLevelEquiv_map_universalStructure_fst,
      naiveLevelEquiv_map_universalStructure_snd] at hP hQ
    exact (existsUnique_hom_of_isFiberwiseInjective hα).unique
      ⟨hP.trans (naiveLevelEquiv_map_universalStructure_fst k').symm,
        hQ.trans (naiveLevelEquiv_map_universalStructure_snd k').symm⟩
      ⟨(naiveLevelEquiv_map_universalStructure_fst k').symm,
        (naiveLevelEquiv_map_universalStructure_snd k').symm⟩
  · -- the arrow classifying the basis of a structure pulls back the universal structure to it
    intro α
    obtain ⟨k, ⟨hkP, hkQ⟩, -⟩ := existsUnique_hom_of_isFiberwiseInjective (naiveLevelEquiv X α).2
    refine ⟨k, (naiveLevelEquiv X).injective (Subtype.ext ?_)⟩
    refine (zmodProdMonoidHomEquiv 3 _).injective (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · rw [coe_zmodProdMonoidHomEquiv_apply_fst, coe_zmodProdMonoidHomEquiv_apply_fst,
        naiveLevelEquiv_map_universalStructure_fst, hkP]
    · rw [coe_zmodProdMonoidHomEquiv_apply_snd, coe_zmodProdMonoidHomEquiv_apply_snd,
        naiveLevelEquiv_map_universalStructure_snd, hkQ]

variable (B)

/-- **The universal level-three normal form is a fine moduli scheme for naive full level three.**
The naive moduli problem `[Γ(3)]` over `Ell/B` is represented by the universal level-three normal
form over `B × Spec ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` (`EllObj.universalLevelThree B`): the naive
`[Γ(3)]`-structures on an object `X` of `Ell/B` correspond to the arrows
`X ⟶ EllObj.universalLevelThree B`, by pulling back the basis `(0, 0)`,
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the `3`-torsion
(`naiveLevelEquiv_gammaNaiveThreeRepresentableBy_homEquiv_fst` and
`naiveLevelEquiv_gammaNaiveThreeRepresentableBy_homEquiv_snd`). -/
noncomputable def gammaNaiveThreeRepresentableBy :
    (gammaNaive B 3).RepresentableBy (universalLevelThree B) where
  homEquiv := Equiv.ofBijective _ (bijective_map_universalStructure _)
  homEquiv_comp f k := by
    rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, op_comp, Functor.map_comp_apply]

variable {B}

/-- The naive `[Γ(3)]`-structure corresponding to an arrow `k : X ⟶ EllObj.universalLevelThree B`
sends `(1, 0)` to the pullback along `k` of the point `(0, 0)` of the universal level-three normal
form. -/
theorem naiveLevelEquiv_gammaNaiveThreeRepresentableBy_homEquiv_fst {X : EllObj B}
    (k : X ⟶ universalLevelThree B) :
    (naiveLevelEquiv X ((gammaNaiveThreeRepresentableBy B).homEquiv k)).1 (.ofAdd (1, 0)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B firstPointHom) :=
  naiveLevelEquiv_map_universalStructure_fst k

/-- The naive `[Γ(3)]`-structure corresponding to an arrow `k : X ⟶ EllObj.universalLevelThree B`
sends `(0, 1)` to the pullback along `k` of the point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` of the
universal level-three normal form. -/
theorem naiveLevelEquiv_gammaNaiveThreeRepresentableBy_homEquiv_snd {X : EllObj B}
    (k : X ⟶ universalLevelThree B) :
    (naiveLevelEquiv X ((gammaNaiveThreeRepresentableBy B).homEquiv k)).1 (.ofAdd (0, 1)) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B secondPointHom) :=
  naiveLevelEquiv_map_universalStructure_snd k

end ModuliProblem

end TauCeti.AlgebraicGeometry
