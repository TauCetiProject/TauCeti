/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveExactOrder.FiniteEtale
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.TateNormalForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.OfWeierstrass
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel
public import TauCeti.AlgebraicGeometry.ResidueField

/-!
# The fine moduli scheme `Y₁(N)` for `N ≥ 4`

Let `B` be a scheme. The **universal Tate normal form over `B`** (`EllObj.universalTate B`) is the
object of `Ell/B` given by the projective model of `Y² + AXY + BY = X³ + BX²` over
`B × Spec ℤ[A, B][Δ⁻¹]`, with its point `(0, 0)` (`EllObj.universalTatePoint B`). It classifies
elliptic curves with a section `P` such that none of `P`, `2P` and `3P` meets the zero section:
for such a pair `(E/S, P)` there is exactly one arrow `(E/S) ⟶ EllObj.universalTate B` of `Ell/B`
pulling the point `(0, 0)` back to `P` (`EllObj.existsUnique_hom_universalTate`). This is the
universal property `EllipticCurveGeom.existsUnique_tateNormalForm`, read in `Ell/B`.

Now let `N ≥ 4` be invertible on `B`. A naive `[Γ₁(N)]`-structure on `E/S` is a point `P` of
exact order `N` in every fibre, so `P`, `2P` and `3P` miss the zero section, and `(E, P)` is
classified by an arrow to the universal Tate normal form. That arrow is a naive
`[Γ₁(N)]`-structure exactly when its morphism of bases factors through the locus where `(0, 0)`
has naive exact order `N`, the closed subscheme `Y₁(N)` of `B × Spec ℤ[A, B][Δ⁻¹]` on which
`N(0, 0) = 0` and `d(0, 0)` misses the zero section for every proper divisor `d` of `N`
(`EllipticCurveGeom.naiveExactOrderPreimage`). Hence the naive moduli problem `[Γ₁(N)]` is
represented by the restriction `EllObj.yOne B N hN` of the universal Tate normal form to `Y₁(N)`
(`ModuliProblem.gammaOneNaiveRepresentableBy`): `Y₁(N)` is a fine moduli scheme. It is a closed
subscheme of `B × Spec ℤ[A, B][Δ⁻¹]`, so it is affine over `B`
(`EllObj.isAffineHom_yOne_structureMap`), and affine when `B` is, for example for
`B = Spec ℤ[1/N]`.

The hypothesis `N ≥ 4` is what makes the Tate normal form apply: for `N ≤ 3`, a point `P` with
`NP = 0` has one of `P`, `2P` and `3P` equal to the zero section. For `N ≤ 2` the automorphism
`[-1]` fixes every naive `[Γ₁(N)]`-structure, so `[Γ₁(N)]` is not rigid.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllObj.universalTate B`: the universal Tate normal form over `B`, as
  an object of `Ell/B`.
* `TauCeti.AlgebraicGeometry.EllObj.universalTatePoint B`: its point `(0, 0)`.
* `TauCeti.AlgebraicGeometry.EllObj.yOne B N hN`: the restriction of the universal Tate normal
  form to the locus `Y₁(N)` where `(0, 0)` has naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllObj.yOnePoint`: the point `(0, 0)` of the universal elliptic curve
  over `Y₁(N)`, which has naive exact order `N` (`EllObj.isOfNaiveExactOrder_yOnePoint`).

## Main results

* `TauCeti.AlgebraicGeometry.EllObj.existsUnique_hom_universalTate`: the universal property of the
  universal Tate normal form in `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveRepresentableBy`: for `N ≥ 4` invertible
  on `B`, the naive moduli problem `[Γ₁(N)]` over `Ell/B` is represented by `EllObj.yOne B N hN`.
* `TauCeti.AlgebraicGeometry.EllObj.isAffineHom_yOne_structureMap`: `Y₁(N)` is affine over `B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.3 (Tate normal form) and Chapter 4.
* D. Loeffler, *Modular Curves*, lecture notes, 3.3.4 and §3.8.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj WeierstrassCurve UniversalTate

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllObj

/-! ### The universal Tate normal form in `Ell/B` -/

variable (B : Scheme.{u})

/-- **The universal Tate normal form over `B`**: the projective model of the universal Tate normal
form `Y² + AXY + BY = X³ + BX²`, pulled back to `B × Spec ℤ[A, B][Δ⁻¹]` along the second
projection, as an object of `Ell/B` through the first projection. -/
-- An `abbrev`, so that its base, structure morphism and curve are reducibly the product, the first
-- projection and the base change, and morphisms into the product compose with them.
noncomputable abbrev universalTate : EllObj B where
  base := B ⨯ Spec (.of (ULift.{u} UniversalTate.Ring))
  structureMap := prod.fst
  curve := curveULift.toEllipticCurveGeom.baseChange prod.snd

/-- The projection from the universal Tate normal form over `B` to the projective model of the
universal Tate normal form over `Spec ℤ[A, B][Δ⁻¹]`. -/
noncomputable def universalTateProj : (universalTate B).curve.carrier ⟶ curveULift.projModel :=
  (curveULift.toEllipticCurveGeom.baseChangeIso prod.snd).hom ≫ pullback.fst _ _ ≫
    (toEllipticCurveGeomIso curveULift).hom

/-- The universal Tate normal form over `B` is the base change of the universal Tate normal form
over `Spec ℤ[A, B][Δ⁻¹]` along the second projection. -/
theorem isPullback_universalTateProj :
    IsPullback (universalTateProj B) (universalTate B).curve.structureMap
      curveULift.projModelOver prod.snd := by
  have h := (curveULift.toEllipticCurveGeom.isPullback_baseChange
    (prod.snd : B ⨯ Spec (.of (ULift.{u} UniversalTate.Ring)) ⟶ _)).paste_horiz
    (IsPullback.of_horiz_isIso (fst := (toEllipticCurveGeomIso curveULift).hom)
      (snd := curveULift.toEllipticCurveGeom.structureMap) (f := curveULift.projModelOver)
      (g := 𝟙 _) ⟨by simp⟩)
  simpa [universalTateProj] using h

/-- The projection `universalTateProj B` carries the zero section to the zero section. -/
@[reassoc]
theorem zero_universalTateProj :
    (universalTate B).curve.zero ≫ universalTateProj B = prod.snd ≫ curveULift.projModelZero := by
  simp [universalTateProj, pullbackSection_fst_assoc]

/-- **The point `(0, 0)` of the universal Tate normal form over `B`**: the base change of the point
`(0, 0)` of the universal Tate normal form over `Spec ℤ[A, B][Δ⁻¹]`. -/
noncomputable def universalTatePoint :
    𝟙_ (Over (universalTate B).base) ⟶ Over.mk (universalTate B).curve.structureMap :=
  Over.homMk ((isPullback_universalTateProj B).lift (prod.snd ≫ point) (𝟙 _) (by
    simp)) (by simp)

/-- The projection `universalTateProj B` carries the point `(0, 0)` to the point `(0, 0)`. -/
@[reassoc (attr := simp)]
theorem universalTatePoint_left_universalTateProj :
    (universalTatePoint B).left ≫ universalTateProj B = prod.snd ≫ point :=
  (isPullback_universalTateProj B).lift_fst _ _ _

section Classifying

variable {B} {X : EllObj B}

-- For an arrow `k : X ⟶ universalTate B`, the composites of `k` with the projections to the
-- universal Tate normal form over `Spec ℤ[A, B][Δ⁻¹]` classify `X` with the base change of `(0, 0)`
-- along `k`, in the sense of `EllipticCurveGeom.existsUnique_tateNormalForm`.
private theorem isTate_hom (k : X ⟶ universalTate B) :
    IsPullback (k.total ≫ universalTateProj B) X.curve.structureMap curveULift.projModelOver
        (k.base ≫ prod.snd) ∧
      X.curve.zero ≫ k.total ≫ universalTateProj B =
        (k.base ≫ prod.snd) ≫ curveULift.projModelZero ∧
      (EllipticCurveGeom.pointsPullback k.isPullback k.zero_total (universalTatePoint B)).left ≫
          k.total ≫ universalTateProj B = (k.base ≫ prod.snd) ≫ point := by
  refine ⟨k.isPullback.paste_horiz (isPullback_universalTateProj B), ?_, ?_⟩
  · rw [k.zero_total_assoc, zero_universalTateProj, Category.assoc]
  · rw [EllipticCurveGeom.pointsPullback_left_comp_assoc, universalTatePoint_left_universalTateProj,
      Category.assoc]

/-- **The universal property of the universal Tate normal form in `Ell/B`.** Let `X = (E/S)` be an
object of `Ell/B` and `P` an `S`-point of `E` such that none of `P`, `2P` and `3P` meets the zero
section over any point of `S`. Then there is exactly one arrow `k : X ⟶ universalTate B` of `Ell/B`
along which the point `(0, 0)` pulls back to `P`. -/
theorem existsUnique_hom_universalTate (P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)
    (h₁ : ∀ s, P.left s ≠ X.curve.zero s)
    (h₂ : ∀ s, (P.left ≫ (X.curve.mulBy 2).left) s ≠ X.curve.zero s)
    (h₃ : ∀ s, (P.left ≫ (X.curve.mulBy 3).left) s ≠ X.curve.zero s) :
    ∃! k : X ⟶ universalTate B,
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total (universalTatePoint B) = P := by
  have hP := EllipticCurveGeom.left_comp_structureMap P
  obtain ⟨⟨f, g⟩, ⟨hg, h0, hgP⟩, huniq⟩ := X.curve.existsUnique_tateNormalForm hP h₁ h₂ h₃
  have hT := isPullback_universalTateProj B
  -- the arrow over `(X.structureMap, f) : S ⟶ B × Spec ℤ[A, B][Δ⁻¹]` induced by `g`
  let total := hT.lift g (X.curve.structureMap ≫ prod.lift X.structureMap f) (by simp [hg.w])
  have htot₁ : total ≫ universalTateProj B = g := hT.lift_fst _ _ _
  have htot₂ : total ≫ (universalTate B).curve.structureMap =
      X.curve.structureMap ≫ prod.lift X.structureMap f :=
    hT.lift_snd _ _ _
  let k : X ⟶ universalTate B :=
    { base := prod.lift X.structureMap f
      base_structureMap := prod.lift_fst _ _
      total := total
      isPullback := .of_right (by simpa [htot₁] using hg) htot₂ hT
      zero_total := hT.hom_ext
        (by rw [Category.assoc, htot₁, Category.assoc, zero_universalTateProj, prod.lift_snd_assoc]
            exact h0)
        (by rw [Category.assoc, htot₂, EllipticCurveGeom.zero_comp_structureMap_assoc,
              Category.assoc, EllipticCurveGeom.zero_comp_structureMap, Category.comp_id]) }
  have hkP :
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total (universalTatePoint B) = P :=
    ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr (hT.hom_ext
      (by rw [Category.assoc, htot₁, Category.assoc, universalTatePoint_left_universalTateProj,
            prod.lift_snd_assoc]
          exact hgP)
      (by rw [Category.assoc, htot₂, reassoc_of% hP, Category.assoc,
            EllipticCurveGeom.left_comp_structureMap, Category.comp_id]
          exact Category.id_comp _))).symm
  refine ⟨k, hkP, fun k' hk' ↦ ?_⟩
  -- both arrows give classifying pairs of `(X, P)`, which agree by uniqueness
  have hk := isTate_hom k
  have hk'' := isTate_hom k'
  rw [hkP] at hk
  rw [hk'] at hk''
  have hfg := (huniq (k'.base ≫ prod.snd, k'.total ≫ universalTateProj B) hk'').trans
    (huniq (k.base ≫ prod.snd, k.total ≫ universalTateProj B) hk).symm
  simp only [Prod.mk.injEq] at hfg
  have hb : k'.base = k.base :=
    prod.hom_ext (k'.base_structureMap.trans k.base_structureMap.symm) hfg.1
  exact EllObj.hom_ext (hT.hom_ext hfg.2 (by rw [k'.total_structureMap, k.total_structureMap, hb]))

end Classifying

/-! ### The locus `Y₁(N)` -/

variable (N : ℕ) (hN : ∀ b : B, (N : B.residueField b) ≠ 0)

include hN in
/-- If `N` is invertible on `B`, then it is invertible on the base of the universal Tate normal
form over `B`. -/
theorem natCast_residueField_universalTate_ne_zero (s : (universalTate B).base) :
    (N : (universalTate B).base.residueField s) ≠ 0 :=
  Scheme.Hom.natCast_residueField_ne_zero prod.fst (hN _)

/-- **The fine moduli scheme `Y₁(N)`**, with its universal elliptic curve: when `N` is invertible
on `B`, the restriction of the universal Tate normal form over `B` to the closed subscheme of
`B × Spec ℤ[A, B][Δ⁻¹]` on which the point `(0, 0)` has naive exact order `N`. For `N ≥ 4` it
represents the naive moduli problem `[Γ₁(N)]` (`ModuliProblem.gammaOneNaiveRepresentableBy`). -/
-- Exposed, so that the base of `yOne B N hN` is publicly the locus `naiveExactOrderPreimage`: the
-- statements of `yOneι_base` and `yOne_curve` compare morphisms and curves over the two schemes.
@[expose]
noncomputable def yOne : EllObj B :=
  (universalTate B).baseChangeFunctor.obj (Over.mk (EllipticCurveGeom.naiveExactOrderPreimageι
    (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B)))

/-- The base of `yOne B N hN` is the locus where `(0, 0)` has naive exact order `N`. -/
@[simp]
theorem yOne_base : (yOne B N hN).base = EllipticCurveGeom.naiveExactOrderPreimage
    (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B) :=
  (rfl)

/-- The arrow of `Ell/B` exhibiting the universal elliptic curve over `Y₁(N)` as the restriction
of the universal Tate normal form. -/
noncomputable def yOneι : yOne B N hN ⟶ universalTate B :=
  (universalTate B).baseChangeFunctorHom _

/-- The morphism of bases of `yOneι` is the inclusion of the locus where `(0, 0)` has naive exact
order `N`. -/
@[simp]
theorem yOneι_base : (yOneι B N hN).base = EllipticCurveGeom.naiveExactOrderPreimageι
    (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B) :=
  (baseChangeFunctorHom_base _).trans (Over.mk_hom _)

/-- The structure morphism of `Y₁(N)` is its inclusion in `B × Spec ℤ[A, B][Δ⁻¹]` followed by the
first projection. -/
@[simp]
theorem yOne_structureMap : (yOne B N hN).structureMap = (yOneι B N hN).base ≫ prod.fst := by
  rw [yOneι_base]
  exact (baseChangeFunctor_obj_structureMap (universalTate B) _).trans
    (congrArg (· ≫ prod.fst) (Over.mk_hom _))

/-- The universal elliptic curve over `Y₁(N)` is the base change of the universal Tate normal form
along the inclusion of `Y₁(N)`. -/
theorem yOne_curve : (yOne B N hN).curve = (universalTate B).curve.baseChange
    (EllipticCurveGeom.naiveExactOrderPreimageι (natCast_residueField_universalTate_ne_zero B N hN)
      (universalTatePoint B)) :=
  (rfl)

/-- `Y₁(N)` is a closed subscheme of `B × Spec ℤ[A, B][Δ⁻¹]`. -/
instance isClosedImmersion_yOneι_base : IsClosedImmersion (yOneι B N hN).base := by
  rw [yOneι_base]
  exact EllipticCurveGeom.isClosedImmersion_naiveExactOrderPreimageι _ _ _

/-- **`Y₁(N)` is affine over `B`**: it is a closed subscheme of `B × Spec ℤ[A, B][Δ⁻¹]`. -/
instance isAffineHom_yOne_structureMap : IsAffineHom (yOne B N hN).structureMap := by
  have : IsAffineHom (prod.fst : B ⨯ Spec (.of (ULift.{u} UniversalTate.Ring)) ⟶ B) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' _ _).flip inferInstance
  rw [yOne_structureMap]
  infer_instance

/-- `Y₁(N)` is affine when `B` is, for example for `B = Spec ℤ[1/N]`. -/
instance isAffine_yOne_base [IsAffine B] : IsAffine (yOne B N hN).base :=
  isAffine_of_isAffineHom (yOne B N hN).structureMap

variable {B N hN}

/-- **The point `(0, 0)` of the universal elliptic curve over `Y₁(N)`**: the base change of the
point `(0, 0)` of the universal Tate normal form along `yOneι`. -/
noncomputable def yOnePoint :
    𝟙_ (Over (yOne B N hN).base) ⟶ Over.mk (yOne B N hN).curve.structureMap :=
  EllipticCurveGeom.pointsPullback (yOneι B N hN).isPullback (yOneι B N hN).zero_total
    (universalTatePoint B)

/-- The point `(0, 0)` of the universal elliptic curve over `Y₁(N)` has naive exact order `N`. -/
theorem isOfNaiveExactOrder_yOnePoint :
    (yOne B N hN).curve.IsOfNaiveExactOrder yOnePoint N := by
  rw [← EllipticCurveGeom.isOfNaiveExactOrder_pointsBaseChangeEquiv_iff (yOneι B N hN).isPullback
    (yOneι B N hN).zero_total]
  refine (EllipticCurveGeom.exists_lift_naiveExactOrderPreimageι_iff _ _ ?_).mp
    ⟨𝟙 _, (Category.id_comp _).trans (yOneι_base B N hN).symm⟩
  rw [EllipticCurveGeom.pointsBaseChangeEquiv_left, yOnePoint,
    EllipticCurveGeom.pointsPullback_left_comp]
  simp only [Over.mk_hom]

variable [NeZero N]

-- The universal naive `[Γ₁(N)]`-structure on the universal elliptic curve over `Y₁(N)`: the point
-- `(0, 0)`.
private noncomputable def yOneStructure :
    (ModuliProblem.gammaOneNaive B N).obj (op (yOne B N hN)) :=
  (ModuliProblem.naiveLevelEquiv _).symm
    ⟨(zmodMonoidHomEquiv N
        (𝟙_ (Over (yOne B N hN).base) ⟶ Over.mk (yOne B N hN).curve.structureMap)).symm
        ⟨yOnePoint, isOfNaiveExactOrder_yOnePoint.pow_eq_one⟩,
      EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mpr (by
        rw [← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]
        exact isOfNaiveExactOrder_yOnePoint)⟩

private theorem naiveLevelEquiv_map_yOneStructure {X : EllObj B} (k : X ⟶ yOne B N hN) :
    (ModuliProblem.naiveLevelEquiv X ((ModuliProblem.gammaOneNaive B N).map k.op
        yOneStructure)).1 (.ofAdd 1) =
      EllipticCurveGeom.pointsPullback (k ≫ yOneι B N hN).isPullback
        (k ≫ yOneι B N hN).zero_total (universalTatePoint B) := by
  rw [ModuliProblem.naiveLevelEquiv_map, MonoidHom.comp_apply, yOneStructure,
    Equiv.apply_symm_apply, ← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]
  exact (EllipticCurveGeom.pointsPullback_comp _ _ _ _ _).symm

-- For `N ≥ 4`, the point `P` of a naive `[Γ₁(N)]`-structure satisfies the three conditions of the
-- Tate normal form: `P`, `2P` and `3P` miss the zero section everywhere.
private theorem tate_conditions (h4 : 4 ≤ N) {X : EllObj B}
    {φ : Multiplicative (ZMod N) →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)}
    (hφ : X.curve.IsFiberwiseInjective φ) :
    (∀ s, (φ (.ofAdd 1)).left s ≠ X.curve.zero s) ∧
      (∀ s, ((φ (.ofAdd 1)).left ≫ (X.curve.mulBy 2).left) s ≠ X.curve.zero s) ∧
        ∀ s, ((φ (.ofAdd 1)).left ≫ (X.curve.mulBy 3).left) s ≠ X.curve.zero s := by
  have h := EllipticCurveGeom.isFiberwiseInjective_zmod_iff.mp hφ
  have hn (n : ℕ) (hn : 0 < n) (hnN : n < N) (s : X.base) :
      ((φ (.ofAdd 1)).left ≫ (X.curve.mulBy n).left) s ≠ X.curve.zero s := by
    rw [← Over.comp_left, EllipticCurveGeom.comp_mulBy, zpow_natCast]
    exact h n hn hnN s
  exact ⟨fun s ↦ by simpa using h 1 one_pos (by omega) s, hn 2 two_pos (by omega),
    hn 3 three_pos (by omega)⟩

-- Pulling back the universal naive `[Γ₁(N)]`-structure is a bijection from arrows into `Y₁(N)`.
private theorem bijective_map_yOneStructure (h4 : 4 ≤ N) (X : EllObj B) :
    Function.Bijective fun k : X ⟶ yOne B N hN ↦
      (ModuliProblem.gammaOneNaive B N).map k.op yOneStructure := by
  constructor
  · -- two arrows pulling back the same structure agree after composing with `yOneι`, by the
    -- universal property of the universal Tate normal form, and `yOneι` is a monomorphism on bases
    intro k k' h
    have hp := congrArg (fun α ↦ (ModuliProblem.naiveLevelEquiv X α).1 (.ofAdd 1)) h
    simp only [naiveLevelEquiv_map_yOneStructure] at hp
    obtain ⟨h₁, h₂, h₃⟩ := tate_conditions h4
      (ModuliProblem.naiveLevelEquiv X ((ModuliProblem.gammaOneNaive B N).map k.op
        yOneStructure)).2
    rw [naiveLevelEquiv_map_yOneStructure] at h₁ h₂ h₃
    have hk : k ≫ yOneι B N hN = k' ≫ yOneι B N hN :=
      (existsUnique_hom_universalTate _ h₁ h₂ h₃).unique rfl hp.symm
    refine EllObj.hom_ext_of_comp (yOneι B N hN) hk ?_
    rw [← cancel_mono (yOneι B N hN).base, ← comp_base, hk, comp_base]
  · -- the arrow classifying `(X, P)` lands in `Y₁(N)` because `P` has naive exact order `N`
    intro α
    have hα := (ModuliProblem.naiveLevelEquiv X α).2
    obtain ⟨h₁, h₂, h₃⟩ := tate_conditions h4 hα
    obtain ⟨k₀, hk₀, -⟩ := existsUnique_hom_universalTate _ h₁ h₂ h₃
    obtain ⟨l, hl⟩ := (EllipticCurveGeom.exists_lift_naiveExactOrderPreimageι_iff
      (natCast_residueField_universalTate_ne_zero B N hN) (universalTatePoint B)
      (Z := Over.mk k₀.base)
      (x := EllipticCurveGeom.pointsBaseChangeEquiv k₀.isPullback k₀.zero_total _) (by
        rw [EllipticCurveGeom.pointsBaseChangeEquiv_left, ← hk₀,
          EllipticCurveGeom.pointsPullback_left_comp]
        simp only [Over.mk_hom])).mpr
          ((EllipticCurveGeom.isOfNaiveExactOrder_pointsBaseChangeEquiv_iff _ _).mpr
            (EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp hα))
    obtain ⟨l', hl'⟩ : ∃ l' : X.base ⟶ (yOne B N hN).base, l' ≫ (yOneι B N hN).base = k₀.base :=
      ⟨l, by rw [yOneι_base]; exact hl.trans (Over.mk_hom _)⟩
    refine ⟨Hom.lift (yOneι B N hN) k₀ l' hl', ?_⟩
    apply (ModuliProblem.naiveLevelEquiv X).injective
    apply Subtype.ext
    apply (zmodMonoidHomEquiv N _).injective
    apply Subtype.ext
    simp only [coe_zmodMonoidHomEquiv_apply]
    rw [naiveLevelEquiv_map_yOneStructure, Hom.lift_comp]
    exact hk₀

end EllObj

namespace ModuliProblem

variable {B : Scheme.{u}} {N : ℕ} (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N)

/-- **`Y₁(N)` is a fine moduli scheme for `N ≥ 4`.** If `N ≥ 4` is invertible on `B`, the naive
moduli problem `[Γ₁(N)]` over `Ell/B` is represented by the universal elliptic curve over `Y₁(N)`
(`EllObj.yOne B N hN`): the naive `[Γ₁(N)]`-structures on an object `X` of `Ell/B` correspond to
the arrows `X ⟶ EllObj.yOne B N hN`, by pulling back the point `(0, 0)`
(`naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv`). -/
noncomputable def gammaOneNaiveRepresentableBy :
    (gammaOneNaive B N).RepresentableBy (EllObj.yOne B N hN) :=
  haveI : NeZero N := ⟨by omega⟩
  { homEquiv := Equiv.ofBijective (fun k ↦ (gammaOneNaive B N).map k.op EllObj.yOneStructure)
      (EllObj.bijective_map_yOneStructure (hN := hN) h4 _)
    homEquiv_comp f k := by
      rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, op_comp, Functor.map_comp_apply] }

/-- The naive `[Γ₁(N)]`-structure corresponding to an arrow `k : X ⟶ EllObj.yOne B N hN` sends `1`
to the base change of the point `(0, 0)` of the universal Tate normal form along `k`. -/
theorem naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv {X : EllObj B}
    (k : X ⟶ EllObj.yOne B N hN) :
    (naiveLevelEquiv X ((gammaOneNaiveRepresentableBy hN h4).homEquiv k)).1 (.ofAdd 1) =
      EllipticCurveGeom.pointsPullback (k ≫ EllObj.yOneι B N hN).isPullback
        (k ≫ EllObj.yOneι B N hN).zero_total (EllObj.universalTatePoint B) :=
  haveI : NeZero N := ⟨by omega⟩
  EllObj.naiveLevelEquiv_map_yOneStructure k

/-- The universal naive `[Γ₁(N)]`-structure on `EllObj.yOne B N hN`, attached to its identity
arrow, sends `1` to the point `(0, 0)` of the universal elliptic curve over `Y₁(N)`. -/
theorem naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv_id :
    (naiveLevelEquiv _ ((gammaOneNaiveRepresentableBy hN h4).homEquiv (𝟙 _))).1 (.ofAdd 1) =
      EllObj.yOnePoint := by
  have : NeZero N := ⟨by omega⟩
  rw [gammaOneNaiveRepresentableBy, Equiv.ofBijective_apply, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply, EllObj.yOneStructure, Equiv.apply_symm_apply,
    ← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]

end ModuliProblem

end TauCeti.AlgebraicGeometry
