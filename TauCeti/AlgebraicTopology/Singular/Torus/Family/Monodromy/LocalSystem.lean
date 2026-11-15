/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Trivialization
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Monodromy.Basic

/-!
# Fiber homology local system of a descended family of tori

For a continuous full-lattice family `P : Y → Λ →ₗ[ℤ] E` with a continuous affine `Γ`-action
(`TauCeti.torusFamilyAffineMulAction`), lattice representation `ρ : Representation ℤ Γ Λ`, and
quotient covering `β : Y → Z` by `Γ`, this file identifies the fiber homology local system
`TauCeti.fiberLocalSystem L ℤ n` of `((Y × E)/Λ)/Γ → Z` with the local system on `Z` associated to
`Rep.of (ρ.exteriorPower n)` (`Rep.of ρ` in degree `1`):

* `TauCeti.torusFamilyAffineQuotientHomologyLocalSystemIso`,
  `TauCeti.torusFamilyAffineQuotientFirstHomologyLocalSystemIso`, and their sheet characterizations
  `TauCeti.torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom` and
  `TauCeti.torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom`.
* `TauCeti.torusFamilyAffineQuotientLiftingFunction`,
  `TauCeti.torusFamilyOrbitQuotientLiftingFunction`,
  `TauCeti.torusFamilyOrbitQuotientHomologyLocalSystemIso`, and
  `TauCeti.torusFamilyOrbitQuotientFirstHomologyLocalSystemIso`: canonical Hurewicz lifting
  functions and local-system identifications over normal paracompact `Z` and `Y/Γ`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
* A. Hatcher, *Algebraic Topology*, CUP, 2002, §§3.H, 4.2.
-/

public section

noncomputable section

open CategoryTheory Function TauCeti.LocalCoefficientSystem

universe u

/-- View `hβ : IsQuotientCoveringMap β G` on the bundled morphism `TopCat.of Y ⟶ TopCat.of Z`. -/
abbrev IsQuotientCoveringMap.ofTopHom {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {G : Type u} [Group G] [MulAction G Y] {β : Y → Z} (hβ : IsQuotientCoveringMap β G) :
    IsQuotientCoveringMap (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) G := hβ

namespace TauCeti

variable {Y Λ E Γ : Type} [TopologicalSpace Y] [AddCommGroup Λ] [Module.Free ℤ Λ]
  [Module.Finite ℤ Λ] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (hcont : ∀ l, Continuous fun y ↦ P y l)
  (hinj : ∀ y, Injective (P y)) [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))

/-! ### Global identification of the fiber homology local system -/

section LocalSystem

variable {Z : Type} [TopologicalSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)
  (L : LiftingFunction
    (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ).hom)

private def sheetMarkingObjIso (n : ℕ) {x : FundamentalGroupoid (TopCat.of Z)} (e : β ⁻¹' {x.as}) :
    (fiberLocalSystem L ℤ n).obj x ≅ ModuleCat.of ℤ (⋀[ℤ]^n Λ) :=
  fiberLocalSystemSingularObjIso L ℤ n x ≪≫
    (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ e.1 e.2 n).toModuleIso

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
private theorem sheetMarkingObjIso_comp_fiberIso_inv_eq (n : ℕ)
    {x : FundamentalGroupoid (TopCat.of Z)} (e e' : β ⁻¹' {x.as}) :
    (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom ≫
        (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv =
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e').hom ≫
        (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e').inv := by
  let _ := hβ.ofTopHom.mulActionFiber x.as
  let g := hβ.ofTopHom.fiberEquivGroup e e'
  have he' : g • e = e' := Subtype.ext (by
    simp only [g, IsQuotientCoveringMap.coe_mulActionFiber_smul,
      hβ.ofTopHom.fiberEquivGroup_smul_self])
  rw [← he']
  have hsmul : (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n
        (g • e)).hom =
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom ≫
        ModuleCat.ofHom (ρ.exteriorPower n g) := by
    apply ModuleCat.hom_ext; ext1 v
    dsimp only [sheetMarkingObjIso, Iso.trans_hom, LinearEquiv.toModuleIso_hom]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ e.1 e.2 g (g • e).2 n ((fiberLocalSystemSingularObjIso L ℤ n x).hom v)
  rw [hsmul, hβ.ofTopHom.associatedLocalSystemFiberIso_inv_smul ℤ (Rep.of (ρ.exteriorPower n)) e g,
    Category.assoc]
  have hcancel : ModuleCat.ofHom (ρ.exteriorPower n g) ≫
      (ModuleCat.ofHom ((Rep.of (ρ.exteriorPower n)).ρ g⁻¹) ≫
        (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv) =
      (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv := by
    rw [← Category.assoc, ← ModuleCat.ofHom_comp]
    change ModuleCat.ofHom ((ρ.exteriorPower n g⁻¹).comp (ρ.exteriorPower n g)) ≫ _ = _
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id,
      ModuleCat.ofHom_id, Category.id_comp]
  rw [hcancel]

/-- **Global identification of the `n`-th fiber homology local system** with the local system on `Z`
associated to `Rep.of (ρ.exteriorPower n)`. -/
def torusFamilyAffineQuotientHomologyLocalSystemIso (n : ℕ) :
    fiberLocalSystem L ℤ n ≅ hβ.ofTopHom.associatedLocalSystem ℤ (Rep.of (ρ.exteriorPower n)) := by
  let sheet (x : FundamentalGroupoid (TopCat.of Z)) : β ⁻¹' {x.as} :=
    ⟨Classical.choose (hβ.surjective x.as), Classical.choose_spec (hβ.surjective x.as)⟩
  refine NatIso.ofComponents
    (fun x ↦ sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n
      (sheet x) ≪≫ (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n))
        (sheet x)).symm) ?_
  intro x y q
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  let e := sheet x
  let e' := hβ.ofTopHom.isCoveringMap.monodromy (.mk γ) e
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [sheetMarkingObjIso_comp_fiberIso_inv_eq P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
    β hβ L n (sheet y) e']
  have htr : (fiberLocalSystem L ℤ n).map (.mk γ) ≫
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e').hom =
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom := by
    apply ModuleCat.hom_ext; ext1 v
    dsimp only [sheetMarkingObjIso, Iso.trans_hom, LinearEquiv.toModuleIso_hom]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (congrArg
      (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ e'.1 e'.2 n)
      (fiberLocalSystemSingularObjIso_hom_map_mk L ℤ n γ v)).trans
      (torusFamilyAffineQuotientHomologyMarking_transport_monodromy P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ L γ e n _)
  rw [← Category.assoc, htr, Category.assoc,
    hβ.ofTopHom.associatedLocalSystemFiberIso_inv_map ℤ (Rep.of (ρ.exteriorPower n)) (.mk γ) e]

/-- **Sheet-coordinate characterization of `torusFamilyAffineQuotientHomologyLocalSystemIso`.**
Reading the local-system isomorphism in any sheet `e` over `x.as` recovers the `e`-sheet marking. -/
@[reassoc]
theorem torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom (n : ℕ)
    {x : FundamentalGroupoid (TopCat.of Z)} (e : β ⁻¹' {x.as}) :
    (torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ L n).hom.app x ≫
      (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom =
      (fiberLocalSystemSingularObjIso L ℤ n x).hom ≫
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ e.1 e.2 n).toModuleIso.hom := by
  let e₀ : β ⁻¹' {x.as} :=
    ⟨Classical.choose (hβ.surjective x.as), Classical.choose_spec (hβ.surjective x.as)⟩
  dsimp only [torusFamilyAffineQuotientHomologyLocalSystemIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom]
  rw [sheetMarkingObjIso_comp_fiberIso_inv_eq P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
      β hβ L n e₀ e, Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl

/-- **Global identification of the degree-one fiber homology local system** with `Rep.of ρ`. -/
def torusFamilyAffineQuotientFirstHomologyLocalSystemIso :
    fiberLocalSystem L ℤ 1 ≅ hβ.ofTopHom.associatedLocalSystem ℤ (Rep.of ρ) :=
  torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ L 1 ≪≫
    (hβ.ofTopHom.associatedLocalSystemFunctor ℤ).mapIso (Rep.mkIso ρ.exteriorPowerOneEquiv)

/-- **Sheet-coordinate characterization in degree one.** -/
@[reassoc]
theorem torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom
    {x : FundamentalGroupoid (TopCat.of Z)} (e : β ⁻¹' {x.as}) :
    (torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ L).hom.app x ≫
      (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of ρ) e).hom =
      (fiberLocalSystemSingularObjIso L ℤ 1 x).hom ≫
        (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ e.1 e.2).toModuleIso.hom := by
  dsimp only [torusFamilyAffineQuotientFirstHomologyLocalSystemIso, Iso.trans_hom,
    Functor.mapIso_hom, NatTrans.comp_app, IsQuotientCoveringMap.associatedLocalSystemFunctor_map]
  rw [Category.assoc,
    hβ.ofTopHom.associatedLocalSystemFiberIso_hom_naturality ℤ
      (Rep.mkIso ρ.exteriorPowerOneEquiv).hom e,
    torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc]
  apply ModuleCat.hom_ext; ext1 v
  simpa using oneEquiv_torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone
    hmul hbmul hR hbc β hβ e.1 e.2 ((fiberLocalSystemSingularObjIso L ℤ 1 x).hom v)

end LocalSystem

/-- A Hurewicz lifting function for the descended torus family over normal paracompact `Z`. -/
def torusFamilyAffineQuotientLiftingFunction
    {Z : Type} [TopologicalSpace Z] [NormalSpace Z] [ParacompactSpace Z]
    (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) :
    LiftingFunction
      (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ).hom :=
  (isHurewiczFibration_torusFamilyAffineQuotientLift.{0} P hinj hcont R ρ hequiv b hb hone hmul
    hbmul hR hbc β hβ).nonempty_liftingFunction.some

section OrbitQuotient

variable [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y]

/-- **Canonical Hurewicz lifting function over `Y/Γ`.** -/
def torusFamilyOrbitQuotientLiftingFunction :
    LiftingFunction (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul
      (Quotient.mk (MulAction.orbitRel Γ Y))
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul).hom :=
  haveI : T2Space (MulAction.orbitRel.Quotient Γ Y) :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
  haveI : LocallyCompactSpace (MulAction.orbitRel.Quotient Γ Y) :=
    MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  haveI : SecondCountableTopology (MulAction.orbitRel.Quotient Γ Y) :=
    ContinuousConstSMul.secondCountableTopology
  torusFamilyAffineQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
    (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- **Fiber homology local system over `Y/Γ`**, identified with `Rep.of (ρ.exteriorPower n)`. -/
def torusFamilyOrbitQuotientHomologyLocalSystemIso (n : ℕ) :
    fiberLocalSystem
      (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)
      ℤ n ≅ (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (G := Γ) (E := Y)).ofTopHom.associatedLocalSystem ℤ (Rep.of (ρ.exteriorPower n)) :=
  torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
    hR hbc (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc) n

/-- **Degree-one fiber homology local system over `Y/Γ`**, identified with `Rep.of ρ`. -/
def torusFamilyOrbitQuotientFirstHomologyLocalSystemIso :
    fiberLocalSystem
      (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)
      ℤ 1 ≅ (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (G := Γ) (E := Y)).ofTopHom.associatedLocalSystem ℤ (Rep.of ρ) :=
  torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
    hbmul hR hbc (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)

/-- Reading `torusFamilyOrbitQuotientHomologyLocalSystemIso` in the `y`-sheet coordinate over
`⟦y⟧ ∈ Y/Γ` recovers the `y`-sheet homology marking. -/
theorem torusFamilyOrbitQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom
    (n : ℕ) (y : Y) :
    let hβ := isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ) (E := Y)
    let L := torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc
    (torusFamilyOrbitQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc n).hom.app (.mk (Quotient.mk _ y)) ≫
      (hβ.ofTopHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) ⟨y, rfl⟩).hom =
      (fiberLocalSystemSingularObjIso L ℤ n (.mk (Quotient.mk _ y))).hom ≫
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc (Quotient.mk (MulAction.orbitRel Γ Y)) hβ y rfl n).toModuleIso.hom :=
  torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom P hcont hinj R ρ hequiv
    b hb hone hmul hbmul hR hbc (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)
    n ⟨y, rfl⟩

end OrbitQuotient

end TauCeti
