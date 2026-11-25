/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Trivialization
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Monodromy.Basic
public import TauCeti.Topology.Covering.Quotient

/-!
# Fiber homology local system of a descended family of tori

For a continuous full-lattice family `P : Y → Λ →ₗ[ℤ] E` with a continuous affine `Γ`-action,
representation `ρ : Representation ℤ Γ Λ`, and quotient covering `β : Y → Z` by `Γ`, this file
identifies `TauCeti.fiberLocalSystem L ℤ n` of `((Y × E)/Λ)/Γ → Z` (for any Hurewicz lifting
function `L`) with `IsQuotientCoveringMap.associatedLocalSystem ℤ` of `Rep.of (ρ.exteriorPower n)`
(`Rep.of ρ` in degree `1`):

* `TauCeti.torusFamilyAffineQuotientHomologyLocalSystemIso` and `...FirstHomologyLocalSystemIso`,
  with forward/inverse sheet characterizations (`..._hom_app_comp_fiberIso_hom` and
  `..._inv_app_comp_singularObjIso_hom`).
* `TauCeti.torusFamilyOrbitQuotientHomologyLocalSystemIso` and `...FirstHomologyLocalSystemIso`
  (via `TauCeti.torusFamilyOrbitQuotientLiftingFunction`): specializations over `Y/Γ` for a free
  properly discontinuous continuous `Γ`-action on a second-countable locally compact Hausdorff `Y`.

In `associatedLocalSystem`, `⟦a ⊗ [g • e]⟧ = ⟦g⁻¹ • a ⊗ [e]⟧`, so sheet change `e ↦ g • e` acts by
`g` (`associatedLocalSystemFiberIso_inv_smul`) and loop monodromy `e ↝ g • e` acts by `g⁻¹`,
matching `torusFamilyAffineQuotientHomologyMarking` for uninverted `Rep.of (ρ.exteriorPower n)`.
Here `Y, Z, Λ, E, Γ : Type` so `TopCat.of Z`, singular chains, and `Rep ℤ Γ` share universe `0`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
* A. Hatcher, *Algebraic Topology*, CUP, 2002, §§3.H, 4.2.
-/

public section

noncomputable section

open CategoryTheory Function TauCeti.LocalCoefficientSystem

namespace TauCeti

variable {Y Λ E Γ : Type} [TopologicalSpace Y] [AddCommGroup Λ] [Module.Free ℤ Λ]
  [Module.Finite ℤ Λ] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (hcont : ∀ l, Continuous fun y ↦ P y l)
  (hinj : ∀ y, Injective (P y)) [Group Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ) (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))

section LocalSystem

variable {Z : Type} [TopologicalSpace Z] (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)
  (L : LiftingFunction (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ).hom)

private def sheetMarkingObjIso (n : ℕ) {x : FundamentalGroupoid (TopCat.of Z)} (e : β ⁻¹' {x.as}) :
    (fiberLocalSystem L ℤ n).obj x ≅ ModuleCat.of ℤ (⋀[ℤ]^n Λ) :=
  fiberLocalSystemSingularObjIso L ℤ n x ≪≫ (torusFamilyAffineQuotientHomologyMarking P hcont hinj
    R ρ hequiv b hb hone hmul hbmul hR hbc β hβ e.val e.property n).toModuleIso

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
private theorem sheetMarkingObjIso_comp_fiberIso_inv_eq (n : ℕ)
    {x : FundamentalGroupoid (TopCat.of Z)} (e e' : β ⁻¹' {x.as}) :
    (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom ≫
        (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv =
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e').hom ≫
        (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e').inv := by
  let _ := hβ.topCat_ofHom.mulActionFiber x.as; let g := hβ.topCat_ofHom.fiberEquivGroup e e'
  have hsmul : (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n
        (g • e)).hom =
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom ≫
        ModuleCat.ofHom (ρ.exteriorPower n g) := by
    apply ModuleCat.hom_ext; ext1 v
    exact torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul
      hbmul hR hbc β hβ e.val e.property g (g • e).property n
      ((fiberLocalSystemSingularObjIso L ℤ n x).hom v)
  have hcancel : ModuleCat.ofHom (ρ.exteriorPower n g) ≫
      (ModuleCat.ofHom ((Rep.of (ρ.exteriorPower n)).ρ g⁻¹) ≫
        (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv) =
      (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv := by
    dsimp only [Rep.of_ρ]; ext v; simp [Function.comp_def]
  rw [← (Subtype.ext (by simp [g, IsQuotientCoveringMap.coe_mulActionFiber_smul,
      hβ.topCat_ofHom.fiberEquivGroup_smul_self]) : g • e = e'), hsmul,
    hβ.topCat_ofHom.associatedLocalSystemFiberIso_inv_smul ℤ (Rep.of (ρ.exteriorPower n)) e g,
    Category.assoc, hcancel]

/-- **Global identification of the `n`-th fiber homology local system** with
`Rep.of (ρ.exteriorPower n)`. -/
def torusFamilyAffineQuotientHomologyLocalSystemIso (n : ℕ) :
    fiberLocalSystem L ℤ n ≅
      hβ.topCat_ofHom.associatedLocalSystem ℤ (Rep.of (ρ.exteriorPower n)) := by
  let sheet (x : FundamentalGroupoid (TopCat.of Z)) : β ⁻¹' {x.as} :=
    ⟨Classical.choose (hβ.surjective x.as), Classical.choose_spec (hβ.surjective x.as)⟩
  refine NatIso.ofComponents (fun x ↦
    sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n (sheet x) ≪≫
      (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n))
        (sheet x)).symm) fun {x y} q ↦ ?_
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  let e := sheet x; let e' := hβ.topCat_ofHom.isCoveringMap.monodromy (.mk γ) e
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [sheetMarkingObjIso_comp_fiberIso_inv_eq P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
    β hβ L n (sheet y) e']
  have htr : (fiberLocalSystem L ℤ n).map (.mk γ) ≫
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e').hom =
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom := by
    apply ModuleCat.hom_ext; ext1 v
    exact (congrArg (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone
        hmul hbmul hR hbc β hβ e'.val e'.property n)
      (fiberLocalSystemSingularObjIso_hom_map_mk L ℤ n γ v)).trans
      (torusFamilyAffineQuotientHomologyMarking_transport_monodromy P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ L γ e n _)
  rw [← Category.assoc, htr, Category.assoc,
    hβ.topCat_ofHom.associatedLocalSystemFiberIso_inv_map ℤ (Rep.of (ρ.exteriorPower n)) (.mk γ) e]

/-- **Global identification of the degree-one fiber homology local system** with `Rep.of ρ`. -/
def torusFamilyAffineQuotientFirstHomologyLocalSystemIso :
    fiberLocalSystem L ℤ 1 ≅ hβ.topCat_ofHom.associatedLocalSystem ℤ (Rep.of ρ) :=
  torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
    hR hbc β hβ L 1 ≪≫
    (hβ.topCat_ofHom.associatedLocalSystemFunctor ℤ).mapIso (Rep.mkIso ρ.exteriorPowerOneEquiv)

/-- `torusFamilyAffineQuotientFirstHomologyLocalSystemIso` factors via `exteriorPowerOneEquiv`. -/
theorem torusFamilyAffineQuotientFirstHomologyLocalSystemIso_eq :
    torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ L =
      torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ L 1 ≪≫ (hβ.topCat_ofHom.associatedLocalSystemFunctor ℤ).mapIso
          (Rep.mkIso ρ.exteriorPowerOneEquiv) := (rfl)

variable {x : FundamentalGroupoid (TopCat.of Z)} (e : β ⁻¹' {x.as})

/-- **Sheet-coordinate characterization of `torusFamilyAffineQuotientHomologyLocalSystemIso`.** -/
@[reassoc] theorem torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom
    (n : ℕ) :
    (torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ L n).hom.app x ≫
      (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom =
      (fiberLocalSystemSingularObjIso L ℤ n x).hom ≫
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ e.val e.property n).toModuleIso.hom := by
  dsimp only [torusFamilyAffineQuotientHomologyLocalSystemIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom]
  rw [sheetMarkingObjIso_comp_fiberIso_inv_eq P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
    β hβ L n _ e, Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl

/-- **Inverse sheet-coordinate characterization in degree `n`.** -/
@[reassoc] theorem torusFamilyAffineQuotientHomologyLocalSystemIso_inv_app_comp_singularObjIso_hom
    (n : ℕ) :
    (torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ L n).inv.app x ≫ (fiberLocalSystemSingularObjIso L ℤ n x).hom =
      (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom ≫
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ e.val e.property n).symm.toModuleIso.hom := by
  rw [← cancel_epi ((torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb
      hone hmul hbmul hR hbc β hβ L n).hom.app x), Iso.hom_inv_id_app_assoc,
    torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc]
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro v; simp

/-- **Sheet-coordinate characterization in degree one.** -/
@[reassoc] theorem torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom :
    (torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ L).hom.app x ≫
      (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of ρ) e).hom =
      (fiberLocalSystemSingularObjIso L ℤ 1 x).hom ≫
        (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
          e.val e.property).toModuleIso.hom := by
  dsimp only [torusFamilyAffineQuotientFirstHomologyLocalSystemIso, Iso.trans_hom,
    Functor.mapIso_hom, NatTrans.comp_app, IsQuotientCoveringMap.associatedLocalSystemFunctor_map]
  rw [Category.assoc, hβ.topCat_ofHom.associatedLocalSystemFiberIso_hom_naturality ℤ
      (Rep.mkIso ρ.exteriorPowerOneEquiv).hom e,
    torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc]
  apply ModuleCat.hom_ext; ext1 v
  simpa using oneEquiv_torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone
    hmul hbmul hR hbc β hβ e.val e.property ((fiberLocalSystemSingularObjIso L ℤ 1 x).hom v)

/-- **Inverse sheet-coordinate characterization in degree one.** -/
@[reassoc]
theorem torusFamilyAffineQuotientFirstHomologyLocalSystemIso_inv_app_comp_singularObjIso_hom :
    (torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ L).inv.app x ≫ (fiberLocalSystemSingularObjIso L ℤ 1 x).hom =
      (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of ρ) e).hom ≫
        (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
          e.val e.property).symm.toModuleIso.hom := by
  rw [← cancel_epi ((torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv
      b hb hone hmul hbmul hR hbc β hβ L).hom.app x), Iso.hom_inv_id_app_assoc,
    torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc]
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro v; simp

end LocalSystem

section OrbitQuotient

variable [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
  [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y]

/-- **Fiber homology local system over `Y/Γ`** (free properly discontinuous continuous `Γ`-action on
a second-countable locally compact Hausdorff `Y`), identified with `Rep.of (ρ.exteriorPower n)`. -/
def torusFamilyOrbitQuotientHomologyLocalSystemIso (n : ℕ) :
    fiberLocalSystem (p := torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul
        (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul)
      (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul hR hbc)
      ℤ n ≅ (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (G := Γ) (E := Y)).topCat_ofHom.associatedLocalSystem ℤ (Rep.of (ρ.exteriorPower n)) :=
  torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
    hR hbc (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul hR hbc) n

/-- Unfolding `torusFamilyOrbitQuotientHomologyLocalSystemIso`. -/
theorem torusFamilyOrbitQuotientHomologyLocalSystemIso_eq (n : ℕ) :
    torusFamilyOrbitQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc n =
      torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul
          hR hbc) n := (rfl)

/-- **Degree-one fiber homology local system over `Y/Γ`** (free properly discontinuous continuous
`Γ`-action on a second-countable locally compact Hausdorff `Y`), identified with `Rep.of ρ`. -/
def torusFamilyOrbitQuotientFirstHomologyLocalSystemIso :
    fiberLocalSystem (p := torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul
        (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul)
      (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul hR hbc)
      ℤ 1 ≅ (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (G := Γ) (E := Y)).topCat_ofHom.associatedLocalSystem ℤ (Rep.of ρ) :=
  torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
    hR hbc (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul hR hbc)

/-- Unfolding `torusFamilyOrbitQuotientFirstHomologyLocalSystemIso`. -/
theorem torusFamilyOrbitQuotientFirstHomologyLocalSystemIso_eq :
    torusFamilyOrbitQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc =
      torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul
          hR hbc) := (rfl)

/-- Reading `torusFamilyOrbitQuotientHomologyLocalSystemIso` in sheet `y` over `⟦y⟧`. -/
@[reassoc] theorem torusFamilyOrbitQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom
    (n : ℕ) (y : Y) :
    (torusFamilyOrbitQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc n).hom.app (.mk (Quotient.mk _ y)) ≫
      ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (G := Γ) (E := Y)).topCat_ofHom.associatedLocalSystemFiberIso ℤ
          (Rep.of (ρ.exteriorPower n)) ⟨y, rfl⟩).hom =
      (fiberLocalSystemSingularObjIso (p := torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone
          hmul hbmul (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul)
        (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul
          hR hbc) ℤ n (.mk (Quotient.mk _ y))).hom ≫
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
          y rfl n).toModuleIso.hom :=
  torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom P hcont hinj R ρ hequiv
    b hb hone hmul hbmul hR hbc (Quotient.mk _) _ _ ⟨y, rfl⟩ n

/-- Reading `torusFamilyOrbitQuotientFirstHomologyLocalSystemIso` in sheet `y` over `⟦y⟧`. -/
@[reassoc] theorem torusFamilyOrbitQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom
    (y : Y) :
    (torusFamilyOrbitQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc).hom.app (.mk (Quotient.mk _ y)) ≫
      ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
        (G := Γ) (E := Y)).topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of ρ) ⟨y, rfl⟩).hom =
      (fiberLocalSystemSingularObjIso (p := torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone
          hmul hbmul (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul)
        (torusFamilyOrbitQuotientLiftingFunction P hinj hcont R ρ hequiv b hb hone hmul hbmul
          hR hbc) ℤ 1 (.mk (Quotient.mk _ y))).hom ≫
        (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
          (Quotient.mk _) isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
          y rfl).toModuleIso.hom :=
  torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom P hcont hinj R ρ
    hequiv b hb hone hmul hbmul hR hbc (Quotient.mk _) _ _ ⟨y, rfl⟩

end OrbitQuotient

end TauCeti
