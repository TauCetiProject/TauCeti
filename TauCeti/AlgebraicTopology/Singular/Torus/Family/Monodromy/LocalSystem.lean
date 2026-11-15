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

For a continuous family of full lattices `P : Y → Λ →ₗ[ℤ] E` equipped with a continuous affine
`Γ`-action (`TauCeti.torusFamilyAffineMulAction`) with lattice representation
`ρ : Representation ℤ Γ Λ` and a quotient covering map `β : Y → Z` by `Γ`, this file identifies the
fiber homology local system `TauCeti.fiberLocalSystem L ℤ n` of the descended torus family
`((Y × E)/Λ)/Γ → Z` with the local coefficient system on `Z` associated to
`Rep.of (ρ.exteriorPower n)` (and in degree `1` with `Rep.of ρ`).

When `Z` is normal and paracompact — in particular for `Z = Y/Γ` when `Γ` acts freely, properly
discontinuously, and continuously on a second-countable locally compact Hausdorff space `Y` (such as
`TauCeti.freeLocus Γ Y₀`) — `TauCeti.isHurewiczFibration_torusFamilyAffineQuotientLift` supplies a
canonical Hurewicz lifting function with no external lifting hypothesis.

## Main definitions

* `TauCeti.torusFamilyAffineQuotientHomologyLocalSystemIso`: global isomorphism of local systems on
  `Z` between `TauCeti.fiberLocalSystem L ℤ n` and
  `IsQuotientCoveringMap.associatedLocalSystem ℤ` of `Rep.of (ρ.exteriorPower n)`.
* `TauCeti.torusFamilyAffineQuotientFirstHomologyLocalSystemIso`: degree-one isomorphism between
  `TauCeti.fiberLocalSystem L ℤ 1` and the local system associated to `Rep.of ρ`.
* `TauCeti.torusFamilyAffineQuotientLiftingFunction`,
  `TauCeti.torusFamilyOrbitQuotientLiftingFunction`: canonical Hurewicz lifting functions over a
  normal paracompact base `Z` and over the orbit space `Y/Γ`.
* `TauCeti.torusFamilyOrbitQuotientHomologyLocalSystemIso`,
  `TauCeti.torusFamilyOrbitQuotientFirstHomologyLocalSystemIso`: unconditional local-system
  identifications over `Y/Γ`.

## Main results

* `TauCeti.torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom`,
  `TauCeti.torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom`: at every
  point `x` and *every* sheet `e` over `x.as`, reading the local-system isomorphism in the `e`-sheet
  coordinate recovers the `e`-sheet homology marking.
* `TauCeti.torusFamilyOrbitQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom`: sheet
  characterization over `Y/Γ`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
* A. Hatcher, *Algebraic Topology*, CUP, 2002, §§3.H, 4.2.
-/

public section

noncomputable section

open CategoryTheory Function TauCeti.LocalCoefficientSystem

namespace TauCeti

/-! ### Global identification of the fiber homology local system -/

section LocalSystem

variable {Y Z Λ E Γ : Type} [TopologicalSpace Y] [TopologicalSpace Z]
  [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ)
  (L : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    LiftingFunction (TopCat.ofHom
      ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g),
        continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
          hβ.continuous⟩).hom)

/-- The `e`-sheet marking at `x : FundamentalGroupoid (TopCat.of Z)`, packaged as an isomorphism in
`ModuleCat ℤ` from `(fiberLocalSystem L ℤ n).obj x` to `ModuleCat.of ℤ (⋀[ℤ]^n Λ)`. -/
private def sheetMarkingObjIso (n : ℕ) {x : FundamentalGroupoid (TopCat.of Z)}
    (e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹' {x.as}) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    (fiberLocalSystem L ℤ n).obj x ≅ ModuleCat.of ℤ (⋀[ℤ]^n Λ) :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  fiberLocalSystemSingularObjIso L ℤ n x ≪≫
    (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ e.1 e.2 n).toModuleIso

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
/-- Composing `sheetMarkingObjIso` with the inverse sheet coordinate of `associatedLocalSystem` is
independent of the chosen sheet `e` over `x.as`. -/
private theorem sheetMarkingObjIso_comp_fiberIso_inv_eq (n : ℕ)
    {x : FundamentalGroupoid (TopCat.of Z)}
    (e e' : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹' {x.as}) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom ≫
        (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv =
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e').hom ≫
        (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e').inv := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  let _ := hβHom.mulActionFiber x.as
  let g := hβHom.fiberEquivGroup e e'
  have he' : g • e = e' := Subtype.ext (by
    simp only [g, IsQuotientCoveringMap.coe_mulActionFiber_smul, hβHom.fiberEquivGroup_smul_self])
  dsimp only
  rw [← he']
  have hsmul :
      (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n
          (g • e)).hom =
        (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e).hom ≫
          ModuleCat.ofHom (ρ.exteriorPower n g) := by
    apply ModuleCat.hom_ext
    ext1 v
    dsimp only [sheetMarkingObjIso, Iso.trans_hom, LinearEquiv.toModuleIso_hom]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact torusFamilyAffineQuotientHomologyMarking_smul P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ e.1 e.2 g (g • e).2 n ((fiberLocalSystemSingularObjIso L ℤ n x).hom v)
  rw [hsmul, hβHom.associatedLocalSystemFiberIso_inv_smul ℤ (Rep.of (ρ.exteriorPower n)) e g,
    Category.assoc]
  have hcancel : ModuleCat.ofHom (ρ.exteriorPower n g) ≫
      (ModuleCat.ofHom ((Rep.of (ρ.exteriorPower n)).ρ g⁻¹) ≫
        (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv) =
      (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).inv := by
    rw [← Category.assoc, ← ModuleCat.ofHom_comp]
    -- `(Rep.of (ρ.exteriorPower n)).ρ` is definitionally `ρ.exteriorPower n`, and `g⁻¹ * g = 1`.
    change ModuleCat.ofHom ((ρ.exteriorPower n g⁻¹).comp (ρ.exteriorPower n g)) ≫ _ = _
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id,
      ModuleCat.ofHom_id, Category.id_comp]
  rw [hcancel]

/-- **Global identification of the `n`-th fiber homology local system.** For any quotient covering
`β : Y → Z` by `Γ` and any Hurewicz lifting function `L` of the descended torus family, the `n`-th
fiber homology local system `TauCeti.fiberLocalSystem L ℤ n` is canonically isomorphic to the local
coefficient system on `Z` associated to `Rep.of (ρ.exteriorPower n)`. -/
def torusFamilyAffineQuotientHomologyLocalSystemIso (n : ℕ) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    fiberLocalSystem L ℤ n ≅ hβHom.associatedLocalSystem ℤ (Rep.of (ρ.exteriorPower n)) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  let sheet (x : FundamentalGroupoid (TopCat.of Z)) :
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹' {x.as} :=
    ⟨Classical.choose (hβ.surjective x.as), Classical.choose_spec (hβ.surjective x.as)⟩
  refine NatIso.ofComponents
    (fun x ↦ sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n
      (sheet x) ≪≫
        (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) (sheet x)).symm) ?_
  intro x y q
  induction q using Path.Homotopic.Quotient.ind with | mk γ =>
  let e := sheet x
  let e' := hβHom.isCoveringMap.monodromy (.mk γ) e
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [sheetMarkingObjIso_comp_fiberIso_inv_eq P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
    β hβ L n (sheet y) e']
  have htr :
      (fiberLocalSystem L ℤ n).map (.mk γ) ≫
          (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n e').hom =
        (sheetMarkingObjIso P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n
          e).hom := by
    apply ModuleCat.hom_ext
    ext1 v
    dsimp only [sheetMarkingObjIso, Iso.trans_hom, LinearEquiv.toModuleIso_hom]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact (congrArg
      (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ e'.1 e'.2 n)
      (fiberLocalSystemSingularObjIso_hom_map_mk L ℤ n γ v)).trans
      (torusFamilyAffineQuotientHomologyMarking_transport_monodromy P hcont hinj R ρ hequiv b hb
        hone hmul hbmul hR hbc β hβ L γ e n _)
  rw [← Category.assoc, htr, Category.assoc,
    hβHom.associatedLocalSystemFiberIso_inv_map ℤ (Rep.of (ρ.exteriorPower n)) (.mk γ) e]

/-- **Sheet-coordinate characterization of `torusFamilyAffineQuotientHomologyLocalSystemIso`.** At
every point `x` and *every* sheet `e` over `x.as` (not only the internally chosen one), reading
`torusFamilyAffineQuotientHomologyLocalSystemIso` in the `e`-sheet coordinate recovers the `e`-sheet
homology marking. -/
@[reassoc]
theorem torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom (n : ℕ)
    {x : FundamentalGroupoid (TopCat.of Z)}
    (e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹' {x.as}) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    (torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ L n).hom.app x ≫
      (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom =
      (fiberLocalSystemSingularObjIso L ℤ n x).hom ≫
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ e.1 e.2 n).toModuleIso.hom := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let e₀ : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹' {x.as} :=
    ⟨Classical.choose (hβ.surjective x.as), Classical.choose_spec (hβ.surjective x.as)⟩
  dsimp only [torusFamilyAffineQuotientHomologyLocalSystemIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom]
  rw [sheetMarkingObjIso_comp_fiberIso_inv_eq P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
      β hβ L n e₀ e,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- **Global identification of the degree-one fiber homology local system** with the local
coefficient system on `Z` associated to `Rep.of ρ`. -/
def torusFamilyAffineQuotientFirstHomologyLocalSystemIso :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    fiberLocalSystem L ℤ 1 ≅ hβHom.associatedLocalSystem ℤ (Rep.of ρ) :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ L 1 ≪≫
    (hβHom.associatedLocalSystemFunctor ℤ).mapIso (Rep.mkIso ρ.exteriorPowerOneEquiv)

/-- **Sheet-coordinate characterization in degree one.** At every sheet `e` over `x.as`, reading
`torusFamilyAffineQuotientFirstHomologyLocalSystemIso` in the `e`-sheet coordinate recovers
`TauCeti.torusFamilyAffineQuotientMarking`. -/
@[reassoc]
theorem torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom
    {x : FundamentalGroupoid (TopCat.of Z)}
    (e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹' {x.as}) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    (torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ L).hom.app x ≫
      (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of ρ) e).hom =
      (fiberLocalSystemSingularObjIso L ℤ 1 x).hom ≫
        (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc β hβ e.1 e.2).toModuleIso.hom := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  dsimp only [torusFamilyAffineQuotientFirstHomologyLocalSystemIso, Iso.trans_hom,
    Functor.mapIso_hom, NatTrans.comp_app, IsQuotientCoveringMap.associatedLocalSystemFunctor_map]
  rw [Category.assoc,
    hβHom.associatedLocalSystemFiberIso_hom_naturality ℤ (Rep.mkIso ρ.exteriorPowerOneEquiv).hom e,
    torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc]
  apply ModuleCat.hom_ext
  ext1 v
  simpa using oneEquiv_torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone
    hmul hbmul hR hbc β hβ e.1 e.2 ((fiberLocalSystemSingularObjIso L ℤ 1 x).hom v)

end LocalSystem

/-! ### Canonical Hurewicz lifting functions and the orbit-space local system -/

section CanonicalOrbitQuotient

variable {Y Λ E Γ : Type} [TopologicalSpace Y]
  [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g : Γ, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))

/-- A Hurewicz lifting function for the descended torus family over a normal paracompact base `Z`,
constructed via `TauCeti.isHurewiczFibration_torusFamilyAffineQuotientLift`. -/
def torusFamilyAffineQuotientLiftingFunction
    {Z : Type} [TopologicalSpace Z] [NormalSpace Z] [ParacompactSpace Z]
    (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    LiftingFunction (TopCat.ofHom
      ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g),
        continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
          hβ.continuous⟩).hom :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  (isHurewiczFibration_torusFamilyAffineQuotientLift.{0} P hinj hcont R ρ hequiv b hb hone hmul
    hbmul hR hbc β hβ).nonempty_liftingFunction.some

/-- **Canonical Hurewicz lifting function over `Y/Γ`.** When `Γ` acts freely, properly
discontinuously, and continuously on a second-countable locally compact Hausdorff space `Y` (such as
`TauCeti.freeLocus Γ Y₀`), the descended torus family over `Y/Γ` carries a Hurewicz lifting function
with no auxiliary covering or paracompactness hypotheses. -/
def torusFamilyOrbitQuotientLiftingFunction
    [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y] :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    LiftingFunction (TopCat.ofHom
      ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        (Quotient.mk (MulAction.orbitRel Γ Y))
        (fun g _ ↦ (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
          (G := Γ) (E := Y)).map_smul g),
        continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
          continuous_quot_mk⟩).hom :=
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  haveI : T2Space (MulAction.orbitRel.Quotient Γ Y) :=
    t2Space_of_properlyDiscontinuousSMul_of_t2Space
  haveI : LocallyCompactSpace (MulAction.orbitRel.Quotient Γ Y) :=
    MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace
  haveI : SecondCountableTopology (MulAction.orbitRel.Quotient Γ Y) :=
    ContinuousConstSMul.secondCountableTopology
  torusFamilyAffineQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
    (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- **Fiber homology local system over the canonical orbit space `Y/Γ`**, identified with the local
system associated to `Rep.of (ρ.exteriorPower n)` with no external lifting-function hypothesis. -/
def torusFamilyOrbitQuotientHomologyLocalSystemIso
    [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y] (n : ℕ) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨Quotient.mk (MulAction.orbitRel Γ Y), continuous_quot_mk⟩ :
        TopCat.of Y ⟶ TopCat.of (MulAction.orbitRel.Quotient Γ Y)) Γ :=
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    fiberLocalSystem
      (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)
      ℤ n ≅ hβHom.associatedLocalSystem ℤ (Rep.of (ρ.exteriorPower n)) :=
  torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
    hR hbc (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc) n

/-- **Degree-one fiber homology local system over the canonical orbit space `Y/Γ`**, identified with
the local system associated to `Rep.of ρ` with no external lifting-function hypothesis. -/
def torusFamilyOrbitQuotientFirstHomologyLocalSystemIso
    [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y] :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨Quotient.mk (MulAction.orbitRel Γ Y), continuous_quot_mk⟩ :
        TopCat.of Y ⟶ TopCat.of (MulAction.orbitRel.Quotient Γ Y)) Γ :=
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    fiberLocalSystem
      (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)
      ℤ 1 ≅ hβHom.associatedLocalSystem ℤ (Rep.of ρ) :=
  torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
    hbmul hR hbc (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)

/-- At any sheet `y : Y` over `⟦y⟧ ∈ Y/Γ`, reading `torusFamilyOrbitQuotientHomologyLocalSystemIso`
in the `y`-sheet coordinate recovers the `y`-sheet homology marking. -/
theorem torusFamilyOrbitQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom
    [T2Space Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [ProperlyDiscontinuousSMul Γ Y] [ContinuousConstSMul Γ Y] [IsCancelSMul Γ Y]
    (n : ℕ) (y : Y) :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨Quotient.mk (MulAction.orbitRel Γ Y), continuous_quot_mk⟩ :
        TopCat.of Y ⟶ TopCat.of (MulAction.orbitRel.Quotient Γ Y)) Γ :=
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    let L := torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc
    (torusFamilyOrbitQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc n).hom.app (.mk (Quotient.mk _ y)) ≫
      (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) ⟨y, rfl⟩).hom =
      (fiberLocalSystemSingularObjIso L ℤ n (.mk (Quotient.mk _ y))).hom ≫
        (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
          hR hbc (Quotient.mk (MulAction.orbitRel Γ Y))
          isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul y rfl n).toModuleIso.hom :=
  torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom P hcont hinj R ρ hequiv
    b hb hone hmul hbmul hR hbc (Quotient.mk (MulAction.orbitRel Γ Y))
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (torusFamilyOrbitQuotientLiftingFunction P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc)
    n ⟨y, rfl⟩

end CanonicalOrbitQuotient

end TauCeti
