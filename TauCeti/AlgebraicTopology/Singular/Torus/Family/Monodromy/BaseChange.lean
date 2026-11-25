/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.QuotientPullback
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Pullback
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Monodromy.LocalSystem

/-!
# Equivariant base-change naturality of descended torus families and monodromy

For `P : Y → Λ →ₗ[ℤ] E` with a continuous affine `Γ`-action over `β : Y → Z`, `σ : Γ' →* Γ`,
quotient covering `β' : Y' → Z'`, and `σ`-equivariant `f : C(Y', Y)` covering `fZ : C(Z', Z)`,
`TauCeti.torusFamilyAffineQuotientBaseChangeCommSq` descends `P ∘ f` to `((Y' × E)/Λ)/Γ' → Z'` over
`fZ` (allowing arbitrary `σ : Γ' →* Γ` for cover maps, subcovers, and universal covers):

* `TauCeti.torusFamilyAffineQuotientHomologyMarking_baseChange` and `...Marking_baseChange`:
  naturality of sheet markings.
* `TauCeti.torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_iso` and
  `..._firstHomologyIso`: global local-system base-change naturality.

Here `Y, Y', Z, Z', E : Type` (and `Λ, Γ, Γ' : Type` in `LocalSystemBaseChange`) so `TopCat`,
singular chains, and `Rep ℤ` share universe `0`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
* A. Hatcher, *Algebraic Topology*, CUP, 2002, §§3.H, 4.2.
-/

public section

noncomputable section

open CategoryTheory Function TauCeti.LocalCoefficientSystem

namespace TauCeti

variable {Y Y' Z Z' E : Type} [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]
  [TopologicalSpace Z'] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section FiberAndMarking

variable {Λ Γ Γ' : Type*} [AddCommGroup Λ] (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) [Group Γ] [Group Γ']
  [MulAction Γ Y] [MulAction Γ' Y'] (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) (β' : Y' → Z') (hβ' : IsQuotientCoveringMap β' Γ')
  (σ : Γ' →* Γ) (f : C(Y', Y)) (hf : ∀ g' y', f (g' • y') = σ g' • f y') (fZ : C(Z', Z))

omit [TopologicalSpace Z] β hβ fZ in
/-- The `y'`-sheet homology marking in degree `n` for the pulled-back torus family `P ∘ f`. -/
abbrev torusFamilyBaseChangeQuotientHomologyMarking {z' : Z'} (y' : Y') (hy' : β' y' = z')
    (n : ℕ) :=
  haveI := hβ'.toContinuousConstSMul
  torusFamilyAffineQuotientHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
    (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
    (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
      (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' n

omit [TopologicalSpace Z] β hβ fZ in
/-- The degree-one `y'`-sheet marking for the pulled-back torus family `P ∘ f`. -/
abbrev torusFamilyBaseChangeQuotientMarking {z' : Z'} (y' : Y') (hy' : β' y' = z') :=
  torusFamilyBaseChangeQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
    β' hβ' σ f hf y' hy' 1 ≪≫ₗ exteriorPower.oneEquiv ℤ Λ

/-- **Naturality of sheet homology markings under equivariant base change.** -/
theorem torusFamilyAffineQuotientHomologyMarking_baseChange (hfZ : ∀ y' : Y', fZ (β' y') = β (f y'))
    {z' : Z'} (y' : Y') (hy' : β' y' = z') (hy : β (f y') = fZ z') (n : ℕ)
    (c : ((singularChains ℤ).obj (TopCat.of (torusFamilyBaseChangeQuotientMap P R ρ hequiv b hb hone
      hmul hbmul β' hβ' σ f hf ⁻¹' {z'}))).homology n) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ (f y') hy n (ContinuousMap.singularHomologyMap ℤ n
          ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
            σ f hf fZ hfZ).fiberMap z').hom c) =
      torusFamilyBaseChangeQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β' hβ' σ f hf y' hy' n c := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
  have := hβ'.toContinuousConstSMul
  let e' := torusFamilyBaseChangeQuotientFiberHomeomorph P hcont R ρ hequiv b hb hone hmul hbmul
    hR hbc β' hβ' σ f hf y' hy'
  have hsq : ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β'
      hβ' σ f hf fZ hfZ).fiberMap z').hom.comp (ContinuousMap.ofClass e') =
      (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul
        hbmul hcont hR hbc β hβ (f y') hy)).comp
        ((torusFamilyBaseChangeCommSq P f).fiberMap y').hom :=
    congrArg TopCat.Hom.hom (torusFamilyAffineQuotientBaseChangeCommSq_fiberMap_comp_fiberHomeomorph
      P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy' hy)
  set d := ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass e'.symm) c
  have hc : ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass e') d = c := by
    rw [← ContinuousMap.singularHomologyMap_comp]; simp [Homeomorph.toContinuousMap_comp_symm]
  rw [← hc, ← ContinuousMap.singularHomologyMap_comp, hsq, ContinuousMap.singularHomologyMap_comp]
  exact (torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph P hcont hinj R ρ hequiv b hb hone
      hmul hbmul hR hbc β hβ (f y') hy n _).trans
    ((torusFamilyHomologyMarking_baseChange P hcont hinj f y' n d).trans
      (torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph (P ∘ f)
        (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
        (ρ.comp σ) _ _ _ _ _ _ _ _ β' hβ' y' hy' n d).symm)

/-- **Degree-one sheet marking naturality under equivariant base change.** -/
theorem torusFamilyAffineQuotientMarking_baseChange (hfZ : ∀ y' : Y', fZ (β' y') = β (f y'))
    {z' : Z'} (y' : Y') (hy' : β' y' = z') (hy : β (f y') = fZ z')
    (c : ((singularChains ℤ).obj (TopCat.of (torusFamilyBaseChangeQuotientMap P R ρ hequiv b hb hone
      hmul hbmul β' hβ' σ f hf ⁻¹' {z'}))).homology 1) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ
        (f y') hy (ContinuousMap.singularHomologyMap ℤ 1
          ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
            σ f hf fZ hfZ).fiberMap z').hom c) =
      torusFamilyBaseChangeQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β'
        hβ' σ f hf y' hy' c := by
  simpa only [← oneEquiv_torusFamilyAffineQuotientHomologyMarking, LinearEquiv.trans_apply] using
    congrArg (exteriorPower.oneEquiv ℤ Λ) (torusFamilyAffineQuotientHomologyMarking_baseChange P
      hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy' hy 1 c)

end FiberAndMarking

section LocalSystemBaseChange

variable {Λ Γ Γ' : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (P : Y → Λ →ₗ[ℤ] E)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) [Group Γ] [Group Γ']
  [MulAction Γ Y] [MulAction Γ' Y'] (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) (β' : Y' → Z') (hβ' : IsQuotientCoveringMap β' Γ')
  (σ : Γ' →* Γ) (f : C(Y', Y)) (hf : ∀ g' y', f (g' • y') = σ g' • f y')
  (fZ : C(Z', Z)) (hfZ : ∀ y', fZ (β' y') = β (f y'))
  (L : LiftingFunction
    (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ).hom)
  (L' : LiftingFunction
    (torusFamilyBaseChangeQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β' hβ' σ f hf).hom)

omit [TopologicalSpace Z] β hβ fZ hfZ L in
/-- Global fiber-homology local-system isomorphism in degree `n` for `P ∘ f` over `Z'`. -/
abbrev torusFamilyBaseChangeQuotientHomologyLocalSystemIso (n : ℕ) :=
  haveI := hβ'.toContinuousConstSMul
  torusFamilyAffineQuotientHomologyLocalSystemIso (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
    (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
    (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
      (continuous_const_smul g') (hbc (σ g'))) β' hβ' L' n

omit [TopologicalSpace Z] β hβ fZ hfZ L in
/-- Global degree-one fiber-homology local-system isomorphism for `P ∘ f` over `Z'`. -/
abbrev torusFamilyBaseChangeQuotientFirstHomologyLocalSystemIso :=
  torusFamilyBaseChangeQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul hbmul
    hR hbc β' hβ' σ f hf L' 1 ≪≫ (hβ'.topCat_ofHom.associatedLocalSystemFunctor ℤ).mapIso
      (Rep.mkIso (Representation.exteriorPowerOneEquiv (ρ.comp σ)))

/-- **Global local-system base-change naturality in degree `n`.** -/
theorem torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_iso (n : ℕ) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    (torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
        σ f hf fZ hfZ).fiberLocalSystemMap L' L ℤ n ≫
      (pullback (TopCat.ofHom fZ).hom).map (torusFamilyAffineQuotientHomologyLocalSystemIso P hcont
        hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L n).hom =
      (torusFamilyBaseChangeQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
          hbmul hR hbc β' hβ' σ f hf L' n).hom ≫
        hβ'.topCat_ofHom.associatedLocalSystemMap ℤ (Rep.mkIso (ρ.exteriorPowerCompEquiv σ n)).hom ≫
        (hβ'.topCat_ofHom.associatedLocalSystemBaseChangeIso ℤ hβ.topCat_ofHom (TopCat.ofHom f) hf
          (TopCat.ofHom fZ) (by ext y'; exact hfZ y') (Rep.of (ρ.exteriorPower n))).hom := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
  have := hβ'.toContinuousConstSMul
  let sq := torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β'
    hβ' σ f hf fZ hfZ
  let α : Rep.of (Representation.exteriorPower (ρ.comp σ) n) ⟶
      Rep.res σ (Rep.of (ρ.exteriorPower n)) := (Rep.mkIso (ρ.exteriorPowerCompEquiv σ n)).hom
  have hα : ModuleCat.ofHom (Rep.Hom.hom α).toLinearMap = 𝟙 _ := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro w; simp [α]
  rw [← hβ'.topCat_ofHom.associatedLocalSystemMapOver_eq ℤ hβ.topCat_ofHom (TopCat.ofHom f) hf
    (TopCat.ofHom fZ) (by ext y'; exact hfZ y') α]
  refine NatTrans.ext <| funext fun x ↦ ?_
  obtain ⟨y', hy'⟩ := hβ'.surjective x.as; let e' : β' ⁻¹' {x.as} := ⟨y', hy'⟩
  let e : β ⁻¹' {((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x).as} :=
    ⟨f y', (hfZ y').symm.trans (congrArg fZ hy')⟩
  apply (cancel_mono (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n))
    e).hom).1
  -- Since `((pullback g).obj L).obj x` unfolds semireducible `pullback` to `L.obj (...obj x)`
  -- (above `implicit` transparency), this `calc` block displays each intermediate stage in the
  -- `e`- and `e'`-sheet markings and steps across `pullback` in term mode.
  calc
    ((sq.fiberLocalSystemMap L' L ℤ n).app x ≫
        (torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
          hbmul hR hbc β hβ L n).hom.app ((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x)) ≫
      (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom
    _ = (sq.fiberLocalSystemMap L' L ℤ n).app x ≫
          (fiberLocalSystemSingularObjIso L ℤ n
            ((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x)).hom ≫
          (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
            hR hbc β hβ e.val e.property n).toModuleIso.hom :=
      (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·)
        (torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom P hcont hinj R ρ
          hequiv b hb hone hmul hbmul hR hbc β hβ L e n)
    _ = (fiberLocalSystemSingularObjIso L' ℤ n x).hom ≫
          (torusFamilyBaseChangeQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul
            hbmul hR hbc β' hβ' σ f hf y' hy' n).toModuleIso.hom := by
      apply ModuleCat.hom_ext; ext1 v
      exact (congrArg (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone
          hmul hbmul hR hbc β hβ e.val e.property n)
        (sq.fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app L' L ℤ n x v)).trans
        (torusFamilyAffineQuotientHomologyMarking_baseChange P hcont hinj R ρ hequiv b hb hone
          hmul hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy' e.property n _)
    _ = ((torusFamilyBaseChangeQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone
            hmul hbmul hR hbc β' hβ' σ f hf L' n).hom.app x ≫
          (hβ'.topCat_ofHom.associatedLocalSystemMapOver ℤ hβ.topCat_ofHom (TopCat.ofHom f) hf
            (TopCat.ofHom fZ) (by ext w; exact hfZ w) α).app x) ≫
        (hβ.topCat_ofHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom :=
      ((Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
        (hβ'.topCat_ofHom.associatedLocalSystemMapOver_app_comp_fiberIso_hom ℤ hβ.topCat_ofHom
          (TopCat.ofHom f) hf (TopCat.ofHom fZ) (by ext w; exact hfZ w) α e' e rfl)).trans
        ((torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc (P ∘ f)
          _ _ (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ) _
          (torusFamilyBaseChangeTranslation P f σ hf b hb) _ _ _ _ _ _ β' hβ' L' e' n _).trans
          (congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) hα).trans (Category.comp_id _))))).symm

/-- **Global local-system base-change naturality in degree one.** -/
theorem torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_firstHomologyIso :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    (torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
        σ f hf fZ hfZ).fiberLocalSystemMap L' L ℤ 1 ≫
      (pullback (TopCat.ofHom fZ).hom).map (torusFamilyAffineQuotientFirstHomologyLocalSystemIso
        P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L).hom =
      (torusFamilyBaseChangeQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone
          hmul hbmul hR hbc β' hβ' σ f hf L').hom ≫
        (hβ'.topCat_ofHom.associatedLocalSystemBaseChangeIso ℤ hβ.topCat_ofHom (TopCat.ofHom f) hf
          (TopCat.ofHom fZ) (by ext y'; exact hfZ y') (Rep.of ρ)).hom := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
  have := hβ'.toContinuousConstSMul
  have hone_comp : (Rep.mkIso (ρ.exteriorPowerCompEquiv σ 1)).hom ≫
      (Rep.resFunctor σ).map (Rep.mkIso ρ.exteriorPowerOneEquiv).hom =
      (Rep.mkIso (Representation.exteriorPowerOneEquiv (ρ.comp σ))).hom := by ext w; simp
  simp only [torusFamilyBaseChangeQuotientFirstHomologyLocalSystemIso,
    torusFamilyAffineQuotientFirstHomologyLocalSystemIso_eq, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  slice_lhs 1 2 =>
    rw [torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_iso P hcont hinj R ρ hequiv
      b hb hone hmul hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ L L' 1]
  rw [Category.assoc, Category.assoc,
    ← hβ'.topCat_ofHom.associatedLocalSystemBaseChangeIso_hom_naturality ℤ hβ.topCat_ofHom
      (TopCat.ofHom f) hf (TopCat.ofHom fZ) (by ext y'; exact hfZ y')
      (Rep.mkIso ρ.exteriorPowerOneEquiv).hom,
    ← IsQuotientCoveringMap.associatedLocalSystemMap_comp_assoc, hone_comp]

end LocalSystemBaseChange

end TauCeti
