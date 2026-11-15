/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.AffineAction
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Pullback
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Monodromy.LocalSystem

/-!
# Equivariant base-change naturality of descended torus families and monodromy

Let `P : Y → Λ →ₗ[ℤ] E` be a continuous family of full lattices equipped with a continuous affine
`Γ`-action (`TauCeti.torusFamilyAffineMulAction`) over a quotient covering `β : Y → Z` by `Γ`. Given
a group homomorphism `σ : Γ' →* Γ`, a continuous `σ`-equivariant base map `f : C(Y', Y)`, and a
quotient covering `β' : Y' → Z'` by `Γ'` covering `fZ : C(Z', Z)` (`∀ y', fZ (β' y') = β (f y')`),
the pulled-back family `P ∘ f` inherits a continuous affine `Γ'`-action
(`TauCeti.torusFamilyAffineBaseChangeHom`) and descends to `((Y' × E)/Λ)/Γ' → Z'`.

This file constructs the induced commutative square of descended torus families over `fZ`, proves
that it is fiberwise a homeomorphism, and proves naturality of the sheet-indexed homology markings
and of the global fiber-homology local-system identifications
`TauCeti.torusFamilyAffineQuotientHomologyLocalSystemIso` and
`TauCeti.torusFamilyAffineQuotientFirstHomologyLocalSystemIso` with respect to
`IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso`.

## Main results

* `TauCeti.continuous_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom`: continuity of the
  descended total-space map `((Y' × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ`.
* `TauCeti.torusFamilyAffineQuotientBaseChangeCommSq`,
  `TauCeti.isIso_torusFamilyAffineQuotientBaseChangeCommSq_fiberMap`: the `TopCat` commutative
  square of descended torus projections over `fZ` and its fiberwise `IsIso` property.
* `TauCeti.torusFamilyAffineQuotientHomologyMarking_baseChange`,
  `TauCeti.torusFamilyAffineQuotientMarking_baseChange`: naturality of sheet-indexed homology
  markings in degree `n` and degree `1`.
* `TauCeti.torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_iso`,
  `TauCeti.torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_firstHomologyIso`: global
  local-system base-change naturality in degree `n` and degree `1`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
* A. Hatcher, *Algebraic Topology*, CUP, 2002, §§3.H, 4.2.
-/

public section

noncomputable section

open CategoryTheory Function TauCeti.LocalCoefficientSystem

namespace TauCeti

section CommSq

variable {Y Y' Z Z' E : Type*}
  [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z] [TopologicalSpace Z']
  {Λ : Type*} [AddCommGroup Λ] [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E]
  (P : Y → Λ →ₗ[ℤ] E)
  {Γ Γ' : Type*} [Group Γ] [Group Γ'] [MulAction Γ Y] [MulAction Γ' Y']
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))

omit [ContinuousAdd E] in
/-- The map of descended torus families `((Y' × E)/Λ)/Γ' → ((Y × E)/Λ)/Γ` induced by a continuous
`σ`-equivariant base map `f : C(Y', Y)` is continuous. -/
theorem continuous_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom
    (σ : Γ' →* Γ) (f : C(Y', Y)) (hf : ∀ (g' : Γ') (y' : Y'), f (g' • y') = σ g' • f y') :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    Continuous (MulActionHom.orbitRelQuotientMap
      (torusFamilyAffineBaseChangeHom P b hb R ρ hequiv hone hmul hbmul σ f hf)) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  let _ : Setoid (AddAction.orbitRel.Quotient Λ (Y' × E)) := MulAction.orbitRel Γ' _
  let _ : Setoid (AddAction.orbitRel.Quotient Λ (Y × E)) := MulAction.orbitRel Γ _
  let φ := torusFamilyAffineBaseChangeHom P b hb R ρ hequiv hone hmul hbmul σ f hf
  have hcomp : φ.orbitRelQuotientMap ∘ Quotient.mk' =
      Quotient.mk' ∘ torusFamilyBaseChangeMap P f := by
    ext x
    exact (MulActionHom.orbitRelQuotientMap_mk φ x).trans
      (congrArg (Quotient.mk _)
        (torusFamilyAffineBaseChangeHom_apply P b hb R ρ hequiv hone hmul hbmul σ f hf x))
  rw [isQuotientMap_quotient_mk'.continuous_iff, hcomp]
  exact continuous_quot_mk.comp (continuous_torusFamilyBaseChangeMap P f f.continuous)

end CommSq

section FiberAndMarking

variable {Y Y' Z Z' E : Type}
  [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z] [TopologicalSpace Z']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  {Γ Γ' : Type*} [Group Γ] [Group Γ'] [MulAction Γ Y] [MulAction Γ' Y']
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
  (β' : Y' → Z') (hβ' : IsQuotientCoveringMap β' Γ')
  (σ : Γ' →* Γ) (f : C(Y', Y)) (hf : ∀ (g' : Γ') (y' : Y'), f (g' • y') = σ g' • f y')
  (fZ : C(Z', Z))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] hcont hinj hR hbc in
/-- **Commutative square of descended torus families under equivariant base change.** A continuous
`σ`-equivariant map `f : C(Y', Y)` covering `fZ : C(Z', Z)` induces a commutative square in `TopCat`
between the descended torus projections over `Z'` and `Z`. -/
theorem torusFamilyAffineQuotientBaseChangeCommSq (hfZ : ∀ y' : Y', fZ (β' y') = β (f y')) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    CommSq
      (TopCat.ofHom ⟨MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineBaseChangeHom P b hb R ρ hequiv hone hmul hbmul σ f hf),
        continuous_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom P R ρ hequiv b hb hone hmul
          hbmul σ f hf⟩)
      (TopCat.ofHom ⟨torusFamilyAffineQuotientLift (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
        (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        β' (fun g' _ ↦ hβ'.map_smul g'),
        continuous_torusFamilyAffineQuotientLift _ _ _ _ _ _ _ _ _ hβ'.continuous⟩)
      (TopCat.ofHom ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
        β (fun g _ ↦ hβ.map_smul g),
        continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
          hβ.continuous⟩)
      (TopCat.ofHom fZ) :=
  ⟨by
    let _ := periodAddAction P
    let _ := periodAddAction (P ∘ f)
    let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    ext q
    induction q using Quotient.ind with | _ x =>
    simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      MulActionHom.orbitRelQuotientMap_mk, torusFamilyAffineBaseChangeHom_apply,
      torusFamilyAffineQuotientLift_mk, torusFamilyProjection_baseChangeMap, hfZ]⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] hinj in
/-- Over any sheet `y'` of `z'`, the descended fiber map of
`torusFamilyAffineQuotientBaseChangeCommSq` intertwines the sheet fiber homeomorphisms at `y'` and
`f y'` with the upstairs fiber map of `torusFamilyBaseChangeCommSq P f`. -/
private theorem baseChangeCommSq_fiberMap_comp_fiberHomeomorph
    (hfZ : ∀ y' : Y', fZ (β' y') = β (f y')) {z' : Z'} (y' : Y') (hy' : β' y' = z') :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    let hy : β (f y') = fZ z' := (hfZ y').symm.trans (congrArg fZ hy')
    let e' := torusFamilyAffineQuotientFiberHomeomorph (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
      (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      (fun l ↦ (hcont l).comp f.continuous)
      (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
      (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
        (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy'
    let e := torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul hbmul
      hcont hR hbc β hβ (f y') hy
    (TopCat.isoOfHomeo e').hom ≫
        (torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
          σ f hf fZ hfZ).fiberMap z' =
      (torusFamilyBaseChangeCommSq P f).fiberMap y' ≫ (TopCat.isoOfHomeo e).hom := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  ext u
  let hy : β (f y') = fZ z' := (hfZ y').symm.trans (congrArg fZ hy')
  let e' := torusFamilyAffineQuotientFiberHomeomorph (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
    (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    (fun l ↦ (hcont l).comp f.continuous)
    (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
    (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
      (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy'
  let sq := torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
    σ f hf fZ hfZ
  let φ := torusFamilyAffineBaseChangeHom P b hb R ρ hequiv hone hmul hbmul σ f hf
  exact (sq.fiberMap_apply_coe z' (e' u)).trans <|
    (congrArg φ.orbitRelQuotientMap
      (torusFamilyAffineQuotientFiberHomeomorph_coe (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
        (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun l ↦ (hcont l).comp f.continuous)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' u)).trans <|
    (MulActionHom.orbitRelQuotientMap_mk φ u.1).trans <|
    (congrArg (Quotient.mk _)
      ((torusFamilyAffineBaseChangeHom_apply P b hb R ρ hequiv hone hmul hbmul σ f hf u.1).trans
        ((torusFamilyBaseChangeCommSq P f).fiberMap_apply_coe y' u).symm)).trans
    (torusFamilyAffineQuotientFiberHomeomorph_coe P R ρ hequiv b hb hone hmul hbmul hcont hR hbc
      β hβ (f y') hy ((torusFamilyBaseChangeCommSq P f).fiberMap y' u)).symm

include hcont hR hbc in
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] hinj in
/-- Equivariant base change of descended torus families induces an isomorphism in `TopCat` on every
fiber. -/
theorem isIso_torusFamilyAffineQuotientBaseChangeCommSq_fiberMap
    (hfZ : ∀ y' : Y', fZ (β' y') = β (f y')) (z' : Z') :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    IsIso ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
      σ f hf fZ hfZ).fiberMap z') := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  obtain ⟨y', hy'⟩ := hβ'.surjective z'
  have hcomp := baseChangeCommSq_fiberMap_comp_fiberHomeomorph P hcont R ρ hequiv b hb hone hmul
    hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy'
  have : IsIso ((torusFamilyBaseChangeCommSq P f).fiberMap y') :=
    isIso_torusFamilyBaseChangeCommSq_fiberMap P f hcont y'
  have heq : (torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ
      β' hβ' σ f hf fZ hfZ).fiberMap z' =
      (TopCat.isoOfHomeo _).inv ≫
        ((torusFamilyBaseChangeCommSq P f).fiberMap y' ≫ (TopCat.isoOfHomeo _).hom) :=
    (Iso.eq_inv_comp _).2 hcomp
  rw [heq]
  infer_instance

omit [TopologicalSpace Z] β hβ fZ in
private theorem baseChangeQuotientHomologyMarking_fiberHomeomorph
    {z' : Z'} (y' : Y') (hy' : β' y' = z') (n : ℕ)
    (d : letI := periodAddAction (P ∘ f)
      ((singularChains ℤ).obj (TopCat.of (torusFamilyProjection (P ∘ f) ⁻¹' {y'}))).homology n) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    torusFamilyAffineQuotientHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' n
        (ContinuousMap.singularHomologyMap ℤ n
          (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph (P ∘ f)
            (fun g' y' ↦ R (σ g') (f y')) (ρ.comp σ)
            (period_baseChange_equivariant R P ρ hequiv σ hf)
            (torusFamilyBaseChangeTranslation P f σ hf b hb)
            (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
            (linearCocycle_baseChange_one R hone σ f)
            (linearCocycle_baseChange_mul R hmul σ hf)
            (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
            (fun l ↦ (hcont l).comp f.continuous)
            (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
            (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
              (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy')) d) =
      torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun w ↦ hinj (f w)) y' n d :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph (P ∘ f)
    (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
    (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
    (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
      (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' n d

/-- **Naturality of sheet homology markings under equivariant base change.** For any sheet `y'` over
`z'` (`β' y' = z'`) and its image sheet `f y'` over `fZ z'`, the induced map on fiber homology
intertwines the `y'`-sheet marking of the pulled-back family with the `(f y')`-sheet marking of the
target family. -/
theorem torusFamilyAffineQuotientHomologyMarking_baseChange
    (hfZ : ∀ y' : Y', fZ (β' y') = β (f y'))
    {z' : Z'} (y' : Y') (hy' : β' y' = z') (hy : β (f y') = fZ z') (n : ℕ)
    (c : letI := periodAddAction (P ∘ f)
      letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      ((singularChains ℤ).obj (TopCat.of
        (torusFamilyAffineQuotientLift (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
          (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          β' (fun g' _ ↦ hβ'.map_smul g') ⁻¹' {z'}))).homology n) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ (f y') hy n
        (ContinuousMap.singularHomologyMap ℤ n
          ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ
            β' hβ' σ f hf fZ hfZ).fiberMap z').hom c) =
      torusFamilyAffineQuotientHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' n c := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  dsimp only
  let e' := torusFamilyAffineQuotientFiberHomeomorph (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
    (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    (fun l ↦ (hcont l).comp f.continuous)
    (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
    (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
      (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy'
  have hsq : ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ
      β' hβ' σ f hf fZ hfZ).fiberMap z').hom.comp (ContinuousMap.ofClass e') =
      (ContinuousMap.ofClass (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul
        hbmul hcont hR hbc β hβ (f y') hy)).comp
        ((torusFamilyBaseChangeCommSq P f).fiberMap y').hom := by
    have hy_eq : (hfZ y').symm.trans (congrArg fZ hy') = hy := Subsingleton.elim _ _
    rw [← hy_eq]
    exact congrArg TopCat.Hom.hom (baseChangeCommSq_fiberMap_comp_fiberHomeomorph P hcont R ρ
      hequiv b hb hone hmul hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy')
  set d := ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass e'.symm) c
  have hc : ContinuousMap.singularHomologyMap ℤ n (ContinuousMap.ofClass e') d = c := by
    rw [← ContinuousMap.singularHomologyMap_comp]
    simp [Homeomorph.toContinuousMap_comp_symm]
  rw [← hc, ← ContinuousMap.singularHomologyMap_comp, hsq, ContinuousMap.singularHomologyMap_comp]
  exact (torusFamilyAffineQuotientHomologyMarking_fiberHomeomorph P hcont hinj R ρ hequiv b hb
      hone hmul hbmul hR hbc β hβ (f y') hy n _).trans
    ((torusFamilyHomologyMarking_baseChange P hcont hinj f y' n d).trans
      (baseChangeQuotientHomologyMarking_fiberHomeomorph P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β' hβ' σ f hf y' hy' n d).symm)

/-- **Degree-one sheet marking naturality under equivariant base change.** -/
theorem torusFamilyAffineQuotientMarking_baseChange
    (hfZ : ∀ y' : Y', fZ (β' y') = β (f y'))
    {z' : Z'} (y' : Y') (hy' : β' y' = z') (hy : β (f y') = fZ z')
    (c : letI := periodAddAction (P ∘ f)
      letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      ((singularChains ℤ).obj (TopCat.of
        (torusFamilyAffineQuotientLift (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
          (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          β' (fun g' _ ↦ hβ'.map_smul g') ⁻¹' {z'}))).homology 1) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
        hR hbc β hβ (f y') hy
        (ContinuousMap.singularHomologyMap ℤ 1
          ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ
            β' hβ' σ f hf fZ hfZ).fiberMap z').hom c) =
      torusFamilyAffineQuotientMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' c := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  exact (oneEquiv_torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul
      hbmul hR hbc β hβ (f y') hy _).symm.trans <|
    (congrArg (exteriorPower.oneEquiv ℤ Λ)
      (torusFamilyAffineQuotientHomologyMarking_baseChange P hcont hinj R ρ hequiv b hb hone hmul
        hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy' hy 1 c)).trans
    (oneEquiv_torusFamilyAffineQuotientHomologyMarking (P ∘ f)
      (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
      (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
      (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
        (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' c)

end FiberAndMarking

section LocalSystemBaseChange

variable {Y Y' Z Z' Λ E Γ Γ' : Type}
  [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z] [TopologicalSpace Z']
  [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  [Group Γ] [Group Γ'] [MulAction Γ Y] [MulAction Γ' Y']
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
  (β' : Y' → Z') (hβ' : IsQuotientCoveringMap β' Γ')
  (σ : Γ' →* Γ) (f : C(Y', Y)) (hf : ∀ (g' : Γ') (y' : Y'), f (g' • y') = σ g' • f y')
  (fZ : C(Z', Z)) (hfZ : ∀ y' : Y', fZ (β' y') = β (f y'))

omit [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z] [TopologicalSpace Z']
  [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  P hcont hinj [MulAction Γ Y] [MulAction Γ' Y'] R hequiv b hb hone hmul hbmul hR hbc
  β hβ β' hβ' f hf fZ hfZ in
private theorem ofHom_exteriorPowerCompEquiv_toLinearMap (n : ℕ) :
    ModuleCat.ofHom
      (Rep.Hom.hom (Rep.mkIso (ρ.exteriorPowerCompEquiv σ n)).hom).toLinearMap = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  simp

private theorem pulledBackHomologyLocalSystem_rhs
    (L' : letI := periodAddAction (P ∘ f)
      letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      LiftingFunction (TopCat.ofHom
        ⟨torusFamilyAffineQuotientLift (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
          (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          β' (fun g' _ ↦ hβ'.map_smul g'),
          continuous_torusFamilyAffineQuotientLift _ _ _ _ _ _ _ _ _ hβ'.continuous⟩).hom)
    (n : ℕ) (x : FundamentalGroupoid Z') (y' : Y') (hy' : β' y' = x.as) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    let hβ'Hom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
    let α : Rep.of (Representation.exteriorPower (ρ.comp σ) n) ⟶
      Rep.res σ (Rep.of (ρ.exteriorPower n)) := (Rep.mkIso (ρ.exteriorPowerCompEquiv σ n)).hom
    let e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹'
      {((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x).as} :=
      ⟨f y', (hfZ y').symm.trans (congrArg fZ hy')⟩
    ((torusFamilyAffineQuotientHomologyLocalSystemIso (P ∘ f)
        (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
        (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' L' n).hom.app x ≫
      (hβ'Hom.associatedLocalSystemMapOver ℤ hβHom (TopCat.ofHom f) hf (TopCat.ofHom fZ)
        (by ext w; exact hfZ w) α).app x) ≫
      (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom =
    (fiberLocalSystemSingularObjIso L' ℤ n x).hom ≫
      (torusFamilyAffineQuotientHomologyMarking (P ∘ f)
        (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
        (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy' n).toModuleIso.hom :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  let hβ'Hom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
  let α : Rep.of (Representation.exteriorPower (ρ.comp σ) n) ⟶
    Rep.res σ (Rep.of (ρ.exteriorPower n)) := (Rep.mkIso (ρ.exteriorPowerCompEquiv σ n)).hom
  let e' : (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') ⁻¹' {x.as} :=
    ⟨y', hy'⟩
  let e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹'
    {((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x).as} :=
    ⟨f y', (hfZ y').symm.trans (congrArg fZ hy')⟩
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (hβ'Hom.associatedLocalSystemMapOver_app_comp_fiberIso_hom ℤ hβHom (TopCat.ofHom f) hf
        (TopCat.ofHom fZ) (by ext w; exact hfZ w) α e' e rfl)).trans
    ((torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc (P ∘ f)
      (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
      (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
      (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
        (continuous_const_smul g') (hbc (σ g'))) β' hβ' L' n e' _).trans
      (congrArg (_ ≫ ·)
        ((congrArg (_ ≫ ·) (ofHom_exteriorPowerCompEquiv_toLinearMap ρ σ n)).trans
          (Category.comp_id _))))

/-- **Global local-system base-change naturality in degree `n`.** Under an equivariant map of
quotient coverings `f : C(Y', Y)` over `fZ : C(Z', Z)`, `CommSq.fiberLocalSystemMap` intertwines
`TauCeti.torusFamilyAffineQuotientHomologyLocalSystemIso` with
`IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso`. -/
theorem torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_iso
    (L : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
      LiftingFunction (TopCat.ofHom
        ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
          β (fun g _ ↦ hβ.map_smul g),
          continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
            hβ.continuous⟩).hom)
    (L' : letI := periodAddAction (P ∘ f)
      letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      LiftingFunction (TopCat.ofHom
        ⟨torusFamilyAffineQuotientLift (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
          (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          β' (fun g' _ ↦ hβ'.map_smul g'),
          continuous_torusFamilyAffineQuotientLift _ _ _ _ _ _ _ _ _ hβ'.continuous⟩).hom)
    (n : ℕ) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    let hβ'Hom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
    (torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
        σ f hf fZ hfZ).fiberLocalSystemMap L' L ℤ n ≫
      (pullback (TopCat.ofHom fZ).hom).map
        (torusFamilyAffineQuotientHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone hmul
          hbmul hR hbc β hβ L n).hom =
      (torusFamilyAffineQuotientHomologyLocalSystemIso (P ∘ f)
          (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w))
          (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ)
          (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
          (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
            (continuous_const_smul g') (hbc (σ g'))) β' hβ' L' n).hom ≫
        hβ'Hom.associatedLocalSystemMap ℤ (Rep.mkIso (ρ.exteriorPowerCompEquiv σ n)).hom ≫
        (hβ'Hom.associatedLocalSystemBaseChangeIso ℤ hβHom (TopCat.ofHom f) hf (TopCat.ofHom fZ)
          (by ext y'; exact hfZ y') (Rep.of (ρ.exteriorPower n))).hom := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  let hβ'Hom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
  let α : Rep.of (Representation.exteriorPower (ρ.comp σ) n) ⟶
      Rep.res σ (Rep.of (ρ.exteriorPower n)) :=
    (Rep.mkIso (ρ.exteriorPowerCompEquiv σ n)).hom
  dsimp only
  rw [← hβ'Hom.associatedLocalSystemMapOver_eq ℤ hβHom (TopCat.ofHom f) hf (TopCat.ofHom fZ)
    (by ext y'; exact hfZ y') α]
  refine NatTrans.ext <| funext fun x ↦ ?_
  obtain ⟨y', hy'⟩ := hβ'.surjective x.as
  let e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹'
      {((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x).as} :=
    ⟨f y', (hfZ y').symm.trans (congrArg fZ hy')⟩
  apply (cancel_mono (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of (ρ.exteriorPower n)) e).hom).1
  refine ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·)
      (torusFamilyAffineQuotientHomologyLocalSystemIso_hom_app_comp_fiberIso_hom P hcont hinj R ρ
        hequiv b hb hone hmul hbmul hR hbc β hβ L n e))).trans
    (Eq.trans ?_
      (pulledBackHomologyLocalSystem_rhs P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ β' hβ' σ f hf fZ hfZ L' n x y' hy').symm)
  apply ModuleCat.hom_ext
  ext1 v
  dsimp only [LinearEquiv.toModuleIso_hom]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact ((congrArg
    (torusFamilyAffineQuotientHomologyMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ e.1 e.2 n)
    ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
      σ f hf fZ hfZ).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app L' L ℤ n
        x v)).trans
    (torusFamilyAffineQuotientHomologyMarking_baseChange P hcont hinj R ρ hequiv b hb hone hmul
      hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy' e.2 n _))

omit [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z] [TopologicalSpace Z']
  [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  P hcont hinj [MulAction Γ Y] [MulAction Γ' Y'] R hequiv b hb hone hmul hbmul hR hbc
  β hβ β' hβ' f hf fZ hfZ in
private theorem ofHom_id_res_toLinearMap :
    ModuleCat.ofHom (Rep.Hom.hom (𝟙 (Rep.res σ (Rep.of ρ)))).toLinearMap = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  simp

private theorem pulledBackFirstHomologyLocalSystem_rhs
    (L' : letI := periodAddAction (P ∘ f)
      letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      LiftingFunction (TopCat.ofHom
        ⟨torusFamilyAffineQuotientLift (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
          (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          β' (fun g' _ ↦ hβ'.map_smul g'),
          continuous_torusFamilyAffineQuotientLift _ _ _ _ _ _ _ _ _ hβ'.continuous⟩).hom)
    (x : FundamentalGroupoid Z') (y' : Y') (hy' : β' y' = x.as) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    let hβ'Hom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
    let e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹'
      {((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x).as} :=
      ⟨f y', (hfZ y').symm.trans (congrArg fZ hy')⟩
    ((torusFamilyAffineQuotientFirstHomologyLocalSystemIso (P ∘ f)
        (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
        (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' L').hom.app x ≫
      (hβ'Hom.associatedLocalSystemMapOver ℤ hβHom (TopCat.ofHom f) hf (TopCat.ofHom fZ)
        (by ext w; exact hfZ w) (𝟙 (Rep.res σ (Rep.of ρ)))).app x) ≫
      (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of ρ) e).hom =
    (fiberLocalSystemSingularObjIso L' ℤ 1 x).hom ≫
      (torusFamilyAffineQuotientMarking (P ∘ f)
        (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
        (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
        (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
        (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
          (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy').toModuleIso.hom :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  let hβ'Hom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
  let e' : (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') ⁻¹' {x.as} :=
    ⟨y', hy'⟩
  let e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹'
    {((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x).as} :=
    ⟨f y', (hfZ y').symm.trans (congrArg fZ hy')⟩
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (hβ'Hom.associatedLocalSystemMapOver_app_comp_fiberIso_hom ℤ hβHom (TopCat.ofHom f) hf
        (TopCat.ofHom fZ) (by ext w; exact hfZ w) (𝟙 (Rep.res σ (Rep.of ρ))) e' e rfl)).trans
    ((torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom_assoc (P ∘ f)
      (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w)) (fun g' w ↦ R (σ g') (f w))
      (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
      (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
        (continuous_const_smul g') (hbc (σ g'))) β' hβ' L' e' _).trans
      (congrArg (_ ≫ ·)
        ((congrArg (_ ≫ ·) (ofHom_id_res_toLinearMap ρ σ)).trans (Category.comp_id _))))

/-- **Global local-system base-change naturality in degree one.** -/
theorem torusFamilyAffineQuotientBaseChange_fiberLocalSystemMap_comp_firstHomologyIso
    (L : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
      LiftingFunction (TopCat.ofHom
        ⟨torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
          β (fun g _ ↦ hβ.map_smul g),
          continuous_torusFamilyAffineQuotientLift P R ρ hequiv b hb hone hmul hbmul
            hβ.continuous⟩).hom)
    (L' : letI := periodAddAction (P ∘ f)
      letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
        (linearCocycle_baseChange_one R hone σ f)
        (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
        (period_baseChange_equivariant R P ρ hequiv σ hf)
        (torusFamilyBaseChangeTranslation P f σ hf b hb)
        (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
        (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
      LiftingFunction (TopCat.ofHom
        ⟨torusFamilyAffineQuotientLift (P ∘ f) (fun g' y' ↦ R (σ g') (f y'))
          (ρ.comp σ) (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          β' (fun g' _ ↦ hβ'.map_smul g'),
          continuous_torusFamilyAffineQuotientLift _ _ _ _ _ _ _ _ _ hβ'.continuous⟩).hom) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
      (linearCocycle_baseChange_one R hone σ f)
      (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
      (period_baseChange_equivariant R P ρ hequiv σ hf)
      (torusFamilyBaseChangeTranslation P f σ hf b hb)
      (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
      (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    have := hβ'.toContinuousConstSMul
    let hβHom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
    let hβ'Hom : IsQuotientCoveringMap
      (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
    (torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
        σ f hf fZ hfZ).fiberLocalSystemMap L' L ℤ 1 ≫
      (pullback (TopCat.ofHom fZ).hom).map
        (torusFamilyAffineQuotientFirstHomologyLocalSystemIso P hcont hinj R ρ hequiv b hb hone
          hmul hbmul hR hbc β hβ L).hom =
      (torusFamilyAffineQuotientFirstHomologyLocalSystemIso (P ∘ f)
          (fun l ↦ (hcont l).comp f.continuous) (fun w ↦ hinj (f w))
          (fun g' w ↦ R (σ g') (f w)) (ρ.comp σ)
          (period_baseChange_equivariant R P ρ hequiv σ hf)
          (torusFamilyBaseChangeTranslation P f σ hf b hb)
          (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
          (linearCocycle_baseChange_one R hone σ f)
          (linearCocycle_baseChange_mul R hmul σ hf)
          (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
          (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
          (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
            (continuous_const_smul g') (hbc (σ g'))) β' hβ' L').hom ≫
        (hβ'Hom.associatedLocalSystemBaseChangeIso ℤ hβHom (TopCat.ofHom f) hf (TopCat.ofHom fZ)
          (by ext y'; exact hfZ y') (Rep.of ρ)).hom := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineMulAction (fun g' y' ↦ R (σ g') (f y'))
    (linearCocycle_baseChange_one R hone σ f)
    (linearCocycle_baseChange_mul R hmul σ hf) (P ∘ f) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
  have := hβ'.toContinuousConstSMul
  let hβHom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) Γ := hβ
  let hβ'Hom : IsQuotientCoveringMap
    (TopCat.ofHom ⟨β', hβ'.continuous⟩ : TopCat.of Y' ⟶ TopCat.of Z') Γ' := hβ'
  dsimp only
  rw [hβ'Hom.associatedLocalSystemBaseChangeIso_hom]
  refine NatTrans.ext <| funext fun x ↦ ?_
  obtain ⟨y', hy'⟩ := hβ'.surjective x.as
  let e : (TopCat.ofHom ⟨β, hβ.continuous⟩ : TopCat.of Y ⟶ TopCat.of Z) ⁻¹'
      {((FundamentalGroupoid.map (TopCat.ofHom fZ).hom).obj x).as} :=
    ⟨f y', (hfZ y').symm.trans (congrArg fZ hy')⟩
  apply (cancel_mono (hβHom.associatedLocalSystemFiberIso ℤ (Rep.of ρ) e).hom).1
  refine ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·)
      (torusFamilyAffineQuotientFirstHomologyLocalSystemIso_hom_app_comp_fiberIso_hom P hcont hinj
        R ρ hequiv b hb hone hmul hbmul hR hbc β hβ L e))).trans
    (Eq.trans ?_
      (pulledBackFirstHomologyLocalSystem_rhs P hcont hinj R ρ hequiv b hb hone hmul hbmul hR hbc
        β hβ β' hβ' σ f hf fZ hfZ L' x y' hy').symm)
  apply ModuleCat.hom_ext
  ext1 v
  dsimp only [LinearEquiv.toModuleIso_hom]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact ((congrArg
    (torusFamilyAffineQuotientMarking P hcont hinj R ρ hequiv b hb hone hmul hbmul
      hR hbc β hβ e.1 e.2)
    ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
      σ f hf fZ hfZ).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app L' L ℤ 1
        x v)).trans
    (torusFamilyAffineQuotientMarking_baseChange P hcont hinj R ρ hequiv b hb hone hmul
      hbmul hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy' e.2 _))

end LocalSystemBaseChange

end TauCeti
