/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.AffineAction
public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.Fiber
public import TauCeti.Algebra.Module.ZLattice.Family.QuotientPullback

/-!
# Categorical base-change square and fiber isomorphism of descended torus families

For `P : Y → Λ →ₗ[ℤ] E` with an affine `Γ`-action over `β : Y → Z`, `σ : Γ' →* Γ`, `σ`-equivariant
`f : Y' → Y`, and quotient covering `β' : Y' → Z'`, `P ∘ f` descends to
`TauCeti.torusFamilyBaseChangeQuotientMap` (`((Y' × E)/Λ)/Γ' → Z'`) with sheet fiber homeomorphisms
`TauCeti.torusFamilyBaseChangeQuotientFiberHomeomorph` over arbitrary universes. Over `Type u`,
`f : C(Y', Y)` covering `fZ : C(Z', Z)` yields `TauCeti.torusFamilyAffineQuotientBaseChangeCommSq`
in `TopCat` (without `[ContinuousAdd E]`), whose `CommSq.fiberMap` intertwines sheet fiber
homeomorphisms (`TauCeti.torusFamilyAffineQuotientBaseChangeCommSq_fiberMap_comp_fiberHomeomorph`)
and is an isomorphism (`TauCeti.isIso_torusFamilyAffineQuotientBaseChangeCommSq_fiberMap`).

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, Chapter 8.
-/

public section

open CategoryTheory Function

universe u

namespace TauCeti

section Topology

variable {Y Y' Z' E Λ Γ Γ' : Type*} [TopologicalSpace Y'] [TopologicalSpace Z'] [AddCommGroup Λ]
  [AddCommGroup E] [Group Γ] [Group Γ'] [MulAction Γ Y] [MulAction Γ' Y'] (P : Y → Λ →ₗ[ℤ] E)
  [TopologicalSpace Y] [TopologicalSpace E] [ContinuousAdd E]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β' : Y' → Z') (hβ' : IsQuotientCoveringMap β' Γ') (σ : Γ' →* Γ)

omit [TopologicalSpace Y] [TopologicalSpace E] [ContinuousAdd E] hcont hR hbc in
/-- Descended projection `((Y' × E)/Λ)/Γ' → Z'` of `P ∘ f` along `β' : Y' → Z'`. -/
abbrev torusFamilyBaseChangeQuotientMap (f : Y' → Y) (hf : ∀ g' y', f (g' • y') = σ g' • f y') :
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    MulAction.orbitRel.Quotient Γ' (AddAction.orbitRel.Quotient Λ (Y' × E)) → Z' :=
  torusFamilyAffineQuotientMap (P ∘ f) (fun g' y' ↦ R (σ g') (f y')) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul) β' hβ'

/-- Sheetwise fiber homeomorphism between the `y'`-fiber of `P ∘ f` and the `z'`-fiber of
`torusFamilyBaseChangeQuotientMap` over `β' y' = z'`. -/
noncomputable abbrev torusFamilyBaseChangeQuotientFiberHomeomorph (f : C(Y', Y))
    (hf : ∀ g' y', f (g' • y') = σ g' • f y') {z' : Z'} (y' : Y') (hy' : β' y' = z' := by rfl) :
    letI := periodAddAction (P ∘ f); torusFamilyProjection (P ∘ f) ⁻¹' {y'} ≃ₜ
      torusFamilyBaseChangeQuotientMap P R ρ hequiv b hb hone hmul hbmul β' hβ' σ f hf ⁻¹' {z'} :=
  haveI := hβ'.toContinuousConstSMul
  torusFamilyAffineQuotientFiberHomeomorph (P ∘ f) (fun g' y' ↦ R (σ g') (f y')) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul)
    (fun l ↦ (hcont l).comp f.continuous)
    (fun g' ↦ (hR (σ g')).comp (f.continuous.prodMap continuous_id))
    (fun g' ↦ continuous_torusFamilyBaseChangeTranslation P hcont f.continuous σ hf b hb
      (continuous_const_smul g') (hbc (σ g'))) β' hβ' y' hy'

/-- `torusFamilyBaseChangeQuotientFiberHomeomorph` sends a point in the `y'`-fiber to its
`Γ'`-orbit.

This is intentionally not a simp lemma: `torusFamilyBaseChangeQuotientFiberHomeomorph` is an
`abbrev`, so `simp` already simplifies it via `torusFamilyAffineQuotientFiberHomeomorph_coe`. -/
theorem torusFamilyBaseChangeQuotientFiberHomeomorph_coe (f : C(Y', Y))
    (hf : ∀ g' y', f (g' • y') = σ g' • f y') {z' : Z'} (y' : Y') (hy' : β' y' = z')
    (u : letI := periodAddAction (P ∘ f); torusFamilyProjection (P ∘ f) ⁻¹' {y'}) :
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    (torusFamilyBaseChangeQuotientFiberHomeomorph P hcont R ρ hequiv b hb hone hmul hbmul hR hbc
        β' hβ' σ f hf y' hy' u :
      MulAction.orbitRel.Quotient Γ' (AddAction.orbitRel.Quotient Λ (Y' × E))) =
      Quotient.mk _ u.val := by
  let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
  simp only [torusFamilyAffineQuotientFiberHomeomorph_coe]

end Topology

section CommSq

variable {Y Y' Z Z' E : Type u} {Λ Γ Γ' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z'] [AddCommGroup Λ] [AddCommGroup E] [TopologicalSpace E]
  [ContinuousAdd E] (P : Y → Λ →ₗ[ℤ] E) [Group Γ] [Group Γ'] [MulAction Γ Y] [MulAction Γ' Y']
  (R : Γ → Y → E →+ E) (ρ : Representation ℤ Γ Λ)
  (hequiv : ∀ g y l, P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ g y, torusFamilyProjection P (b g y) = g • y) (hone : ∀ y v, R 1 y v = v)
  (hmul : ∀ g h y v, R (g * h) y v = R g (h • y) (R h y v))
  (hbmul : ∀ g h y, b (g * h) y = torusFamilyAffineMap R P ρ hequiv b hb g (b h y))
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hR : ∀ g, Continuous fun a : Y × E ↦ R g a.1 a.2)
  (hbc : letI := periodAddAction P; ∀ g, Continuous (b g))
  (β : Y → Z) (hβ : IsQuotientCoveringMap β Γ) (β' : Y' → Z') (hβ' : IsQuotientCoveringMap β' Γ')
  (σ : Γ' →* Γ)

omit [TopologicalSpace Z] [ContinuousAdd E] hcont hR hbc β hβ in
/-- The descended projection `((Y' × E)/Λ)/Γ' ⟶ Z'` of `P ∘ f` as a morphism in `TopCat`. -/
abbrev torusFamilyBaseChangeQuotientTopHom (f : Y' → Y)
    (hf : ∀ (g' : Γ') (y' : Y'), f (g' • y') = σ g' • f y') :
    letI := periodAddAction (P ∘ f)
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    TopCat.of (MulAction.orbitRel.Quotient Γ' (AddAction.orbitRel.Quotient Λ (Y' × E))) ⟶
      TopCat.of Z' :=
  torusFamilyAffineQuotientTopHom (P ∘ f) (fun g' y' ↦ R (σ g') (f y')) (ρ.comp σ)
    (period_baseChange_equivariant R P ρ hequiv σ hf)
    (torusFamilyBaseChangeTranslation P f σ hf b hb)
    (torusFamilyProjection_baseChangeTranslation P f σ hf b hb)
    (linearCocycle_baseChange_one R hone σ f) (linearCocycle_baseChange_mul R hmul σ hf)
    (torusFamilyBaseChangeTranslation_mul P b hb R ρ hequiv σ hf hbmul) β' hβ'

omit [ContinuousAdd E] hcont hR hbc in
/-- **Commutative square of descended torus families under equivariant base change.** -/
theorem torusFamilyAffineQuotientBaseChangeCommSq (f : C(Y', Y))
    (hf : ∀ (g' : Γ') (y' : Y'), f (g' • y') = σ g' • f y') (fZ : C(Z', Z))
    (hfZ : ∀ y' : Y', fZ (β' y') = β (f y')) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    CommSq (TopCat.ofHom ⟨MulActionHom.orbitRelQuotientMap
        (torusFamilyAffineBaseChangeHom P b hb R ρ hequiv hone hmul hbmul σ f hf),
        continuous_orbitRelQuotientMap_torusFamilyAffineBaseChangeHom R hone hmul P ρ hequiv b hb
          hbmul σ hf f.continuous⟩)
      (torusFamilyBaseChangeQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β' hβ' σ f hf)
      (torusFamilyAffineQuotientTopHom P R ρ hequiv b hb hone hmul hbmul β hβ) (TopCat.ofHom fZ) :=
  ⟨by let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
      let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
      let _ := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
      ext q; induction q using Quotient.ind with | _ x =>
      simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        MulActionHom.orbitRelQuotientMap_mk, torusFamilyAffineBaseChangeHom_apply,
        torusFamilyAffineQuotientLift_mk, torusFamilyProjection_baseChangeMap, hfZ]⟩

/-- `CommSq.fiberMap` of `torusFamilyAffineQuotientBaseChangeCommSq` intertwines the sheet fiber
homeomorphisms at `y'` and `f y'` with `torusFamilyBaseChangeCommSq`. -/
theorem torusFamilyAffineQuotientBaseChangeCommSq_fiberMap_comp_fiberHomeomorph (f : C(Y', Y))
    (hf : ∀ (g' : Γ') (y' : Y'), f (g' • y') = σ g' • f y') (fZ : C(Z', Z))
    (hfZ : ∀ y' : Y', fZ (β' y') = β (f y')) {z' : Z'} (y' : Y') (hy' : β' y' = z')
    (hy : β (f y') = fZ z' := (hfZ y').symm.trans (congrArg fZ hy')) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    (TopCat.isoOfHomeo (torusFamilyBaseChangeQuotientFiberHomeomorph P hcont R ρ hequiv b hb hone
        hmul hbmul hR hbc β' hβ' σ f hf y' hy')).hom ≫
      (torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β' hβ'
        σ f hf fZ hfZ).fiberMap z' = (torusFamilyBaseChangeCommSq P f).fiberMap y' ≫
      (TopCat.isoOfHomeo (torusFamilyAffineQuotientFiberHomeomorph P R ρ hequiv b hb hone hmul
        hbmul hcont hR hbc β hβ (f y') hy)).hom := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
  refine TopCat.ext fun u ↦ Subtype.ext ?_
  rw [TopCat.comp_app, TopCat.comp_app, CommSq.fiberMap_apply_coe]
  simp only [TopCat.isoOfHomeo_hom, ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk]
  rw [torusFamilyBaseChangeQuotientFiberHomeomorph_coe,
    torusFamilyAffineQuotientFiberHomeomorph_coe, MulActionHom.orbitRelQuotientMap_mk,
    torusFamilyAffineBaseChangeHom_apply, CommSq.fiberMap_apply_coe]
  rfl

include hcont hR hbc in
/-- Equivariant base change of descended torus families induces an isomorphism on every fiber. -/
theorem isIso_torusFamilyAffineQuotientBaseChangeCommSq_fiberMap (f : C(Y', Y))
    (hf : ∀ (g' : Γ') (y' : Y'), f (g' • y') = σ g' • f y') (fZ : C(Z', Z))
    (hfZ : ∀ y' : Y', fZ (β' y') = β (f y')) (z' : Z') :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
    IsIso ((torusFamilyAffineQuotientBaseChangeCommSq P R ρ hequiv b hb hone hmul hbmul β hβ β'
      hβ' σ f hf fZ hfZ).fiberMap z') := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyBaseChangeAffineMulAction P b hb R ρ hequiv hone hmul hbmul σ f hf
  obtain ⟨y', hy'⟩ := hβ'.surjective z'
  have := isIso_torusFamilyBaseChangeCommSq_fiberMap P f hcont y'
  rw [(Iso.eq_inv_comp _).2 (torusFamilyAffineQuotientBaseChangeCommSq_fiberMap_comp_fiberHomeomorph
    P R ρ hequiv b hb hone hmul hbmul hcont hR hbc β hβ β' hβ' σ f hf fZ hfZ y' hy')]
  infer_instance

end CommSq

end TauCeti
