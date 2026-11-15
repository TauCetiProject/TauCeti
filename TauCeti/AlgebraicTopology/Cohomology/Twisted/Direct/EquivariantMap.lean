/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.GroupCohomology
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.Pullback
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Pullback
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.EquivariantMap
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups

/-!
# Change of groups in direct local-coefficient cohomology of quotient covers

Let `p : E ⟶ B` and `q : F ⟶ C` be quotient covering maps of actions of groups `G` and `H`, let
`f : E ⟶ F` be an equivariant map along an arbitrary group homomorphism `φ : G →* H` lying over
`b : B ⟶ C`, and let `ξ : Rep.res φ D ⟶ A` be a compatible morphism of `k`-linear representations.

Pulling direct cochains of `C` valued in `L_D = hH.associatedLocalSystem k D` back along `b`,
identifying `b^* L_D` with `L_{Res(φ)(D)}` via
`IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso`, and changing coefficients along `ξ`
defines contravariant change-of-groups maps on direct cochains
(`IsQuotientCoveringMap.associatedCochainComplexMap`) and on direct local-coefficient cohomology
(`IsQuotientCoveringMap.associatedCohomologyMap`).

In sheet coordinates at `e` over the initial vertex of `σ` and `e'` over the initial vertex of
`b ∘ σ` with `f e = e'`, `associatedCochainComplexMap` evaluates a cochain on `b ∘ σ` in sheet `e'`
and applies `ξ`
(`IsQuotientCoveringMap.associatedLocalSystemFiberIso_hom_eval_associatedCochainComplexMap_f`).
Under `IsQuotientCoveringMap.cochainComplexIsoLinearYonedaObj`, this agrees with the algebraic
change-of-groups map `φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf)` on equivariant
cochains of the total spaces
(`IsQuotientCoveringMap.associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom`).

When `E` and `F` are contractible, `IsQuotientCoveringMap.cohomologyIsoGroupCohomology` therefore
carries `associatedCohomologyMap` to Mathlib's `groupCohomology.map φ ξ n`
(`IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_naturality_over`), with no hypothesis on
`φ` and no projectivity or flatness assumption on the representations.

## Main definitions

* `IsQuotientCoveringMap.associatedCochainComplexMap`,
  `IsQuotientCoveringMap.associatedCohomologyMap`: the contravariant change-of-groups maps on direct
  cochains and cohomology along an equivariant map of quotient covers and a compatible coefficient
  morphism `ξ : Rep.res φ D ⟶ A`.

## Main results

* `IsQuotientCoveringMap.cochainComplexEval_associatedCochainComplexMap_f`,
  `IsQuotientCoveringMap.associatedLocalSystemFiberIso_hom_eval_associatedCochainComplexMap_f`:
  simplex and sheet-coordinate evaluation of `associatedCochainComplexMap`.
* `IsQuotientCoveringMap.associatedCochainComplexMap_id_hom`,
  `IsQuotientCoveringMap.associatedCochainComplexMap_id`,
  `IsQuotientCoveringMap.associatedCochainComplexMap_comp`,
  `IsQuotientCoveringMap.associatedCohomologyMap_id_hom`,
  `IsQuotientCoveringMap.associatedCohomologyMap_id`,
  `IsQuotientCoveringMap.associatedCohomologyMap_comp`: identity and contravariant composition laws
  for `associatedCochainComplexMap` and `associatedCohomologyMap`.
* `IsQuotientCoveringMap.associatedCohomologyMap_naturality`,
  `IsQuotientCoveringMap.cohomologyδ_comp_associatedCohomologyMap`: coefficient naturality and
  connecting-map compatibility for change of groups on quotient covers.
* `IsQuotientCoveringMap.associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom`,
  `IsQuotientCoveringMap.linearYonedaObjMap_comp_cochainComplexIsoLinearYonedaObj_inv`,
  `IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_naturality_over`,
  `IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_pullback`,
  `IsQuotientCoveringMap.cohomologyIsoGroupCohomology_inv_pullback`: naturality of the direct
  cochain and cohomology identifications with respect to equivariant maps of quotient covers.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4, III.1, and III.8.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Simplicial TauCeti TauCeti.TopCat TauCeti.LocalCoefficientSystem

universe u

namespace IsQuotientCoveringMap

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k]

/-- Sheet coordinates on equal base simplices depend only on the simplex and underlying point in
the total space. -/
private lemma fiberIso_hom_eval_congr (A : Rep.{u} k G) {n : ℕ}
    {σ₁ σ₀ : (_root_.TopCat.toSSet.obj B) _⦋n⦌} (hσ : σ₁ = σ₀)
    (e₁ : p ⁻¹' {(initialVertex σ₁).as}) (e₀ : p ⁻¹' {(initialVertex σ₀).as})
    (he : (e₁ : E) = (e₀ : E))
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n) :
    (hG.associatedLocalSystemFiberIso k A e₁).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n σ₁ c) =
      (hG.associatedLocalSystemFiberIso k A e₀).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n σ₀ c) := by
  subst hσ
  obtain rfl : e₁ = e₀ := Subtype.ext he
  rfl

variable {F C : _root_.TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)

/-- The contravariant cochain map `C•(C; L_D) ⟶ C•(B; L_A)` induced by an equivariant map of
quotient covers along `φ : G →* H` over `b : B ⟶ C` and a compatible coefficient morphism
`ξ : Rep.res φ D ⟶ A`: pull cochains back along `b`, identify `b^* L_D` with `L_{Res(φ)(D)}`, and
apply `ξ`. -/
def associatedCochainComplexMap {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) :
    (hH.associatedLocalSystem k D).cochainComplex ⟶
      (hG.associatedLocalSystem k A).cochainComplex :=
  cochainComplexPullback b (hH.associatedLocalSystem k D) ≫
    cochainComplexCoefficientMap
      ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
        hG.associatedLocalSystemMap k ξ)

/-- `associatedCochainComplexMap` is cochain pullback followed by the base-change and coefficient
morphisms of local systems. -/
theorem associatedCochainComplexMap_def {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) :
    hG.associatedCochainComplexMap k hH f hf b hb ξ =
      cochainComplexPullback b (hH.associatedLocalSystem k D) ≫
        cochainComplexCoefficientMap
          ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
            hG.associatedLocalSystemMap k ξ) :=
  (rfl)

/-- Evaluating `associatedCochainComplexMap` on a simplex `σ` of `B` pulls `c` back along `b`,
applies `(associatedLocalSystemBaseChangeIso D).inv`, and applies `associatedLocalSystemMap ξ`
at the initial vertex of `σ`. -/
@[simp]
theorem cochainComplexEval_associatedCochainComplexMap_f
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ)
    (c : (hH.associatedLocalSystem k D).cochainComplex.X n)
    (σ : (_root_.TopCat.toSSet.obj B) _⦋n⦌) :
    cochainComplexEval (hG.associatedLocalSystem k A) n σ
        ((hG.associatedCochainComplexMap k hH f hf b hb ξ).f n c) =
      ((hG.associatedLocalSystemMap k ξ).app (initialVertex σ))
        (((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv.app (initialVertex σ))
          (cochainComplexEval (hH.associatedLocalSystem k D) n
            ((_root_.TopCat.toSSet.map b).app _ σ) c)) := by
  rw [associatedCochainComplexMap_def, cochainComplexCoefficientMap_comp, ← Category.assoc,
    HomologicalComplex.comp_f, ModuleCat.comp_apply, cochainComplexCoefficientMap_eval.{u, u, u},
    HomologicalComplex.comp_f, ModuleCat.comp_apply, cochainComplexCoefficientMap_eval.{u, u, u},
    cochainComplexPullback_eval.{u, u, u}]

/-- In sheet coordinates at `e` over the initial vertex of `σ` and `e'` over the initial vertex of
`b ∘ σ` with `f e = e'`, `associatedCochainComplexMap` evaluates `c` on `b ∘ σ` in sheet `e'` and
applies `ξ`. -/
theorem associatedLocalSystemFiberIso_hom_eval_associatedCochainComplexMap_f
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ)
    (c : (hH.associatedLocalSystem k D).cochainComplex.X n)
    (σ : (_root_.TopCat.toSSet.obj B) _⦋n⦌)
    (e : p ⁻¹' {(initialVertex σ).as})
    (e' : q ⁻¹' {(initialVertex ((_root_.TopCat.toSSet.map b).app _ σ)).as})
    (he : f e = e') :
    (hG.associatedLocalSystemFiberIso k A e).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n σ
          ((hG.associatedCochainComplexMap k hH f hf b hb ξ).f n c)) =
      ξ.hom ((hH.associatedLocalSystemFiberIso k D e').hom
        (cochainComplexEval (hH.associatedLocalSystem k D) n
          ((_root_.TopCat.toSSet.map b).app _ σ) c)) := by
  -- The pulled-back fibre over `initialVertex σ` and the fibre over `initialVertex (b ∘ σ)` agree
  -- by definition of `pullback`, so the sheet-coordinate identity is instantiated on `e''` and `v`.
  let e'' : q ⁻¹' {((FundamentalGroupoid.map b.hom).obj (initialVertex σ)).as} := e'
  let v : ((LocalCoefficientSystem.pullback b.hom).obj (hH.associatedLocalSystem k D)).obj
      (initialVertex σ) :=
    cochainComplexEval (hH.associatedLocalSystem k D) n
      ((_root_.TopCat.toSSet.map b).app _ σ) c
  have hcoord := ConcreteCategory.congr_hom
    (hG.associatedLocalSystemBaseChangeIso_inv_app_comp_map_app_comp_fiberIso_hom k hH f hf b hb ξ
      e e'' he) v
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hcoord
  rw [cochainComplexEval_associatedCochainComplexMap_f]
  exact hcoord.trans
    ((ModuleCat.comp_apply (hH.associatedLocalSystemFiberIso k D e').hom
        (ModuleCat.ofHom ξ.hom.toLinearMap) _).trans
      (ModuleCat.ofHom_apply ξ.hom.toLinearMap _))

/-- Evaluating `associatedCochainComplexMap` on the projection `p ∘ τ` of a simplex `τ` of `E` in
`initialSheet τ` reads the coordinate of `c` on `q ∘ f ∘ τ` in `initialSheet (f ∘ τ)` and applies
`ξ`. -/
private lemma fiberIso_hom_eval_associatedCochainComplexMap_map_p
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ)
    (c : (hH.associatedLocalSystem k D).cochainComplex.X n)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) :
    (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n
          ((_root_.TopCat.toSSet.map p).app _ τ)
          ((hG.associatedCochainComplexMap k hH f hf b hb ξ).f n c)) =
      ξ.hom ((hH.associatedLocalSystemFiberIso k D
          (initialSheet ((_root_.TopCat.toSSet.map f).app _ τ))).hom
        (cochainComplexEval (hH.associatedLocalSystem k D) n
          ((_root_.TopCat.toSSet.map q).app _
            ((_root_.TopCat.toSSet.map f).app _ τ)) c)) := by
  let σB := (_root_.TopCat.toSSet.map p).app (Opposite.op ⦋n⦌) τ
  let τF := (_root_.TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ
  have hσC : (_root_.TopCat.toSSet.map b).app (Opposite.op ⦋n⦌) σB =
      (_root_.TopCat.toSSet.map q).app (Opposite.op ⦋n⦌) τF := by
    simpa only [σB, τF, Functor.map_comp, NatTrans.comp_app, types_comp_apply] using
      congrArg (fun m : E ⟶ C ↦ (_root_.TopCat.toSSet.map m).app (Opposite.op ⦋n⦌) τ) hb
  let e' : q ⁻¹' {(initialVertex ((_root_.TopCat.toSSet.map b).app _ σB)).as} :=
    (CommSq.mk hb.symm).fiberMap (initialVertex σB).as (initialSheet τ)
  have hcongr :
      (hH.associatedLocalSystemFiberIso k D e').hom
          (cochainComplexEval (hH.associatedLocalSystem k D) n
            ((_root_.TopCat.toSSet.map b).app _ σB) c) =
        (hH.associatedLocalSystemFiberIso k D (initialSheet τF)).hom
          (cochainComplexEval (hH.associatedLocalSystem k D) n
            ((_root_.TopCat.toSSet.map q).app _ τF) c) :=
    fiberIso_hom_eval_congr hH k D hσC e' (initialSheet τF)
      ((CommSq.fiberMap_apply_coe (CommSq.mk hb.symm) (initialVertex σB).as (initialSheet τ)).trans
        (by simp [τF, simplexMap_app])) c
  exact (hG.associatedLocalSystemFiberIso_hom_eval_associatedCochainComplexMap_f k hH f hf b hb ξ
    n c σB (initialSheet τ) e'
    (CommSq.fiberMap_apply_coe (CommSq.mk hb.symm) (initialVertex σB).as (initialSheet τ)).symm
    ).trans (congrArg ξ.hom hcongr)

/-- `associatedCochainComplexMap` is natural with respect to compatible morphisms of coefficient
representations: if `ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂`, then the induced cochain maps form a
commutative square. -/
@[reassoc]
theorem associatedCochainComplexMap_naturality
    {D₁ D₂ : Rep.{u} k H} {A₁ A₂ : Rep.{u} k G}
    (β : D₁ ⟶ D₂) (α : A₁ ⟶ A₂)
    (ξ₁ : Rep.res φ D₁ ⟶ A₁) (ξ₂ : Rep.res φ D₂ ⟶ A₂)
    (hcomm : ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂) :
    cochainComplexCoefficientMap (hH.associatedLocalSystemMap k β) ≫
        hG.associatedCochainComplexMap k hH f hf b hb ξ₂ =
      hG.associatedCochainComplexMap k hH f hf b hb ξ₁ ≫
        cochainComplexCoefficientMap (hG.associatedLocalSystemMap k α) := by
  rw [associatedCochainComplexMap_def, associatedCochainComplexMap_def,
    cochainComplexPullback_coefficient_naturality_assoc]
  simp only [Category.assoc]
  congr 1
  rw [← cochainComplexCoefficientMap_comp, ← cochainComplexCoefficientMap_comp]
  congr 1
  rw [hG.associatedLocalSystemBaseChangeIso_inv_naturality_assoc k hH f hf b hb β,
    ← associatedLocalSystemMap_comp, ← hcomm, associatedLocalSystemMap_comp, Category.assoc]

/-- Along the identity map of a quotient cover, `associatedCochainComplexMap` reduces to
`cochainComplexCoefficientMap`. -/
@[simp]
theorem associatedCochainComplexMap_id_hom {A A' : Rep.{u} k G} (ξ : A ⟶ A') :
    hG.associatedCochainComplexMap k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ by simp)
        (𝟙 B) (by simp) ξ =
      cochainComplexCoefficientMap (hG.associatedLocalSystemMap k ξ) := by
  -- `Rep.res (MonoidHom.id G) A` is `A` by definition, so `associatedLocalSystemBaseChangeIso` has
  -- source `hG.associatedLocalSystem k A`.
  have hbc_hom :
      (hG.associatedLocalSystemBaseChangeIso k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ by simp)
          (𝟙 B) (by simp) A).hom ≫
        (LocalCoefficientSystem.pullbackIdIso.{u, u, u} B).hom.app
          (hG.associatedLocalSystem k A) =
      𝟙 (hG.associatedLocalSystem k A) :=
    (congrArg (· ≫ _)
      (hG.associatedLocalSystemBaseChangeIso_hom k hG (𝟙 E) (fun _ _ ↦ by simp) (𝟙 B) (by simp)
        A)).trans
      ((hG.associatedLocalSystemMapOver_id k (𝟙 A)).trans (hG.associatedLocalSystemMap_id k))
  have hp :
      (LocalCoefficientSystem.pullbackIdIso.{u, u, u} B).inv.app (hG.associatedLocalSystem k A) =
        (hG.associatedLocalSystemBaseChangeIso k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ by simp)
          (𝟙 B) (by simp) A).hom :=
    (cancel_mono ((LocalCoefficientSystem.pullbackIdIso.{u, u, u} B).hom.app
      (hG.associatedLocalSystem k A))).1
      ((Iso.inv_hom_id_app _ _).trans hbc_hom.symm)
  have hbc :
      (LocalCoefficientSystem.pullbackIdIso.{u, u, u} B).inv.app (hG.associatedLocalSystem k A) ≫
        (hG.associatedLocalSystemBaseChangeIso k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ by simp)
          (𝟙 B) (by simp) A).inv =
      𝟙 (hG.associatedLocalSystem k A) :=
    (congrArg (· ≫ _) hp).trans (Iso.hom_inv_id _)
  rw [associatedCochainComplexMap_def, cochainComplexPullback_id,
    ← cochainComplexCoefficientMap_comp]
  exact congrArg cochainComplexCoefficientMap
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ hG.associatedLocalSystemMap k ξ) hbc).trans (Category.id_comp _)))

/-- Along the identity map of a quotient cover with the identity representation morphism,
`associatedCochainComplexMap` is the identity cochain map. -/
-- Match before the general identity-homomorphism rule reduces to coefficient change.
@[simp↓]
theorem associatedCochainComplexMap_id (A : Rep.{u} k G) :
    hG.associatedCochainComplexMap k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ by simp)
        (𝟙 B) (by simp) (𝟙 A) =
      𝟙 _ := by
  rw [associatedCochainComplexMap_id_hom, associatedLocalSystemMap_id,
    cochainComplexCoefficientMap_id]

/-- Along a composite of equivariant maps of quotient covers, `associatedCochainComplexMap`
contravariantly composes the two induced cochain maps. -/
@[reassoc]
theorem associatedCochainComplexMap_comp
    {S W : _root_.TopCat.{u}} {r : S ⟶ W} {K : Type u} [Group K] [MulAction K S]
    (hK : IsQuotientCoveringMap r K) {φ' : H →* K}
    (f' : F ⟶ S) (hf' : ∀ h y, f' (h • y) = φ' h • f' y)
    (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    {V : Rep.{u} k K} {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) (ζ : Rep.res φ' V ⟶ D) :
    hG.associatedCochainComplexMap k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc])
        ((Rep.resFunctor φ).map ζ ≫ ξ) =
      hH.associatedCochainComplexMap k hK f' hf' b' hb' ζ ≫
        hG.associatedCochainComplexMap k hH f hf b hb ξ := by
  have hbc :
      (hG.associatedLocalSystemBaseChangeIso k hK (f ≫ f') (φ := φ'.comp φ)
          (fun g e ↦ by simp [hf, hf']) (b ≫ b')
          (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) V).inv =
        (LocalCoefficientSystem.pullbackCompIso.{u, u, u, u} b.hom b'.hom).hom.app
            (hK.associatedLocalSystem k V) ≫
          (LocalCoefficientSystem.pullback b.hom).map
            (hH.associatedLocalSystemBaseChangeIso k hK f' hf' b' hb' V).inv ≫
          (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb (Rep.res φ' V)).inv := by
    apply (cancel_epi (hG.associatedLocalSystemBaseChangeIso k hK (f ≫ f') (φ := φ'.comp φ)
      (fun g e ↦ by simp [hf, hf']) (b ≫ b')
      (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) V).hom).1
    rw [Iso.hom_inv_id, hG.associatedLocalSystemBaseChangeIso_hom_comp k hH hK
      f hf b hb f' hf' b' hb' V]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc ((LocalCoefficientSystem.pullback b.hom).map _),
      ← (LocalCoefficientSystem.pullback b.hom).map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  rw [associatedCochainComplexMap_def, associatedCochainComplexMap_def,
    associatedCochainComplexMap_def, Category.assoc,
    cochainComplexPullback_coefficient_naturality_assoc, ← cochainComplexPullback_comp_assoc]
  congr 1
  rw [← cochainComplexCoefficientMap_comp, ← cochainComplexCoefficientMap_comp,
    CategoryTheory.Functor.map_comp, Category.assoc,
    hG.associatedLocalSystemBaseChangeIso_inv_naturality_assoc k hH f hf b hb ζ,
    hbc, associatedLocalSystemMap_comp]
  congr 1

/-- **The direct cochain comparison is natural for equivariant maps of quotient covers.**
Pulling direct cochains back along `b : B ⟶ C` and changing local coefficients by
`ξ : Rep.res φ D ⟶ A` corresponds to the change-of-groups map
`φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf)` on equivariant cochains of the total
spaces. -/
@[reassoc]
theorem associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    hG.associatedCochainComplexMap k hH f hf b hb ξ ≫
        (hG.cochainComplexIsoLinearYonedaObj k A).hom =
      (hH.cochainComplexIsoLinearYonedaObj k D).hom ≫
        φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf) := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun c ↦ ?_
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    singularChains_linearMap_ext fun τ ↦ ?_
  let τF := (_root_.TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ
  -- Both routes evaluate `c` on `q ∘ f ∘ τ` in `initialSheet (f ∘ τ)` and apply `ξ`.
  have hleft :
      (((hG.associatedCochainComplexMap k hH f hf b hb ξ ≫
          (hG.cochainComplexIsoLinearYonedaObj k A).hom).f n c) :
        (singularChainsRep k E G).X n ⟶ A).hom (simplexChain τ 1) =
      ξ.hom ((hH.associatedLocalSystemFiberIso k D (initialSheet τF)).hom
        (cochainComplexEval (hH.associatedLocalSystem k D) n
          ((_root_.TopCat.toSSet.map q).app _ τF) c)) := by
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply,
      cochainComplexIsoLinearYonedaObj_hom_f_simplexChain, one_smul,
      hG.fiberIso_hom_eval_associatedCochainComplexMap_map_p k hH f hf b hb ξ n c τ]
  -- `φ.linearYonedaObjMap` acts on `((singularChainsRep k F H).linearYonedaObj k D).X n` by
  -- precomposing with `singularChainsRepResMap`, restricting along `φ`, and postcomposing with `ξ`.
  let w : (singularChainsRep k F H).X n ⟶ D :=
    (hH.cochainComplexIsoLinearYonedaObj k D).hom.f n c
  have hpush := (singularChainsRepResMap_f_hom_apply k f hf n (simplexChain τ 1)).trans
    (singularChains_map_f_simplexChain f τ 1)
  have hright :
      ((((hH.cochainComplexIsoLinearYonedaObj k D).hom ≫
          φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf)).f n c) :
        (singularChainsRep k E G).X n ⟶ A).hom (simplexChain τ 1) =
      ξ.hom ((hH.associatedLocalSystemFiberIso k D (initialSheet τF)).hom
        (cochainComplexEval (hH.associatedLocalSystem k D) n
          ((_root_.TopCat.toSSet.map q).app _ τF) c)) :=
    (congrArg (fun g : (singularChainsRep k E G).X n ⟶ A ↦ g.hom (simplexChain τ 1))
        ((ModuleCat.comp_apply _ _ c).trans
          (φ.linearYonedaObjMap_f_apply ξ (singularChainsRepResMap k f hf) n w))).trans <|
      (DFunLike.congr_fun
          (Rep.hom_comp _ _ _ ((singularChainsRepResMap k f hf).f n) (Rep.resMap φ w ≫ ξ))
        (simplexChain τ 1)).trans <|
      (DFunLike.congr_fun (Rep.hom_comp _ _ _ (Rep.resMap φ w) ξ)
        (((singularChainsRepResMap k f hf).f n).hom (simplexChain τ 1))).trans <|
      (congrArg ξ.hom (Rep.resMap_hom_apply φ w _)).trans <|
      (congrArg (fun z ↦ ξ.hom (w.hom z)) hpush).trans
        (congrArg ξ.hom
          ((hH.cochainComplexIsoLinearYonedaObj_hom_f_simplexChain k D n c τF 1).trans
            (one_smul k _)))
  exact hleft.trans hright.symm

/-- Inverse form of `associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom`. -/
@[reassoc]
theorem linearYonedaObjMap_comp_cochainComplexIsoLinearYonedaObj_inv
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf) ≫
        (hG.cochainComplexIsoLinearYonedaObj k A).inv =
      (hH.cochainComplexIsoLinearYonedaObj k D).inv ≫
        hG.associatedCochainComplexMap k hH f hf b hb ξ := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom k hH f hf b hb ξ,
    Iso.inv_hom_id_assoc]

/-- The contravariant map `Hⁿ(C; L_D) ⟶ Hⁿ(B; L_A)` on direct local-coefficient cohomology induced
by an equivariant map of quotient covers along `φ : G →* H` over `b : B ⟶ C` and a compatible
coefficient morphism `ξ : Rep.res φ D ⟶ A`. -/
def associatedCohomologyMap {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    (hH.associatedLocalSystem k D).cohomology n ⟶
      (hG.associatedLocalSystem k A).cohomology n :=
  cohomologyPullback b (hH.associatedLocalSystem k D) n ≫
    cohomologyCoefficientMap
      ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
        hG.associatedLocalSystemMap k ξ) n

/-- `associatedCohomologyMap` is cohomology pullback along `b` followed by the base-change and
coefficient maps. -/
theorem associatedCohomologyMap_def {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    hG.associatedCohomologyMap k hH f hf b hb ξ n =
      cohomologyPullback b (hH.associatedLocalSystem k D) n ≫
        cohomologyCoefficientMap
          ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
            hG.associatedLocalSystemMap k ξ) n :=
  (rfl)

/-- `associatedCohomologyMap` is the map on cohomology induced by `associatedCochainComplexMap`. -/
theorem associatedCohomologyMap_eq_homologyMap {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    hG.associatedCohomologyMap k hH f hf b hb ξ n =
      HomologicalComplex.homologyMap (hG.associatedCochainComplexMap k hH f hf b hb ξ) n := by
  rw [associatedCohomologyMap_def, cohomologyPullback_eq, cohomologyCoefficientMap_eq,
    ← HomologicalComplex.homologyMap_comp, associatedCochainComplexMap_def]

/-- `associatedCohomologyMap` is natural with respect to compatible morphisms of coefficient
representations: if `ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂`, then the induced cohomology maps form
a commutative square. -/
@[reassoc]
theorem associatedCohomologyMap_naturality
    {D₁ D₂ : Rep.{u} k H} {A₁ A₂ : Rep.{u} k G}
    (β : D₁ ⟶ D₂) (α : A₁ ⟶ A₂)
    (ξ₁ : Rep.res φ D₁ ⟶ A₁) (ξ₂ : Rep.res φ D₂ ⟶ A₂)
    (hcomm : ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂) (n : ℕ) :
    cohomologyCoefficientMap (hH.associatedLocalSystemMap k β) n ≫
        hG.associatedCohomologyMap k hH f hf b hb ξ₂ n =
      hG.associatedCohomologyMap k hH f hf b hb ξ₁ n ≫
        cohomologyCoefficientMap (hG.associatedLocalSystemMap k α) n := by
  rw [cohomologyCoefficientMap_eq, cohomologyCoefficientMap_eq,
    associatedCohomologyMap_eq_homologyMap, associatedCohomologyMap_eq_homologyMap,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    hG.associatedCochainComplexMap_naturality k hH f hf b hb β α ξ₁ ξ₂ hcomm]

/-- **The geometric connecting map of local-coefficient cohomology commutes with change of groups
on quotient covers**, without assuming contractibility of the total spaces. -/
@[reassoc]
theorem cohomologyδ_comp_associatedCohomologyMap
    {Y : ShortComplex (Rep.{u} k H)} {X : ShortComplex (Rep.{u} k G)}
    (hY : Y.ShortExact) (hX : X.ShortExact)
    (Φ : Y.map (Rep.resFunctor φ) ⟶ X) (n m : ℕ) (h : n + 1 = m := by lia) :
    (hH.shortExact_associatedLocalSystem k hY).cohomologyδ n m h ≫
        hG.associatedCohomologyMap k hH f hf b hb Φ.τ₁ m =
      hG.associatedCohomologyMap k hH f hf b hb Φ.τ₃ n ≫
        (hG.shortExact_associatedLocalSystem k hX).cohomologyδ n m h := by
  let ψ : (Y.map (hH.associatedLocalSystemFunctor k)).map (cochainComplexFunctor k C) ⟶
      (X.map (hG.associatedLocalSystemFunctor k)).map (cochainComplexFunctor k B) :=
    { τ₁ := hG.associatedCochainComplexMap k hH f hf b hb Φ.τ₁
      τ₂ := hG.associatedCochainComplexMap k hH f hf b hb Φ.τ₂
      τ₃ := hG.associatedCochainComplexMap k hH f hf b hb Φ.τ₃
      comm₁₂ := (hG.associatedCochainComplexMap_naturality k hH f hf b hb Y.f X.f Φ.τ₁ Φ.τ₂
        Φ.comm₁₂).symm
      comm₂₃ := (hG.associatedCochainComplexMap_naturality k hH f hf b hb Y.g X.g Φ.τ₂ Φ.τ₃
        Φ.comm₂₃).symm }
  rw [ShortComplex.ShortExact.cohomologyδ_eq_δ, ShortComplex.ShortExact.cohomologyδ_eq_δ,
    associatedCohomologyMap_eq_homologyMap, associatedCohomologyMap_eq_homologyMap]
  exact HomologicalComplex.HomologySequence.δ_naturality ψ
    ((hH.shortExact_associatedLocalSystem k hY).map_cochainComplexFunctor)
    ((hG.shortExact_associatedLocalSystem k hX).map_cochainComplexFunctor) n m h

/-- Along the identity map of a quotient cover, `associatedCohomologyMap` reduces to
`cohomologyCoefficientMap`. -/
@[simp]
theorem associatedCohomologyMap_id_hom {A A' : Rep.{u} k G} (ξ : A ⟶ A') (n : ℕ) :
    hG.associatedCohomologyMap k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ by simp)
        (𝟙 B) (by simp) ξ n =
      cohomologyCoefficientMap (hG.associatedLocalSystemMap k ξ) n := by
  rw [associatedCohomologyMap_eq_homologyMap, associatedCochainComplexMap_id_hom,
    cohomologyCoefficientMap_eq]

/-- Along the identity map of a quotient cover with the identity representation morphism,
`associatedCohomologyMap` is the identity on cohomology. -/
-- Match before the general identity-homomorphism rule reduces to coefficient change.
@[simp↓]
theorem associatedCohomologyMap_id (A : Rep.{u} k G) (n : ℕ) :
    hG.associatedCohomologyMap k hG (𝟙 E) (φ := MonoidHom.id G) (fun _ _ ↦ by simp)
        (𝟙 B) (by simp) (𝟙 A) n =
      𝟙 _ := by
  rw [associatedCohomologyMap_id_hom, associatedLocalSystemMap_id,
    cohomologyCoefficientMap_id]

/-- Along a composite of equivariant maps of quotient covers, `associatedCohomologyMap`
contravariantly composes the two induced cohomology maps. -/
@[reassoc]
theorem associatedCohomologyMap_comp
    {S W : _root_.TopCat.{u}} {r : S ⟶ W} {K : Type u} [Group K] [MulAction K S]
    (hK : IsQuotientCoveringMap r K) {φ' : H →* K}
    (f' : F ⟶ S) (hf' : ∀ h y, f' (h • y) = φ' h • f' y)
    (b' : C ⟶ W) (hb' : q ≫ b' = f' ≫ r)
    {V : Rep.{u} k K} {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) (ζ : Rep.res φ' V ⟶ D) (n : ℕ) :
    hG.associatedCohomologyMap k hK (f ≫ f') (φ := φ'.comp φ)
        (fun g e ↦ by simp [hf, hf']) (b ≫ b')
        (by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc])
        ((Rep.resFunctor φ).map ζ ≫ ξ) n =
      hH.associatedCohomologyMap k hK f' hf' b' hb' ζ n ≫
        hG.associatedCohomologyMap k hH f hf b hb ξ n := by
  rw [associatedCohomologyMap_eq_homologyMap, associatedCohomologyMap_eq_homologyMap,
    associatedCohomologyMap_eq_homologyMap, ← HomologicalComplex.homologyMap_comp,
    hG.associatedCochainComplexMap_comp k hH f hf b hb hK f' hf' b' hb' ξ ζ]

/-- **The local-coefficient cohomology of the base of a contractible free cover is naturally group
cohomology, in the covering and the group**: for quotient covering maps `p : E ⟶ B` and `q : F ⟶ C`
with contractible total spaces, an equivariant map `f : E ⟶ F` along any `φ : G →* H` over
`b : B ⟶ C`, and a compatible morphism `ξ : Rep.res φ D ⟶ A`, the identifications
`Hⁿ(C; L_D) ≅ Hⁿ(H, D)` and `Hⁿ(B; L_A) ≅ Hⁿ(G, A)` carry `associatedCohomologyMap` to Mathlib's
`groupCohomology.map φ ξ n`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_hom_naturality_over
    [ContractibleSpace E] [ContractibleSpace F]
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    hG.associatedCohomologyMap k hH f hf b hb ξ n ≫
        (hG.cohomologyIsoGroupCohomology k A n).hom =
      (hH.cohomologyIsoGroupCohomology k D n).hom ≫
        groupCohomology.map φ ξ n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (hG.associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom k hH f hf b hb
        ξ)).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [associatedCohomologyMap_eq_homologyMap, cohomologyIsoGroupCohomology_hom_eq,
    cohomologyIsoGroupCohomology_hom_eq]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (φ.groupCohomologyIso_inv_naturality ξ (singularChainsResolution k E G)
        (singularChainsResolution k F H) (singularChainsRepResMap k f hf)
        (singularChainsRepResMap_f_zero_comp_augmentation k f hf) n)).trans
    (Category.assoc _ _ _).symm

/-- Inverse form of `cohomologyIsoGroupCohomology_hom_naturality_over`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_inv_naturality_over
    [ContractibleSpace E] [ContractibleSpace F]
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    groupCohomology.map φ ξ n ≫
        (hG.cohomologyIsoGroupCohomology k A n).inv =
      (hH.cohomologyIsoGroupCohomology k D n).inv ≫
        hG.associatedCohomologyMap k hH f hf b hb ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.cohomologyIsoGroupCohomology_hom_naturality_over k hH f hf b hb ξ n, Iso.inv_hom_id_assoc]

/-- Pulling direct local-coefficient cohomology back along `b : B ⟶ C` from `L_D` to `b^* L_D`
corresponds, via `IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso`, to
`groupCohomology.map φ (𝟙 (Rep.res φ D)) n`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_hom_pullback
    [ContractibleSpace E] [ContractibleSpace F] (D : Rep.{u} k H) (n : ℕ) :
    cohomologyPullback b (hH.associatedLocalSystem k D) n ≫
        cohomologyCoefficientMap
          (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv n ≫
        (hG.cohomologyIsoGroupCohomology k (Rep.res φ D) n).hom =
      (hH.cohomologyIsoGroupCohomology k D n).hom ≫
        groupCohomology.map φ (𝟙 (Rep.res φ D)) n := by
  have h := hG.cohomologyIsoGroupCohomology_hom_naturality_over k hH f hf b hb
    (𝟙 (Rep.res φ D)) n
  rw [associatedCohomologyMap_def, associatedLocalSystemMap_id, Category.comp_id,
    Category.assoc] at h
  exact h

/-- Inverse form of `cohomologyIsoGroupCohomology_hom_pullback`: the inverse comparisons carry
`groupCohomology.map φ (𝟙 (Rep.res φ D)) n` to `cohomologyPullback b`, up to
`associatedLocalSystemBaseChangeIso`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_inv_pullback
    [ContractibleSpace E] [ContractibleSpace F] (D : Rep.{u} k H) (n : ℕ) :
    (hH.cohomologyIsoGroupCohomology k D n).inv ≫
        cohomologyPullback b (hH.associatedLocalSystem k D) n =
      groupCohomology.map φ (𝟙 (Rep.res φ D)) n ≫
        (hG.cohomologyIsoGroupCohomology k (Rep.res φ D) n).inv ≫
        cohomologyCoefficientMap
          (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom n := by
  have h := hG.cohomologyIsoGroupCohomology_inv_naturality_over k hH f hf b hb
    (𝟙 (Rep.res φ D)) n
  rw [associatedCohomologyMap_def, associatedLocalSystemMap_id, Category.comp_id] at h
  have hcancel :
      cohomologyCoefficientMap (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv n ≫
        cohomologyCoefficientMap (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom n =
      𝟙 _ := by
    rw [← cohomologyCoefficientMap_comp, Iso.inv_hom_id, cohomologyCoefficientMap_id]
  have h' := h =≫
    cohomologyCoefficientMap (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom n
  simpa only [Category.assoc, hcancel, Category.comp_id] using h'.symm

end IsQuotientCoveringMap
