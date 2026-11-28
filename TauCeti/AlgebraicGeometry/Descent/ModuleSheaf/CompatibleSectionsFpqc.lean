/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Descent.ModuleSheaf.CompatibleSections
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Fpqc
import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Prestack

/-!
# Compatible sections of fpqc descent data

Compatible sections of quasi-coherent descent data along an fpqc covering family form a
quasi-coherent module. Its canonical pullback comparison realizes the descent datum.
The fpqc stack equivalence supplies a quasi-coherent realization, and gluing morphisms into
that realization identifies it with the module constructed from compatible sections.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules CategoryTheory
  Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Descent.ModuleSheaf

variable {S : Scheme.{u}} {ι : Type u} {X : ι → Scheme.{u}} {p : ∀ i, X i ⟶ S}

/-- Forget quasi-coherence in a native descent datum. -/
public def underlying (D : qcohPseudofunctor.DescentData p) :
    modulesPseudofunctor.DescentData p where
  obj i := (D.obj i).obj
  hom Y q i j a b ha hb := (D.hom q a b ha hb).hom
  pullHom_hom Z Y g q q' hq i j a b ha hb a' b' ha' hb' := by
    rw [← qcohPseudofunctor_pullHom_hom]
    exact congrArg (fun f ↦ f.hom) (D.pullHom_hom g q q' hq a b ha hb a' b' ha' hb')
  hom_self Y q i a ha := congrArg (fun f ↦ f.hom) (D.hom_self q a ha)
  hom_comp Y q i j k a b c ha hb hc := congrArg (fun f ↦ f.hom)
    (D.hom_comp q a b c ha hb hc)

private def underlyingHom {D E : qcohPseudofunctor.DescentData p} (φ : D ⟶ E) :
    underlying D ⟶ underlying E where
  hom i := (φ.hom i).hom
  comm _ q _ _ a b ha hb := congrArg (fun f ↦ f.hom) (φ.comm q a b ha hb)

private def forgetQuasicoherence :
    qcohPseudofunctor.DescentData p ⥤ modulesPseudofunctor.DescentData p where
  obj := underlying
  map := underlyingHom
  map_id _ := Pseudofunctor.DescentData.hom_ext fun _ ↦ rfl
  map_comp _ _ := Pseudofunctor.DescentData.hom_ext fun _ ↦ rfl

private abbrev pulledDatum (M : S.Modules) :=
  Pseudofunctor.DescentData.ofObj (F := modulesPseudofunctor) (f := p) M

private abbrev pulledDatumQcoh (M : QuasicoherentSheaf S) :=
  Pseudofunctor.DescentData.ofObj (F := qcohPseudofunctor) (f := p) M

private lemma ofObjUnderlyingComm (M : QuasicoherentSheaf S) {Y : Scheme.{u}}
    (q : Y ⟶ S) {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ p i = q) (hb : b ≫ p j = q) :
    (pullback a).map (𝟙 ((pullback (p i)).obj M.obj)) ≫
        ((pulledDatumQcoh (p := p) M).hom q a b ha hb).hom =
      (pulledDatum (p := p) M.obj).hom q a b ha hb ≫
        (pullback b).map (𝟙 ((pullback (p j)).obj M.obj)) := by
  have h₁ := qcohPseudofunctor_mapComp'_inv_toNatTrans_app_hom (p i) a q ha M
  have h₂ := qcohPseudofunctor_mapComp'_hom_toNatTrans_app_hom (p j) b q hb M
  have h₃ := modulesPseudofunctor_mapComp'_inv_toNatTrans_app (p i) a q ha M.obj
  have h₄ := modulesPseudofunctor_mapComp'_hom_toNatTrans_app (p j) b q hb M.obj
  let α : (pullback a).obj ((pullback (p i)).obj M.obj) ⟶
      (pullback b).obj ((pullback (p j)).obj M.obj) :=
    ((pulledDatumQcoh (p := p) M).hom q a b ha hb).hom
  let β : (pullback a).obj ((pullback (p i)).obj M.obj) ⟶
      (pullback b).obj ((pullback (p j)).obj M.obj) :=
    (pulledDatum (p := p) M.obj).hom q a b ha hb
  have h : α = β :=
    (congrArg₂ (fun r s ↦ r ≫ s) h₁ h₂).trans
      (congrArg₂ (fun r s ↦ r ≫ s) h₃ h₄).symm
  calc
    _ = α := (congrArg (· ≫ α) ((pullback a).map_id _)).trans (Category.id_comp _)
    _ = β := h
    _ = _ := ((congrArg (β ≫ ·) ((pullback b).map_id _)).trans (Category.comp_id _)).symm

private def ofObjUnderlyingIso (M : QuasicoherentSheaf S) :
    pulledDatum (p := p) M.obj ≅ underlying (pulledDatumQcoh (p := p) M) :=
  Pseudofunctor.DescentData.isoMk
    (D₁ := pulledDatum (p := p) M.obj) (D₂ := underlying (pulledDatumQcoh (p := p) M))
    (fun i ↦ Iso.refl ((pullback (p i)).obj M.obj))
    (by
      intro Y q i j a b ha hb
      -- The components of both descent data are the native pullback modules.
      change (pullback a).map (𝟙 ((pullback (p i)).obj M.obj)) ≫
          ((pulledDatumQcoh (p := p) M).hom q a b ha hb).hom =
        (pulledDatum (p := p) M.obj).hom q a b ha hb ≫
          (pullback b).map (𝟙 ((pullback (p j)).obj M.obj))
      exact @ofObjUnderlyingComm S ι X p M Y q i j a b ha hb)

private theorem exists_map_eq_of_fpqc {M N : S.Modules} [N.IsQuasicoherent]
    (hp : Sieve.ofArrows X p ∈ fpqcTopology S)
    (φ : pulledDatum (p := p) M ⟶ pulledDatum (p := p) N) :
    ∃ ψ : M ⟶ N, (modulesPseudofunctor.toDescentData p).map ψ = φ := by
  let X' := fun i ↦ Over.mk (p i)
  let p' : ∀ i, X' i ⟶ Over.mk (𝟙 S) := fun i ↦ Over.homMk (p i)
  let R : Sieve (Over.mk (𝟙 S)) := Sieve.ofArrows X' p'
  have hR : R ∈ (fpqcTopology.over S) (Over.mk (𝟙 S)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hp
  let e := Pseudofunctor.DescentData.subtypeCompatibleHomEquiv modulesPseudofunctor p
    (M := M) (N := N)
  let x := e.symm φ
  let y := x.property.familyOfElements
  have hy := x.property.familyOfElements_compatible
  obtain ⟨ψ, hψ, _⟩ := existsUnique_pullback_map_eq_of_mem_fpqcTopology hR
    (fun _ g hg ↦ y.sieveExtend g hg) fun _ _ a g hg ↦ hy.sieveExtend.to_sieveCompatible g a hg
  refine ⟨ψ, Pseudofunctor.DescentData.hom_ext fun i ↦ ?_⟩
  have he := congrArg (fun k : pulledDatum (p := p) M ⟶ pulledDatum (p := p) N ↦ k.hom i)
    (e.apply_symm_apply φ)
  exact (hψ (p' i) (Sieve.ofArrows_mk X' p' i)).trans
    ((Presieve.extend_agrees hy (Presieve.ofArrows.mk i)).trans
      ((x.property.familyOfElements_ofArrows_mk i).trans he))

private theorem descent_of_lift {C E : Type*} [Category* C] [Category* E]
    (G : C ⥤ E) {M L : C} {D : E} (c : G.obj L ⟶ D) (e : G.obj M ≅ D)
    (α : M ⟶ L) (β : L ⟶ M) (hα : G.map α ≫ c = e.hom) (hβ : G.map β = c ≫ e.inv)
    (hL : ∀ {f g : L ⟶ L}, G.map f ≫ c = G.map g ≫ c → f = g)
    (hM : ∀ {f g : M ⟶ M}, G.map f = G.map g → f = g) :
    Nonempty (M ≅ L) ∧ IsIso c := by
  have hβα : β ≫ α = 𝟙 L := hL (by simp [hβ, hα])
  have hαβ : α ≫ β = 𝟙 M := hM (by simp [hβ, reassoc_of% hα])
  refine ⟨⟨⟨α, β, hαβ, hβα⟩⟩, ⟨⟨e.inv ≫ G.map α, ?_, by simp [hα]⟩⟩⟩
  calc
    c ≫ e.inv ≫ G.map α = G.map β ≫ G.map α := by rw [← Category.assoc, hβ]
    _ = 𝟙 _ := by rw [← G.map_comp, hβα, G.map_id]

private theorem descent_of_effective {D : modulesPseudofunctor.DescentData p}
    (hp : Sieve.ofArrows X p ∈ fpqcTopology S) {M : S.Modules} [M.IsQuasicoherent]
    (e : pulledDatum (p := p) M ≅ D)
    (hM : ∀ {φ ψ : M ⟶ M}, (modulesPseudofunctor.toDescentData p).map φ =
      (modulesPseudofunctor.toDescentData p).map ψ → φ = ψ) :
    Nonempty (M ≅ descendedModule (D := D)) ∧ IsIso (comparisonHom D) := by
  let G := modulesPseudofunctor.toDescentData p
  let α := lift e.hom
  let c := comparisonHom D
  have hα : G.map α ≫ c = e.hom := toDescentData_map_lift_comp_comparisonHom e.hom
  obtain ⟨β, hβ⟩ := exists_map_eq_of_fpqc hp (c ≫ e.inv)
  exact descent_of_lift G c e α β hα hβ (fun h ↦ hom_ext_of_comparisonHom h) hM

private theorem map_injective_of_qcohFaithful
    [(qcohPseudofunctor.toDescentData p).Faithful] (M : QuasicoherentSheaf S)
    {φ ψ : M.obj ⟶ M.obj} (h : (modulesPseudofunctor.toDescentData p).map φ =
      (modulesPseudofunctor.toDescentData p).map ψ) : φ = ψ := by
  let F := qcohPseudofunctor.toDescentData p
  let f : M ⟶ M := ObjectProperty.homMk φ
  let g : M ⟶ M := ObjectProperty.homMk ψ
  have hfg : F.map f = F.map g := Pseudofunctor.DescentData.hom_ext fun i ↦
    ObjectProperty.hom_ext _ (congrArg (fun k ↦ k.hom i) h)
  exact congrArg (fun k ↦ k.hom) (F.map_injective hfg)

private theorem fpqcDescentComparison (hp : Sieve.ofArrows X p ∈ fpqcTopology S)
    (D : qcohPseudofunctor.DescentData p) :
    (descendedModule (D := underlying D)).IsQuasicoherent ∧
      IsIso (comparisonHom (underlying D)) := by
  let F := qcohPseudofunctor.toDescentData p
  have : F.IsEquivalence := qcohPseudofunctor.isEquivalence_toDescentData p hp
  let M : QuasicoherentSheaf S := F.objPreimage D
  have : M.obj.IsQuasicoherent := M.property
  let e := ofObjUnderlyingIso (p := p) M ≪≫ forgetQuasicoherence.mapIso (F.objObjPreimageIso D)
  obtain ⟨⟨i⟩, hi⟩ := descent_of_effective hp e
    (fun h ↦ map_injective_of_qcohFaithful M h)
  exact ⟨(SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso i M.property, hi⟩

/-- Compatible sections of a quasi-coherent datum along an fpqc covering family form a
quasi-coherent module on the base. -/
public theorem isQuasicoherent_descendedModule_of_mem_fpqcTopology
    (hp : Sieve.ofArrows X p ∈ fpqcTopology S) (D : qcohPseudofunctor.DescentData p) :
    (descendedModule (D := underlying D)).IsQuasicoherent :=
  (fpqcDescentComparison hp D).1

/-- The canonical pullback comparison realizes quasi-coherent descent data along an fpqc
covering family. -/
public theorem isIso_comparisonHom_of_mem_fpqcTopology
    (hp : Sieve.ofArrows X p ∈ fpqcTopology S) (D : qcohPseudofunctor.DescentData p) :
    IsIso (comparisonHom (underlying D)) :=
  (fpqcDescentComparison hp D).2

end TauCeti.AlgebraicGeometry.Descent.ModuleSheaf
