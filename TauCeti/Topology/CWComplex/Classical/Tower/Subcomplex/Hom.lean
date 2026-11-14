/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Map
public import TauCeti.Topology.CWComplex.Classical.Tower.Subcomplex.Colimit

/-!
# Cellular morphisms of CW subcomplex towers

For a sequential tower `T : TauCeti.CWSubcomplexTower W newCell`, every stage map `T.step k` and
colimit inclusion `c.ι.app k` / `T.incl k` is cellular (`isCellular_step`, `isCellular_ι`,
`isCellular_incl`). Stagewise cellular morphisms between towers (`TauCeti.CWSubcomplexTower.Hom`)
induce cellular maps on colimits (`Hom.isCellular_mapOfIsColimit`, `Hom.isCellular_unionMap`) whose
skeletal restrictions commute with stage inclusions (`Hom.skeletonMap_ι_comp`,
`Hom.skeletonMap_incl_comp`).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti.CWSubcomplexTower

section SingleTower

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell)

/-- Each stage inclusion `T.step k : W k → W (k + 1)` is cellular. -/
theorem isCellular_step (k : ℕ) :
    IsCellular (univ : Set (W k)) (univ : Set (W (k + 1)))
      (TopCat.ofHom ((T.step k).restrictPreimage univ)) :=
  isCellular_univ_of_map_eq fun n i ↦ ⟨T.oldCellEquiv k n i, fun _ hx ↦ T.step_map_eq_map k n i hx⟩

/-- For any colimit cocone `c` of `T.diagram`, each stage inclusion `c.ι.app k : W k → c.pt` is
cellular. -/
theorem isCellular_ι {c : Cocone T.diagram} (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc; letI := T.t2Space_of_isColimit hc
    IsCellular (univ : Set (W k)) (univ : Set c.pt)
      (TopCat.ofHom ((c.ι.app k).hom.restrictPreimage univ)) :=
  letI := T.cwComplexOfIsColimit hc; letI := T.t2Space_of_isColimit hc
  isCellular_univ_of_map_eq fun n i ↦
    ⟨(T.cwComplexOfIsColimitCellEquiv hc n).symm ((T.stageCellEquiv k n).symm i).1,
      fun _ hx ↦ T.ι_map_eq_map hc k n i hx⟩

/-- Each stage inclusion `T.incl k : W k → T.Union` is cellular. -/
theorem isCellular_incl (k : ℕ) :
    IsCellular (univ : Set (W k)) (univ : Set T.Union)
      (TopCat.ofHom ((T.incl k).hom.restrictPreimage univ)) := by
  rw [T.instCWComplexUnion_eq]; exact T.isCellular_ι (colimit.isColimit T.diagram) k

end SingleTower

/-- A cellular morphism between two `CWSubcomplexTower`s: a family of continuous stage maps
commuting with the stage inclusions such that each stage map is cellular. -/
structure Hom {W₁ W₂ : ℕ → Type u}
    [∀ k, TopologicalSpace (W₁ k)] [∀ k, T2Space (W₁ k)] [∀ k, CWComplex (univ : Set (W₁ k))]
    [∀ k, TopologicalSpace (W₂ k)] [∀ k, T2Space (W₂ k)] [∀ k, CWComplex (univ : Set (W₂ k))]
    {newCell₁ newCell₂ : ℕ → ℕ → Type u}
    (T₁ : CWSubcomplexTower W₁ newCell₁) (T₂ : CWSubcomplexTower W₂ newCell₂) where
  /-- The stage map `W₁ k → W₂ k`. -/
  app (k : ℕ) : C(W₁ k, W₂ k)
  /-- Commutativity with stage inclusions. -/
  comm (k : ℕ) : (app (k + 1)).comp (T₁.step k) = (T₂.step k).comp (app k)
  /-- Each stage map is cellular. -/
  isCellular_app (k : ℕ) :
    IsCellular (univ : Set (W₁ k)) (univ : Set (W₂ k))
      (TopCat.ofHom ((app k).restrictPreimage univ))

namespace Hom

variable {W₁ W₂ W₃ W₄ : ℕ → Type u}
  [∀ k, TopologicalSpace (W₁ k)] [∀ k, T2Space (W₁ k)] [∀ k, CWComplex (univ : Set (W₁ k))]
  [∀ k, TopologicalSpace (W₂ k)] [∀ k, T2Space (W₂ k)] [∀ k, CWComplex (univ : Set (W₂ k))]
  [∀ k, TopologicalSpace (W₃ k)] [∀ k, T2Space (W₃ k)] [∀ k, CWComplex (univ : Set (W₃ k))]
  [∀ k, TopologicalSpace (W₄ k)] [∀ k, T2Space (W₄ k)] [∀ k, CWComplex (univ : Set (W₄ k))]
  {newCell₁ newCell₂ newCell₃ newCell₄ : ℕ → ℕ → Type u}
  {T₁ : CWSubcomplexTower W₁ newCell₁} {T₂ : CWSubcomplexTower W₂ newCell₂}
  {T₃ : CWSubcomplexTower W₃ newCell₃} {T₄ : CWSubcomplexTower W₄ newCell₄}

@[ext] theorem ext {φ ψ : T₁.Hom T₂} (h : ∀ k, φ.app k = ψ.app k) : φ = ψ := by
  cases φ; cases ψ; congr; exact funext h

@[simp] lemma comm_apply (φ : T₁.Hom T₂) (k : ℕ) (x : W₁ k) :
    φ.app (k + 1) (T₁.step k x) = T₂.step k (φ.app k x) :=
  ContinuousMap.congr_fun (φ.comm k) x

/-- The identity cellular morphism on a `CWSubcomplexTower`. -/
def id (T₁ : CWSubcomplexTower W₁ newCell₁) : T₁.Hom T₁ where
  app k := ContinuousMap.id (W₁ k)
  comm _ := rfl
  isCellular_app _ := isCellular_univ_iff.2 fun _ ↦ mapsTo_id _

@[simp] lemma id_app (T₁ : CWSubcomplexTower W₁ newCell₁) (k : ℕ) :
    (Hom.id T₁).app k = ContinuousMap.id (W₁ k) := (rfl)

/-- Composition of cellular morphisms of `CWSubcomplexTower`s. -/
def comp (ψ : T₂.Hom T₃) (φ : T₁.Hom T₂) : T₁.Hom T₃ where
  app k := (ψ.app k).comp (φ.app k)
  comm k := by ext x; simp
  isCellular_app k := isCellular_univ_iff.2 fun n ↦
    (isCellular_univ_iff.1 (ψ.isCellular_app k) n).comp
      (isCellular_univ_iff.1 (φ.isCellular_app k) n)

@[simp] lemma comp_app (ψ : T₂.Hom T₃) (φ : T₁.Hom T₂) (k : ℕ) :
    (ψ.comp φ).app k = (ψ.app k).comp (φ.app k) := (rfl)

@[simp] lemma id_comp (φ : T₁.Hom T₂) : (Hom.id T₂).comp φ = φ := by ext; rfl

@[simp] lemma comp_id (φ : T₁.Hom T₂) : φ.comp (Hom.id T₁) = φ := by ext; rfl

@[simp] lemma comp_assoc (χ : T₃.Hom T₄) (ψ : T₂.Hom T₃) (φ : T₁.Hom T₂) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by ext; rfl

/-- The natural transformation `T₁.diagram ⟶ T₂.diagram` induced by `φ : T₁.Hom T₂`. -/
def natTrans (φ : T₁.Hom T₂) : T₁.diagram ⟶ T₂.diagram :=
  NatTrans.ofSequence (fun k ↦ TopCat.ofHom (φ.app k)) fun k ↦ by
    rw [T₁.diagram_map_succ, T₂.diagram_map_succ]; ext x; exact φ.comm_apply k x

@[simp] lemma natTrans_app (φ : T₁.Hom T₂) (k : ℕ) : φ.natTrans.app k = TopCat.ofHom (φ.app k) :=
  (rfl)

@[simp] lemma natTrans_id : (Hom.id T₁).natTrans = 𝟙 T₁.diagram :=
  NatTrans.ext <| funext fun _ ↦ TopCat.ofHom_id

@[simp] lemma natTrans_comp (ψ : T₂.Hom T₃) (φ : T₁.Hom T₂) :
    (ψ.comp φ).natTrans = φ.natTrans ≫ ψ.natTrans :=
  NatTrans.ext <| funext fun k ↦ TopCat.ofHom_comp (φ.app k) (ψ.app k)

/-- The induced morphism `c₁.pt ⟶ c₂.pt` from a colimit cocone `c₁` of `T₁.diagram` to `c₂`. -/
def mapOfIsColimit (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) : c₁.pt ⟶ c₂.pt := hc₁.map c₂ φ.natTrans

@[reassoc (attr := simp)] lemma ι_comp_mapOfIsColimit (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram}
    {c₂ : Cocone T₂.diagram} (hc₁ : IsColimit c₁) (k : ℕ) :
    c₁.ι.app k ≫ φ.mapOfIsColimit hc₁ = TopCat.ofHom (φ.app k) ≫ c₂.ι.app k :=
  hc₁.ι_map c₂ φ.natTrans k

@[simp] lemma mapOfIsColimit_ι_apply (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram}
    {c₂ : Cocone T₂.diagram} (hc₁ : IsColimit c₁) (k : ℕ) (x : W₁ k) :
    dsimp% φ.mapOfIsColimit (c₂ := c₂) hc₁ (c₁.ι.app k x) = c₂.ι.app k (φ.app k x) :=
  ConcreteCategory.congr_hom (φ.ι_comp_mapOfIsColimit hc₁ k) x

@[simp] lemma mapOfIsColimit_id {c₁ : Cocone T₁.diagram} (hc₁ : IsColimit c₁) :
    (Hom.id T₁).mapOfIsColimit (c₂ := c₁) hc₁ = 𝟙 c₁.pt := hc₁.hom_ext fun k ↦ by simp

@[reassoc (attr := simp)] lemma mapOfIsColimit_comp_mapOfIsColimit (ψ : T₂.Hom T₃) (φ : T₁.Hom T₂)
    {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram} {c₃ : Cocone T₃.diagram}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    φ.mapOfIsColimit (c₂ := c₂) hc₁ ≫ ψ.mapOfIsColimit (c₂ := c₃) hc₂ =
      (ψ.comp φ).mapOfIsColimit (c₂ := c₃) hc₁ :=
  hc₁.hom_ext fun k ↦ by simp [TopCat.ofHom_comp]

/-- **Cellular naturality:** the map induced on colimits by a cellular tower morphism is
cellular. -/
theorem isCellular_mapOfIsColimit (φ : T₁.Hom T₂)
    {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    letI := T₁.cwComplexOfIsColimit hc₁; letI := T₁.t2Space_of_isColimit hc₁
    letI := T₂.cwComplexOfIsColimit hc₂; letI := T₂.t2Space_of_isColimit hc₂
    IsCellular (univ : Set c₁.pt) (univ : Set c₂.pt)
      (TopCat.ofHom ((φ.mapOfIsColimit (c₂ := c₂) hc₁).hom.restrictPreimage univ)) := by
  let _ := T₁.cwComplexOfIsColimit hc₁; let _ := T₁.t2Space_of_isColimit hc₁
  let _ := T₂.cwComplexOfIsColimit hc₂; let _ := T₂.t2Space_of_isColimit hc₂
  refine isCellular_univ_iff.2 fun n z hz ↦ ?_
  rcases RelCWComplex.mem_skeletonLT_iff.1 hz with hzEmpty | ⟨m, hmn, i, hzi⟩
  · exact hzEmpty.elim
  · obtain ⟨p, rfl⟩ := (T₁.cwComplexOfIsColimitCellEquiv hc₁ m).symm.surjective i
    rw [T₁.openCell_cwComplexOfIsColimitCellEquiv_symm hc₁] at hzi
    obtain ⟨y, hy, rfl⟩ := hzi
    have hy_skel : y ∈ skeletonLT (univ : Set (W₁ p.1)) (n : ℕ∞) :=
      RelCWComplex.mem_skeletonLT_iff.2 (Or.inr ⟨m, hmn, T₁.birthCell p.1 m p.2, hy⟩)
    rw [φ.mapOfIsColimit_ι_apply hc₁]
    exact isCellular_univ_iff.1 (T₂.isCellular_ι hc₂ p.1) n
      (isCellular_univ_iff.1 (φ.isCellular_app p.1) n hy_skel)

/-- On every skeleton, `φ.mapOfIsColimit hc₁` commutes with stage skeletal restrictions. -/
@[reassoc] theorem skeletonMap_ι_comp (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram}
    {c₂ : Cocone T₂.diagram} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) (k n : ℕ) :
    letI := T₁.cwComplexOfIsColimit hc₁; letI := T₁.t2Space_of_isColimit hc₁
    letI := T₂.cwComplexOfIsColimit hc₂; letI := T₂.t2Space_of_isColimit hc₂
    skeletonMap _ _ (T₁.isCellular_ι hc₁ k) n ≫
      skeletonMap _ _ (φ.isCellular_mapOfIsColimit hc₁ hc₂) n =
      skeletonMap _ _ (φ.isCellular_app k) n ≫ skeletonMap _ _ (T₂.isCellular_ι hc₂ k) n :=
  letI := T₁.cwComplexOfIsColimit hc₁; letI := T₁.t2Space_of_isColimit hc₁
  letI := T₂.cwComplexOfIsColimit hc₂; letI := T₂.t2Space_of_isColimit hc₂
  skeletonMap_univ_comm _ _ _ _ (φ.mapOfIsColimit_ι_apply hc₁ k) n

/-- The induced continuous map `T₁.Union ⟶ T₂.Union` between canonical tower unions. -/
def unionMap (φ : T₁.Hom T₂) : T₁.Union ⟶ T₂.Union := Limits.colimMap φ.natTrans

@[reassoc (attr := simp)]
lemma incl_comp_unionMap (φ : T₁.Hom T₂) (k : ℕ) :
    T₁.incl k ≫ φ.unionMap = TopCat.ofHom (φ.app k) ≫ T₂.incl k :=
  Limits.ι_colimMap φ.natTrans k

@[simp] lemma unionMap_incl_apply (φ : T₁.Hom T₂) (k : ℕ) (x : W₁ k) :
    φ.unionMap (T₁.incl k x) = T₂.incl k (φ.app k x) :=
  ConcreteCategory.congr_hom (φ.incl_comp_unionMap k) x

lemma unionMap_eq_mapOfIsColimit (φ : T₁.Hom T₂) :
    φ.unionMap =
      φ.mapOfIsColimit (c₂ := colimit.cocone T₂.diagram) (colimit.isColimit T₁.diagram) :=
  colimit.hom_ext fun k ↦ (φ.incl_comp_unionMap k).trans
    (φ.ι_comp_mapOfIsColimit (c₂ := colimit.cocone T₂.diagram)
      (colimit.isColimit T₁.diagram) k).symm

@[simp] lemma unionMap_id : (Hom.id T₁).unionMap = 𝟙 T₁.Union := colimit.hom_ext fun k ↦ by simp

@[simp, reassoc] lemma unionMap_comp (ψ : T₂.Hom T₃) (φ : T₁.Hom T₂) :
    (ψ.comp φ).unionMap = φ.unionMap ≫ ψ.unionMap :=
  colimit.hom_ext fun k ↦ by simp [TopCat.ofHom_comp]

/-- The induced map `T₁.Union ⟶ T₂.Union` of a cellular tower morphism is cellular. -/
theorem isCellular_unionMap (φ : T₁.Hom T₂) :
    IsCellular (univ : Set T₁.Union) (univ : Set T₂.Union)
      (TopCat.ofHom (φ.unionMap.hom.restrictPreimage univ)) := by
  rw [T₁.instCWComplexUnion_eq, T₂.instCWComplexUnion_eq, φ.unionMap_eq_mapOfIsColimit]
  exact φ.isCellular_mapOfIsColimit (colimit.isColimit T₁.diagram) (colimit.isColimit T₂.diagram)

/-- On every skeleton, `φ.unionMap` commutes with stage skeletal restrictions. -/
@[reassoc] theorem skeletonMap_incl_comp (φ : T₁.Hom T₂) (k n : ℕ) :
    skeletonMap _ _ (T₁.isCellular_incl k) n ≫ skeletonMap _ _ φ.isCellular_unionMap n =
      skeletonMap _ _ (φ.isCellular_app k) n ≫ skeletonMap _ _ (T₂.isCellular_incl k) n :=
  skeletonMap_univ_comm _ _ _ _ (φ.unionMap_incl_apply k) n

end Hom

end TauCeti.CWSubcomplexTower
