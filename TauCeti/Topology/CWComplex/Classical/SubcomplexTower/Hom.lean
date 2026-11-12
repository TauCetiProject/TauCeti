/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Map
public import TauCeti.Topology.CWComplex.Classical.SubcomplexTower.Colimit

/-!
# Cellular morphisms and examples of CW subcomplex towers

For a sequential tower `T : TauCeti.CWSubcomplexTower W newCell`, every stage map `T.step k` and
colimit inclusion `c.ι.app k` / `T.incl k` is cellular (`isCellular_step`, `isCellular_ι`,
`isCellular_incl`). Stagewise cellular morphisms between towers (`TauCeti.CWSubcomplexTower.Hom`)
induce cellular maps on colimits (`Hom.isCellular_mapOfIsColimit`, `Hom.isCellular_unionMap`) whose
skeletal restrictions commute with stage inclusions (`Hom.skeletonMap_incl_comp`).

This file also provides two concrete families of towers: the constant tower `const X` on a single
Hausdorff CW complex `X` (whose union is homeomorphic to `X` via `constUnionHomeomorph`), and the
two-stage stabilizing tower `pair` associated to a single closed CW subcomplex embedding `W₀ → W₁`
whose stage-`1` cells may have dimensions smaller than cells already present in `W₀`.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti.CWSubcomplexTower

/-! ### Cellularity of stage maps and cellular naturality -/

section CellularNaturality

section SingleTower

variable {W : ℕ → Type u}
  [∀ k, TopologicalSpace (W k)] [∀ k, T2Space (W k)] [∀ k, CWComplex (univ : Set (W k))]
  {newCell : ℕ → ℕ → Type u} (T : CWSubcomplexTower W newCell)

/-- Each stage inclusion `T.step k : W k → W (k + 1)` is cellular. -/
theorem isCellular_step (k : ℕ) :
    IsCellular (univ : Set (W k)) (univ : Set (W (k + 1)))
      (TopCat.ofHom ((T.step k).restrictPreimage univ)) := by
  refine isCellular_of_map_eq _ _ (fun _ h ↦ False.elim h) fun n i ↦ ?_
  refine ⟨(T.oldCellEquiv k n i : cell (univ : Set (W (k + 1))) n), fun x hx _ ↦ ?_⟩
  exact T.map_oldCell k n i hx

/-- For any colimit cocone `c` of `T.diagram`, each stage inclusion `c.ι.app k : W k → c.pt` is
cellular. -/
theorem isCellular_ι {c : Cocone T.diagram} (hc : IsColimit c) (k : ℕ) :
    letI := T.cwComplexOfIsColimit hc
    letI := T.t2Space_of_isColimit hc
    IsCellular (univ : Set (W k)) (univ : Set c.pt)
      (TopCat.ofHom ((c.ι.app k).hom.restrictPreimage univ)) := by
  let _ := T.cwComplexOfIsColimit hc
  let _ := T.t2Space_of_isColimit hc
  refine isCellular_of_map_eq _ _ (fun _ h ↦ False.elim h) fun n i ↦ ?_
  let q := (T.stageCellEquiv k n).symm i
  have hiq : T.stageCellEquiv k n q = i := (T.stageCellEquiv k n).apply_symm_apply i
  refine ⟨(T.cwComplexOfIsColimitCellEquiv hc n).symm q.1, fun x hx _ ↦ ?_⟩
  exact (congrArg (fun j ↦ c.ι.app k (map (C := (univ : Set (W k))) n j x)) hiq).symm.trans
    (T.map_eq_ι_stageCellEquiv hc n q.1 q.2 hx).symm

/-- Each stage inclusion `T.incl k : W k → T.Union` is cellular. -/
theorem isCellular_incl (k : ℕ) :
    IsCellular (univ : Set (W k)) (univ : Set T.Union)
      (TopCat.ofHom ((T.incl k).hom.restrictPreimage univ)) := by
  rw [T.instCWComplexUnion_eq]
  exact T.isCellular_ι (colimit.isColimit T.diagram) k

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

section Basic

variable {W₁ W₂ W₃ : ℕ → Type u}
  [∀ k, TopologicalSpace (W₁ k)] [∀ k, T2Space (W₁ k)] [∀ k, CWComplex (univ : Set (W₁ k))]
  [∀ k, TopologicalSpace (W₂ k)] [∀ k, T2Space (W₂ k)] [∀ k, CWComplex (univ : Set (W₂ k))]
  [∀ k, TopologicalSpace (W₃ k)] [∀ k, T2Space (W₃ k)] [∀ k, CWComplex (univ : Set (W₃ k))]
  {newCell₁ newCell₂ newCell₃ : ℕ → ℕ → Type u}
  {T₁ : CWSubcomplexTower W₁ newCell₁} {T₂ : CWSubcomplexTower W₂ newCell₂}
  {T₃ : CWSubcomplexTower W₃ newCell₃}

@[ext]
theorem ext {φ ψ : T₁.Hom T₂} (h : ∀ k, φ.app k = ψ.app k) : φ = ψ := by
  cases φ
  cases ψ
  congr
  exact funext h

/-- The identity cellular morphism on a `CWSubcomplexTower`. -/
def id (T₁ : CWSubcomplexTower W₁ newCell₁) : T₁.Hom T₁ where
  app k := ContinuousMap.id (W₁ k)
  comm _ := rfl
  isCellular_app _ _ _ hx := hx

@[simp]
lemma id_app (T₁ : CWSubcomplexTower W₁ newCell₁) (k : ℕ) :
    (Hom.id T₁).app k = ContinuousMap.id (W₁ k) :=
  (rfl)

/-- Composition of cellular morphisms of `CWSubcomplexTower`s. -/
def comp (φ : T₁.Hom T₂) (ψ : T₂.Hom T₃) : T₁.Hom T₃ where
  app k := (ψ.app k).comp (φ.app k)
  comm k := by
    ext x
    have h₁ := ContinuousMap.congr_fun (φ.comm k) x
    have h₂ := ContinuousMap.congr_fun (ψ.comm k) (φ.app k x)
    exact (congrArg (ψ.app (k + 1)) h₁).trans h₂
  isCellular_app k n _ hx := ψ.isCellular_app k n (φ.isCellular_app k n hx)

@[simp]
lemma comp_app (φ : T₁.Hom T₂) (ψ : T₂.Hom T₃) (k : ℕ) :
    (φ.comp ψ).app k = (ψ.app k).comp (φ.app k) :=
  (rfl)

/-- The natural transformation `T₁.diagram ⟶ T₂.diagram` induced by `φ : T₁.Hom T₂`. -/
def natTrans (φ : T₁.Hom T₂) : T₁.diagram ⟶ T₂.diagram :=
  NatTrans.ofSequence (fun k ↦ TopCat.ofHom (φ.app k)) fun k ↦ by
    rw [T₁.diagram_map_succ, T₂.diagram_map_succ]
    ext x
    exact ContinuousMap.congr_fun (φ.comm k) x

@[simp]
lemma natTrans_app (φ : T₁.Hom T₂) (k : ℕ) :
    φ.natTrans.app k = TopCat.ofHom (φ.app k) :=
  (rfl)

/-- The induced continuous map `c₁.pt ⟶ c₂.pt` between any colimit cocones of `T₁` and `T₂`. -/
def mapOfIsColimit (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) : c₁.pt ⟶ c₂.pt :=
  hc₁.desc ⟨c₂.pt, φ.natTrans ≫ c₂.ι⟩

@[simp, reassoc]
lemma ι_comp_mapOfIsColimit (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) (k : ℕ) :
    c₁.ι.app k ≫ φ.mapOfIsColimit hc₁ = TopCat.ofHom (φ.app k) ≫ c₂.ι.app k :=
  hc₁.fac ⟨c₂.pt, φ.natTrans ≫ c₂.ι⟩ k

lemma mapOfIsColimit_ι_apply (φ : T₁.Hom T₂) {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) (k : ℕ) (x : W₁ k) :
    φ.mapOfIsColimit hc₁ (c₁.ι.app k x) = c₂.ι.app k (φ.app k x) := by
  rw [← ConcreteCategory.comp_apply, φ.ι_comp_mapOfIsColimit hc₁ k, ConcreteCategory.comp_apply]
  rfl

/-- **Cellular naturality:** the map induced on colimits by a cellular tower morphism is
cellular. -/
theorem isCellular_mapOfIsColimit (φ : T₁.Hom T₂)
    {c₁ : Cocone T₁.diagram} {c₂ : Cocone T₂.diagram}
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    letI := T₁.cwComplexOfIsColimit hc₁
    letI := T₁.t2Space_of_isColimit hc₁
    letI := T₂.cwComplexOfIsColimit hc₂
    letI := T₂.t2Space_of_isColimit hc₂
    IsCellular (univ : Set c₁.pt) (univ : Set c₂.pt)
      (TopCat.ofHom ((φ.mapOfIsColimit (c₂ := c₂) hc₁).hom.restrictPreimage univ)) := by
  let _ := T₁.cwComplexOfIsColimit hc₁
  let _ := T₁.t2Space_of_isColimit hc₁
  let _ := T₂.cwComplexOfIsColimit hc₂
  let _ := T₂.t2Space_of_isColimit hc₂
  rintro n ⟨z, -⟩ (hz : z ∈ skeletonLT (univ : Set c₁.pt) (n : ℕ∞))
  rw [RelCWComplex.mem_skeletonLT_iff] at hz
  rcases hz with hzEmpty | ⟨m, hmn, i, hzi⟩
  · exact False.elim hzEmpty
  · obtain ⟨p, rfl⟩ := (T₁.cwComplexOfIsColimitCellEquiv hc₁ m).symm.surjective i
    rw [T₁.openCell_cwComplexOfIsColimitCellEquiv_symm hc₁] at hzi
    obtain ⟨y, hy, rfl⟩ := hzi
    have hy_skel : (⟨y, mem_univ y⟩ : (univ : Set (W₁ p.1))) ∈
        {x | x.1 ∈ skeletonLT (univ : Set (W₁ p.1)) (n : ℕ∞)} :=
      RelCWComplex.mem_skeletonLT_iff.2 (Or.inr ⟨m, hmn, T₁.birthCell p.1 m p.2, hy⟩)
    have hι_skel := T₂.isCellular_ι hc₂ p.1 n (φ.isCellular_app p.1 n hy_skel)
    -- `Set.MapsTo` reduces subtype membership in `{y : univ | y.1 ∈ skeletonLT _ _}` to the
    -- ambient point of `c₂.pt`.
    change φ.mapOfIsColimit (c₂ := c₂) hc₁ (c₁.ι.app p.1 y) ∈ skeletonLT (univ : Set c₂.pt) (n : ℕ∞)
    rw [φ.mapOfIsColimit_ι_apply hc₁]
    exact hι_skel

/-- The induced continuous map `T₁.Union ⟶ T₂.Union` between canonical tower unions. -/
def unionMap (φ : T₁.Hom T₂) : T₁.Union ⟶ T₂.Union :=
  φ.mapOfIsColimit (colimit.isColimit T₁.diagram)

@[simp, reassoc]
lemma incl_comp_unionMap (φ : T₁.Hom T₂) (k : ℕ) :
    T₁.incl k ≫ φ.unionMap = TopCat.ofHom (φ.app k) ≫ T₂.incl k :=
  φ.ι_comp_mapOfIsColimit (colimit.isColimit T₁.diagram) k

@[simp]
lemma unionMap_incl_apply (φ : T₁.Hom T₂) (k : ℕ) (x : W₁ k) :
    φ.unionMap (T₁.incl k x) = T₂.incl k (φ.app k x) :=
  φ.mapOfIsColimit_ι_apply (colimit.isColimit T₁.diagram) k x

@[simp]
lemma unionMap_id : (Hom.id T₁).unionMap = 𝟙 T₁.Union :=
  T₁.union_hom_ext fun k ↦ by simp

@[simp, reassoc]
lemma unionMap_comp (φ : T₁.Hom T₂) (ψ : T₂.Hom T₃) :
    (φ.comp ψ).unionMap = φ.unionMap ≫ ψ.unionMap :=
  T₁.union_hom_ext fun k ↦ by simp [TopCat.ofHom_comp, incl_comp_unionMap_assoc]

/-- The induced map `T₁.Union ⟶ T₂.Union` of a cellular tower morphism is cellular. -/
theorem isCellular_unionMap (φ : T₁.Hom T₂) :
    IsCellular (univ : Set T₁.Union) (univ : Set T₂.Union)
      (TopCat.ofHom (φ.unionMap.hom.restrictPreimage univ)) := by
  rw [T₁.instCWComplexUnion_eq, T₂.instCWComplexUnion_eq]
  exact φ.isCellular_mapOfIsColimit (colimit.isColimit T₁.diagram) (colimit.isColimit T₂.diagram)

/-- On every dimension skeleton, the induced map `φ.unionMap` restricts to a map commuting with
stage skeletal restrictions. -/
@[reassoc]
theorem skeletonMap_incl_comp (φ : T₁.Hom T₂) (k n : ℕ) :
    skeletonMap _ _ (T₁.isCellular_incl k) n ≫ skeletonMap _ _ φ.isCellular_unionMap n =
      skeletonMap _ _ (φ.isCellular_app k) n ≫ skeletonMap _ _ (T₂.isCellular_incl k) n := by
  have hcongr :
      ∀ {f₁ f₂ : TopCat.of (univ : Set (W₁ k)) ⟶ TopCat.of (univ : Set T₂.Union)}
        (_ : f₁ = f₂) (hf₁ : IsCellular _ _ f₁) (hf₂ : IsCellular _ _ f₂),
        skeletonMap _ _ hf₁ n = skeletonMap _ _ hf₂ n := by
    rintro _ _ rfl _ _
    rfl
  rw [← skeletonMap_comp, ← skeletonMap_comp]
  exact hcongr (by ext x; exact φ.unionMap_incl_apply k x.1) _ _

end Basic

end Hom

end CellularNaturality

/-! ### Stabilizing and two-stage towers -/

section Examples

/-- The constant `CWSubcomplexTower` on a Hausdorff classical CW complex `X`, where stage `0` has
all cells of `X` and stages `k + 1` attach no new cells (`PEmpty`). -/
def const (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)] :
    CWSubcomplexTower (fun _ ↦ X) (fun k n ↦ match k with
      | 0 => cell (univ : Set X) n
      | _ + 1 => PEmpty) :=
  ofCellSum
    (fun _ ↦ ContinuousMap.id X)
    (fun _ ↦ IsClosedEmbedding.id)
    (fun _ ↦ Equiv.refl _)
    (fun _ _ ↦ Equiv.sumEmpty _ _)
    (fun _ _ _ {_} _ ↦ rfl)

@[simp]
lemma const_step (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    (k : ℕ) : (const X).step k = ContinuousMap.id X := by
  unfold const
  exact ofCellSum_step _ _ _ _ _ k

/-- The union of the constant tower `CWSubcomplexTower.const X` is homeomorphic to `X`. -/
def constUnionHomeomorph (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)] :
    (const X).Union ≃ₜ X :=
  let T := const X
  let cX : Cocone T.diagram :=
    { pt := TopCat.of X
      ι := NatTrans.ofSequence (fun _ ↦ 𝟙 (TopCat.of X)) fun k ↦ by
        rw [T.diagram_map_succ, const_step]
        rfl }
  let hcX : IsColimit cX :=
    { desc := fun s ↦ s.ι.app 0
      fac := fun s k ↦ by
        dsimp only [cX]
        rw [NatTrans.ofSequence_app, Category.id_comp]
        induction k with
        | zero => rfl
        | succ k ih =>
          have hw := s.w (homOfLE (Nat.le_add_right k 1))
          rw [T.diagram_map_succ, const_step] at hw
          have hid : TopCat.ofHom (ContinuousMap.id X) = 𝟙 (TopCat.of X) := by ext x; rfl
          rw [hid, Category.id_comp] at hw
          exact ih.trans hw.symm
      uniq := fun s m hm ↦ by
        have hm0 := hm 0
        dsimp only [cX] at hm0
        rwa [NatTrans.ofSequence_app, Category.id_comp] at hm0 }
  TopCat.homeoOfIso (colimit.isoColimitCocone ⟨cX, hcX⟩)

/-- A two-stage-then-stabilizing `CWSubcomplexTower` built from a single closed CW subcomplex
embedding `f : C(W₀, W₁)`: stage `0` has the cells of `W₀`, stage `1` attaches the complementary
cells `new₁` of `W₁` (which may have **strictly smaller** dimensions than cells of `W₀`), and all
higher stages `k + 2` stabilize at `W₁` with no further cells. -/
def pair {W₀ W₁ : Type u}
    [TopologicalSpace W₀] [T2Space W₀] [CWComplex (univ : Set W₀)]
    [TopologicalSpace W₁] [T2Space W₁] [CWComplex (univ : Set W₁)]
    {new₁ : ℕ → Type u}
    (f : C(W₀, W₁)) (hf : IsClosedEmbedding f)
    (cellSum : ∀ n, cell (univ : Set W₀) n ⊕ new₁ n ≃ cell (univ : Set W₁) n)
    (hmap : ∀ n (i : cell (univ : Set W₀) n) {x : Fin n → ℝ},
      x ∈ closedBall 0 1 →
      f (map (C := (univ : Set W₀)) n i x) =
        map (C := (univ : Set W₁)) n (cellSum n (Sum.inl i)) x) :
    let W : ℕ → Type u := fun
      | 0 => W₀
      | _ + 1 => W₁
    letI : ∀ k, TopologicalSpace (W k) := fun
      | 0 => inferInstance
      | _ + 1 => inferInstance
    letI : ∀ k, T2Space (W k) := fun
      | 0 => inferInstance
      | _ + 1 => inferInstance
    letI : ∀ k, CWComplex (univ : Set (W k)) := fun
      | 0 => inferInstance
      | _ + 1 => inferInstance
    CWSubcomplexTower W (fun k n ↦ match k with
      | 0 => cell (univ : Set W₀) n
      | 1 => new₁ n
      | _ + 2 => PEmpty) :=
  let W : ℕ → Type u := fun
    | 0 => W₀
    | _ + 1 => W₁
  letI : ∀ k, TopologicalSpace (W k) := fun
    | 0 => inferInstance
    | _ + 1 => inferInstance
  letI : ∀ k, T2Space (W k) := fun
    | 0 => inferInstance
    | _ + 1 => inferInstance
  letI : ∀ k, CWComplex (univ : Set (W k)) := fun
    | 0 => inferInstance
    | _ + 1 => inferInstance
  ofCellSum (W := W)
    (fun
      | 0 => f
      | _ + 1 => ContinuousMap.id W₁)
    (fun
      | 0 => hf
      | _ + 1 => IsClosedEmbedding.id)
    (fun _ ↦ Equiv.refl _)
    (fun
      | 0, n => cellSum n
      | _ + 1, _ => Equiv.sumEmpty _ _)
    (fun k n i {_} hx ↦ by
      cases k with
      | zero => exact hmap n i hx
      | succ _ => exact rfl)

end Examples

end TauCeti.CWSubcomplexTower
