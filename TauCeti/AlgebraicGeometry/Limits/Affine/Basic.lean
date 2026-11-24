/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Category.Ring.Colimits
import TauCeti.Order.Interval.Set.Directed

/-!
# Limits of affine schemes and colimits of global sections

The comparison between an arbitrary affine limit cone and the spectrum of the
colimit of global sections respects every component. Sections of the pullbacks of one
affine open in an affine-transition inverse limit give a directed ring system; its colimit
is the ring of sections on the corresponding limit open.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Functor

/-- The limit of any diagram of affine schemes is the spectrum of the colimit
of its rings of global sections, compatibly with every cone projection. -/
theorem exists_isoSpec_colimit_of_isLimit
    {J : Type u} [Category.{u} J] (E : Jᵒᵖ ⥤ Scheme.{u})
    [∀ j, IsAffine (E.obj j)] (c : Cone E) (hc : IsLimit c) :
    ∃ e : c.pt ≅ Spec (colimit (E.rightOp ⋙ Scheme.Γ)), ∀ j : J,
      c.π.app (op j) ≫ (E.obj (op j)).isoSpec.hom =
        e.hom ≫ Spec.map (colimit.ι (E.rightOp ⋙ Scheme.Γ) j) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have (j : J) : IsAffine (E.rightOp.obj j).unop :=
    inferInstanceAs (IsAffine (E.obj (op j)))
  let F := E.rightOp ⋙ Scheme.Γ
  let hΓ := isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone E hc)
  let eΓ : Γ(c.pt, ⊤) ≅ colimit F :=
    hΓ.coconePointUniqueUpToIso (colimit.isColimit F)
  refine ⟨c.pt.isoSpec ≪≫ Scheme.Spec.mapIso eΓ.symm.op, fun j ↦ ?_⟩
  -- Expose the composite Spec isomorphism to use Spec.map_comp.
  change c.π.app (op j) ≫ (E.obj (op j)).isoSpec.hom =
    (c.pt.isoSpec.hom ≫ Spec.map eΓ.inv) ≫ Spec.map (colimit.ι F j)
  rw [Category.assoc, ← Spec.map_comp]
  have hι := hΓ.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) j
  -- Expose the sections cocone underlying the transported colimit.
  change colimit.ι F j ≫ eΓ.inv = (c.π.app (op j)).appTop at hι
  rw [hι]
  exact (Scheme.isoSpec_hom_naturality (X := c.pt) (Y := E.obj (op j))
    (c.π.app (op j))).symm

end CategoryTheory.Functor

noncomputable section

namespace CategoryTheory.Functor

private def tailOver {I : Type u} [Preorder I] (i₀ : I) :
    {i : I // i₀ ≤ i}ᵒᵖ ⥤ Over (op i₀) where
  obj i := Over.mk (homOfLE i.unop.property).op
  map f := Over.homMk (homOfLE (leOfHom f.unop)).op (Subsingleton.elim _ _)

private theorem tailOver_initial {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (i₀ : I) : (tailOver i₀).Initial := by
  have : Nonempty I := ⟨i₀⟩
  have : Nonempty {i : I // i₀ ≤ i} := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected {i : I // i₀ ≤ i} (· ≤ ·) := inferInstanceAs (IsDirectedOrder (Set.Ici i₀))
  exact Functor.initial_of_exists_of_isCofiltered (tailOver i₀)
    (fun i ↦ ⟨op ⟨i.left.unop, leOfHom i.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (Subsingleton.elim _ _)⟩⟩)
    (fun {_ _} f g ↦ ⟨_, 𝟙 _, by
      apply Over.OverMorphism.ext
      apply Subsingleton.elim⟩)

private theorem tail_opens_comparison
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D) (i₀ : I) (W : (D.obj (op i₀)).Opens) :
    let J := {i : I // i₀ ≤ i}
    let o : J := ⟨i₀, le_rfl⟩
    let K := tailOver i₀
    let E := K ⋙ opensDiagram D (op i₀) W
    let cE := (opensCone D c (op i₀) W).whisker K
    ∃ q : E.obj (op o) ≅ W.toScheme,
      -- The explicit order type selects the tail category, rather than I.
      (∀ i : J, E.map (homOfLE (show o ≤ i from i.property)).op ≫ q.hom =
        (D.map (homOfLE i.property).op).resLE W _ le_rfl) ∧
      cE.π.app (op o) ≫ q.hom = (c.π.app (op i₀)).resLE W _ le_rfl := by
  dsimp only
  let o : {i : I // i₀ ≤ i} := ⟨i₀, le_rfl⟩
  have h₀ : D.map (homOfLE o.property).op ⁻¹ᵁ W = W := by
    have : (homOfLE o.property).op = 𝟙 (op i₀) := Subsingleton.elim _ _
    rw [this, D.map_id]
    rfl
  refine ⟨(D.obj (op i₀)).isoOfEq h₀, ?_, ?_⟩
  · intro i
    -- Expose opensDiagram so restriction composition can be checked after the inclusion.
    change (D.map (homOfLE i.property).op).resLE
      (D.map (homOfLE o.property).op ⁻¹ᵁ W) (D.map (homOfLE i.property).op ⁻¹ᵁ W)
      (by simp [o]) ≫ ((D.obj (op i₀)).isoOfEq h₀).hom =
      (D.map (homOfLE i.property).op).resLE W _ le_rfl
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.resLE_comp_ι]
  -- Expose opensCone so its component can be compared after the inclusion.
  · change (c.π.app (op i₀)).resLE _ _ _ ≫ ((D.obj (op i₀)).isoOfEq h₀).hom = _
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, Scheme.isoOfEq_hom_ι]
    calc
      _ = (c.π.app (op i₀) ⁻¹ᵁ W).ι ≫ c.π.app (op i₀) :=
        Scheme.Hom.resLE_comp_ι _ _
      _ = _ := (Scheme.Hom.resLE_comp_ι _ _).symm

/-- Global sections of pulled-back affine opens give a directed ring-colimit presentation. -/
theorem exists_affineOpen_directedRingSystem
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W) :
    ∃ (F : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
      (e0 : W.toScheme ≅ Spec (F.obj ⟨i₀, le_rfl⟩)),
      (∀ i : {i : I // i₀ ≤ i},
        ∃ e : (D.map (homOfLE i.property).op ⁻¹ᵁ W).toScheme ≅ Spec (F.obj i),
          (D.map (homOfLE i.property).op).resLE W _ le_rfl ≫ e0.hom =
            e.hom ≫ Spec.map (F.map (homOfLE i.property))) ∧
      ∃ eL : (c.π.app (op i₀) ⁻¹ᵁ W).toScheme ≅ Spec (colimit F),
        (c.π.app (op i₀)).resLE W _ le_rfl ≫ e0.hom =
          eL.hom ≫ Spec.map (colimit.ι F ⟨i₀, le_rfl⟩) := by
  classical
  let : Nonempty I := ⟨i₀⟩
  let J := {i : I // i₀ ≤ i}
  let o : J := ⟨i₀, le_rfl⟩
  let : Nonempty J := ⟨o⟩
  let : IsDirected J (· ≤ ·) := inferInstanceAs (IsDirectedOrder (Set.Ici i₀))
  let K : Jᵒᵖ ⥤ Over (op i₀) := tailOver i₀
  let : K.Initial := tailOver_initial i₀
  let E := K ⋙ opensDiagram D (op i₀) W
  let cE : Cone E := (opensCone D c (op i₀) W).whisker K
  have hE : IsLimit cE :=
    (Functor.Initial.isLimitWhiskerEquiv K _).symm (isLimitOpensCone D c hc (op i₀) W)
  let (i : Jᵒᵖ) : IsAffine (E.obj i) := hW.preimage (D.map (homOfLE i.unop.property).op)
  let : IsAffine cE.pt := Scheme.isAffine_of_isLimit cE hE
  let F : J ⥤ CommRingCat := E.rightOp ⋙ Scheme.Γ
  let (i : J) : IsAffine (E.rightOp.obj i).unop := inferInstanceAs (IsAffine (E.obj (op i)))
  obtain ⟨q, hqstage, hqlim⟩ := tail_opens_comparison D c i₀ W
  let e0 : W.toScheme ≅ Spec (F.obj o) := q.symm ≪≫ (E.obj (op o)).isoSpec
  refine ⟨F, e0, ?_, ?_⟩
  · intro i
    refine ⟨(E.obj (op i)).isoSpec, ?_⟩
    -- Expose opensDiagram so restriction composition can be checked after the inclusion.
    change (D.map (homOfLE i.property).op).resLE W _ le_rfl ≫
      (q.inv ≫ (E.obj (op o)).isoSpec.hom) = _
    rw [← hqstage i]
    -- Expose the chosen e0 composite to cancel the comparison isomorphism.
    change (E.map (homOfLE (show o ≤ i from i.property)).op ≫ q.hom) ≫
      (q.inv ≫ (E.obj (op o)).isoSpec.hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.isoSpec_hom_naturality (E.map (homOfLE i.property).op)).symm
  · obtain ⟨eL, heL⟩ := CategoryTheory.Functor.exists_isoSpec_colimit_of_isLimit E cE hE
    refine ⟨eL, ?_⟩
    -- Expose the chosen e0 composite before using the cone comparison.
    change (c.π.app (op i₀)).resLE W _ le_rfl ≫
      (q.inv ≫ (E.obj (op o)).isoSpec.hom) = _
    rw [← hqlim]
    -- Expose e0 after the cone comparison to cancel the comparison isomorphism.
    change (cE.π.app (op o) ≫ q.hom) ≫ (q.inv ≫ (E.obj (op o)).isoSpec.hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact heL o


end CategoryTheory.Functor
