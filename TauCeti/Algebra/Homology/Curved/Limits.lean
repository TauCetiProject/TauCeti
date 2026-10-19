/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Duplex
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Limits and colimits of curved duplexes

Limits and colimits of curved duplexes are computed componentwise. If a diagram
`F : J ⥤ CurvedDuplex C w` has a limit after evaluation at both components, then the two
componentwise limits, with the differentials induced by those of the duplexes in the diagram,
form a curved duplex of curvature `w`, and this is a limit of `F` preserved by both evaluation
functors. The same holds for colimits.

The curvature equations of the componentwise limit hold because the curvature acts through the
linear structure, hence commutes with the limit projections. No limits are assumed in `C`; this is
what lets an exact structure on `C` induce a componentwise exact structure on curved duplexes,
whose kernels, cokernels, pushouts and pullbacks exist only for the diagrams the axioms need.

The construction follows Joël Riou's `Mathlib.Algebra.Homology.HomologicalComplexLimits` for
homological complexes.

## Main definitions

* `TauCeti.CurvedDuplex.d₀NatTrans` and `TauCeti.CurvedDuplex.d₁NatTrans`: the differentials as
  natural transformations between the evaluation functors.
* `TauCeti.CurvedDuplex.isLimitOfEval` and `TauCeti.CurvedDuplex.isColimitOfEval`: a cone
  (resp. cocone) whose evaluations at both components are limits (resp. colimits) is a limit
  (resp. colimit).
* `TauCeti.CurvedDuplex.coneOfHasLimitEval` and `TauCeti.CurvedDuplex.coconeOfHasColimitEval`:
  the componentwise limit cone and colimit cocone.

## Main results

* The instances `HasLimit F` and `HasColimit F` when the evaluated diagrams have limits
  (resp. colimits), with `PreservesLimit F (eval₀ C w)` and its variants for the other
  evaluation functor and for colimits.
* `TauCeti.CurvedDuplex.hasColimit_span_comp_eval₀` and
  `TauCeti.CurvedDuplex.hasLimit_cospan_comp_eval₀`, with their odd variants: a span (resp.
  cospan) of curved duplexes with a pushout (resp. pullback) in a component has a colimit
  (resp. limit) after evaluation at that component.
-/

public section

universe w' v u v' u'

namespace TauCeti.CurvedDuplex

open CategoryTheory Category Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type w'} [Semiring R] [Linear R C]
  {w : R} {J : Type u'} [Category.{v'} J] (F : J ⥤ CurvedDuplex C w)

-- The objects of an evaluated diagram `F ⋙ eval₀ C w` are the even components of the duplexes of
-- `F` only up to unfolding `eval₀`, which `rw` and `simp` do not see through. The proofs below
-- therefore state the relevant equations with explicit component types and close them with
-- `exact`, or use the natural transformations `d₀NatTrans` and `d₁NatTrans` to name the induced
-- differentials.

variable (C w) in
/-- The even differentials of curved duplexes, as a natural transformation between the
evaluation functors. -/
def d₀NatTrans : eval₀ C w ⟶ eval₁ C w where
  app X := X.d₀
  naturality _ _ f := f.comm₀

/-- The components of `d₀NatTrans` are the even differentials. -/
@[simp]
theorem d₀NatTrans_app (X : CurvedDuplex C w) : (d₀NatTrans C w).app X = X.d₀ := (rfl)

variable (C w) in
/-- The odd differentials of curved duplexes, as a natural transformation between the
evaluation functors. -/
def d₁NatTrans : eval₁ C w ⟶ eval₀ C w where
  app X := X.d₁
  naturality _ _ f := f.comm₁

/-- The components of `d₁NatTrans` are the odd differentials. -/
@[simp]
theorem d₁NatTrans_app (X : CurvedDuplex C w) : (d₁NatTrans C w).app X = X.d₁ := (rfl)

/-! ### Limits -/

/-- A cone of curved duplexes is a limit if its evaluations at the even and the odd components
are limits. -/
def isLimitOfEval (s : Cone F) (h₀ : IsLimit ((eval₀ C w).mapCone s))
    (h₁ : IsLimit ((eval₁ C w).mapCone s)) : IsLimit s where
  lift t :=
    -- The componentwise lifts, with their types stated in terms of the components.
    let l₀ : t.pt.X₀ ⟶ s.pt.X₀ := h₀.lift ((eval₀ C w).mapCone t)
    let l₁ : t.pt.X₁ ⟶ s.pt.X₁ := h₁.lift ((eval₁ C w).mapCone t)
    have e₀ (j : J) : l₀ ≫ (s.π.app j).f₀ = (t.π.app j).f₀ := h₀.fac ((eval₀ C w).mapCone t) j
    have e₁ (j : J) : l₁ ≫ (s.π.app j).f₁ = (t.π.app j).f₁ := h₁.fac ((eval₁ C w).mapCone t) j
    { f₀ := l₀
      f₁ := l₁
      comm₀ := h₁.hom_ext fun j ↦
        (by rw [assoc, assoc, e₁, ← Hom.comm₀, reassoc_of% e₀]; exact (t.π.app j).comm₀ :
          (l₀ ≫ s.pt.d₀) ≫ (s.π.app j).f₁ = (t.pt.d₀ ≫ l₁) ≫ (s.π.app j).f₁)
      comm₁ := h₀.hom_ext fun j ↦
        (by rw [assoc, assoc, e₀, ← Hom.comm₁, reassoc_of% e₁]; exact (t.π.app j).comm₁ :
          (l₁ ≫ s.pt.d₁) ≫ (s.π.app j).f₀ = (t.pt.d₁ ≫ l₀) ≫ (s.π.app j).f₀) }
  fac t j := by
    ext
    · exact h₀.fac ((eval₀ C w).mapCone t) j
    · exact h₁.fac ((eval₁ C w).mapCone t) j
  uniq t m hm := by
    ext
    · exact h₀.uniq ((eval₀ C w).mapCone t) _ fun j ↦ congrArg Hom.f₀ (hm j)
    · exact h₁.uniq ((eval₁ C w).mapCone t) _ fun j ↦ congrArg Hom.f₁ (hm j)

variable [HasLimit (F ⋙ eval₀ C w)] [HasLimit (F ⋙ eval₁ C w)]

/-- The componentwise limit of a diagram of curved duplexes, with the differentials induced by
the differentials of the duplexes in the diagram. -/
-- Exposed so that its evaluations unfold to the limit cones of the evaluated diagrams, which
-- also lets its `simps` lemmas be exported.
@[expose, simps]
noncomputable def coneOfHasLimitEval : Cone F where
  pt :=
    { X₀ := limit (F ⋙ eval₀ C w)
      X₁ := limit (F ⋙ eval₁ C w)
      d₀ := limMap (Functor.whiskerLeft F (d₀NatTrans C w))
      d₁ := limMap (Functor.whiskerLeft F (d₁NatTrans C w))
      d₀_comp_d₁ := limit.hom_ext fun j ↦ by
        rw [assoc, limMap_π, limMap_π_assoc, Linear.smul_comp, id_comp]
        exact (congrArg (limit.π (F ⋙ eval₀ C w) j ≫ ·) (F.obj j).d₀_comp_d₁).trans
          ((Linear.comp_smul _ _ _ _ _ _).trans (congrArg (w • ·) (comp_id _)))
      d₁_comp_d₀ := limit.hom_ext fun j ↦ by
        rw [assoc, limMap_π, limMap_π_assoc, Linear.smul_comp, id_comp]
        exact (congrArg (limit.π (F ⋙ eval₁ C w) j ≫ ·) (F.obj j).d₁_comp_d₀).trans
          ((Linear.comp_smul _ _ _ _ _ _).trans (congrArg (w • ·) (comp_id _))) }
  π :=
    { app j :=
        { f₀ := limit.π (F ⋙ eval₀ C w) j
          f₁ := limit.π (F ⋙ eval₁ C w) j
          comm₀ := ((limMap_π (Functor.whiskerLeft F (d₀NatTrans C w)) j).trans
              (congrArg (_ ≫ ·) (d₀NatTrans_app _))).symm
          comm₁ := ((limMap_π (Functor.whiskerLeft F (d₁NatTrans C w)) j).trans
              (congrArg (_ ≫ ·) (d₁NatTrans_app _))).symm }
      naturality i j φ := hom_ext ((id_comp _).trans (limit.w (F ⋙ eval₀ C w) φ).symm)
        ((id_comp _).trans (limit.w (F ⋙ eval₁ C w) φ).symm) }

/-- The even component of the componentwise limit cone is a limit. -/
noncomputable def isLimitEval₀ConeOfHasLimitEval :
    IsLimit ((eval₀ C w).mapCone (coneOfHasLimitEval F)) :=
  (limit.isLimit (F ⋙ eval₀ C w)).ofIsoLimit (Cone.ext (Iso.refl _) fun _ ↦ (id_comp _).symm)

/-- The odd component of the componentwise limit cone is a limit. -/
noncomputable def isLimitEval₁ConeOfHasLimitEval :
    IsLimit ((eval₁ C w).mapCone (coneOfHasLimitEval F)) :=
  (limit.isLimit (F ⋙ eval₁ C w)).ofIsoLimit (Cone.ext (Iso.refl _) fun _ ↦ (id_comp _).symm)

/-- The componentwise limit cone is a limit. -/
noncomputable def isLimitConeOfHasLimitEval : IsLimit (coneOfHasLimitEval F) :=
  isLimitOfEval _ _ (isLimitEval₀ConeOfHasLimitEval F) (isLimitEval₁ConeOfHasLimitEval F)

instance : HasLimit F :=
  ⟨⟨⟨_, isLimitConeOfHasLimitEval F⟩⟩⟩

noncomputable instance : PreservesLimit F (eval₀ C w) :=
  preservesLimit_of_preserves_limit_cone (isLimitConeOfHasLimitEval F)
    (isLimitEval₀ConeOfHasLimitEval F)

noncomputable instance : PreservesLimit F (eval₁ C w) :=
  preservesLimit_of_preserves_limit_cone (isLimitConeOfHasLimitEval F)
    (isLimitEval₁ConeOfHasLimitEval F)

/-! ### Colimits -/

/-- A cocone of curved duplexes is a colimit if its evaluations at the even and the odd
components are colimits. -/
def isColimitOfEval (s : Cocone F) (h₀ : IsColimit ((eval₀ C w).mapCocone s))
    (h₁ : IsColimit ((eval₁ C w).mapCocone s)) : IsColimit s where
  desc t :=
    -- The componentwise descents, with their types stated in terms of the components.
    let l₀ : s.pt.X₀ ⟶ t.pt.X₀ := h₀.desc ((eval₀ C w).mapCocone t)
    let l₁ : s.pt.X₁ ⟶ t.pt.X₁ := h₁.desc ((eval₁ C w).mapCocone t)
    have e₀ (j : J) : (s.ι.app j).f₀ ≫ l₀ = (t.ι.app j).f₀ :=
      h₀.fac ((eval₀ C w).mapCocone t) j
    have e₁ (j : J) : (s.ι.app j).f₁ ≫ l₁ = (t.ι.app j).f₁ :=
      h₁.fac ((eval₁ C w).mapCocone t) j
    { f₀ := l₀
      f₁ := l₁
      comm₀ := h₀.hom_ext fun j ↦
        (by
          rw [reassoc_of% e₀]
          refine (t.ι.app j).comm₀.trans ?_
          rw [← e₁]
          exact ((s.ι.app j).comm₀_assoc l₁).symm :
          (s.ι.app j).f₀ ≫ l₀ ≫ t.pt.d₀ = (s.ι.app j).f₀ ≫ s.pt.d₀ ≫ l₁)
      comm₁ := h₁.hom_ext fun j ↦
        (by
          rw [reassoc_of% e₁]
          refine (t.ι.app j).comm₁.trans ?_
          rw [← e₀]
          exact ((s.ι.app j).comm₁_assoc l₀).symm :
          (s.ι.app j).f₁ ≫ l₁ ≫ t.pt.d₁ = (s.ι.app j).f₁ ≫ s.pt.d₁ ≫ l₀) }
  fac t j := by
    ext
    · exact h₀.fac ((eval₀ C w).mapCocone t) j
    · exact h₁.fac ((eval₁ C w).mapCocone t) j
  uniq t m hm := by
    ext
    · exact h₀.uniq ((eval₀ C w).mapCocone t) _ fun j ↦ congrArg Hom.f₀ (hm j)
    · exact h₁.uniq ((eval₁ C w).mapCocone t) _ fun j ↦ congrArg Hom.f₁ (hm j)

variable [HasColimit (F ⋙ eval₀ C w)] [HasColimit (F ⋙ eval₁ C w)]

/-- The componentwise colimit of a diagram of curved duplexes, with the differentials induced by
the differentials of the duplexes in the diagram. -/
-- Exposed so that its evaluations unfold to the colimit cocones of the evaluated diagrams, which
-- also lets its `simps` lemmas be exported.
@[expose, simps]
noncomputable def coconeOfHasColimitEval : Cocone F where
  pt :=
    { X₀ := colimit (F ⋙ eval₀ C w)
      X₁ := colimit (F ⋙ eval₁ C w)
      d₀ := colimMap (Functor.whiskerLeft F (d₀NatTrans C w))
      d₁ := colimMap (Functor.whiskerLeft F (d₁NatTrans C w))
      d₀_comp_d₁ := colimit.hom_ext fun j ↦ by
        simp only [ι_colimMap_assoc, ι_colimMap, Linear.comp_smul, comp_id]
        exact ((F.obj j).d₀_comp_d₁_assoc _).trans
          ((Linear.smul_comp _ _ _ _ _ _).trans (congrArg (w • ·) (id_comp _)))
      d₁_comp_d₀ := colimit.hom_ext fun j ↦ by
        simp only [ι_colimMap_assoc, ι_colimMap, Linear.comp_smul, comp_id]
        exact ((F.obj j).d₁_comp_d₀_assoc _).trans
          ((Linear.smul_comp _ _ _ _ _ _).trans (congrArg (w • ·) (id_comp _))) }
  ι :=
    { app j :=
        { f₀ := colimit.ι (F ⋙ eval₀ C w) j
          f₁ := colimit.ι (F ⋙ eval₁ C w) j
          comm₀ := (ι_colimMap (Functor.whiskerLeft F (d₀NatTrans C w)) j).trans
              (congrArg (· ≫ _) (d₀NatTrans_app _))
          comm₁ := (ι_colimMap (Functor.whiskerLeft F (d₁NatTrans C w)) j).trans
              (congrArg (· ≫ _) (d₁NatTrans_app _)) }
      naturality i j φ := hom_ext ((colimit.w (F ⋙ eval₀ C w) φ).trans (comp_id _).symm)
        ((colimit.w (F ⋙ eval₁ C w) φ).trans (comp_id _).symm) }

/-- The even component of the componentwise colimit cocone is a colimit. -/
noncomputable def isColimitEval₀CoconeOfHasColimitEval :
    IsColimit ((eval₀ C w).mapCocone (coconeOfHasColimitEval F)) :=
  (colimit.isColimit (F ⋙ eval₀ C w)).ofIsoColimit (Cocone.ext (Iso.refl _) fun _ ↦ comp_id _)

/-- The odd component of the componentwise colimit cocone is a colimit. -/
noncomputable def isColimitEval₁CoconeOfHasColimitEval :
    IsColimit ((eval₁ C w).mapCocone (coconeOfHasColimitEval F)) :=
  (colimit.isColimit (F ⋙ eval₁ C w)).ofIsoColimit (Cocone.ext (Iso.refl _) fun _ ↦ comp_id _)

/-- The componentwise colimit cocone is a colimit. -/
noncomputable def isColimitCoconeOfHasColimitEval : IsColimit (coconeOfHasColimitEval F) :=
  isColimitOfEval _ _ (isColimitEval₀CoconeOfHasColimitEval F)
    (isColimitEval₁CoconeOfHasColimitEval F)

instance : HasColimit F :=
  ⟨⟨⟨_, isColimitCoconeOfHasColimitEval F⟩⟩⟩

noncomputable instance : PreservesColimit F (eval₀ C w) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCoconeOfHasColimitEval F)
    (isColimitEval₀CoconeOfHasColimitEval F)

noncomputable instance : PreservesColimit F (eval₁ C w) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCoconeOfHasColimitEval F)
    (isColimitEval₁CoconeOfHasColimitEval F)

/-! ### Pushouts and pullbacks -/

section PushoutPullback

variable {X Y Z : CurvedDuplex C w}

/-- If a span of curved duplexes has a pushout in the even component, then its composite with
the even evaluation functor has a colimit. -/
theorem hasColimit_span_comp_eval₀ {f : X ⟶ Y} {g : X ⟶ Z}
    [HasPushout f.f₀ g.f₀] : HasColimit (span f g ⋙ eval₀ C w) :=
  hasColimit_of_iso (F := span f.f₀ g.f₀) (spanCompIso (eval₀ C w) f g)

/-- If a span of curved duplexes has a pushout in the odd component, then its composite with
the odd evaluation functor has a colimit. -/
theorem hasColimit_span_comp_eval₁ {f : X ⟶ Y} {g : X ⟶ Z}
    [HasPushout f.f₁ g.f₁] : HasColimit (span f g ⋙ eval₁ C w) :=
  hasColimit_of_iso (F := span f.f₁ g.f₁) (spanCompIso (eval₁ C w) f g)

/-- If a cospan of curved duplexes has a pullback in the even component, then its composite
with the even evaluation functor has a limit. -/
theorem hasLimit_cospan_comp_eval₀ {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f.f₀ g.f₀] : HasLimit (cospan f g ⋙ eval₀ C w) :=
  hasLimit_of_iso (F := cospan f.f₀ g.f₀) (cospanCompIso (eval₀ C w) f g).symm

/-- If a cospan of curved duplexes has a pullback in the odd component, then its composite with
the odd evaluation functor has a limit. -/
theorem hasLimit_cospan_comp_eval₁ {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f.f₁ g.f₁] : HasLimit (cospan f g ⋙ eval₁ C w) :=
  hasLimit_of_iso (F := cospan f.f₁ g.f₁) (cospanCompIso (eval₁ C w) f g).symm

end PushoutPullback

end TauCeti.CurvedDuplex
