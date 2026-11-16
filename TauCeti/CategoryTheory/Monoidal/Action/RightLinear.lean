/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.Opposites
public import TauCeti.CategoryTheory.Monoidal.Action.LinearFunctor
public import TauCeti.CategoryTheory.Dagger.Basic

/-!
# Right-linear functors through the monoidal opposite

A right action of `C` is a left action of `Cᴹᵒᵖ`, not the left regular action of `C`.
We transport lax, oplax and strong lineators along Mathlib's
`MonoidalLeftAction.monoidalOppositeLeftAction`. Strong structures correspond bijectively,
with the same lineator arrows; in particular this preserves unitary lineators.

Identity and composite right-linear structures, and right-linear natural transformations,
are obtained from the left-linear API. Thus its composition and coherence results are
available for right module categories without a second implementation of their proofs.
-/

public section

namespace CategoryTheory

open MonoidalCategory MonoidalOpposite
open scoped MonoidalLeftAction MonoidalRightAction

variable {C D E H : Type*} [Category* C] [MonoidalCategory C]
  [Category* D] [Category* E] [Category* H]
  [MonoidalRightAction C D] [MonoidalRightAction C E] [MonoidalRightAction C H]

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

namespace Functor

/-- Read lax right lineators as lax left lineators for the monoidal opposite. -/
@[instance_reducible]
def LaxRightLinear.monoidalOpposite (F : D ⥤ E) [F.LaxRightLinear C] :
    F.LaxLeftLinear Cᴹᵒᵖ where
  μₗ c d := LaxRightLinear.μᵣ F d (unmop c)
  μₗ_naturality_left f d := LaxRightLinear.μᵣ_naturality_right F d f.unmop
  μₗ_naturality_right c _ _ f := LaxRightLinear.μᵣ_naturality_left F f (unmop c)
  μₗ_associativity c c' d := LaxRightLinear.μᵣ_associativity F d (unmop c') (unmop c)
  μₗ_unitality d := LaxRightLinear.μᵣ_unitality F d

/-- Read oplax right lineators as oplax left lineators for the monoidal opposite. -/
@[instance_reducible]
def OplaxRightLinear.monoidalOpposite (F : D ⥤ E) [F.OplaxRightLinear C] :
    F.OplaxLeftLinear Cᴹᵒᵖ where
  δₗ c d := OplaxRightLinear.δᵣ F d (unmop c)
  δₗ_naturality_left f d := OplaxRightLinear.δᵣ_naturality_right F d f.unmop
  δₗ_naturality_right c _ _ f := OplaxRightLinear.δᵣ_naturality_left F f (unmop c)
  δₗ_associativity c c' d := OplaxRightLinear.δᵣ_associativity F d (unmop c') (unmop c)
  δₗ_unitality_inv d := OplaxRightLinear.δᵣ_unitality_inv F d

/-- Read a strong right-linear structure as a strong left-linear structure over `Cᴹᵒᵖ`.
This is deliberately not a global instance: both directions of transport are available. -/
@[instance_reducible]
def RightLinear.monoidalOpposite (F : D ⥤ E) [F.RightLinear C] :
    F.LeftLinear Cᴹᵒᵖ where
  toLaxLeftLinear := LaxRightLinear.monoidalOpposite (C := C) F
  toOplaxLeftLinear := OplaxRightLinear.monoidalOpposite (C := C) F
  μₗ_comp_δₗ c d := RightLinear.μᵣ_comp_δᵣ F d (unmop c)
  δₗ_comp_μₗ c d := RightLinear.δᵣ_comp_μᵣ F d (unmop c)

/-- Recover lax right lineators from left lineators for the opposite action. -/
@[instance_reducible]
def LaxRightLinear.ofMonoidalOpposite (F : D ⥤ E) [F.LaxLeftLinear Cᴹᵒᵖ] :
    F.LaxRightLinear C where
  μᵣ d c := LaxLeftLinear.μₗ F (mop c) d
  μᵣ_naturality_right d _ _ f := LaxLeftLinear.μₗ_naturality_left F f.mop d
  μᵣ_naturality_left f c := LaxLeftLinear.μₗ_naturality_right F (mop c) f
  μᵣ_associativity d c c' := LaxLeftLinear.μₗ_associativity F (mop c') (mop c) d
  μᵣ_unitality d := LaxLeftLinear.μₗ_unitality (C := Cᴹᵒᵖ) F d

/-- Recover oplax right lineators from left lineators for the opposite action. -/
@[instance_reducible]
def OplaxRightLinear.ofMonoidalOpposite (F : D ⥤ E) [F.OplaxLeftLinear Cᴹᵒᵖ] :
    F.OplaxRightLinear C where
  δᵣ d c := OplaxLeftLinear.δₗ F (mop c) d
  δᵣ_naturality_right d _ _ f := OplaxLeftLinear.δₗ_naturality_left F f.mop d
  δᵣ_naturality_left f c := OplaxLeftLinear.δₗ_naturality_right F (mop c) f
  δᵣ_associativity d c c' := OplaxLeftLinear.δₗ_associativity F (mop c') (mop c) d
  δᵣ_unitality_inv d := OplaxLeftLinear.δₗ_unitality_inv (C := Cᴹᵒᵖ) F d

/-- Recover a strong right-linear structure from the opposite left action. -/
@[instance_reducible]
def RightLinear.ofMonoidalOpposite (F : D ⥤ E) [F.LeftLinear Cᴹᵒᵖ] :
    F.RightLinear C where
  toLaxRightLinear := LaxRightLinear.ofMonoidalOpposite (C := C) F
  toOplaxRightLinear := OplaxRightLinear.ofMonoidalOpposite (C := C) F
  μᵣ_comp_δᵣ d c := LeftLinear.μₗ_comp_δₗ F (mop c) d
  δᵣ_comp_μᵣ d c := LeftLinear.δₗ_comp_μₗ F (mop c) d

/-- Strong right-linear structures are exactly strong left-linear structures for the
opposite action. Both lineators are retained, and the two transports are inverse. -/
def rightLinearEquivMonoidalOpposite (F : D ⥤ E) :
    F.RightLinear C ≃ F.LeftLinear Cᴹᵒᵖ where
  toFun h := letI := h; RightLinear.monoidalOpposite (C := C) F
  invFun h := letI := h; RightLinear.ofMonoidalOpposite (C := C) F
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport of a lax right lineator only reindexes its arguments. -/
@[simp] theorem LaxRightLinear.monoidalOpposite_μₗ (F : D ⥤ E) [F.LaxRightLinear C]
    (c : Cᴹᵒᵖ) (d : D) :
    letI := LaxRightLinear.monoidalOpposite (C := C) F
    LaxLeftLinear.μₗ F c d = LaxRightLinear.μᵣ F d (unmop c) := (rfl)

/-- Transport of an oplax right lineator only reindexes its arguments. -/
@[simp] theorem OplaxRightLinear.monoidalOpposite_δₗ (F : D ⥤ E) [F.OplaxRightLinear C]
    (c : Cᴹᵒᵖ) (d : D) :
    letI := OplaxRightLinear.monoidalOpposite (C := C) F
    OplaxLeftLinear.δₗ F c d = OplaxRightLinear.δᵣ F d (unmop c) := (rfl)

/-- Recovering a lax right lineator only reindexes its arguments. -/
theorem LaxRightLinear.ofMonoidalOpposite_μᵣ (F : D ⥤ E) [F.LaxLeftLinear Cᴹᵒᵖ]
    (d : D) (c : C) :
    letI := LaxRightLinear.ofMonoidalOpposite (C := C) F
    LaxRightLinear.μᵣ F d c = LaxLeftLinear.μₗ F (mop c) d := (rfl)

/-- Recovering an oplax right lineator only reindexes its arguments. -/
theorem OplaxRightLinear.ofMonoidalOpposite_δᵣ (F : D ⥤ E) [F.OplaxLeftLinear Cᴹᵒᵖ]
    (d : D) (c : C) :
    letI := OplaxRightLinear.ofMonoidalOpposite (C := C) F
    OplaxRightLinear.δᵣ F d c = OplaxLeftLinear.δₗ F (mop c) d := (rfl)

section Lineators

variable (F : D ⥤ E) [F.LaxRightLinear C]

/-- Unitarity of all lineators is preserved and reflected by transport. -/
theorem LaxRightLinear.monoidalOpposite_unitary_iff [TauCeti.DaggerCategory E] :
    letI := LaxRightLinear.monoidalOpposite (C := C) F
    (∀ (c : Cᴹᵒᵖ) (d : D), TauCeti.IsUnitary (LaxLeftLinear.μₗ F c d)) ↔
      ∀ (d : D) (c : C), TauCeti.IsUnitary (LaxRightLinear.μᵣ F d c) := by
  constructor
  · intro h d c
    exact h (mop c) d
  · intro h c d
    exact h d (unmop c)

end Lineators

namespace RightLinear

variable (C D) in
/-- The identity right module functor, obtained from the identity left module functor. -/
instance id : (𝟭 D).RightLinear C :=
  ofMonoidalOpposite (C := C) (𝟭 D)

/-- Transport carries the identity right-linear structure to the identity left-linear one. -/
@[simp] theorem monoidalOpposite_id :
    monoidalOpposite (C := C) (𝟭 D) = LeftLinear.id Cᴹᵒᵖ D := (rfl)

/-- Identity right lineators are identity arrows. -/
@[simp] theorem id_μᵣ (d : D) (c : C) : LaxRightLinear.μᵣ (𝟭 D) d c = 𝟙 _ := (rfl)

/-- Identity right oplax lineators are identity arrows. -/
@[simp] theorem id_δᵣ (d : D) (c : C) : OplaxRightLinear.δᵣ (𝟭 D) d c = 𝟙 _ := (rfl)

variable (F : D ⥤ E) (G : E ⥤ H) [F.RightLinear C] [G.RightLinear C]

/-- Composition of right module functors is composition over the opposite left action. -/
instance comp : (F ⋙ G).RightLinear C :=
  letI := monoidalOpposite (C := C) F
  letI := monoidalOpposite (C := C) G
  ofMonoidalOpposite (C := C) (F ⋙ G)

/-- The right lineator of a composite applies the outer lineator first. -/
@[simp] theorem comp_μᵣ (d : D) (c : C) :
    LaxRightLinear.μᵣ (F ⋙ G) d c =
      LaxRightLinear.μᵣ G (F.obj d) c ≫ G.map (LaxRightLinear.μᵣ F d c) := (rfl)

/-- The right oplax lineator of a composite applies the inner oplax lineator first. -/
@[simp] theorem comp_δᵣ (d : D) (c : C) :
    OplaxRightLinear.δᵣ (F ⋙ G) d c =
      G.map (OplaxRightLinear.δᵣ F d c) ≫ OplaxRightLinear.δᵣ G (F.obj d) c := (rfl)

end RightLinear

end Functor

namespace NatTrans

variable {F G : D ⥤ E} [F.LaxRightLinear C] [G.LaxRightLinear C]

/-- A right module natural transformation is a left module natural transformation over
`Cᴹᵒᵖ`. This abbreviation gives access to all left-linear transformation operations. -/
abbrev IsRightLinear (τ : F ⟶ G) : Prop :=
  letI := Functor.LaxRightLinear.monoidalOpposite (C := C) F
  letI := Functor.LaxRightLinear.monoidalOpposite (C := C) G
  IsLeftLinear τ Cᴹᵒᵖ

/-- Right-linearity says exactly that the components commute with the right lineators. -/
theorem isRightLinear_iff (τ : F ⟶ G) :
    IsRightLinear (C := C) τ ↔ ∀ (d : D) (c : C),
      Functor.LaxRightLinear.μᵣ F d c ≫ τ.app (d ⊙ᵣ c) =
        τ.app d ⊵ᵣ c ≫ Functor.LaxRightLinear.μᵣ G d c := by
  let := Functor.LaxRightLinear.monoidalOpposite (C := C) F
  let := Functor.LaxRightLinear.monoidalOpposite (C := C) G
  constructor
  · intro h d c
    exact h.μₗ_comp_app (mop c) d
  · intro h
    exact ⟨fun c d => h d (unmop c)⟩

namespace IsRightLinear

/-- Components of a right-linear transformation commute with the right lineators. -/
@[reassoc (attr := simp)] theorem μᵣ_comp_app (τ : F ⟶ G)
    [h : IsRightLinear (C := C) τ] (d : D) (c : C) :
    Functor.LaxRightLinear.μᵣ F d c ≫ τ.app (d ⊙ᵣ c) =
      τ.app d ⊵ᵣ c ≫ Functor.LaxRightLinear.μᵣ G d c :=
  (isRightLinear_iff τ).mp h d c

/-- Identity transformations are right-linear. -/
instance id : IsRightLinear (C := C) (𝟙 F) :=
  (isRightLinear_iff _).mpr (by simp)

/-- Vertical composites of right-linear transformations are right-linear. -/
instance comp {K : D ⥤ E} [K.LaxRightLinear C] (τ : F ⟶ G) (σ : G ⟶ K)
    [IsRightLinear (C := C) τ] [IsRightLinear (C := C) σ] :
    IsRightLinear (C := C) (τ ≫ σ) := by
  let := Functor.LaxRightLinear.monoidalOpposite (C := C) F
  let := Functor.LaxRightLinear.monoidalOpposite (C := C) G
  let := Functor.LaxRightLinear.monoidalOpposite (C := C) K
  exact IsLeftLinear.comp τ σ

end IsRightLinear

end NatTrans

end CategoryTheory
