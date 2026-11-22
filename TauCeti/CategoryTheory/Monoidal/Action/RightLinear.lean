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

A right action of `C` on `D` gives a left action of `Cᴹᵒᵖ` on `D`, reversing the tensor
order in `C`. We transport lax, oplax and strong lineators along Mathlib's
`MonoidalLeftAction.monoidalOppositeLeftAction`. Strong structures correspond bijectively,
with the same lineator arrows; in particular this preserves unitary lineators. To use the
left-linear API over `Cᴹᵒᵖ`, install the opposite left action locally.

We use the left-linear API to equip identities and composites with right-linear structures
and to express right-linear natural transformations, which are closed under vertical composition.
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

variable (C)

/-- Read lax right lineators as lax left lineators for the monoidal opposite. -/
@[expose, instance_reducible]
def LaxRightLinear.monoidalOpposite (F : D ⥤ E) [F.LaxRightLinear C] :
    F.LaxLeftLinear Cᴹᵒᵖ where
  μₗ c d := LaxRightLinear.μᵣ F d (unmop c)
  μₗ_naturality_left f d := LaxRightLinear.μᵣ_naturality_right F d f.unmop
  μₗ_naturality_right c _ _ f := LaxRightLinear.μᵣ_naturality_left F f (unmop c)
  μₗ_associativity c c' d := LaxRightLinear.μᵣ_associativity F d (unmop c') (unmop c)
  μₗ_unitality d := LaxRightLinear.μᵣ_unitality F d

/-- Read oplax right lineators as oplax left lineators for the monoidal opposite. -/
@[expose, instance_reducible]
def OplaxRightLinear.monoidalOpposite (F : D ⥤ E) [F.OplaxRightLinear C] :
    F.OplaxLeftLinear Cᴹᵒᵖ where
  δₗ c d := OplaxRightLinear.δᵣ F d (unmop c)
  δₗ_naturality_left f d := OplaxRightLinear.δᵣ_naturality_right F d f.unmop
  δₗ_naturality_right c _ _ f := OplaxRightLinear.δᵣ_naturality_left F f (unmop c)
  δₗ_associativity c c' d := OplaxRightLinear.δᵣ_associativity F d (unmop c') (unmop c)
  δₗ_unitality_inv d := OplaxRightLinear.δᵣ_unitality_inv F d

/-- Read a strong right-linear structure as a strong left-linear structure over `Cᴹᵒᵖ`.
This is deliberately not a global instance: both directions of transport are available. -/
@[expose, instance_reducible]
def RightLinear.monoidalOpposite (F : D ⥤ E) [F.RightLinear C] :
    F.LeftLinear Cᴹᵒᵖ where
  toLaxLeftLinear := LaxRightLinear.monoidalOpposite C F
  toOplaxLeftLinear := OplaxRightLinear.monoidalOpposite C F
  μₗ_comp_δₗ c d := RightLinear.μᵣ_comp_δᵣ F d (unmop c)
  δₗ_comp_μₗ c d := RightLinear.δᵣ_comp_μᵣ F d (unmop c)

/-- Recover lax right lineators from left lineators for the opposite action. -/
@[expose, instance_reducible]
def LaxRightLinear.ofMonoidalOpposite (F : D ⥤ E) [F.LaxLeftLinear Cᴹᵒᵖ] :
    F.LaxRightLinear C where
  μᵣ d c := LaxLeftLinear.μₗ F (mop c) d
  μᵣ_naturality_right d _ _ f := LaxLeftLinear.μₗ_naturality_left F f.mop d
  μᵣ_naturality_left f c := LaxLeftLinear.μₗ_naturality_right F (mop c) f
  μᵣ_associativity d c c' := LaxLeftLinear.μₗ_associativity F (mop c') (mop c) d
  μᵣ_unitality d := LaxLeftLinear.μₗ_unitality (C := Cᴹᵒᵖ) F d

/-- Recover oplax right lineators from left lineators for the opposite action. -/
@[expose, instance_reducible]
def OplaxRightLinear.ofMonoidalOpposite (F : D ⥤ E) [F.OplaxLeftLinear Cᴹᵒᵖ] :
    F.OplaxRightLinear C where
  δᵣ d c := OplaxLeftLinear.δₗ F (mop c) d
  δᵣ_naturality_right d _ _ f := OplaxLeftLinear.δₗ_naturality_left F f.mop d
  δᵣ_naturality_left f c := OplaxLeftLinear.δₗ_naturality_right F (mop c) f
  δᵣ_associativity d c c' := OplaxLeftLinear.δₗ_associativity F (mop c') (mop c) d
  δᵣ_unitality_inv d := OplaxLeftLinear.δₗ_unitality_inv (C := Cᴹᵒᵖ) F d

/-- Recover a strong right-linear structure from the opposite left action. -/
@[expose, instance_reducible]
def RightLinear.ofMonoidalOpposite (F : D ⥤ E) [F.LeftLinear Cᴹᵒᵖ] :
    F.RightLinear C where
  toLaxRightLinear := LaxRightLinear.ofMonoidalOpposite C F
  toOplaxRightLinear := OplaxRightLinear.ofMonoidalOpposite C F
  μᵣ_comp_δᵣ d c := LeftLinear.μₗ_comp_δₗ F (mop c) d
  δᵣ_comp_μᵣ d c := LeftLinear.δₗ_comp_μₗ F (mop c) d

/-- Strong right-linear structures are exactly strong left-linear structures for the
opposite action. Both lineators are retained, and the two transports are inverse. -/
def rightLinearEquivMonoidalOpposite (F : D ⥤ E) :
    F.RightLinear C ≃ F.LeftLinear Cᴹᵒᵖ where
  toFun h := letI := h; RightLinear.monoidalOpposite C F
  invFun h := letI := h; RightLinear.ofMonoidalOpposite C F
  left_inv _ := rfl
  right_inv _ := rfl

/-- The forward map of the equivalence is transport to the opposite left action. -/
@[simp] theorem rightLinearEquivMonoidalOpposite_apply (F : D ⥤ E) (h : F.RightLinear C) :
    rightLinearEquivMonoidalOpposite C F h = (letI := h; RightLinear.monoidalOpposite C F) := (rfl)

/-- The inverse map of the equivalence recovers right lineators from the opposite left action. -/
@[simp] theorem rightLinearEquivMonoidalOpposite_symm_apply (F : D ⥤ E) (h : F.LeftLinear Cᴹᵒᵖ) :
    (rightLinearEquivMonoidalOpposite C F).symm h =
      (letI := h; RightLinear.ofMonoidalOpposite C F) := (rfl)

variable {C}

/-- Transport of a lax right lineator only reindexes its arguments. -/
@[simp] theorem LaxRightLinear.monoidalOpposite_μₗ (F : D ⥤ E) [F.LaxRightLinear C]
    (c : Cᴹᵒᵖ) (d : D) :
    letI := LaxRightLinear.monoidalOpposite C F
    LaxLeftLinear.μₗ F c d = LaxRightLinear.μᵣ F d (unmop c) := rfl

/-- Transport of an oplax right lineator only reindexes its arguments. -/
@[simp] theorem OplaxRightLinear.monoidalOpposite_δₗ (F : D ⥤ E) [F.OplaxRightLinear C]
    (c : Cᴹᵒᵖ) (d : D) :
    letI := OplaxRightLinear.monoidalOpposite C F
    OplaxLeftLinear.δₗ F c d = OplaxRightLinear.δᵣ F d (unmop c) := rfl

/-- Recovering a lax right lineator only reindexes its arguments. -/
theorem LaxRightLinear.ofMonoidalOpposite_μᵣ (F : D ⥤ E) [F.LaxLeftLinear Cᴹᵒᵖ]
    (d : D) (c : C) :
    letI := LaxRightLinear.ofMonoidalOpposite C F
    LaxRightLinear.μᵣ F d c = LaxLeftLinear.μₗ F (mop c) d := rfl

/-- Recovering an oplax right lineator only reindexes its arguments. -/
theorem OplaxRightLinear.ofMonoidalOpposite_δᵣ (F : D ⥤ E) [F.OplaxLeftLinear Cᴹᵒᵖ]
    (d : D) (c : C) :
    letI := OplaxRightLinear.ofMonoidalOpposite C F
    OplaxRightLinear.δᵣ F d c = OplaxLeftLinear.δₗ F (mop c) d := rfl

section Lineators

variable (F : D ⥤ E) [F.LaxRightLinear C]

/-- Unitarity of all lineators is preserved and reflected by transport. -/
theorem LaxRightLinear.forall_isUnitary_monoidalOpposite_μₗ_iff [TauCeti.DaggerCategory E] :
    letI := LaxRightLinear.monoidalOpposite C F
    (∀ (c : Cᴹᵒᵖ) (d : D), TauCeti.IsUnitary (LaxLeftLinear.μₗ F c d)) ↔
      ∀ (d : D) (c : C), TauCeti.IsUnitary (LaxRightLinear.μᵣ F d c) := by
  constructor
  · intro h d c
    exact h (mop c) d
  · intro h c d
    exact h d (unmop c)

end Lineators

namespace LaxRightLinear

variable (C D) in
/-- The identity functor is lax right-linear, with identity lineators. -/
instance id : (𝟭 D).LaxRightLinear C := ofMonoidalOpposite C (𝟭 D)

/-- The lax right lineator of the identity functor is the identity arrow. -/
@[simp] theorem id_μᵣ (d : D) (c : C) : μᵣ (𝟭 D) d c = 𝟙 _ := (rfl)

variable (F : D ⥤ E) (G : E ⥤ H) [F.LaxRightLinear C] [G.LaxRightLinear C]

/-- The composite of lax right-linear functors is lax right-linear. -/
instance comp : (F ⋙ G).LaxRightLinear C :=
  letI := monoidalOpposite C F
  letI := monoidalOpposite C G
  ofMonoidalOpposite C (F ⋙ G)

/-- The lax right lineator of a composite applies the outer lineator first. -/
@[simp] theorem comp_μᵣ (d : D) (c : C) :
    μᵣ (F ⋙ G) d c = μᵣ G (F.obj d) c ≫ G.map (μᵣ F d c) := (rfl)

end LaxRightLinear

namespace OplaxRightLinear

variable (C D) in
/-- The identity functor is oplax right-linear, with identity lineators. -/
instance id : (𝟭 D).OplaxRightLinear C := ofMonoidalOpposite C (𝟭 D)

/-- The oplax right lineator of the identity functor is the identity arrow. -/
@[simp] theorem id_δᵣ (d : D) (c : C) : δᵣ (𝟭 D) d c = 𝟙 _ := (rfl)

variable (F : D ⥤ E) (G : E ⥤ H) [F.OplaxRightLinear C] [G.OplaxRightLinear C]

/-- The composite of oplax right-linear functors is oplax right-linear. -/
instance comp : (F ⋙ G).OplaxRightLinear C :=
  letI := monoidalOpposite C F
  letI := monoidalOpposite C G
  ofMonoidalOpposite C (F ⋙ G)

/-- The oplax right lineator of a composite applies the inner lineator first. -/
@[simp] theorem comp_δᵣ (d : D) (c : C) :
    δᵣ (F ⋙ G) d c = G.map (δᵣ F d c) ≫ δᵣ G (F.obj d) c := (rfl)

end OplaxRightLinear

namespace RightLinear

variable (C D) in
/-- The identity functor is right-linear, with identity lineators. -/
instance id : (𝟭 D).RightLinear C := ofMonoidalOpposite C (𝟭 D)

variable (C D) in
/-- Transport carries the identity right-linear structure to the identity left-linear one. -/
@[simp] theorem monoidalOpposite_id :
    monoidalOpposite C (𝟭 D) = LeftLinear.id Cᴹᵒᵖ D := (rfl)

variable (F : D ⥤ E) (G : E ⥤ H) [F.RightLinear C] [G.RightLinear C]

/-- The composite of right-linear functors is right-linear, with the lax and oplax lineators
of `LaxRightLinear.comp` and `OplaxRightLinear.comp`. -/
instance comp : (F ⋙ G).RightLinear C :=
  letI := monoidalOpposite C F
  letI := monoidalOpposite C G
  ofMonoidalOpposite C (F ⋙ G)

variable (C) in
/-- Transport carries composite right-linear structures to composite left-linear structures. -/
@[simp] theorem monoidalOpposite_comp :
    monoidalOpposite C (F ⋙ G) =
      letI := monoidalOpposite C F
      letI := monoidalOpposite C G
      LeftLinear.comp F G := (rfl)

end RightLinear

end Functor

namespace NatTrans

variable {F G : D ⥤ E} [F.LaxRightLinear C] [G.LaxRightLinear C]

/-- A right module natural transformation commutes with the lax right lineators. This is
`IsLeftLinear τ Cᴹᵒᵖ` for the opposite left actions and the transported lax lineators.
Install those actions and transported structures locally to invoke the left-linear API. -/
abbrev IsRightLinear (τ : F ⟶ G) (C : Type*) [Category* C] [MonoidalCategory C]
    [MonoidalRightAction C D] [MonoidalRightAction C E]
    [F.LaxRightLinear C] [G.LaxRightLinear C] : Prop :=
  letI := Functor.LaxRightLinear.monoidalOpposite C F
  letI := Functor.LaxRightLinear.monoidalOpposite C G
  IsLeftLinear τ Cᴹᵒᵖ

variable (C) in
/-- Right-linearity says exactly that the components commute with the right lineators. -/
theorem isRightLinear_iff (τ : F ⟶ G) :
    IsRightLinear τ C ↔ ∀ (d : D) (c : C),
      Functor.LaxRightLinear.μᵣ F d c ≫ τ.app (d ⊙ᵣ c) =
        τ.app d ⊵ᵣ c ≫ Functor.LaxRightLinear.μᵣ G d c := by
  let := Functor.LaxRightLinear.monoidalOpposite C F
  let := Functor.LaxRightLinear.monoidalOpposite C G
  constructor
  · intro h d c
    exact h.μₗ_comp_app (mop c) d
  · intro h
    exact ⟨fun c d => h d (unmop c)⟩

namespace IsRightLinear

/-- Components of a right-linear transformation commute with the right lineators. -/
@[reassoc (attr := simp)] theorem μᵣ_comp_app (τ : F ⟶ G)
    [h : IsRightLinear τ C] (d : D) (c : C) :
    Functor.LaxRightLinear.μᵣ F d c ≫ τ.app (d ⊙ᵣ c) =
      τ.app d ⊵ᵣ c ≫ Functor.LaxRightLinear.μᵣ G d c :=
  (isRightLinear_iff C τ).mp h d c

/-- Vertical composites of right-linear transformations are right-linear. -/
instance comp {K : D ⥤ E} [K.LaxRightLinear C] (τ : F ⟶ G) (σ : G ⟶ K)
    [IsRightLinear τ C] [IsRightLinear σ C] :
    IsRightLinear (τ ≫ σ) C := by
  let := Functor.LaxRightLinear.monoidalOpposite C F
  let := Functor.LaxRightLinear.monoidalOpposite C G
  let := Functor.LaxRightLinear.monoidalOpposite C K
  exact IsLeftLinear.comp τ σ

open Functor.OplaxRightLinear in
/-- A right-linear transformation between strong right-linear functors also commutes with
oplax lineators. -/
@[reassoc] theorem app_comp_δᵣ {F G : D ⥤ E} [F.RightLinear C] [G.RightLinear C]
    (τ : F ⟶ G) [IsRightLinear τ C] (d : D) (c : C) :
    τ.app (d ⊙ᵣ c) ≫ δᵣ G d c = δᵣ F d c ≫ τ.app d ⊵ᵣ c := by
  let := Functor.RightLinear.monoidalOpposite C F
  let := Functor.RightLinear.monoidalOpposite C G
  exact IsLeftLinear.app_comp_δₗ τ (mop c) d

open Functor.OplaxRightLinear in
/-- A transformation between strong right-linear functors is right-linear if it commutes with
oplax lineators. -/
theorem of_app_comp_δᵣ {F G : D ⥤ E} [F.RightLinear C] [G.RightLinear C] (τ : F ⟶ G)
    (h : ∀ (d : D) (c : C), τ.app (d ⊙ᵣ c) ≫ δᵣ G d c = δᵣ F d c ≫ τ.app d ⊵ᵣ c) :
    IsRightLinear τ C := by
  let := Functor.RightLinear.monoidalOpposite C F
  let := Functor.RightLinear.monoidalOpposite C G
  exact IsLeftLinear.of_app_comp_δₗ τ fun c d => h d (unmop c)

end IsRightLinear

end NatTrans

end CategoryTheory
