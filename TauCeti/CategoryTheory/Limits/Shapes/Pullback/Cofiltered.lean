/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of a cofiltered limit

Let `D : I ⥤ C` be a diagram in a category with pullbacks, `i : I`, and `r : Z ⟶ Dᵢ`. The members
`Dⱼ` over `i` base change along `r` to the diagram `D.pullbackOver r : Over i ⥤ C`,
`j ↦ Dⱼ ×_{Dᵢ} Z`, and a cone `c` over `D` base changes to the cone `c.pullbackOver r` with point
`c.pt ×_{Dᵢ} Z`. When `I` is cofiltered, the base change of a limit cone is a limit cone
(`CategoryTheory.Limits.IsLimit.pullbackOver`).

Objectwise, `D.pullbackOver r` is the composite `Over.post D ⋙ Over.pullback r ⋙ Over.forget Z`,
and the limit statement is transported from that composite. It is stated with the objects
`pullback (D.map j.hom) r` and the transition maps `pullback.map` so that the pullback projections
apply to its members directly, with the lemmas `Functor.pullbackOver_map_fst` and
`Functor.pullbackOver_map_snd` describing the transition maps.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasPullbacks C] {I : Type*} [Category* I] (D : I ⥤ C) {i : I}
  {Z : C} (r : Z ⟶ D.obj i)

/-- The base change `j ↦ Dⱼ ×_{Dᵢ} Z` of the members of `D` over `i` along `r : Z ⟶ Dᵢ`. -/
noncomputable abbrev _root_.CategoryTheory.Functor.pullbackOver : Over i ⥤ C where
  obj j := pullback (D.map j.hom) r
  map {j k} f := pullback.map _ _ _ _ (D.map f.left) (𝟙 Z) (𝟙 _)
    (by simp [← D.map_comp]) (by simp)
  map_id j := by ext <;> simp
  map_comp f g := by ext <;> simp

@[reassoc]
lemma _root_.CategoryTheory.Functor.pullbackOver_map_fst {j k : Over i} (f : j ⟶ k) :
    (D.pullbackOver r).map f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ D.map f.left := by
  simp [Functor.pullbackOver]

@[reassoc]
lemma _root_.CategoryTheory.Functor.pullbackOver_map_snd {j k : Over i} (f : j ⟶ k) :
    (D.pullbackOver r).map f ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [Functor.pullbackOver]

variable {D}

/-- The base change `c.pt ×_{Dᵢ} Z` of a cone `c` over `D` along `r : Z ⟶ Dᵢ`. -/
noncomputable abbrev Cone.pullbackOver (c : Cone D) : Cone (D.pullbackOver r) where
  pt := pullback (c.π.app i) r
  π :=
    { app j := pullback.map _ _ _ _ (c.π.app j.left) (𝟙 Z) (𝟙 _) (by simp) (by simp)
      naturality j k f := by ext <;> simp [Functor.pullbackOver] }

@[reassoc]
lemma Cone.pullbackOver_π_app_fst (c : Cone D) (j : Over i) :
    (c.pullbackOver r).π.app j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ c.π.app j.left := by
  simp [Cone.pullbackOver]

@[reassoc]
lemma Cone.pullbackOver_π_app_snd (c : Cone D) (j : Over i) :
    (c.pullbackOver r).π.app j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [Cone.pullbackOver]

/-- The base change of a limit cone of a cofiltered diagram is a limit cone. -/
noncomputable def IsLimit.pullbackOver [IsCofilteredOrEmpty I] {c : Cone D}
    (hc : IsLimit c) : IsLimit (c.pullbackOver r) := by
  -- `Over.isLimitConePost` lifts the limit to `Over Dᵢ`, `Over.pullback r` is a right adjoint,
  -- and `Over.forget Z` preserves cofiltered limits; the composite agrees with
  -- `D.pullbackOver r` objectwise.
  let e : Over.post D ⋙ Over.pullback r ⋙ Over.forget Z ≅ D.pullbackOver r :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by ext <;> simp [Functor.pullbackOver]
  exact (IsLimit.postcomposeHomEquiv e _).symm
      (isLimitOfPreserves (Over.pullback r ⋙ Over.forget Z) (Over.isLimitConePost i hc))
    |>.ofIsoLimit (Cone.ext (Iso.refl _) fun j ↦ by
      ext <;> simp [Cone.pullbackOver, e, Over.conePost])

end CategoryTheory.Limits
