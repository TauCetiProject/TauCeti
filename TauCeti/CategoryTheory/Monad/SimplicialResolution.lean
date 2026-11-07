/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import TauCeti.AlgebraicTopology.SimplexCategory.GeneratorsRelations

/-!
# The simplicial resolution of a comonad

A comonad `G` gives a simplicial object with terms `G^(n+1) X`. Faces apply the
counit and degeneracies apply the comultiplication at the indicated position.
The simplicial identities are precisely naturality and the comonad axioms.
This construction supplies the simplicial object underlying the standard
polynomial resolution when applied to the free-polynomial comonad.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM), for the polynomial example.

The assembly follows `SimplexCategoryGenRel.toSimplexCategory`, using Mathlib's
simplex-category presentation by Robin Carlier and Tau Ceti's proof that its
comparison with the simplex category is an equivalence.
-/

public section

open CategoryTheory Opposite Functor

namespace CategoryTheory.Comonad

universe v u
variable {C : Type u} [Category.{v} C] (G : Comonad C)

/-- The `n`-fold iterate of a comonad, including the identity in degree zero.
Exposed so the source and target types of the recursive operators compute. -/
@[expose] def resolutionStage : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => resolutionStage n ⋙ (G : C ⥤ C)

lemma resolutionStage_zero : G.resolutionStage 0 = 𝟭 C := (rfl)
lemma resolutionStage_succ (n : ℕ) :
    G.resolutionStage (n + 1) = G.resolutionStage n ⋙ (G : C ⥤ C) := (rfl)

/-- Apply the counit at position `i` in an iterated comonad. Degree zero is the
augmentation `G X → X`. -/
def resolutionFace : ∀ n, Fin (n + 1) → (G.resolutionStage (n + 1) ⟶ G.resolutionStage n)
  | 0, _ => G.ε
  | n + 1, i => Fin.cases (whiskerLeft (G.resolutionStage (n + 1)) G.ε)
      (fun j ↦ whiskerRight (resolutionFace n j) (G : C ⥤ C)) i

/-- Apply the comultiplication at position `i` in an iterated comonad. -/
def resolutionDegeneracy : ∀ n, Fin (n + 1) →
    (G.resolutionStage (n + 1) ⟶ G.resolutionStage (n + 2))
  | 0, _ => G.δ
  | n + 1, i => Fin.cases (whiskerLeft (G.resolutionStage (n + 1)) G.δ)
      (fun j ↦ whiskerRight (resolutionDegeneracy n j) (G : C ⥤ C)) i

@[simp] lemma resolutionFace_zero (n : ℕ) (X : C) :
    (G.resolutionFace n 0).app X = G.ε.app ((G.resolutionStage n).obj X) := by
  cases n <;> rfl

@[simp] lemma resolutionFace_succ (n : ℕ) (i : Fin (n + 1)) (X : C) :
    (G.resolutionFace (n + 1) i.succ).app X = G.map ((G.resolutionFace n i).app X) := (rfl)

@[simp] lemma resolutionDegeneracy_zero (n : ℕ) (X : C) :
    (G.resolutionDegeneracy n 0).app X = G.δ.app ((G.resolutionStage n).obj X) := by
  cases n <;> rfl

@[simp] lemma resolutionDegeneracy_succ (n : ℕ) (i : Fin (n + 1)) (X : C) :
    (G.resolutionDegeneracy (n + 1) i.succ).app X =
      G.map ((G.resolutionDegeneracy n i).app X) := (rfl)

-- Normalize the recursive operators, whiskering and componentwise composition uniformly
-- in the six identities; using a fixed list avoids naturality simplification erasing the
-- comparison before both sides have the same component types.
local macro "resolution_simpa" " using " h:term : tactic =>
  `(tactic| (have h' := $h
             simp only [NatTrans.comp_app, NatTrans.id_app] at h' ⊢
             dsimp only [resolutionFace, resolutionDegeneracy, resolutionStage, Fin.cases,
               NatTrans.comp_app, NatTrans.id_app, NatTrans.vcomp, NatTrans.id,
               whiskerLeft, whiskerRight,
               Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h' ⊢
             simpa only [Fin.cases_zero, Fin.cases_succ, Fin.castSucc_zero,
               Fin.castSucc_succ, Fin.zero_eta, Fin.mk_one, ← Fin.succ_zero_eq_one,
               Fin.induction_zero,
               Fin.induction_succ, Functor.map_comp, Functor.map_id] using h'))

/-- Two counits at different positions commute. This includes the augmentation identity. -/
lemma resolutionFace_comp_face : ∀ (n : ℕ) (i j : Fin (n + 1)), i ≤ j →
    G.resolutionFace (n + 1) j.succ ≫ G.resolutionFace n i =
      G.resolutionFace (n + 1) i.castSucc ≫ G.resolutionFace n j := by
  intro n
  induction n with
  | zero =>
    intro i j h
    fin_cases i; fin_cases j
    ext X
    resolution_simpa using G.ε.naturality (G.ε.app X)
  | succ n ih =>
    intro i j h
    ext X
    induction i using Fin.cases with
    | zero =>
      resolution_simpa using G.ε.naturality ((G.resolutionFace (n + 1) j).app X)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        resolution_simpa using
          congrArg (fun f ↦ G.map (f.app X)) (ih i j (by simpa using h))

/-- A degeneracy followed by an earlier face commutes past that face. -/
lemma resolutionDegeneracy_comp_face_of_le : ∀ (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)),
    i ≤ j.castSucc →
    G.resolutionDegeneracy (n + 1) j.succ ≫ G.resolutionFace (n + 2) i.castSucc =
      G.resolutionFace (n + 1) i ≫ G.resolutionDegeneracy n j := by
  intro n
  induction n with
  | zero =>
    intro i j h
    fin_cases j
    have : i = 0 := Fin.ext (by simpa using h)
    subst i
    ext X
    resolution_simpa using G.ε.naturality (G.δ.app X)
  | succ n ih =>
    intro i j h
    ext X
    induction i using Fin.cases with
    | zero =>
      resolution_simpa using G.ε.naturality ((G.resolutionDegeneracy (n + 1) j).app X)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        resolution_simpa using
          congrArg (fun f ↦ G.map (f.app X)) (ih i j (by simpa using h))

/-- The first counit law cancels a duplicated position. -/
@[simp] lemma resolutionDegeneracy_comp_face_self : ∀ (n : ℕ) (i : Fin (n + 1)),
    G.resolutionDegeneracy n i ≫ G.resolutionFace (n + 1) i.castSucc = 𝟙 _ := by
  intro n
  induction n with
  | zero =>
    intro i
    fin_cases i
    ext X
    resolution_simpa using G.left_counit X
  | succ n ih =>
    intro i
    ext X
    induction i using Fin.cases with
    | zero => resolution_simpa using G.left_counit ((G.resolutionStage (n + 1)).obj X)
    | succ i => resolution_simpa using congrArg (fun f ↦ G.map (f.app X)) (ih i)

/-- The second counit law cancels a duplicated position. -/
@[simp] lemma resolutionDegeneracy_comp_face_succ : ∀ (n : ℕ) (i : Fin (n + 1)),
    G.resolutionDegeneracy n i ≫ G.resolutionFace (n + 1) i.succ = 𝟙 _ := by
  intro n
  induction n with
  | zero =>
    intro i
    fin_cases i
    ext X
    resolution_simpa using G.right_counit X
  | succ n ih =>
    intro i
    ext X
    induction i using Fin.cases with
    | zero => resolution_simpa using G.right_counit ((G.resolutionStage (n + 1)).obj X)
    | succ i => resolution_simpa using congrArg (fun f ↦ G.map (f.app X)) (ih i)

/-- A degeneracy followed by a later face commutes past that face. -/
lemma resolutionDegeneracy_comp_face_of_gt : ∀ (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)),
    j.castSucc < i →
    G.resolutionDegeneracy (n + 1) j.castSucc ≫ G.resolutionFace (n + 2) i.succ =
      G.resolutionFace (n + 1) i ≫ G.resolutionDegeneracy n j := by
  intro n
  induction n with
  | zero =>
    intro i j h
    fin_cases i <;> fin_cases j
    · simp at h
    · ext X
      resolution_simpa using (G.δ.naturality (G.ε.app X)).symm
  | succ n ih =>
    intro i j h
    ext X
    induction j using Fin.cases with
    | zero =>
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
      resolution_simpa using (G.δ.naturality ((G.resolutionFace (n + 1) i).app X)).symm
    | succ j =>
      induction i using Fin.cases with
      | zero => simp at h
      | succ i =>
        resolution_simpa using
          congrArg (fun f ↦ G.map (f.app X)) (ih i j (by simpa using h))

/-- Comultiplications commute, using coassociativity at a repeated position. -/
lemma resolutionDegeneracy_comp_degeneracy : ∀ (n : ℕ) (i j : Fin (n + 1)), i ≤ j →
    G.resolutionDegeneracy n j ≫ G.resolutionDegeneracy (n + 1) i.castSucc =
      G.resolutionDegeneracy n i ≫ G.resolutionDegeneracy (n + 1) j.succ := by
  intro n
  induction n with
  | zero =>
    intro i j h
    fin_cases i; fin_cases j
    ext X
    resolution_simpa using (G.coassoc X).symm
  | succ n ih =>
    intro i j h
    ext X
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => resolution_simpa using (G.coassoc ((G.resolutionStage (n + 1)).obj X)).symm
      | succ j =>
        resolution_simpa using G.δ.naturality ((G.resolutionDegeneracy n j).app X)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        resolution_simpa using
          congrArg (fun f ↦ G.map (f.app X)) (ih i j (by simpa using h))

/-- The simplicial resolution, functorial in its input object. Its `n`th term is `G^(n+1)`.
The body is exposed so these term types compute in dependent statements. -/
@[expose] noncomputable def simplicialResolution : C ⥤ SimplicialObject C :=
  (SimplexCategoryGenRel.fromSimplexCategory ⋙ Quotient.lift _
    (Paths.lift
      { obj n := op (G.resolutionStage (n.len + 1))
        map f := match f with
          | .δ i => (G.resolutionFace _ i).op
          | .σ i => (G.resolutionDegeneracy _ i).op })
    (by
      intro _ _ _ _ h
      -- Reduce singleton paths before using the comonad identities. The path lift
      -- computes through the presentation's named quiver object types.
      cases h
      all_goals repeat first
        | erw [Functor.map_comp]
        | erw [Paths.lift_toPath]
        | erw [Functor.map_id]
      all_goals apply Quiver.Hom.unop_inj
      case δ_comp_δ H => exact G.resolutionFace_comp_face _ _ _ H
      case δ_comp_σ_of_le H => exact G.resolutionDegeneracy_comp_face_of_le _ _ _ H
      case δ_comp_σ_self => exact G.resolutionDegeneracy_comp_face_self _ _
      case δ_comp_σ_succ => exact G.resolutionDegeneracy_comp_face_succ _ _
      case δ_comp_σ_of_gt H => exact G.resolutionDegeneracy_comp_face_of_gt _ _ _ H
      case σ_comp_σ H => exact G.resolutionDegeneracy_comp_degeneracy _ _ _ H)).leftOp.flip

@[simp] lemma simplicialResolution_obj_obj (X : C) (n : ℕ) :
    ((G.simplicialResolution.obj X).obj (op (SimplexCategory.mk n))) =
      (G.resolutionStage (n + 1)).obj X := (rfl)

/-- Faces of the simplicial resolution are the iterated counits. -/
@[simp] lemma simplicialResolution_δ (X : C) {n : ℕ} (i : Fin (n + 2)) :
    (G.simplicialResolution.obj X).δ i = (G.resolutionFace (n + 1) i).app X := by
  dsimp only [simplicialResolution, SimplicialObject.δ, Functor.flip, Functor.leftOp]
  erw [Functor.comp_map, SimplexCategoryGenRel.fromSimplexCategory_map_δ]
  erw [Quotient.lift_map_functor_map, Paths.lift_toPath]
  rfl

/-- Degeneracies of the simplicial resolution are the iterated comultiplications. -/
@[simp] lemma simplicialResolution_σ (X : C) {n : ℕ} (i : Fin (n + 1)) :
    (G.simplicialResolution.obj X).σ i = (G.resolutionDegeneracy n i).app X := by
  dsimp only [simplicialResolution, SimplicialObject.σ, Functor.flip, Functor.leftOp]
  erw [Functor.comp_map, SimplexCategoryGenRel.fromSimplexCategory_map_σ]
  erw [Quotient.lift_map_functor_map, Paths.lift_toPath]
  rfl

/-- A morphism acts on each term by the corresponding iterate of the comonad. -/
@[simp] lemma simplicialResolution_map_app {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (G.simplicialResolution.map f).app (op (SimplexCategory.mk n)) =
      (G.resolutionStage (n + 1)).map f := (rfl)

end CategoryTheory.Comonad
