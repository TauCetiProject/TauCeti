/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.HomDifferential
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Splitting extensions of quiver representations

Short exact sequences split at each vertex over a field. Their vertexwise linear sections
define an arrow family measuring the failure to commute with arrows.

## References

H. Derksen and J. Weyman, *An Introduction to Quiver Representations*, Chapter 1,
for the description of extensions by arrow maps modulo changes of vertex splittings.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits
open QuiverRep

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

namespace QuiverRep

variable {S : ShortComplex (QuiverRep.{u, v, w, t} k Q)}

/-- A short exact sequence of representations admits a splitting at each vertex. -/
noncomputable def vertexSplitting (hS : S.ShortExact) (i : Q) :
    (S.map ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i))).Splitting :=
  (hS.map_of_exact ((evaluation (Paths Q) (ModuleCat k)).obj
    ((Paths.of Q).obj i))).splittingOfProjective

variable (sp : ∀ i : Q,
  (S.map ((evaluation (Paths Q) (ModuleCat k)).obj ((Paths.of Q).obj i))).Splitting)

/-- The linear sections supplied by a family of vertex splittings. -/
noncomputable def vertexSplittingSection : HomVertex S.X₃ S.X₂ := fun i ↦ (sp i).s.hom

/-- The linear retractions supplied by a family of vertex splittings. -/
noncomputable def vertexSplittingRetraction : HomVertex S.X₂ S.X₁ := fun i ↦ (sp i).r.hom

-- These accessor formulas are not simp lemmas: keep the typed vertex families in
-- normal form so the section and decomposition identities can apply.
/-- The section family evaluates to the section of the chosen vertex splitting. -/
theorem vertexSplittingSection_apply (i : Q) (x : vertexSpace k Q S.X₃ i) :
    vertexSplittingSection sp i x = (sp i).s.hom x := (rfl)

/-- The retraction family evaluates to the retraction of the chosen vertex splitting. -/
theorem vertexSplittingRetraction_apply (i : Q) (x : vertexSpace k Q S.X₂ i) :
    vertexSplittingRetraction sp i x = (sp i).r.hom x := (rfl)

/-- The vertex section is a right inverse to the quotient map. -/
@[simp]
theorem vertexSplittingSection_comp_g (i : Q) (x : vertexSpace k Q S.X₃ i) :
    homVertex S.X₂ S.X₃ S.g i (vertexSplittingSection sp i x) = x := by
  erw [homVertex_apply]
  exact congrArg (fun p ↦ p x) (sp i).s_g

/-- The vertex retraction and section give the direct-sum decomposition. -/
theorem vertexSplitting_decomposition (i : Q) (x : vertexSpace k Q S.X₂ i) :
    homVertex S.X₁ S.X₂ S.f i (vertexSplittingRetraction sp i x) +
      vertexSplittingSection sp i (homVertex S.X₂ S.X₃ S.g i x) = x := by
  erw [homVertex_apply, homVertex_apply]
  exact congrArg (fun p ↦ p x) (sp i).id

/-- The upper right arrow block determined by a family of vertex splittings. -/
noncomputable def vertexSplittingArrow : HomArrow S.X₃ S.X₁ := fun i j a ↦
  (vertexSplittingRetraction sp j).comp
    ((mapₗ k Q S.X₂ a.toPath).comp (vertexSplittingSection sp i))

/-- The arrow family is computed by projecting the arrow action on the vertex section. -/
theorem vertexSplittingArrow_apply (i j : Q) (a : i ⟶ j)
    (x : vertexSpace k Q S.X₃ i) :
    vertexSplittingArrow sp i j a x = vertexSplittingRetraction sp j
      (mapₗ k Q S.X₂ a.toPath (vertexSplittingSection sp i x)) := (rfl)

/-- The upper right block measures the failure of the sections to commute with arrows. -/
theorem vertexSplittingArrow_defect (i j : Q) (a : i ⟶ j)
    (x : vertexSpace k Q S.X₃ i) :
    homVertex S.X₁ S.X₂ S.f j (vertexSplittingArrow sp i j a x) +
        vertexSplittingSection sp j (mapₗ k Q S.X₃ a.toPath x) =
      mapₗ k Q S.X₂ a.toPath (vertexSplittingSection sp i x) := by
  have hn : homVertex S.X₂ S.X₃ S.g j (mapₗ k Q S.X₂ a.toPath (vertexSplittingSection sp i x)) =
      mapₗ k Q S.X₃ a.toPath x := by
    calc
      _ = mapₗ k Q S.X₃ a.toPath
          (homVertex S.X₂ S.X₃ S.g i (vertexSplittingSection sp i x)) :=
        homVertex_naturality _ _ _ i j a _
      _ = _ := by rw [vertexSplittingSection_comp_g]
  rw [vertexSplittingArrow_apply, ← hn]
  exact vertexSplitting_decomposition sp j _

end QuiverRep

end TauCeti
