/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Lifting against horn inclusions

A map of simplicial sets `Λ[n + 1, i] ⟶ X` out of a horn is the same as a compatible family of
`n`-simplices of `X`, one for each face `j ≠ i` (`SSet.horn.IsCompatible`). Accordingly, a map
`p : X ⟶ Y` has the right lifting property with respect to the horn inclusion
`Λ[n + 1, i] ⟶ Δ[n + 1]` exactly when every compatible family of faces lying over the faces of
an `(n + 1)`-simplex of `Y` extends to an `(n + 1)`-simplex of `X` over it
(`SSet.hasLiftingProperty_horn_ι_iff`). This is the relative form of Mathlib's criterion
`SSet.KanComplex.iff` for Kan complexes. It reduces horn-lifting conditions to statements about
simplices and their faces, which is how such conditions are transported along constructions
that act on simplices, such as universe lifts.

Kan fibrations and inner fibrations are the maps with the right lifting property with respect
to all horn inclusions, respectively all inner horn inclusions
(`SSet.modelCategoryQuillen.rlp_J_iff`, `SSet.mem_innerFibrations_iff`).
-/

public section

open CategoryTheory Simplicial
open SSet.modelCategoryQuillen

universe u

namespace SSet

variable {X Y : SSet.{u}}

variable {X Y : SSet.{u}}

/-- A map `p` has the right lifting property with respect to the horn inclusion
`Λ[n + 1, i] ⟶ Δ[n + 1]` exactly when every compatible family of faces in the source of `p`,
lying over the faces of an `(n + 1)`-simplex `b` of the target, extends to an
`(n + 1)`-simplex over `b`. -/
theorem hasLiftingProperty_horn_ι_iff (p : X ⟶ Y) {n : ℕ} (i : Fin (n + 2)) :
    HasLiftingProperty Λ[n + 1, i].ι p ↔
      ∀ (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X) (_ : horn.IsCompatible f)
        (b : Δ[n + 1] ⟶ Y) (_ : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
          f j hj ≫ p = stdSimplex.δ j ≫ b),
        ∃ φ : Δ[n + 1] ⟶ X,
          (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫ p = b := by
  refine ⟨fun _ f hf b comm ↦ ?_, fun h ↦ ⟨fun {t b} sq ↦ ?_⟩⟩
  · have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
      ⟨horn.hom_ext' fun j hj ↦ by simpa using comm j hj⟩
    exact ⟨sq.lift, fun j hj ↦ by simp [← horn.ι_ι_assoc i j hj], by simp⟩
  · obtain ⟨φ, hφ, hφp⟩ := h _ (horn.IsCompatible.of_hom t) b fun j hj ↦ by
      rw [Category.assoc, sq.w, ← horn.ι_ι_assoc i j hj]
    exact ⟨⟨{ l := φ
              fac_left := horn.hom_ext' fun j hj ↦ by rw [horn.ι_ι_assoc, hφ]
              fac_right := hφp }⟩⟩

/-- A map is a Kan fibration exactly when it has the right lifting property with respect to every
horn inclusion. -/
theorem modelCategoryQuillen.rlp_J_iff (p : X ⟶ Y) :
    J.rlp p ↔ ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty Λ[n + 1, i].ι p := by
  refine ⟨fun h n i ↦ h _ ?_, fun h _ _ _ hj ↦ ?_⟩
  · simp only [J, MorphismProperty.iSup_iff]
    exact ⟨n, ⟨i⟩⟩
  · simp only [J, MorphismProperty.iSup_iff] at hj
    obtain ⟨n, ⟨i⟩⟩ := hj
    exact h n i

/-- A map is an inner fibration exactly when it has the right lifting property with respect to
every inner horn inclusion. -/
theorem mem_innerFibrations_iff (p : X ⟶ Y) :
    innerFibrations p ↔ ∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
      HasLiftingProperty Λ[n + 2, i].ι p := by
  refine ⟨fun h n i h0 hn ↦ h _ ⟨i, h0, hn⟩, ?_⟩
  rintro h _ _ _ ⟨i, h0, hn⟩
  exact h _ i h0 hn

end SSet
