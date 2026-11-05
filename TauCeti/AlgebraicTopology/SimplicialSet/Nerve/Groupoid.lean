/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import Mathlib.CategoryTheory.Groupoid
public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import TauCeti.AlgebraicTopology.SimplicialSet.Coskeletal
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# The nerve of a groupoid is a Kan complex

The nerve of a category `C` is a Kan complex exactly when `C` is a groupoid
(`CategoryTheory.nerve.kanComplex_iff`). This is the `1`-categorical case of Joyal's theorem that
a quasicategory is a Kan complex exactly when its homotopy category is a groupoid. Nerves of
groupoids, such as the nerve of a group viewed as a category with one object, are the simplest Kan
complexes with nontrivial fundamental groups.

One direction holds in any Kan complex: every edge is an equivalence
(`SSet.Edge.isEquivalence_of_kanComplex`), and an edge of a nerve is an equivalence exactly when
the morphism it represents is an isomorphism.

For the converse, nerves are `2`-coskeletal, so horns of dimension at least `4` have fillers in
any nerve (`SSet.existsUnique_horn_extension_of_isCoskeletal`), and inner horns have fillers since
nerves are quasicategories. The remaining horns are the outer horns of dimensions `2` and `3`. For
`Λ[2, 0]`, given `f : x₀ ⟶ x₁` and `h : x₀ ⟶ x₂`, the filler is the composable pair
`f, inv f ≫ h`. For `Λ[3, 0]`, the three given triangles determine every edge, and the missing
face `δ 0` commutes after cancelling the isomorphism on the edge from `0` to `1`. The horns
`Λ[2, 2]` and `Λ[3, 3]` are dual.

## Main results

* `CategoryTheory.nerve.kanComplex`: the nerve of a groupoid is a Kan complex.
* `CategoryTheory.nerve.kanComplex_iff`: the nerve of a category is a Kan complex exactly when
  the category is a groupoid.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.2.4.3 and Proposition 1.2.5.1.
-/

public section

open CategoryTheory Simplicial SSet

universe u v

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C]

section

variable [IsGroupoid C]

/-- The outer horn `Λ[2, 0]` in the nerve of a groupoid, given by its faces `δ 1` and `δ 2`, has
a filler. -/
private lemma exists_horn₂₀ (y₁ y₂ : (nerve C) _⦋1⦌)
    (h₁₂ : (nerve C).δ 1 y₁ = (nerve C).δ 1 y₂) :
    ∃ x : (nerve C) _⦋2⦌, (nerve C).δ 1 x = y₁ ∧ (nerve C).δ 2 x = y₂ := by
  obtain ⟨a, _, p, rfl⟩ := ComposableArrows.mk₁_surjective y₁
  obtain ⟨a', _, f, rfl⟩ := ComposableArrows.mk₁_surjective y₂
  -- The two edges share their source.
  obtain rfl : a = a' := congrArg (fun z : ComposableArrows C 0 ↦ z.obj 0) h₁₂
  exact ⟨ComposableArrows.mk₂ f (inv f ≫ p), by rw [δ₁_mk₂_eq, IsIso.hom_inv_id_assoc],
    δ₂_mk₂_eq _ _⟩

/-- The outer horn `Λ[2, 2]` in the nerve of a groupoid, given by its faces `δ 0` and `δ 1`, has
a filler. -/
private lemma exists_horn₂₂ (y₀ y₁ : (nerve C) _⦋1⦌)
    (h₀₁ : (nerve C).δ 0 y₀ = (nerve C).δ 0 y₁) :
    ∃ x : (nerve C) _⦋2⦌, (nerve C).δ 0 x = y₀ ∧ (nerve C).δ 1 x = y₁ := by
  obtain ⟨_, c, g, rfl⟩ := ComposableArrows.mk₁_surjective y₀
  obtain ⟨_, c', p, rfl⟩ := ComposableArrows.mk₁_surjective y₁
  -- The two edges share their target.
  obtain rfl : c = c' := congrArg (fun z : ComposableArrows C 0 ↦ z.obj 0) h₀₁
  exact ⟨ComposableArrows.mk₂ (p ≫ inv g) g, δ₀_mk₂_eq _ _,
    by rw [δ₁_mk₂_eq, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

/-- The outer horn `Λ[3, 0]` in the nerve of a groupoid, given by its faces `δ 1`, `δ 2` and
`δ 3`, has a filler. -/
private lemma exists_horn₃₀ (y₁ y₂ y₃ : (nerve C) _⦋2⦌)
    (h₁₂ : (nerve C).δ 1 y₁ = (nerve C).δ 1 y₂) (h₁₃ : (nerve C).δ 2 y₁ = (nerve C).δ 1 y₃)
    (h₂₃ : (nerve C).δ 2 y₂ = (nerve C).δ 2 y₃) :
    ∃ x : (nerve C) _⦋3⦌,
      (nerve C).δ 1 x = y₁ ∧ (nerve C).δ 2 x = y₂ ∧ (nerve C).δ 3 x = y₃ := by
  obtain ⟨_, _, _, p, q, rfl⟩ := ComposableArrows.mk₂_surjective y₁
  obtain ⟨_, _, _, r, s, rfl⟩ := ComposableArrows.mk₂_surjective y₂
  obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective y₃
  rw [δ₁_mk₂_eq, δ₁_mk₂_eq] at h₁₂
  rw [δ₂_mk₂_eq, δ₁_mk₂_eq] at h₁₃
  rw [δ₂_mk₂_eq, δ₂_mk₂_eq] at h₂₃
  -- The faces `δ 2` and `δ 3` share the edge `f` from `0` to `1`, the faces `δ 1` and `δ 3` the
  -- edge `f ≫ g` from `0` to `2`, and the faces `δ 1` and `δ 2` the edge from `0` to `3`.
  obtain ⟨rfl, rfl, hr⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₂₃)
  obtain ⟨rfl, rfl, hp⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₁₃)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hr hp
  subst hr hp
  obtain ⟨_, rfl, hs⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₁₂)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc] at hs
  -- Cancelling the isomorphism `r` identifies the edge `s` from `1` to `3` with `g ≫ q`.
  obtain rfl : s = g ≫ q := (cancel_epi r).1 hs.symm
  exact ⟨ComposableArrows.mk₃ r g q, δ₁_mk₃_eq _ _ _, δ₂_mk₃_eq _ _ _, δ₃_mk₃_eq _ _ _⟩

/-- The outer horn `Λ[3, 3]` in the nerve of a groupoid, given by its faces `δ 0`, `δ 1` and
`δ 2`, has a filler. -/
private lemma exists_horn₃₃ (y₀ y₁ y₂ : (nerve C) _⦋2⦌)
    (h₀₁ : (nerve C).δ 0 y₀ = (nerve C).δ 0 y₁) (h₀₂ : (nerve C).δ 1 y₀ = (nerve C).δ 0 y₂)
    (h₁₂ : (nerve C).δ 1 y₁ = (nerve C).δ 1 y₂) :
    ∃ x : (nerve C) _⦋3⦌,
      (nerve C).δ 0 x = y₀ ∧ (nerve C).δ 1 x = y₁ ∧ (nerve C).δ 2 x = y₂ := by
  obtain ⟨_, _, _, g, h, rfl⟩ := ComposableArrows.mk₂_surjective y₀
  obtain ⟨_, _, _, p, q, rfl⟩ := ComposableArrows.mk₂_surjective y₁
  obtain ⟨_, _, _, r, s, rfl⟩ := ComposableArrows.mk₂_surjective y₂
  rw [δ₀_mk₂_eq, δ₀_mk₂_eq] at h₀₁
  rw [δ₁_mk₂_eq, δ₀_mk₂_eq] at h₀₂
  rw [δ₁_mk₂_eq, δ₁_mk₂_eq] at h₁₂
  -- The faces `δ 0` and `δ 1` share the edge `h` from `2` to `3`, the faces `δ 0` and `δ 2` the
  -- edge `g ≫ h` from `1` to `3`, and the faces `δ 1` and `δ 2` the edge from `0` to `3`.
  obtain ⟨rfl, rfl, hq⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₀₁)
  obtain ⟨rfl, rfl, hs⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₀₂)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hq hs
  subst hq hs
  obtain ⟨rfl, _, hp⟩ := (Arrow.mk_eq_mk_iff _ _).1 (ComposableArrows.mk₁_eq_mk₁_iff.1 h₁₂)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, ← Category.assoc] at hp
  -- Cancelling the isomorphism `h` identifies the edge `p` from `0` to `2` with `r ≫ g`.
  obtain rfl : p = r ≫ g := (cancel_mono h).1 hp
  exact ⟨ComposableArrows.mk₃ r g h, δ₀_mk₃_eq _ _ _, δ₁_mk₃_eq _ _ _, δ₂_mk₃_eq _ _ _⟩

/-- The nerve of a groupoid is a Kan complex. -/
instance kanComplex : KanComplex (nerve C) := by
  rw [KanComplex.iff]
  intro n i f hf
  -- A filler of the horn assembled from the family `f` restricts to `f` on the faces.
  have of_horn (σ : Δ[n + 1] ⟶ nerve C) (hσ : Λ[n + 1, i].ι ≫ σ = hf.desc) :
      ∃ φ : Δ[n + 1] ⟶ nerve C, ∀ j hj, stdSimplex.δ j ≫ φ = f j hj :=
    ⟨σ, fun j hj ↦ by rw [← horn.ι_ι i j hj, Category.assoc, hσ, hf.ι_desc]⟩
  -- A simplex whose faces are the simplices of the family `f` is a filler.
  have of_simplex (x : (nerve C) _⦋n + 1⦌)
      (hx : ∀ j hj, (nerve C).δ j x = SSet.yonedaEquiv (f j hj)) :
      ∃ φ : Δ[n + 1] ⟶ nerve C, ∀ j hj, stdSimplex.δ j ≫ φ = f j hj :=
    ⟨SSet.yonedaEquiv.symm x, fun j hj ↦ by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, hx, Equiv.symm_apply_apply]⟩
  obtain _ | _ | _ | m := n
  · -- The horn `Λ[1, i]` is a single vertex, filled by a degenerate edge.
    fin_cases i
    · refine of_simplex ((nerve C).σ 0 (SSet.yonedaEquiv (f 1 (by decide)))) fun j hj ↦ ?_
      fin_cases j
      exacts [absurd rfl hj, δ_comp_σ_succ_apply 0 _]
    · refine of_simplex ((nerve C).σ 0 (SSet.yonedaEquiv (f 0 (by decide)))) fun j hj ↦ ?_
      fin_cases j
      exacts [δ_comp_σ_self_apply 0 _, absurd rfl hj]
  all_goals
    -- Two faces of the family agree on their common face.
    have compat (j k : Fin _) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k) :=
      congrArg SSet.yonedaEquiv (hf.δ_pred_comp j k hj hk hjk)
    simp only [stdSimplex.yonedaEquiv_δ_comp] at compat
  · -- Horns of dimension `2`: the inner horn is filled since the nerve is a quasicategory.
    fin_cases i
    · obtain ⟨x, h₁, h₂⟩ := exists_horn₂₀ _ _ (compat 1 2 (by decide) (by decide) (by decide))
      refine of_simplex x fun j hj ↦ ?_
      fin_cases j
      exacts [absurd rfl hj, h₁, h₂]
    · obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling (by decide) (by decide) hf.desc
      exact of_horn σ hσ.symm
    · obtain ⟨x, h₀, h₁⟩ := exists_horn₂₂ _ _ (compat 0 1 (by decide) (by decide) (by decide))
      refine of_simplex x fun j hj ↦ ?_
      fin_cases j
      exacts [h₀, h₁, absurd rfl hj]
  · -- Horns of dimension `3`: the inner horns are filled since the nerve is a quasicategory.
    fin_cases i
    · obtain ⟨x, h₁, h₂, h₃⟩ := exists_horn₃₀ _ _ _
        (compat 1 2 (by decide) (by decide) (by decide))
        (compat 1 3 (by decide) (by decide) (by decide))
        (compat 2 3 (by decide) (by decide) (by decide))
      refine of_simplex x fun j hj ↦ ?_
      fin_cases j
      exacts [absurd rfl hj, h₁, h₂, h₃]
    · obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling (by decide) (by decide) hf.desc
      exact of_horn σ hσ.symm
    · obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling (by decide) (by decide) hf.desc
      exact of_horn σ hσ.symm
    · obtain ⟨x, h₀, h₁, h₂⟩ := exists_horn₃₃ _ _ _
        (compat 0 1 (by decide) (by decide) (by decide))
        (compat 0 2 (by decide) (by decide) (by decide))
        (compat 1 2 (by decide) (by decide) (by decide))
      refine of_simplex x fun j hj ↦ ?_
      fin_cases j
      exacts [h₀, h₁, h₂, absurd rfl hj]
  · -- Horns of dimension at least `4` are filled since the nerve is `2`-coskeletal.
    obtain ⟨σ, hσ, -⟩ := existsUnique_horn_extension_of_isCoskeletal (k := 2) (by omega) i hf.desc
    exact of_horn σ hσ

end

/-- The nerve of a category is a Kan complex exactly when the category is a groupoid: in a Kan
complex every edge is an equivalence. -/
theorem kanComplex_iff : KanComplex (nerve C) ↔ IsGroupoid C :=
  ⟨fun _ ↦ ⟨fun f ↦ (isEquivalence_edgeMk_iff f).1 (Edge.isEquivalence_of_kanComplex _)⟩,
    fun _ ↦ inferInstance⟩

end CategoryTheory.nerve
