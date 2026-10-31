/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
public import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits

/-!
# Boundaries in strict Segal simplicial sets

A strict Segal simplicial set, such as the nerve of a category, is determined by its simplices of
dimension at most two: a simplex is determined by its spine. This file records two consequences.
A simplex of dimension at least two is determined by its first and last faces, which together
contain its spine (`SSet.IsStrictSegal.ext_of_δ_zero_of_δ_last`). Every map from the boundary
`∂Δ[n]` with `n ≥ 3` extends to `Δ[n]` (`SSet.IsStrictSegal.exists_boundary_extension`): fill
the inner horn `Λ[n, 1]` and observe that the missing face is forced by the others. In dimensions
one and two this fails, as the boundary of an edge or a triangle prescribes no composite.
-/

public section

universe u

namespace SSet

open CategoryTheory Simplicial

namespace IsStrictSegal

variable {X : SSet.{u}} [X.IsStrictSegal]

/-- In a strict Segal simplicial set, a simplex of dimension at least two is determined by its
first and last faces, which together contain its spine. -/
lemma ext_of_δ_zero_of_δ_last {n : ℕ} {x y : X _⦋n + 2⦌}
    (h₀ : X.δ 0 x = X.δ 0 y) (hl : X.δ (Fin.last _) x = X.δ (Fin.last _) y) : x = y := by
  have sx := StrictSegal.ofIsStrictSegal X
  apply (IsStrictSegal.segal (X := X) _).injective
  refine Path.ext' fun i ↦ ?_
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · have hx := sx.spine_δ_arrow_lt (X.spine _ x) (i := i) (j := Fin.last _)
      (Fin.lt_def.2 (by simp; omega))
    have hy := sx.spine_δ_arrow_lt (X.spine _ y) (i := i) (j := Fin.last _)
      (Fin.lt_def.2 (by simp; omega))
    simp only [StrictSegal.spineToSimplex_spine_apply] at hx hy
    exact hx.symm.trans ((congrArg (fun z ↦ (X.spine _ z).arrow i) hl).trans hy)
  · have hx := sx.spine_δ_arrow_gt (X.spine _ x) (i := Fin.last n) (j := 0)
      (Fin.lt_def.2 (by simp))
    have hy := sx.spine_δ_arrow_gt (X.spine _ y) (i := Fin.last n) (j := 0)
      (Fin.lt_def.2 (by simp))
    simp only [StrictSegal.spineToSimplex_spine_apply] at hx hy
    rw [← Fin.succ_last]
    exact hx.symm.trans ((congrArg (fun z ↦ (X.spine _ z).arrow (Fin.last n)) h₀).trans hy)

/-- In a strict Segal simplicial set, every map from the boundary `∂Δ[n + 3]` extends to
`Δ[n + 3]`. -/
lemma exists_boundary_extension {n : ℕ} (σ₀ : (∂Δ[n + 3] : SSet) ⟶ X) :
    ∃ σ : Δ[n + 3] ⟶ X, σ₀ = ∂Δ[n + 3].ι ≫ σ := by
  have hΛ : Λ[n + 3, 1] ≤ ∂Δ[n + 3] := by
    rw [horn_eq_iSup, boundary_eq_iSup]
    exact iSup_le fun j ↦ le_iSup (fun k : Fin (n + 4) ↦ stdSimplex.face {k}ᶜ) j.1
  obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling (n := n + 3) (i := 1) (Fin.lt_def.2 (by simp))
    (Fin.lt_def.2 (by simp)) (Subcomplex.homOfLE hΛ ≫ σ₀)
  refine ⟨σ, ?_⟩
  -- The faces of `σ₀` and of the restriction of `σ` agree away from the face `1`.
  have hface (j : Fin (n + 4)) (hj : j ≠ 1) : boundary.ι j ≫ σ₀ = stdSimplex.δ j ≫ σ := by
    have : boundary.ι j = horn.ι 1 j hj ≫ Subcomplex.homOfLE hΛ := by
      rw [← cancel_mono (∂Δ[n + 3]).ι]
      simp
    rw [this, Category.assoc, hσ, horn.ι_ι_assoc]
  have h01 : (0 : Fin (n + 4)) < 1 := Fin.lt_def.2 (by simp)
  have h1l : (1 : Fin (n + 4)) < Fin.last _ := Fin.lt_def.2 (by simp)
  have h₀ := (boundary.IsCompatible.of_hom σ₀).δ_pred_comp 0 1 h01
  have hl := (boundary.IsCompatible.of_hom σ₀).δ_pred_comp 1 (Fin.last _) h1l
  have h₀' := (boundary.IsCompatible.of_hom (∂Δ[n + 3].ι ≫ σ)).δ_pred_comp 0 1 h01
  have hl' := (boundary.IsCompatible.of_hom (∂Δ[n + 3].ι ≫ σ)).δ_pred_comp 1 (Fin.last _) h1l
  simp only [boundary.ι_ι_assoc] at h₀' hl'
  refine boundary.hom_ext fun j ↦ ?_
  by_cases hj : j = 1
  · subst hj
    rw [boundary.ι_ι_assoc]
    -- The remaining face is determined by its first and last faces.
    apply yonedaEquiv.injective
    apply ext_of_δ_zero_of_δ_last
    · rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
      congr 1
      simp only [Fin.castPred_zero] at h₀ h₀'
      rw [← h₀, ← h₀', hface 0 (by simp)]
    · rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
      congr 1
      rw [hface (Fin.last _) (by simp [Fin.ext_iff])] at hl
      simpa only [Fin.pred_last] using hl.trans hl'.symm
  · rw [hface j hj, boundary.ι_ι_assoc]

end IsStrictSegal

end SSet
