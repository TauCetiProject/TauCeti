/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
public import TauCeti.AlgebraicTopology.SimplicialSet.BoundaryColimits

/-!
# Strict Segal simplicial sets

In a strict Segal simplicial set, such as the nerve of a category, a simplex is determined by its
spine (Mathlib's `SSet.IsStrictSegal`), so it is determined by its simplices of dimension at most
two. This file records consequences of this.

A simplicial operator fixes a simplex as soon as it fixes every edge of its spine. A simplex of
dimension at least two is determined by its first and last faces, which together contain its
spine. Every map from the boundary `∂Δ[n]` with `n ≥ 3` extends to `Δ[n]`: fill the inner horn
`Λ[n, 1]` and observe that the missing face is forced by the others. In dimensions one and two
this fails in general: two vertices need not be joined by an edge, and the third edge of the
boundary of a triangle need not be the composite of the other two.

## Main results

* `SSet.map_eq_of_isStrictSegal`: an `(n + 1)`-simplex whose face opposite to the last vertex is
  constant at a vertex is fixed by any operator that fixes its last edge and collapses the other
  edges of its spine to the vertex `n`.
* `SSet.IsStrictSegal.ext_of_δ_zero_of_δ_last`: a simplex of dimension at least two is determined
  by its first and last faces.
* `SSet.IsStrictSegal.exists_boundary_extension`: every map `∂Δ[n + 3] ⟶ X` extends to
  `Δ[n + 3]`.
-/

public section

open CategoryTheory Opposite Simplicial SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}} [X.IsStrictSegal]

/-- In a strict Segal simplicial set, an `(n + 1)`-simplex whose face opposite to the last vertex
is constant at `x` is fixed by any operator `r` that fixes the last edge and sends every other
edge of the spine to the vertex `n`. -/
theorem map_eq_of_isStrictSegal {n : ℕ} (r : ⦋n + 1⦌ ⟶ ⦋n + 1⦌)
    (hlast : mkOfSucc (Fin.last n) ≫ r = mkOfSucc (Fin.last n))
    (hcast : ∀ j : Fin n, mkOfSucc j.castSucc ≫ r =
      SimplexCategory.const ⦋1⦌ ⦋n⦌ (Fin.last n) ≫ δ (Fin.last (n + 1)))
    {x : X _⦋0⦌} (σ : X _⦋n + 1⦌)
    (hσ : X.δ (Fin.last (n + 1)) σ = X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x) :
    X.map r.op σ = σ := by
  refine (IsStrictSegal.segal (X := X) (n + 1)).injective (Path.ext' fun i ↦ ?_)
  rw [spine_arrow, spine_arrow, ← Functor.map_comp_apply, ← op_comp]
  cases i using Fin.lastCases with
  | last => rw [hlast]
  | cast j =>
    -- Both edges lie in the face opposite to the last vertex, which is constant at `x`.
    rw [hcast, ← mkOfSucc_δ_lt (Fin.castSucc_lt_last _), op_comp, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply]
    -- `X.δ i` is by definition `X.map (δ i).op`; `change` exposes the face to rewrite with `hσ`.
    change X.map _ (X.δ _ σ) = X.map _ (X.δ _ σ)
    -- Both sides are now pullbacks of the totally degenerate simplex at `x`.
    have key (f : ⦋1⦌ ⟶ ⦋n⦌) : X.map f.op (X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x) =
        X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x := by
      rw [← Functor.map_comp_apply, ← op_comp, Subsingleton.elim (f ≫ _)]
    rw [hσ, key, key]

namespace IsStrictSegal

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
