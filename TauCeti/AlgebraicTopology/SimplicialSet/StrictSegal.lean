/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Simplicial operators on strict Segal simplicial sets

In a strict Segal simplicial set, such as the nerve of a category, a simplex is determined by its
spine (Mathlib's `SSet.IsStrictSegal`). Hence a simplicial operator fixes a simplex as soon as it
fixes every edge of its spine. Since every inner horn contains the spine of the standard simplex,
a map from a standard simplex to a strict Segal simplicial set is determined by its restriction to
an inner horn, so any map from a quasicategory to a strict Segal simplicial set is an inner
fibration. In particular the nerve of every functor is an inner fibration. The inner horn
containing the spine is Mathlib's `SSet.horn.spineId`, as in Mathlib's proof
`SSet.StrictSegal.quasicategory` that strict Segal simplicial sets are quasicategories.

## Main results

* `SSet.map_eq_of_isStrictSegal`: an `(n + 1)`-simplex whose face opposite to the last vertex is
  constant at a vertex is fixed by any operator that fixes its last edge and collapses the other
  edges of its spine to the vertex `n`.
* `SSet.IsStrictSegal.hom_ext_of_innerHorn`: maps from `Δ[n + 2]` to a strict Segal simplicial
  set agree as soon as they agree on an inner horn.
* `SSet.innerFibration_of_isStrictSegal`: a map from a quasicategory to a strict Segal simplicial
  set is an inner fibration.
-/

public section

open CategoryTheory Opposite Simplicial SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}} [X.IsStrictSegal]

/-- Two maps from `Δ[n + 2]` to a strict Segal simplicial set agree as soon as they agree on an
inner horn: the inner horn contains the spine of `Δ[n + 2]`. -/
theorem IsStrictSegal.hom_ext_of_innerHorn {n : ℕ} {i : Fin (n + 3)} (h₀ : 0 < i)
    (hₙ : i < Fin.last (n + 2)) {f g : Δ[n + 2] ⟶ X}
    (h : Λ[n + 2, i].ι ≫ f = Λ[n + 2, i].ι ≫ g) : f = g := by
  have key (f : Δ[n + 2] ⟶ X) :
      X.spine (n + 2) (yonedaEquiv f) = (horn.spineId i h₀ hₙ).map (Λ[n + 2, i].ι ≫ f) := by
    ext k
    rw [spine_arrow, yonedaEquiv_naturality, yonedaEquiv_comp]
    -- Both sides are the image under `f` of the edge `mkOfSucc k` of `Δ[n + 2]`.
    rfl
  exact yonedaEquiv.injective ((IsStrictSegal.segal (n + 2)).injective (by rw [key, key, h]))

/-- A map from a quasicategory to a strict Segal simplicial set is an inner fibration: inner horns
fill in the source, and the filler lies over the given simplex because simplices of the target
are determined by their restrictions to inner horns. -/
instance innerFibration_of_isStrictSegal {W : SSet.{u}} [Quasicategory W] (p : W ⟶ X) :
    InnerFibration p where
  mem _ _ _ := fun ⟨_, h₀, hₙ⟩ ↦ ⟨fun {a _} sq ↦ by
    obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling h₀ hₙ a
    refine ⟨⟨{ l := σ
               fac_left := hσ.symm
               fac_right := IsStrictSegal.hom_ext_of_innerHorn h₀ hₙ ?_ }⟩⟩
    rw [← Category.assoc, ← hσ, sq.w]⟩

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

end SSet
