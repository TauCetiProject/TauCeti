/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Bases selected from mapped generating families

For a family of linear maps, a basis of the sum of the images of given spans can be chosen
from the images of the generators themselves. Index the basis in blocks by the maps from which
its vectors come. This makes it possible to use pointwise bounds on the generators and, for the
same basis, bounds on whole blocks belonging to an individual map.

This is the linear-algebra selection used in `New.star_inequality` in
`grh/src/New/Reduction/MainInequality.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Module Set

namespace TauCeti

/-- Choose a basis of the sum of the images of the spans of `s i`, grouped by the originating map
`f i`. Each basis vector is the image of an actual generator in `s i`, not a linear combination
of generators. Only the sum of images needs to be finite-dimensional. -/
theorem exists_basis_iSup_map {K ι W : Type*} [DivisionRing K] [AddCommMonoid W] [Module K W]
    {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    (f : ∀ i, V i →ₗ[K] W) (s : ∀ i, Set (V i))
    [Module.Finite K (⨆ i, (Submodule.span K (s i)).map (f i) : Submodule K W)] :
    ∃ (n : ι → ℕ)
      (b : Basis (Σ i, Fin (n i)) K (⨆ i, (Submodule.span K (s i)).map (f i) : Submodule K W))
      (v : ∀ i, Fin (n i) → s i), ∀ i j, (b ⟨i, j⟩ : W) = f i (v i j) := by
  classical
  let g : (Σ i, s i) → W := fun p ↦ f p.1 p.2
  have hg : Submodule.span K (range g) = ⨆ i, (Submodule.span K (s i)).map (f i) := by
    rw [range_sigma_eq_iUnion_range, Submodule.span_iUnion]
    exact iSup_congr fun i ↦ by
      rw [← Submodule.span_image]
      exact congrArg (Submodule.span K) (image_eq_range (f i : V i → W) (s i)).symm
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  obtain ⟨κ, a, -, haSpan, haIndep⟩ := exists_linearIndependent' K g
  let b := Basis.ofSpanEq haIndep (haSpan.trans hg)
  have : Finite κ := b.linearIndependent.finite
  -- Reindex the independent extraction by the fibres of its originating-map label.
  let label : κ → ι := fun k ↦ (a k).1
  let (i : ι) := Fintype.ofFinite {k // label k = i}
  let n (i : ι) := Fintype.card {k // label k = i}
  let e (i : ι) : Fin (n i) ≃ {k // label k = i} := (Fintype.equivFin _).symm
  let E : (Σ i, Fin (n i)) ≃ κ := (Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv label)
  let v (i : ι) (j : Fin (n i)) : s i := (e i j).property ▸ (a (e i j)).2
  refine ⟨n, b.reindex E.symm, v, ?_⟩
  intro i j
  rw [Basis.reindex_apply, Equiv.symm_symm, Basis.coe_ofSpanEq]
  have apply_eq (p : Σ i, s i) (i : ι) (h : p.1 = i) : g p = f i (↑(h ▸ p.2 : s i)) := by
    subst i
    rfl
  have hE : E ⟨i, j⟩ = (e i j : κ) := rfl
  simpa only [hE, Function.comp_apply, v] using apply_eq (a (e i j)) i (e i j).property

end TauCeti
