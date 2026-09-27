/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import TauCeti.Geometry.Manifold.Boundary.Collar.Basic

/-!
# A global collar for the Euclidean half-space

The standard half-space has an explicit collar of its boundary: split off the zeroth coordinate
and restrict the inward normal to the open interval `[0, 1)`.  The arbitrary-manifold collar
theorem still has to patch the local product collars from `Boundary.Collar.Diffeomorph`.

The construction reuses Mathlib's `IccLeftChart` to identify `[0, 1)` with the one-dimensional
half-space, and Tau Ceti's `EuclideanHalfSpace.collarDiffeomorph` for the product identification.

## Main results

* `EuclideanHalfSpace.isCollar_boundaryParam`: the standard boundary parametrization admits the
  explicit collar obtained from the product half-space diffeomorphism.
* `EuclideanHalfSpace.isCollared_boundaryParam`: the corresponding existential statement.
-/

public section

noncomputable section

open Function Set Topology WithLp

open scoped Manifold

namespace TauCeti.EuclideanHalfSpace

private noncomputable def depthSourceHomeomorph :
    Ico (0 : ℝ) 1 ≃ₜ {z : Icc (0 : ℝ) 1 // z ∈ (IccLeftChart 0 1).source} := by
  letI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  let e := IccLeftChart 0 1
  exact
    { toFun := fun t ↦
        ⟨⟨t, ⟨t.2.1, t.2.2.le⟩⟩, by
          -- The source of `IccLeftChart` is the open part `z < 1` of `Icc 0 1`.
          change (t : ℝ) < 1
          exact t.2.2⟩
      invFun := fun z ↦
        ⟨z.1, ⟨z.1.2.1, by
          -- Unfolding the chart source exposes its defining strict inequality.
          change (z.1 : ℝ) < 1
          exact z.2⟩⟩
      left_inv := by
        intro t
        rfl
      right_inv := by
        intro z
        rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

private noncomputable def depthEmbedding : Ico (0 : ℝ) 1 → EuclideanHalfSpace 1 := by
  letI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  let e := IccLeftChart 0 1
  exact e.source.domRestrict e ∘ depthSourceHomeomorph

private theorem depthEmbedding_isOpenEmbedding : IsOpenEmbedding depthEmbedding := by
  let e := IccLeftChart 0 1
  exact e.isOpenEmbedding_restrict.comp depthSourceHomeomorph.isOpenEmbedding

private theorem depthEmbedding_apply_zero :
    depthEmbedding ⟨0, by norm_num⟩ = (0 : EuclideanHalfSpace 1) := by
  -- `depthEmbedding` is a composition through the chart source subtype; expose that subtype
  -- before evaluating the chart at the zero normal coordinate.
  change IccLeftChart 0 1
    (⟨(⟨(0 : ℝ), ⟨by norm_num, by norm_num⟩⟩ : Icc (0 : ℝ) 1),
      by change (0 : ℝ) < 1; norm_num⟩ :
      {z : Icc (0 : ℝ) 1 // z ∈ (IccLeftChart 0 1).source}) = _
  apply Subtype.ext
  ext i
  rw [Subsingleton.elim i 0]
  rw [IccLeftChart_apply]
  simp only [sub_zero]
  change (0 : ℝ) = (0 : EuclideanSpace ℝ (Fin 1)) 0
  rfl

/-- The explicit collar map of the standard half-space boundary. -/
noncomputable def boundaryCollar (n : ℕ) :
    EuclideanSpace ℝ (Fin n) × Ico (0 : ℝ) 1 → EuclideanHalfSpace (n + 1) :=
  EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n ∘
    Prod.map id depthEmbedding

theorem boundaryCollar_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    boundaryCollar n (x, ⟨0, by norm_num⟩) = EuclideanHalfSpace.boundaryParam n x := by
  have hzero := depthEmbedding_apply_zero
  rw [boundaryCollar, Function.comp_apply, Prod.map_apply, hzero]
  exact EuclideanHalfSpace.collarDiffeomorph_apply_zero_eq_boundaryParam n x

theorem isCollar_boundaryParam (n : ℕ) :
    IsCollar (EuclideanHalfSpace.boundaryParam n) (boundaryCollar n) := by
  refine ⟨?_, boundaryCollar_apply_zero n⟩
  apply (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).toHomeomorph.isOpenEmbedding.comp
  exact IsOpenEmbedding.id.prodMap depthEmbedding_isOpenEmbedding

theorem isCollared_boundaryParam (n : ℕ) :
    IsCollared (EuclideanHalfSpace.boundaryParam n) :=
  (isCollar_boundaryParam n).isCollared

end TauCeti.EuclideanHalfSpace

end
