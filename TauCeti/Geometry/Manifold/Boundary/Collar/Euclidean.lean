/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# A global collar for the Euclidean half-space

The standard half-space has an explicit collar of its boundary: split off the zeroth coordinate
and restrict the inward normal to the half-open interval `[0, 1)`.  This model collar supplies the
standard-coordinate input for local-to-global collar constructions on manifolds with boundary.

The construction reuses Tau Ceti's `EuclideanHalfSpace.homeomorphNormalIio` to identify `[0, 1)`
with the initial segment of the one-dimensional half-space, and
`EuclideanHalfSpace.collarDiffeomorph` for the product identification.

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

private noncomputable def depthEmbedding : Ico (0 : ℝ) 1 → EuclideanHalfSpace 1 :=
  (fun t : ↥(normalIio 1) ↦ (t : EuclideanHalfSpace 1)) ∘
    (homeomorphNormalIio 1).symm

private theorem depthEmbedding_isOpenEmbedding : IsOpenEmbedding depthEmbedding := by
  exact (isOpen_normalIio 1).isOpenEmbedding_subtypeVal.comp
    (homeomorphNormalIio 1).symm.isOpenEmbedding

private theorem depthEmbedding_apply (t : Ico (0 : ℝ) 1) :
    (depthEmbedding t).1 0 = t := by
  rw [depthEmbedding, Function.comp_apply, ← coe_homeomorphNormalIio]
  exact congrArg (fun s : Ico (0 : ℝ) 1 ↦ (s : ℝ))
    ((homeomorphNormalIio 1).apply_symm_apply t)

private theorem depthEmbedding_apply_zero :
    depthEmbedding (0 : Ico (0 : ℝ) 1) = (0 : EuclideanHalfSpace 1) := by
  apply Subtype.ext
  apply (WithLp.ext_iff _).2
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rw [depthEmbedding, Function.comp_apply, ← coe_homeomorphNormalIio]
  exact congrArg (fun s : Ico (0 : ℝ) 1 ↦ (s : ℝ))
    ((homeomorphNormalIio 1).apply_symm_apply (0 : Ico (0 : ℝ) 1))

/-- The explicit collar map of the standard half-space boundary. -/
noncomputable def boundaryCollar (n : ℕ) :
    EuclideanSpace ℝ (Fin n) × Ico (0 : ℝ) 1 → EuclideanHalfSpace (n + 1) :=
  EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n ∘
    Prod.map id depthEmbedding

/-- The zero-depth slice of the explicit collar is the boundary parametrization. -/
@[simp] theorem boundaryCollar_apply_zero_eq_boundaryParam (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    boundaryCollar n (x, (0 : Ico (0 : ℝ) 1)) = EuclideanHalfSpace.boundaryParam n x := by
  have hzero := depthEmbedding_apply_zero
  rw [boundaryCollar, Function.comp_apply, Prod.map_apply, hzero]
  exact EuclideanHalfSpace.collarDiffeomorph_apply_zero_eq_boundaryParam n x

/-- The normal coordinate of the explicit collar is its depth parameter. -/
@[simp] theorem boundaryCollar_apply_zero (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (t : Ico (0 : ℝ) 1) :
    (boundaryCollar n (x, t)).1 0 = (t : ℝ) := by
  rw [boundaryCollar, Function.comp_apply, Prod.map_apply,
    EuclideanHalfSpace.collarDiffeomorph_apply_zero]
  exact depthEmbedding_apply t

/-- The positive coordinates of the explicit collar are its boundary parameters. -/
@[simp] theorem boundaryCollar_apply_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (t : Ico (0 : ℝ) 1) (i : Fin n) :
    (boundaryCollar n (x, t)).1 i.succ = x i := by
  rw [boundaryCollar, Function.comp_apply, Prod.map_apply,
    EuclideanHalfSpace.collarDiffeomorph_apply_succ]
  rfl

/-- The collar image is exactly the half-space region with normal coordinate below one. -/
theorem mem_range_boundaryCollar_iff (n : ℕ)
    {p : EuclideanHalfSpace (n + 1)} :
    p ∈ range (boundaryCollar n) ↔ p.1 0 < 1 := by
  constructor
  · rintro ⟨⟨x, t⟩, rfl⟩
    simpa only [boundaryCollar_apply_zero] using t.2.2
  · intro hp
    let t : Ico (0 : ℝ) 1 := ⟨p.1 0, p.2, hp⟩
    refine ⟨(boundaryProj n p, t), ?_⟩
    apply Subtype.ext
    apply (WithLp.ext_iff _).2
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [t]
    · simp [t]

/-- The explicit map `boundaryCollar n` is a collar of the standard half-space boundary
parametrization. -/
theorem isCollar_boundaryParam (n : ℕ) :
    IsCollar (EuclideanHalfSpace.boundaryParam n) (boundaryCollar n) := by
  refine ⟨?_, boundaryCollar_apply_zero_eq_boundaryParam n⟩
  apply (EuclideanHalfSpace.collarDiffeomorph (k := ⊤) n).toHomeomorph.isOpenEmbedding.comp
  exact IsOpenEmbedding.id.prodMap depthEmbedding_isOpenEmbedding

/-- The standard half-space boundary parametrization admits a collar. -/
theorem isCollared_boundaryParam (n : ℕ) :
    IsCollared (EuclideanHalfSpace.boundaryParam n) :=
  (isCollar_boundaryParam n).isCollared

end TauCeti.EuclideanHalfSpace

end
