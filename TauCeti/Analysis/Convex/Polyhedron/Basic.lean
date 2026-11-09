/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Convex polyhedra

A *convex polyhedron* in a real topological vector space is the solution set of finitely many
non-strict affine inequalities `g i x ≤ 0`, the `g i` being continuous affine functionals. This
file introduces that predicate and the three closure properties a piecewise-linear calculus needs:
a convex polyhedron is closed and convex, a finite intersection of convex polyhedra is one, and
the preimage of one under a continuous affine map is one.

Those last two are exactly what makes the cells of a piecewise-affine decomposition composable:
composing two piecewise-affine maps refines the source decomposition by pulling the target cells
back along the affine pieces, and both operations must stay inside the class of cells.

Near each of its points a convex polyhedron is a translate of a polyhedral cone, cut out by the
inequalities that are equalities at the point. This is what makes the germ of a piecewise-affine
map at a point conical.

The name is deliberately *not* `IsPolyhedron`. In piecewise-linear topology a polyhedron is a
much weaker notion — a subset that is locally a cone, so a locally finite union of simplices,
which need not be convex. The convex sets defined here are the *cells* out of which such a
polyhedron is assembled.

## Main definitions

* `TauCeti.IsConvexPolyhedron`: the solution set of finitely many non-strict affine inequalities.

## Main results

* `TauCeti.isConvexPolyhedron_setOf_forall`: the defining form, with the inequalities indexed by
  an arbitrary finite type rather than by `Fin n`.
* `TauCeti.IsConvexPolyhedron.isClosed` and `TauCeti.IsConvexPolyhedron.convex`: a convex
  polyhedron is closed and convex, which is what its name claims.
* `TauCeti.IsConvexPolyhedron.inter`: an intersection of two convex polyhedra is one.
* `TauCeti.IsConvexPolyhedron.preimage`: the preimage of a convex polyhedron under a continuous
  affine map is one.
* `TauCeti.IsConvexPolyhedron.exists_cone`: near each of its points, a convex polyhedron is the
  translate of a polyhedral cone.
-/

public section

open Set Topology

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {s t : Set E}

/-- A *convex polyhedron* is the solution set of finitely many non-strict affine inequalities,
the inequalities being given by continuous affine functionals. -/
def IsConvexPolyhedron (s : Set E) : Prop :=
  ∃ (n : ℕ) (g : Fin n → (E →ᴬ[ℝ] ℝ)), s = {x | ∀ i, g i x ≤ 0}

/-- The finite affine inequalities characterizing a convex polyhedron. -/
theorem isConvexPolyhedron_iff :
    IsConvexPolyhedron s ↔
      ∃ (n : ℕ) (g : Fin n → (E →ᴬ[ℝ] ℝ)), s = {x | ∀ i, g i x ≤ 0} := Iff.rfl

/-- The solution set of a finite family of non-strict affine inequalities, indexed by an arbitrary
finite type, is a convex polyhedron. This is the form in which the definition is used: the
constructions below produce their inequalities indexed by sums and products of index types. -/
theorem isConvexPolyhedron_setOf_forall {ι : Type*} [Finite ι] (g : ι → (E →ᴬ[ℝ] ℝ)) :
    IsConvexPolyhedron {x : E | ∀ i, g i x ≤ 0} := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact ⟨n, g ∘ e.symm, by simp [e.symm.forall_congr_left]⟩

/-- A single non-strict affine inequality cuts out a convex polyhedron. -/
theorem isConvexPolyhedron_setOf_le (g : E →ᴬ[ℝ] ℝ) : IsConvexPolyhedron {x : E | g x ≤ 0} :=
  ⟨1, fun _ => g, by ext x; simp⟩

/-- The whole space is a convex polyhedron: it is cut out by the empty family of inequalities. -/
theorem isConvexPolyhedron_univ : IsConvexPolyhedron (univ : Set E) :=
  ⟨0, Fin.elim0, by ext x; simp⟩

/-- A convex polyhedron is closed, being an intersection of preimages of `Set.Iic 0` under
continuous maps. -/
theorem IsConvexPolyhedron.isClosed (h : IsConvexPolyhedron s) : IsClosed s := by
  obtain ⟨n, g, rfl⟩ := h
  rw [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (g i).continuous continuous_const

/-- A convex polyhedron is convex, being an intersection of preimages of `Set.Iic 0` under
affine maps. -/
theorem IsConvexPolyhedron.convex (h : IsConvexPolyhedron s) : Convex ℝ s := by
  obtain ⟨n, g, rfl⟩ := h
  rw [ofPred_forall]
  exact convex_iInter fun i => (convex_Iic 0).affine_preimage (g i).toAffineMap

/-- An intersection of two convex polyhedra is a convex polyhedron: concatenate the two families
of defining inequalities. -/
theorem IsConvexPolyhedron.inter (hs : IsConvexPolyhedron s) (ht : IsConvexPolyhedron t) :
    IsConvexPolyhedron (s ∩ t) := by
  obtain ⟨n, g, rfl⟩ := hs
  obtain ⟨m, h, rfl⟩ := ht
  simpa [Sum.forall, ofPred_and] using isConvexPolyhedron_setOf_forall (Sum.elim g h)

/-- The preimage of a convex polyhedron under a continuous affine map is a convex polyhedron:
precompose each defining inequality with the map. -/
theorem IsConvexPolyhedron.preimage {u : Set F} (hu : IsConvexPolyhedron u) (A : E →ᴬ[ℝ] F) :
    IsConvexPolyhedron (A ⁻¹' u) := by
  obtain ⟨n, g, rfl⟩ := hu
  exact ⟨n, fun i => (g i).comp A, by ext x; simp⟩

/-- **A convex polyhedron is a cone near each of its points.** For a point `x` of a convex
polyhedron `s` there is a convex polyhedron `K` which is a cone (closed under multiplication by
nonnegative scalars) such that `s` lies in the translate `x + K`, and agrees with it near `x`.
The cone is cut out by the linear parts of the inequalities of `s` that are equalities at `x`;
the other inequalities are strict at `x`, so they still hold near `x`. -/
theorem IsConvexPolyhedron.exists_cone [IsTopologicalAddGroup E] {x : E}
    (hs : IsConvexPolyhedron s) (hx : x ∈ s) :
    ∃ K : Set E, IsConvexPolyhedron K ∧ (∀ c : ℝ, 0 ≤ c → ∀ v ∈ K, c • v ∈ K) ∧
      (∀ y ∈ s, y - x ∈ K) ∧ ∀ᶠ y in 𝓝 x, y - x ∈ K → y ∈ s := by
  obtain ⟨n, g, rfl⟩ := hs
  -- The inequalities that are equalities at `x`, read through their linear parts.
  let ℓ (i : {i // g i x = 0}) : E →ᴬ[ℝ] ℝ := (g i).contLinear.toContinuousAffineMap
  have hℓ (i : {i // g i x = 0}) (y : E) : ℓ i (y - x) = g i y := by
    simpa [ℓ, i.2] using (g i).contLinear_apply_vsub y x
  refine ⟨{v | ∀ i, ℓ i v ≤ 0}, isConvexPolyhedron_setOf_forall ℓ, fun c hc v hv i => ?_,
    fun y hy i => (hℓ i y).symm ▸ hy i, ?_⟩
  · simpa [ℓ] using mul_nonpos_of_nonneg_of_nonpos hc (hv i)
  -- The remaining inequalities are strict at `x`, hence near `x`.
  have hstrict : ∀ᶠ y in 𝓝 x, ∀ i, g i x ≠ 0 → g i y < 0 :=
    Filter.eventually_all.2 fun i => Filter.eventually_imp_distrib_left.2 fun hi =>
      (g i).continuous.continuousAt.eventually_lt continuousAt_const ((hx i).lt_of_ne hi)
  filter_upwards [hstrict] with y hy hyK i
  by_cases hi : g i x = 0
  · exact hℓ ⟨i, hi⟩ y ▸ hyK ⟨i, hi⟩
  · exact (hy i hi).le

end TauCeti
