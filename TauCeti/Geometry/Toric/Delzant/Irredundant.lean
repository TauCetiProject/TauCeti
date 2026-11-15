/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Irredundant
public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic
public import TauCeti.Geometry.Toric.Delzant.Basic

import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# A Delzant polytope determines its presentation

Let `i : N →+ V` be an integral lattice. A Delzant presentation `(u, c)` lists the inward facet
normals `u j ∈ N` and the support constants `c j` of a Delzant polytope
`Δ = {x ∈ V* | c j ≤ ⟨x, u j⟩ for every j}` (`TauCeti.Toric.IsDelzant`). This file proves that
the polytope recovers the presentation: two Delzant presentations, indexed by finite types,
describe the same polytope exactly when one is a relabelling of the other
(`TauCeti.Toric.IsDelzant.facetPolyhedron_eq_iff`). So the facets of a Delzant polytope, their
primitive inward normals and their support constants are well defined, independently of how the
polytope was presented. This is what makes the Delzant construction and the moment-polytope
invariant of a symplectic toric manifold depend only on the polytope.

The proof combines two facts. An irredundant presentation of a polyhedron by nonzero functionals
is unique up to relabelling and positive rescaling of the constraints
(`TauCeti.polyhedron_eq_iff_exists_equiv`); the constraints of a Delzant presentation are
irredundant by definition and nonzero because their normals are primitive. A positive rescaling
of one primitive lattice vector into another is the identity
(`TauCeti.Toric.IsIntegralLattice.eq_of_isPrimitive_of_eq_smul`), so the rescaling factors are
all `1`.

## Main results

* `TauCeti.Toric.IsDelzant.facetPolyhedron_eq_iff`: two finite Delzant presentations in an
  integral lattice describe the same polytope exactly when they agree up to relabelling.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
-/

public section

namespace TauCeti.Toric

variable {ι ι' N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ} {u' : ι' → N} {c' : ι' → ℝ}

namespace IsDelzant

/-- **A Delzant polytope determines its presentation.** Two Delzant presentations in an integral
lattice, indexed by finite types, describe the same polytope exactly when they agree up to
relabelling the facets: same inward normals and same support constants. -/
theorem facetPolyhedron_eq_iff [Finite ι] [Finite ι'] (hi : IsIntegralLattice i)
    (hΔ : IsDelzant i u c) (hΔ' : IsDelzant i u' c') :
    facetPolyhedron i u c = facetPolyhedron i u' c' ↔
      ∃ e : ι ≃ ι', ∀ j, u' (e j) = u j ∧ c' (e j) = c j := by
  have := hi.finiteDimensional
  rw [facetPolyhedron_def, facetPolyhedron_def,
    polyhedron_eq_iff_exists_equiv (hΔ.facetPairing_ne_zero hi.injective)
      (hΔ'.facetPairing_ne_zero hi.injective)
      (by simpa only [facetPolyhedron_def] using hΔ.irredundant)
      (by simpa only [facetPolyhedron_def] using hΔ'.irredundant)]
  constructor
  · rintro ⟨e, r, h⟩
    refine ⟨e, fun j ↦ ?_⟩
    obtain ⟨hr, hu, hc⟩ := h j
    -- Matched facet pairings are positive multiples, hence so are the normals in `V`.
    have hiu : i (u' (e j)) = r j • i (u j) :=
      (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun x ↦ by
        simpa using LinearMap.congr_fun hu x
    have huj := hi.eq_of_isPrimitive_of_eq_smul (hΔ.isPrimitive j) (hΔ'.isPrimitive (e j)) hr.le
      hiu
    have hr₁ : r j = 1 :=
      smul_left_injective ℝ ((map_ne_zero_iff i hi.injective).2 (hΔ.isPrimitive j).ne_zero)
        (by simpa [huj] using hiu.symm)
    exact ⟨huj, by rw [hc, hr₁, one_mul]⟩
  · rintro ⟨e, h⟩
    refine ⟨e, 1, fun j ↦ ⟨one_pos, ?_, by simp [(h j).2]⟩⟩
    ext x
    simp [(h j).1]

end IsDelzant

end TauCeti.Toric
