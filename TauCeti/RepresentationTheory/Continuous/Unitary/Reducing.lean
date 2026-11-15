/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Reducing
public import TauCeti.RepresentationTheory.Continuous.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.RepresentationTheory.Invariants

/-!
# Invariant vectors of a finite unitary group action reduce equivariant operators

Let `π` be a unitary representation of a finite group `G` on an inner product space `E`. The
average of the action operators,

`P v = |G|⁻¹ ∑_g π g v`,

is the orthogonal projection onto the subspace `π.invariants` of fixed vectors: it fixes
invariant vectors, its values are invariant because left translation permutes `G`, and it is
symmetric because unitarity moves `π g` across the inner product as `π g⁻¹` and inversion
permutes `G` too. In particular the fixed subspace has an orthogonal projection, with no
completeness assumption on `E`.

Now let `A` be a partial linear map on `E`, typically an unbounded self-adjoint operator such as a
Laplacian, that commutes with the action: each `π g` maps `dom A` into itself and
`A (π g x) = π g (A x)`, which is to say that `π g × π g` maps the graph of `A` into itself. Then
so does the average `P × P`, since the graph is a subspace, and therefore `π.invariants`
**reduces** `A` (`LinearPMap.IsReducing`): `P` preserves `dom A` and both `π.invariants` and its
orthogonal complement are `A`-invariant. The reduced part of a self-adjoint `A` on the invariant
vectors is then self-adjoint (`LinearPMap.IsReducing.isSelfAdjoint_restrict`), so the spectral
theory of `A` restricts to `G`-invariant vectors.

This is the step used for a finite group acting freely by isometries on a closed Riemannian
manifold `X`, where the invariants of a subgroup `H` in `L²(X)` are the functions pulled back from
`X / H`: the Laplacian of `X` commutes with the action, so `L²(X)^H` reduces it.

## Main results

* `ContRepresentation.IsUnitary.hasOrthogonalProjection_invariants`: the fixed vectors of a unitary
  representation of a finite group admit an orthogonal projection.
* `ContRepresentation.IsUnitary.starProjection_invariants_apply`: that projection is the average
  `v ↦ |G|⁻¹ ∑_g π g v`.
* `ContRepresentation.IsUnitary.isReducing_invariants`: the fixed vectors reduce every partial
  linear map commuting with the action.

## References

* P. Bérard, *Transplantation et isospectralité I*, Math. Ann. 292 (1992), §II.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 1.4.
-/

public section

open scoped InnerProductSpace

namespace ContRepresentation

namespace IsUnitary

variable {𝕜 G E : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {π : ContRepresentation 𝕜 G E}

section Fintype

variable [Fintype G] [Invertible (Fintype.card G : 𝕜)]

/-- The average of the action operators of a unitary representation is symmetric. -/
private theorem inner_averageMap_left (hπ : IsUnitary π) (v w : E) :
    ⟪π.toRepresentation.averageMap v, w⟫_𝕜 = ⟪v, π.toRepresentation.averageMap w⟫_𝕜 := by
  simp only [Representation.averageMap_apply, inner_smul_left, inner_smul_right, sum_inner,
    inner_sum, toRepresentation_apply, hπ.inner_map_left]
  rw [← Fintype.sum_equiv (Equiv.inv G) _ _ fun _ ↦ rfl]
  simp [invOf_eq_inv]

/-- Averaging leaves a remainder orthogonal to the invariant vectors. -/
private theorem sub_averageMap_mem_orthogonal (hπ : IsUnitary π) (v : E) :
    v - π.toRepresentation.averageMap v ∈ π.invariantsᗮ := by
  refine (Submodule.mem_orthogonal _ _).2 fun w hw ↦ ?_
  rw [inner_sub_right, ← inner_averageMap_left hπ, π.toRepresentation.averageMap_id w hw,
    sub_self]

/-- **The average is the orthogonal projection onto the invariants.** For a unitary representation
of a finite group, the orthogonal projection onto the fixed vectors is the average
`v ↦ |G|⁻¹ ∑_g π g v` of the action operators (`Representation.averageMap_apply`). -/
theorem starProjection_invariants_apply (hπ : IsUnitary π) [π.invariants.HasOrthogonalProjection]
    (v : E) : π.invariants.starProjection v = π.toRepresentation.averageMap v :=
  Submodule.eq_starProjection_of_mem_orthogonal (π.toRepresentation.averageMap_invariant v)
    (sub_averageMap_mem_orthogonal hπ v)

end Fintype

variable [Finite G]

/-- The fixed vectors of a unitary representation of a finite group admit an orthogonal
projection, namely the average of the action operators
(`ContRepresentation.IsUnitary.starProjection_invariants_apply`). No completeness is needed. -/
theorem hasOrthogonalProjection_invariants (hπ : IsUnitary π) :
    π.invariants.HasOrthogonalProjection := by
  have := Fintype.ofFinite G
  have : Invertible (Fintype.card G : 𝕜) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  exact ⟨fun v ↦ ⟨_, π.toRepresentation.averageMap_invariant v,
    sub_averageMap_mem_orthogonal hπ v⟩⟩

/-- **Invariant vectors reduce equivariant operators.** Let `π` be a unitary representation of a
finite group and `A` a partial linear map commuting with it, in the sense that `π g × π g` maps the
graph of `A` into itself: every `π g` preserves `dom A` and `A (π g x) = π g (A x)`. Then the
subspace of fixed vectors reduces `A`. -/
theorem isReducing_invariants (hπ : IsUnitary π) [π.invariants.HasOrthogonalProjection]
    {A : E →ₗ.[𝕜] E} (hA : ∀ g x y, (x, y) ∈ A.graph → (π g x, π g y) ∈ A.graph) :
    A.IsReducing π.invariants := by
  have := Fintype.ofFinite G
  have : Invertible (Fintype.card G : 𝕜) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  refine LinearPMap.isReducing_iff_starProjection_mem_graph.2 fun x y hxy ↦ ?_
  have hsum : (∑ g, π g x, ∑ g, π g y) = ∑ g, (π g x, π g y) :=
    Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])
  rw [hπ.starProjection_invariants_apply, hπ.starProjection_invariants_apply,
    Representation.averageMap_apply, Representation.averageMap_apply, ← Prod.smul_mk]
  simp only [toRepresentation_apply]
  rw [hsum]
  exact A.graph.smul_mem _ (A.graph.sum_mem fun g _ ↦ hA g x y hxy)

end IsUnitary

end ContRepresentation
