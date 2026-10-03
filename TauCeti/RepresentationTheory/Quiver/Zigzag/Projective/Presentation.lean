/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Quotient.Principal
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Basic

/-!
# Zigzag projectives as quotients of path-algebra projectives

Write `A = kQ` for the path algebra of the doubled graph, `I` for the zigzag relation ideal, and
`Z = A/I`. The vertex projective `Z eᵢ` is canonically the quotient of `A eᵢ` by `I eᵢ`.
This file gives the surjective presentation, identifies its kernel with right multiples of the
relations, and constructs the resulting `A`-linear isomorphism. Thus the comparison respects
left path action over any commutative coefficient ring. In the associated quiver representation,
a path acts by left multiplication by its zigzag class.

These statements concern the relation quotient. For the public componentwise zigzag algebra,
they apply to each component with an edge; singleton components instead use the dual numbers.

See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Chapter III, Section 2, for bound-quiver projectives, and Huerfano--Khovanov,
*A category for the adjoint representation*, Section 3, for zigzag algebras.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

/-- The relations on the path-algebra vertex projective `kQ eᵢ`: the submodule `I eᵢ`, obtained
by multiplying elements of the zigzag relation ideal on the right by the vertex idempotent. -/
noncomputable def zigzagProjectivePathRelations (i : V) :
    Submodule (pathAlgebra k (DoubledQuiver G))
      (Ideal.span {vertexIdempotent k (vertex G i)} : Ideal (pathAlgebra k (DoubledQuiver G))) :=
  LinearMap.range (spanSingletonRelationMap (vertexIdempotent k (vertex G i))
    (zigzagIdeal k G).asIdeal)

/-- Membership in the path-projective relations is precisely membership in the zigzag ideal.
The fixed-point condition `x eᵢ = x` already holds because `x` belongs to `kQ eᵢ`. -/
@[simp]
theorem mem_zigzagProjectivePathRelations_iff (i : V)
    (x : (Ideal.span {vertexIdempotent k (vertex G i)} :
      Ideal (pathAlgebra k (DoubledQuiver G)))) :
    x ∈ zigzagProjectivePathRelations k G i ↔
      (x : pathAlgebra k (DoubledQuiver G)) ∈ zigzagIdeal k G := by
  rw [zigzagProjectivePathRelations, range_spanSingletonRelationMap _ _
    (vertexIdempotent_mul_self (k := k) (vertex G i)), Submodule.mem_comap, Submodule.subtype_apply,
    TwoSidedIdeal.mem_asIdeal]

private theorem quotient_span_eq_projective (i : V) :
    (Ideal.span (Set.singleton (Ideal.Quotient.mk (zigzagIdeal k G).asIdeal
      (vertexIdempotent k (vertex G i)))) : Ideal (nonisolatedZigzagQuotient k G)) =
        zigzagProjective k G i := by
  rw [zigzagProjective_def, zigzagVertexIdempotent, zigzagMk_apply]
  rfl

/-- The canonical presentation of `Z eᵢ` by the path-algebra vertex projective `kQ eᵢ`.
The target is acted on by the path algebra through the zigzag quotient map. -/
noncomputable def zigzagProjectivePresentation (i : V) :
    (Ideal.span {vertexIdempotent k (vertex G i)} : Ideal (pathAlgebra k (DoubledQuiver G)))
      →ₗ[pathAlgebra k (DoubledQuiver G)] zigzagProjective k G i :=
  ((LinearEquiv.ofEq _ _ (quotient_span_eq_projective k G i)).restrictScalars
    (pathAlgebra k (DoubledQuiver G))).toLinearMap.comp
      (spanSingletonQuotientMap (vertexIdempotent k (vertex G i)) (zigzagIdeal k G).asIdeal)

/-- The presentation sends a path-algebra element to its zigzag class. -/
@[simp]
theorem coe_zigzagProjectivePresentation (i : V)
    (x : (Ideal.span {vertexIdempotent k (vertex G i)} :
      Ideal (pathAlgebra k (DoubledQuiver G)))) :
    (zigzagProjectivePresentation k G i x : nonisolatedZigzagQuotient k G) =
      zigzagMk k G x := by
  simp only [zigzagProjectivePresentation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, LinearEquiv.coe_ofEq_apply, zigzagMk_apply]
  exact coe_spanSingletonQuotientMap _ _ _

/-- The vertex generator of the path projective maps to the vertex generator of `Z eᵢ`. -/
@[simp]
theorem zigzagProjectivePresentation_generator (i : V) :
    zigzagProjectivePresentation k G i (spanSingletonGenerator (vertexIdempotent k (vertex G i))) =
      zigzagProjectiveGenerator k G i := by
  apply Subtype.ext
  rw [coe_zigzagProjectivePresentation, coe_spanSingletonGenerator,
    coe_zigzagProjectiveGenerator]

/-- The path-algebra presentation of a zigzag vertex projective is surjective. -/
theorem zigzagProjectivePresentation_surjective (i : V) :
    Function.Surjective (zigzagProjectivePresentation k G i) :=
  (LinearEquiv.ofEq _ _ (quotient_span_eq_projective k G i)).surjective.comp
    (spanSingletonQuotientMap_surjective _ _)

/-- The kernel of the path-algebra presentation is exactly `I eᵢ`. -/
theorem ker_zigzagProjectivePresentation (i : V) :
    LinearMap.ker (zigzagProjectivePresentation k G i) = zigzagProjectivePathRelations k G i := by
  ext x
  rw [LinearMap.mem_ker, mem_zigzagProjectivePathRelations_iff, ← zigzagMk_eq_zero_iff,
    ← coe_zigzagProjectivePresentation]
  exact Subtype.val_inj.symm

/-- The exact bound-quiver comparison `kQ eᵢ / I eᵢ ≅ Z eᵢ`. It is linear over the path
algebra, so restriction of scalars also gives the comparison over `k`. -/
noncomputable def zigzagProjectivePathQuotientEquiv (i : V) :
    ((Ideal.span {vertexIdempotent k (vertex G i)} : Ideal (pathAlgebra k (DoubledQuiver G)))
      ⧸ zigzagProjectivePathRelations k G i) ≃ₗ[pathAlgebra k (DoubledQuiver G)]
        zigzagProjective k G i :=
  (Submodule.quotEquivOfEq _ _ (ker_zigzagProjectivePresentation k G i).symm).trans
    ((zigzagProjectivePresentation k G i).quotKerEquivOfSurjective
      (zigzagProjectivePresentation_surjective k G i))

/-- On representatives, the comparison is the zigzag quotient map. -/
@[simp]
theorem zigzagProjectivePathQuotientEquiv_mk (i : V)
    (x : (Ideal.span {vertexIdempotent k (vertex G i)} :
      Ideal (pathAlgebra k (DoubledQuiver G)))) :
    zigzagProjectivePathQuotientEquiv k G i (Submodule.Quotient.mk x) =
      zigzagProjectivePresentation k G i x := by
  simp [zigzagProjectivePathQuotientEquiv]

/-- Left multiplication on the path-projective quotient corresponds to multiplication by the
zigzag class. This pins the later-factor-first convention of the comparison. -/
-- Apply before generic linearity rules rewrite the action inside the coercion.
@[simp↓]
theorem coe_zigzagProjectivePathQuotientEquiv_smul (i : V)
    (a : pathAlgebra k (DoubledQuiver G))
    (x : (Ideal.span {vertexIdempotent k (vertex G i)} : Ideal (pathAlgebra k (DoubledQuiver G)))
      ⧸ zigzagProjectivePathRelations k G i) :
    (zigzagProjectivePathQuotientEquiv k G i (a • x) : nonisolatedZigzagQuotient k G) =
      zigzagMk k G a * (zigzagProjectivePathQuotientEquiv k G i x :
        nonisolatedZigzagQuotient k G) := by
  rw [map_smul, zigzagMk_apply]
  -- The inherited path-algebra action on the quotient is defined via its quotient map.
  rfl

end TauCeti
