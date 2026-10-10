/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Radical
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# The vertex idempotents of a path algebra are primitive

Let `Q` be a quiver with finitely many vertices and `k` a semiring in which `1` is a primitive
idempotent — a domain or a local ring, say (`TauCeti.isPrimitiveIdempotent_one`). Then every
vertex idempotent `eᵥ` of the path algebra `kQ` is primitive: it is not the sum of two nonzero
orthogonal idempotents. Read through
`TauCeti.isPrimitiveIdempotent_iff_isIndecomposableModule`, this says that the left ideal
`kQ eᵥ` — the indecomposable projective `Pᵥ` — is an indecomposable module, and it is the input to
the primitive-idempotent decomposition of `1 = ∑ᵥ eᵥ`
(`TauCeti.PathAlgebra.completeOrthogonalIdempotents_vertexIdempotent`).

No hypothesis is placed on the paths at `v`: oriented cycles through `v` are allowed. For the
quiver with a single vertex and a single loop at it, where `kQ` is the polynomial ring `k[X]`
(`TauCeti.PathAlgebra.oneLoopAlgEquiv`) and the one vertex idempotent is `1`, the statement is that
`k[X]` has no idempotent other than `0` and `1`.

What replaces that hypothesis is the length filtration of the path algebra (`TauCeti.pathSpan`),
which is where the two coordinate facts this file rests on come from. Reading the coordinate on the
trivial path at `v` is a multiplicative map `kQ → k` (`TauCeti.pathAlgebraBasis_repr_mul_nil`),
because a concatenation is that trivial path only when both its factors are; and the arrow ideal —
the first step of the filtration, the elements whose coordinates on the trivial paths all vanish —
contains no nonzero idempotent
(`TauCeti.eq_zero_of_isIdempotentElem_of_mem_pathSpan_one`). Among the trivial paths, only the one
at `v` can carry a nonzero coordinate of an element of the corner `eᵥ kQ eᵥ`, a vertex idempotent
on the left confining the coordinates to the paths ending at `v`
(`TauCeti.pathAlgebraBasis_repr_vertexIdempotent_mul`). So the trivial-path coordinates of
the two summands of a decomposition of `eᵥ` decompose `1` in `k`, and the summand whose coordinate
primitivity of `1` kills lies in the arrow ideal, hence is zero.

The acyclic-at-`v` form of the theorem instead computed the corner `eᵥ kQ eᵥ` outright as a copy of
`k` (`TauCeti.vertexIdempotent_mul_mul_vertexIdempotent`), which is where the path hypothesis was
needed; that computation plays no part here.

## Main results

* `TauCeti.isPrimitiveIdempotent_vertexIdempotent`: **a vertex idempotent of the path algebra of a
  quiver with finitely many vertices is primitive** as soon as `1` is primitive in the coefficient
  semiring.
* `TauCeti.isIndecomposableModule_span_singleton_vertexIdempotent`: consequently the left ideal
  `kQ eᵥ` is an indecomposable `kQ`-module.

Primitivity of `eᵥ` is a semiring-level statement. Additive inverses enter only with the corollary,
the module characterization asking for a ring.

## References

This supplies the vertex-idempotent instance of the primitive idempotents of Layer 3A in
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, whose Layer 1 identifies
`kQ eᵥ` with the indecomposable projective `Pᵥ`.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

variable {k : Type w} {Q : Type u} [Quiver.{v} Q] [Finite Q]

section Semiring

variable [Semiring k]

omit [Finite Q] in
/-- The coordinate on the trivial path at `v` of an element of the corner `eᵥ kQ eᵥ` is its only
coordinate on a trivial path: every other trivial path fails to end at `v`. -/
private theorem mem_pathSpan_one_of_corner {v : Q} {f : pathAlgebra k Q}
    (hf : vertexIdempotent k v * f = f)
    (hv : (pathAlgebraBasis k Q).repr f ⟨v, v, _root_.Quiver.Path.nil⟩ = 0) :
    f ∈ pathSpan k Q 1 := by
  refine mem_pathSpan_iff.2 fun x hx => ?_
  by_contra hlen
  obtain ⟨a, b, p⟩ := x
  have hzero : p.length = 0 := Nat.le_zero.1 (Nat.not_lt.1 hlen)
  obtain rfl : a = b := p.eq_of_length_zero hzero
  obtain rfl : p = _root_.Quiver.Path.nil := p.eq_nil_of_length_zero hzero
  rcases eq_or_ne a v with rfl | hav
  · exact hx hv
  · have hcoord : (pathAlgebraBasis k Q).repr (vertexIdempotent k v * f)
        (⟨a, a, _root_.Quiver.Path.nil⟩ : Quiver.TotalPath Q) = 0 := by
      classical
      rw [pathAlgebraBasis_repr_vertexIdempotent_mul]
      simp [hav]
    exact hx (hf ▸ hcoord)

/-- **A vertex idempotent of a path algebra is primitive.** In a decomposition of `eᵥ` into
orthogonal idempotents, the two coordinates on the trivial path at `v` decompose `1` in the
coefficient semiring, so one of them vanishes; the corresponding summand then has no coordinate on
any trivial path, and an idempotent of the arrow ideal is zero. -/
theorem isPrimitiveIdempotent_vertexIdempotent (hk : IsPrimitiveIdempotent (1 : k)) (v : Q) :
    IsPrimitiveIdempotent (vertexIdempotent k v : pathAlgebra k Q) := by
  have := hk.nontrivial
  refine ⟨vertexIdempotent_mul_self v, vertexIdempotent_ne_zero v, ?_⟩
  intro f₁ f₂ h₁ h₂ h₁₂ h₂₁ hsum
  set c₁ := (pathAlgebraBasis k Q).repr f₁ ⟨v, v, _root_.Quiver.Path.nil⟩ with hc₁def
  set c₂ := (pathAlgebraBasis k Q).repr f₂ ⟨v, v, _root_.Quiver.Path.nil⟩ with hc₂def
  have hcorner₁ : vertexIdempotent k v * f₁ = f₁ := by
    rw [← hsum, add_mul, h₁.eq, h₂₁, add_zero]
  have hcorner₂ : vertexIdempotent k v * f₂ = f₂ := by
    rw [← hsum, add_mul, h₁₂, h₂.eq, zero_add]
  have hsq₁ : c₁ * c₁ = c₁ := by rw [hc₁def, ← pathAlgebraBasis_repr_mul_nil, h₁.eq]
  have hsq₂ : c₂ * c₂ = c₂ := by rw [hc₂def, ← pathAlgebraBasis_repr_mul_nil, h₂.eq]
  have hmul₁₂ : c₁ * c₂ = 0 := by
    rw [hc₁def, hc₂def, ← pathAlgebraBasis_repr_mul_nil, h₁₂, map_zero,
      Finsupp.zero_apply]
  have hmul₂₁ : c₂ * c₁ = 0 := by
    rw [hc₁def, hc₂def, ← pathAlgebraBasis_repr_mul_nil, h₂₁, map_zero,
      Finsupp.zero_apply]
  have hone : c₁ + c₂ = 1 := by
    rw [hc₁def, hc₂def, ← Finsupp.add_apply, ← map_add, hsum, vertexIdempotent_eq_single,
      pathAlgebraBasis_repr_single, Finsupp.single_eq_same]
  refine (hk.eq_zero_or_eq_zero_of_add hsq₁ hsq₂ hmul₁₂ hmul₂₁ hone).imp (fun hz => ?_) fun hz => ?_
  · exact eq_zero_of_isIdempotentElem_of_mem_pathSpan_one h₁
      (mem_pathSpan_one_of_corner hcorner₁ hz)
  · exact eq_zero_of_isIdempotentElem_of_mem_pathSpan_one h₂
      (mem_pathSpan_one_of_corner hcorner₂ hz)

end Semiring

/-- **The indecomposable projective `Pᵥ = kQ eᵥ` is an indecomposable module**: its generator is a
primitive idempotent. -/
theorem isIndecomposableModule_span_singleton_vertexIdempotent [Ring k]
    (hk : IsPrimitiveIdempotent (1 : k)) (v : Q) :
    IsIndecomposableModule (pathAlgebra k Q)
      (Ideal.span {(vertexIdempotent k v : pathAlgebra k Q)}) :=
  (isPrimitiveIdempotent_vertexIdempotent hk v).isIndecomposableModule

end TauCeti
