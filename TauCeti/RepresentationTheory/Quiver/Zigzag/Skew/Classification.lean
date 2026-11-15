/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Automorphism

/-!
# Graded isomorphism classes of skew-zigzag algebras

The skew-zigzag relation quotients of two parameters on a finite simple graph are graded
isomorphic exactly when their gauge classes differ by a graph automorphism. Equivalently,
their classes in `H¹(G, kˣ)` lie in the same orbit of `Aut(G)`.

The coefficient ring is any nontrivial commutative ring with only trivial idempotents. In
particular, every field qualifies, with `IsIdempotentElem.iff_eq_zero_or_one` supplying this
condition; neither square roots nor a restriction on the characteristic are needed. The graph
need not be connected. These statements concern `skewZigzagQuotient`, the relation quotient,
whose isolated-vertex factors are copies of `k`; they do not replace those factors with the
dual numbers used in the public ordinary `zigzagAlgebra`.

Gradedness is expressed by preservation and reflection of membership in every path-length
piece, as in the vertex-fixing classification in
`TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Grading`. No condition on the images of the
vertex idempotents is imposed: a graded isomorphism necessarily permutes them. Conversely,
relabelling followed by a gauge isomorphism supplies a graded isomorphism.

## Main results

* `TauCeti.SkewZigzagParameter.exists_isGaugeEquivalent_relabel_iff_exists_graded_algEquiv`:
  the gauge criterion for arbitrary graded isomorphisms.
* `TauCeti.SkewZigzagParameter.exists_firstCohomologyRelabel_eq_iff_exists_graded_algEquiv`:
  the cohomological classification by graph-automorphism orbits.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, Theorem 4.12,
https://arxiv.org/abs/1509.08405, proves the graded classification for connected graphs over
fields containing square roots. Here the existing gauge and vertex-permutation criteria give
the classification under the weaker coefficient and graph hypotheses above.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

namespace SkewZigzagParameter

universe u w

variable {k : Type w} [CommRing k] [Nontrivial k] {V : Type u} [Finite V]
  {G : SimpleGraph V} {c c' : SkewZigzagParameter k G}

/-- **Gauge classes modulo graph automorphisms are the graded isomorphism classes.** Over a
nontrivial commutative ring with only trivial idempotents, two skew-zigzag relation quotients
are graded isomorphic exactly when one parameter becomes gauge equivalent to the other after
relabelling by a graph automorphism. The isomorphism is not required to fix the vertices. -/
theorem exists_isGaugeEquivalent_relabel_iff_exists_graded_algEquiv
    (hidempotents : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) :
    (∃ τ : G ≃g G, (c.relabel τ).IsGaugeEquivalent c') ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ (n : ℕ) (x : skewZigzagQuotient k G c),
          φ x ∈ skewZigzagGrade k G c' n ↔ x ∈ skewZigzagGrade k G c n := by
  refine ⟨fun ⟨τ, hτ⟩ => ?_, fun ⟨φ, hφ⟩ => ?_⟩
  · obtain ⟨ψ, hψ, -⟩ := isGaugeEquivalent_iff_exists_graded_vertexFixing_algEquiv.mp hτ
    refine ⟨(skewZigzagQuotientEquiv k τ c).trans ψ, fun n x => ?_⟩
    rw [AlgEquiv.trans_apply, hψ]
    exact skewZigzagQuotientEquiv_mem_skewZigzagGrade_iff k G τ c
  · apply (exists_isGaugeEquivalent_relabel_iff_exists_algEquiv_vertexImages_mem_grade_zero
      hidempotents).mpr
    refine ⟨φ, fun i => (hφ 0 _).mpr ?_⟩
    exact skewZigzagMk_mem_skewZigzagGrade k G c (vertexIdempotent_mem_grade_zero _)

/-- **Couture's graded classification by `Aut(G)`-orbits on `H¹(G, kˣ)`.** Over a nontrivial
commutative ring with only trivial idempotents, the cohomology classes of two parameters lie
in the same graph-automorphism orbit exactly when their skew-zigzag relation quotients are
graded isomorphic. Together with `cohomologyClass_surjective`, this describes all graded
isomorphism classes of the relation quotients arising from skew-zigzag parameters. -/
theorem exists_firstCohomologyRelabel_eq_iff_exists_graded_algEquiv
    (hidempotents : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1) :
    (∃ τ : G ≃g G,
        SimpleGraph.firstCohomologyRelabel kˣ τ (cohomologyClass k G c) = cohomologyClass k G c') ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ (n : ℕ) (x : skewZigzagQuotient k G c),
          φ x ∈ skewZigzagGrade k G c' n ↔ x ∈ skewZigzagGrade k G c n := by
  simp_rw [← cohomologyClass_relabel, cohomologyClass_eq_iff]
  exact exists_isGaugeEquivalent_relabel_iff_exists_graded_algEquiv hidempotents

end SkewZigzagParameter

end TauCeti
