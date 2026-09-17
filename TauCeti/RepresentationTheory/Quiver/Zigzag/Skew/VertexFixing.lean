/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Multiplication

/-!
# Vertex-fixing isomorphisms of skew-zigzag algebras are gauge transforms

A skew-zigzag parameter `c` of a finite simple graph `G` labels each ordered pair of incident edges
by a unit-valued ratio, and gauge equivalent parameters present isomorphic algebras through an
arrow rescaling, which fixes every vertex idempotent. This file proves the converse over a field:
an algebra isomorphism

```text
φ : Z_k(G, c) ≃ₐ[k] Z_k(G, c')
```

fixing every vertex idempotent is a gauge transform, so `c` and `c'` are gauge equivalent. Hence
the vertex-fixing isomorphism classes of skew-zigzag algebras of `G` are exactly the gauge classes
of parameters. No grading hypothesis on `φ` is needed: an isomorphism fixing the idempotents
preserves the corner `e_j Z e_i` between the endpoints of an edge, and that corner is the line
spanned by the arrow `i ⟶ j`. So `φ` multiplies every arrow by a scalar, necessarily a unit, and
applying `φ` to the defining relation `backtrack(h) = c.ratio h h' • backtrack(h')` shows that
these units gauge `c` to `c'`.

## Main results

* `TauCeti.skewZigzagMk_vertexIdempotent_mul_mul_vertexIdempotent_mem_span`: the corner between
  the tail and the head of an arrow is spanned by that arrow.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_of_algEquiv`: a vertex-fixing isomorphism of
  skew-zigzag relation quotients forces the parameters to be gauge equivalent.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_iff_exists_algEquiv`: two parameters are gauge
  equivalent exactly when their relation quotients are isomorphic by a vertex-fixing isomorphism.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, https://arxiv.org/abs/1509.08405, which identifies
the vertex-fixing graded isomorphism classes of skew-zigzag algebras with the gauge classes of their
parameters, and those with the graph cohomology `H¹(G, kˣ)`.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### The corner of an arrow -/

section CommRing

variable [CommRing k] (c : SkewZigzagParameter k G)

/-- A path whose tail is `vertex G i` and whose head is `vertex G j`, for an edge `h : G.Adj i j`,
is a multiple of the arrow of `h` in the skew-zigzag quotient: it cannot have length zero since
`i ≠ j`, it is the arrow if it has length one, and it dies otherwise. -/
private theorem skewZigzagMk_ofPath_mem_span {i j : V} (h : G.Adj i j)
    (p : _root_.Quiver.Path (vertex G i) (vertex G j)) :
    skewZigzagMk k G c (ofPath ⟨_, _, p⟩) ∈ k ∙ skewZigzagMk k G c (ofArrow (arrow G h)) := by
  have hij : vertex G i ≠ vertex G j := (vertex_injective G).ne (G.ne_of_adj h)
  rcases Nat.lt_or_ge p.length 3 with hlt | hge
  · have hcases : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by omega
    rcases hcases with hp | hp | hp
    · exact absurd (p.eq_of_length_zero hp) hij
    · obtain ⟨h', rfl⟩ := exists_eq_arrowPath G p hp
      rw [← ofArrow_eq_ofPath_arrowPath]
      exact Submodule.mem_span_singleton_self _
    · rw [skewZigzagMk_ofPath_eq_zero_of_ne k G c p hp hij]
      exact Submodule.zero_mem _
  · rw [skewZigzagMk_ofPath_eq_zero_of_three_le k G c ⟨_, _, p⟩ hge]
    exact Submodule.zero_mem _

/-- **The corner of an arrow is spanned by the arrow.** For an arrow `e : x ⟶ y` of the doubled
quiver, cutting any element of a skew-zigzag relation quotient down by the vertex idempotent at the
head on the left and at the tail on the right gives a scalar multiple of the arrow. -/
theorem skewZigzagMk_vertexIdempotent_mul_mul_vertexIdempotent_mem_span {x y : DoubledQuiver G}
    (e : x ⟶ y) (z : skewZigzagQuotient k G c) :
    skewZigzagMk k G c (vertexIdempotent k y) * z * skewZigzagMk k G c (vertexIdempotent k x) ∈
      k ∙ skewZigzagMk k G c (ofArrow e) := by
  obtain ⟨i, rfl⟩ : ∃ i, x = vertex G i := ⟨_, (vertexEquiv_symm_apply G x).symm⟩
  obtain ⟨j, rfl⟩ : ∃ j, y = vertex G j := ⟨_, (vertexEquiv_symm_apply G y).symm⟩
  have h : G.Adj i j := by simpa using e.down
  obtain rfl : e = arrow G h := Subsingleton.elim _ _
  obtain ⟨z, rfl⟩ := skewZigzagMk_surjective k G c z
  rw [← map_mul, ← map_mul]
  induction z using PathAlgebra.induction_linear with
  | zero => rw [mul_zero, zero_mul, map_zero]; exact Submodule.zero_mem _
  | add z₁ z₂ h₁ h₂ => rw [mul_add, add_mul, map_add]; exact Submodule.add_mem _ h₁ h₂
  | single q r =>
    rw [single_eq_smul_ofPath, mul_smul_comm, smul_mul_assoc, map_smul]
    refine Submodule.smul_mem _ r ?_
    obtain ⟨a, b, p⟩ := q
    by_cases hb : vertex G j = b
    · subst hb
      rw [vertexIdempotent_mul_ofPath]
      by_cases ha : vertex G i = a
      · subst ha
        rw [ofPath_mul_vertexIdempotent]
        exact skewZigzagMk_ofPath_mem_span k G c h p
      · rw [ofPath_mul_vertexIdempotent_of_ne _ ha, map_zero]
        exact Submodule.zero_mem _
    · rw [vertexIdempotent_mul_ofPath_of_ne _ hb, zero_mul, map_zero]
      exact Submodule.zero_mem _

end CommRing

/-! ### Vertex-fixing isomorphisms -/

namespace SkewZigzagParameter

variable {k G} [Field k] {c c' : SkewZigzagParameter k G}

/-- A vertex-fixing isomorphism multiplies each arrow by a unit. -/
private theorem exists_unit_smul_of_algEquiv
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    ∃ r : kˣ, φ (skewZigzagMk k G c (ofArrow e)) = (r : k) • skewZigzagMk k G c' (ofArrow e) := by
  obtain ⟨i, rfl⟩ : ∃ i, x = vertex G i := ⟨_, (vertexEquiv_symm_apply G x).symm⟩
  obtain ⟨j, rfl⟩ : ∃ j, y = vertex G j := ⟨_, (vertexEquiv_symm_apply G y).symm⟩
  have h : G.Adj i j := by simpa using e.down
  obtain rfl : e = arrow G h := Subsingleton.elim _ _
  have hmem := skewZigzagMk_vertexIdempotent_mul_mul_vertexIdempotent_mem_span k G c' (arrow G h)
    (φ (skewZigzagMk k G c (ofArrow (arrow G h))))
  rw [← hφ i, ← hφ j, ← map_mul, ← map_mul, ← map_mul, ← map_mul, vertexIdempotent_mul_ofArrow,
    ofArrow_mul_vertexIdempotent] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul, eq_comm, map_eq_zero_iff φ φ.injective] at hr
    exact skewZigzagMk_ofArrow_ne_zero k G c (arrow G h) hr
  exact ⟨Units.mk0 r hr0, hr.symm⟩

/-- The unit by which a vertex-fixing isomorphism multiplies an arrow. -/
private noncomputable def arrowUnit
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    ⦃x y : DoubledQuiver G⦄ (e : x ⟶ y) : kˣ :=
  (exists_unit_smul_of_algEquiv φ hφ e).choose

/-- A vertex-fixing isomorphism multiplies each arrow by its arrow unit. -/
private theorem apply_skewZigzagMk_ofArrow
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    φ (skewZigzagMk k G c (ofArrow e)) =
      (arrowUnit φ hφ e : k) • skewZigzagMk k G c' (ofArrow e) :=
  (exists_unit_smul_of_algEquiv φ hφ e).choose_spec

/-- A vertex-fixing isomorphism multiplies each backtrack by the backtrack scale of its arrow
units. -/
private theorem apply_skewZigzagMk_backtrackElem
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    {i j : V} (h : G.Adj i j) :
    φ (skewZigzagMk k G c (backtrackElem G k h)) =
      ((backtrackScale G (arrowUnit φ hφ) h : kˣ) : k) •
        skewZigzagMk k G c' (backtrackElem G k h) := by
  rw [← ofArrow_symm_mul_ofArrow, map_mul, map_mul, apply_skewZigzagMk_ofArrow φ hφ,
    apply_skewZigzagMk_ofArrow φ hφ, smul_mul_smul_comm, ← map_mul, ofArrow_symm_mul_ofArrow,
    val_backtrackScale, backtrackScale_apply, mul_comm]

/-- **A vertex-fixing isomorphism of skew-zigzag relation quotients is a gauge transform.** Over a
field, if an algebra isomorphism between the relation quotients of two parameters fixes every
vertex idempotent, then the parameters are gauge equivalent, the gauge being the units by which the
isomorphism multiplies the arrows. -/
theorem isGaugeEquivalent_of_algEquiv
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i))) :
    c.IsGaugeEquivalent c' := by
  refine isGaugeEquivalent_iff.mpr ⟨arrowUnit φ hφ, ?_⟩
  ext i j j' h h'
  -- the image of the relation `backtrack(h) = c.ratio h h' • backtrack(h')` under `φ`
  have key := congrArg φ (skewZigzagMk_backtrackElem_eq_smul k G c h h')
  rw [map_smul, apply_skewZigzagMk_backtrackElem φ hφ, apply_skewZigzagMk_backtrackElem φ hφ,
    skewZigzagMk_backtrackElem_eq_smul k G c' h h', smul_smul, smul_smul] at key
  have hscalar := smul_left_injective k (skewZigzagMk_backtrackElem_ne_zero k G c' h') key
  have hunits : backtrackScale G (arrowUnit φ hφ) h * c'.ratio h h' =
      backtrackScale G (arrowUnit φ hφ) h * (c.gauge (arrowUnit φ hφ)).ratio h h' := by
    rw [backtrackScale_mul_gauge_ratio]
    exact Units.ext hscalar
  rw [mul_left_cancel hunits]

/-- **Gauge classes are vertex-fixing isomorphism classes.** Over a field, two skew-zigzag
parameters are gauge equivalent exactly when their relation quotients are isomorphic by an algebra
isomorphism fixing every vertex idempotent. -/
theorem isGaugeEquivalent_iff_exists_algEquiv :
    c.IsGaugeEquivalent c' ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (vertexIdempotent k (vertex G i)) := by
  refine ⟨fun h => ?_, fun ⟨φ, hφ⟩ => isGaugeEquivalent_of_algEquiv φ hφ⟩
  obtain ⟨u, hu⟩ := isGaugeEquivalent_iff.mp h
  exact ⟨skewZigzagQuotientGaugeEquiv k G c c' u hu, fun i => by
    rw [skewZigzagQuotientGaugeEquiv_skewZigzagMk, rescale_vertexIdempotent]⟩

end SkewZigzagParameter

end TauCeti
