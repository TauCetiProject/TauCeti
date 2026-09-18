/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basis

/-!
# Vertex-fixing isomorphisms of skew-zigzag algebras and gauge equivalence

A skew-zigzag parameter `c` of a finite simple graph `G` labels each ordered pair of incident edges
by a unit-valued ratio, and gauge equivalent parameters present isomorphic algebras through an
arrow rescaling, which fixes every vertex idempotent. This file proves the converse over a
commutative ring: an algebra isomorphism

```text
φ : Z_k(G, c) ≃ₐ[k] Z_k(G, c')
```

fixing every vertex idempotent forces `c` and `c'` to be gauge equivalent. Hence
the vertex-fixing isomorphism classes of skew-zigzag algebras of `G` are exactly the gauge classes
of parameters. No grading hypothesis on `φ` is needed: an isomorphism fixing the idempotents
preserves the corner `e_j Z e_i` between the endpoints of an edge, and that corner is the line
spanned by the arrow `i ⟶ j`. So `φ` multiplies every arrow by a scalar, necessarily a unit, and
applying `φ` to the defining relation `backtrack(h) = c.ratio h h' • backtrack(h')` shows that
these units gauge `c` to `c'`.

## Main results

* `TauCeti.SkewZigzagParameter.existsUnique_unit_smul_of_vertexFixing_algEquiv`: a vertex-fixing
  isomorphism of skew-zigzag relation quotients multiplies each arrow by a unique unit.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_of_vertexFixing_algEquiv`: a vertex-fixing
  isomorphism of skew-zigzag relation quotients forces the parameters to be gauge equivalent.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_iff_exists_vertexFixing_algEquiv`: two parameters
  are gauge equivalent exactly when their relation quotients are isomorphic by a vertex-fixing
  isomorphism.

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

/-! ### Vertex-fixing isomorphisms -/

namespace SkewZigzagParameter

variable {k G} [CommRing k] {c c' : SkewZigzagParameter k G}

/-- A vertex-fixing isomorphism multiplies each arrow by a scalar. -/
private theorem exists_smul_of_algEquiv
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    ∃ r : k, φ (skewZigzagMk k G c (ofArrow e)) = r • skewZigzagMk k G c' (ofArrow e) := by
  obtain ⟨i, rfl⟩ : ∃ i, x = vertex G i := ⟨_, (vertexEquiv_symm_apply G x).symm⟩
  obtain ⟨j, rfl⟩ : ∃ j, y = vertex G j := ⟨_, (vertexEquiv_symm_apply G y).symm⟩
  have h : G.Adj i j := by simpa using e.down
  obtain rfl : e = arrow G h := Subsingleton.elim _ _
  have hmem := skewZigzagMk_vertexIdempotent_mul_mul_vertexIdempotent_mem_span k G c' (arrow G h)
    (φ (skewZigzagMk k G c (ofArrow (arrow G h))))
  rw [← hφ i, ← hφ j, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
    vertexIdempotent_mul_ofArrow, ofArrow_mul_vertexIdempotent] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨r, hr.symm⟩

/-- Scalar multiplication of an arrow class is injective. -/
private theorem skewZigzagMk_ofArrow_smul_left_injective
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    Function.Injective fun r : k ↦ r • skewZigzagMk k G c (ofArrow e) := by
  obtain ⟨i, rfl⟩ : ∃ i, x = vertex G i := ⟨_, (vertexEquiv_symm_apply G x).symm⟩
  obtain ⟨j, rfl⟩ : ∃ j, y = vertex G j := ⟨_, (vertexEquiv_symm_apply G y).symm⟩
  have h : G.Adj i j := by simpa using e.down
  obtain rfl : e = arrow G h := Subsingleton.elim _ _
  intro r s hrs
  beta_reduce at hrs
  apply skewZigzagMk_backtrackElem_smul_left_injective k G c h
  beta_reduce
  rw [← ofArrow_symm_mul_ofArrow, map_mul, ← mul_smul_comm, ← mul_smul_comm, hrs]

/-- **A vertex-fixing isomorphism rescales arrows by units.** An algebra isomorphism between the
relation quotients of two parameters that fixes every vertex idempotent multiplies each arrow by a
unique unit. -/
theorem existsUnique_unit_smul_of_vertexFixing_algEquiv
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    ∃! r : kˣ, φ (skewZigzagMk k G c (ofArrow e)) = (r : k) • skewZigzagMk k G c' (ofArrow e) := by
  obtain ⟨r, hr⟩ := exists_smul_of_algEquiv φ hφ e
  have hφsymm : ∀ i : V, φ.symm (skewZigzagMk k G c' (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c (vertexIdempotent k (vertex G i)) := fun i => by
    rw [← hφ i, φ.symm_apply_apply]
  obtain ⟨s, hs⟩ := exists_smul_of_algEquiv φ.symm hφsymm e
  have hrs_smul : (r * s) • skewZigzagMk k G c (ofArrow e) =
      (1 : k) • skewZigzagMk k G c (ofArrow e) := by
    calc
      (r * s) • skewZigzagMk k G c (ofArrow e) =
          r • (s • skewZigzagMk k G c (ofArrow e)) := by rw [smul_smul]
      _ = r • φ.symm (skewZigzagMk k G c' (ofArrow e)) := congrArg (r • ·) hs.symm
      _ = φ.symm (r • skewZigzagMk k G c' (ofArrow e)) := (map_smul _ _ _).symm
      _ = φ.symm (φ (skewZigzagMk k G c (ofArrow e))) := congrArg φ.symm hr.symm
      _ = skewZigzagMk k G c (ofArrow e) := φ.symm_apply_apply _
      _ = (1 : k) • skewZigzagMk k G c (ofArrow e) := (one_smul _ _).symm
  have hrs : r * s = 1 := skewZigzagMk_ofArrow_smul_left_injective (c := c) e hrs_smul
  refine ⟨⟨r, s, hrs, by simpa [mul_comm] using hrs⟩, hr, fun t ht => Units.ext ?_⟩
  exact skewZigzagMk_ofArrow_smul_left_injective (c := c') e (ht.symm.trans hr)

/-- The unit by which a vertex-fixing isomorphism multiplies an arrow. -/
private noncomputable def arrowUnit
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    ⦃x y : DoubledQuiver G⦄ (e : x ⟶ y) : kˣ :=
  (existsUnique_unit_smul_of_vertexFixing_algEquiv φ hφ e).exists.choose

/-- A vertex-fixing isomorphism multiplies each arrow by its arrow unit. -/
private theorem apply_skewZigzagMk_ofArrow
    (φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c')
    (hφ : ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
      skewZigzagMk k G c' (vertexIdempotent k (vertex G i)))
    {x y : DoubledQuiver G} (e : x ⟶ y) :
    φ (skewZigzagMk k G c (ofArrow e)) =
      (arrowUnit φ hφ e : k) • skewZigzagMk k G c' (ofArrow e) :=
  (existsUnique_unit_smul_of_vertexFixing_algEquiv φ hφ e).exists.choose_spec

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

/-- **A vertex-fixing isomorphism forces gauge equivalence.** If an
algebra isomorphism between the relation quotients of two parameters over a commutative ring fixes
every vertex idempotent, then the parameters are gauge equivalent, a gauge being given by the units
by which the isomorphism multiplies the arrows. -/
theorem isGaugeEquivalent_of_vertexFixing_algEquiv
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
  have hscalar := skewZigzagMk_backtrackElem_smul_left_injective k G c' h' key
  have hunits : backtrackScale G (arrowUnit φ hφ) h * c'.ratio h h' =
      backtrackScale G (arrowUnit φ hφ) h * (c.gauge (arrowUnit φ hφ)).ratio h h' := by
    rw [backtrackScale_mul_gauge_ratio]
    exact Units.ext hscalar
  rw [mul_left_cancel hunits]

/-- **Gauge classes are vertex-fixing isomorphism classes.** Two skew-zigzag parameters over a
commutative ring are gauge equivalent exactly when their relation quotients are isomorphic by an
algebra isomorphism fixing every vertex idempotent. -/
theorem isGaugeEquivalent_iff_exists_vertexFixing_algEquiv :
    c.IsGaugeEquivalent c' ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (vertexIdempotent k (vertex G i)) := by
  refine ⟨fun h => ?_, fun ⟨φ, hφ⟩ => isGaugeEquivalent_of_vertexFixing_algEquiv φ hφ⟩
  obtain ⟨u, hu⟩ := isGaugeEquivalent_iff.mp h
  exact ⟨skewZigzagQuotientGaugeEquiv k G c c' u hu, fun i => by
    rw [skewZigzagQuotientGaugeEquiv_skewZigzagMk, rescale_vertexIdempotent]⟩

end SkewZigzagParameter

end TauCeti
