/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Relabel
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Cohomology
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Isomorphism

/-!
# Graph relabelling and skew-zigzag cohomology classes

The first cohomology class classifying a skew-zigzag parameter is natural under graph
isomorphisms. Thus changing vertex labels transports the class by the induced isomorphism of
graph cohomology. This identifies the action of graph automorphisms that enters the
classification of skew-zigzag algebras without fixed vertex idempotents.

The parameter classification follows C. Couture, *Skew-Zigzag Algebras*, Section 4. The
cohomology transport uses the graph cohomology construction in
`TauCeti.Combinatorics.SimpleGraph.Cohomology.Basic`.
-/

public section

namespace TauCeti.SkewZigzagParameter

variable {k : Type*} [CommMonoid k] {V W : Type*}
  {G : SimpleGraph V} {H : SimpleGraph W}

/-- Relabelling a skew-zigzag parameter transports its first cohomology class along the same
graph isomorphism. -/
@[simp]
theorem cohomologyClass_relabel (e : G ≃g H) (c : SkewZigzagParameter k G) :
    cohomologyClass k H (c.relabel e) =
      SimpleGraph.firstCohomologyRelabel kˣ e (cohomologyClass k G c) := by
  classical
  let τ : ∀ ⦃i j : V⦄, G.Adj i j → kˣ := fun _ _ h => localCoordinate c h
  let τ' : ∀ ⦃i j : W⦄, H.Adj i j → kˣ :=
    fun _ _ h => τ (e.symm.map_adj_iff.mpr h)
  have hτ : ∀ ⦃i j j' : V⦄ (h : G.Adj i j) (h' : G.Adj i j'),
      c.ratio h h' = τ h / τ h' := by
    intro i j j' h h'
    exact ratio_eq_localCoordinate_div c h h'
  have hτ' : ∀ ⦃i j j' : W⦄ (h : H.Adj i j) (h' : H.Adj i j'),
      (c.relabel e).ratio h h' = τ' h / τ' h' := by
    intro i j j' h h'
    rw [relabel_ratio]
    exact hτ _ _
  rw [cohomologyClass_eq_mk_of_ratio_eq_div c τ hτ,
    cohomologyClass_eq_mk_of_ratio_eq_div (c.relabel e) τ' hτ',
    SimpleGraph.firstCohomologyRelabel_mk]
  congr 1
  ext d
  simp only [SimpleGraph.oneCochainsRelabel_apply]
  simp [τ', SimpleGraph.Hom.mapDart]

end TauCeti.SkewZigzagParameter
