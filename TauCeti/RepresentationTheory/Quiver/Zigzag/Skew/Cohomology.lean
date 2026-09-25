/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Map
public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Relabel
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Cohomology
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Isomorphism

/-!
# Graph relabelling and skew-zigzag cohomology classes

The first cohomology class classifying a skew-zigzag parameter is natural under graph
isomorphisms and under a change of coefficient group. Thus changing vertex labels transports the
class by the induced isomorphism of graph cohomology, and a monoid homomorphism `k → l` carries
the class of a parameter to the class of its image under the induced change of coefficients
`H¹(G, kˣ) → H¹(G, lˣ)`.

The change of coefficients on cohomology is injective as soon as the induced map on units is, so
two parameters whose images under a monoid homomorphism have the same cohomology class were
already gauge equivalent, and over a commutative ring their relation quotients were already
isomorphic by an algebra isomorphism fixing every vertex idempotent. The map on units is the
hypothesis under which this is true, and no statement of injectivity is made without it: the
coefficient groups of the cohomology are the units of the coefficient rings.

The parameter classification follows C. Couture, *Skew-Zigzag Algebras*, Section 4. The
cohomology transport uses the graph cohomology construction in
`TauCeti.Combinatorics.SimpleGraph.Cohomology.Basic`, and the change of coefficients in
`TauCeti.Combinatorics.SimpleGraph.Cohomology.Map`.
-/

public section

namespace TauCeti.SkewZigzagParameter

universe u w z

variable {k : Type w} {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}

section Relabel

variable [CommMonoid k]

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

end Relabel

/-! ### Scalar extension of cohomology classes -/

section BaseChange

variable {l : Type z} [CommMonoid k] [CommMonoid l]

/-- **A coefficient homomorphism carries the cohomology class of a parameter to the cohomology
class of its image**: the class of `c.map f` is the class obtained from the class of `c` by the
change of coefficients on units `kˣ → lˣ`. -/
theorem cohomologyClass_map (f : k →* l) (c : SkewZigzagParameter k G) :
    cohomologyClass l G (c.map f) =
      G.firstCohomologyMap (Units.map f) (cohomologyClass k G c) := by
  rw [cohomologyClass_apply, cohomologyClass_apply, SimpleGraph.firstCohomologyMap_mk]
  refine SimpleGraph.FirstCohomology.mk_eq_mk_iff.mpr ⟨1, ?_⟩
  ext d
  simp [SimpleGraph.oneCochainsMap_apply, transition_map]

/-- **Injectivity on units makes scalar extension preserve the classification**: the parameters
whose images along `f` have the same cohomology class are exactly the gauge equivalent ones, the
easy direction because gauge equivalence is preserved by `f` and the other because the induced map
on cohomology is injective on units. -/
theorem cohomologyClass_map_eq_iff (f : k →* l) (hf : Function.Injective (Units.map f))
    {c c' : SkewZigzagParameter k G} :
    cohomologyClass l G (c.map f) = cohomologyClass l G (c'.map f) ↔ c.IsGaugeEquivalent c' := by
  constructor
  · intro h
    rw [cohomologyClass_map, cohomologyClass_map] at h
    exact cohomologyClass_eq_iff.mp
      (SimpleGraph.firstCohomologyMap_injective G (Units.map f) hf h)
  · intro h
    have hh : cohomologyClass l G (c.map f) = cohomologyClass l G (c'.map f) :=
      cohomologyClass_eq_iff.mpr (h.map f)
    rw [cohomologyClass_map, cohomologyClass_map] at hh ⊢
    exact hh

end BaseChange

/-! ### Scalar extension of the classified relation quotients -/

section BaseChangeAlgebra

open DoubledQuiver

variable {l : Type z} [CommRing k] [CommRing l] [Finite V]

/-- **Couture's classification is injective under a coefficient homomorphism that is injective on
units**: two parameters whose images along `f` have the same cohomology class, with `f` injective
on units, have already isomorphic relation quotients, by an algebra isomorphism fixing every vertex
idempotent. -/
theorem cohomologyClass_map_eq_iff_exists_vertexFixing_algEquiv (f : k →+* l)
    (hf : Function.Injective (Units.map f.toMonoidHom)) {c c' : SkewZigzagParameter k G} :
    cohomologyClass l G (c.map f) = cohomologyClass l G (c'.map f) ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ i : V, φ (skewZigzagMk k G c (PathAlgebra.vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (PathAlgebra.vertexIdempotent k (vertex G i)) := by
  constructor
  · intro h
    have hc : c.IsGaugeEquivalent c' :=
      (cohomologyClass_map_eq_iff (k := k) (l := l) (f := f.toMonoidHom) (c := c) (c' := c')
        hf).mp h
    exact cohomologyClass_eq_iff_exists_vertexFixing_algEquiv.mp
      (cohomologyClass_eq_iff.mpr hc)
  · rintro ⟨φ, hφ⟩
    have hc : cohomologyClass k G c = cohomologyClass k G c' :=
      cohomologyClass_eq_iff_exists_vertexFixing_algEquiv.mpr ⟨φ, hφ⟩
    exact (cohomologyClass_map_eq_iff (k := k) (l := l) (f := f.toMonoidHom) (c := c) (c' := c')
      hf).mpr (cohomologyClass_eq_iff.mp hc)

end BaseChangeAlgebra

end TauCeti.SkewZigzagParameter
