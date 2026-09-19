/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Cohomology
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Potential
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.VertexFixing

/-!
# The cohomology class of a skew-zigzag parameter

A skew-zigzag parameter `c` of a simple graph `G` labels each ordered pair of incident edges by a
unit-valued ratio between the two backtracks they carry. This file identifies the gauge classes of
such parameters with the first cohomology `H¹(G, kˣ)` of the graph.

The identification goes through local edge coordinates. Every parameter can be written as
`ratio(h, h') = τ h / τ h'` for a unit `τ h` on each oriented edge, and the `1`-cochain
`h ↦ τ h / τ h.symm` has a cohomology class which does not depend on the choice of `τ`; this is
the **cohomology class** of `c`. Parameters form a group under the ratio-by-ratio product and the
class is a group homomorphism. Its kernel consists of the gauge-trivial parameters, and every
class is attained: the edge coordinate `τ` can be put on one orientation of every edge, so no
square roots of units are needed. Hence:

```text
gauge classes of skew-zigzag parameters of G  ≃  H¹(G, kˣ),
```

over any commutative monoid `k`. Over a commutative ring and for a finite graph, the gauge classes
are the vertex-fixing isomorphism classes of the skew-zigzag relation quotients, so the cohomology
class classifies those quotients up to vertex-fixing isomorphism.

## Main definitions

* `TauCeti.SkewZigzagParameter.cohomologyClass`: the cohomology class of a skew-zigzag parameter,
  as a group homomorphism to `H¹(G, kˣ)`.
* `TauCeti.SkewZigzagParameter.gaugeClassEquivFirstCohomology`: the gauge classes of skew-zigzag
  parameters are in bijection with `H¹(G, kˣ)`.

## Main results

* `TauCeti.SkewZigzagParameter.cohomologyClass_apply`: the cohomology class of a parameter is
  the class of its `1`-cochain of transition factors.
* `TauCeti.SkewZigzagParameter.cohomologyClass_eq_mk_of_ratio_eq_div`: the cohomology class of a
  parameter written in edge coordinates `τ` is the class of `h ↦ τ h / τ h.symm`.
* `TauCeti.SkewZigzagParameter.cohomologyClass_eq_one_iff`: a parameter has trivial class exactly
  when it is gauge trivial.
* `TauCeti.SkewZigzagParameter.cohomologyClass_eq_iff`: two parameters have the same class exactly
  when they are gauge equivalent.
* `TauCeti.SkewZigzagParameter.cohomologyClass_surjective`: every class in `H¹(G, kˣ)` is the class
  of a parameter.
* `TauCeti.SkewZigzagParameter.cohomologyClass_eq_iff_exists_vertexFixing_algEquiv`: over a
  commutative ring and for a finite graph, two parameters have the same class exactly when their
  relation quotients are isomorphic by an isomorphism fixing every vertex idempotent.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, Theorem 4.8, https://arxiv.org/abs/1509.08405,
which identifies the vertex-fixing graded isomorphism classes of skew-zigzag algebras with the
graph cohomology `H¹(G, kˣ)`.
-/

public section

namespace TauCeti

open DoubledQuiver SimpleGraph

universe u w

namespace SkewZigzagParameter

variable {k : Type w} {V : Type u} {G : SimpleGraph V}

/-! ### Parameters from edge coordinates -/

section EdgeCoordinate

variable [Monoid k]

/-- The parameter with prescribed edge coordinates `τ`, whose ratios are `τ h / τ h'`. -/
def ofEdgeCoordinate (τ : ∀ ⦃i j : V⦄, G.Adj i j → kˣ) : SkewZigzagParameter k G where
  ratio _ _ _ h h' := τ h / τ h'
  ratio_self _ _ h := div_self' (τ h)
  ratio_inv _ _ _ h h' := by rw [div_mul_div_cancel, div_self']
  ratio_cocycle _ _ _ _ h h' h'' := by rw [div_mul_div_cancel, div_mul_div_cancel, div_self']

/-- The ratio of the parameter constructed from edge coordinates is their quotient. -/
@[simp]
theorem ofEdgeCoordinate_ratio (τ : ∀ ⦃i j : V⦄, G.Adj i j → kˣ) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    (ofEdgeCoordinate τ).ratio h h' = τ h / τ h' := (rfl)

end EdgeCoordinate

variable [CommMonoid k]

/-! ### The cohomology class -/

/-- The `1`-cochain of transition factors of a parameter. It depends on the chosen reference edges
of the local coordinates, but only up to a coboundary. -/
private noncomputable def transitionCochain : SkewZigzagParameter k G →* G.oneCochains kˣ :=
  MonoidHom.mk'
    (fun c ↦ ⟨fun d ↦ transition c d.adj, mem_oneCochains_iff.mpr fun d ↦ transition_symm c d.adj⟩)
    fun c c' ↦ Subtype.ext <| funext fun d ↦ transition_mul c c' d.adj

private theorem transitionCochain_apply (c : SkewZigzagParameter k G) (d : G.Dart) :
    (transitionCochain c : G.Dart → kˣ) d = transition c d.adj := (rfl)

variable (k G) in
/-- The **cohomology class** of a skew-zigzag parameter in the first cohomology `H¹(G, kˣ)` of
the graph: the class of the `1`-cochain `h ↦ τ h / τ h.symm` for any edge coordinates `τ` with
`ratio(h, h') = τ h / τ h'` (see `cohomologyClass_eq_mk_of_ratio_eq_div`). -/
noncomputable def cohomologyClass : SkewZigzagParameter k G →* G.FirstCohomology kˣ :=
  (FirstCohomology.mk G kˣ).comp transitionCochain

/-- The cohomology class of a parameter is the class of its `1`-cochain of transition factors
`h ↦ transition c h`. -/
theorem cohomologyClass_apply (c : SkewZigzagParameter k G) :
    cohomologyClass k G c =
      FirstCohomology.mk G kˣ ⟨fun d ↦ transition c d.adj,
        mem_oneCochains_iff.mpr fun d ↦ transition_symm c d.adj⟩ := (rfl)

/-- For edge coordinates `τ` of a parameter, the transition factors differ from the quotients
`τ h / τ h.symm` by the coboundary of a function on the vertices: at every vertex with an incident
edge the local coordinates and `τ` differ by a common factor. -/
private theorem exists_transition_eq_of_ratio_eq_div (c : SkewZigzagParameter k G)
    (τ : ∀ ⦃i j : V⦄, G.Adj i j → kˣ)
    (hτ : ∀ ⦃i j j' : V⦄ (h : G.Adj i j) (h' : G.Adj i j'), c.ratio h h' = τ h / τ h') :
    ∃ χ : V → kˣ, ∀ ⦃v w : V⦄ (h : G.Adj v w),
      transition c h = τ h / τ h.symm * (χ w / χ v) := by
  classical
  let χ' : V → kˣ := fun v ↦
    if hv : ∃ w, G.Adj v w then localCoordinate c hv.choose_spec / τ hv.choose_spec else 1
  have hχ' {v w : V} (h : G.Adj v w) : localCoordinate c h = χ' v * τ h := by
    have hv : ∃ w, G.Adj v w := ⟨w, h⟩
    have hr := (ratio_eq_localCoordinate_div c hv.choose_spec h).symm.trans (hτ _ h)
    rw [div_eq_div_iff_div_eq_div] at hr
    simp only [χ', dite_eq_left hv, hr, div_mul_cancel]
  refine ⟨fun v ↦ (χ' v)⁻¹, fun v w h ↦ ?_⟩
  rw [transition_def, hχ' h, hχ' h.symm]
  rw [inv_div_inv, div_mul_div_comm, mul_comm (χ' v), mul_comm (χ' w)]

/-- **The cohomology class of a parameter in edge coordinates**: if `ratio(h, h') = τ h / τ h'`
for every two edges at a common vertex, the class of the parameter is the class of the
`1`-cochain `h ↦ τ h / τ h.symm`. -/
theorem cohomologyClass_eq_mk_of_ratio_eq_div (c : SkewZigzagParameter k G)
    (τ : ∀ ⦃i j : V⦄, G.Adj i j → kˣ)
    (hτ : ∀ ⦃i j j' : V⦄ (h : G.Adj i j) (h' : G.Adj i j'), c.ratio h h' = τ h / τ h') :
    cohomologyClass k G c =
      FirstCohomology.mk G kˣ ⟨fun d ↦ τ d.adj / τ d.adj.symm,
        mem_oneCochains_iff.mpr fun _ ↦ (inv_div _ _).symm⟩ := by
  obtain ⟨χ, hχ⟩ := exists_transition_eq_of_ratio_eq_div c τ hτ
  refine (FirstCohomology.mk_eq_mk_iff.mpr ⟨χ, Subtype.ext <| funext fun d ↦ ?_⟩).symm
  rw [transitionCochain_apply, hχ d.adj, Subgroup.coe_mul, Pi.mul_apply, coboundary_apply]

/-- **A parameter has trivial cohomology class exactly when it is gauge trivial.** -/
theorem cohomologyClass_eq_one_iff {c : SkewZigzagParameter k G} :
    cohomologyClass k G c = 1 ↔ IsGaugeEquivalent 1 c := by
  constructor
  · -- A coboundary of transition factors is a vertex potential, which trivializes `c`.
    intro hc
    obtain ⟨φ, hφ⟩ := FirstCohomology.mk_eq_one_iff.mp hc
    refine isGaugeEquivalent_one_of_potential c φ fun v w h ↦ ?_
    have := congrFun (congrArg Subtype.val hφ) ⟨(v, w), h⟩
    rw [coboundary_apply, transitionCochain_apply] at this
    exact (div_eq_iff_eq_mul'.mp this)
  · -- A gauge-trivial parameter has symmetric edge coordinates, whose cochain is trivial.
    intro hc
    obtain ⟨s, hs, hsc⟩ := isGaugeEquivalent_one_iff_exists_ratio_eq_div.mp hc
    rw [cohomologyClass_eq_mk_of_ratio_eq_div c s hsc]
    refine FirstCohomology.mk_eq_one_iff.mpr ⟨1, Subtype.ext <| funext fun d ↦ ?_⟩
    simp only [coboundary_apply, Pi.one_apply, div_self']
    rw [hs d.adj, div_self']

/-- **Two parameters have the same cohomology class exactly when they are gauge equivalent.** -/
theorem cohomologyClass_eq_iff {c c' : SkewZigzagParameter k G} :
    cohomologyClass k G c = cohomologyClass k G c' ↔ c.IsGaugeEquivalent c' := by
  rw [isGaugeEquivalent_iff_isGaugeEquivalent_one_div, ← cohomologyClass_eq_one_iff, map_div,
    div_eq_one, eq_comm]

/-- A gauge transform does not change the cohomology class. -/
@[simp]
theorem cohomologyClass_gauge (c : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) :
    cohomologyClass k G (c.gauge u) = cohomologyClass k G c :=
  (cohomologyClass_eq_iff.mpr (isGaugeEquivalent_iff.mpr ⟨u, rfl⟩)).symm

/-! ### Every class is attained -/

/-- **Every class in `H¹(G, kˣ)` is the cohomology class of a skew-zigzag parameter.** -/
theorem cohomologyClass_surjective : Function.Surjective (cohomologyClass k G) := by
  classical
  intro x
  obtain ⟨σ, rfl⟩ := FirstCohomology.mk_surjective x
  -- Put the value of `σ` on one orientation of every edge, for a well-ordering of the vertices,
  -- and `1` on the other.
  let τ : ∀ ⦃i j : V⦄, G.Adj i j → kˣ := fun i j h ↦
    if WellOrderingRel i j then (σ : G.Dart → kˣ) ⟨(i, j), h⟩ else 1
  refine ⟨ofEdgeCoordinate τ, ?_⟩
  rw [cohomologyClass_eq_mk_of_ratio_eq_div (ofEdgeCoordinate τ) τ
    (fun _ _ _ h h' ↦ ofEdgeCoordinate_ratio τ h h')]
  congr 1
  refine Subtype.ext <| funext fun ⟨(i, j), h⟩ ↦ ?_
  have hsymm : (σ : G.Dart → kˣ) ⟨(j, i), h.symm⟩ = ((σ : G.Dart → kˣ) ⟨(i, j), h⟩)⁻¹ :=
    oneCochains_apply_symm σ ⟨(i, j), h⟩
  simp only [τ]
  rcases trichotomous_of WellOrderingRel i j with hij | rfl | hji
  · rw [ite_eq_left hij, ite_eq_right (asymm hij), div_one]
  · exact absurd h G.irrefl
  · rw [ite_eq_right (asymm hji), ite_eq_left hji, hsymm, one_div, inv_inv]

/-! ### Gauge classes and vertex-fixing isomorphism classes -/

private theorem isGaugeEquivalent_of_orbitRel {c c' : SkewZigzagParameter k G}
    (h : MulAction.orbitRel (∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) _ c c') :
    c'.IsGaugeEquivalent c :=
  let ⟨u, hu⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  isGaugeEquivalent_iff.mpr ⟨u, hu.symm⟩

private theorem orbitRel_of_isGaugeEquivalent {c c' : SkewZigzagParameter k G}
    (h : c'.IsGaugeEquivalent c) :
    MulAction.orbitRel (∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) _ c c' :=
  let ⟨u, hu⟩ := isGaugeEquivalent_iff.mp h
  MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨u, hu.symm⟩)

variable (k G) in
/-- **The gauge classes of skew-zigzag parameters are in bijection with `H¹(G, kˣ)`**, a class
being sent to the cohomology class of any of its parameters. -/
noncomputable def gaugeClassEquivFirstCohomology :
    MulAction.orbitRel.Quotient (∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ)
        (SkewZigzagParameter k G) ≃ G.FirstCohomology kˣ :=
  Equiv.ofBijective
    (Quotient.lift (cohomologyClass k G) fun _ _ h ↦
      (cohomologyClass_eq_iff.mpr (isGaugeEquivalent_of_orbitRel h)).symm)
    ⟨fun a b ↦ Quotient.inductionOn₂ a b fun _ _ h ↦
        Quotient.sound (orbitRel_of_isGaugeEquivalent (cohomologyClass_eq_iff.mp h.symm)),
      fun x ↦ let ⟨c, hc⟩ := cohomologyClass_surjective x; ⟨Quotient.mk _ c, hc⟩⟩

/-- The bijection sends the gauge class of a parameter to its cohomology class. -/
@[simp]
theorem gaugeClassEquivFirstCohomology_mk (c : SkewZigzagParameter k G) :
    gaugeClassEquivFirstCohomology k G (Quotient.mk _ c) = cohomologyClass k G c := (rfl)

/-- **Couture's classification**: over a commutative ring, two skew-zigzag parameters of a finite
graph have the same cohomology class in `H¹(G, kˣ)` exactly when their relation quotients are
isomorphic by an algebra isomorphism fixing every vertex idempotent. -/
theorem cohomologyClass_eq_iff_exists_vertexFixing_algEquiv {k : Type w} [CommRing k] [Finite V]
    {c c' : SkewZigzagParameter k G} :
    cohomologyClass k G c = cohomologyClass k G c' ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        ∀ i : V, φ (skewZigzagMk k G c (PathAlgebra.vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (PathAlgebra.vertexIdempotent k (vertex G i)) :=
  cohomologyClass_eq_iff.trans isGaugeEquivalent_iff_exists_vertexFixing_algEquiv

end SkewZigzagParameter

end TauCeti
