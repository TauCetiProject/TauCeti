/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.Geometry.Manifold.Morse.Perfect
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Index
public import TauCeti.Geometry.Toric.Delzant.Quotient.Darboux
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.Geometry.Toric.Delzant.Face

/-!
# Betti numbers of Delzant toric manifolds from the edges of the polytope

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a Delzant polytope
`Δ ⊆ V*`, with Delzant quotient `M_Δ` (`TauCeti.Toric.DelzantQuotient i u c`), a compact smooth
manifold of dimension `2 n`, `n = dim V`, and reduced moment map `μ_Δ : M_Δ → V*`. At a vertex `v`
of `Δ`, the `n` edges of `Δ` leave `v` in the directions of the inward edge basis `ε_k`
(`TauCeti.Toric.IsSmoothVertex.edgeBasis`). This file computes every Betti number of `M_Δ` by
counting, at each vertex, the edges along which a generic linear function on `V*` decreases.

Fix `X ∈ V` with `ε_k(X) ≠ 0` for every edge `ε_k` at every vertex: the linear function
`y ↦ y(X)` is constant along no edge of `Δ`. Such `X` exist, as the edges are finitely many nonzero
covectors (`TauCeti.Toric.IsDelzant.exists_forall_edgeBasis_apply_ne_zero`). Consider the component
`f(q) = μ_Δ(q)(X)` of the moment map.

* **Local form.** In the Darboux chart at a vertex `v`
  (`TauCeti.Toric.IsDelzant.vertexDarbouxChart`), with coordinates `w ∈ ℂ^A` for the set `A` of
  facets active at `v`, the moment map is `v + Σ_k ½ |w_k|² ε_k`, so
  `f = v(X) + Σ_k ½ ε_k(X) |w_k|²`.
* **Critical points.** Hence the critical points of `f` are exactly the points over the vertices of
  `Δ` (`TauCeti.Toric.IsDelzant.mem_criticalPoints_reducedMomentMap_apply_iff`), all of them
  nondegenerate, so `f` is a Morse function
  (`TauCeti.Toric.IsDelzant.isMorse_reducedMomentMap_apply`).
* **Indices.** The Morse index of `f` at the point over `v` is twice the number of edges at `v`
  along which `X` decreases, `2 #{k | ε_k(X) < 0}`
  (`TauCeti.Toric.IsDelzant.manifoldMorseIndex_reducedMomentMap_apply`). This formula needs no
  genericity of `X`.
* **Perfection.** All indices are even, so by the lacunary principle `f` is a perfect Morse
  function for every division ring of coefficients
  (`TauCeti.Toric.IsDelzant.isPerfectMorse_reducedMomentMap_apply`).
* **Betti numbers.** Therefore `b_(2m)(M_Δ; k)` is the number of vertices of `Δ` at which exactly
  `m` edges descend for `X` (`TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_two_mul`). The
  odd Betti numbers vanish (`TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_eq_zero_of_odd`),
  and replacing `X` by `-X` exchanges `m` and `n - m` descending edges at each vertex, so
  `b_(2m) = b_(2n - 2m)` (`TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_two_mul_sub`).

The count does not depend on the generic `X`, although the descending edges at a single vertex do.

## Main results

* `TauCeti.Toric.IsDelzant.exists_forall_edgeBasis_apply_ne_zero`: generic directions exist.
* `TauCeti.Toric.IsDelzant.mem_criticalPoints_reducedMomentMap_apply_iff`: the critical points of
  a generic moment component are the points over the vertices.
* `TauCeti.Toric.IsDelzant.manifoldMorseIndex_reducedMomentMap_apply`: the Morse index at the point
  over a vertex is twice the number of descending edges.
* `TauCeti.Toric.IsDelzant.isMorse_reducedMomentMap_apply`,
  `TauCeti.Toric.IsDelzant.isPerfectMorse_reducedMomentMap_apply`: a generic moment component is a
  perfect Morse function.
* `TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_two_mul`: `b_(2m)` counts the vertices with
  `m` descending edges.
* `TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_two_mul_sub`: `b_(2m) = b_(2n - 2m)`.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994.
* W. Fulton, *Introduction to Toric Varieties*, Annals of Mathematics Studies 131, Princeton
  University Press, 1993, Section 5.2 (the Betti numbers of a smooth projective toric variety
  from a generic linear function on its polytope).
-/

public section

noncomputable section

open Module Set
open scoped Manifold ContDiff

namespace TauCeti.Toric

universe w

variable {ι : Type w} {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

namespace IsDelzant

open DelzantQuotient

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

/-- **Generic directions exist.** There is `X ∈ V` on which no edge covector `ε_k` at any vertex of
a Delzant polytope vanishes: the linear function `y ↦ y(X)` on `V*` is constant along no edge.
The edges are finitely many nonzero covectors, and a finite union of hyperplanes does not cover
`V`. -/
theorem exists_forall_edgeBasis_apply_ne_zero [Finite ι] :
    ∃ X : V, ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) j,
      (hΔ.isSmoothVertex v hv).edgeBasis hi j X ≠ 0 := by
  have : Finite ((facetPolyhedron i u c).extremePoints ℝ) :=
    finite_extremePoints_facetPolyhedron.to_subtype
  obtain ⟨X, hX⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists (K := ℝ)
    (fun p : Σ v : (facetPolyhedron i u c).extremePoints ℝ,
        activeSet (facetPairing i u) c (v : StrongDual ℝ V) ↦
      ((hΔ.isSmoothVertex p.1 p.1.property).edgeBasis hi p.2 : V →L[ℝ] ℝ).toLinearMap)
    fun p ↦ by
      by_contra! h
      exact ((hΔ.isSmoothVertex p.1 p.1.property).edgeBasis hi).ne_zero p.2
        (ContinuousLinearMap.ext h)
  exact ⟨X, fun v hv j ↦ hX ⟨⟨v, hv⟩, j⟩⟩

variable [Fintype ι] [FiniteDimensional ℝ V]
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
include hβ

/-- In the vertex chart at `v`, the moment component `μ_Δ(·)(X)` is the constant `v(X)` plus the
component at `X` of the weight model with the weights `-ε_k`. -/
private theorem reducedMomentMap_apply_eq_add {X : V} {v : StrongDual ℝ V}
    (hv : IsSmoothVertex i u c v) (hvP : v ∈ facetPolyhedron i u c)
    [Fintype (activeSet (facetPairing i u) c v)] :
    letI := hΔ.delzantQuotientChartedSpace hi
    ∀ q ∈ (hΔ.vertexDarbouxChart hi hv hvP).source, reducedMomentMap hβ q X =
      v X + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (hΔ.vertexDarbouxChart hi hv hvP q) X :=
  fun q hq ↦ by
    rw [vertexDarbouxChart_source] at hq
    rw [coe_vertexDarbouxChart, ← add_apply, add_weightMomentMap_vertexChart hv hi hvP hq]

/-- The point over a vertex lies in the source of the vertex chart at that vertex. -/
private theorem mem_vertexChart_source_self {q : DelzantQuotient i u c}
    (hq : reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ)
    [Fintype (activeSet (facetPairing i u) c (reducedMomentMap hβ q))] :
    letI := hΔ.delzantQuotientChartedSpace hi
    q ∈ (hΔ.vertexDarbouxChart hi (hΔ.isSmoothVertex _ hq) hq.1).source := by
  rw [vertexDarbouxChart_source]
  exact mem_vertexChart_source_of_reducedMomentMap_eq _ hi hq.1 rfl

/-- **The points over the vertices are critical.** At the point of the Delzant quotient over a
vertex of `Δ`, every moment component `q ↦ μ_Δ(q)(X)` has a critical point: it is fixed by the
torus. -/
theorem mem_criticalPoints_reducedMomentMap_apply (X : V) {q : DelzantQuotient i u c}
    (hq : reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    letI := hΔ.delzantQuotientChartedSpace hi
    q ∈ criticalPoints 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
      (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (fun q ↦ reducedMomentMap hβ q X) := by
  classical
  let _ := hΔ.delzantQuotientChartedSpace hi
  refine (mem_criticalPoints_iff_weightGenerator_eq_zero
    (hΔ.reducedMomentMap_apply_eq_add hi hβ (X := X) (hΔ.isSmoothVertex _ hq) hq.1)
    (hΔ.mem_vertexChart_source_self hi hβ hq)).2 ?_
  have hsrc := hΔ.mem_vertexChart_source_self hi hβ hq
  rw [vertexDarbouxChart_source] at hsrc
  rw [coe_vertexDarbouxChart, (vertexChart_eq_zero_iff _ hi hq.1 hsrc).2 rfl, map_zero]

/-- **The Morse index at a vertex counts descending edges.** At the point of the Delzant quotient
over a vertex `v` of `Δ`, the Morse index of the moment component `q ↦ μ_Δ(q)(X)` is twice the
number of edges `ε_k` at `v` with `ε_k(X) < 0`, along which `y ↦ y(X)` decreases. No genericity of
`X` is needed. -/
theorem manifoldMorseIndex_reducedMomentMap_apply (X : V) {q : DelzantQuotient i u c}
    (hq : reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    letI := hΔ.delzantQuotientChartedSpace hi
    manifoldMorseIndex 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (fun q ↦ reducedMomentMap hβ q X) q =
      2 * {k | (hΔ.isSmoothVertex _ hq).edgeBasis hi k X < 0}.ncard := by
  classical
  let _ := hΔ.delzantQuotientChartedSpace hi
  rw [manifoldMorseIndex_eq_two_mul_ncard_pos_of_weightMomentMap
    (hΔ.reducedMomentMap_apply_eq_add hi hβ (X := X) (hΔ.isSmoothVertex _ hq) hq.1)
    (hΔ.mem_vertexChart_source_self hi hβ hq)
    (hΔ.mem_criticalPoints_reducedMomentMap_apply hi hβ X hq)]
  simp only [neg_apply, Left.neg_pos_iff]

variable {X : V} (hX : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) j,
  (hΔ.isSmoothVertex v hv).edgeBasis hi j X ≠ 0)
include hX

/-- **Critical points of a generic moment component.** If no edge covector of `Δ` vanishes at `X`,
the critical points of `q ↦ μ_Δ(q)(X)` are exactly the points over the vertices of `Δ`. -/
theorem mem_criticalPoints_reducedMomentMap_apply_iff {q : DelzantQuotient i u c} :
    letI := hΔ.delzantQuotientChartedSpace hi
    q ∈ criticalPoints 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (fun q ↦ reducedMomentMap hβ q X) ↔
      reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  classical
  let _ := hΔ.delzantQuotientChartedSpace hi
  refine ⟨fun hcrit ↦ ?_, fun hq ↦ hΔ.mem_criticalPoints_reducedMomentMap_apply hi hβ X hq⟩
  -- In a vertex chart containing `q`, the generator of the weight model vanishes at the
  -- coordinates `w` of `q`; as no weight vanishes at `X`, `w = 0` and `q` lies over the vertex.
  obtain ⟨v, hv, hq⟩ := hΔ.exists_mem_vertexChart_source hi q
  have hf := hΔ.reducedMomentMap_apply_eq_add hi hβ (X := X) (hΔ.isSmoothVertex v hv) hv.1
  have hgen := (mem_criticalPoints_iff_weightGenerator_eq_zero hf
    (by rwa [vertexDarbouxChart_source])).1 hcrit
  rw [weightGenerator_apply_eq_zero_iff, coe_vertexDarbouxChart] at hgen
  have hw : vertexChart (hΔ.isSmoothVertex v hv) hi hv.1 q = 0 := by
    have h (k) := not_or.1 (mt (hgen k) (neg_ne_zero.2 (hX v hv k)))
    ext k
    · exact not_not.1 (h k).1
    · exact not_not.1 (h k).2
  rw [(vertexChart_eq_zero_iff _ hi hv.1 hq).1 hw]
  exact hv

/-- **A generic moment component is a Morse function.** If no edge covector of `Δ` vanishes at
`X`, the moment component `q ↦ μ_Δ(q)(X)` is a Morse function on the Delzant quotient: in the
vertex chart at `v` it is `v(X) + Σ_k ½ ε_k(X) |w_k|²` with all `ε_k(X) ≠ 0`. -/
theorem isMorse_reducedMomentMap_apply :
    letI := hΔ.delzantQuotientChartedSpace hi
    IsMorse 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) (fun q ↦ reducedMomentMap hβ (c := c) q X) := by
  classical
  let _ := hΔ.delzantQuotientChartedSpace hi
  refine isMorseOn_univ.1 <| isMorseOn_iff_criticalPoints.2
    ⟨((hΔ.contMDiff_reducedMomentMap hi hβ).clm_apply contMDiff_const).contMDiffOn,
      fun q _ hcrit ↦ ?_⟩
  obtain ⟨v, hv, hq⟩ := hΔ.exists_mem_vertexChart_source hi q
  rw [← vertexDarbouxChart_source hΔ] at hq
  exact (isManifoldNondegenerateCriticalPoint_iff_forall_ne_zero_of_weightMomentMap
    (hΔ.reducedMomentMap_apply_eq_add hi hβ (hΔ.isSmoothVertex v hv) hv.1) hq hcrit).2
    fun k ↦ neg_ne_zero.2 (hX v hv k)

/-- **A generic moment component is a perfect Morse function.** If no edge covector of `Δ`
vanishes at `X`, the moment component `q ↦ μ_Δ(q)(X)` is a perfect Morse function on the Delzant
quotient for every division ring of coefficients, since all its indices are even. -/
theorem isPerfectMorse_reducedMomentMap_apply (k : Type w) [DivisionRing k] :
    letI := hΔ.delzantQuotientChartedSpace hi
    IsPerfectMorse 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) k (fun q ↦ reducedMomentMap hβ (c := c) q X) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := hi.t2Space_delzantQuotient (u := u) (c := c)
  have := compactSpace_delzantQuotient (c := c) hΔ.isBounded
  refine (hΔ.isMorse_reducedMomentMap_apply hi hβ hX).isPerfectMorse_of_even fun q hq ↦ ?_
  rw [hΔ.manifoldMorseIndex_reducedMomentMap_apply hi hβ X
    ((hΔ.mem_criticalPoints_reducedMomentMap_apply_iff hi hβ hX).1 hq)]
  exact even_two_mul _

omit [FiniteDimensional ℝ V] hβ in
/-- **The even Betti numbers of a Delzant toric manifold count descending edges.** Let `X ∈ V` be
such that no edge covector `ε_k` at any vertex of `Δ` vanishes at `X`. Then for every division
ring `k`, the Betti number `b_(2m)(M_Δ; k)` is the number of vertices of `Δ` at which exactly `m`
edges `ε_k` satisfy `ε_k(X) < 0`, that is, exactly `m` edges descend for the linear function
`y ↦ y(X)`. -/
theorem bettiNumber_delzantQuotient_two_mul (k : Type w) [DivisionRing k] (m : ℕ) :
    bettiNumber k (DelzantQuotient i u c) (2 * m) =
      {v | ∃ hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ,
        {j | (hΔ.isSmoothVertex v hv).edgeBasis hi j X < 0}.ncard = m}.ncard := by
  have := hi.finiteDimensional
  have hβ := surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination
  let _ := hΔ.delzantQuotientChartedSpace hi
  rw [(hΔ.isPerfectMorse_reducedMomentMap_apply hi hβ hX k).bettiNumber_eq_ncard,
    ← InjOn.ncard_image (f := reducedMomentMap hβ)]
  · -- The moment map sends the critical points of index `2 m` onto the vertices with `m`
    -- descending edges.
    congr 1
    ext v
    simp only [mem_image, mem_ofPred_eq, hΔ.mem_criticalPoints_reducedMomentMap_apply_iff hi hβ hX]
    constructor
    · rintro ⟨q, ⟨hq, hm⟩, rfl⟩
      rw [hΔ.manifoldMorseIndex_reducedMomentMap_apply hi hβ X hq] at hm
      exact ⟨hq, by omega⟩
    · rintro ⟨hv, hm⟩
      obtain ⟨q, -, rfl⟩ := (bijOn_reducedMomentMap_fixedPoints hβ hi).surjOn hv
      exact ⟨q, ⟨hv, by rw [hΔ.manifoldMorseIndex_reducedMomentMap_apply hi hβ X hv, hm]⟩,
        rfl⟩
  · -- Critical points lie over vertices, where the moment map is injective.
    rintro q ⟨hq, -⟩ q' ⟨hq', -⟩ h
    rw [mem_criticalPoints_reducedMomentMap_apply_iff hΔ hi hβ hX] at hq hq'
    exact (bijOn_reducedMomentMap_fixedPoints hβ hi).injOn ((mem_fixedPoints_iff hβ hi).2 hq)
      ((mem_fixedPoints_iff hβ hi).2 hq') h

omit [FiniteDimensional ℝ V] hβ hX in
/-- **The Betti numbers of a Delzant toric manifold are symmetric**: `b_(2m) = b_(2n - 2m)` for
`m ≤ n = dim V`, for every division ring of coefficients. A vertex of `Δ` has exactly `n` edges,
and for a generic `X` the edges descending for `-X` are those ascending for `X`, so `m`
descending edges for `X` are `n - m` descending edges for `-X`. -/
theorem bettiNumber_delzantQuotient_two_mul_sub (k : Type w) [DivisionRing k] {m : ℕ}
    (hm : m ≤ finrank ℝ V) :
    bettiNumber k (DelzantQuotient i u c) (2 * (finrank ℝ V - m)) =
      bettiNumber k (DelzantQuotient i u c) (2 * m) := by
  obtain ⟨X, hX⟩ := hΔ.exists_forall_edgeBasis_apply_ne_zero hi
  have hX' : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) j,
      (hΔ.isSmoothVertex v hv).edgeBasis hi j (-X) ≠ 0 := fun v hv j ↦ by
    simpa only [map_neg, neg_ne_zero] using hX v hv j
  rw [hΔ.bettiNumber_delzantQuotient_two_mul hi hX' k,
    hΔ.bettiNumber_delzantQuotient_two_mul hi hX k]
  congr 1
  ext v
  refine exists_congr fun hv ↦ ?_
  -- The edges descending for `-X` are the complement of those descending for `X`, among the
  -- `n` edges at `v`.
  have hcompl : {j | (hΔ.isSmoothVertex v hv).edgeBasis hi j (-X) < 0} =
      {j | (hΔ.isSmoothVertex v hv).edgeBasis hi j X < 0}ᶜ := by
    ext j
    simp only [mem_ofPred_eq, mem_compl_iff, map_neg, Left.neg_neg_iff, not_lt]
    exact ⟨le_of_lt, fun h ↦ h.lt_of_ne' (hX v hv j)⟩
  have hcard := ncard_add_ncard_compl {j | (hΔ.isSmoothVertex v hv).edgeBasis hi j X < 0}
  rw [Nat.card_coe_set_eq, (hΔ.mem_extremePoints_iff_ncard_activeSet hi hv.1).1 hv] at hcard
  rw [hcompl]
  omega

end IsDelzant

end TauCeti.Toric
