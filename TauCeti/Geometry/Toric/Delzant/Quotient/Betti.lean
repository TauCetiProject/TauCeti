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
public import TauCeti.Geometry.Toric.Delzant.Quotient.Hamiltonian
public import TauCeti.Geometry.Toric.Delzant.Simplex
import TauCeti.Geometry.Manifold.Algebra.TypeTags
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Perfect
import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap

/-!
# The Betti numbers of a Delzant toric manifold

Let `i : N →+ V` be an integral lattice and `(u, c)` the facet presentation of a Delzant polytope
`Δ ⊆ V*`, with Delzant quotient `M_Δ` (`TauCeti.Toric.DelzantQuotient i u c`), its symplectic
form and its reduced moment map `μ_Δ : M_Δ → V*`. At each vertex `v` of `Δ` the inward edge
vectors `ε_k ∈ V*`, indexed by the facets active at `v`, form a basis
(`TauCeti.Toric.IsSmoothVertex.edgeBasis`). This file computes every Betti number of `M_Δ` from
the polytope: for `x ∈ V` on which no edge vector vanishes,

`b_j(M_Δ) = #{v vertex of Δ | 2 #{k | ε_k(x) < 0} = j}`

(`TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_eq_ncard`), for every division ring of
coefficients. So `b_(2m)` counts the vertices at which exactly `m` of the edges descend for the
linear function `⟨·, x⟩` on `Δ`, and the odd Betti numbers vanish. Such `x` exist
(`TauCeti.Toric.IsDelzant.exists_forall_edgeBasis_apply_ne_zero`), and replacing `x` by `-x`
gives the symmetry `b_(2n - j) = b_j`, `n = dim V`
(`TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_two_mul_finrank_sub`).

**The Morse index at a vertex.** In the Darboux chart of `M_Δ` at a vertex `v`
(`TauCeti.Toric.IsDelzant.vertexDarbouxChart`), with coordinates `w ∈ ℂ^A`, the moment map is the
translated weight model `μ_Δ = v + Σ_k ½ |w_k|² ε_k`
(`TauCeti.Toric.DelzantQuotient.add_weightMomentMap_vertexChart`). So the component
`f = ⟨μ_Δ, x⟩` is the constant `v(x)` plus the weight-model component with weights `-ε_k`, and the
Morse indices of weight-model components
(`TauCeti.manifoldMorseIndex_eq_two_mul_ncard_pos_of_weightMomentMap`) show that `f` has Morse
index `2 #{k | ε_k(x) < 0}` at the point over `v`
(`TauCeti.Toric.IsDelzant.manifoldMorseIndex_vertexChart_symm_zero`).

**Critical points.** If no edge vector at `v` vanishes on `x`, then in the chart at `v` the only
critical point of `f` is the point over `v`, and it is nondegenerate. The vertex charts cover
`M_Δ` (`TauCeti.Toric.IsDelzant.exists_mem_vertexChart_source`), so for such `x` the function `f`
is a Morse function whose critical points are exactly the points over the vertices
(`TauCeti.Toric.IsDelzant.isMorse_reducedMomentMap_apply`,
`TauCeti.Toric.IsDelzant.mem_criticalPoints_reducedMomentMap_apply_iff`).

**Perfection.** The component `f` is a component of the moment map of the torus action on `M_Δ`
(`TauCeti.Toric.IsDelzant.hamiltonianTorusData_delzantQuotientSymplecticForm`), and a moment map
component which is a Morse function is perfect, since all its indices are even
(`TauCeti.SmoothTwoForm.IsMomentMap.isPerfectMorse`,
`TauCeti.Toric.IsDelzant.isPerfectMorse_reducedMomentMap_apply`). So `b_j(M_Δ)` is the number of
critical points of `f` of index `j`, and these lie one over each vertex.

For instance, along the direction `(1, 2, …, n)` the standard `n`-simplex, the polytope of `ℂPⁿ`,
has no descending edge at the vertex `0` and `p + 1` descending edges at the vertex `a e p*`. So
`ℂPⁿ` has Betti number `1` in each even degree `0, 2, …, 2n` and `0` otherwise
(`TauCeti.Toric.bettiNumber_delzantQuotient_simplex`). The edge vectors of the simplex
(`TauCeti.Toric.edgeBasis_simplex_zero`, `TauCeti.Toric.edgeBasis_simplex_smul_proj_none`,
`TauCeti.Toric.edgeBasis_simplex_smul_proj_some`) are identified by their pairings with the active
normals (`TauCeti.Toric.IsSmoothVertex.eq_edgeBasis_iff`).

## Main results

* `TauCeti.Toric.IsDelzant.manifoldMorseIndex_vertexChart_symm_zero`: the Morse index of
  `⟨μ_Δ, x⟩` at the point over a vertex is twice the number of edges along which `⟨·, x⟩`
  decreases.
* `TauCeti.Toric.IsDelzant.mem_criticalPoints_reducedMomentMap_apply`,
  `TauCeti.Toric.IsDelzant.manifoldMorseIndex_reducedMomentMap_apply`: every point over a vertex
  is a critical point of every `⟨μ_Δ, x⟩`, with Morse index twice its number of descending edges.
* `TauCeti.Toric.IsDelzant.isMorse_reducedMomentMap_apply`,
  `TauCeti.Toric.IsDelzant.mem_criticalPoints_reducedMomentMap_apply_iff`: for `x` on which no
  edge vector vanishes, `⟨μ_Δ, x⟩` is a Morse function whose critical points lie over the vertices.
* `TauCeti.Toric.IsDelzant.isPerfectMorse_reducedMomentMap_apply`: for such `x`, `⟨μ_Δ, x⟩` is a
  perfect Morse function for every division ring of coefficients.
* `TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_eq_ncard`: the Betti numbers of `M_Δ`
  count vertices by their descending edges.
* `TauCeti.Toric.IsDelzant.bettiNumber_delzantQuotient_two_mul_finrank_sub`: the symmetry
  `b_(2n - j) = b_j`.
* `TauCeti.Toric.bettiNumber_delzantQuotient_simplex`: the Betti numbers of `ℂPⁿ`.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 and Homework 21.
-/

public section

open Module Set Real Topology
open scoped Manifold ContDiff

namespace TauCeti.Toric

local instance delzantQuotientBettiTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

universe w

variable {ι : Type w} {N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {i : N →+ V} {u : ι → N} {c : ι → ℝ}

namespace IsDelzant

open DelzantQuotient

/-! ### The moment map components near a vertex -/

section Vertex

variable [FiniteDimensional ℝ V] (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
  {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v) (hvP : v ∈ facetPolyhedron i u c)
  [Fintype (activeSet (facetPairing i u) c v)]
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))

/-- In the Darboux chart at a smooth vertex `v`, the component `⟨μ_Δ, x⟩` of the moment map is
the constant `v(x)` plus the weight-model component with the weights `-ε_k`, for the edge basis
`ε` at `v`. -/
private theorem reducedMomentMap_apply_eq_weightMomentMap (x : V) :
    letI := hΔ.delzantQuotientChartedSpace hi
    ∀ q ∈ (hΔ.vertexDarbouxChart hi hv hvP).source, reducedMomentMap hβ q x =
      v x + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (hΔ.vertexDarbouxChart hi hv hvP q) x :=
  fun q hq ↦ by
    rw [vertexDarbouxChart_source] at hq
    rw [← add_weightMomentMap_vertexChart hv hi hvP hq, add_apply,
      ← coe_vertexDarbouxChart hΔ hi hv hvP]

/-- The point over a smooth vertex `v` lies in the Darboux chart at `v`. -/
private theorem vertexChart_symm_zero_mem_vertexDarbouxChart_source :
    letI := hΔ.delzantQuotientChartedSpace hi
    (vertexChart hv hi hvP).symm 0 ∈ (hΔ.vertexDarbouxChart hi hv hvP).source := by
  rw [vertexDarbouxChart_source]
  exact (vertexChart hv hi hvP).map_target (zero_mem_vertexChart_target hv hi hvP)

/-- The point over a smooth vertex `v` is a critical point of every component `⟨μ_Δ, x⟩` of the
moment map. -/
theorem vertexChart_symm_zero_mem_criticalPoints (x : V) :
    letI := hΔ.delzantQuotientChartedSpace hi
    (vertexChart hv hi hvP).symm 0 ∈ criticalPoints
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have h0 := hΔ.vertexChart_symm_zero_mem_vertexDarbouxChart_source hi hv hvP
  rw [mem_criticalPoints_iff_weightGenerator_eq_zero
      (hΔ.reducedMomentMap_apply_eq_weightMomentMap hi hv hvP hβ x) h0, coe_vertexDarbouxChart,
    (vertexChart hv hi hvP).right_inv (zero_mem_vertexChart_target hv hi hvP), map_zero]

/-- **The Morse index at a vertex.** At the point of `M_Δ` over a smooth vertex `v`, the
component `⟨μ_Δ, x⟩` of the moment map has Morse index twice the number of edges at `v` along
which the linear function `⟨·, x⟩` decreases. -/
theorem manifoldMorseIndex_vertexChart_symm_zero (x : V) :
    letI := hΔ.delzantQuotientChartedSpace hi
    manifoldMorseIndex 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
      (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) ((vertexChart hv hi hvP).symm 0) =
      2 * {k | hv.edgeBasis hi k x < 0}.ncard := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have h0 := hΔ.vertexChart_symm_zero_mem_vertexDarbouxChart_source hi hv hvP
  rw [manifoldMorseIndex_eq_two_mul_ncard_pos_of_weightMomentMap
    (hΔ.reducedMomentMap_apply_eq_weightMomentMap hi hv hvP hβ x) h0
    (hΔ.vertexChart_symm_zero_mem_criticalPoints hi hv hvP hβ x)]
  simp only [neg_apply, neg_pos]

/-- **Critical points near a vertex.** If no edge vector at a smooth vertex `v` vanishes on `x`,
then the only critical point of `⟨μ_Δ, x⟩` in the chart at `v` is the point over `v`, and it is
nondegenerate. -/
theorem eq_vertexChart_symm_zero_and_isManifoldNondegenerateCriticalPoint {x : V}
    (hx : ∀ k, hv.edgeBasis hi k x ≠ 0) {q : DelzantQuotient i u c}
    (hq : q ∈ (vertexChart hv hi hvP).source)
    (hcrit : letI := hΔ.delzantQuotientChartedSpace hi
      q ∈ criticalPoints 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x)) :
    letI := hΔ.delzantQuotientChartedSpace hi
    q = (vertexChart hv hi hvP).symm 0 ∧
      IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, ProperSMul.QuotientModelSpace
        (kernelTorusLieAlgebra i u) (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) q := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have hf := hΔ.reducedMomentMap_apply_eq_weightMomentMap hi hv hvP hβ x
  have hq' : q ∈ (hΔ.vertexDarbouxChart hi hv hvP).source := by
    rwa [vertexDarbouxChart_source]
  have hne : ∀ k, (-hv.edgeBasis hi k) x ≠ 0 := fun k ↦ by
    simpa only [neg_apply, neg_ne_zero] using hx k
  refine ⟨?_, (isManifoldNondegenerateCriticalPoint_iff_forall_ne_zero_of_weightMomentMap hf hq'
    hcrit).2 hne⟩
  -- In the chart, the model generator vanishes only at the origin.
  have hgen := (mem_criticalPoints_iff_weightGenerator_eq_zero hf hq').1 hcrit
  rw [weightGenerator_apply_eq_zero_iff, coe_vertexDarbouxChart] at hgen
  have hw : vertexChart hv hi hvP q = 0 := by
    refine Prod.ext (PiLp.ext fun k ↦ ?_) (PiLp.ext fun k ↦ ?_)
    · by_contra hk
      exact hne k (hgen k (.inl hk))
    · by_contra hk
      exact hne k (hgen k (.inr hk))
  rw [← hw, (vertexChart hv hi hvP).left_inv hq]

end Vertex

/-! ### Morse components and Betti numbers -/

variable (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))

/-- Every critical point of a component `⟨μ_Δ, x⟩` along which no edge vector vanishes is the
point over some vertex. -/
private theorem exists_eq_vertexChart_symm_zero [FiniteDimensional ℝ V] {x : V}
    (hx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) k,
      (hΔ.isSmoothVertex v hv).edgeBasis hi k x ≠ 0) {q : DelzantQuotient i u c}
    (hcrit : letI := hΔ.delzantQuotientChartedSpace hi
      q ∈ criticalPoints 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x)) :
    letI := hΔ.delzantQuotientChartedSpace hi
    ∃ (v : StrongDual ℝ V) (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ),
      haveI := Fintype.ofFinite (activeSet (facetPairing i u) c v)
      q = (vertexChart (hΔ.isSmoothVertex v hv) hi hv.1).symm 0 ∧
        IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, ProperSMul.QuotientModelSpace
          (kernelTorusLieAlgebra i u) (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
          (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) q := by
  classical
  obtain ⟨v, hv, hq⟩ := hΔ.exists_mem_vertexChart_source hi q
  let := Fintype.ofFinite (activeSet (facetPairing i u) c v)
  -- Read the membership in the source for the chart built with this `Fintype` instance.
  rw [vertexChart_source] at hq
  rw [← vertexChart_source (hΔ.isSmoothVertex v hv) hi hv.1] at hq
  exact ⟨v, hv, hΔ.eq_vertexChart_symm_zero_and_isManifoldNondegenerateCriticalPoint hi _ hv.1 hβ
    (hx v hv) hq hcrit⟩

/-- The point of `M_Δ` over a vertex of `Δ` is the centre of the vertex chart there. -/
private theorem eq_vertexChart_symm_zero [FiniteDimensional ℝ V] {q : DelzantQuotient i u c}
    (hq : reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ)
    [Fintype (activeSet (facetPairing i u) c (reducedMomentMap hβ q))] :
    q = (vertexChart (hΔ.isSmoothVertex _ hq) hi hq.1).symm 0 := by
  have hs := mem_vertexChart_source_of_reducedMomentMap_eq (hΔ.isSmoothVertex _ hq) hi hq.1 rfl
  rw [← (vertexChart_eq_zero_iff _ hi hq.1 hs).2 rfl, (vertexChart _ hi hq.1).left_inv hs]

/-- **The points over the vertices are critical.** At the point of `M_Δ` over a vertex of `Δ`,
every component `⟨μ_Δ, x⟩` of the moment map has a critical point. -/
theorem mem_criticalPoints_reducedMomentMap_apply [FiniteDimensional ℝ V] (x : V)
    {q : DelzantQuotient i u c}
    (hq : reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    letI := hΔ.delzantQuotientChartedSpace hi
    q ∈ criticalPoints 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) := by
  let := Fintype.ofFinite (activeSet (facetPairing i u) c (reducedMomentMap hβ q))
  rw [hΔ.eq_vertexChart_symm_zero hi hβ hq]
  exact hΔ.vertexChart_symm_zero_mem_criticalPoints hi _ hq.1 hβ x

/-- **The Morse index at the point over a vertex.** At a point of `M_Δ` over a vertex of `Δ`, the
component `⟨μ_Δ, x⟩` of the moment map has Morse index twice the number of edges there along
which `⟨·, x⟩` decreases. -/
theorem manifoldMorseIndex_reducedMomentMap_apply [FiniteDimensional ℝ V] (x : V)
    {q : DelzantQuotient i u c}
    (hq : reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    letI := hΔ.delzantQuotientChartedSpace hi
    manifoldMorseIndex 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) q =
      2 * {k | (hΔ.isSmoothVertex _ hq).edgeBasis hi k x < 0}.ncard := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  let := Fintype.ofFinite (activeSet (facetPairing i u) c (reducedMomentMap hβ q))
  exact (congrArg (manifoldMorseIndex _ _) (hΔ.eq_vertexChart_symm_zero hi hβ hq)).trans
    (hΔ.manifoldMorseIndex_vertexChart_symm_zero hi _ hq.1 hβ x)

/-- **Critical points of a generic component.** If no edge vector at any vertex of `Δ` vanishes
on `x`, then a point of `M_Δ` is a critical point of `⟨μ_Δ, x⟩` exactly when its moment value is
a vertex of `Δ`. -/
theorem mem_criticalPoints_reducedMomentMap_apply_iff [FiniteDimensional ℝ V] {x : V}
    (hx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) k,
      (hΔ.isSmoothVertex v hv).edgeBasis hi k x ≠ 0) {q : DelzantQuotient i u c} :
    letI := hΔ.delzantQuotientChartedSpace hi
    q ∈ criticalPoints 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) ↔
      reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  constructor
  · intro hcrit
    obtain ⟨v, hv, rfl, -⟩ := hΔ.exists_eq_vertexChart_symm_zero hi hβ hx hcrit
    rwa [reducedMomentMap_vertexChart_symm_zero]
  · exact hΔ.mem_criticalPoints_reducedMomentMap_apply hi hβ x

/-- **Generic components are Morse functions.** If no edge vector at any vertex of `Δ` vanishes
on `x`, then the component `⟨μ_Δ, x⟩` of the moment map is a Morse function on `M_Δ`. -/
theorem isMorse_reducedMomentMap_apply [FiniteDimensional ℝ V] {x : V}
    (hx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) k,
      (hΔ.isSmoothVertex v hv).edgeBasis hi k x ≠ 0) :
    letI := hΔ.delzantQuotientChartedSpace hi
    IsMorse 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ))
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints]
  refine ⟨((hΔ.contMDiff_reducedMomentMap hi hβ).clm_apply contMDiff_const).contMDiffOn,
    fun q _ hcrit ↦ ?_⟩
  obtain ⟨v, hv, -, hnd⟩ := hΔ.exists_eq_vertexChart_symm_zero hi hβ hx hcrit
  exact hnd

/-- **Generic components are perfect Morse functions.** If no edge vector at any vertex of `Δ`
vanishes on `x`, then the component `⟨μ_Δ, x⟩` of the moment map is a perfect Morse function on
`M_Δ`, for every division ring of coefficients. -/
theorem isPerfectMorse_reducedMomentMap_apply (k : Type w) [DivisionRing k]
    [FiniteDimensional ℝ V] {x : V}
    (hx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) e,
      (hΔ.isSmoothVertex v hv).edgeBasis hi e x ≠ 0) :
    letI := hΔ.delzantQuotientChartedSpace hi
    IsPerfectMorse 𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
        (Fin (Fintype.card ι + finrank ℝ V) → ℝ)) k
        (fun q : DelzantQuotient i u c ↦ reducedMomentMap hβ q x) := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ.contMDiffVAdd_delzantQuotient hi
  have := hi.t2Space_delzantQuotient (u := u) (c := c)
  have := compactSpace_delzantQuotient (c := c) hΔ.isBounded
  have h := hΔ.hamiltonianTorusData_delzantQuotientSymplecticForm hi hβ
  have hσ := (hΔ.isSymplectic_delzantQuotientSymplecticForm hi).isNondegenerate
  have hσG := fun g ↦
    ((SmoothTwoForm.isSymplecticMap_iff_mpullback_eq _).2 (h.mpullback_smul g)).apply
  -- The component `⟨μ_Δ, x⟩` is the component of the torus moment map along a preimage of `x`.
  obtain ⟨ξ, rfl⟩ := hβ x
  exact h.toIsMomentMap.isPerfectMorse hσ hσG k (ξ := ξ)
    (hΔ.isMorse_reducedMomentMap_apply hi hβ hx)

/-- **The Betti numbers of a Delzant toric manifold.** For `x ∈ V` on which no edge vector at any
vertex of `Δ` vanishes, the Betti number `b_j(M_Δ)`, for any division ring of coefficients, is
the number of vertices of `Δ` at which twice the number of edges along which `⟨·, x⟩` decreases
is `j`. -/
theorem bettiNumber_delzantQuotient_eq_ncard (k : Type w) [DivisionRing k] {x : V}
    (hx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) e,
      (hΔ.isSmoothVertex v hv).edgeBasis hi e x ≠ 0) (j : ℕ) :
    bettiNumber k (DelzantQuotient i u c) j =
      {v | ∃ hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ,
        2 * {e | (hΔ.isSmoothVertex v hv).edgeBasis hi e x < 0}.ncard = j}.ncard := by
  have := hi.finiteDimensional
  have hβ := surjective_linearCombination_real hi.span_range_eq_top hΔ.surjective_linearCombination
  let _ := hΔ.delzantQuotientChartedSpace hi
  rw [(hΔ.isPerfectMorse_reducedMomentMap_apply hi hβ k hx).bettiNumber_eq_ncard j]
  refine BijOn.ncard_eq (f := reducedMomentMap hβ) ⟨fun q ⟨hcrit, hj⟩ ↦ ?_,
    fun q ⟨hcrit, _⟩ q' ⟨hcrit', _⟩ hqq' ↦ ?_, fun v ⟨hv, hj⟩ ↦ ?_⟩
  · obtain ⟨v, hv, rfl, -⟩ := hΔ.exists_eq_vertexChart_symm_zero hi hβ hx hcrit
    let := Fintype.ofFinite (activeSet (facetPairing i u) c v)
    exact (reducedMomentMap_vertexChart_symm_zero _ hi hv.1).symm ▸
      ⟨hv, (hΔ.manifoldMorseIndex_vertexChart_symm_zero hi _ hv.1 hβ _).symm.trans hj⟩
  · obtain ⟨v, hv, rfl, -⟩ := hΔ.exists_eq_vertexChart_symm_zero hi hβ hx hcrit
    obtain ⟨v', hv', rfl, -⟩ := hΔ.exists_eq_vertexChart_symm_zero hi hβ hx hcrit'
    let := Fintype.ofFinite (activeSet (facetPairing i u) c v)
    let := Fintype.ofFinite (activeSet (facetPairing i u) c v')
    rw [reducedMomentMap_vertexChart_symm_zero, reducedMomentMap_vertexChart_symm_zero] at hqq'
    subst hqq'
    rfl
  · let := Fintype.ofFinite (activeSet (facetPairing i u) c v)
    exact ⟨(vertexChart (hΔ.isSmoothVertex v hv) hi hv.1).symm 0,
      ⟨hΔ.vertexChart_symm_zero_mem_criticalPoints hi _ hv.1 hβ _,
        (hΔ.manifoldMorseIndex_vertexChart_symm_zero hi _ hv.1 hβ _).trans hj⟩,
      reducedMomentMap_vertexChart_symm_zero _ hi hv.1⟩

include hΔ hi in
/-- **Symmetry of the Betti numbers.** The Betti numbers of a Delzant toric manifold of dimension
`2 n`, `n = dim V`, satisfy `b_(2n - j) = b_j`: reversing the direction `x` exchanges the
descending and ascending edges at every vertex. -/
theorem bettiNumber_delzantQuotient_two_mul_finrank_sub (k : Type w) [DivisionRing k] {j : ℕ}
    (hj : j ≤ 2 * finrank ℝ V) :
    bettiNumber k (DelzantQuotient i u c) (2 * finrank ℝ V - j) =
      bettiNumber k (DelzantQuotient i u c) j := by
  obtain ⟨x, hx⟩ := hΔ.exists_forall_edgeBasis_apply_ne_zero hi
  have hnx : ∀ v (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ) e,
      (hΔ.isSmoothVertex v hv).edgeBasis hi e (-x) ≠ 0 := fun v hv e ↦ by
    rw [map_neg, neg_ne_zero]
    exact hx v hv e
  rw [hΔ.bettiNumber_delzantQuotient_eq_ncard hi k hnx,
    hΔ.bettiNumber_delzantQuotient_eq_ncard hi k hx]
  congr 1
  ext v
  refine exists_congr fun hv ↦ ?_
  -- At each vertex the edges descending for `-x` are those ascending for `x`.
  set s := {e | (hΔ.isSmoothVertex v hv).edgeBasis hi e x < 0}
  have hs : {e | (hΔ.isSmoothVertex v hv).edgeBasis hi e (-x) < 0} = sᶜ := by
    ext e
    simp only [mem_ofPred_eq, mem_compl_iff, s, map_neg, neg_neg_iff_pos, not_lt]
    exact ⟨le_of_lt, fun he ↦ he.lt_of_ne' (hx v hv e)⟩
  have hcard : s.ncard + sᶜ.ncard = finrank ℝ V := by
    rw [ncard_add_ncard_compl, Nat.card_coe_set_eq, (hΔ.isSmoothVertex v hv).ncard_activeSet,
      hi.finrank_eq]
  rw [hs]
  omega

end IsDelzant

/-! ### Complex projective space -/

section Simplex

variable {n : ℕ} {a : ℝ}

/-- The generic direction `x = (1, 2, …, n)` used for the standard simplex. -/
private def simplexDirection (n : ℕ) : Fin n → ℝ := fun k ↦ (k : ℝ) + 1

/-- At the vertex `0` of the standard simplex, no edge descends along `(1, 2, …, n)`. -/
private theorem ncard_edgeBasis_simplexDirection_zero (ha : 0 < a)
    (hv : IsSmoothVertex ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a) 0) :
    {e | hv.edgeBasis (isIntegralLattice_intCast n) e (simplexDirection n) < 0}.ncard = 0 := by
  rw [ncard_eq_zero, eq_empty_iff_forall_notMem]
  rintro ⟨j, hj⟩ he
  cases j with
  | none => exact absurd hj (none_notMem_activeSet_simplex_zero ha.ne')
  | some k =>
    rw [mem_ofPred_eq, edgeBasis_simplex_zero ha.ne' _ hv _ rfl] at he
    simp only [ContinuousLinearMap.proj_apply, simplexDirection] at he
    linarith [(k : ℕ).cast_nonneg (α := ℝ)]

/-- At the vertex `a e p*` of the standard simplex, exactly `p + 1` edges descend along
`(1, 2, …, n)`: the edge towards the vertex `0` and the edges towards the vertices `a e k*` with
`k < p`. -/
private theorem ncard_edgeBasis_simplexDirection_smul_proj (ha : 0 < a) {p : Fin n}
    (hv : IsSmoothVertex ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a) (a • ContinuousLinearMap.proj p)) :
    {e | hv.edgeBasis (isIntegralLattice_intCast n) e (simplexDirection n) < 0}.ncard =
      p + 1 := by
  classical
  -- The descending edges are those leaving the slanted facet and the facets `x(e k) ≥ 0`, `k < p`.
  have himage : Subtype.val ''
      {e | hv.edgeBasis (isIntegralLattice_intCast n) e (simplexDirection n) < 0} =
      insert none (some '' Iio p) := by
    ext j
    constructor
    · rintro ⟨⟨j, hj⟩, he, rfl⟩
      cases j with
      | none => exact mem_insert _ _
      | some k =>
        rw [mem_ofPred_eq, edgeBasis_simplex_smul_proj_some ha.ne' _ hv _ rfl] at he
        simp only [sub_apply, ContinuousLinearMap.proj_apply,
          simplexDirection, sub_neg, add_lt_add_iff_right, Nat.cast_lt] at he
        exact mem_insert_of_mem _ ⟨k, Fin.lt_def.2 he, rfl⟩
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · have hj : none ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n))
            (simplexNormal (Fin n))) (simplexSupport a) (a • ContinuousLinearMap.proj p) :=
          (mem_activeSet_simplex_smul_proj_iff ha.ne').2 (Option.some_ne_none p).symm
        refine ⟨⟨none, hj⟩, ?_, rfl⟩
        rw [mem_ofPred_eq, edgeBasis_simplex_smul_proj_none ha.ne' _ hv _ rfl]
        simp only [neg_apply, ContinuousLinearMap.proj_apply,
          simplexDirection, neg_neg_iff_pos]
        positivity
      · have hkp : k ≠ p := (Fin.lt_def.1 hk).ne ∘ congrArg Fin.val
        have hj : some k ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n))
            (simplexNormal (Fin n))) (simplexSupport a) (a • ContinuousLinearMap.proj p) :=
          (mem_activeSet_simplex_smul_proj_iff ha.ne').2 (Option.some_injective _ |>.ne hkp)
        refine ⟨⟨some k, hj⟩, ?_, rfl⟩
        rw [mem_ofPred_eq, edgeBasis_simplex_smul_proj_some ha.ne' _ hv _ rfl]
        simp only [sub_apply, ContinuousLinearMap.proj_apply,
          simplexDirection, sub_neg, add_lt_add_iff_right, Nat.cast_lt]
        exact Fin.lt_def.1 hk
  rw [← ncard_image_of_injective _ Subtype.val_injective, himage,
    ncard_insert_of_notMem (by simp), ncard_image_of_injective _ (Option.some_injective _),
    ncard_eq_toFinset_card', toFinset_Iio, Fin.card_Iio, add_comm]

/-- No edge vector of the standard simplex vanishes on the direction `(1, 2, …, n)`. -/
private theorem edgeBasis_simplexDirection_ne_zero (ha : 0 < a)
    (hΔ : IsDelzant ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a))
    (v : StrongDual ℝ (Fin n → ℝ)) (hv : v ∈ (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal (Fin n)) (simplexSupport a)).extremePoints ℝ) (e) :
    (hΔ.isSmoothVertex v hv).edgeBasis (isIntegralLattice_intCast n) e (simplexDirection n) ≠
      0 := by
  obtain ⟨e, he⟩ := e
  rcases (mem_extremePoints_facetPolyhedron_simplex_iff ha).1 hv with rfl | ⟨p, rfl⟩
  · cases e with
    | none => exact absurd he (none_notMem_activeSet_simplex_zero ha.ne')
    | some l =>
      rw [edgeBasis_simplex_zero ha.ne' _ _ _ rfl]
      simp only [ContinuousLinearMap.proj_apply, simplexDirection]
      positivity
  · cases e with
    | none =>
      rw [edgeBasis_simplex_smul_proj_none ha.ne' _ _ _ rfl]
      simp only [neg_apply, ContinuousLinearMap.proj_apply, simplexDirection, neg_ne_zero]
      positivity
    | some l =>
      rw [edgeBasis_simplex_smul_proj_some ha.ne' _ _ _ rfl]
      simp only [sub_apply, ContinuousLinearMap.proj_apply, simplexDirection, ne_eq, sub_eq_zero,
        add_left_inj, Nat.cast_inj]
      exact fun h ↦ (mem_activeSet_simplex_smul_proj_iff ha.ne').1 he (congrArg some (Fin.ext h))

/-- The vertices of the standard simplex with their numbers of edges descending along
`(1, 2, …, n)`: none at the vertex `0` and `p + 1` at the vertex `a e p*`. -/
private theorem ncard_edgeBasis_simplexDirection (ha : 0 < a)
    (hΔ : IsDelzant ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a))
    (v : StrongDual ℝ (Fin n → ℝ)) (hv : v ∈ (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal (Fin n)) (simplexSupport a)).extremePoints ℝ) :
    (v = 0 ∧ {e | (hΔ.isSmoothVertex v hv).edgeBasis (isIntegralLattice_intCast n) e
      (simplexDirection n) < 0}.ncard = 0) ∨
    ∃ p : Fin n, v = a • ContinuousLinearMap.proj p ∧
      {e | (hΔ.isSmoothVertex v hv).edgeBasis (isIntegralLattice_intCast n) e
        (simplexDirection n) < 0}.ncard = p + 1 := by
  rcases (mem_extremePoints_facetPolyhedron_simplex_iff ha).1 hv with rfl | ⟨p, rfl⟩
  · exact .inl ⟨rfl, ncard_edgeBasis_simplexDirection_zero ha _⟩
  · exact .inr ⟨p, rfl, ncard_edgeBasis_simplexDirection_smul_proj ha _⟩

/-- **The Betti numbers of `ℂPⁿ`.** The Delzant quotient of the standard `n`-simplex, which is
`ℂPⁿ` (`TauCeti.Toric.DelzantQuotient.simplexHomeomorph`), has Betti number `1` in each even
degree `0, 2, …, 2n` and `0` in every other degree, for every division ring of coefficients. -/
theorem bettiNumber_delzantQuotient_simplex (hn : 0 < n) (ha : 0 < a) (k : Type) [DivisionRing k]
    (j : ℕ) :
    bettiNumber k (DelzantQuotient ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a)) j = if Even j ∧ j ≤ 2 * n then 1 else 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hΔ := isDelzant_simplex (κ := Fin n) ha
  -- Count the vertices by their edges descending along the generic direction `(1, 2, …, n)`.
  rw [hΔ.bettiNumber_delzantQuotient_eq_ncard (isIntegralLattice_intCast n) k
    (edgeBasis_simplexDirection_ne_zero ha hΔ) j]
  split_ifs with hj
  · -- The unique vertex with `j / 2` descending edges.
    obtain ⟨⟨m, rfl⟩, hm⟩ := hj
    rw [ncard_eq_one]
    cases m with
    | zero =>
      refine ⟨0, Set.ext fun v ↦ ⟨fun ⟨hv, hv'⟩ ↦ ?_, ?_⟩⟩
      · rcases ncard_edgeBasis_simplexDirection ha hΔ v hv with ⟨rfl, -⟩ | ⟨p, rfl, hp⟩
        · rfl
        · omega
      · rintro rfl
        have hv := (mem_extremePoints_facetPolyhedron_simplex_iff (κ := Fin n) ha).2 (.inl rfl)
        exact ⟨hv, by rw [ncard_edgeBasis_simplexDirection_zero ha]⟩
    | succ m =>
      refine ⟨a • ContinuousLinearMap.proj ⟨m, by omega⟩,
        Set.ext fun v ↦ ⟨fun ⟨hv, hv'⟩ ↦ ?_, ?_⟩⟩
      · rcases ncard_edgeBasis_simplexDirection ha hΔ v hv with ⟨rfl, hp⟩ | ⟨p, rfl, hp⟩
        · omega
        · rw [mem_singleton_iff,
            show p = (⟨m, by omega⟩ : Fin n) from Fin.ext (by dsimp only; omega)]
      · rintro rfl
        have hv := (mem_extremePoints_facetPolyhedron_simplex_iff (κ := Fin n) ha).2
          (.inr ⟨⟨m, by omega⟩, rfl⟩)
        exact ⟨hv, by rw [ncard_edgeBasis_simplexDirection_smul_proj ha]; dsimp only; omega⟩
  · -- No vertex has a number of descending edges outside `0, …, n`.
    refine (ncard_eq_zero ?_).2 (eq_empty_iff_forall_notMem.2 fun v ⟨hv, hv'⟩ ↦ ?_)
    · exact finite_extremePoints_facetPolyhedron.subset fun _ ⟨hv, _⟩ ↦ hv
    rcases ncard_edgeBasis_simplexDirection ha hΔ v hv with ⟨-, hp⟩ | ⟨p, -, hp⟩
    · exact hj ⟨⟨0, by omega⟩, by omega⟩
    · exact hj ⟨⟨p + 1, by omega⟩, by omega⟩

end Simplex

end TauCeti.Toric
