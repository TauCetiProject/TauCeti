/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import TauCeti.Geometry.Toric.Delzant.Quotient.Basic
public import TauCeti.Geometry.Toric.Delzant.Stabilizer
public import TauCeti.Geometry.Toric.Delzant.TangentCone

/-!
# Vertices of the Delzant quotient: fixed points and local models

Let `i : N →+ V` be an integral lattice, let `(u, c)` be a facet presentation of the polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`, and let `M_Δ = Z / N_Δ`
(`TauCeti.Toric.DelzantQuotient i u c`) be its Delzant quotient, with the action of the residual
torus `T = (ℝ / 2πℤ)^ι / N_Δ` and the reduced moment map `μ_Δ : M_Δ → V*`. This file describes
`M_Δ` near the points over the vertices of `Δ`.

**Fixed points.** A point of `M_Δ` is fixed by the whole residual torus exactly when its moment
value is a vertex of `Δ` (`TauCeti.Toric.DelzantQuotient.mem_fixedPoints_iff`), and `μ_Δ`
restricts to a bijection from the fixed points onto the vertices
(`TauCeti.Toric.DelzantQuotient.bijOn_reducedMomentMap_fixedPoints`): over each vertex lies
exactly one point, and it is fixed.

**The torus at a smooth vertex.** Let `v` be a smooth vertex of the presentation: the normals of
the set `A` of facets active at `v` form a basis `b` of `N`
(`TauCeti.Toric.IsSmoothVertex.basis`). Write `u j = Σ_(k ∈ A) a_(j k) b_k` with integers
`a_(j k)`. Reading `facetTorusHom` in the basis `i ∘ b` gives the homomorphism
`D : (ℝ / 2πℤ)^ι → (ℝ / 2πℤ)^A`, `D(θ)_k = Σ_j a_(j k) θ_j`
(`TauCeti.Toric.IsSmoothVertex.vertexTorusHom`), whose kernel is the kernel torus `N_Δ`. Since
`D` is the identity on the angles supported on `A`, it induces an isomorphism of the residual
torus with the standard torus `(ℝ / 2πℤ)^A`
(`TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv`), whose inverse sends `φ` to the class of `φ`
extended by zero.

**The local model.** Let `ε_k` be the inward edge basis at `v`, dual to the active normals
(`TauCeti.Toric.IsSmoothVertex.edgeBasis`). The *vertex chart*
(`TauCeti.Toric.DelzantQuotient.vertexChart`) is a homeomorphism from the open set of points of
`M_Δ` whose active facets lie in `A` onto the open set `W ⊆ ℂ^A` of the `w` with
`c j < ⟨v + Σ_k ½ |w_k|² ε_k, u j⟩` for every facet `j ∉ A`. Its inverse sends `w` to the class
of the point `z ∈ Z` with `z_k = w_k` for `k ∈ A` and `z_j = √(2(⟨y, u j⟩ - c j))` for `j ∉ A`,
where `y = v + Σ_k ½ |w_k|² ε_k`. In the other direction, a class `[z]` is sent to the
coordinates in `A` of the unique representative of `[z]` whose coordinates outside `A` are
positive reals. In this chart

* the moment map is the translate of the weight model at `v`:
  `μ_Δ = v + Σ_k ½ |w_k|² ε_k`
  (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_vertexChart_symm`);
* the residual torus acts by the standard rotation `w_k ↦ exp(-i φ_k) w_k` of `ℂ^A`, through the
  isomorphism `(ℝ / 2πℤ)^A ≃ T` above
  (`TauCeti.Toric.DelzantQuotient.vertexChart_symm_torusRotation`,
  `TauCeti.Toric.DelzantQuotient.vertexChart_vadd`).

So near the fixed point over a smooth vertex, `M_Δ` with its torus action and moment map is
equivariantly homeomorphic to an open invariant subset of `ℂ^n`, `n = dim V`, with the standard
action and a translated quadratic moment map. For a Delzant polytope every vertex is smooth, and
every point of `Δ` has its active facets among those of some vertex
(`TauCeti.Toric.exists_mem_extremePoints_activeSet_subset`), so by
`TauCeti.Toric.DelzantQuotient.mem_vertexChart_source_iff` the charts at the vertices cover
`M_Δ`.

## Main definitions

* `TauCeti.Toric.IsSmoothVertex.vertexTorusHom`: the homomorphism `facetTorusHom` in the
  coordinates of the lattice basis of the active normals.
* `TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv`: the residual torus as `(ℝ / 2πℤ)^A`.
* `TauCeti.Toric.DelzantQuotient.vertexChart`: the equivariant chart of `M_Δ` at a smooth vertex.

## Main results

* `TauCeti.Toric.DelzantQuotient.mem_fixedPoints_iff`,
  `TauCeti.Toric.DelzantQuotient.bijOn_reducedMomentMap_fixedPoints`: fixed points correspond
  exactly to vertices.
* `TauCeti.Toric.IsSmoothVertex.ker_vertexTorusHom`: the kernel of `D` is the kernel torus.
* `TauCeti.Toric.DelzantQuotient.mem_vertexChart_source_iff`: the source of the vertex chart is
  the set of points whose active facets are active at `v`.
* `TauCeti.Toric.DelzantQuotient.reducedMomentMap_vertexChart_symm`: the moment map in the chart.
* `TauCeti.Toric.DelzantQuotient.vertexChart_symm_torusRotation`,
  `TauCeti.Toric.DelzantQuotient.vertexChart_vadd`: equivariance of the chart.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28 and 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Real

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### Fixed points and vertices -/

namespace DelzantQuotient

section FixedPoints

variable [FiniteDimensional ℝ V]
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
include hβ

/-- **Fixed points are the points over the vertices.** A point of the Delzant quotient is fixed
by the whole residual torus exactly when its moment value is a vertex of `Δ`. -/
theorem mem_fixedPoints_iff (hi : IsIntegralLattice i) {q : DelzantQuotient i u c} :
    q ∈ AddAction.fixedPoints ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
        (DelzantQuotient i u c) ↔
      reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  have hu : Submodule.span ℝ (range fun j ↦ i (u j)) = ⊤ := by
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact hβ
  rw [AddAction.mem_fixedPoints, ← forall_exists_weightRotation_neg_apply_eq_iff_mem_extremePoints
    hi hu fun j ↦ (reducedMomentMap_mk_apply hβ x j).symm]
  -- The class of real angles `t` fixes the class of `x` exactly when the rotation of `x` by `-t`
  -- is a rotation of `x` by an element of the kernel torus.
  have key (t : ι → ℝ) :
      ((fun j ↦ (t j : AddCircle (2 * π)) : ι → AddCircle (2 * π)) :
        (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ mk x = mk x ↔
      ∃ t' : ι → ℝ, (fun j ↦ (t' j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
        weightRotation (-t) x = weightRotation (-t') x := by
    rw [coe_vadd_mk, mk_eq_mk_iff]
    constructor
    · rintro ⟨θ, hθ, h⟩
      choose t' ht' using fun j ↦ QuotientAddGroup.mk_surjective (θ j)
      obtain rfl : (fun j ↦ (t' j : AddCircle (2 * π))) = θ := funext ht'
      refine ⟨t', hθ, ?_⟩
      simpa only [coe_vadd_delzantLevel, torusRotation_coe] using (congrArg Subtype.val h).symm
    · rintro ⟨t', ht', h⟩
      exact ⟨_, ht', Subtype.ext (by simp only [coe_vadd_delzantLevel, torusRotation_coe, h])⟩
  refine ⟨fun h t ↦ (key t).1 (h _), fun h θ ↦ ?_⟩
  induction θ using QuotientAddGroup.induction_on with | H θ =>
  choose t ht using fun j ↦ QuotientAddGroup.mk_surjective (θ j)
  obtain rfl : (fun j ↦ (t j : AddCircle (2 * π))) = θ := funext ht
  exact (key t).2 (h t)

/-- **Fixed points correspond exactly to vertices.** The reduced moment map restricts to a
bijection from the fixed points of the residual torus onto the vertices of `Δ`. In particular
exactly one point of the Delzant quotient lies over each vertex. -/
theorem bijOn_reducedMomentMap_fixedPoints (hi : IsIntegralLattice i) :
    BijOn (reducedMomentMap hβ)
      (AddAction.fixedPoints ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
        (DelzantQuotient i u c))
      ((facetPolyhedron i u c).extremePoints ℝ) := by
  refine ⟨fun q hq ↦ (mem_fixedPoints_iff hβ hi).1 hq, fun q hq q' hq' h ↦ ?_, fun y hy ↦ ?_⟩
  · -- Two points with the same moment value lie in one orbit, and `q'` is fixed.
    obtain ⟨θ, rfl⟩ := (reducedMomentMap_eq_reducedMomentMap_iff hβ).1 h
    exact hq' θ
  · obtain ⟨q, rfl⟩ : y ∈ range (reducedMomentMap hβ (c := c)) := by
      rw [range_reducedMomentMap hβ]
      exact hy.1
    exact ⟨q, (mem_fixedPoints_iff hβ hi).2 hy, rfl⟩

end FixedPoints

end DelzantQuotient

/-! ### Extension by zero -/

section ExtendByZero

variable {ι : Type*} {s : Set ι} {M : Type*} [Zero M]

/-- The extension by zero of a function on a subset vanishes outside the subset. -/
private theorem extend_apply_of_notMem {j : ι} (hj : j ∉ s) (φ : s → M) :
    (Function.extend Subtype.val φ 0 : ι → M) j = 0 :=
  Function.extend_apply' (f := Subtype.val) _ _ _ fun ⟨a, ha⟩ ↦ hj (ha ▸ a.2)

/-- Extension by zero from a subset is continuous. -/
private theorem continuous_extend_zero [TopologicalSpace M] :
    Continuous fun φ : s → M ↦ (Function.extend Subtype.val φ 0 : ι → M) := by
  refine continuous_pi fun j ↦ ?_
  by_cases hj : j ∈ s
  · exact (continuous_apply _).congr fun φ ↦ (Subtype.val_injective.extend_apply φ 0 ⟨j, hj⟩).symm
  · exact continuous_const.congr fun φ ↦ (extend_apply_of_notMem hj φ).symm

end ExtendByZero

/-! ### The residual torus at a smooth vertex -/

namespace IsSmoothVertex

variable {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)

/-- The homomorphism `facetTorusHom` read in the coordinates of the lattice basis formed by the
normals active at a smooth vertex `v`: writing `u j = Σ_(k ∈ A) a_(j k) u_k`, it sends `θ` to
`(Σ_j a_(j k) θ_j)_(k ∈ A)`. Its kernel is the kernel torus
(`TauCeti.Toric.IsSmoothVertex.ker_vertexTorusHom`). -/
def vertexTorusHom :
    (ι → AddCircle (2 * π)) →+ (activeSet (facetPairing i u) c v → AddCircle (2 * π)) where
  toFun θ k := ∑ j, hv.basis.repr (u j) k • θ j
  map_zero' := by ext; simp
  map_add' θ θ' := by ext; simp [smul_add, Finset.sum_add_distrib]

@[simp]
theorem vertexTorusHom_apply (θ : ι → AddCircle (2 * π)) (k : activeSet (facetPairing i u) c v) :
    hv.vertexTorusHom θ k = ∑ j, hv.basis.repr (u j) k • θ j :=
  (rfl)

/-- The homomorphism `vertexTorusHom` is continuous. -/
theorem continuous_vertexTorusHom : Continuous hv.vertexTorusHom :=
  continuous_pi fun _ ↦ continuous_finsetSum _ fun j _ ↦
    (continuous_zsmul _).comp (continuous_apply j)

/-- The kernel of `vertexTorusHom` is the kernel torus. -/
theorem ker_vertexTorusHom (hi : IsIntegralLattice i) :
    hv.vertexTorusHom.ker = (facetTorusHom i u (2 * π)).ker := by
  ext θ
  rw [mem_ker_facetTorusHom_iff_of_basis hi hv.basis, AddMonoidHom.mem_ker, funext_iff]
  rfl

/-- `vertexTorusHom` is the identity on the angles supported on the active facets: it sends the
extension by zero of `φ : (ℝ / 2πℤ)^A` back to `φ`. -/
@[simp]
theorem vertexTorusHom_extend (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π)) :
    hv.vertexTorusHom (Function.extend Subtype.val φ 0) = φ := by
  ext k
  rw [vertexTorusHom_apply, Finset.sum_eq_single (k : ι)]
  · rw [Subtype.val_injective.extend_apply, ← hv.basis_apply k, hv.basis.repr_self,
      Finsupp.single_eq_same, one_smul]
  · intro j _ hjk
    by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · -- Distinct active normals are distinct members of the basis.
      have hne : (⟨j, hj⟩ : activeSet (facetPairing i u) c v) ≠ k := fun h ↦ hjk (by rw [← h])
      rw [← hv.basis_apply ⟨j, hj⟩, hv.basis.repr_self,
        Finsupp.single_eq_of_ne' hne, zero_smul]
    · rw [extend_apply_of_notMem hj, smul_zero]
  · simp

/-- **The residual torus at a smooth vertex.** The homomorphism `vertexTorusHom` identifies the
residual torus `(ℝ / 2πℤ)^ι / N_Δ` with the standard torus `(ℝ / 2πℤ)^A` on the facets active at
`v`. Its inverse, this equivalence, sends `φ` to the class of the extension of `φ` by zero
(`TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv_apply`). -/
def vertexTorusEquiv (hi : IsIntegralLattice i) :
    (activeSet (facetPairing i u) c v → AddCircle (2 * π)) ≃+
      (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker :=
  ((QuotientAddGroup.quotientAddEquivOfEq (hv.ker_vertexTorusHom hi).symm).trans
    (QuotientAddGroup.quotientKerEquivOfRightInverse hv.vertexTorusHom
      (Function.extend Subtype.val · 0) hv.vertexTorusHom_extend)).symm

@[simp]
theorem vertexTorusEquiv_apply (hi : IsIntegralLattice i)
    (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π)) :
    hv.vertexTorusEquiv hi φ = ((Function.extend Subtype.val φ 0 : ι → AddCircle (2 * π)) :
      (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) :=
  (rfl)

@[simp]
theorem vertexTorusEquiv_symm_mk (hi : IsIntegralLattice i) (θ : ι → AddCircle (2 * π)) :
    (hv.vertexTorusEquiv hi).symm θ = hv.vertexTorusHom θ :=
  (rfl)

end IsSmoothVertex

/-! ### The vertex chart -/

namespace DelzantQuotient

variable [FiniteDimensional ℝ V] {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
  (hi : IsIntegralLattice i) (hvP : v ∈ facetPolyhedron i u c)
  [Fintype (activeSet (facetPairing i u) c v)]

omit [Fintype ι] [FiniteDimensional ℝ V] in
/-- The translated weight model `v + Σ_k ½ |w_k|² ε_k` pairs with an active normal `u_k` to
`½ |w_k|² + c_k`. -/
private theorem vertexMoment_apply_active [Finite ι]
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    (k : activeSet (facetPairing i u) c v) :
    (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u k)) =
      (w.1 k ^ 2 + w.2 k ^ 2) / 2 + c k := by
  classical
  have hk : v (i (u k)) = c k := by simpa using mem_activeSet.1 k.2
  simp [weightMomentMap_apply, hk, IsSmoothVertex.edgeBasis_apply]
  ring

open Classical in
/-- The point of `ℂ^ι` over `w ∈ ℂ^A`: its coordinates in `A` are those of `w`, and its
coordinates outside `A` are the nonnegative reals `√(2(⟨y, u j⟩ - c j))`, for
`y = v + Σ_k ½ |w_k|² ε_k`. -/
private def vertexLift
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  (WithLp.toLp 2 fun j ↦ if h : j ∈ activeSet (facetPairing i u) c v then w.1 ⟨j, h⟩ else
      √(2 * ((v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) - c j)),
    WithLp.toLp 2 fun j ↦ if h : j ∈ activeSet (facetPairing i u) c v then w.2 ⟨j, h⟩ else 0)

omit [FiniteDimensional ℝ V] in
private theorem vertexLift_active
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    (k : activeSet (facetPairing i u) c v) :
    (vertexLift hv hi w).1 k = w.1 k ∧ (vertexLift hv hi w).2 k = w.2 k := by
  simp only [vertexLift, PiLp.toLp_apply, dite_eq_left_of_eq_true (eq_true k.2), Subtype.coe_eta,
    and_self]

omit [FiniteDimensional ℝ V] in
private theorem vertexLift_inactive
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    {j : ι} (hj : j ∉ activeSet (facetPairing i u) c v) :
    (vertexLift hv hi w).1 j =
        √(2 * ((v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) - c j)) ∧
      (vertexLift hv hi w).2 j = 0 := by
  simp only [vertexLift, PiLp.toLp_apply, dite_eq_right_of_eq_false (eq_false hj), and_self]

omit [FiniteDimensional ℝ V] in
private theorem continuous_vertexLift : Continuous (vertexLift hv hi) := by
  refine Continuous.prodMk (PiLp.continuous_toLp _ _ |>.comp (continuous_pi fun j ↦ ?_))
    (PiLp.continuous_toLp _ _ |>.comp (continuous_pi fun j ↦ ?_)) <;>
  by_cases hj : j ∈ activeSet (facetPairing i u) c v <;> simp only [hj, dite_true, dite_false]
  · fun_prop
  · have : Continuous fun w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ↦
        weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w := by
      simp only [weightMomentMap_def]
      fun_prop
    fun_prop
  · fun_prop
  · fun_prop

omit [FiniteDimensional ℝ V] in
/-- Over a point `w` whose translated moment value lies in `Δ`, the lift has moment value
`v + Σ_k ½ |w_k|² ε_k`. -/
private theorem vertexLift_moment
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) (j : ι) :
    ((vertexLift hv hi w).1 j ^ 2 + (vertexLift hv hi w).2 j ^ 2) / 2 + c j =
      (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) := by
  by_cases hj : j ∈ activeSet (facetPairing i u) c v
  · obtain ⟨h1, h2⟩ := vertexLift_active hv hi w ⟨j, hj⟩
    rw [h1, h2]
    exact (vertexMoment_apply_active hv hi w ⟨j, hj⟩).symm
  · obtain ⟨h1, h2⟩ := vertexLift_inactive hv hi w hj
    rw [h1, h2, Real.sq_sqrt (by linarith [hw j hj])]
    ring

open Classical in
/-- The inverse of the vertex chart: the class of `vertexLift w`, when the translated moment
value of `w` lies in `Δ`, and the class over `v` otherwise. -/
private def vertexChartSymm
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) : DelzantQuotient i u c :=
  if hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) then
    mk ⟨vertexLift hv hi w, mem_delzantLevel_of_forall_eq (vertexLift_moment hv hi hw)⟩
  else
    mk ⟨vertexLift hv hi 0, mem_delzantLevel_of_forall_eq (vertexLift_moment hv hi fun j _ ↦ by
      simpa using mem_facetPolyhedron.1 hvP j)⟩

omit [FiniteDimensional ℝ V] in
private theorem vertexChartSymm_of_le
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    vertexChartSymm hv hi hvP w =
      mk ⟨vertexLift hv hi w, mem_delzantLevel_of_forall_eq (vertexLift_moment hv hi hw)⟩ :=
  dite_eq_left_of_eq_true (eq_true hw)

open Classical in
/-- The arguments of the coordinates of `x` outside the active facets. -/
private def inactiveArg (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ι → AddCircle (2 * π) :=
  fun j ↦ if j ∈ activeSet (facetPairing i u) c v then 0 else
    ((⟨x.1 j, x.2 j⟩ : ℂ).arg : AddCircle (2 * π))

/-- The element of the kernel torus that rotates the coordinates of `x` outside the active facets
to nonnegative reals. -/
private def normalizer (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ι → AddCircle (2 * π) :=
  inactiveArg (i := i) (u := u) (c := c) (v := v) x -
    Function.extend Subtype.val
      (hv.vertexTorusHom (inactiveArg (i := i) (u := u) (c := c) (v := v) x)) 0

omit [FiniteDimensional ℝ V] [Fintype (activeSet (facetPairing i u) c v)] in
include hi in
private theorem normalizer_mem_ker (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    normalizer hv x ∈ (facetTorusHom i u (2 * π)).ker := by
  rw [← hv.ker_vertexTorusHom hi, AddMonoidHom.mem_ker, normalizer, map_sub,
    IsSmoothVertex.vertexTorusHom_extend, sub_self]

omit [FiniteDimensional ℝ V] [Fintype (activeSet (facetPairing i u) c v)] in
private theorem normalizer_inactive (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) {j : ι}
    (hj : j ∉ activeSet (facetPairing i u) c v) :
    normalizer hv x j = ((⟨x.1 j, x.2 j⟩ : ℂ).arg : AddCircle (2 * π)) := by
  simp only [normalizer, Pi.sub_apply, extend_apply_of_notMem hj, sub_zero,
    inactiveArg, hj, ↓reduceIte]

omit [FiniteDimensional ℝ V] [Fintype (activeSet (facetPairing i u) c v)] in
/-- Rotating by the normalizer makes the coordinates outside the active facets nonnegative reals,
of the same moduli. -/
private theorem torusRotation_normalizer_inactive (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    {j : ι} (hj : j ∉ activeSet (facetPairing i u) c v) :
    (torusRotation (normalizer hv x) x).1 j = √(x.1 j ^ 2 + x.2 j ^ 2) ∧
      (torusRotation (normalizer hv x) x).2 j = 0 := by
  rw [torusRotation_apply_fst, torusRotation_apply_snd, normalizer_inactive hv x hj,
    Function.Periodic.lift_coe, Function.Periodic.lift_coe]
  -- Write the coordinate `z_j` in polar form `‖z_j‖ (cos a + i sin a)`.
  set z : ℂ := ⟨x.1 j, x.2 j⟩
  have hre : x.1 j = ‖z‖ * cos z.arg := (Complex.norm_mul_cos_arg z).symm
  have him : x.2 j = ‖z‖ * sin z.arg := (Complex.norm_mul_sin_arg z).symm
  have hn : ‖z‖ = √(x.1 j ^ 2 + x.2 j ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_mk, sq, sq]
  rw [← hn]
  exact ⟨by linear_combination cos z.arg * hre + sin z.arg * him + ‖z‖ * sin_sq_add_cos_sq z.arg,
    by linear_combination -sin z.arg * hre + cos z.arg * him⟩

omit [Fintype ι] in
private theorem continuous_complex_mk (j : ι) :
    Continuous fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ (⟨x.1 j, x.2 j⟩ : ℂ) :=
  (Complex.equivRealProdCLM.symm.continuous.comp
    (by fun_prop : Continuous fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      (x.1 j, x.2 j))).congr fun _ ↦ Complex.ext (by simp) (by simp)

omit [FiniteDimensional ℝ V] [Fintype (activeSet (facetPairing i u) c v)] in
/-- The normalizer is continuous at the points whose coordinates outside the active facets do
not vanish. -/
private theorem continuousAt_normalizer {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.1 j ^ 2 + x.2 j ^ 2) :
    ContinuousAt (normalizer hv) x := by
  have harg : ContinuousAt (inactiveArg (i := i) (u := u) (c := c) (v := v)) x := by
    refine continuousAt_pi.2 fun j ↦ ?_
    by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · simp only [inactiveArg, hj, ↓reduceIte]
      exact continuousAt_const
    · simp only [inactiveArg, hj, ↓reduceIte]
      have hz : (⟨x.1 j, x.2 j⟩ : ℂ) ≠ 0 := fun h ↦ by
        have h1 : x.1 j = 0 := congrArg Complex.re h
        have h2 : x.2 j = 0 := congrArg Complex.im h
        simpa [h1, h2] using hx j hj
      exact ContinuousAt.comp (g := fun z : ℂ ↦ (z.arg : AddCircle (2 * π)))
        (Complex.continuousAt_arg_coe_angle hz) (continuous_complex_mk j).continuousAt
  exact harg.sub
    ((continuous_extend_zero.comp hv.continuous_vertexTorusHom).continuousAt.comp harg)

/-- A rotation of `ℂ^ι` that fixes a nonzero coordinate has angle zero there. -/
private theorem eq_zero_of_torusRotation_apply {θ : ι → AddCircle (2 * π)}
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} {j : ι}
    (h1 : (torusRotation θ x).1 j = x.1 j) (h2 : (torusRotation θ x).2 j = x.2 j)
    (hx : 0 < x.1 j ^ 2 + x.2 j ^ 2) : θ j = 0 := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (θ j)
  rw [torusRotation_apply_fst, ← ht, Function.Periodic.lift_coe, Function.Periodic.lift_coe] at h1
  rw [torusRotation_apply_snd, ← ht, Function.Periodic.lift_coe, Function.Periodic.lift_coe] at h2
  have hcos : cos t = 1 := by
    have h : (cos t - 1) * (x.1 j ^ 2 + x.2 j ^ 2) = 0 := by
      linear_combination x.1 j * h1 + x.2 j * h2
    linarith [(mul_eq_zero.1 h).resolve_right hx.ne']
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff t).1 hcos
  rw [← ht, AddCircle.coe_eq_zero_iff]
  exact ⟨n, by rw [zsmul_eq_mul, hn]⟩

/-- The coordinates in a finite set `s` of indices of a point of `ℂ^ι`. -/
private def restrictTo (s : Set ι) [Fintype s] :
    (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ s × EuclideanSpace ℝ s :=
  LinearMap.toContinuousLinearMap
    { toFun x := (WithLp.toLp 2 fun k ↦ x.1 k, WithLp.toLp 2 fun k ↦ x.2 k)
      map_add' _ _ := by ext <;> simp
      map_smul' _ _ := by ext <;> simp }

private theorem restrictTo_apply (s : Set ι) [Fintype s]
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (k : s) :
    (restrictTo s x).1 k = x.1 k ∧ (restrictTo s x).2 k = x.2 k :=
  ⟨rfl, rfl⟩

omit [FiniteDimensional ℝ V] in
include hi in
/-- The coordinates in `A` of the normalized representative do not change when the point is moved
by the kernel torus. Both normalized representatives lie in one orbit of the kernel torus and
have the same nonnegative real coordinates outside `A`. The element relating them therefore
vanishes outside `A`, and so is zero, since the active normals form a lattice basis. -/
private theorem restrictTo_torusRotation_normalizer_torusRotation {θ : ι → AddCircle (2 * π)}
    (hθ : θ ∈ (facetTorusHom i u (2 * π)).ker) {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.1 j ^ 2 + x.2 j ^ 2) :
    restrictTo (activeSet (facetPairing i u) c v)
        (torusRotation (normalizer hv (torusRotation θ x)) (torusRotation θ x)) =
      restrictTo (activeSet (facetPairing i u) c v) (torusRotation (normalizer hv x) x) := by
  set δ := normalizer hv (torusRotation θ x) + θ - normalizer hv x
  have hb : torusRotation (normalizer hv (torusRotation θ x)) (torusRotation θ x) =
      torusRotation δ (torusRotation (normalizer hv x) x) := by
    rw [← ContinuousLinearMap.comp_apply, ← torusRotation_add, ← ContinuousLinearMap.comp_apply,
      ← torusRotation_add, sub_add_cancel]
  have hδ : δ = 0 := by
    refine eq_zero_of_mem_ker_facetTorusHom hi ⟨hv.basis, hv.basis_apply⟩
      (sub_mem (add_mem (normalizer_mem_ker hv hi _) hθ) (normalizer_mem_ker hv hi x))
      fun j hj ↦ ?_
    obtain ⟨ha1, ha2⟩ := torusRotation_normalizer_inactive hv x hj
    obtain ⟨hb1, hb2⟩ := torusRotation_normalizer_inactive hv (torusRotation θ x) hj
    rw [torusRotation_apply_normSq, hb] at hb1
    rw [hb] at hb2
    refine eq_zero_of_torusRotation_apply (hb1.trans ha1.symm) (hb2.trans ha2.symm) ?_
    rw [ha1, ha2, Real.sq_sqrt (by positivity)]
    simpa using hx j hj
  rw [hb, hδ, torusRotation_zero, ContinuousLinearMap.id_apply]

open Classical in
/-- The vertex chart: the class of `z ∈ Z` is sent to the coordinates in `A` of its representative
whose coordinates outside `A` are positive reals. -/
private def vertexChartFun (q : DelzantQuotient i u c) :
    EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v) :=
  lift (fun x ↦ if ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.1.1 j ^ 2 + x.1.2 j ^ 2 then
      restrictTo (activeSet (facetPairing i u) c v) (torusRotation (normalizer hv x) x) else 0)
    fun θ hθ x ↦ by
      simp only [coe_vadd_delzantLevel, torusRotation_apply_normSq]
      split_ifs with h
      · exact restrictTo_torusRotation_normalizer_torusRotation hv hi hθ h
      · rfl
  q

omit [FiniteDimensional ℝ V] in
private theorem vertexChartFun_mk {x : delzantLevel i u c}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.1.1 j ^ 2 + x.1.2 j ^ 2) :
    vertexChartFun hv hi (mk x) =
      restrictTo (activeSet (facetPairing i u) c v) (torusRotation (normalizer hv x) x) := by
  rw [vertexChartFun, lift_mk]
  split_ifs with h
  · rfl
  · exact absurd hx h

omit [Fintype (activeSet (facetPairing i u) c v)] in
/-- The coordinates outside `A` of a point over the source of the vertex chart do not vanish. -/
private theorem pos_of_lt_reducedMomentMap_mk {x : delzantLevel i u c}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) (mk x) (i (u j))) :
    ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.1.1 j ^ 2 + x.1.2 j ^ 2 := fun j hj ↦ by
  have h := hx j hj
  rw [reducedMomentMap_mk_apply] at h
  linarith

/-- The translated weight model at the image of a normalized representative is the moment value
of its class. -/
private theorem vertexMoment_restrictTo_normalizer (x : delzantLevel i u c) :
    v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k)
        (restrictTo (activeSet (facetPairing i u) c v) (torusRotation (normalizer hv x) x)) =
      reducedMomentMap (hv.surjective_linearCombination_real hi) (mk x) := by
  refine (hv.edgeBasis hi).ext_elem fun k ↦ ?_
  rw [IsSmoothVertex.edgeBasis_repr, IsSmoothVertex.edgeBasis_repr, vertexMoment_apply_active,
    reducedMomentMap_mk_apply, (restrictTo_apply _ _ k).1, (restrictTo_apply _ _ k).2,
    torusRotation_apply_normSq]

/-- `vertexLift` recovers a normalized representative from its coordinates in `A`. -/
private theorem vertexLift_restrictTo_normalizer (x : delzantLevel i u c) :
    vertexLift hv hi
        (restrictTo (activeSet (facetPairing i u) c v) (torusRotation (normalizer hv x) x)) =
      torusRotation (normalizer hv x) x := by
  ext j
  · by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · exact ((vertexLift_active hv hi _ ⟨j, hj⟩).1).trans (restrictTo_apply _ _ ⟨j, hj⟩).1
    · rw [(vertexLift_inactive hv hi _ hj).1, (torusRotation_normalizer_inactive hv x hj).1,
        vertexMoment_restrictTo_normalizer, reducedMomentMap_mk_apply]
      ring_nf
  · by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · exact ((vertexLift_active hv hi _ ⟨j, hj⟩).2).trans (restrictTo_apply _ _ ⟨j, hj⟩).2
    · rw [(vertexLift_inactive hv hi _ hj).2, (torusRotation_normalizer_inactive hv x hj).2]

omit [FiniteDimensional ℝ V] in
/-- The normalizer of a lift is trivial: its coordinates outside `A` are already nonnegative
reals. -/
private theorem normalizer_vertexLift
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    normalizer hv (vertexLift hv hi w) = 0 := by
  have harg : inactiveArg (i := i) (u := u) (c := c) (v := v) (vertexLift hv hi w) = 0 := by
    funext j
    by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · simp only [inactiveArg, hj, ↓reduceIte, Pi.zero_apply]
    · simp only [inactiveArg, hj, ↓reduceIte, Pi.zero_apply, (vertexLift_inactive hv hi w hj).1,
        (vertexLift_inactive hv hi w hj).2]
      rw [Complex.arg_eq_zero_iff.2 ⟨Real.sqrt_nonneg _, rfl⟩, QuotientAddGroup.mk_zero]
  have hext : (Function.extend Subtype.val
      (0 : activeSet (facetPairing i u) c v → AddCircle (2 * π)) 0 : ι → AddCircle (2 * π)) = 0 :=
    Function.extend_const _ _
  rw [normalizer, harg, map_zero, hext, sub_zero]

omit [Fintype ι] [FiniteDimensional ℝ V] in
private theorem continuous_vertexMoment [Finite ι] :
    Continuous fun w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ↦
      v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w := by
  simp only [weightMomentMap_def]
  fun_prop

/-- The vertex chart sends its source into its target. -/
private theorem vertexChartFun_mem_target {q : DelzantQuotient i u c}
    (hq : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))) :
    ∀ j ∉ activeSet (facetPairing i u) c v, c j <
      (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (vertexChartFun hv hi q)) (i (u j)) := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  intro j hj
  rw [vertexChartFun_mk hv hi (pos_of_lt_reducedMomentMap_mk hv hi hq),
    vertexMoment_restrictTo_normalizer]
  exact hq j hj

/-- The inverse of the vertex chart sends its target into its source. -/
private theorem vertexChartSymm_mem_source
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi)
        (vertexChartSymm hv hi hvP w) (i (u j)) := by
  have hw' := fun j hj ↦ (hw j hj).le
  intro j hj
  rw [vertexChartSymm_of_le hv hi hvP hw',
    (reducedMomentMap_mk_eq_iff _).2 (vertexLift_moment hv hi hw')]
  exact hw j hj

/-- The inverse of the vertex chart is a left inverse on the source. -/
private theorem vertexChartSymm_vertexChartFun {q : DelzantQuotient i u c}
    (hq : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))) :
    vertexChartSymm hv hi hvP (vertexChartFun hv hi q) = q := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  have hle : ∀ j ∉ activeSet (facetPairing i u) c v, c j ≤
      (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k)
        (restrictTo (activeSet (facetPairing i u) c v) (torusRotation (normalizer hv x) x)))
        (i (u j)) := fun j _ ↦ by
    rw [vertexMoment_restrictTo_normalizer]
    exact mem_facetPolyhedron.1 (reducedMomentMap_mem_facetPolyhedron _ _) j
  rw [vertexChartFun_mk hv hi (pos_of_lt_reducedMomentMap_mk hv hi hq),
    vertexChartSymm_of_le hv hi hvP hle]
  -- The normalized representative is a rotation of `x` by the kernel torus.
  rw [← mk_vadd_of_mem_ker (normalizer_mem_ker hv hi x) x]
  exact congrArg mk (Subtype.ext (vertexLift_restrictTo_normalizer hv hi x))

omit [FiniteDimensional ℝ V] in
/-- The inverse of the vertex chart is a right inverse on the target. -/
private theorem vertexChartFun_vertexChartSymm
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    vertexChartFun hv hi (vertexChartSymm hv hi hvP w) = w := by
  have hw' := fun j hj ↦ (hw j hj).le
  have hpos : ∀ j ∉ activeSet (facetPairing i u) c v,
      0 < (vertexLift hv hi w).1 j ^ 2 + (vertexLift hv hi w).2 j ^ 2 := fun j hj ↦ by
    rw [(vertexLift_inactive hv hi w hj).1, (vertexLift_inactive hv hi w hj).2,
      Real.sq_sqrt (by linarith [hw j hj])]
    linarith [hw j hj]
  rw [vertexChartSymm_of_le hv hi hvP hw', vertexChartFun_mk hv hi hpos,
    normalizer_vertexLift, torusRotation_zero, ContinuousLinearMap.id_apply]
  ext k
  · exact ((restrictTo_apply _ _ k).1).trans (vertexLift_active hv hi w k).1
  · exact ((restrictTo_apply _ _ k).2).trans (vertexLift_active hv hi w k).2

/-- The vertex chart is continuous on its source. -/
private theorem continuousOn_vertexChartFun :
    ContinuousOn (vertexChartFun hv hi)
      {q | ∀ j ∉ activeSet (facetPairing i u) c v,
        c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))} := by
  refine fun q hq ↦ ContinuousAt.continuousWithinAt ?_
  induction q using DelzantQuotient.inductionOn with | h x =>
  have hx := pos_of_lt_reducedMomentMap_mk hv hi hq
  refine isOpenQuotientMap_mk.continuousAt_comp_iff.1 ?_
  -- Near `x`, the coordinates outside `A` still do not vanish, so the chart is given by the
  -- normalized representative.
  have hU : IsOpen {y : delzantLevel i u c |
      ∀ j ∉ activeSet (facetPairing i u) c v, 0 < y.1.1 j ^ 2 + y.1.2 j ^ 2} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const (by fun_prop)
  refine ContinuousAt.congr (f := fun y : delzantLevel i u c ↦
    restrictTo (activeSet (facetPairing i u) c v) (torusRotation (normalizer hv y) y)) ?_
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy ↦
      (vertexChartFun_mk hv hi hy).symm)
  exact (restrictTo _).continuous.continuousAt.comp (continuous_torusRotation.continuousAt.comp
    (((continuousAt_normalizer hv hx).comp continuous_subtype_val.continuousAt).prodMk
      continuous_subtype_val.continuousAt))

omit [FiniteDimensional ℝ V] in
/-- The inverse of the vertex chart is continuous on its target. -/
private theorem continuousOn_vertexChartSymm :
    ContinuousOn (vertexChartSymm hv hi hvP)
      {w | ∀ j ∉ activeSet (facetPairing i u) c v,
        c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))} := by
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  refine (continuous_mk.comp (((continuous_vertexLift hv hi).comp
    continuous_subtype_val).subtype_mk fun w ↦ ?_)).congr fun w ↦ ?_
  · exact mem_delzantLevel_of_forall_eq (vertexLift_moment hv hi fun j hj ↦ (w.2 j hj).le)
  · exact (vertexChartSymm_of_le hv hi hvP fun j hj ↦ (w.2 j hj).le).symm

/-- **The equivariant chart of the Delzant quotient at a smooth vertex.** Let `v` be a smooth
vertex of `Δ`, with active facets `A` and inward edge basis `ε`. The vertex chart is a
homeomorphism from the open set of points `q` of `M_Δ` with `c j < ⟨μ_Δ q, u j⟩` for every
`j ∉ A`, that is with active facets in `A`
(`TauCeti.Toric.DelzantQuotient.mem_vertexChart_source_iff`), onto the open set of `w ∈ ℂ^A`
with `c j < ⟨v + Σ_k ½ |w_k|² ε_k, u j⟩` for every `j ∉ A`. Its inverse sends `w` to the class
of the point of the level with coordinates `w_k` in `A` and nonnegative real coordinates outside
`A`. It intertwines the moment map with the translated weight model
(`TauCeti.Toric.DelzantQuotient.reducedMomentMap_vertexChart_symm`) and the residual torus with
the standard rotation of `ℂ^A` (`TauCeti.Toric.DelzantQuotient.vertexChart_vadd`). -/
def vertexChart :
    OpenPartialHomeomorph (DelzantQuotient i u c)
      (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) where
  toFun := vertexChartFun hv hi
  invFun := vertexChartSymm hv hi hvP
  source := {q | ∀ j ∉ activeSet (facetPairing i u) c v,
    c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))}
  target := {w | ∀ j ∉ activeSet (facetPairing i u) c v,
    c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))}
  map_source' _ hq := vertexChartFun_mem_target hv hi hq
  map_target' _ hw := vertexChartSymm_mem_source hv hi hvP hw
  left_inv' _ hq := vertexChartSymm_vertexChartFun hv hi hvP hq
  right_inv' _ hw := vertexChartFun_vertexChartSymm hv hi hvP hw
  open_source := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const ((continuous_clm_apply.1 (continuous_reducedMomentMap _)) _)
  open_target := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const ((continuous_clm_apply.1 (continuous_vertexMoment hv hi)) _)
  continuousOn_toFun := continuousOn_vertexChartFun hv hi
  continuousOn_invFun := continuousOn_vertexChartSymm hv hi hvP

private theorem vertexChart_symm_eq :
    (vertexChart hv hi hvP).symm = vertexChartSymm hv hi hvP :=
  (rfl)

theorem vertexChart_source :
    (vertexChart hv hi hvP).source = {q | ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))} :=
  (rfl)

theorem vertexChart_target :
    (vertexChart hv hi hvP).target = {w | ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))} :=
  (rfl)

/-- **The source of the vertex chart.** A point of the Delzant quotient lies in the source of the
chart at `v` exactly when every facet active at its moment value is active at `v`. -/
theorem mem_vertexChart_source_iff {q : DelzantQuotient i u c} :
    q ∈ (vertexChart hv hi hvP).source ↔
      activeSet (facetPairing i u) c (reducedMomentMap (hv.surjective_linearCombination_real hi) q)
        ⊆ activeSet (facetPairing i u) c v := by
  have hq := mem_facetPolyhedron.1 (reducedMomentMap_mem_facetPolyhedron
    (hv.surjective_linearCombination_real hi) q)
  simp only [vertexChart_source, mem_ofPred_eq, subset_def, mem_activeSet, facetPairing_apply]
  refine ⟨fun h j hj ↦ by_contra fun hjv ↦ (h j hjv).ne hj.symm, fun h j hj ↦ ?_⟩
  exact (hq j).lt_of_ne fun he ↦ hj (h j he.symm)

/-- The vertex chart is centred at the point over `v`: `0` lies in its target. -/
theorem zero_mem_vertexChart_target : 0 ∈ (vertexChart hv hi hvP).target := fun j hj ↦ by
  rw [weightMomentMap_zero, add_zero]
  exact (mem_facetPolyhedron.1 hvP j).lt_of_ne fun h ↦
    hj (mem_activeSet.2 (by rw [facetPairing_apply, h]))

/-- **The moment map in the vertex chart** is the weight model translated to the vertex:
`μ_Δ = v + Σ_k ½ |w_k|² ε_k`. -/
theorem reducedMomentMap_vertexChart_symm
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target) :
    reducedMomentMap (hv.surjective_linearCombination_real hi) ((vertexChart hv hi hvP).symm w) =
      v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w := by
  have hw' := fun j hj ↦ (hw j hj).le
  rw [vertexChart_symm_eq, vertexChartSymm_of_le hv hi hvP hw',
    (reducedMomentMap_mk_eq_iff _).2 (vertexLift_moment hv hi hw')]

/-- The moment value of a point of the source is the translated weight model at its image under
the vertex chart. -/
theorem vertexMoment_vertexChart {q : DelzantQuotient i u c}
    (hq : q ∈ (vertexChart hv hi hvP).source) :
    v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (vertexChart hv hi hvP q) =
      reducedMomentMap (hv.surjective_linearCombination_real hi) q := by
  rw [← reducedMomentMap_vertexChart_symm hv hi hvP ((vertexChart hv hi hvP).map_source hq),
    (vertexChart hv hi hvP).left_inv hq]

/-- The point of the Delzant quotient at the centre of the vertex chart lies over `v`; it is the
fixed point over `v` (`TauCeti.Toric.DelzantQuotient.bijOn_reducedMomentMap_fixedPoints`). -/
theorem reducedMomentMap_vertexChart_symm_zero :
    reducedMomentMap (hv.surjective_linearCombination_real hi) ((vertexChart hv hi hvP).symm 0) =
      v := by
  rw [reducedMomentMap_vertexChart_symm hv hi hvP (zero_mem_vertexChart_target hv hi hvP),
    weightMomentMap_zero, add_zero]

omit [Fintype ι] [FiniteDimensional ℝ V] in
/-- The translated weight model is invariant under the rotations of `ℂ^A`. -/
private theorem vertexMoment_torusRotation [Finite ι]
    (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π))
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (torusRotation φ w) =
      v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w := by
  simp only [weightMomentMap_def, torusRotation_apply_normSq]

omit [FiniteDimensional ℝ V] in
/-- The rotation by `φ ∈ (ℝ / 2πℤ)^A` of the lift of `w` is the lift of the rotation of `w`. -/
private theorem vertexLift_torusRotation
    (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π))
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    vertexLift hv hi (torusRotation φ w) =
      torusRotation (Function.extend Subtype.val φ 0) (vertexLift hv hi w) := by
  have h0 : cos_periodic.lift (0 : AddCircle (2 * π)) = 1 ∧
      sin_periodic.lift (0 : AddCircle (2 * π)) = 0 := by
    rw [← QuotientAddGroup.mk_zero, Function.Periodic.lift_coe, Function.Periodic.lift_coe,
      cos_zero, sin_zero]
    exact ⟨rfl, rfl⟩
  ext j <;> by_cases hj : j ∈ activeSet (facetPairing i u) c v
  · rw [(vertexLift_active hv hi _ ⟨j, hj⟩).1, torusRotation_apply_fst, torusRotation_apply_fst,
      (vertexLift_active hv hi _ ⟨j, hj⟩).1, (vertexLift_active hv hi _ ⟨j, hj⟩).2,
      Subtype.val_injective.extend_apply φ 0 ⟨j, hj⟩]
  · rw [(vertexLift_inactive hv hi _ hj).1, torusRotation_apply_fst,
      (vertexLift_inactive hv hi _ hj).1, (vertexLift_inactive hv hi _ hj).2,
      extend_apply_of_notMem hj, h0.1, h0.2, vertexMoment_torusRotation]
    ring
  · rw [(vertexLift_active hv hi _ ⟨j, hj⟩).2, torusRotation_apply_snd, torusRotation_apply_snd,
      (vertexLift_active hv hi _ ⟨j, hj⟩).1, (vertexLift_active hv hi _ ⟨j, hj⟩).2,
      Subtype.val_injective.extend_apply φ 0 ⟨j, hj⟩]
  · rw [(vertexLift_inactive hv hi _ hj).2, torusRotation_apply_snd,
      (vertexLift_inactive hv hi _ hj).2, extend_apply_of_notMem hj, h0.2]
    ring

/-- **Equivariance of the vertex chart.** The inverse of the chart intertwines the rotation
`w_k ↦ exp(-i φ_k) w_k` of `ℂ^A` with the action of the residual torus through the isomorphism
`(ℝ / 2πℤ)^A ≃ (ℝ / 2πℤ)^ι / N_Δ` (`TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv`). -/
theorem vertexChart_symm_torusRotation
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target)
    (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π)) :
    (vertexChart hv hi hvP).symm (torusRotation φ w) =
      hv.vertexTorusEquiv hi φ +ᵥ (vertexChart hv hi hvP).symm w := by
  have hw' := fun j hj ↦ (hw j hj).le
  have hφw' : ∀ j ∉ activeSet (facetPairing i u) c v, c j ≤
      (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (torusRotation φ w)) (i (u j)) := by
    rwa [vertexMoment_torusRotation]
  rw [vertexChart_symm_eq, vertexChartSymm_of_le hv hi hvP hw',
    vertexChartSymm_of_le hv hi hvP hφw',
    IsSmoothVertex.vertexTorusEquiv_apply, coe_vadd_mk]
  exact congrArg mk (Subtype.ext (vertexLift_torusRotation hv hi φ w))

/-- **Equivariance of the vertex chart.** On its source, the vertex chart sends the action of the
class of `φ ∈ (ℝ / 2πℤ)^A` in the residual torus to the rotation `w_k ↦ exp(-i φ_k) w_k`. -/
theorem vertexChart_vadd {q : DelzantQuotient i u c} (hq : q ∈ (vertexChart hv hi hvP).source)
    (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π)) :
    vertexChart hv hi hvP (hv.vertexTorusEquiv hi φ +ᵥ q) =
      torusRotation φ (vertexChart hv hi hvP q) := by
  have hw := (vertexChart hv hi hvP).map_source hq
  have hφw : torusRotation φ (vertexChart hv hi hvP q) ∈ (vertexChart hv hi hvP).target := by
    intro j hj
    rw [vertexMoment_torusRotation]
    exact hw j hj
  conv_lhs => rw [← (vertexChart hv hi hvP).left_inv hq]
  rw [← vertexChart_symm_torusRotation hv hi hvP hw, (vertexChart hv hi hvP).right_inv hφw]

end DelzantQuotient

end TauCeti.Toric
