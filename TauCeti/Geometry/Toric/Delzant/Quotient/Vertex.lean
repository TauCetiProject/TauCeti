/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Toric.Delzant.Quotient.Basic
public import TauCeti.Geometry.Toric.Delzant.TangentCone
public import TauCeti.Geometry.Toric.Delzant.Torus
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Algebra.AddCircle
import TauCeti.Geometry.Toric.Delzant.Stabilizer
import TauCeti.Topology.Constructions.Pi

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
(`TauCeti.Toric.IsSmoothVertex.vertexTorusHom`), whose kernel is the kernel torus `N_Δ`
(`TauCeti.Toric.IsSmoothVertex.ker_vertexTorusHom`). Since `D` is the identity on the angles
supported on `A`, it induces an isomorphism of the residual torus with the standard torus
`(ℝ / 2πℤ)^A` (`TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv`), whose inverse sends `φ` to the
class of `φ` extended by zero. These are constructed in `TauCeti.Geometry.Toric.Delzant.Torus`.

**The local model.** Let `ε_k` be the inward edge basis at `v`, dual to the active normals
(`TauCeti.Toric.IsSmoothVertex.edgeBasis`). The *vertex chart*
(`TauCeti.Toric.DelzantQuotient.vertexChart`) is a homeomorphism from the open set of points of
`M_Δ` whose active facets lie in `A` onto the open set `W ⊆ ℂ^A` of the `w` with
`c j < ⟨v + Σ_k ½ |w_k|² ε_k, u j⟩` for every facet `j ∉ A`. Its inverse sends `w` to the class
of the point `z ∈ Z` with `z_k = w_k` for `k ∈ A` and `z_j = √(2(⟨y, u j⟩ - c j))` for `j ∉ A`,
where `y = v + Σ_k ½ |w_k|² ε_k` (`TauCeti.Toric.DelzantQuotient.vertexLift`,
`TauCeti.Toric.DelzantQuotient.vertexChart_symm_apply`). In the other direction, a class `[z]` in
the source of the chart is sent to the coordinates in `A` of the unique representative of `[z]`
whose coordinates outside `A` are positive reals (`TauCeti.Toric.DelzantQuotient.vertexChart_mk`).
In this chart

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
`M_Δ` (`TauCeti.Toric.IsDelzant.exists_mem_vertexChart_source`).

## Main definitions

* `TauCeti.Toric.DelzantQuotient.vertexLift`: the point of `ℂ^ι` over `w ∈ ℂ^A` that is a
  nonnegative real outside `A`; it lies in the level when `v + Σ_k ½ |w_k|² ε_k ∈ Δ`
  (`TauCeti.Toric.DelzantQuotient.vertexLift_mem_delzantLevel`).
* `TauCeti.Toric.DelzantQuotient.vertexChart`: the equivariant chart of `M_Δ` at a smooth vertex.

## Main results

* `TauCeti.Toric.DelzantQuotient.mem_fixedPoints_iff`,
  `TauCeti.Toric.DelzantQuotient.bijOn_reducedMomentMap_fixedPoints`: fixed points correspond
  exactly to vertices.
* `TauCeti.Toric.DelzantQuotient.mem_vertexChart_source_iff`: the source of the vertex chart is
  the set of points whose active facets are active at `v`.
* `TauCeti.Toric.IsDelzant.exists_mem_vertexChart_source`: for a Delzant polytope the charts at
  the vertices cover `M_Δ`.
* `TauCeti.Toric.DelzantQuotient.vertexChart_symm_apply`,
  `TauCeti.Toric.DelzantQuotient.vertexChart_mk`: the chart and its inverse on representatives.
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

variable {ι N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

namespace DelzantQuotient

/-! ### Fixed points and vertices -/

section FixedPoints

variable [Fintype ι]
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
include hβ

/-- **Fixed points are the points over the vertices.** A point of the Delzant quotient is fixed
by the whole residual torus exactly when its moment value is a vertex of `Δ`. -/
theorem mem_fixedPoints_iff (hi : IsIntegralLattice i) {q : DelzantQuotient i u c} :
    haveI := hi.finiteDimensional
    q ∈ AddAction.fixedPoints ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
        (DelzantQuotient i u c) ↔
      reducedMomentMap hβ q ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  have := hi.finiteDimensional
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
      obtain ⟨t', rfl⟩ := AddCircle.exists_pi_coe_eq θ
      refine ⟨t', hθ, ?_⟩
      simpa only [coe_vadd_delzantLevel, torusRotation_coe] using (congrArg Subtype.val h).symm
    · rintro ⟨t', ht', h⟩
      exact ⟨_, ht', Subtype.ext (by simp only [coe_vadd_delzantLevel, torusRotation_coe, h])⟩
  refine ⟨fun h t ↦ (key t).1 (h _), fun h θ ↦ ?_⟩
  induction θ using QuotientAddGroup.induction_on with | H θ =>
  obtain ⟨t, rfl⟩ := AddCircle.exists_pi_coe_eq θ
  exact (key t).2 (h t)

/-- **Fixed points correspond exactly to vertices.** The reduced moment map restricts to a
bijection from the fixed points of the residual torus onto the vertices of `Δ`. In particular
exactly one point of the Delzant quotient lies over each vertex. -/
theorem bijOn_reducedMomentMap_fixedPoints (hi : IsIntegralLattice i) :
    haveI := hi.finiteDimensional
    BijOn (reducedMomentMap hβ)
      (AddAction.fixedPoints ((ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker)
        (DelzantQuotient i u c))
      ((facetPolyhedron i u c).extremePoints ℝ) := by
  have := hi.finiteDimensional
  refine ⟨fun q hq ↦ (mem_fixedPoints_iff hβ hi).1 hq, fun q hq q' hq' h ↦ ?_, fun y hy ↦ ?_⟩
  · -- Two points with the same moment value lie in one orbit, and `q'` is fixed.
    obtain ⟨θ, rfl⟩ := (reducedMomentMap_eq_reducedMomentMap_iff hβ).1 h
    exact hq' θ
  · obtain ⟨q, rfl⟩ : y ∈ range (reducedMomentMap hβ (c := c)) := by
      rw [range_reducedMomentMap hβ]
      exact hy.1
    exact ⟨q, (mem_fixedPoints_iff hβ hi).2 hy, rfl⟩

end FixedPoints

/-! ### The lift of the inverse vertex chart -/

section VertexLift

variable [Finite ι] {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
  (hi : IsIntegralLattice i) [Fintype (activeSet (facetPairing i u) c v)]

/-- The translated weight model `v + Σ_k ½ |w_k|² ε_k` pairs with an active normal `u_k` to
`½ |w_k|² + c_k`. -/
private theorem vertexMoment_apply_active
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    (k : activeSet (facetPairing i u) c v) :
    (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u k)) =
      (w.1 k ^ 2 + w.2 k ^ 2) / 2 + c k := by
  classical
  have hk : v (i (u k)) = c k := by simpa using mem_activeSet.1 k.property
  simp [weightMomentMap_apply, hk, IsSmoothVertex.edgeBasis_apply]
  ring

open Classical in
/-- The point of `ℂ^ι` over `w ∈ ℂ^A` used by the inverse of the vertex chart: its coordinates in
`A` are those of `w`, and its coordinates outside `A` are the nonnegative reals
`√(2(⟨y, u j⟩ - c j))`, for `y = v + Σ_k ½ |w_k|² ε_k`. -/
def vertexLift
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  (WithLp.toLp 2 fun j ↦ if h : j ∈ activeSet (facetPairing i u) c v then w.1 ⟨j, h⟩ else
      √(2 * ((v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) - c j)),
    WithLp.toLp 2 fun j ↦ if h : j ∈ activeSet (facetPairing i u) c v then w.2 ⟨j, h⟩ else 0)

/-- The coordinates of `vertexLift w` in `A` are those of `w`. -/
@[simp]
theorem vertexLift_fst_of_mem
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    {j : ι} (hj : j ∈ activeSet (facetPairing i u) c v) :
    (vertexLift hv hi w).1 j = w.1 ⟨j, hj⟩ := by
  simp only [vertexLift, PiLp.toLp_apply, dite_eq_left_of_eq_true (eq_true hj)]

@[simp]
theorem vertexLift_snd_of_mem
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    {j : ι} (hj : j ∈ activeSet (facetPairing i u) c v) :
    (vertexLift hv hi w).2 j = w.2 ⟨j, hj⟩ := by
  simp only [vertexLift, PiLp.toLp_apply, dite_eq_left_of_eq_true (eq_true hj)]

/-- The coordinates of `vertexLift w` outside `A` are nonnegative reals, determined by the
translated moment value of `w`. -/
@[simp]
theorem vertexLift_fst_of_notMem
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    {j : ι} (hj : j ∉ activeSet (facetPairing i u) c v) :
    (vertexLift hv hi w).1 j =
      √(2 * ((v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) - c j)) := by
  simp only [vertexLift, PiLp.toLp_apply, dite_eq_right_of_eq_false (eq_false hj)]

@[simp]
theorem vertexLift_snd_of_notMem
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    {j : ι} (hj : j ∉ activeSet (facetPairing i u) c v) :
    (vertexLift hv hi w).2 j = 0 := by
  simp only [vertexLift, PiLp.toLp_apply, dite_eq_right_of_eq_false (eq_false hj)]

private theorem continuous_vertexLift : Continuous (vertexLift hv hi) := by
  refine Continuous.prodMk (PiLp.continuous_toLp _ _ |>.comp (continuous_pi fun j ↦ ?_))
    (PiLp.continuous_toLp _ _ |>.comp (continuous_pi fun j ↦ ?_)) <;>
  by_cases hj : j ∈ activeSet (facetPairing i u) c v <;> simp only [hj, dite_true, dite_false] <;>
  fun_prop

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
  · rw [vertexLift_fst_of_mem hv hi w hj, vertexLift_snd_of_mem hv hi w hj]
    exact (vertexMoment_apply_active hv hi w ⟨j, hj⟩).symm
  · rw [vertexLift_fst_of_notMem hv hi w hj, vertexLift_snd_of_notMem hv hi w hj,
      Real.sq_sqrt (by linarith [hw j hj])]
    ring

/-- At `w = 0`, the translated weight model is `v`, so it satisfies the facet inequalities
outside `A`. -/
private theorem vertexMoment_zero_le (hvP : v ∈ facetPolyhedron i u c) :
    ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) 0) (i (u j)) := fun j _ ↦ by
  rw [weightMomentMap_zero, add_zero]
  exact mem_facetPolyhedron.1 hvP j

end VertexLift

section VertexLiftLevel

variable [Fintype ι] {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
  (hi : IsIntegralLattice i) [Fintype (activeSet (facetPairing i u) c v)]

/-- Over a point `w` whose translated moment value `v + Σ_k ½ |w_k|² ε_k` lies in `Δ`, the lift
lies in the level set `Z`. -/
theorem vertexLift_mem_delzantLevel
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    vertexLift hv hi w ∈ delzantLevel i u c :=
  mem_delzantLevel_of_forall_eq (vertexLift_moment hv hi hw)

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
  ext j <;> by_cases hj : j ∈ activeSet (facetPairing i u) c v <;>
    simp [hj, torusRotation_apply_fst, torusRotation_apply_snd,
      Function.extend_val_apply, Function.extend_val_apply', h0]

end VertexLiftLevel

/-! ### Normalization outside the active facets -/

section Normalizer

variable [Fintype ι] {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)

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
      (hv.vertexTorusHom (2 * π) (inactiveArg (i := i) (u := u) (c := c) (v := v) x)) 0

private theorem normalizer_mem_ker (hi : IsIntegralLattice i)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    normalizer hv x ∈ (facetTorusHom i u (2 * π)).ker := by
  rw [← hv.ker_vertexTorusHom hi, AddMonoidHom.mem_ker, normalizer, map_sub,
    IsSmoothVertex.vertexTorusHom_extend, sub_self]

private theorem normalizer_inactive (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) {j : ι}
    (hj : j ∉ activeSet (facetPairing i u) c v) :
    normalizer hv x j = ((⟨x.1 j, x.2 j⟩ : ℂ).arg : AddCircle (2 * π)) := by
  simp only [normalizer, Pi.sub_apply, Function.extend_val_apply' hj,
    Pi.zero_apply, sub_zero, inactiveArg, hj, ↓reduceIte]

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
      have hmk : Continuous fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
          (⟨x.1 j, x.2 j⟩ : ℂ) :=
        (Complex.equivRealProdCLM.symm.continuous.comp
          (by fun_prop : Continuous fun x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
            (x.1 j, x.2 j))).congr fun _ ↦ Complex.ext (by simp) (by simp)
      exact ContinuousAt.comp (g := fun z : ℂ ↦ (z.arg : AddCircle (2 * π)))
        (Complex.continuousAt_arg_coe_angle hz) hmk.continuousAt
  exact harg.sub (((continuous_extend_subtypeVal 0).comp
    (hv.continuous_vertexTorusHom (p := 2 * π))).continuousAt.comp harg)

/-- The normalizer of a point whose coordinates outside `A` are already nonnegative reals is
trivial. -/
private theorem normalizer_eq_zero {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v, 0 ≤ x.1 j ∧ x.2 j = 0) :
    normalizer hv x = 0 := by
  have harg : inactiveArg (i := i) (u := u) (c := c) (v := v) x = 0 := by
    funext j
    by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · simp only [inactiveArg, hj, ↓reduceIte, Pi.zero_apply]
    · simp only [inactiveArg, hj, ↓reduceIte, Pi.zero_apply, (hx j hj).2]
      rw [Complex.arg_eq_zero_iff.2 ⟨(hx j hj).1, rfl⟩, QuotientAddGroup.mk_zero]
  have hext : (Function.extend Subtype.val
      (0 : activeSet (facetPairing i u) c v → AddCircle (2 * π)) 0 : ι → AddCircle (2 * π)) = 0 :=
    Function.extend_const _ _
  rw [normalizer, harg, map_zero, hext, sub_zero]

open Classical in
/-- The coordinates in `A` of a point of `ℂ^ι`: the first factor of the splitting
`EuclideanSpace.sumComplEquivProd` along `A`, applied to both real coordinates. -/
private def activeCoords :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ ι →L[ℝ]
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v) :=
  (ContinuousLinearMap.fst ℝ _ _ ∘L (EuclideanSpace.sumComplEquivProd ℝ
      (· ∈ activeSet (facetPairing i u) c v)).toContinuousLinearMap).prodMap
    (ContinuousLinearMap.fst ℝ _ _ ∘L (EuclideanSpace.sumComplEquivProd ℝ
      (· ∈ activeSet (facetPairing i u) c v)).toContinuousLinearMap)

@[simp]
private theorem activeCoords_apply_fst (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (j : activeSet (facetPairing i u) c v) :
    (activeCoords (i := i) (u := u) (c := c) (v := v) x).1 j = x.1 j := by
  simp [activeCoords]

@[simp]
private theorem activeCoords_apply_snd (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (j : activeSet (facetPairing i u) c v) :
    (activeCoords (i := i) (u := u) (c := c) (v := v) x).2 j = x.2 j := by
  simp [activeCoords]

/-- The coordinates in `A` of the normalized representative do not change when the point is moved
by the kernel torus. Both normalized representatives lie in one orbit of the kernel torus and
have the same nonnegative real coordinates outside `A`. The element relating them therefore
vanishes outside `A`, and so is zero, since the active normals form a lattice basis. -/
private theorem activeCoords_torusRotation_normalizer_torusRotation (hi : IsIntegralLattice i)
    {θ : ι → AddCircle (2 * π)} (hθ : θ ∈ (facetTorusHom i u (2 * π)).ker)
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.1 j ^ 2 + x.2 j ^ 2) :
    activeCoords (i := i) (u := u) (c := c) (v := v)
        (torusRotation (normalizer hv (torusRotation θ x)) (torusRotation θ x)) =
      activeCoords (i := i) (u := u) (c := c) (v := v)
        (torusRotation (normalizer hv x) x) := by
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
    refine (torusRotation_apply_eq_self_iff_apply _ _ j).1
      ⟨hb1.trans ha1.symm, hb2.trans ha2.symm⟩ (Or.inl ?_)
    rw [ha1]
    exact (Real.sqrt_pos.2 (hx j hj)).ne'
  rw [hb, hδ, torusRotation_zero, ContinuousLinearMap.id_apply]

open Classical in
/-- The vertex chart: a class `[z]` in the source (whose coordinates outside `A` do not vanish) is
sent to the coordinates in `A` of its representative whose coordinates outside `A` are positive
reals, and `0` outside the source. -/
private def vertexChartFun (hi : IsIntegralLattice i) (q : DelzantQuotient i u c) :
    EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v) :=
  lift (fun x ↦ if ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.val.1 j ^ 2 + x.val.2 j ^ 2 then
      activeCoords (i := i) (u := u) (c := c) (v := v)
        (torusRotation (normalizer hv x) x) else 0)
    fun θ hθ x ↦ by
      simp only [coe_vadd_delzantLevel, torusRotation_apply_normSq]
      split_ifs with h
      · exact activeCoords_torusRotation_normalizer_torusRotation hv hi hθ h
      · rfl
  q

private theorem vertexChartFun_mk (hi : IsIntegralLattice i) {x : delzantLevel i u c}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.val.1 j ^ 2 + x.val.2 j ^ 2) :
    vertexChartFun hv hi (mk x) =
      activeCoords (i := i) (u := u) (c := c) (v := v)
        (torusRotation (normalizer hv x) x) := by
  rw [vertexChartFun, lift_mk, ite_eq_left hx]

private theorem vertexChartFun_mk_of_not (hi : IsIntegralLattice i) {x : delzantLevel i u c}
    (hx : ¬ ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.val.1 j ^ 2 + x.val.2 j ^ 2) :
    vertexChartFun hv hi (mk x) = 0 := by
  rw [vertexChartFun, lift_mk, ite_eq_right hx]

/-- A point of the level satisfies the strict facet inequalities outside `A` exactly when its
coordinates outside `A` have positive squared modulus. -/
private theorem lt_reducedMomentMap_mk_iff_pos (hi : IsIntegralLattice i) {x : delzantLevel i u c} :
    (∀ j ∉ activeSet (facetPairing i u) c v,
      haveI := hi.finiteDimensional
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) (mk x) (i (u j))) ↔
      ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.val.1 j ^ 2 + x.val.2 j ^ 2 := by
  have := hi.finiteDimensional
  refine forall₂_congr fun j _ ↦ ?_
  rw [reducedMomentMap_mk_apply, lt_add_iff_pos_left, div_pos_iff_of_pos_right two_pos]

/-- The vertex chart is continuous on its source. -/
private theorem continuousOn_vertexChartFun (hi : IsIntegralLattice i) :
    ContinuousOn (vertexChartFun hv hi)
      {q | ∀ j ∉ activeSet (facetPairing i u) c v,
        haveI := hi.finiteDimensional
        c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))} := by
  refine fun q hq ↦ ContinuousAt.continuousWithinAt ?_
  induction q using DelzantQuotient.inductionOn with | h x =>
  have hx := (lt_reducedMomentMap_mk_iff_pos hv hi).1 hq
  refine isOpenQuotientMap_mk.continuousAt_comp_iff.1 ?_
  -- Near `x`, the coordinates outside `A` still do not vanish, so the chart is given by the
  -- normalized representative.
  have hU : IsOpen {y : delzantLevel i u c |
      ∀ j ∉ activeSet (facetPairing i u) c v, 0 < y.val.1 j ^ 2 + y.val.2 j ^ 2} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const (by fun_prop)
  refine ContinuousAt.congr (f := fun y : delzantLevel i u c ↦
    activeCoords (i := i) (u := u) (c := c) (v := v)
      (torusRotation (normalizer hv y) y)) ?_
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy ↦
      (vertexChartFun_mk hv hi hy).symm)
  exact (ContinuousLinearMap.continuous _).continuousAt.comp
    (continuous_torusRotation.continuousAt.comp
      (((continuousAt_normalizer hv hx).comp continuous_subtypeVal.continuousAt).prodMk
        continuous_subtypeVal.continuousAt))

end Normalizer

/-! ### The vertex chart -/

section VertexChart

variable [Fintype ι] {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
  (hi : IsIntegralLattice i) [Fintype (activeSet (facetPairing i u) c v)]

/-- The translated weight model at the image of a normalized representative is the moment value
of its class. -/
private theorem vertexMoment_activeCoords_normalizer (x : delzantLevel i u c) :
    haveI := hi.finiteDimensional
    v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k)
        (activeCoords (i := i) (u := u) (c := c) (v := v)
          (torusRotation (normalizer hv x) x)) =
      reducedMomentMap (hv.surjective_linearCombination_real hi) (mk x) := by
  have := hi.finiteDimensional
  refine (hv.edgeBasis hi).ext_elem fun k ↦ ?_
  rw [IsSmoothVertex.edgeBasis_repr, IsSmoothVertex.edgeBasis_repr, vertexMoment_apply_active,
    reducedMomentMap_mk_apply, activeCoords_apply_fst, activeCoords_apply_snd,
    torusRotation_apply_normSq]

/-- `vertexLift` recovers a normalized representative from its coordinates in `A`. -/
private theorem vertexLift_activeCoords_normalizer (x : delzantLevel i u c) :
    vertexLift hv hi
        (activeCoords (i := i) (u := u) (c := c) (v := v)
          (torusRotation (normalizer hv x) x)) =
      torusRotation (normalizer hv x) x := by
  have := hi.finiteDimensional
  ext j <;> by_cases hj : j ∈ activeSet (facetPairing i u) c v
  · simp [hj]
  · rw [vertexLift_fst_of_notMem hv hi _ hj, (torusRotation_normalizer_inactive hv x hj).1,
      vertexMoment_activeCoords_normalizer, reducedMomentMap_mk_apply]
    congr 1
    ring
  · simp [hj]
  · rw [vertexLift_snd_of_notMem hv hi _ hj, (torusRotation_normalizer_inactive hv x hj).2]

/-- The vertex chart sends its source into its target. -/
private theorem vertexChartFun_mem_target {q : DelzantQuotient i u c}
    (hq : ∀ j ∉ activeSet (facetPairing i u) c v,
      haveI := hi.finiteDimensional
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))) :
    ∀ j ∉ activeSet (facetPairing i u) c v, c j <
      (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (vertexChartFun hv hi q)) (i (u j)) := by
  have := hi.finiteDimensional
  induction q using DelzantQuotient.inductionOn with | h x =>
  intro j hj
  rw [vertexChartFun_mk hv hi ((lt_reducedMomentMap_mk_iff_pos hv hi).1 hq),
    vertexMoment_activeCoords_normalizer]
  exact hq j hj

variable (hvP : v ∈ facetPolyhedron i u c)

open Classical in
/-- The inverse of the vertex chart: the class of `vertexLift w`, when the translated moment
value of `w` lies in `Δ`, and the class over `v` otherwise. -/
private def vertexChartSymm
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) : DelzantQuotient i u c :=
  if hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) then
    mk ⟨vertexLift hv hi w, vertexLift_mem_delzantLevel hv hi hw⟩
  else
    mk ⟨vertexLift hv hi 0, vertexLift_mem_delzantLevel hv hi (vertexMoment_zero_le hv hi hvP)⟩

private theorem vertexChartSymm_of_le
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    vertexChartSymm hv hi hvP w = mk ⟨vertexLift hv hi w, vertexLift_mem_delzantLevel hv hi hw⟩ :=
  dite_eq_left_of_eq_true (eq_true hw)

private theorem vertexChartSymm_of_not_le
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ¬ ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    vertexChartSymm hv hi hvP w =
      mk ⟨vertexLift hv hi 0, vertexLift_mem_delzantLevel hv hi (vertexMoment_zero_le hv hi hvP)⟩ :=
  dite_eq_right_of_eq_false (eq_false hw)

/-- The inverse of the vertex chart sends its target into its source. -/
private theorem vertexChartSymm_mem_source
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    ∀ j ∉ activeSet (facetPairing i u) c v,
      haveI := hi.finiteDimensional
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi)
        (vertexChartSymm hv hi hvP w) (i (u j)) := by
  have := hi.finiteDimensional
  have hw' := fun j hj ↦ (hw j hj).le
  intro j hj
  rw [vertexChartSymm_of_le hv hi hvP hw',
    (reducedMomentMap_mk_eq_iff _).2 (vertexLift_moment hv hi hw')]
  exact hw j hj

/-- The inverse of the vertex chart is a left inverse on the source. -/
private theorem vertexChartSymm_vertexChartFun {q : DelzantQuotient i u c}
    (hq : ∀ j ∉ activeSet (facetPairing i u) c v,
      haveI := hi.finiteDimensional
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))) :
    vertexChartSymm hv hi hvP (vertexChartFun hv hi q) = q := by
  have := hi.finiteDimensional
  induction q using DelzantQuotient.inductionOn with | h x =>
  have hle : ∀ j ∉ activeSet (facetPairing i u) c v, c j ≤
      (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k)
        (activeCoords (i := i) (u := u) (c := c) (v := v)
          (torusRotation (normalizer hv x) x)))
        (i (u j)) := fun j _ ↦ by
    rw [vertexMoment_activeCoords_normalizer]
    exact mem_facetPolyhedron.1 (reducedMomentMap_mem_facetPolyhedron _ _) j
  rw [vertexChartFun_mk hv hi ((lt_reducedMomentMap_mk_iff_pos hv hi).1 hq),
    vertexChartSymm_of_le hv hi hvP hle]
  -- The normalized representative is a rotation of `x` by the kernel torus.
  rw [← mk_vadd_of_mem_ker (normalizer_mem_ker hv hi x) x]
  exact congrArg mk (Subtype.ext (vertexLift_activeCoords_normalizer hv hi x))

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
    rw [vertexLift_fst_of_notMem hv hi w hj, vertexLift_snd_of_notMem hv hi w hj,
      Real.sq_sqrt (by linarith [hw j hj])]
    linarith [hw j hj]
  rw [vertexChartSymm_of_le hv hi hvP hw', vertexChartFun_mk hv hi hpos,
    normalizer_eq_zero hv fun j hj ↦ by simp [hj, Real.sqrt_nonneg], torusRotation_zero,
    ContinuousLinearMap.id_apply]
  ext k <;> simp

/-- The inverse of the vertex chart is continuous on its target. -/
private theorem continuousOn_vertexChartSymm :
    ContinuousOn (vertexChartSymm hv hi hvP)
      {w | ∀ j ∉ activeSet (facetPairing i u) c v,
        c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))} := by
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  refine (continuous_mk.comp (((continuous_vertexLift hv hi).comp
    continuous_subtypeVal).subtype_mk fun w ↦ ?_)).congr fun w ↦ ?_
  · exact vertexLift_mem_delzantLevel hv hi fun j hj ↦ (w.property j hj).le
  · exact (vertexChartSymm_of_le hv hi hvP fun j hj ↦ (w.property j hj).le).symm

/-- **The equivariant chart of the Delzant quotient at a smooth vertex.** Let `v` be a smooth
vertex of `Δ`, with active facets `A` and inward edge basis `ε`. The vertex chart is a
homeomorphism from the open set of points `q` of `M_Δ` with `c j < ⟨μ_Δ q, u j⟩` for every
`j ∉ A`, that is with active facets in `A`
(`TauCeti.Toric.DelzantQuotient.mem_vertexChart_source_iff`), onto the open set of `w ∈ ℂ^A`
with `c j < ⟨v + Σ_k ½ |w_k|² ε_k, u j⟩` for every `j ∉ A`. Its inverse sends `w` to the class
of the point `vertexLift w` of the level, with coordinates `w_k` in `A` and nonnegative real
coordinates outside `A` (`TauCeti.Toric.DelzantQuotient.vertexChart_symm_apply`). It intertwines
the moment map with the translated weight model
(`TauCeti.Toric.DelzantQuotient.reducedMomentMap_vertexChart_symm`) and the residual torus with
the standard rotation of `ℂ^A` (`TauCeti.Toric.DelzantQuotient.vertexChart_vadd`). -/
def vertexChart :
    OpenPartialHomeomorph (DelzantQuotient i u c)
      (EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
        EuclideanSpace ℝ (activeSet (facetPairing i u) c v)) where
  toFun := vertexChartFun hv hi
  invFun := vertexChartSymm hv hi hvP
  source := {q | ∀ j ∉ activeSet (facetPairing i u) c v,
    haveI := hi.finiteDimensional
    c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))}
  target := {w | ∀ j ∉ activeSet (facetPairing i u) c v,
    c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))}
  map_source' _ hq := vertexChartFun_mem_target hv hi hq
  map_target' _ hw := vertexChartSymm_mem_source hv hi hvP hw
  left_inv' _ hq := vertexChartSymm_vertexChartFun hv hi hvP hq
  right_inv' _ hw := vertexChartFun_vertexChartSymm hv hi hvP hw
  open_source := by
    have := hi.finiteDimensional
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const ((continuous_clm_apply.1 (continuous_reducedMomentMap _)) _)
  open_target := by
    have := hi.finiteDimensional
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_lt continuous_const
        ((continuous_clm_apply.1 (continuous_const.add (continuous_weightMomentMap _))) _)
  continuousOn_toFun := continuousOn_vertexChartFun hv hi
  continuousOn_invFun := continuousOn_vertexChartSymm hv hi hvP

private theorem coe_vertexChart : ⇑(vertexChart hv hi hvP) = vertexChartFun hv hi := by
  rw [vertexChart, OpenPartialHomeomorph.coe_mk, PartialEquiv.coe_mk]

private theorem coe_vertexChart_symm :
    ⇑(vertexChart hv hi hvP).symm = vertexChartSymm hv hi hvP := by
  rw [vertexChart, OpenPartialHomeomorph.coe_mk_symm, PartialEquiv.coe_symm_mk]

theorem vertexChart_source :
    (vertexChart hv hi hvP).source = {q | ∀ j ∉ activeSet (facetPairing i u) c v,
      haveI := hi.finiteDimensional
      c j < reducedMomentMap (hv.surjective_linearCombination_real hi) q (i (u j))} :=
  (rfl)

theorem vertexChart_target :
    (vertexChart hv hi hvP).target = {w | ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))} :=
  (rfl)

@[simp]
theorem mem_vertexChart_target_iff
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)} :
    w ∈ (vertexChart hv hi hvP).target ↔ ∀ j ∉ activeSet (facetPairing i u) c v,
      c j < (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) :=
  Iff.rfl

/-- Every point in the target of the vertex chart satisfies the weak facet inequalities outside
`A`. -/
theorem le_of_mem_vertexChart_target
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : w ∈ (vertexChart hv hi hvP).target) :
    ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j)) :=
  fun j hj ↦ ((mem_vertexChart_target_iff hv hi hvP).1 hw j hj).le

/-- **The source of the vertex chart.** A point of the Delzant quotient lies in the source of the
chart at `v` exactly when every facet active at its moment value is active at `v`. -/
theorem mem_vertexChart_source_iff {q : DelzantQuotient i u c} :
    haveI := hi.finiteDimensional
    q ∈ (vertexChart hv hi hvP).source ↔
      activeSet (facetPairing i u) c (reducedMomentMap (hv.surjective_linearCombination_real hi) q)
        ⊆ activeSet (facetPairing i u) c v := by
  have := hi.finiteDimensional
  have hq := mem_facetPolyhedron.1 (reducedMomentMap_mem_facetPolyhedron
    (hv.surjective_linearCombination_real hi) q)
  simp only [vertexChart_source, mem_ofPred_eq, subset_def, mem_activeSet, facetPairing_apply]
  refine ⟨fun h j hj ↦ by_contra fun hjv ↦ (h j hjv).ne hj.symm, fun h j hj ↦ ?_⟩
  exact (hq j).lt_of_ne fun he ↦ hj (h j he.symm)

/-- The point over `v` lies in the source of the vertex chart at `v`. -/
theorem mem_vertexChart_source_of_reducedMomentMap_eq {q : DelzantQuotient i u c}
    (h : haveI := hi.finiteDimensional
      reducedMomentMap (hv.surjective_linearCombination_real hi) q = v) :
    q ∈ (vertexChart hv hi hvP).source :=
  (mem_vertexChart_source_iff hv hi hvP).2 (by rw [h])

/-- The class of a point of the level lies in the source of the vertex chart exactly when its
coordinates outside `A` do not vanish. -/
theorem mk_mem_vertexChart_source_iff {x : delzantLevel i u c} :
    mk x ∈ (vertexChart hv hi hvP).source ↔
      ∀ j ∉ activeSet (facetPairing i u) c v, x.val.1 j ≠ 0 ∨ x.val.2 j ≠ 0 := by
  rw [vertexChart_source, mem_ofPred_eq, lt_reducedMomentMap_mk_iff_pos hv hi]
  refine forall₂_congr fun j _ ↦ ?_
  rw [(add_nonneg (sq_nonneg _) (sq_nonneg _)).lt_iff_ne', ne_eq, sq_add_sq_eq_zero, not_and_or]

/-- The vertex chart is centred at the point over `v`: `0` lies in its target. -/
theorem zero_mem_vertexChart_target : 0 ∈ (vertexChart hv hi hvP).target := by
  rw [mem_vertexChart_target_iff]
  intro j hj
  rw [weightMomentMap_zero, add_zero]
  exact (mem_facetPolyhedron.1 hvP j).lt_of_ne fun h ↦
    hj (mem_activeSet.2 (by rw [facetPairing_apply, h]))

/-- **The inverse of the vertex chart.** Whenever the translated moment value of `w` satisfies
the facet inequalities outside `A` (in particular on the target of the chart), the inverse chart
sends `w` to the class of the point `vertexLift w` of the level, with coordinates `w_k` in `A`
and nonnegative real coordinates `√(2(⟨v + Σ_k ½ |w_k|² ε_k, u j⟩ - c j))` outside `A`. -/
theorem vertexChart_symm_apply
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    (vertexChart hv hi hvP).symm w =
      mk ⟨vertexLift hv hi w, vertexLift_mem_delzantLevel hv hi hw⟩ := by
  rw [coe_vertexChart_symm]
  exact vertexChartSymm_of_le hv hi hvP hw

/-- When the translated moment value of `w` violates some facet inequality outside `A`, the
inverse of the vertex chart falls back to its value at `0`. -/
theorem vertexChart_symm_of_not_forall_le
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ¬ ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    (vertexChart hv hi hvP).symm w = (vertexChart hv hi hvP).symm 0 := by
  rw [coe_vertexChart_symm, vertexChartSymm_of_not_le hv hi hvP hw,
    vertexChartSymm_of_le hv hi hvP (vertexMoment_zero_le hv hi hvP)]

open Classical in
/-- **The vertex chart on a normalized representative.** If the coordinates outside `A` of a point
`x` of the level are positive reals, then the chart sends the class of `x` to the coordinates of
`x` in `A`. That this class lies in the source of the chart is `mk_mem_vertexChart_source_iff`. -/
theorem vertexChart_mk {x : delzantLevel i u c}
    (hx : ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.val.1 j ∧ x.val.2 j = 0) :
    vertexChart hv hi hvP (mk x) =
      ((EuclideanSpace.sumComplEquivProd ℝ (· ∈ activeSet (facetPairing i u) c v) x.val.1).1,
        (EuclideanSpace.sumComplEquivProd ℝ (· ∈ activeSet (facetPairing i u) c v) x.val.2).1) := by
  have hpos : ∀ j ∉ activeSet (facetPairing i u) c v, 0 < x.val.1 j ^ 2 + x.val.2 j ^ 2 :=
    fun j hj ↦ by nlinarith [(hx j hj).1]
  rw [coe_vertexChart, vertexChartFun_mk hv hi hpos,
    normalizer_eq_zero hv fun j hj ↦ ⟨(hx j hj).1.le, (hx j hj).2⟩, torusRotation_zero,
    ContinuousLinearMap.id_apply]
  ext j <;> simp

/-- Outside its source, the vertex chart takes the value `0`. -/
theorem vertexChart_of_notMem_source {q : DelzantQuotient i u c}
    (hq : q ∉ (vertexChart hv hi hvP).source) :
    vertexChart hv hi hvP q = 0 := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  rw [vertexChart_source, mem_ofPred_eq, lt_reducedMomentMap_mk_iff_pos hv hi] at hq
  rw [coe_vertexChart, vertexChartFun_mk_of_not hv hi hq]

/-- **The moment map in the vertex chart** is the weight model translated to the vertex:
`μ_Δ = v + Σ_k ½ |w_k|² ε_k`, whenever the translated moment value satisfies the facet
inequalities outside `A` (in particular on the target of the chart). -/
theorem reducedMomentMap_vertexChart_symm
    {w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v)}
    (hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))) :
    haveI := hi.finiteDimensional
    reducedMomentMap (hv.surjective_linearCombination_real hi) ((vertexChart hv hi hvP).symm w) =
      v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w := by
  have := hi.finiteDimensional
  rw [vertexChart_symm_apply hv hi hvP hw,
    (reducedMomentMap_mk_eq_iff _).2 (vertexLift_moment hv hi hw)]

/-- The moment value of a point of the source is the translated weight model at its image under
the vertex chart. -/
theorem add_weightMomentMap_vertexChart {q : DelzantQuotient i u c}
    (hq : q ∈ (vertexChart hv hi hvP).source) :
    haveI := hi.finiteDimensional
    v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (vertexChart hv hi hvP q) =
      reducedMomentMap (hv.surjective_linearCombination_real hi) q := by
  have := hi.finiteDimensional
  rw [← reducedMomentMap_vertexChart_symm hv hi hvP
      (le_of_mem_vertexChart_target hv hi hvP ((vertexChart hv hi hvP).map_source hq)),
    (vertexChart hv hi hvP).left_inv hq]

/-- **The centre of the vertex chart.** A point of the source of the chart at `v` is sent to `0`
exactly when it lies over `v`: the weights `-ε_k` of the translated weight model are linearly
independent. -/
theorem vertexChart_eq_zero_iff {q : DelzantQuotient i u c}
    (hq : q ∈ (vertexChart hv hi hvP).source) :
    haveI := hi.finiteDimensional
    vertexChart hv hi hvP q = 0 ↔
      reducedMomentMap (hv.surjective_linearCombination_real hi) q = v := by
  have := hi.finiteDimensional
  rw [← add_weightMomentMap_vertexChart hv hi hvP hq, add_eq_left,
    weightMomentMap_eq_zero_iff (α := fun k ↦ -hv.edgeBasis hi k)
      (hv.edgeBasis hi).linearIndependent.neg]

/-- The point of the Delzant quotient at the centre of the vertex chart lies over `v`; it is the
fixed point over `v` (`TauCeti.Toric.DelzantQuotient.bijOn_reducedMomentMap_fixedPoints`). -/
theorem reducedMomentMap_vertexChart_symm_zero :
    haveI := hi.finiteDimensional
    reducedMomentMap (hv.surjective_linearCombination_real hi) ((vertexChart hv hi hvP).symm 0) =
      v := by
  have := hi.finiteDimensional
  rw [reducedMomentMap_vertexChart_symm hv hi hvP
      (le_of_mem_vertexChart_target hv hi hvP (zero_mem_vertexChart_target hv hi hvP)),
    weightMomentMap_zero, add_zero]

/-- **Equivariance of the vertex chart.** The inverse of the chart intertwines the rotation
`w_k ↦ exp(-i φ_k) w_k` of `ℂ^A` with the action of the residual torus through the isomorphism
`(ℝ / 2πℤ)^A ≃ (ℝ / 2πℤ)^ι / N_Δ` (`TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv`). -/
theorem vertexChart_symm_torusRotation
    (w : EuclideanSpace ℝ (activeSet (facetPairing i u) c v) ×
      EuclideanSpace ℝ (activeSet (facetPairing i u) c v))
    (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π)) :
    (vertexChart hv hi hvP).symm (torusRotation φ w) =
      hv.vertexTorusEquiv (2 * π) hi φ +ᵥ (vertexChart hv hi hvP).symm w := by
  by_cases hw : ∀ j ∉ activeSet (facetPairing i u) c v,
      c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) w) (i (u j))
  · have hφw : ∀ j ∉ activeSet (facetPairing i u) c v,
        c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (torusRotation φ w)) (i (u j)) := by
      simpa only [weightMomentMap_torusRotation] using hw
    rw [vertexChart_symm_apply hv hi hvP hw, vertexChart_symm_apply hv hi hvP hφw,
      IsSmoothVertex.vertexTorusEquiv_apply, coe_vadd_mk]
    exact congrArg mk (Subtype.ext (vertexLift_torusRotation hv hi φ w))
  · have hφw : ¬ ∀ j ∉ activeSet (facetPairing i u) c v,
        c j ≤ (v + weightMomentMap (fun k ↦ -hv.edgeBasis hi k) (torusRotation φ w)) (i (u j)) := by
      simpa only [weightMomentMap_torusRotation] using hw
    rw [vertexChart_symm_of_not_forall_le hv hi hvP hw,
      vertexChart_symm_of_not_forall_le hv hi hvP hφw,
      vertexChart_symm_apply hv hi hvP (vertexMoment_zero_le hv hi hvP),
      IsSmoothVertex.vertexTorusEquiv_apply, coe_vadd_mk]
    refine congrArg mk (Subtype.ext ?_)
    rw [coe_vadd_delzantLevel, ← vertexLift_torusRotation, map_zero]

/-- **Equivariance of the vertex chart.** The vertex chart intertwines the action of the class of
`φ ∈ (ℝ / 2πℤ)^A` in the residual torus with the rotation `w_k ↦ exp(-i φ_k) w_k`. -/
theorem vertexChart_vadd (q : DelzantQuotient i u c)
    (φ : activeSet (facetPairing i u) c v → AddCircle (2 * π)) :
    vertexChart hv hi hvP (hv.vertexTorusEquiv (2 * π) hi φ +ᵥ q) =
      torusRotation φ (vertexChart hv hi hvP q) := by
  by_cases hq : q ∈ (vertexChart hv hi hvP).source
  · have hw := (vertexChart hv hi hvP).map_source hq
    have hφw : torusRotation φ (vertexChart hv hi hvP q) ∈ (vertexChart hv hi hvP).target := by
      simpa only [mem_vertexChart_target_iff, weightMomentMap_torusRotation] using hw
    conv_lhs => rw [← (vertexChart hv hi hvP).left_inv hq]
    rw [← vertexChart_symm_torusRotation hv hi hvP, (vertexChart hv hi hvP).right_inv hφw]
  · have hφq : hv.vertexTorusEquiv (2 * π) hi φ +ᵥ q ∉ (vertexChart hv hi hvP).source := by
      have := hi.finiteDimensional
      simpa only [vertexChart_source, mem_ofPred_eq, reducedMomentMap_vadd] using hq
    rw [vertexChart_of_notMem_source hv hi hvP hφq, vertexChart_of_notMem_source hv hi hvP hq,
      map_zero]

end VertexChart

end DelzantQuotient

/-! ### The vertex charts cover the Delzant quotient -/

namespace IsDelzant

open DelzantQuotient

variable [Fintype ι] (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)

open Classical in
/-- **The vertex charts cover the Delzant quotient.** Every point of `M_Δ` lies in the
source of the chart at some vertex of `Δ`: the facets active at its moment value are among those
active at some vertex. -/
theorem exists_mem_vertexChart_source (q : DelzantQuotient i u c) :
    ∃ (v : StrongDual ℝ V) (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ),
      q ∈ (vertexChart (hΔ.isSmoothVertex v hv) hi hv.1).source := by
  have := hi.finiteDimensional
  have hβ := surjective_linearCombination_real hi.span_range_eq_top
    hΔ.surjective_linearCombination
  obtain ⟨v, hv, hsub⟩ := exists_mem_extremePoints_activeSet_subset
    (isCompact_facetPolyhedron_of_isBounded hΔ.isBounded)
    (reducedMomentMap_mem_facetPolyhedron hβ q)
  exact ⟨v, hv, (mem_vertexChart_source_iff _ hi _).2 hsub⟩

end IsDelzant

end TauCeti.Toric
