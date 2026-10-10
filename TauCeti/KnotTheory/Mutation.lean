/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.KnotTheory.SmoothCircle

/-!
# Conway mutation of knots

Let `K` be a knot in a three-manifold and `B` a smoothly embedded closed three-ball whose boundary
sphere meets `K` in four points, through which `K` crosses from the inside of `B` to its outside.
Such a sphere is a *Conway sphere* for `K`. A *Conway mutant* of `K` is obtained by cutting out the
two-string tangle `K ∩ B` and gluing it back after one of the three half-turns of `B` that preserve
the four boundary points. Its orientation is fixed by local agreement with `K` on an outside arc.

The construction is stated on the geometric presentation of a knot, a smooth circle embedding
`K : S¹ → M` (`TauCeti.SmoothCircleEmbedding`), with the ball given by a smooth embedding
`e : ℝ³ → M` as the image `e (D³)` of the closed unit ball. A choice of `e`, after an isotopy of
`K` supported near the sphere, brings every Conway sphere into the following standard position:

* the four points are `TauCeti.conwayPoints`, the points `(±1/√2, ±1/√2, 0)` of the unit sphere;
* the half-turns are `TauCeti.conwayHalfTurn i`, the rotations by `π` about the three coordinate
  axes, each of which permutes the four points without fixed points;
* near the sphere the knot is invariant under the chosen half-turn. Then rotating the tangle inside
  `B` leaves the knot unchanged near `∂B`, so the mutated set is again a smooth curve there.

The mutated set (`TauCeti.conwayMutation`) is `(K \ B) ∪ ρ(K ∩ B)`, read through `e`. Being a
mutant (`TauCeti.IsConwayMutant K K'`) is a relation between parametrized knots, rather than an
operation, because the mutated set must be reparametrized as a circle: `K'` is a mutant of `K` when
its image is the mutated set of `K` along some Conway sphere and half-turn, and when it agrees with
`K` near some point outside the ball up to an orientation-preserving change of parameter. For a
knot, this local agreement fixes the orientation of the mutant; the definition imposes agreement
only near the chosen point on its outside arc.

Mutation is symmetric (`TauCeti.IsConwayMutant.symm`): rotating the mutated tangle back recovers
`K` along the same Conway sphere. It is compatible with ambient diffeomorphisms, and a knot whose
tangle is itself invariant under the half-turn is a mutant of itself. The unknot in `S³` has Conway
spheres in standard position for all three half-turns, so the definitions apply to actual knots.

Mutants share many invariants: they have the same Alexander, Jones and HOMFLY polynomials. They need
not be concordant, however. Kirk and Livingston found infinite families of knots that are not even
topologically concordant to their positive mutants, answering Kirby's problem 1.53.
`TauCeti.KirkLivingstonMutationTheorem` records the resulting statement in the smooth category: some
knot in `S³` is not smoothly concordant to some Conway mutant. It is stated, not proved.

## Main definitions

* `TauCeti.conwayHalfTurn i`: the half-turn of `ℝ³` about the `i`-th coordinate axis.
* `TauCeti.conwayPoints`: the four points `(±1/√2, ±1/√2, 0)` of the unit sphere of `ℝ³`.
* `TauCeti.IsConwaySphere K e i`: the ball `e (D³)` meets `K` in a Conway sphere in standard
  position for the half-turn `i`.
* `TauCeti.conwayMutation e i S`: the set obtained from `S ⊆ M` by rotating its part inside the
  ball `e (D³)` by the half-turn `i`.
* `TauCeti.IsConwayMutant K K'`: `K'` is a Conway mutant of `K`.
* `TauCeti.KirkLivingstonMutationTheorem`: some knot in `S³` is not smoothly concordant to one of
  its Conway mutants.

## Main results

* `TauCeti.conwayMutation_conwayMutation`: mutating twice along the same ball and half-turn is the
  identity.
* `TauCeti.IsConwaySphere.of_range_eq_conwayMutation`: the Conway sphere of `K` is a Conway sphere
  of every mutant along it.
* `TauCeti.IsConwayMutant.symm`: mutation is a symmetric relation.
* `TauCeti.IsConwayMutant.transDiffeomorph`: mutation is preserved by ambient diffeomorphisms.
* `TauCeti.exists_isConwaySphere_unknot`: the unknot in `S³` has a Conway sphere in standard
  position for each half-turn; in a suitable ball chart it is an ellipse crossing the unit sphere
  at the four Conway points.

## References

* J. H. Conway, *An enumeration of knots and links, and some of their algebraic properties*, in
  *Computational Problems in Abstract Algebra* (1970), 329–358.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (mutation and the Jones polynomial).
* P. Kirk and C. Livingston, *Concordance and mutation*, Geom. Topol. 5 (2001), 831–883.
* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 1.53, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
-/

public section

noncomputable section

namespace TauCeti

open Function Set Metric Filter Topology
open scoped Manifold ContDiff

/-! ### The standard Conway sphere -/

/-- The half-turn of `ℝ³` about the `i`-th coordinate axis: the rotation by `π` which fixes the
`i`-th coordinate and negates the other two. -/
def conwayHalfTurn (i : Fin 3) : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j ↦
    if j = i then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ

@[simp]
theorem conwayHalfTurn_apply (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    conwayHalfTurn i x j = if j = i then x j else -x j := by
  by_cases h : j = i <;> simp [conwayHalfTurn, h]

/-- A half-turn is an involution. -/
@[simp]
theorem conwayHalfTurn_conwayHalfTurn (i : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    conwayHalfTurn i (conwayHalfTurn i x) = x := by
  ext j
  by_cases h : j = i <;> simp [h]

/-- A half-turn is its own inverse. -/
@[simp]
theorem conwayHalfTurn_symm (i : Fin 3) : (conwayHalfTurn i).symm = conwayHalfTurn i :=
  LinearIsometryEquiv.ext fun x ↦ (conwayHalfTurn i).symm_apply_eq.2 (by simp)

/-- The four points `(±1/√2, ±1/√2, 0)` of the unit sphere of `ℝ³` along which a knot in standard
position crosses its Conway sphere. -/
def conwayPoints : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | x 0 ^ 2 = 1 / 2 ∧ x 1 ^ 2 = 1 / 2 ∧ x 2 = 0}

/-- A point is a Conway point when its first two coordinates square to `1 / 2` and its last
vanishes. -/
@[simp]
theorem mem_conwayPoints {x : EuclideanSpace ℝ (Fin 3)} :
    x ∈ conwayPoints ↔ x 0 ^ 2 = 1 / 2 ∧ x 1 ^ 2 = 1 / 2 ∧ x 2 = 0 :=
  Iff.rfl

/-- The Conway points lie on the unit sphere. -/
theorem conwayPoints_subset_sphere : conwayPoints ⊆ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rintro x ⟨h0, h1, h2⟩
  rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg x) zero_le_one,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h0, h1, h2]
  norm_num

/-- A half-turn permutes the four Conway points. -/
theorem conwayHalfTurn_mem_conwayPoints_iff (i : Fin 3) {x : EuclideanSpace ℝ (Fin 3)} :
    conwayHalfTurn i x ∈ conwayPoints ↔ x ∈ conwayPoints := by
  simp only [mem_conwayPoints, conwayHalfTurn_apply]
  split_ifs <;> simp

/-- A half-turn fixes none of the four Conway points: it permutes them by a product of two
transpositions. -/
theorem conwayHalfTurn_ne_self_of_mem_conwayPoints (i : Fin 3) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ conwayPoints) : conwayHalfTurn i x ≠ x := by
  obtain ⟨h0, h1, -⟩ := hx
  have h0' : x 0 ≠ 0 := fun h ↦ by norm_num [h] at h0
  have h1' : x 1 ≠ 0 := fun h ↦ by norm_num [h] at h1
  intro h
  have hj : ∃ j : Fin 3, j ≠ i ∧ x j ≠ 0 := by
    fin_cases i
    · exact ⟨1, by decide, h1'⟩
    · exact ⟨0, by decide, h0'⟩
    · exact ⟨0, by decide, h0'⟩
  obtain ⟨j, hji, hxj⟩ := hj
  have := congrArg (· j) h
  simp only [conwayHalfTurn_apply, hji, ite_false] at this
  exact hxj (by linarith)

/-- A half-turn maps each closed ball about the origin onto itself. -/
private theorem conwayHalfTurn_mem_closedBall_iff (i : Fin 3) {x : EuclideanSpace ℝ (Fin 3)}
    {r : ℝ} :
    conwayHalfTurn i x ∈ closedBall 0 r ↔ x ∈ closedBall 0 r := by
  simp only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]

/-! ### Conway mutation of a set -/

/-- The **Conway mutation** of a set `S ⊆ M` along the ball `e (D³)` and the half-turn
`conwayHalfTurn i`: the part of `S` outside the ball is kept, and the part inside it is rotated by
the half-turn. -/
def conwayMutation {M : Type*} (e : EuclideanSpace ℝ (Fin 3) → M) (i : Fin 3) (S : Set M) :
    Set M :=
  (S \ e '' closedBall 0 1) ∪ e '' (conwayHalfTurn i '' (e ⁻¹' S ∩ closedBall 0 1))

section Mutation

variable {M : Type*} {e : EuclideanSpace ℝ (Fin 3) → M} {i : Fin 3} {S : Set M}

/-- A point lies in a Conway mutation when it lies in the set outside the ball, or it is the image
of a point of the ball whose half-turn the set contains. -/
theorem mem_conwayMutation_iff {y : M} :
    y ∈ conwayMutation e i S ↔
      (y ∈ S ∧ y ∉ e '' closedBall 0 1) ∨
        ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
          e x = y ∧ e (conwayHalfTurn i x) ∈ S := by
  simp only [conwayMutation, mem_union, Set.mem_sdiff, mem_image, mem_inter_iff, mem_preimage]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨_, ⟨x, ⟨hxS, hx⟩, rfl⟩, rfl⟩
    exact ⟨_, (conwayHalfTurn_mem_closedBall_iff i).2 hx, rfl, by simpa using hxS⟩
  · rintro ⟨x, hx, rfl, hxS⟩
    exact ⟨x, ⟨_, ⟨hxS, (conwayHalfTurn_mem_closedBall_iff i).2 hx⟩, by simp⟩, rfl⟩

/-- Outside the ball, a Conway mutation agrees with the original set. -/
@[simp]
theorem mem_conwayMutation_of_notMem_image {y : M} (hy : y ∉ e '' closedBall 0 1) :
    y ∈ conwayMutation e i S ↔ y ∈ S := by
  rw [mem_conwayMutation_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨x, hx, rfl, -⟩)
    · exact h
    · exact absurd ⟨x, hx, rfl⟩ hy
  · exact fun h ↦ Or.inl ⟨h, hy⟩

variable (he : Injective e)
include he

/-- At a point of the ball, a Conway mutation contains the point exactly when the original set
contains its image under the half-turn. -/
@[simp]
theorem apply_mem_conwayMutation_of_mem_closedBall {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ closedBall 0 1) :
    e x ∈ conwayMutation e i S ↔ e (conwayHalfTurn i x) ∈ S := by
  rw [mem_conwayMutation_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨x', -, hxx', hS⟩)
    · exact absurd ⟨x, hx, rfl⟩ h
    · rwa [← he hxx']
  · exact fun hS ↦ Or.inr ⟨x, hx, rfl, hS⟩

/-- Outside the unit ball, a Conway mutation agrees with the original set, read through `e`. -/
@[simp]
theorem apply_mem_conwayMutation_of_one_lt_norm {x : EuclideanSpace ℝ (Fin 3)} (hx : 1 < ‖x‖) :
    e x ∈ conwayMutation e i S ↔ e x ∈ S := by
  refine mem_conwayMutation_of_notMem_image ?_
  rintro ⟨x', hx', hxx'⟩
  rw [he hxx'] at hx'
  exact (mem_closedBall_zero_iff.1 hx').not_gt hx

/-- Mutating twice along the same ball and half-turn gives back the original set. -/
@[simp]
theorem conwayMutation_conwayMutation : conwayMutation e i (conwayMutation e i S) = S := by
  ext y
  by_cases hy : y ∈ e '' closedBall 0 1
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [apply_mem_conwayMutation_of_mem_closedBall he hx,
      apply_mem_conwayMutation_of_mem_closedBall he ((conwayHalfTurn_mem_closedBall_iff i).2 hx),
      conwayHalfTurn_conwayHalfTurn]
  · rw [mem_conwayMutation_of_notMem_image hy, mem_conwayMutation_of_notMem_image hy]

/-- Near the sphere `e (S²)`, a Conway mutation of a set which is invariant there under the
half-turn agrees with the set. -/
theorem apply_mem_conwayMutation_iff_of_invariant {ε : ℝ}
    (hS : ∀ x : EuclideanSpace ℝ (Fin 3), 1 - ε < ‖x‖ → ‖x‖ < 1 + ε →
      (e (conwayHalfTurn i x) ∈ S ↔ e x ∈ S))
    {x : EuclideanSpace ℝ (Fin 3)} (h₁ : 1 - ε < ‖x‖) (h₂ : ‖x‖ < 1 + ε) :
    e x ∈ conwayMutation e i S ↔ e x ∈ S := by
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · rw [apply_mem_conwayMutation_of_mem_closedBall he (mem_closedBall_zero_iff.2 hx),
      hS x h₁ h₂]
  · exact apply_mem_conwayMutation_of_one_lt_norm he hx

omit he in
/-- An injective map carries the Conway mutation along a ball to the Conway mutation along the
transported ball. -/
theorem image_conwayMutation {N : Type*} {Φ : M → N} (hΦ : Injective Φ) (S : Set M) :
    Φ '' conwayMutation e i S = conwayMutation (Φ ∘ e) i (Φ '' S) := by
  simp only [conwayMutation, image_union, image_sdiff hΦ, image_comp, preimage_comp,
    hΦ.preimage_image]

end Mutation

/-! ### Conway spheres -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- The ball `e (D³)` meets the knot `K` in a **Conway sphere in standard position** for the
half-turn `conwayHalfTurn i`:

* the sphere `e (S²)` meets `K` exactly in the four Conway points;
* `K` crosses the sphere at each of them, accumulating there both from inside and from outside
  the ball;
* on a neighbourhood of the sphere, `K` is invariant under the half-turn. -/
structure IsConwaySphere (K : SmoothCircleEmbedding (𝓡 3) M)
    (e : SmoothEmbedding (𝓡 3) (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3)) M) (i : Fin 3) : Prop where
  /-- The sphere meets the knot exactly in the four Conway points. -/
  preimage_range_inter_sphere : e ⁻¹' range K ∩ sphere 0 1 = conwayPoints
  /-- The knot crosses the sphere at each Conway point. -/
  mem_closure_inside (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ conwayPoints) :
    x ∈ closure (e ⁻¹' range K ∩ ball 0 1)
  /-- The knot crosses the sphere at each Conway point. -/
  mem_closure_outside (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ conwayPoints) :
    x ∈ closure (e ⁻¹' range K \ closedBall 0 1)
  /-- Near the sphere, the knot is invariant under the half-turn. -/
  exists_invariant : ∃ ε > 0, ∀ x : EuclideanSpace ℝ (Fin 3), 1 - ε < ‖x‖ → ‖x‖ < 1 + ε →
    (e (conwayHalfTurn i x) ∈ range K ↔ e x ∈ range K)


variable {e : SmoothEmbedding (𝓡 3) (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3)) M} {i : Fin 3}

/-- A Conway sphere of `K` in standard position for a half-turn is also one for every knot whose
image is the mutation of `K` along it: near the sphere the mutation does not change the knot. -/
theorem IsConwaySphere.of_range_eq_conwayMutation {K K' : SmoothCircleEmbedding (𝓡 3) M}
    (hK : IsConwaySphere K e i) (hK' : range K' = conwayMutation e i (range K)) :
    IsConwaySphere K' e i := by
  obtain ⟨ε, hε, hinv⟩ := hK.exists_invariant
  -- On the open shell `1 - ε < ‖x‖ < 1 + ε` around the sphere the two knots agree.
  set U : Set (EuclideanSpace ℝ (Fin 3)) := {x | 1 - ε < ‖x‖ ∧ ‖x‖ < 1 + ε} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hagree : ∀ x ∈ U, e x ∈ range K' ↔ e x ∈ range K := fun x hx ↦ by
    rw [hK']
    exact apply_mem_conwayMutation_iff_of_invariant e.isEmbedding.injective hinv hx.1 hx.2
  have hsphere : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ U := fun x hx ↦ by
    rw [mem_sphere_zero_iff_norm] at hx
    exact ⟨by linarith, by linarith⟩
  have hclosure : ∀ {T : Set (EuclideanSpace ℝ (Fin 3))} {x}, x ∈ sphere 0 1 →
      x ∈ closure (e ⁻¹' range K ∩ T) → x ∈ closure (e ⁻¹' range K' ∩ T) := by
    intro T x hx hcl
    have h := hUo.inter_closure ⟨hsphere hx, hcl⟩
    refine closure_mono ?_ h
    rintro y ⟨hyU, hyK, hyT⟩
    exact ⟨(hagree y hyU).2 hyK, hyT⟩
  refine ⟨?_, fun x hx ↦ ?_, fun x hx ↦ ?_, ⟨ε, hε, fun x h₁ h₂ ↦ ?_⟩⟩
  · rw [← hK.preimage_range_inter_sphere]
    ext x
    simp only [mem_inter_iff, mem_preimage]
    exact and_congr_left fun hx ↦ hagree x (hsphere hx)
  · exact hclosure (conwayPoints_subset_sphere hx) (hK.mem_closure_inside x hx)
  · have h := hK.mem_closure_outside x hx
    rw [sdiff_eq_compl_inter, inter_comm] at h ⊢
    exact hclosure (conwayPoints_subset_sphere hx) h
  · have hρ : conwayHalfTurn i x ∈ U := by
      simpa only [hU, mem_ofPred_eq, LinearIsometryEquiv.norm_map] using And.intro h₁ h₂
    rw [hagree _ hρ, hagree x ⟨h₁, h₂⟩]
    exact hinv x h₁ h₂

/-- `K'` is a **Conway mutant** of `K`: there is a Conway sphere `e (S²)` of `K` in standard
position for a half-turn `conwayHalfTurn i` such that

* the image of `K'` is the mutation of the image of `K` along it, and
* at some parameter `θ` where `K` lies outside the ball, `K'` agrees with `K` up to an
  orientation-preserving change of parameter locally on the outside arc containing `θ`.

Here `t ↦ K (Circle.exp t)` reads `K` as a `2π`-periodic curve. -/
def IsConwayMutant (K K' : SmoothCircleEmbedding (𝓡 3) M) : Prop :=
  ∃ (e : SmoothEmbedding (𝓡 3) (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3)) M) (i : Fin 3),
    IsConwaySphere K e i ∧ range K' = conwayMutation e i (range K) ∧
      ∃ θ : ℝ, K (Circle.exp θ) ∉ e '' closedBall 0 1 ∧
        ∃ h : ℝ ≃o ℝ, ∀ᶠ t in 𝓝 θ, K' (Circle.exp (h t)) = K (Circle.exp t)

variable {K K' : SmoothCircleEmbedding (𝓡 3) M}

/-- Conway mutation is characterized by a Conway sphere, the mutated image, and local
orientation agreement on an outside arc. -/
theorem isConwayMutant_iff : IsConwayMutant K K' ↔
    ∃ (e : SmoothEmbedding (𝓡 3) (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3)) M) (i : Fin 3),
      IsConwaySphere K e i ∧ range K' = conwayMutation e i (range K) ∧
        ∃ θ : ℝ, K (Circle.exp θ) ∉ e '' closedBall 0 1 ∧
          ∃ h : ℝ ≃o ℝ, ∀ᶠ t in 𝓝 θ, K' (Circle.exp (h t)) = K (Circle.exp t) :=
  Iff.rfl

/-- **Mutation is symmetric**: rotating the tangle of a mutant back along the same Conway sphere
recovers the original knot. -/
theorem IsConwayMutant.symm (h : IsConwayMutant K K') : IsConwayMutant K' K := by
  obtain ⟨e, i, hK, hK', θ, hθ, h, hh⟩ := h
  refine ⟨e, i, hK.of_range_eq_conwayMutation hK',
    by rw [hK', conwayMutation_conwayMutation e.isEmbedding.injective],
    h θ, by rwa [hh.self_of_nhds], h.symm, ?_⟩
  have ht : Tendsto h.symm (𝓝 (h θ)) (𝓝 θ) := by
    simpa using h.symm.toHomeomorph.continuous.tendsto (h θ)
  filter_upwards [ht.eventually hh] with t ht
  simpa using ht.symm

/-- A knot whose whole tangle inside a Conway sphere is invariant under the half-turn is a mutant
of itself. -/
theorem IsConwaySphere.isConwayMutant_self (hK : IsConwaySphere K e i)
    (hinv : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
      e (conwayHalfTurn i x) ∈ range K ↔ e x ∈ range K) :
    IsConwayMutant K K := by
  -- Some point of the knot lies outside the ball, since the knot crosses the sphere.
  have hp : (!₂[(√2)⁻¹, (√2)⁻¹, 0] : EuclideanSpace ℝ (Fin 3)) ∈ conwayPoints := by
    refine ⟨?_, ?_, rfl⟩ <;> simp [inv_pow]
  obtain ⟨y, hyK, hy⟩ := closure_nonempty_iff.1 ⟨_, hK.mem_closure_outside _ hp⟩
  obtain ⟨z, hz⟩ := hyK
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  refine ⟨e, i, hK, ?_, θ, ?_, OrderIso.refl ℝ, Eventually.of_forall fun t ↦ rfl⟩
  · ext y
    by_cases hy : y ∈ e '' closedBall 0 1
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [apply_mem_conwayMutation_of_mem_closedBall e.isEmbedding.injective hx, hinv x hx]
    · exact (mem_conwayMutation_of_notMem_image hy).symm
  · rintro ⟨x, hx, hxy⟩
    rw [hz] at hxy
    rw [← e.isEmbedding.injective hxy] at hy
    exact hy hx

/-! ### Ambient diffeomorphisms -/

section Diffeomorph

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N]

/-- An ambient diffeomorphism carries a Conway sphere of a knot to a Conway sphere of the
transported knot. -/
theorem IsConwaySphere.transDiffeomorph (hK : IsConwaySphere K e i)
    (Φ : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    IsConwaySphere (K.transDiffeomorph Φ) (e.transDiffeomorph Φ) i := by
  have h : e.transDiffeomorph Φ ⁻¹' range (K.transDiffeomorph Φ) = e ⁻¹' range K := by
    rw [SmoothEmbedding.coe_transDiffeomorph, preimage_comp,
      SmoothEmbedding.range_transDiffeomorph, (EquivLike.injective Φ).preimage_image]
  obtain ⟨ε, hε, hinv⟩ := hK.exists_invariant
  refine ⟨?_, fun x hx ↦ ?_, fun x hx ↦ ?_, ⟨ε, hε, fun x h₁ h₂ ↦ ?_⟩⟩
  · rw [h, hK.preimage_range_inter_sphere]
  · rw [h]
    exact hK.mem_closure_inside x hx
  · rw [h]
    exact hK.mem_closure_outside x hx
  · rw [← mem_preimage, h, ← mem_preimage (f := e.transDiffeomorph Φ), h]
    exact hinv x h₁ h₂

/-- **Mutation is preserved by ambient diffeomorphisms.** -/
theorem IsConwayMutant.transDiffeomorph (h : IsConwayMutant K K')
    (Φ : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    IsConwayMutant (K.transDiffeomorph Φ) (K'.transDiffeomorph Φ) := by
  obtain ⟨e, i, hK, hK', θ, hθ, h, hh⟩ := h
  refine ⟨e.transDiffeomorph Φ, i, hK.transDiffeomorph Φ, ?_, θ, ?_, h, ?_⟩
  · rw [SmoothEmbedding.range_transDiffeomorph, hK', image_conwayMutation (EquivLike.injective Φ),
      SmoothEmbedding.range_transDiffeomorph, SmoothEmbedding.coe_transDiffeomorph]
  · rintro ⟨x, hx, hxθ⟩
    simp only [SmoothEmbedding.transDiffeomorph_apply] at hxθ
    exact hθ ⟨x, hx, (EquivLike.injective Φ) hxθ⟩
  · filter_upwards [hh] with t ht
    simp only [SmoothEmbedding.transDiffeomorph_apply, ht]

end Diffeomorph

/-! ### The unknot -/

section Unknot

open Module


/-- The dimension of `ℝ⁴`, in the form the stereographic charts of `S³` take it. -/
private theorem fact_finrank_euclideanSpace_four :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] fact_finrank_euclideanSpace_four

/-- The point `(0, 0, 0, 1)` of `S³`, from which the chart below projects. -/
private def northPole : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ⟨EuclideanSpace.single 3 1, by simp⟩

/-- The orthogonal complement of `northPole` is the hyperplane of vanishing last coordinate. -/
private theorem mem_orthogonal_northPole {y : EuclideanSpace ℝ (Fin 4)} :
    y ∈ (ℝ ∙ (northPole : EuclideanSpace ℝ (Fin 4)))ᗮ ↔ y 3 = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [northPole, EuclideanSpace.inner_single_left]

/-- The linear isomorphism `w ↦ (√2 w₀, √6 w₁, w₂, 0)` onto the orthogonal complement of
`northPole`. It turns the ellipse `w₀² + 3 w₁² = 2, w₂ = 0` into the circle of radius `2` that the
stereographic projection from `northPole` makes of the unknot. -/
private def ellipseCoord :
    EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] (ℝ ∙ (northPole : EuclideanSpace ℝ (Fin 4)))ᗮ where
  toFun w := ⟨!₂[√2 * w 0, √6 * w 1, w 2, 0], mem_orthogonal_northPole.2 (by simp)⟩
  invFun y := !₂[(y : EuclideanSpace ℝ (Fin 4)) 0 / √2, (y : EuclideanSpace ℝ (Fin 4)) 1 / √6,
    (y : EuclideanSpace ℝ (Fin 4)) 2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c w := by ext i; fin_cases i <;> simp <;> ring
  left_inv w := by ext i; fin_cases i <;> simp
  right_inv y := by
    ext i
    fin_cases i
    · simp [field]
    · simp [field]
    · simp
    · simpa using (mem_orthogonal_northPole.1 y.2).symm

private theorem norm_sq_ellipseCoord (w : EuclideanSpace ℝ (Fin 3)) :
    ‖(ellipseCoord w : EuclideanSpace ℝ (Fin 4))‖ ^ 2 = 2 * w 0 ^ 2 + 6 * w 1 ^ 2 + w 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp [ellipseCoord, mul_pow]

/-- `ellipseCoord`, read in the model space of the stereographic chart at `northPole`. -/
private def ellipseChart : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ellipseCoord.toContinuousLinearEquiv.trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere northPole)).repr.toContinuousLinearEquiv

/-- A ball chart of `S³` in which the unknot is the ellipse `w₀² + 3 w₁² = 2, w₂ = 0`: the inverse
stereographic projection from `northPole`, precomposed with `ellipseChart`. -/
private def unknotConwayBall : SmoothEmbedding (𝓡 3) (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3))
    (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  SmoothEmbedding.ofIsSmoothEmbedding ((stereographic' 3 northPole).symm ∘ ellipseChart)
    (isSmoothEmbedding_comp_diffeomorph ellipseChart.toDiffeomorph
      (isSmoothEmbedding_stereographic'_symm northPole))

/-- The ball chart in the coordinates of `ℝ⁴`. -/
private theorem coe_unknotConwayBall_apply (w : EuclideanSpace ℝ (Fin 3)) :
    (unknotConwayBall w : EuclideanSpace ℝ (Fin 4)) =
      (2 * w 0 ^ 2 + 6 * w 1 ^ 2 + w 2 ^ 2 + 4)⁻¹ • (4 : ℝ) •
          (ellipseCoord w : EuclideanSpace ℝ (Fin 4)) +
        (2 * w 0 ^ 2 + 6 * w 1 ^ 2 + w 2 ^ 2 + 4)⁻¹ •
          (2 * w 0 ^ 2 + 6 * w 1 ^ 2 + w 2 ^ 2 - 4) • EuclideanSpace.single 3 1 := by
  have h := stereographic'_symm_apply (n := 3) northPole (ellipseChart w)
  simp only [ellipseChart, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', norm_sq_ellipseCoord] at h
  have hN : (northPole : EuclideanSpace ℝ (Fin 4)) = EuclideanSpace.single 3 1 := rfl
  have he : unknotConwayBall w = (stereographic' 3 northPole).symm (ellipseChart w) :=
    congrFun (SmoothEmbedding.coe_ofIsSmoothEmbedding _ _) w
  rw [he, ← hN]
  exact h

/-- In the ball chart, the unknot is the ellipse `w₀² + 3 w₁² = 2, w₂ = 0`. -/
private theorem unknotConwayBall_mem_range_unknot_iff (w : EuclideanSpace ℝ (Fin 3)) :
    unknotConwayBall w ∈ range unknot ↔ w 2 = 0 ∧ w 0 ^ 2 + 3 * w 1 ^ 2 = 2 := by
  have hc := coe_unknotConwayBall_apply w
  have hpos : 0 < 2 * w 0 ^ 2 + 6 * w 1 ^ 2 + w 2 ^ 2 + 4 := by positivity
  constructor
  · rintro ⟨z, hz⟩
    have h2 := congrArg (fun p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      (p : EuclideanSpace ℝ (Fin 4)) 2) hz
    have h3 := congrArg (fun p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      (p : EuclideanSpace ℝ (Fin 4)) 3) hz
    simp only [coe_unknot_apply, hc] at h2 h3
    simp [ellipseCoord] at h2 h3
    have hw2 : w 2 = 0 := h2.resolve_left hpos.ne'
    have hq := h3.resolve_left hpos.ne'
    rw [hw2] at hq
    exact ⟨hw2, by linarith⟩
  · rintro ⟨h2, hq⟩
    have hnorm_sq : 2 * w 0 ^ 2 / 2 ^ 2 + 6 * w 1 ^ 2 / 2 ^ 2 = 1 := by
      linarith
    have hz : ‖((√2 * w 0 / 2 : ℝ) + (√6 * w 1 / 2 : ℝ) * Complex.I : ℂ)‖ = 1 := by
      rw [Complex.norm_add_mul_I, div_pow, div_pow, mul_pow, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
      rw [hnorm_sq, Real.sqrt_one]
    obtain ⟨z, hz⟩ : ∃ z : Circle,
        (z : ℂ) = (√2 * w 0 / 2 : ℝ) + (√6 * w 1 / 2 : ℝ) * Complex.I :=
      ⟨⟨_, mem_sphere_zero_iff_norm.2 hz⟩, rfl⟩
    refine ⟨z, Subtype.ext ?_⟩
    have hq4 : 2 * w 0 ^ 2 + 6 * w 1 ^ 2 + w 2 ^ 2 = 4 := by rw [h2]; linarith
    rw [coe_unknot_apply, hc, hz, hq4]
    ext j
    fin_cases j <;> simp [ellipseCoord, h2] <;> ring

/-- An arc of the ellipse `w₀² + 3 w₁² = 2` in the plane `w₂ = 0` through a Conway point `x`,
reached at the parameter `(√2)⁻¹`. -/
private def ellipseArc (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[x 0 * (√2 * √(2 - 3 * t ^ 2)), x 1 * (√2 * t), 0]

/-- The arc of the ellipse is continuous. -/
private theorem continuous_ellipseArc (x : EuclideanSpace ℝ (Fin 3)) :
    Continuous (ellipseArc x) := by
  unfold ellipseArc
  fun_prop

/-- The parameter `(√2)⁻¹` of the Conway points squares to `1 / 2`. -/
private theorem sqrt_two_inv_sq : (√2)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt zero_le_two, one_div]

/-- The arc passes through its Conway point at the parameter `(√2)⁻¹`. -/
private theorem ellipseArc_sqrt_two_inv {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ conwayPoints) :
    ellipseArc x (√2)⁻¹ = x := by
  obtain ⟨-, -, h2⟩ := hx
  have h : √2 * √(2 - 3 * 2⁻¹) = 1 := by
    rw [← Real.sqrt_mul zero_le_two]
    norm_num
  ext j
  fin_cases j <;> simp [ellipseArc, h, h2]

/-- The arc lies on the ellipse, and its squared distance to the origin is `2 - 2 t²`. -/
private theorem ellipseArc_mem {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ conwayPoints) {t : ℝ}
    (ht : t ^ 2 ≤ 2 / 3) :
    unknotConwayBall (ellipseArc x t) ∈ range unknot ∧ ‖ellipseArc x t‖ ^ 2 = 2 - 2 * t ^ 2 := by
  obtain ⟨h0, h1, -⟩ := hx
  have hs : √(2 - 3 * t ^ 2) ^ 2 = 2 - 3 * t ^ 2 := Real.sq_sqrt (by linarith)
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  rw [unknotConwayBall_mem_range_unknot_iff, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [ellipseArc, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, true_and]
  refine ⟨?_, ?_⟩
  · rw [mul_pow, mul_pow, mul_pow, mul_pow, hs, h2, h0, h1]
    ring
  · rw [mul_pow, mul_pow, mul_pow, mul_pow, hs, h2, h0, h1]
    ring

/-- The ball chart meets the unknot in a Conway sphere in standard position for every half-turn: the
ellipse crosses the unit sphere at the four Conway points and is invariant under all three
half-turns. -/
private theorem isConwaySphere_unknotConwayBall (i : Fin 3) :
    IsConwaySphere unknot unknotConwayBall i := by
  have ha : 1 / 2 < (√2)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) (by positivity), Real.sqrt_lt' (by norm_num)]
    norm_num
  have hb : (√2)⁻¹ < 4 / 5 := by
    rw [inv_lt_comm₀ (by positivity) (by norm_num), Real.lt_sqrt (by norm_num)]
    norm_num
  have hsq : ∀ {t : ℝ}, 0 ≤ t → (t ^ 2 < 1 / 2 ↔ t < (√2)⁻¹) := fun ht ↦ by
    rw [← sqrt_two_inv_sq, sq_lt_sq₀ ht (by positivity)]
  have hlim : ∀ {x}, x ∈ conwayPoints → Tendsto (ellipseArc x) (𝓝 (√2)⁻¹) (𝓝 x) := fun {x} hx ↦ by
    have := (continuous_ellipseArc x).tendsto (√2)⁻¹
    rwa [ellipseArc_sqrt_two_inv hx] at this
  refine ⟨?_, fun x hx ↦ ?_, fun x hx ↦ ?_, ⟨1, one_pos, fun x _ _ ↦ ?_⟩⟩
  · ext w
    simp only [mem_inter_iff, mem_preimage, unknotConwayBall_mem_range_unknot_iff,
      mem_sphere_zero_iff_norm, mem_conwayPoints]
    rw [← sq_eq_sq₀ (norm_nonneg w) zero_le_one, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_three]
    constructor
    · rintro ⟨⟨h2, hq⟩, hn⟩
      rw [h2] at hn
      exact ⟨by linarith, by linarith, h2⟩
    · rintro ⟨h0, h1, h2⟩
      rw [h0, h1, h2]
      norm_num
  · -- Inside the ball: parameters just above `(√2)⁻¹`.
    refine mem_closure_of_tendsto (f := ellipseArc x) (b := 𝓝[>] (√2)⁻¹)
      ((hlim hx).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsGT hb] with t ht
    have ht0 : 0 ≤ t := (ha.trans ht.1).le.trans' (by norm_num)
    have ht2 : t ^ 2 ≤ 2 / 3 := by nlinarith [ht.2]
    obtain ⟨hK, hn⟩ := ellipseArc_mem hx ht2
    refine ⟨hK, ?_⟩
    rw [mem_ball_zero_iff, ← sq_lt_one_iff₀ (norm_nonneg _), hn]
    have : 1 / 2 < t ^ 2 := by
      rw [← sqrt_two_inv_sq]
      exact pow_lt_pow_left₀ ht.1 (by positivity) two_ne_zero
    linarith
  · -- Outside the ball: parameters just below `(√2)⁻¹`.
    refine mem_closure_of_tendsto (f := ellipseArc x) (b := 𝓝[<] (√2)⁻¹)
      ((hlim hx).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsLT ha] with t ht
    have ht0 : 0 ≤ t := ht.1.le.trans' (by norm_num)
    have ht2 : t ^ 2 < 1 / 2 := (hsq ht0).2 ht.2
    obtain ⟨hK, hn⟩ := ellipseArc_mem hx (t := t) (by linarith)
    refine ⟨hK, ?_⟩
    rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), hn]
    linarith
  · simp only [unknotConwayBall_mem_range_unknot_iff, conwayHalfTurn_apply]
    split_ifs <;> simp

/-- The unknot in `S³` has a Conway sphere in standard position for each half-turn. -/
theorem exists_isConwaySphere_unknot (i : Fin 3) :
    ∃ e : SmoothEmbedding (𝓡 3) (𝓡 3) ∞ (EuclideanSpace ℝ (Fin 3))
      (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1), IsConwaySphere unknot e i :=
  ⟨_, isConwaySphere_unknotConwayBall i⟩

/-- The unknot in `S³` is a Conway mutant of itself, along a Conway sphere whose whole tangle is
invariant under the half-turn. -/
theorem isConwayMutant_unknot_self : IsConwayMutant unknot unknot :=
  (isConwaySphere_unknotConwayBall 0).isConwayMutant_self fun x _ ↦ by
    simp only [unknotConwayBall_mem_range_unknot_iff, conwayHalfTurn_apply]
    split_ifs <;> simp

end Unknot

/-! ### Mutation and concordance -/

/-- **Mutation does not preserve concordance** (Kirk–Livingston). Some knot in `S³` is not smoothly
concordant to one of its Conway mutants.

Kirk and Livingston exhibit infinite families of knots that are not even topologically
concordant to their positive mutants, which implies this statement since smoothly concordant knots
are topologically concordant. This answers Kirby's problem 1.53. It is recorded as a proposition
and not proved. -/
def KirkLivingstonMutationTheorem : Prop :=
  ∃ K K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
    IsConwayMutant K K' ∧ ¬ SmoothEmbedding.Concordant K K'

/-- The Kirk–Livingston theorem spelled out: some knot in `S³` is not smoothly concordant to
one of its Conway mutants. -/
theorem kirkLivingstonMutationTheorem_iff :
    KirkLivingstonMutationTheorem ↔
      ∃ K K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
        IsConwayMutant K K' ∧ ¬ SmoothEmbedding.Concordant K K' :=
  Iff.rfl

/-- By the Kirk–Livingston theorem, smooth concordance of knots in `S³` is not invariant under
Conway mutation. -/
theorem KirkLivingstonMutationTheorem.not_forall_concordant (h : KirkLivingstonMutationTheorem) :
    ¬ ∀ K K' : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
      IsConwayMutant K K' → SmoothEmbedding.Concordant K K' := by
  obtain ⟨K, K', hKK', hc⟩ := h
  exact fun hall ↦ hc (hall K K' hKK')

end TauCeti
