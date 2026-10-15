/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import TauCeti.Analysis.Convex.CoordinateSimplex
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# A simplex and its boundary as a ball and its sphere

The weak realization of the standard `n`-simplex is homeomorphic to the Euclidean closed
`n`-ball. The same homeomorphism takes exactly the proper faces to the unit sphere, so it
identifies the pair consisting of a simplex and its boundary with the ball and sphere pair.
This supplies compatible geometric models for combinatorial balls and their boundaries.
The same holds for the sup-norm closed ball used by Mathlib's classical CW complexes.
Dimension zero is included: the simplex and ball are singletons and their boundaries empty.
An injective vertex enumeration gives the same ball model for every closed face of a complex;
its barycentric support detects the open ball and boundary sphere.

Dropping the last barycentric coordinate gives an explicit homeomorphism to the coordinate
simplex. The omitted coordinate is one minus the sum of the others. The subsequent ball
identification uses Mathlib's convex-body gauge rescaling through
`TauCeti.exists_homeomorph_coordinateSimplex`. The first comparison reuses
`realizationTopHomeomorphStdSimplex` and Mathlib's `Convexity.StdSimplex`.

Reference: C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 2 (simplices and polyhedra).
-/

public section

noncomputable section

open Set Metric TauCeti

namespace AbstractSimplicialComplex

private def topToCoordinateSimplex (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    coordinateSimplex (Fin n) := by
  let y : Fin n → ℝ := fun i => x.1 i.castSucc
  have hsum : (∑ i, y i) + x.1 (Fin.last n) = 1 := by
    have h := Realization.sum_eq_one _ x
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
    exact h
  refine ⟨y, (mem_coordinateSimplex _ _).mpr ⟨fun i => Realization.nonneg _ x i.castSucc, ?_⟩⟩
  have := Realization.nonneg _ x (Fin.last n)
  linarith

private theorem topToCoordinateSimplex_apply (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) (i : Fin n) :
    (topToCoordinateSimplex n x).1 i = x.1 i.castSucc := (rfl)

private def coordinateSimplexToTop (n : ℕ) (y : coordinateSimplex (Fin n)) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) := by
  have hy := (mem_coordinateSimplex _ _).mp y.2
  let z : Fin (n + 1) →₀ ℝ := Finsupp.equivFunOnFinite.symm
    (Fin.snoc y.1 (1 - ∑ i, y.1 i))
  refine (realizationTopHomeomorphStdSimplex (ι := Fin (n + 1))).symm ⟨z, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [z] using sub_nonneg.mpr hy.2
    · simpa [z] using hy.1 j
  · simp [z, Finsupp.sum_fintype, Fin.sum_univ_castSucc]

private theorem coordinateSimplexToTop_castSucc (n : ℕ) (y : coordinateSimplex (Fin n))
    (i : Fin n) : (coordinateSimplexToTop n y).1 i.castSucc = y.1 i := by
  simp [coordinateSimplexToTop, realizationTopHomeomorphStdSimplex_symm_apply_val]

private theorem coordinateSimplexToTop_last (n : ℕ) (y : coordinateSimplex (Fin n)) :
    (coordinateSimplexToTop n y).1 (Fin.last n) = 1 - ∑ i, y.1 i := by
  simp [coordinateSimplexToTop, realizationTopHomeomorphStdSimplex_symm_apply_val]

/-- Dropping the last barycentric coordinate identifies the weak realization of a standard
`n`-simplex with the full-dimensional coordinate simplex. -/
def realizationTopHomeomorphCoordinateSimplex (n : ℕ) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃ₜ coordinateSimplex (Fin n) := by
  let e : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃
      coordinateSimplex (Fin n) := {
    toFun := topToCoordinateSimplex n
    invFun := coordinateSimplexToTop n
    left_inv x := by
      apply Subtype.ext
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [coordinateSimplexToTop_last]
        have h := Realization.sum_eq_one _ x
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
        simp only [topToCoordinateSimplex_apply]
        linarith
      · simp only [coordinateSimplexToTop_castSucc, topToCoordinateSimplex_apply]
    right_inv y := by
      apply Subtype.ext
      funext i
      simp only [topToCoordinateSimplex_apply, coordinateSimplexToTop_castSucc] }
  have hc : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (continuous_apply i.castSucc).comp (continuous_realization_coe _)
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

/-- The coordinate-simplex comparison reads the first barycentric coordinates. -/
@[simp]
theorem realizationTopHomeomorphCoordinateSimplex_apply (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) (i : Fin n) :
    (realizationTopHomeomorphCoordinateSimplex n x).1 i = x.1 i.castSucc := (rfl)

/-- The inverse comparison restores the last coordinate as the missing mass. -/
@[simp]
theorem realizationTopHomeomorphCoordinateSimplex_symm_last (n : ℕ)
    (y : coordinateSimplex (Fin n)) :
    ((realizationTopHomeomorphCoordinateSimplex n).symm y).1 (Fin.last n) =
      1 - ∑ i, y.1 i :=
  coordinateSimplexToTop_last n y

/-- In the standard `n`-simplex, the open star of the last vertex is described in the
dropped barycentric coordinates by the strict sum inequality. -/
theorem mem_openStarRealization_top_last_iff_sum_lt_one (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    x ∈ openStarRealization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))
      (Fin.last n) ↔
      ∑ i : Fin n, (realizationTopHomeomorphCoordinateSimplex n x).1 i < 1 := by
  have h := Realization.sum_eq_one
    (⊤ : AbstractSimplicialComplex (Fin (n + 1))) x
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
  have hsum : (∑ i : Fin n, (realizationTopHomeomorphCoordinateSimplex n x).1 i) +
      x.1 (Fin.last n) = 1 := by
    simpa only [realizationTopHomeomorphCoordinateSimplex_apply] using h
  rw [mem_openStarRealization]
  constructor <;> intro hx <;> linarith

/-- The coordinate homeomorphism maps the open star of the last vertex of the standard
`n`-simplex onto the points of the coordinate simplex whose coordinate sum is less than one. -/
theorem image_openStarRealization_top_last (n : ℕ) :
    realizationTopHomeomorphCoordinateSimplex n ''
        openStarRealization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) (Fin.last n) =
      {y : coordinateSimplex (Fin n) | ∑ i, y.1 i < 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_openStarRealization_top_last_iff_sum_lt_one n x).mp hx
  · intro hy
    refine ⟨(realizationTopHomeomorphCoordinateSimplex n).symm y, ?_, ?_⟩
    · rw [mem_openStarRealization, realizationTopHomeomorphCoordinateSimplex_symm_last]
      simp only [Set.mem_ofPred_eq] at hy
      linarith
    · simp

/-- The inverse comparison preserves the retained coordinates. -/
@[simp]
theorem realizationTopHomeomorphCoordinateSimplex_symm_castSucc (n : ℕ)
    (y : coordinateSimplex (Fin n)) (i : Fin n) :
    ((realizationTopHomeomorphCoordinateSimplex n).symm y).1 i.castSucc = y.1 i :=
  coordinateSimplexToTop_castSucc n y i

/-- A simplex point maps to the geometric frontier exactly when its support is a proper
face. This includes the empty boundary of the zero-simplex. -/
@[simp 1100]
theorem realizationTopHomeomorphCoordinateSimplex_mem_frontier_iff (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    (realizationTopHomeomorphCoordinateSimplex n x).1 ∈ frontier (coordinateSimplex (Fin n)) ↔
      x.1.support ≠ Finset.univ := by
  rw [mem_frontier_coordinateSimplex]
  rw [iff_true_intro ((mem_coordinateSimplex _ _).mp
    (realizationTopHomeomorphCoordinateSimplex n x).2), true_and]
  simp only [realizationTopHomeomorphCoordinateSimplex_apply]
  have hsum : (∑ i : Fin n, x.1 i.castSucc) + x.1 (Fin.last n) = 1 := by
    have h := Realization.sum_eq_one _ x
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at h
  have hmissing : x.1.support ≠ Finset.univ ↔ ∃ i, x.1 i = 0 := by
    simp [Finset.eq_univ_iff_forall, Finsupp.mem_support_iff]
  rw [hmissing]
  constructor
  · rintro (⟨i, hi⟩ | hs)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, by linarith⟩
  · rintro ⟨i, hi⟩
    refine Fin.lastCases ?_ (fun j hj => Or.inl ⟨j, hj⟩) i hi
    intro hl
    exact Or.inr (by linarith)

/-- The weak realization of the standard `n`-simplex is homeomorphic to the Euclidean unit
closed `n`-ball. Its proper-face boundary is taken to the sphere. -/
def realizationTopHomeomorphClosedBall (n : ℕ) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  let h := Classical.choose (exists_homeomorph_coordinateSimplex (Fin n))
  (realizationTopHomeomorphCoordinateSimplex n).trans
    ((h.image (coordinateSimplex (Fin n))).trans
      (Homeomorph.setCongr (Classical.choose_spec
        (exists_homeomorph_coordinateSimplex (Fin n))).1))

/-- Under the simplex-to-ball homeomorphism, exactly the proper faces land on the sphere. -/
@[simp]
theorem realizationTopHomeomorphClosedBall_norm_eq_one_iff (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    ‖(realizationTopHomeomorphClosedBall n x).1‖ = 1 ↔
      x.1.support ≠ Finset.univ := by
  rw [← mem_sphere_zero_iff_norm]
  let h := Classical.choose (exists_homeomorph_coordinateSimplex (Fin n))
  have hfr : h '' frontier (coordinateSimplex (Fin n)) =
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    (Classical.choose_spec (exists_homeomorph_coordinateSimplex (Fin n))).2.2
  have he : (realizationTopHomeomorphClosedBall n x).1 =
      h (realizationTopHomeomorphCoordinateSimplex n x).1 := (rfl)
  rw [he, ← hfr]
  simpa only [h.injective.mem_set_image] using
    realizationTopHomeomorphCoordinateSimplex_mem_frontier_iff n x

/-- The weak realization of the standard `n`-simplex is homeomorphic to the closed unit ball
of `Fin n → ℝ` with the sup norm, the domain of Mathlib's classical CW characteristic maps.
Its proper-face boundary is taken to the sphere. -/
def realizationTopHomeomorphPiClosedBall (n : ℕ) :
    Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1))) ≃ₜ
      closedBall (0 : Fin n → ℝ) 1 :=
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  (realizationTopHomeomorphClosedBall n).trans
    ((L.unitBallHomeomorph.image _).trans
      (Homeomorph.setCongr L.image_unitBallHomeomorph_closedBall))

/-- Under the simplex-to-sup-norm-ball homeomorphism, exactly the proper faces land on the
sphere. -/
@[simp]
theorem realizationTopHomeomorphPiClosedBall_norm_eq_one_iff (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    ‖(realizationTopHomeomorphPiClosedBall n x).1‖ = 1 ↔
      x.1.support ≠ Finset.univ := by
  rw [← realizationTopHomeomorphClosedBall_norm_eq_one_iff]
  exact ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff _

section EnumeratedFace

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [DecidableEq ι] (K : AbstractSimplicialComplex ι) {n : ℕ}
  (f : Fin (n + 1) ↪ ι) (hf : Finset.univ.image f ∈ K)

/-- The sup-norm closed unit ball parametrizes the closed simplex on an explicitly
enumerated face. Its boundary corresponds to the proper faces. -/
def simplexClosedBallHomeomorph :
    closedBall (0 : Fin n → ℝ) 1 ≃ₜ
      {x : Realization K // x.1.support ⊆ Finset.univ.image f} :=
  (realizationTopHomeomorphPiClosedBall n).symm.trans (realizationTopHomeomorphFace K f hf)

/-- Barycentric coordinates are obtained from the fixed standard ball model by pushing
its coordinate vector along the vertex enumeration. -/
theorem simplexClosedBallHomeomorph_val (x : closedBall (0 : Fin n → ℝ) 1) :
    (simplexClosedBallHomeomorph K f hf x).1.1 =
      Finsupp.mapDomain f ((realizationTopHomeomorphPiClosedBall n).symm x).1 :=
  realizationTopHomeomorphFace_val K f hf _

/-- The boundary sphere corresponds exactly to barycentric support smaller than the face. -/
theorem simplexClosedBallHomeomorph_support_ne_iff
    (x : closedBall (0 : Fin n → ℝ) 1) :
    (simplexClosedBallHomeomorph K f hf x).1.1.support ≠ Finset.univ.image f ↔ ‖x.1‖ = 1 := by
  rw [simplexClosedBallHomeomorph_val, Finsupp.mapDomain_support_of_injective f.injective,
    ne_eq, Finset.image_inj f.injective, ← ne_eq,
    ← realizationTopHomeomorphPiClosedBall_norm_eq_one_iff, Homeomorph.apply_symm_apply]

/-- The open ball corresponds exactly to the points with full barycentric support. -/
@[simp]
theorem simplexClosedBallHomeomorph_support_eq_iff
    (x : closedBall (0 : Fin n → ℝ) 1) :
    (simplexClosedBallHomeomorph K f hf x).1.1.support = Finset.univ.image f ↔ ‖x.1‖ < 1 := by
  have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  have h := simplexClosedBallHomeomorph_support_ne_iff K f hf x
  grind

/-- The inverse closed-simplex homeomorphism lands in the open ball exactly at the points
with full barycentric support. -/
theorem norm_simplexClosedBallHomeomorph_symm_lt_one_iff
    (y : {x : Realization K // x.1.support ⊆ Finset.univ.image f}) :
    ‖((simplexClosedBallHomeomorph K f hf).symm y).1‖ < 1 ↔
      y.1.1.support = Finset.univ.image f := by
  rw [← simplexClosedBallHomeomorph_support_eq_iff K f hf, Homeomorph.apply_symm_apply]

/-- The inverse closed-simplex homeomorphism lands on the sphere exactly at the points of
proper faces. -/
theorem norm_simplexClosedBallHomeomorph_symm_eq_one_iff
    (y : {x : Realization K // x.1.support ⊆ Finset.univ.image f}) :
    ‖((simplexClosedBallHomeomorph K f hf).symm y).1‖ = 1 ↔
      y.1.1.support ⊂ Finset.univ.image f := by
  rw [← simplexClosedBallHomeomorph_support_ne_iff K f hf, Homeomorph.apply_symm_apply,
    Finset.ssubset_iff_subset_ne, and_iff_right y.2]

end EnumeratedFace

end AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

open AbstractSimplicialComplex

variable {ι : Type*} {A : AbstractSimplicialComplex ι} {n : ℕ}

/-- The polyhedron of a simplex with `n + 1` vertices is homeomorphic to the Euclidean closed
`n`-ball, inside any ambient realization containing it. -/
theorem nonempty_homeomorph_simplex_closedBall {V : Finset ι}
    (hV : V.card = n + 1) (hA : simplex V ≤ A.toPreAbstractSimplicialComplex) :
    Nonempty ({x : Realization A // x.1.support ∈ simplex V} ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  classical
  let P := simplex (Finset.univ : Finset (Fin (n + 1)))
  have hP : P = (⊤ : AbstractSimplicialComplex (Fin (n + 1))).toPreAbstractSimplicialComplex := by
    simp only [P, simplex_univ, AbstractSimplicialComplex.top_toPreAbstractSimplicialComplex]
  obtain ⟨r⟩ := nonempty_finsetRelabelingHomeomorph hV (fun f himage => by
      rw [map_simplex, himage]) hP hA
  exact ⟨r.trans (AbstractSimplicialComplex.realizationTopHomeomorphClosedBall n)⟩

end PreAbstractSimplicialComplex
