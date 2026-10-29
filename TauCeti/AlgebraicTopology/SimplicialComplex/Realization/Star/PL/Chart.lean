/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.PL.Simplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# PL charts on open vertex stars with spherical links

A vertex with a combinatorial sphere as link has a Euclidean PL chart on its entire
open star. Its target is the interior of the coordinate simplex. Both the chart and
its inverse admit ambient PL formulas, suitable for checking transitions between
vertex-star charts. Neither the complex nor its vertex type needs to be finite.

The closed-star simplex model sends the apex coordinate to a positive multiple of
the minimum barycentric coordinate. Thus the open star corresponds exactly to the
interior of the simplex. Dropping the last barycentric coordinate gives Euclidean
coordinates; the inverse restores it as one minus the sum of the retained coordinates.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (pseudo-radial projection and vertex-star charts).

The construction uses `IsCombinatorialSphere.exists_homeomorph_closedStarRealization_top`
and `AbstractSimplicialComplex.realizationTopHomeomorphCoordinateSimplex`.
-/

public noncomputable section

open AbstractSimplicialComplex Set TauCeti

namespace PreAbstractSimplicialComplex

/-- Restrict a closed-star simplex model to its open interior and extend the resulting
chart to the weak realization. -/
private theorem exists_openStar_chart_of_simplexModel
    {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {m : ℕ}
    (e₀ : closedStarRealization K {v} ≃ₜ coordinateSimplex (Fin m))
    (hmem : ∀ x : closedStarRealization K {v}, x.1 ∈ openStarRealization K v ↔
      (e₀ x).1 ∈ interior (coordinateSimplex (Fin m))) :
    ∃ c : OpenPartialHomeomorph (Realization K) (Fin m → ℝ),
      c.source = openStarRealization K v ∧
      c.target = interior (coordinateSimplex (Fin m)) ∧
      ∀ x : openStarRealization K v,
        c x.1 = (e₀ ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩).1 := by
  let toStar (x : openStarRealization K v) : closedStarRealization K {v} :=
    ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩
  let ofInterior (y : interior (coordinateSimplex (Fin m))) :
      coordinateSimplex (Fin m) := ⟨y.1, interior_subset y.2⟩
  let e : openStarRealization K v ≃ₜ interior (coordinateSimplex (Fin m)) := {
    toFun x := ⟨(e₀ (toStar x)).1, (hmem (toStar x)).mp x.2⟩
    invFun y := ⟨(e₀.symm (ofInterior y)).1,
      (hmem _).mpr (by rw [e₀.apply_symm_apply]; exact y.2)⟩
    left_inv x := by simp [toStar, ofInterior]
    right_inv y := by simp [toStar, ofInterior]
    continuous_toFun := ((e₀.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_val).subtype_mk _
    continuous_invFun := ((e₀.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_val).subtype_mk _ }
  let : Nonempty (interior (coordinateSimplex (Fin m))) :=
    (nonempty_interior_coordinateSimplex _).to_subtype
  let j := (isOpen_interior.isOpenEmbedding_subtypeVal
    (s := interior (coordinateSimplex (Fin m)))).toOpenPartialHomeomorph
  let f := e.toOpenPartialHomeomorph.trans j
  let c := f.lift_openEmbedding (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal
  have hc (x : openStarRealization K v) : c x.1 = (e₀ (toStar x)).1 := by
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply,
      OpenPartialHomeomorph.trans_apply,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    rfl
  have hcs : c.source = openStarRealization K v := by
    simp only [c, f, j, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_self,
      image_univ, Subtype.range_coe]
  have hct : c.target = interior (coordinateSimplex (Fin m)) := by
    ext
    simp [c, f, j]
  exact ⟨c, hcs, hct, hc⟩

/-- A spherical vertex link gives a PL chart on the entire open star, with target the
interior of a full-dimensional simplex. The vertex maps to the barycentre. The ambient
formulas agree with the chart on its source and with its inverse on its target, so
callers can prove PL compatibility without unfolding the chart construction. -/
theorem IsCombinatorialSphere.exists_openPartialHomeomorph_openStar_isPL
    {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}
    (h : IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ c : OpenPartialHomeomorph (Realization K) (Fin (n + 1) → ℝ),
      c.source = openStarRealization K v ∧
      c.target = interior (coordinateSimplex (Fin (n + 1))) ∧
      c (vertex K v) = (fun _ => ((n : ℝ) + 2)⁻¹) ∧
      ∃ F : (ι → ℝ) → (Fin (n + 1) → ℝ),
      ∃ G : (Fin (n + 1) → ℝ) → (ι → ℝ),
        IsPLOn F (range fun x : closedStarRealization K {v} => (x.1.1 : ι → ℝ)) ∧
        IsPLOn G c.target ∧
        (∀ x ∈ c.source, F (x.1 : ι → ℝ) = c x) ∧
        (∀ y ∈ c.target, G y = ((c.symm y).1 : ι → ℝ)) := by
  obtain ⟨φ, hapex, hheight, F, G, hF, hG, hFφ, hGφ⟩ :=
    h.exists_homeomorph_closedStarRealization_top
  let r := realizationTopHomeomorphCoordinateSimplex (n + 1)
  let e₀ := φ.trans r
  -- The height formula identifies the open star with the simplex interior.
  have hmem (x : closedStarRealization K {v}) :
      x.1 ∈ openStarRealization K v ↔
        (e₀ x).1 ∈ interior (coordinateSimplex (Fin (n + 1))) := by
    have hs := Realization.sum_eq_one _ (φ x)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at hs
    have hpos : 0 < (n : ℝ) + 2 := by positivity
    rw [mem_openStarRealization, ← hheight x, mul_pos_iff_of_pos_left hpos,
      Finset.lt_inf'_iff]
    simp only [Finset.mem_univ, forall_const]
    rw [interior_coordinateSimplex]
    simp only [mem_ofPred_eq, e₀, r, Homeomorph.trans_apply,
      realizationTopHomeomorphCoordinateSimplex_apply]
    constructor
    · intro hx
      exact ⟨fun i => hx i.castSucc, by linarith [hx (Fin.last (n + 1))]⟩
    · rintro ⟨hx, hsum⟩ i
      exact Fin.lastCases (by linarith) hx i
  obtain ⟨c, hcs, hct, hc⟩ := exists_openStar_chart_of_simplexModel e₀ hmem
  let toStar (x : openStarRealization K v) : closedStarRealization K {v} :=
    ⟨x.1, K.openStarRealization_subset_closedStarRealization v x.2⟩
  have hc' (x : openStarRealization K v) : c x.1 = (e₀ (toStar x)).1 := hc x
  -- Drop one barycentric coordinate; its affine inverse restores the missing mass.
  let A : (Fin (n + 2) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.castSucc
  let B₀ : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 2) → ℝ) :=
    ContinuousLinearMap.pi (Fin.lastCases (-(∑ i, ContinuousLinearMap.proj i))
      (fun i => ContinuousLinearMap.proj i))
  let B : (Fin (n + 1) → ℝ) →ᴬ[ℝ] (Fin (n + 2) → ℝ) :=
    B₀.toContinuousAffineMap + ContinuousAffineMap.const ℝ (Fin (n + 1) → ℝ)
      (Pi.single (Fin.last (n + 1)) 1 : Fin (n + 2) → ℝ)
  have hB (y : coordinateSimplex (Fin (n + 1))) :
      B y.1 = ((r.symm y).1 : Fin (n + 2) → ℝ) := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [B, B₀, r, sub_eq_add_neg, add_comm]
    · simp [B, B₀, r]
  -- Read the inverse on its target through the closed-star inverse formula.
  have hGB (y : c.target) : G (B y.1) = ((c.symm y.1).1 : ι → ℝ) := by
    have hx : c.symm y.1 ∈ openStarRealization K v := by
      rw [← hcs]
      exact c.map_target y.2
    let x : openStarRealization K v := ⟨c.symm y.1, hx⟩
    have hcx : c x.1 = y.1 := c.right_inv y.2
    have hBφ : B y.1 = ((φ (toStar x)).1 : Fin (n + 2) → ℝ) := by
      rw [← hcx, hc', hB]
      simp [e₀]
    rw [hBφ, hGφ]
  refine ⟨c, hcs, hct, ?_, A ∘ F, G ∘ B, ?_, ?_, ?_, ?_⟩
  · rw [hc' ⟨vertex K v, by simp [mem_openStarRealization]⟩]
    funext i
    have ha : toStar ⟨vertex K v, by simp [mem_openStarRealization]⟩ = starApex K v :=
      Subtype.ext (starApex_val K v).symm
    simpa only [e₀, r, Homeomorph.trans_apply, ha,
      realizationTopHomeomorphCoordinateSimplex_apply] using congrFun hapex i.castSucc
  · exact (isPLOn_continuousAffineMap A.toContinuousAffineMap univ).comp hF
      (mapsTo_univ _ _)
  · refine hG.comp (isPLOn_continuousAffineMap B c.target) ?_
    intro y hy
    rw [hct] at hy
    exact ⟨r.symm ⟨y, interior_subset hy⟩, (hB _).symm⟩
  · intro x hx
    rw [hcs] at hx
    rw [Function.comp_apply, hFφ (toStar ⟨x, hx⟩), hc' ⟨x, hx⟩]
    funext i
    simp [e₀, r, A]
  · intro y hy
    exact hGB ⟨y, hy⟩

end PreAbstractSimplicialComplex
