/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Geometry
public import TauCeti.AlgebraicTopology.SimplicialComplex.ElementaryCollapse
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Homotopy

/-!
# Elementary collapse as a strong deformation retraction

The polyhedron of a complex strongly deformation retracts onto the polyhedron left by an
elementary collapse. The deformation of the upper simplex of the free pair extends by the
identity on the retained complex. Freeness makes the two deformations agree on every overlap.

Polyhedra are actual support-defined subsets of an ambient weak realization: a deleted free
vertex is absent from the target. No finiteness or local finiteness is required. Joint
continuity is checked on closed simplex cylinders, rather than separately in time and space.
This supplies the geometric interpretation of the elementary simplicial collapse relation.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapter 3 (elementary collapse and its geometric deformation).
* `PreAbstractSimplicialComplex.exists_strong_deformation_retraction_simplex_deletion`:
  the local simplex deformation extended here.
-/

public noncomputable section

open Set AbstractSimplicialComplex

attribute [local instance] Classical.decEq

namespace PreAbstractSimplicialComplex

variable {ι : Type*} {K L : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {σ τ : Finset ι}

/-- The polyhedron of a free-pair deletion is a strong deformation retract of the original
polyhedron, inside any containing weak realization. The homotopy fixes the entire retained
polyhedron at every time, including when the free face is a vertex. -/
theorem IsFreePair.exists_strong_deformation_retraction (h : IsFreePair K σ τ)
    (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    let X := {x : Realization A // x.1.support ∈ K}
    let S : Set X := {x | x.1.1.support ∈ deletion K σ}
    ∃ r : C(X, S), (∀ x : S, r x = x) ∧ Nonempty
      ((ContinuousMap.id X).HomotopyRel ((ContinuousMap.subtypeVal S).comp r) S) := by
  classical
  let X := {x : Realization A // x.1.support ∈ K}
  let S : Set X := {x | x.1.1.support ∈ deletion K σ}
  let T : Set (StandardSimplex τ) :=
    {x | x.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (deletion K σ)).space}
  obtain ⟨rτ, _, ⟨Hτ⟩⟩ :=
    exists_strong_deformation_retraction_simplex_deletion K h.upper_mem h.covBy
      (K.isRelLowerSet_faces.prop_of_mem h.lower_mem)
  let iτ : C(StandardSimplex τ, X) :=
    ⟨fun x => ⟨faceInclusion A ⟨τ, hK h.upper_mem⟩ x,
      support_faceInclusion_mem hK h.upper_mem x⟩,
      (continuous_faceInclusion A ⟨τ, hK h.upper_mem⟩).subtype_mk
        (support_faceInclusion_mem hK h.upper_mem)⟩
  -- Read a point supported on the upper face as a point of its closed simplex.
  let toτ (x : X) (hx : x.1.1.support ⊆ τ) : StandardSimplex τ := ⟨x.1.1, by
    rw [Finset.coe_image, mem_standardSimplex_iff]
    exact ⟨Realization.nonneg A x.1, Realization.sum_eq_one A x.1, hx⟩⟩
  have hiτ (x : X) (hx : x.1.1.support ⊆ τ) : iτ (toτ x hx) = x := by
    apply Subtype.ext
    exact Subtype.ext (faceInclusion_val _ _ _)
  have hT (x : StandardSimplex τ) : x ∈ T ↔ x.1.support ∈ deletion K σ := by
    simp only [T, mem_ofPred_eq, Geometry.SimplicialComplex.mem_space_onFinsupp_iff,
      StandardSimplex.nonneg, StandardSimplex.sum_eq_one, implies_true, true_and]
  let F (p : unitInterval × X) : X :=
    if hx : p.2.1.1.support ⊆ τ then iτ (Hτ (p.1, toτ p.2 hx)) else p.2
  have hFτ (t : unitInterval) (x : X) (hx : x.1.1.support ⊆ τ) :
      F (t, x) = iτ (Hτ (t, toτ x hx)) := by
    simp only [F, dite_eq_left hx]
  have hfix (t : unitInterval) (x : X) (hx : x ∈ S) : F (t, x) = x := by
    by_cases hxt : x.1.1.support ⊆ τ
    · rw [hFτ t x hxt, Hτ.eq_fst t ((hT (toτ x hxt)).mpr hx), ContinuousMap.id_apply]
      exact hiτ x hxt
    · simp only [F, dite_eq_right hxt]
  -- Each simplex is either contained in the upper face or entirely retained.
  -- In the latter case the extension is the identity; in the former it factors through Hτ.
  have hFc : Continuous F := by
    apply continuous_prod_subtype_iff_faceInclusion hK |>.mpr
    intro ω hω
    let iω (x : StandardSimplex ω) : X :=
      ⟨faceInclusion A ⟨ω, hK hω⟩ x, support_faceInclusion_mem hK hω x⟩
    by_cases hσω : σ ⊆ ω
    · have hωτ : ω ⊆ τ := by
        rcases h.eq_lower_or_eq_upper hω hσω with rfl | rfl
        · exact h.lower_ssubset_upper.subset
        · exact Finset.Subset.rfl
      let j : StandardSimplex ω → StandardSimplex τ :=
        Set.inclusion (convexHull_mono
          (Finset.coe_subset.mpr (Finset.image_mono _ hωτ)))
      have hj : Continuous j := by
        apply continuous_induced_rng.mpr
        exact continuous_induced_dom
      apply (iτ.continuous.comp
        (Hτ.continuous.comp (continuous_id.prodMap hj))).congr
      intro p
      have hp : (iω p.2).1.1.support ⊆ τ := by
        simpa only [iω, faceInclusion_val] using
          (StandardSimplex.support_subset p.2).trans hωτ
      have he : j p.2 = toτ (iω p.2) hp :=
        Subtype.ext (faceInclusion_val A ⟨ω, hK hω⟩ p.2).symm
      rw [hFτ p.1 (iω p.2) hp]
      simp only [Function.comp_apply, Prod.map, id_eq, he]
    · apply ((continuous_faceInclusion A ⟨ω, hK hω⟩).subtype_mk
        (support_faceInclusion_mem hK hω) |>.comp continuous_snd).congr
      intro p
      apply (hfix p.1 (iω p.2) ?_).symm
      exact support_faceInclusion_mem (deletion_le.trans hK)
        (mem_deletion.mpr ⟨hω, hσω⟩) p.2
  have hzero (x : X) : F (0, x) = x := by
    by_cases hx : x.1.1.support ⊆ τ
    · rw [hFτ 0 x hx, Hτ.apply_zero, ContinuousMap.id_apply]
      exact hiτ x hx
    · simp only [F, dite_eq_right hx]
  have hone (x : X) : F (1, x) ∈ S := by
    by_cases hx : x.1.1.support ⊆ τ
    · rw [hFτ 1 x hx, Hτ.apply_one]
      simpa only [S, iτ, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
        ContinuousMap.subtypeVal_apply, mem_ofPred_eq, faceInclusion_val] using
          (hT (rτ (toτ x hx))).mp (rτ (toτ x hx)).2
    · have hσx : ¬ σ ⊆ x.1.1.support := by
        intro hσx
        rcases h.eq_lower_or_eq_upper x.2 hσx with he | he
        · exact hx (he ▸ h.lower_ssubset_upper.subset)
        · exact hx (he ▸ Finset.Subset.rfl)
      simpa only [F, dite_eq_right hx, S, mem_ofPred_eq] using
        (mem_deletion.mpr ⟨x.2, hσx⟩)
  -- The time-one map lands in the retained polyhedron, so corestrict it to the retraction.
  let r : C(X, S) := ⟨fun x => ⟨F (1, x), hone x⟩,
    (hFc.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  refine ⟨r, fun x => Subtype.ext (hfix 1 x.1 x.2), ⟨?_⟩⟩
  exact
    { toFun := F
      continuous_toFun := hFc
      map_zero_left := hzero
      map_one_left := fun _ => rfl
      prop' := hfix }

/-- Every elementary simplicial collapse gives a strong deformation retraction onto the
target polyhedron. The subsets carry the topology inherited from any ambient weak realization;
no finiteness hypothesis is needed. -/
theorem ElementaryCollapsesTo.exists_strong_deformation_retraction
    (h : ElementaryCollapsesTo K L) (hK : K ≤ A.toPreAbstractSimplicialComplex) :
    let X := {x : Realization A // x.1.support ∈ K}
    let S : Set X := {x | x.1.1.support ∈ L}
    ∃ r : C(X, S), (∀ x : S, r x = x) ∧ Nonempty
      ((ContinuousMap.id X).HomotopyRel ((ContinuousMap.subtypeVal S).comp r) S) := by
  obtain ⟨σ, τ, hfree, _, hL⟩ := h.exists_pair
  have he : L = deletion K σ := by
    apply SetLike.ext
    intro ω
    rw [hL, mem_deletion]
    exact (mem_deletion_of_isFreePair K hfree).symm
  subst L
  exact hfree.exists_strong_deformation_retraction hK

end PreAbstractSimplicialComplex
