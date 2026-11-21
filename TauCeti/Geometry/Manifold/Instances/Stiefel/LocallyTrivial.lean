/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Reflection
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Fiber
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Homogeneous
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Local triviality of the projection of a Stiefel manifold to the first vector

Let `E` be a real inner product space with unit sphere `Sⁿ`. An orthonormal `(k + 1)`-frame
`(p, u₁, …, u_k)` of `E` is a point `p` of the sphere together with an orthonormal `k`-frame of the
tangent space `p^⊥`, so the projection `π : V_{k+1}(E) → Sⁿ` to the first vector
(`TauCeti.stiefelProj E (k + 1) 0`) has fibre `V_k(p^⊥)` over `p`
(`TauCeti.range_stiefelFrameIncl`). This file shows that `π` is locally trivial, with fibre the
Stiefel manifold `V_k(F)` of any real inner product space `F` of dimension `n`
(`TauCeti.exists_trivialization_stiefelProj_zero_of_finrank_add_one_eq`), by explicit charts.
This refines `TauCeti.exists_trivialization_stiefelProj_zero`, with fibre `V_k(ℝⁿ)`, from which
`π` is a Serre fibration and a Hurewicz fibration
(`TauCeti.TopCat.mem_serreFibrations_stiefelProj_zero`,
`TauCeti.isHurewiczFibration_stiefelProj_zero`). For `k = 1` this is the unit tangent bundle of
the sphere. For `k = 2` it is the space of orthonormal triples `(p, u, v)` parametrizing the
round two-spheres of `Sⁿ` through `p` tangent to `u` and `v` (`TauCeti.stiefelSphereFamily`), and
this fibration over `Sⁿ` is the parameter space of the fibered family of two-spheres of the sphere
of Barraud–Damian–Humilière–Oancea (Definition 6.14 and Example 6.16).

The chart around a point `p₀` (`TauCeti.stiefelProjTrivialization`) is defined over the complement
of the antipode `-p₀`. For `p ≠ -p₀`, the rotation `R_p = TauCeti.pairRotation p₀ p` in the plane
of `p₀` and `p`, the product of the reflections in the hyperplanes orthogonal to `p₀` and to
`p₀ + p`, is a linear isometry of `E` carrying `p₀` to `p`, and it depends continuously on `p`. So
`R_p` carries the frames of `p₀^⊥` to the frames of `p^⊥`, and a linear isometry
`φ : F ≃ p₀^⊥` reads the frames of `p₀^⊥` as frames of `F`. The chart sends a frame
`(p, u₁, …, u_k)` with `p ≠ -p₀` to `(p, (φ⁻¹ (R_p⁻¹ uᵢ))ᵢ)`, and its inverse sends `(p, w)` to
`(p, (R_p (φ wᵢ))ᵢ)`. At `p₀` itself `R_{p₀}` is the identity, so for `F = p₀^⊥` and `φ` the
identity the inverse chart restricts over `p₀` to the inclusion of the fibre
(`TauCeti.stiefelProjTrivialization_symm_apply_self`).

## Main declarations

* `TauCeti.stiefelProjTrivialization`: the chart of the projection to the first vector over the
  complement of the antipode of a point, with fibre `V_k(F)`.
* `TauCeti.exists_trivialization_stiefelProj_zero_of_finrank_add_one_eq`: the projection to the
  first vector is locally trivial, with fibre the Stiefel manifold of any space of one dimension
  less.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7 (Stiefel
  manifolds as bundles over spheres).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14 and
  Example 6.16.
-/

public section

noncomputable section

open Bundle Metric Module Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {k : ℕ}

/-- The rotation carrying `p₀` to a point `p` of the unit sphere carries `p₀` to `p`. -/
private theorem pairRotation_apply_sphere (p₀ p : sphere (0 : E) 1) :
    pairRotation (p₀ : E) p p₀ = p :=
  pairRotation_apply_self (by rw [norm_eq_of_mem_sphere, norm_eq_of_mem_sphere])

omit [InnerProductSpace ℝ E] in
/-- A point of the unit sphere other than the antipode of `p₀` does not cancel `p₀`, so the
rotation carrying `p₀` to it depends continuously on it. -/
private theorem add_ne_zero_of_ne_neg_sphere {p₀ p : sphere (0 : E) 1} (h : p ≠ -p₀) :
    (p₀ : E) + p ≠ 0 :=
  fun h' => h (Subtype.ext (by simpa using eq_neg_of_add_eq_zero_right h'))

/-- The vectors after the first of an orthonormal frame `(p, u₁, …, u_k)`, rotated back from `p` to
`p₀`, lie in `p₀^⊥`. -/
private theorem pairRotation_symm_apply_mem (p₀ : sphere (0 : E) 1) (v : stiefel E (k + 1))
    (i : Fin k) :
    (pairRotation (p₀ : E) (stiefelProj E (k + 1) 0 v)).symm (v.val i.succ) ∈
      (ℝ ∙ (p₀ : E))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    ← LinearIsometryEquiv.inner_map_eq_flip, pairRotation_apply_sphere, coe_stiefelProj]
  exact (mem_stiefel_iff.1 v.property).inner_eq_zero (Fin.succ_ne_zero i).symm

/-- The fibre coordinate of the chart `TauCeti.stiefelProjTrivialization`: the vectors after the
first of an orthonormal frame `(p, u₁, …, u_k)`, rotated back from `p` to `p₀` and read in `F`
through `φ`. -/
private def fiberFrame (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ)
    (v : stiefel E (k + 1)) : stiefel F k :=
  ⟨fun i => φ.symm ⟨_, pairRotation_symm_apply_mem p₀ v i⟩,
    mem_stiefel_iff.2 <|
      ((((mem_stiefel_iff.1 v.property).comp _ (Fin.succ_injective k)).comp_linearIsometryEquiv
        (pairRotation (p₀ : E) (stiefelProj E (k + 1) 0 v)).symm).codRestrict _
          (pairRotation_symm_apply_mem p₀ v)).comp_linearIsometryEquiv φ.symm⟩

/-- The inverse of the chart `TauCeti.stiefelProjTrivialization`: a point `p` of the sphere and a
frame `w` of `F`, read in `p₀^⊥` through `φ` and rotated from `p₀` to `p`, give the orthonormal
frame `(p, R_p (φ w₁), …, R_p (φ w_k))`. -/
private def baseFrame (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ)
    (q : sphere (0 : E) 1 × stiefel F k) : stiefel E (k + 1) :=
  pairRotation (p₀ : E) q.1 • stiefelFrameIncl p₀ k
    ⟨fun i => φ (q.2.val i),
      mem_stiefel_iff.2 ((mem_stiefel_iff.1 q.2.property).comp_linearIsometryEquiv φ)⟩

private theorem coe_baseFrame (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ)
    (q : sphere (0 : E) 1 × stiefel F k) :
    (baseFrame p₀ φ q : Fin (k + 1) → E) =
      Matrix.vecCons (q.1 : E) fun i => pairRotation (p₀ : E) q.1 (φ (q.2.val i)) := by
  refine funext (Fin.cases ?_ fun i => ?_)
  · simp [baseFrame, pairRotation_apply_sphere]
  · simp [baseFrame]

private theorem stiefelProj_baseFrame (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ)
    (q : sphere (0 : E) 1 × stiefel F k) :
    stiefelProj E (k + 1) 0 (baseFrame p₀ φ q) = q.1 := by
  rw [baseFrame, stiefelProj_smul, stiefelProj_zero_stiefelFrameIncl]
  exact Subtype.ext ((LinearIsometryEquiv.coe_smul_unitSphere _ _).trans
    (pairRotation_apply_sphere p₀ q.1))

private theorem baseFrame_fiberFrame (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ)
    (v : stiefel E (k + 1)) :
    baseFrame p₀ φ (stiefelProj E (k + 1) 0 v, fiberFrame p₀ φ v) = v := by
  refine Subtype.ext (funext (Fin.cases ?_ fun i => ?_))
  · simp [coe_baseFrame]
  · simp [coe_baseFrame, fiberFrame]

private theorem fiberFrame_baseFrame (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ)
    (q : sphere (0 : E) 1 × stiefel F k) : fiberFrame p₀ φ (baseFrame p₀ φ q) = q.2 := by
  refine Subtype.ext (funext fun i => ?_)
  simp [fiberFrame, stiefelProj_baseFrame, coe_baseFrame]

/-- **The chart of the projection of the Stiefel manifold to the first vector** over the
complement of the antipode of a point `p₀` of the unit sphere, with fibre the Stiefel manifold
`V_k(F)` of a space `F` identified with `p₀^⊥` by a linear isometry `φ`. It sends a frame
`(p, u₁, …, u_k)` with `p ≠ -p₀` to `p` and the frame `(φ⁻¹ (R_p⁻¹ uᵢ))ᵢ` of `F`, where
`R_p = TauCeti.pairRotation p₀ p` is the rotation carrying `p₀` to `p`; its inverse sends `(p, w)`
to the frame `(p, R_p (φ w₁), …, R_p (φ w_k))`. -/
def stiefelProjTrivialization (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ) (k : ℕ) :
    Trivialization (stiefel F k) (stiefelProj E (k + 1) 0) where
  toFun v := (stiefelProj E (k + 1) 0 v, fiberFrame p₀ φ v)
  invFun q := baseFrame p₀ φ q
  source := stiefelProj E (k + 1) 0 ⁻¹' {-p₀}ᶜ
  target := {-p₀}ᶜ ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' q hq := by
    rw [mem_preimage, stiefelProj_baseFrame]
    exact hq.1
  left_inv' v _ := baseFrame_fiberFrame p₀ φ v
  right_inv' q _ := Prod.ext (stiefelProj_baseFrame p₀ φ q) (fiberFrame_baseFrame p₀ φ q)
  open_source := isOpen_compl_singleton.preimage (continuous_stiefelProj 0)
  open_target := isOpen_compl_singleton.prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_stiefelProj 0).continuousOn.prodMk ?_
    refine IsInducing.subtypeVal.continuousOn_iff.2 (continuousOn_pi.2 fun i => ?_)
    refine φ.symm.continuous.comp_continuousOn
      (IsInducing.subtypeVal.continuousOn_iff.2 ?_)
    exact ContinuousOn.pairRotation_symm_apply
      (continuous_subtypeVal.comp (continuous_stiefelProj 0)).continuousOn
      ((continuous_apply i.succ).comp continuous_subtypeVal).continuousOn
      fun _ hv => add_ne_zero_of_ne_neg_sphere hv
  continuousOn_invFun := by
    refine IsInducing.subtypeVal.continuousOn_iff.2 ?_
    simp only [Function.comp_def, coe_baseFrame]
    refine (continuous_subtypeVal.comp continuous_fst).continuousOn.matrixVecCons
      (continuousOn_pi.2 fun i => ?_)
    exact ContinuousOn.pairRotation_apply (continuous_subtypeVal.comp continuous_fst).continuousOn
      ((continuous_subtypeVal.comp φ.continuous).comp
        ((continuous_apply i).comp (continuous_subtypeVal.comp continuous_snd))).continuousOn
      fun _ hq => add_ne_zero_of_ne_neg_sphere hq.1
  baseSet := {-p₀}ᶜ
  open_baseSet := isOpen_compl_singleton
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (p₀ : sphere (0 : E) 1) (φ : F ≃ₗᵢ[ℝ] (ℝ ∙ (p₀ : E))ᗮ)

@[simp]
theorem stiefelProjTrivialization_baseSet :
    (stiefelProjTrivialization p₀ φ k).baseSet = {-p₀}ᶜ :=
  (rfl)

/-- The base point lies in the base of its chart. -/
theorem mem_stiefelProjTrivialization_baseSet :
    p₀ ∈ (stiefelProjTrivialization p₀ φ k).baseSet :=
  ne_neg_of_mem_unit_sphere ℝ p₀

/-- The fibre coordinate of the chart `TauCeti.stiefelProjTrivialization`: the `i`th vector of the
frame of `F` attached to a frame `(p, u₁, …, u_k)` is `φ⁻¹ (R_p⁻¹ u_{i+1})`. -/
theorem coe_stiefelProjTrivialization_snd_apply (v : stiefel E (k + 1)) (i : Fin k) :
    ((φ (((stiefelProjTrivialization p₀ φ k v).2 : Fin k → F) i) : (ℝ ∙ (p₀ : E))ᗮ) : E) =
      (pairRotation (p₀ : E) (v.val 0)).symm (v.val i.succ) := by
  simp [stiefelProjTrivialization, fiberFrame]

/-- The inverse of the chart `TauCeti.stiefelProjTrivialization` sends a point `p` and a frame `w`
of `F` to the frame `(p, R_p (φ w₁), …, R_p (φ w_k))`. -/
@[simp]
theorem coe_stiefelProjTrivialization_symm_apply (q : sphere (0 : E) 1 × stiefel F k) :
    ((stiefelProjTrivialization p₀ φ k).toOpenPartialHomeomorph.symm q : Fin (k + 1) → E) =
      Matrix.vecCons (q.1 : E) fun i => pairRotation (p₀ : E) q.1 (φ (q.2.val i)) :=
  coe_baseFrame p₀ φ q

/-- **The inverse chart over the base point is the inclusion of the fibre.** With fibre `p₀^⊥`
itself, the inverse of the chart around `p₀` sends `(p₀, w)` to the frame `(p₀, w)`
(`TauCeti.stiefelFrameIncl`). -/
theorem stiefelProjTrivialization_symm_apply_self (w : stiefel (ℝ ∙ (p₀ : E))ᗮ k) :
    (stiefelProjTrivialization p₀ (LinearIsometryEquiv.refl ℝ _) k).toOpenPartialHomeomorph.symm
      (p₀, w) = stiefelFrameIncl p₀ k w :=
  Subtype.ext (by simp)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **The projection of a Stiefel manifold to the first vector is locally trivial.** For a real
inner product space `F` of dimension one less than `E`, every point of the unit sphere of `E` lies
in the base of a chart of the projection `V_{k+1}(E) → Sⁿ` with fibre `V_k(F)`. -/
theorem exists_trivialization_stiefelProj_zero_of_finrank_add_one_eq
    (hF : finrank ℝ F + 1 = finrank ℝ E) :
    ∃ e : Trivialization (stiefel F k) (stiefelProj E (k + 1) 0), p₀ ∈ e.baseSet := by
  have h : finrank ℝ F = finrank ℝ (ℝ ∙ (p₀ : E))ᗮ := by
    have h₁ := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (p₀ : E))
    rw [finrank_span_singleton (ne_zero_of_mem_unit_sphere p₀)] at h₁
    omega
  exact ⟨stiefelProjTrivialization p₀ ((stdOrthonormalBasis ℝ F).equiv
    (stdOrthonormalBasis ℝ (ℝ ∙ (p₀ : E))ᗮ) (finCongr h)) k,
    mem_stiefelProjTrivialization_baseSet _ _⟩

end TauCeti
