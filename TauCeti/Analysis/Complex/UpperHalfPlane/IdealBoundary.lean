/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
-- `OnePoint.instContinuousConstSMul`: `GL (Fin 2) ℂ` acts on the Riemann sphere by homeomorphisms.
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
public import TauCeti.Topology.Compactification.OnePoint.Nhds
import TauCeti.Topology.Compactification.OnePoint.Map

/-!
# The ideal boundary of a subset of the upper half-plane

The ideal boundary `∂ℍ = OnePoint ℝ` sits in the Riemann sphere `OnePoint ℂ` through
`OnePoint.map ((↑) : ℝ → ℂ)`. The *ideal boundary* `TauCeti.UpperHalfPlane.idealBoundary A` of a
subset `A ⊆ ℍ` is the set of ideal points lying in the closure of `A` in the sphere: the points of
`∂ℍ` at which `A` accumulates. It is the boundary part of the closure of `A` in the
compactification `ℍ ∪ ∂ℍ`, which the Cayley transform identifies with the closed unit disc. Limit
sets of Fuchsian groups are ideal boundaries of orbits.

## Main statements

* `UpperHalfPlane.dist_coe_ofReal_le_exp_dist_mul`: the Euclidean distance of a point of `ℍ`
  to a real point grows at most by the factor `exp d` along a hyperbolic displacement `d`.
* `TauCeti.UpperHalfPlane.coe_mem_idealBoundary_iff` and
  `TauCeti.UpperHalfPlane.infty_mem_idealBoundary_iff`: a real point is in the ideal boundary of
  `A` when `A` has points arbitrarily close to it, and `∞` is when `A` is unbounded in `ℂ`.
* `TauCeti.UpperHalfPlane.isClosed_idealBoundary`: the ideal boundary is closed in `∂ℍ`.
* `TauCeti.UpperHalfPlane.idealBoundary_subset_of_forall_exists_dist_le`: a set within bounded
  hyperbolic distance of another has no more ideal boundary points, so sets at finite Hausdorff
  distance have the same ideal boundary, and a bounded set has none
  (`TauCeti.UpperHalfPlane.idealBoundary_eq_empty_of_isBounded`).
* `TauCeti.UpperHalfPlane.idealBoundary_smul`: the ideal boundary is equivariant for `PSL(2, ℝ)`,
  which acts on the sphere through `TauCeti.UpperHalfPlane.coe_smul_eq_map_smul` and
  `TauCeti.UpperHalfPlane.map_ofReal_smul`.

## References

* W. Duke, Ö. Imamoglu and Á. Tóth, *Geometric invariants for real quadratic fields*, Ann. of
  Math. 184 (2016), 949–990, §2 (limit sets as the boundary accumulation points of orbits).
-/

public section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane
open scoped MatrixGroups OnePoint Pointwise

namespace UpperHalfPlane

/-- Along a hyperbolic displacement `d`, the Euclidean distance from a point of `ℍ` to a real
point grows at most by the factor `exp d`. -/
theorem dist_coe_ofReal_le_exp_dist_mul (z w : ℍ) (x : ℝ) :
    dist (z : ℂ) x ≤ Real.exp (dist z w) * dist (w : ℂ) x := by
  have him : w.im ≤ dist (w : ℂ) x := by
    simpa [abs_of_pos w.im_pos, Complex.dist_eq] using Complex.abs_im_le_norm ((w : ℂ) - x)
  calc dist (z : ℂ) x ≤ dist (z : ℂ) w + dist (w : ℂ) x := dist_triangle _ _ _
    _ ≤ dist (w : ℂ) x * (Real.exp (dist z w) - 1) + dist (w : ℂ) x := by
      gcongr
      exact (dist_coe_le z w).trans (mul_le_mul_of_nonneg_right him
        (sub_nonneg.2 (Real.one_le_exp dist_nonneg)))
    _ = Real.exp (dist z w) * dist (w : ℂ) x := by ring

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

noncomputable section

/-- The **ideal boundary** of a subset `A` of `ℍ`: the ideal points of `∂ℍ = OnePoint ℝ` lying in
the closure of `A` in the Riemann sphere `OnePoint ℂ`, that is, the points of `∂ℍ` at which `A`
accumulates. -/
def idealBoundary (A : Set ℍ) : Set (OnePoint ℝ) :=
  OnePoint.map ((↑) : ℝ → ℂ) ⁻¹' closure ((↑) '' (((↑) : ℍ → ℂ) '' A))

theorem mem_idealBoundary_iff {A : Set ℍ} {ξ : OnePoint ℝ} :
    ξ ∈ idealBoundary A ↔
      OnePoint.map ((↑) : ℝ → ℂ) ξ ∈ closure ((↑) '' (((↑) : ℍ → ℂ) '' A)) :=
  Iff.rfl

/-- A real point is in the ideal boundary of `A` exactly when `A` has points arbitrarily close to
it in `ℂ`. -/
theorem coe_mem_idealBoundary_iff {A : Set ℍ} {x : ℝ} :
    (x : OnePoint ℝ) ∈ idealBoundary A ↔ ∀ ε > 0, ∃ z ∈ A, dist (z : ℂ) x < ε := by
  rw [mem_idealBoundary_iff, OnePoint.map_some, ← mem_preimage,
    ← OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image,
    Metric.mem_closure_iff]
  simp [dist_comm]

/-- The point `∞` is in the ideal boundary of `A` exactly when `A` is unbounded in `ℂ`. -/
theorem infty_mem_idealBoundary_iff {A : Set ℍ} :
    ∞ ∈ idealBoundary A ↔ ∀ r : ℝ, ∃ z ∈ A, r < ‖(z : ℂ)‖ := by
  rw [mem_idealBoundary_iff, OnePoint.map_infty, mem_closure_iff_nhdsWithin_neBot,
    nhdsWithin_infty_coe_image, map_neBot_iff, coclosedCompact_eq_cocompact,
    ← Metric.cobounded_eq_cocompact,
    (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).inf_principal_neBot_iff]
  simp [Set.Nonempty, and_comm]

theorem isClosed_idealBoundary (A : Set ℍ) : IsClosed (idealBoundary A) :=
  isClosed_closure.preimage
    (continuous_onePointMap_of_isProperMap Complex.isometry_ofReal.isClosedEmbedding.isProperMap)

@[gcongr]
theorem idealBoundary_mono {A B : Set ℍ} (h : A ⊆ B) : idealBoundary A ⊆ idealBoundary B :=
  preimage_mono (closure_mono (image_mono (image_mono h)))

@[simp]
theorem idealBoundary_empty : idealBoundary ∅ = ∅ := by
  simp [idealBoundary]

@[simp]
theorem idealBoundary_union (A B : Set ℍ) :
    idealBoundary (A ∪ B) = idealBoundary A ∪ idealBoundary B := by
  simp [idealBoundary, image_union, closure_union, preimage_union]

/-- If every point of `A` lies within hyperbolic distance `C` of a point of `B`, then every ideal
point at which `A` accumulates is one at which `B` accumulates. -/
theorem idealBoundary_subset_of_forall_exists_dist_le {A B : Set ℍ} {C : ℝ}
    (h : ∀ z ∈ A, ∃ w ∈ B, dist z w ≤ C) : idealBoundary A ⊆ idealBoundary B := by
  intro ξ hξ
  induction ξ using OnePoint.rec with
  | infty =>
    rw [infty_mem_idealBoundary_iff] at hξ ⊢
    intro r
    obtain ⟨z, hz, hzr⟩ := hξ (Real.exp C * r)
    obtain ⟨w, hw, hzw⟩ := h z hz
    refine ⟨w, hw, lt_of_mul_lt_mul_left ?_ (Real.exp_pos C).le⟩
    have hz0 := dist_coe_ofReal_le_exp_dist_mul z w 0
    simp only [Complex.ofReal_zero, dist_zero_right] at hz0
    calc Real.exp C * r < ‖(z : ℂ)‖ := hzr
      _ ≤ Real.exp (dist z w) * ‖(w : ℂ)‖ := hz0
      _ ≤ Real.exp C * ‖(w : ℂ)‖ := by gcongr
  | coe x =>
    rw [coe_mem_idealBoundary_iff] at hξ ⊢
    intro ε hε
    obtain ⟨z, hz, hzx⟩ := hξ (ε / Real.exp C) (div_pos hε (Real.exp_pos C))
    obtain ⟨w, hw, hzw⟩ := h z hz
    refine ⟨w, hw, ?_⟩
    calc dist (w : ℂ) x ≤ Real.exp (dist w z) * dist (z : ℂ) x :=
          dist_coe_ofReal_le_exp_dist_mul w z x
      _ ≤ Real.exp C * dist (z : ℂ) x := by rw [dist_comm]; gcongr
      _ < Real.exp C * (ε / Real.exp C) := by gcongr
      _ = ε := mul_div_cancel₀ ε (Real.exp_pos C).ne'

/-- A bounded subset of `ℍ` accumulates at no ideal point. -/
theorem idealBoundary_eq_empty_of_isBounded {A : Set ℍ} (hA : IsBounded A) :
    idealBoundary A = ∅ := by
  obtain ⟨C, hC⟩ := hA.subset_closedBall UpperHalfPlane.I
  refine subset_empty_iff.1 ((idealBoundary_subset_of_forall_exists_dist_le
    (B := {UpperHalfPlane.I}) fun z hz ↦ ⟨_, rfl, hC hz⟩).trans fun ξ hξ ↦ ?_)
  rw [mem_idealBoundary_iff, image_singleton, image_singleton, closure_singleton] at hξ
  induction ξ using OnePoint.rec with
  | infty => exact OnePoint.infty_ne_coe _ hξ
  | coe x =>
    have h := congrArg Complex.im (OnePoint.coe_injective hξ)
    simp at h

/-- The inclusion of `ℍ` in the Riemann sphere intertwines the action of `SL(2, ℝ)` with the
Möbius action of the same matrix with complex entries. -/
theorem coe_smul_eq_map_smul (A : SL(2, ℝ)) (z : ℍ) :
    (((A • z : ℍ) : ℂ) : OnePoint ℂ) =
      Matrix.GeneralLinearGroup.map Complex.ofRealHom (A : GL (Fin 2) ℝ) •
        ((z : ℂ) : OnePoint ℂ) := by
  have h := denom_ne_zero (A : GL (Fin 2) ℝ) z
  simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h
  simp [OnePoint.smul_some_eq_ite, coe_specialLinearGroup_apply, h]

/-- The inclusion of the ideal boundary `OnePoint ℝ` in the Riemann sphere intertwines the action
of `PSL(2, ℝ)` with the Möbius action of a representative with complex entries. -/
theorem map_ofReal_smul (A : SL(2, ℝ)) (ξ : OnePoint ℝ) :
    OnePoint.map ((↑) : ℝ → ℂ) ((A : PSL(2, ℝ)) • ξ) =
      Matrix.GeneralLinearGroup.map Complex.ofRealHom (A : GL (Fin 2) ℝ) •
        OnePoint.map ((↑) : ℝ → ℂ) ξ := by
  rw [OnePoint.pslMk_smul]
  exact OnePoint.map_smul Complex.ofRealHom _ ξ

/-- The ideal boundary is equivariant: the ideal points at which `g • A` accumulates are the
`g`-translates of those at which `A` accumulates. -/
theorem idealBoundary_smul (g : PSL(2, ℝ)) (A : Set ℍ) :
    idealBoundary (g • A) = g • idealBoundary A := by
  induction g using QuotientGroup.induction_on with | _ B =>
  set M := Matrix.GeneralLinearGroup.map Complex.ofRealHom (B : GL (Fin 2) ℝ)
  have himage : ((↑) : ℂ → OnePoint ℂ) '' (((↑) : ℍ → ℂ) '' ((B : PSL(2, ℝ)) • A)) =
      M • ((↑) '' (((↑) : ℍ → ℂ) '' A)) := by
    simp only [image_image, ← image_smul, UpperHalfPlane.pslMk_smul, coe_smul_eq_map_smul, M]
  ext ξ
  rw [mem_idealBoundary_iff, himage, closure_smul, mem_smul_set_iff_inv_smul_mem,
    mem_smul_set_iff_inv_smul_mem, mem_idealBoundary_iff, ← QuotientGroup.mk_inv,
    map_ofReal_smul, map_inv, map_inv]

end

end TauCeti.UpperHalfPlane
