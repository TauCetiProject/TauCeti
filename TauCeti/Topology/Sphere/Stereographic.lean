/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The punctured sphere in stereographic coordinates

The complement of a point of the unit sphere `Sᵐ` of a real normed space of dimension `m + 1` is
homeomorphic to any real normed space `E` of dimension `m`: transport the point to a Euclidean
sphere and project stereographically from it. The complements of two antipodal points, the poles,
therefore cover `Sᵐ` by two open sets homeomorphic to `E`.

Let `K` be a compact subset of the unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1`, missing a point `w`. Reading `Sⁿ \ {w}` in the stereographic chart from `w`, the image of
`K` is bounded, so `K` lies in the image of a large coordinate ball. Rescaling, `K` lies in the
image of the open unit ball of any real normed space `E` of dimension `n` under a continuous
injection `E → Sⁿ` missing `w`.

## Main results

* `TauCeti.nonempty_homeomorph_sphere_compl_singleton`: the sphere `Sᵐ` minus a point is
  homeomorphic to `E`.
* `TauCeti.exists_two_euclidean_opens_sphere`: `Sᵐ` is covered by two open sets homeomorphic to
  `E`.
* `TauCeti.exists_continuous_injective_subset_image_ball`: a compact subset of the sphere missing
  `w` lies in the image of the open unit ball under a continuous injection `E → Sⁿ` missing `w`.
-/

public section

open Function Metric Module Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The sphere minus a point is Euclidean.** Let `F` be a real normed space of dimension `m + 1`
and `E` one of dimension `m`. The complement of any point `p` of the unit sphere of `F` is
homeomorphic to `E`; in an inner product space this is stereographic projection from `p`. -/
theorem nonempty_homeomorph_sphere_compl_singleton (hEF : finrank ℝ F = finrank ℝ E + 1)
    (p : sphere (0 : F) 1) :
    Nonempty (({p}ᶜ : Set (sphere (0 : F) 1)) ≃ₜ E) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) = finrank ℝ E + 1) :=
    ⟨by simp⟩
  -- Move `p` to the Euclidean sphere and project stereographically from its image.
  let h : sphere (0 : F) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1 :=
    sphereHomeomorphOfFinrankEq (by simp [hEF])
  let σ := stereographic' (finrank ℝ E) (h p)
  have hsource : h '' {p}ᶜ = σ.source := by
    rw [stereographic'_source, image_compl_eq h.bijective, image_singleton]
  exact ⟨(h.image _).trans <| (Homeomorph.setCongr hsource).trans <|
    σ.toHomeomorphSourceTarget.trans <| (Homeomorph.setCongr (stereographic'_target _)).trans <|
      (Homeomorph.Set.univ _).trans
        (ContinuousLinearEquiv.ofFinrankEq (E := EuclideanSpace ℝ (Fin (finrank ℝ E))) (F := E)
          finrank_euclideanSpace_fin).toHomeomorph⟩

/-- **The sphere is covered by two Euclidean open sets.** The unit sphere `Sᵐ` of a real normed
space `F` of dimension `m + 1` is the union of the complements of two antipodal points `p` and
`-p`, its two poles, and each of them is homeomorphic to a real normed space `E` of dimension `m`.
For `m = 1` these are two open arcs of the circle; for `m = 0` they are the two points of `S⁰`. -/
theorem exists_two_euclidean_opens_sphere (hEF : finrank ℝ F = finrank ℝ E + 1) :
    ∃ U V : Set (sphere (0 : F) 1), IsOpen U ∧ IsOpen V ∧ U ∪ V = univ ∧ Nonempty (U ≃ₜ E) ∧
      Nonempty (V ≃ₜ E) := by
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
    ((NormedSpace.sphere_nonempty (x := (0 : F))).2 zero_le_one).to_subtype
  refine ⟨{p}ᶜ, {-p}ᶜ, isOpen_compl_singleton, isOpen_compl_singleton, ?_,
    nonempty_homeomorph_sphere_compl_singleton hEF p,
    nonempty_homeomorph_sphere_compl_singleton hEF (-p)⟩
  rw [← compl_inter, compl_univ_iff, singleton_inter_eq_empty, mem_singleton_iff]
  exact ne_neg_of_mem_unit_sphere ℝ p

end NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A compact subset `K` of the unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1` missing a point `w` lies in the image of the open unit ball of `E`, `dim E = n`, under a
continuous injection `E → Sⁿ` missing `w`: a large ball in the stereographic chart from `w`. -/
theorem exists_continuous_injective_subset_image_ball
    (hEF : finrank ℝ F = finrank ℝ E + 1) {K : Set (sphere (0 : F) 1)} (hK : IsCompact K)
    {w : sphere (0 : F) 1} (hwK : w ∉ K) :
    ∃ ψ : E → sphere (0 : F) 1, Continuous ψ ∧ Injective ψ ∧ (∀ v, ψ v ≠ w) ∧
      K ⊆ ψ '' ball 0 1 := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φs := stereographic' (finrank ℝ E) w
  have hsymm : Continuous φs.symm :=
    continuousOn_univ.1 (stereographic'_target (n := finrank ℝ E) w ▸ φs.continuousOn_symm)
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hKs : K ⊆ φs.source := fun x hx ↦ by
    rw [stereographic'_source (n := finrank ℝ E)]
    rintro rfl
    exact hwK hx
  -- `K` lies in the coordinate ball of radius `R`.
  obtain ⟨R, hR, hKR⟩ := ((hK.image_of_continuousOn (φs.continuousOn.mono hKs)).image
    L.symm.continuous).isBounded.subset_ball_lt 0 0
  refine ⟨fun v ↦ φs.symm (L (R • v)), hsymm.comp (L.continuous.comp (continuous_const_smul R)),
    fun v v' h ↦ smul_right_injective E hR.ne'
      (L.injective (φs.symm.injOn (by simp [φs]) (by simp [φs]) h)), fun v ↦ ?_,
    fun x hx ↦ ⟨R⁻¹ • L.symm (φs x), ?_, ?_⟩⟩
  · have := φs.map_target (x := L (R • v)) (by simp [φs])
    rwa [stereographic'_source (n := finrank ℝ E)] at this
  · have h := hKR ⟨φs x, ⟨x, hx, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at h ⊢
    rwa [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_lt_iff₀ hR, mul_one]
  · simp only [smul_inv_smul₀ hR.ne', ContinuousLinearEquiv.apply_symm_apply,
      φs.left_inv (hKs hx)]


end TauCeti
