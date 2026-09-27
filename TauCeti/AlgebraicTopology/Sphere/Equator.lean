/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Analysis.Normed.Module.Normalize

/-!
# The equator of a unit sphere

Removing two antipodal points `p` and `-p` from the unit sphere of a real inner product space `E`
leaves a space homotopy equivalent to the equator, the unit sphere of the orthogonal complement
`(ℝ ∙ p)ᗮ`. One map is the inclusion of the equator; the other is radial projection of the
orthogonal projection onto `(ℝ ∙ p)ᗮ`. Retracting the equator this way fixes it, and the
deformation of the punctured sphere normalizes the segment from a point to its orthogonal
projection, which never meets the line through `p`.

Together with the contractibility of a sphere minus one point, this is the geometric input to
the Mayer–Vietoris computation of the homology of spheres.

## Main declarations

* `TauCeti.coe_mem_span_singleton_iff`: a point of the unit sphere lies on the line through a
  point `p` of the sphere exactly when it is `p` or `-p`.
* `TauCeti.equatorHomotopyEquiv`: the unit sphere minus `p` and `-p` is homotopy equivalent to
  the unit sphere of `(ℝ ∙ p)ᗮ`, with `TauCeti.coe_equatorHomotopyEquiv_apply` and
  `TauCeti.coe_equatorHomotopyEquiv_symm_apply` computing both maps.

## References

This is the deformation retraction of `Sⁿ ∖ {±p}` onto the equator `Sⁿ⁻¹` used in Hatcher,
*Algebraic Topology*, Section 2.2, to compute the homology of spheres.
-/

public section

noncomputable section

open Metric NormedSpace
open scoped unitInterval ContinuousMap

namespace TauCeti

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point of the unit sphere lies on the line through a point `p` of the sphere exactly when it
is `p` or `-p`. -/
theorem coe_mem_span_singleton_iff {x p : sphere (0 : E) 1} :
    (x : E) ∈ ℝ ∙ (p : E) ↔ x = p ∨ x = -p := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
    have habs : |a| = 1 := by
      simpa [← ha, norm_smul] using mem_sphere_zero_iff_norm.1 x.2
    rcases (abs_eq zero_le_one).1 habs with rfl | rfl
    · exact Or.inl (Subtype.ext (by rw [← ha, one_smul]))
    · exact Or.inr (Subtype.ext (by rw [← ha, coe_neg_sphere, neg_one_smul]))
  · rintro (rfl | rfl)
    · exact Submodule.mem_span_singleton_self _
    · rw [coe_neg_sphere]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- A point of the unit sphere avoids `p` and `-p` exactly when it is off the line through
`p`. -/
private lemma mem_compl_iff_notMem_span {x : sphere (0 : E) 1} :
    x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) ↔ (x : E) ∉ ℝ ∙ (p : E) := by
  simp [coe_mem_span_singleton_iff, not_or]

/-- Moving a point of the sphere off the line through `p` along the direction of `p` keeps it off
that line. -/
private lemma sub_smul_starProjection_notMem {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) (t : ℝ) :
    (x : E) - t • (ℝ ∙ (p : E)).starProjection x ∉ ℝ ∙ (p : E) := by
  intro h
  refine (mem_compl_iff_notMem_span p).1 hx ?_
  simpa using Submodule.add_mem _ h
    (Submodule.smul_mem _ t ((ℝ ∙ (p : E)).starProjection_apply_mem x))

/-- Normalizing a vector off the line through `p` keeps it off that line. -/
private lemma normalize_notMem {v : E} (hv : v ∉ ℝ ∙ (p : E)) : normalize v ∉ ℝ ∙ (p : E) := by
  have hv0 : ‖v‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 fun h => hv (by
    rw [h]
    exact Submodule.zero_mem _))
  rwa [NormedSpace.normalize, Submodule.smul_mem_iff _ hv0]

/-- The orthogonal projection onto `(ℝ ∙ p)ᗮ` of a point of the sphere, as a vector of `E`. -/
private lemma coe_orthogonalProjectionOnto_orthogonal (x : E) :
    (((ℝ ∙ (p : E))ᗮ.orthogonalProjectionOnto x : (ℝ ∙ (p : E))ᗮ) : E) =
      x - (1 : ℝ) • (ℝ ∙ (p : E)).starProjection x := by
  rw [one_smul, ← Submodule.starProjection_orthogonal_val, Submodule.starProjection_apply]

/-- The orthogonal projection onto `(ℝ ∙ p)ᗮ` of a point of the sphere other than `±p` is
nonzero. -/
private lemma orthogonalProjectionOnto_ne_zero (x : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    (ℝ ∙ (p : E))ᗮ.orthogonalProjectionOnto ((x : sphere (0 : E) 1) : E) ≠ 0 := by
  intro h
  refine sub_smul_starProjection_notMem p x.2 1 ?_
  rw [← coe_orthogonalProjectionOnto_orthogonal, h]
  exact Submodule.zero_mem _

/-- Radial projection of the orthogonal projection onto `(ℝ ∙ p)ᗮ`, retracting the sphere minus
`±p` onto the equator. -/
private def toEquator :
    C(({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)), sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
  normalizeToSphere (fun x => (ℝ ∙ (p : E))ᗮ.orthogonalProjectionOnto ((x : sphere (0 : E) 1) : E))
    ((ContinuousLinearMap.continuous _).comp (continuous_subtype_val.comp continuous_subtype_val))
    (orthogonalProjectionOnto_ne_zero p)

private lemma coe_toEquator_apply (x : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ((toEquator p x : (ℝ ∙ (p : E))ᗮ) : E) =
      normalize ((ℝ ∙ (p : E))ᗮ.starProjection ((x : sphere (0 : E) 1) : E)) := by
  simp [toEquator, NormedSpace.normalize]

/-- A unit vector orthogonal to `p` is neither `p` nor `-p`. -/
private lemma coe_notMem_span (y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ((y : (ℝ ∙ (p : E))ᗮ) : E) ∉ ℝ ∙ (p : E) := by
  intro h
  have hy : ‖((y : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 :=
    (Submodule.norm_coe _).trans (norm_eq_of_mem_sphere y)
  have h0 := Submodule.inner_right_of_mem_orthogonal h (y : (ℝ ∙ (p : E))ᗮ).2
  rw [inner_self_eq_zero] at h0
  simp [h0] at hy

/-- The inclusion of the equator into the sphere minus `±p`. -/
private def ofEquator :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1, ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) where
  toFun y := ⟨⟨((y : (ℝ ∙ (p : E))ᗮ) : E),
    mem_sphere_zero_iff_norm.2 ((Submodule.norm_coe _).trans (norm_eq_of_mem_sphere y))⟩,
    (mem_compl_iff_notMem_span p).2 (coe_notMem_span p y)⟩
  continuous_toFun := by fun_prop

/-- Retracting the equator onto itself is the identity. -/
private lemma toEquator_comp_ofEquator : (toEquator p).comp (ofEquator p) = ContinuousMap.id _ := by
  ext y
  rw [ContinuousMap.comp_apply, coe_toEquator_apply]
  simp [ofEquator, normalize_eq_self_of_norm_eq_one
    ((Submodule.norm_coe _).trans (norm_eq_of_mem_sphere y))]

/-- The deformation of the sphere minus `±p` onto the equator: at time `t` a point `x` moves to
the normalization of `x - t • π x`, where `π` is the orthogonal projection onto the line through
`p`. -/
private def deformation :
    ContinuousMap.Homotopy (ContinuousMap.id _) ((ofEquator p).comp (toEquator p)) :=
  let g : I × ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) → E := fun z =>
    ((z.2 : sphere (0 : E) 1) : E) -
      (z.1 : ℝ) • (ℝ ∙ (p : E)).starProjection (z.2 : sphere (0 : E) 1)
  have hg : Continuous g := by fun_prop
  have hg0 : ∀ z, g z ≠ 0 := fun z h => sub_smul_starProjection_notMem p z.2.2 z.1
    ((congrArg (· ∈ ℝ ∙ (p : E)) h).mpr (Submodule.zero_mem _))
  have hmem : ∀ z, normalizeToSphere g hg hg0 z ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) :=
    fun z => (mem_compl_iff_notMem_span p).2 (by
      rw [coe_normalizeToSphere_apply]
      exact normalize_notMem p (sub_smul_starProjection_notMem p z.2.2 z.1))
  { toFun z := ⟨_, hmem z⟩
    continuous_toFun := (ContinuousMap.continuous _).subtype_mk hmem
    map_zero_left x := by
      refine Subtype.ext (Subtype.ext ?_)
      simp [g, normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.1 (x : sphere (0 : E) 1).2)]
    map_one_left x := by
      refine Subtype.ext (Subtype.ext ?_)
      simp only [coe_normalizeToSphere_apply, Set.Icc.coe_one, ContinuousMap.comp_apply, g]
      rw [← coe_orthogonalProjectionOnto_orthogonal]
      simp [ofEquator, coe_toEquator_apply] }

/-- **The sphere minus two antipodal points is homotopy equivalent to the equator.** For a point
`p` of the unit sphere of a real inner product space `E`, the unit sphere minus `p` and `-p` is
homotopy equivalent to the unit sphere of the orthogonal complement `(ℝ ∙ p)ᗮ`: radial projection
of the orthogonal projection is a homotopy inverse of the inclusion. -/
def equatorHomotopyEquiv :
    ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) ≃ₕ sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 where
  toFun := toEquator p
  invFun := ofEquator p
  left_inv := ⟨(deformation p).symm⟩
  right_inv := by
    rw [toEquator_comp_ofEquator]

/-- The homotopy equivalence `TauCeti.equatorHomotopyEquiv` is radial projection of the
orthogonal projection onto `(ℝ ∙ p)ᗮ`. -/
@[simp]
theorem coe_equatorHomotopyEquiv_apply (x : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ((equatorHomotopyEquiv p x : (ℝ ∙ (p : E))ᗮ) : E) =
      normalize ((ℝ ∙ (p : E))ᗮ.starProjection ((x : sphere (0 : E) 1) : E)) :=
  coe_toEquator_apply p x

/-- The homotopy inverse of `TauCeti.equatorHomotopyEquiv` is the inclusion of the equator. -/
@[simp]
theorem coe_equatorHomotopyEquiv_symm_apply (y : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    (((equatorHomotopyEquiv p).symm y : sphere (0 : E) 1) : E) = ((y : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

end TauCeti
