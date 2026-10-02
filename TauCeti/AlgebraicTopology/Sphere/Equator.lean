/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.AlgebraicTopology.Sphere.Zero
public import TauCeti.Analysis.Normed.Module.Ball
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

When `E` is two-dimensional, the equator is a zero-sphere, so the circle minus `p` and `-p`
consists of two open arcs: for any point `x` of it, the path components of `x` and of `-x` are
distinct and are the only two path components.

## Main declarations

* `TauCeti.equatorHomotopyEquiv`: the unit sphere minus `p` and `-p` is homotopy equivalent to
  the unit sphere of `(ℝ ∙ p)ᗮ`, with `TauCeti.coe_equatorHomotopyEquiv_apply` and
  `TauCeti.coe_equatorHomotopyEquiv_symm_apply` computing both maps.
* `TauCeti.zerothHomotopy_mk_neg_ne_of_finrank_eq_two` and
  `TauCeti.zerothHomotopy_mk_eq_or_eq_neg_of_finrank_eq_two`: in dimension two, the circle minus
  `p` and `-p` has exactly two path components, those of `x` and of `-x`.

## References

This is the deformation retraction of `Sⁿ ∖ {±p}` onto the equator `Sⁿ⁻¹` used in Hatcher,
*Algebraic Topology*, Section 2.2, to compute the homology of spheres.
-/

public section

noncomputable section

open Metric Module NormedSpace
open scoped unitInterval ContinuousMap

namespace TauCeti

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The unit sphere minus two antipodal points is invariant under the antipodal map. -/
theorem neg_mem_compl_singleton_inter_compl_singleton_neg {p x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    -x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) := by
  simp only [Set.mem_inter_iff, Set.mem_compl_singleton_iff] at hx ⊢
  exact ⟨fun h ↦ hx.2 (neg_eq_iff_eq_neg.mp h), fun h ↦ hx.1 (neg_inj.mp h)⟩

/-- A point of the unit sphere avoids `p` and `-p` exactly when it is off the line through
`p`. -/
private lemma mem_compl_iff_notMem_span (p : sphere (0 : E) 1) {x : sphere (0 : E) 1} :
    x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) ↔ (x : E) ∉ ℝ ∙ (p : E) := by
  simp [not_or]

end Seminormed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- Moving a point of the sphere off the line through `p` along the direction of `p` keeps it off
that line. -/
private lemma sub_smul_starProjection_notMem {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) (t : ℝ) :
    (x : E) - t • (ℝ ∙ (p : E)).starProjection x ∉ ℝ ∙ (p : E) := by
  intro h
  refine (mem_compl_iff_notMem_span p).1 hx ?_
  simpa using Submodule.add_mem _ h
    (Submodule.smul_mem _ t ((ℝ ∙ (p : E)).starProjection_apply_mem x))

/-- The orthogonal projection onto `(ℝ ∙ p)ᗮ` of a point of the sphere other than `±p` is
nonzero. -/
private lemma orthogonalProjectionOnto_ne_zero (x : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    (ℝ ∙ (p : E))ᗮ.orthogonalProjectionOnto ((x : sphere (0 : E) 1) : E) ≠ 0 := by
  intro h
  apply (mem_compl_iff_notMem_span p).1 x.2
  rw [← Submodule.starProjection_eq_self_iff]
  apply Eq.symm
  simpa [Submodule.orthogonalProjectionOnto_orthogonal, sub_eq_zero] using
    congrArg (fun v : (ℝ ∙ (p : E))ᗮ => (v : E)) h

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
  exact ne_zero_of_mem_unit_sphere y
    ((Submodule.mem_left_iff_eq_zero_of_disjoint (ℝ ∙ (p : E)).orthogonal_disjoint).1 h)

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
      intro h
      apply sub_smul_starProjection_notMem p z.2.2 z.1
      simpa using (ℝ ∙ (p : E)).smul_mem ‖g z‖ h)
  { toFun z := ⟨_, hmem z⟩
    continuous_toFun := (ContinuousMap.continuous _).subtype_mk hmem
    map_zero_left x := by
      refine Subtype.ext (Subtype.ext ?_)
      simp [g, normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.1 (x : sphere (0 : E) 1).2)]
    map_one_left x := by
      refine Subtype.ext (Subtype.ext ?_)
      simp only [coe_normalizeToSphere_apply, Set.Icc.coe_one, ContinuousMap.comp_apply, g]
      simp [ofEquator, coe_toEquator_apply, Submodule.starProjection_orthogonal_val] }

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

/-- Radial projection onto the equator commutes with the antipodal map. -/
private lemma equatorHomotopyEquiv_neg {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    equatorHomotopyEquiv p ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ =
      -equatorHomotopyEquiv p ⟨x, hx⟩ := by
  ext
  simp only [coe_equatorHomotopyEquiv_apply, coe_neg_sphere, Submodule.coe_neg, map_neg,
    normalize_neg]

/-- Every point of the sphere minus `±p` is joined by a path to its image under the retraction
onto the equator. -/
private lemma zerothHomotopy_mk_equatorHomotopyEquiv_symm
    (x : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ZerothHomotopy.mk ((equatorHomotopyEquiv p).symm (equatorHomotopyEquiv p x)) =
      ZerothHomotopy.mk x :=
  ZerothHomotopy.sound ((equatorHomotopyEquiv p).left_inv.some.evalAt x)

section Circle

variable {p} (hE : finrank ℝ E = 2)
include hE

/-- In dimension two the equator is a zero-sphere. -/
private lemma finrank_orthogonal_span_eq_one : finrank ℝ (ℝ ∙ (p : E))ᗮ = 1 :=
  have : Fact (finrank ℝ E = 1 + 1) := ⟨hE⟩
  Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)

/-- **The two arcs of a punctured circle are distinct.** On the unit circle of a two-dimensional
real inner product space minus two antipodal points `p` and `-p`, a point `x` and its antipode
`-x` lie in distinct path components. -/
theorem zerothHomotopy_mk_neg_ne_of_finrank_eq_two {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ZerothHomotopy.mk (⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ :
        ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) ≠
      ZerothHomotopy.mk ⟨x, hx⟩ := fun h ↦ by
  -- Radial projection onto the equator, a zero-sphere, would join `-y` to `y`.
  have hj := (Quotient.exact h).map (equatorHomotopyEquiv p).continuous
  rw [equatorHomotopyEquiv_neg p hx] at hj
  exact zerothHomotopy_mk_neg_ne (finrank_orthogonal_span_eq_one hE)
    (equatorHomotopyEquiv p ⟨x, hx⟩) (Quotient.sound hj)

/-- **A punctured circle has no third arc.** On the unit circle of a two-dimensional real inner
product space minus two antipodal points `p` and `-p`, every point lies in the path component of
`x` or in that of `-x`. -/
theorem zerothHomotopy_mk_eq_or_eq_neg_of_finrank_eq_two {x : sphere (0 : E) 1}
    (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
    (y : ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) :
    ZerothHomotopy.mk y = ZerothHomotopy.mk ⟨x, hx⟩ ∨
      ZerothHomotopy.mk y =
        ZerothHomotopy.mk ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ := by
  -- The retraction of `y` onto the equator, a zero-sphere, is that of `x` or its antipode.
  have hy := (sphere_eq_pair_of_finrank_eq_one (finrank_orthogonal_span_eq_one hE)
    (equatorHomotopyEquiv p ⟨x, hx⟩).2).subset (equatorHomotopyEquiv p y).2
  rw [← zerothHomotopy_mk_equatorHomotopyEquiv_symm p y]
  rcases hy with hy | hy
  · left
    rw [Subtype.ext hy, zerothHomotopy_mk_equatorHomotopyEquiv_symm]
  · right
    rw [← zerothHomotopy_mk_equatorHomotopyEquiv_symm p
        ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩,
      equatorHomotopyEquiv_neg p hx, Subtype.ext ((Set.mem_singleton_iff.mp hy).trans
        (coe_neg_sphere _).symm)]

end Circle

end TauCeti
