/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import TauCeti.Topology.Connected.AtInfinity

import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.BoundaryPrevertex
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.ParallelEnd
import TauCeti.Analysis.Complex.Conformal.Reflection.Principle
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Distinct accesses to infinity lie in distinct ends

Let `f` be a conformal map of the upper half-plane onto an unbounded domain `U`, and let
`g = (f - q)⁻¹` be its inverted coordinate, continuous on the closed upper half-plane.  The real
zeros of `g` are the boundary parameters at which `f` tends to infinity, and near each of them `f`
takes its values in a single end of `U`
(`TauCeti.exists_eventually_mem_of_inverted_coordinate_eq_zero`).

This file shows that two distinct zeros cannot share an end, provided the end is preconnected at
infinity inside `U` (`TauCeti.IsPreconnectedAtInfinityIn`): outside each bounded set, far out it
lies in a preconnected subset of `U`, as the far part of a half-strip or of a sector of opening
less than `2 * π` contained in `U` does.  The argument is a crosscut argument.  Two real
parameters on either side of one zero at which `g` does not vanish (they exist because a zero-free
holomorphic function cannot vanish on a whole boundary interval,
`TauCeti.exists_lt_lt_ne_zero_of_ne_zero`) span a semicircle in the closed upper half-plane on
which `g` is bounded away from zero, so `f` is bounded there.  The far part of the end avoids the
image of that semicircle, so its preimage under `f`, being preconnected, lies on one side of the
semicircle, and it cannot contain points near both zeros.

Consequently the zeros of `g` are matched injectively to the ends of `U`; when there are only
finitely many ends, as for a polygonal domain, `g` has only finitely many zeros.  This is the
bookkeeping that attaches one vertex at infinity of the Schwarz--Christoffel formula
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` to each end of a
polygonal domain with several ends.

## Main results

* `TauCeti.eq_of_eventually_mem_of_inverted_coordinate_eq_zero`: two zeros of the inverted
  coordinate near which `f` takes values in the same end coincide.
* `TauCeti.exists_injective_end_of_inverted_coordinate_eq_zero`: the zeros of the inverted
  coordinate are matched injectively to the ends.
* `TauCeti.finite_setOf_inverted_coordinate_eq_zero`: with finitely many ends, the inverted
  coordinate has finitely many zeros.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {f g : ℂ → ℂ} {q : ℂ} {U : Set ℂ}

/-- The semicircle in the closed upper half-plane over a real interval `[y₁, y₂]` at whose ends the
inverted coordinate `g = (f - q)⁻¹` is nonzero is a crosscut on which `f` is bounded. -/
private theorem exists_norm_le_on_sphere_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) {y₁ y₂ : ℝ} (hy₁ : g y₁ ≠ 0) (hy₂ : g y₂ ≠ 0) :
    ∃ M : ℝ, ∀ z ∈ sphere (((y₁ + y₂) / 2 : ℝ) : ℂ) ((y₂ - y₁) / 2),
      z ∈ upperHalfPlaneSet → ‖f z‖ ≤ M := by
  set K := sphere (((y₁ + y₂) / 2 : ℝ) : ℂ) ((y₂ - y₁) / 2) ∩ {z : ℂ | 0 ≤ z.im}
  -- `g` has no zeros on the semicircle: its only real points are `y₁` and `y₂`
  have hK : ∀ z ∈ K, g z ≠ 0 := by
    rintro z ⟨hzs, hz⟩
    rcases (show 0 ≤ z.im from hz).lt_or_eq with hz | hz
    · exact hgne z hz
    have hzx : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [← hz])
    rw [mem_sphere, dist_of_im_eq (by simp [← hz]), ofReal_re, Real.dist_eq] at hzs
    rcases abs_eq (by linarith [abs_nonneg (z.re - (y₁ + y₂) / 2)]) |>.mp hzs with h | h
    · rw [← hzx, show z.re = y₂ by linarith]; exact hy₂
    · rw [← hzx, show z.re = y₁ by linarith]; exact hy₁
  obtain ⟨M, hM⟩ := ((isCompact_sphere (((y₁ + y₂) / 2 : ℝ) : ℂ) _).inter_right
    (isClosed_le continuous_const Complex.continuous_im)).exists_bound_of_continuousOn
      ((hgc.mono inter_subset_right).inv₀ hK)
  refine ⟨‖q‖ + M, fun z hz hzH => ?_⟩
  calc ‖f z‖ = ‖q + (g z)⁻¹‖ := by rw [eq_add_inv_of_inverted_coordinate hgf hzH]
    _ ≤ ‖q‖ + M := (norm_add_le _ _).trans (by gcongr; exact hM z ⟨hz, le_of_lt hzH⟩)

/-- **Distinct accesses to infinity lie in distinct ends.**  Let `f` be injective on the upper
half-plane, with inverted coordinate `g = (f - q)⁻¹` continuous on the closed upper half-plane and
holomorphic and nonzero in its interior.  Let `E` be preconnected at infinity inside the image of
`f`: outside each bounded set, far out `E` lies in a preconnected subset of that image.  If near
two real zeros `x` and `x'` of `g` the map `f` takes its values in `E`, then `x = x'`. -/
theorem eq_of_eventually_mem_of_inverted_coordinate_eq_zero
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hfi : InjOn f upperHalfPlaneSet) {E : Set ℂ}
    (hE : IsPreconnectedAtInfinityIn (f '' upperHalfPlaneSet) E)
    {x x' : ℝ} (hx : g x = 0) (hx' : g x' = 0)
    (hfx : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ), f z ∈ E)
    (hfx' : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x' : ℂ), f z ∈ E) :
    x = x' := by
  by_contra hxx'
  -- the crosscut: a semicircle about `x`, with nonzero real ends, leaving out `x'`
  obtain ⟨y₁, y₂, h₁, h₁', h₂, h₂', hy₁, hy₂⟩ :=
    exists_lt_lt_ne_zero_of_ne_zero (x := x) (abs_pos.mpr (sub_ne_zero.mpr hxx'))
      (hgc.mono inter_subset_right) (hgd.mono inter_subset_right) fun z _ hz => hgne z hz
  set m : ℂ := (((y₁ + y₂) / 2 : ℝ) : ℂ)
  set s : ℝ := (y₂ - y₁) / 2 with hs
  have hdist (y : ℝ) : dist (y : ℂ) m = |y - (y₁ + y₂) / 2| := by
    rw [dist_of_im_eq (by simp [m]), ofReal_re, ofReal_re, Real.dist_eq]
  have hxm : (x : ℂ) ∈ ball m s := by
    rw [mem_ball, hdist, abs_sub_lt_iff]
    constructor <;> linarith
  have hx'm : (x' : ℂ) ∈ (closedBall m s)ᶜ := by
    rw [mem_compl_iff, mem_closedBall, hdist, not_le, lt_abs]
    rcases lt_or_gt_of_ne hxx' with h | h
    · rw [abs_of_neg (by linarith)] at h₂'
      left; linarith
    · rw [abs_of_pos (by linarith)] at h₁
      right; linarith
  -- far out, the end lies in a preconnected set avoiding the image of the semicircle
  obtain ⟨M, hM⟩ := exists_norm_le_on_sphere_of_inverted_coordinate hgc hgf hgne hy₁ hy₂
  obtain ⟨C, hCU, hCc, hCM, hEC⟩ :=
    isPreconnectedAtInfinityIn_iff.mp hE (closedBall 0 M) isBounded_closedBall
  -- it contains values of `f` near `x`, inside the semicircle, and near `x'`, outside it
  have hnear {y : ℝ} (hy : g y = 0) (hfy : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (y : ℂ), f z ∈ E)
      {V : Set ℂ} (hV : IsOpen V) (hyV : (y : ℂ) ∈ V) :
      ∃ z ∈ V ∩ upperHalfPlaneSet, f z ∈ C := by
    have := Real.nhdsWithin_upperHalfPlaneSet_neBot y
    obtain ⟨z, hzC, hzE, hzV, hzH⟩ :=
      ((tendsto_cobounded_of_inverted_boundary_eq_zero (hgc _ (by simp)) hgf hgne hy).eventually
        hEC |>.and (hfy.and ((eventually_nhdsWithin_of_eventually_nhds
          (hV.eventually_mem hyV)).and eventually_mem_nhdsWithin))).exists
    exact ⟨z, ⟨hzV, hzH⟩, hzC hzE⟩
  obtain ⟨z, hzD, hzC⟩ := hnear hx hfx isOpen_ball hxm
  obtain ⟨z', ⟨hz'm, hz'H⟩, hzC'⟩ := hnear hx' hfx' isClosed_closedBall.isOpen_compl hx'm
  -- pulled back by the continuous inverse of `f`, it would cross the semicircle
  have hfd : DifferentiableOn ℂ f upperHalfPlaneSet :=
    differentiableOn_of_inverted_coordinate hgd hgf hgne
  have hinv := hfi.leftInvOn_invFunOn
  have hC : invFunOn f upperHalfPlaneSet '' C ⊆ ball m s ∪ (closedBall m s)ᶜ := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨y, hyH, rfl⟩ := hCU hw
    rw [hinv hyH]
    by_cases hyb : y ∈ ball m s
    · exact Or.inl hyb
    refine Or.inr fun hyc => disjoint_left.mp hCM hw (mem_closedBall_zero_iff.mpr (hM y ?_ hyH))
    rw [← closedBall_sdiff_ball]
    exact ⟨hyc, hyb⟩
  have hsub := ((hCc.image _ ((hfd.invFunOn isOpen_upperHalfPlaneSet hfi).continuousOn.mono
    hCU)).subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
    (disjoint_compl_right.mono_left ball_subset_closedBall) hC
    ⟨z, ⟨f z, hzC, hinv hzD.2⟩, hzD.1⟩) ⟨f z', hzC', hinv hz'H⟩
  exact hz'm (ball_subset_closedBall hsub)

/-- **The zeros of the inverted coordinate are matched injectively to the ends.**  Let `f` be a
bijection of the upper half-plane onto `U` whose inverted coordinate `g = (f - q)⁻¹` is continuous
on the closed upper half-plane and holomorphic and nonzero in its interior.  Suppose that far out
`U` is covered by pairwise disjoint open ends `E i`, each preconnected at infinity inside `U`.  Then
there is an injective assignment of an end to each real zero `x` of `g` such that near `x` the map
`f` takes its values in the assigned end. -/
theorem exists_injective_end_of_inverted_coordinate_eq_zero {ι : Type*} {E : ι → Set ℂ} {R : ℝ}
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hfU : BijOn f upperHalfPlaneSet U)
    (hEo : ∀ i, IsOpen (E i)) (hEd : Pairwise (Disjoint on E))
    (hEU : ∀ w ∈ U, R < ‖w‖ → ∃ i, w ∈ E i)
    (hE : ∀ i, IsPreconnectedAtInfinityIn U (E i)) :
    ∃ φ : {x : ℝ // g x = 0} → ι, Injective φ ∧
      ∀ x, ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((x : ℝ) : ℂ), f z ∈ E (φ x) := by
  choose φ hφ using fun x : {x : ℝ // g x = 0} =>
    exists_eventually_mem_of_inverted_coordinate_eq_zero hgc hgf hgne x.2 hfU.mapsTo hEo hEd hEU
  refine ⟨φ, fun x x' h => Subtype.ext ?_, hφ⟩
  exact eq_of_eventually_mem_of_inverted_coordinate_eq_zero hgc hgd hgf hgne hfU.injOn
    (hfU.image_eq ▸ hE (φ x)) x.2 x'.2 (hφ x) (h ▸ hφ x')

/-- **Finitely many ends give finitely many accesses to infinity.**  Under the hypotheses of
`TauCeti.exists_injective_end_of_inverted_coordinate_eq_zero`, if there are only finitely many
ends, then the inverted coordinate has only finitely many real zeros. -/
theorem finite_setOf_inverted_coordinate_eq_zero {ι : Type*} [Finite ι] {E : ι → Set ℂ} {R : ℝ}
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hfU : BijOn f upperHalfPlaneSet U)
    (hEo : ∀ i, IsOpen (E i)) (hEd : Pairwise (Disjoint on E))
    (hEU : ∀ w ∈ U, R < ‖w‖ → ∃ i, w ∈ E i)
    (hE : ∀ i, IsPreconnectedAtInfinityIn U (E i)) :
    {x : ℝ | g x = 0}.Finite := by
  obtain ⟨φ, hφ, -⟩ :=
    exists_injective_end_of_inverted_coordinate_eq_zero hgc hgd hgf hgne hfU hEo hEd hEU hE
  have : Finite {x : ℝ // g x = 0} := Finite.of_injective φ hφ
  exact Set.toFinite _

end TauCeti
