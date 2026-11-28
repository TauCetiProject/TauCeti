/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.ExtSegment
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.IdealBoundary
import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Geometry

/-!
# Hyperbolic convex hulls of ideal sets

The ideal convex hull is the intersection in the upper half-plane of the closed geodesic
half-planes whose ideal arcs contain the given set. It is contained in every closed
geodesically convex set whose ideal boundary contains the given set. It contains the
geodesic segments, rays and complete lines between its finite points and points in the
closure of the prescribed ideal set. With at least two prescribed ideal points, the
ideal boundary of the hull is the closure of that set. Three distinct ideal points give
a hull with nonempty interior.

For the use of this construction for Fuchsian groups, see C. Series, *A crash course on
Kleinian groups*, Rend. Ist. Mat. Univ. Trieste 37 (2005), pp. 32–33, The convex core.
-/

public noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups OnePoint Pointwise

namespace TauCeti.UpperHalfPlane

/-- The intersection of the closed hyperbolic half-planes whose ideal boundaries contain `S`. -/
def idealConvexHull (S : Set (OnePoint ℝ)) : Set ℍ :=
  ⋂ g : PSL(2, ℝ), ⋂ (_ : S ⊆ idealBoundary (closure (leftHalfPlane g))),
    closure (leftHalfPlane g)

/-- Membership in the ideal convex hull is tested by all closed half-planes containing the
prescribed set at infinity. -/
theorem mem_idealConvexHull_iff {S : Set (OnePoint ℝ)} {z : ℍ} :
    z ∈ idealConvexHull S ↔
      ∀ g : PSL(2, ℝ), S ⊆ idealBoundary (closure (leftHalfPlane g)) →
        z ∈ closure (leftHalfPlane g) := by
  simp [idealConvexHull]

/-- Enlarging the prescribed set at infinity enlarges its ideal convex hull. -/
@[gcongr]
theorem idealConvexHull_mono : Monotone idealConvexHull := by
  intro S T h z hz
  exact mem_idealConvexHull_iff.2 fun g hg ↦ mem_idealConvexHull_iff.1 hz g (h.trans hg)

/-- The ideal convex hull is closed in the upper half-plane. -/
theorem isClosed_idealConvexHull (S : Set (OnePoint ℝ)) : IsClosed (idealConvexHull S) :=
  isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ isClosed_closure

/-- Closing the prescribed ideal set does not change its hull. -/
@[simp]
theorem idealConvexHull_closure (S : Set (OnePoint ℝ)) :
    idealConvexHull (closure S) = idealConvexHull S := by
  apply (idealConvexHull_mono subset_closure).antisymm'
  intro z hz
  exact mem_idealConvexHull_iff.2 fun g hg ↦
    mem_idealConvexHull_iff.1 hz g ((isClosed_idealBoundary _).closure_subset_iff.2 hg)

/-- The ideal hull is contained in every closed geodesically convex set whose ideal
boundary contains the prescribed set. -/
theorem idealConvexHull_minimal {S : Set (OnePoint ℝ)} {C : Set ℍ} (hC : IsClosed C)
    (hconv : ∀ ⦃p q⦄, p ∈ C → q ∈ C → geodesicSegment p q ⊆ C)
    (hS : S ⊆ idealBoundary C) : idealConvexHull S ⊆ C := by
  intro z hz
  by_contra h
  obtain ⟨g, hg, hzg⟩ := exists_subset_closure_leftHalfPlane_of_isClosed hC hconv h
  exact hzg (mem_idealConvexHull_iff.1 hz g (hS.trans (idealBoundary_mono hg)))

/-- The ideal convex hull commutes with the projective action. -/
theorem idealConvexHull_smul (g : PSL(2, ℝ)) (S : Set (OnePoint ℝ)) :
    idealConvexHull (g • S) = g • idealConvexHull S := by
  symm
  calc
    g • idealConvexHull S =
        ⋂ k : PSL(2, ℝ), ⋂ (_ : S ⊆ idealBoundary (closure (leftHalfPlane k))),
          closure (leftHalfPlane (g * k)) := by
      simp_rw [idealConvexHull, Set.smul_set_iInter, ← closure_smul, smul_leftHalfPlane]
    _ = ⋂ k : PSL(2, ℝ),
        ⋂ (_ : g • S ⊆ idealBoundary (closure (leftHalfPlane (g * k)))),
          closure (leftHalfPlane (g * k)) := by
      congr 1
      funext k
      rw [← smul_leftHalfPlane, closure_smul, idealBoundary_smul,
        Set.smul_set_subset_smul_set_iff]
    _ = idealConvexHull (g • S) := by
      rw [idealConvexHull]
      exact (mul_left_surjective g).iInter_comp fun k : PSL(2, ℝ) ↦
        ⋂ (_ : g • S ⊆ idealBoundary (closure (leftHalfPlane k))), closure (leftHalfPlane k)

/-- The geodesic piece between two points of the hull, allowing endpoints in `closure S`
at infinity, is contained in the hull. -/
theorem extGeodesicSegment_subset_idealConvexHull {S : Set (OnePoint ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hp : Sum.elim (· ∈ idealConvexHull S) (· ∈ closure S) p)
    (hq : Sum.elim (· ∈ idealConvexHull S) (· ∈ closure S) q) :
    extGeodesicSegment p q ⊆ idealConvexHull S := by
  intro z hz
  refine mem_idealConvexHull_iff.2 fun g hg ↦ ?_
  have point (r : ℍ ⊕ OnePoint ℝ) (hr : Sum.elim (· ∈ idealConvexHull S) (· ∈ closure S) r) :
      r ∈ extClosedLeftHalfPlane g := by
    rcases r with w | ξ
    · exact inl_mem_extClosedLeftHalfPlane_iff.2 (mem_idealConvexHull_iff.1 hr g hg)
    · exact mem_idealBoundary_closure_leftHalfPlane_iff.1
        (((isClosed_idealBoundary _).closure_subset_iff.2 hg) hr)
  exact extGeodesicSegment_subset_closure_leftHalfPlane (point p hp) (point q hq) hz

/-- A full geodesic whose ideal endpoints lie in `closure S` lies in its ideal convex hull. -/
theorem range_geodesicLine_subset_idealConvexHull {S : Set (OnePoint ℝ)} {g : PSL(2, ℝ)}
    (h₀ : g • ((0 : ℝ) : OnePoint ℝ) ∈ closure S)
    (hInf : g • (∞ : OnePoint ℝ) ∈ closure S) :
    range (geodesicLine g) ⊆ idealConvexHull S := by
  rw [range_geodesicLine_eq_extGeodesicSegment]
  exact extGeodesicSegment_subset_idealConvexHull h₀ hInf

/-- With at least two prescribed ideal points, every one is an ideal point of the hull. -/
theorem subset_idealBoundary_idealConvexHull {S : Set (OnePoint ℝ)} (hS : S.Nontrivial) :
    S ⊆ idealBoundary (idealConvexHull S) := by
  intro ξ hξ
  obtain ⟨η, hη, hηξ⟩ := hS.exists_ne ξ
  obtain ⟨g, hg₀, hgInf⟩ := exists_smul_zero_eq_and_smul_infty_eq hηξ.symm
  have hg := range_geodesicLine_subset_idealConvexHull (subset_closure (hg₀ ▸ hξ))
    (subset_closure (hgInf ▸ hη))
  apply idealBoundary_mono hg
  rw [idealBoundary_range_geodesicLine, hg₀, hgInf]
  exact mem_insert _ _

private theorem coe_mem_of_mem_idealBoundary_idealConvexHull {S : Set (OnePoint ℝ)}
    (hS : IsClosed S) {x : ℝ} (hx : (x : OnePoint ℝ) ∈ idealBoundary (idealConvexHull S)) :
    (x : OnePoint ℝ) ∈ S := by
  by_contra hxS
  obtain ⟨a, b, hxab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((hS.isOpen_compl.preimage OnePoint.continuous_coe).mem_nhds hxS)
  have hab := hxab.1.trans hxab.2
  obtain ⟨g, ha, hb⟩ := exists_smul_zero_eq_and_smul_infty_eq
    (OnePoint.coe_injective.ne hab.ne)
  have hsg : S ⊆ idealBoundary (closure (leftHalfPlane g)) := by
    rw [idealBoundary_closure_leftHalfPlane_eq_compl_image_coe_Ioo hab ha hb]
    rintro _ hξ ⟨y, hy, rfl⟩
    exact hsub hy hξ
  have h := idealBoundary_mono (fun _ hz ↦ mem_idealConvexHull_iff.1 hz g hsg) hx
  rw [idealBoundary_closure_leftHalfPlane_eq_compl_image_coe_Ioo hab ha hb] at h
  exact h (mem_image_of_mem _ hxab)

private theorem idealBoundary_idealConvexHull_subset_of_isClosed {S : Set (OnePoint ℝ)}
    (hS : IsClosed S) : idealBoundary (idealConvexHull S) ⊆ S := by
  intro ξ hξ
  induction ξ using OnePoint.rec with
  | coe x => exact coe_mem_of_mem_idealBoundary_idealConvexHull hS hξ
  | infty =>
    have h : pslS • (∞ : OnePoint ℝ) ∈ idealBoundary (idealConvexHull (pslS • S)) := by
      rw [idealConvexHull_smul, idealBoundary_smul, Set.smul_mem_smul_set_iff]
      exact hξ
    rw [pslS_smul_infty] at h
    let : ContinuousConstSMul PSL(2, ℝ) (OnePoint ℝ) :=
      ContMDiffConstSMul.continuousConstSMul (I := 𝓘(ℝ)) ω
    have h' := coe_mem_of_mem_idealBoundary_idealConvexHull (hS.smul _) h
    rwa [← pslS_smul_infty, Set.smul_mem_smul_set_iff] at h'

/-- Every ideal point of the hull lies in the closure of the prescribed ideal set. -/
theorem idealBoundary_idealConvexHull_subset (S : Set (OnePoint ℝ)) :
    idealBoundary (idealConvexHull S) ⊆ closure S := by
  simpa only [idealConvexHull_closure] using
    idealBoundary_idealConvexHull_subset_of_isClosed (S := closure S) isClosed_closure

/-- The ideal boundary of the hull of a set with at least two points is its closure. -/
theorem idealBoundary_idealConvexHull {S : Set (OnePoint ℝ)} (h₂ : S.Nontrivial) :
    idealBoundary (idealConvexHull S) = closure S :=
  (idealBoundary_idealConvexHull_subset S).antisymm
    ((isClosed_idealBoundary _).closure_subset_iff.2 (subset_idealBoundary_idealConvexHull h₂))

/-- The hull contains all of the upper half-plane when all ideal points are prescribed. -/
@[simp]
theorem idealConvexHull_univ : idealConvexHull (univ : Set (OnePoint ℝ)) = univ := by
  apply eq_univ_of_forall
  intro z
  refine mem_idealConvexHull_iff.2 fun g hg ↦ ?_
  have h := hg (mem_univ (g • (1 : ℝ) : OnePoint ℝ))
  rw [mem_idealBoundary_closure_leftHalfPlane_iff_inv_smul_mem, inv_smul_smul] at h
  rw [mem_idealBoundary_closure_leftHalfPlane_iff, inr_mem_extClosedLeftHalfPlane_iff] at h
  norm_num [coe_mem_boundaryLeftHalfPlane_iff, sideForm_one] at h

/-- The ideal hull is full exactly when the prescribed ideal set is dense. -/
theorem idealConvexHull_eq_univ_iff {S : Set (OnePoint ℝ)} :
    idealConvexHull S = univ ↔ Dense S := by
  rw [dense_iff_closure_eq]
  refine ⟨fun h ↦ eq_univ_of_forall fun ξ ↦ ?_, fun h ↦ ?_⟩
  · exact idealBoundary_idealConvexHull_subset S (by rw [h, idealBoundary_univ]; trivial)
  · rw [← idealConvexHull_closure, h, idealConvexHull_univ]

private theorem mem_idealConvexHull_of_re_eq_of_im_le {S : Set (OnePoint ℝ)}
    (hInf : (∞ : OnePoint ℝ) ∈ S) {w z : ℍ} (hw : w ∈ idealConvexHull S)
    (hre : z.re = w.re) (him : w.im ≤ z.im) : z ∈ idealConvexHull S := by
  apply extGeodesicSegment_subset_idealConvexHull (p := .inl w) (q := .inr ∞) hw
    (subset_closure hInf)
  rw [extGeodesicSegment_inl_inr]
  exact UpperHalfPlane.mem_image_geodesicLine_rayToward_inr_infty_iff.2 ⟨hre, him⟩

private theorem interior_idealConvexHull_nonempty_of_infty_mem {S : Set (OnePoint ℝ)}
    (hInf : (∞ : OnePoint ℝ) ∈ S) {a b : ℝ} (ha : (a : OnePoint ℝ) ∈ S)
    (hb : (b : OnePoint ℝ) ∈ S) (hab : a < b) :
    (interior (idealConvexHull S)).Nonempty := by
  obtain ⟨g, hga, hgb⟩ := exists_smul_zero_eq_and_smul_infty_eq (OnePoint.coe_injective.ne hab.ne)
  obtain ⟨κ, -, hform⟩ := exists_sideForm_eq_of_smul_zero_of_smul_infty hga hgb
  let U : Set ℍ := {z | z.re ∈ Ioo a b ∧ (b - a) / 2 < z.im}
  have hopen : IsOpen U :=
    (isOpen_Ioo.preimage UpperHalfPlane.continuous_re).inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im)
  have hsub : U ⊆ idealConvexHull S := by
    intro z hz
    have hz' : z.re ∈ Ioo a b ∧ (b - a) / 2 < z.im := hz
    let w : ℍ := ⟨⟨z.re, Real.sqrt ((z.re - a) * (b - z.re))⟩,
      Real.sqrt_pos.2 (mul_pos (sub_pos.2 hz'.1.1) (sub_pos.2 hz'.1.2))⟩
    have hwSq : w.im ^ 2 = (z.re - a) * (b - z.re) :=
      Real.sq_sqrt (mul_nonneg (sub_nonneg.2 hz'.1.1.le) (sub_nonneg.2 hz'.1.2.le))
    have hwRe : w.re = z.re := rfl
    have hwLine : w ∈ range (geodesicLine g) := by
      rw [mem_range_geodesicLine_iff_sideForm_eq_zero, hform]
      have hc : Complex.normSq ((w : ℂ) - ((a + b) / 2 : ℝ)) = ((b - a) / 2) ^ 2 := by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hwRe]
        nlinarith only [hwSq]
      rw [hc, sub_self, mul_zero]
    apply mem_idealConvexHull_of_re_eq_of_im_le hInf
      (range_geodesicLine_subset_idealConvexHull (subset_closure (hga ▸ ha))
        (subset_closure (hgb ▸ hb)) hwLine) hwRe.symm
    have hBound : w.im ≤ (b - a) / 2 := by
      refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by linarith))
      nlinarith only [hwSq, sq_nonneg (z.re - (a + b) / 2)]
    exact hBound.trans hz'.2.le
  refine ⟨⟨⟨(a + b) / 2, b - a⟩, sub_pos.2 hab⟩, interior_maximal hsub hopen ?_⟩
  exact ⟨⟨by dsimp; linarith, by dsimp; linarith⟩, by dsimp; linarith⟩

/-- Three distinct prescribed ideal points suffice for the hull to have nonempty interior. -/
theorem interior_idealConvexHull_nonempty {S : Set (OnePoint ℝ)} (hS : 3 ≤ S.encard) :
    (interior (idealConvexHull S)).Nonempty := by
  obtain ⟨f, hf, hfi⟩ := (Set.le_encard_iff_exists_fin_injective S 3).1 hS
  obtain ⟨g, hg₀, hgInf⟩ := exists_smul_zero_eq_and_smul_infty_eq
    (hfi.ne (by decide : (0 : Fin 3) ≠ 2))
  have hzero : ((0 : ℝ) : OnePoint ℝ) ∈ g⁻¹ • S := by
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, hg₀]
    exact hf 0
  have hInf : (∞ : OnePoint ℝ) ∈ g⁻¹ • S := by
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, hgInf]
    exact hf 2
  have hne : g⁻¹ • f 1 ≠ (∞ : OnePoint ℝ) := by
    intro h
    have eq := congrArg (fun ξ : OnePoint ℝ ↦ g • ξ) h
    rw [smul_inv_smul, hgInf] at eq
    exact hfi.ne (by decide : (1 : Fin 3) ≠ 2) eq
  obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.1 hne
  have hB : (b : OnePoint ℝ) ∈ g⁻¹ • S := hb ▸ Set.smul_mem_smul_set (hf 1)
  have hb₀ : b ≠ 0 := by
    rintro rfl
    have eq := congrArg (fun ξ : OnePoint ℝ ↦ g • ξ) hb
    rw [hg₀, smul_inv_smul] at eq
    exact hfi.ne (by decide : (0 : Fin 3) ≠ 1) eq
  have h : (interior (idealConvexHull (g⁻¹ • S))).Nonempty := by
    rcases hb₀.lt_or_gt with hneg | hpos
    · exact interior_idealConvexHull_nonempty_of_infty_mem hInf hB hzero hneg
    · exact interior_idealConvexHull_nonempty_of_infty_mem hInf hzero hB hpos
  rw [idealConvexHull_smul, interior_smul, Set.smul_set_nonempty] at h
  exact h

end TauCeti.UpperHalfPlane
