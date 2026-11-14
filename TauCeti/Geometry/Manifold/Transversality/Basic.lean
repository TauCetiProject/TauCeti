/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.MFDeriv.Opens
public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Transversality of maps between manifolds

Two maps `f : X → N` and `g : Y → N` into a common manifold `N` are *transverse* at `(x, y)`
(`TauCeti.IsTransverseAt`) when either `f x ≠ g y`, or `f x = g y` and the images of the manifold
differentials `mfderiv IX IN f x` and `mfderiv IY IN g y` span `TangentSpace IN (f x)` after the
canonical equal-point identification `tangentSpaceCast IN (g y) (f x)`. They are transverse on a
subset `s ⊆ X` (`TauCeti.IsTransverseOn`) when this holds for all `x ∈ s` and all `y : Y`, and
globally transverse (`TauCeti.IsTransverse`) when it holds at every pair `(x, y)`.

This definition is formulated directly in the form consumed by the transverse fibre-product
construction `TauCeti.transverseFiberProductChartedSpace` and by the Pontryagin–Thom normal
coordinate submersion criterion `TauCeti.IsFramedTube.surjective_mfderiv_snd_comp_of_transverse`,
without requiring boundarylessness, finite-dimensionality, or manifold regularity in the predicate
itself. Transversality to an embedded submanifold `Z ↪ N` is recovered by taking `g` to be the
inclusion `Z → N`, and regular values of `f` are recovered by taking `g` to be a constant map.

## Main definitions

* `TauCeti.IsTransverseAt IX IY IN f g x y`: transversality of `f` and `g` at `(x, y)`.
* `TauCeti.IsTransverseOn IX IY IN f g s`: transversality of `f` and `g` along `s ⊆ X`.
* `TauCeti.IsTransverse IX IY IN f g`: global transversality of `f` and `g`.

## Main results

* `TauCeti.isTransverseAt_iff_forall`: pointwise spanning characterization `df u + dg w = v`.
* `TauCeti.IsTransverseAt.symm`, `TauCeti.isTransverseAt_comm`, `TauCeti.IsTransverse.symm`,
  `TauCeti.isTransverse_comm`: symmetry of transversality in the two maps.
* `TauCeti.IsRegularPoint.isTransverseAt_left`, `TauCeti.IsRegularPoint.isTransverseAt_right`,
  `TauCeti.isTransverseAt_const_iff`, `TauCeti.isTransverse_const_iff`: regular points are
  transverse to every map, and transversality to a constant map is regularity.
* `TauCeti.IsTransverseAt.congr_left`, `TauCeti.IsTransverseAt.congr_right`,
  `TauCeti.IsTransverseOn.congr_of_isOpen`: local invariance under `Filter.EventuallyEq` and
  agreement on open sets.
* `TauCeti.isTransverseAt_comp_subtype_val_iff`, `TauCeti.isTransverse_comp_subtype_val_iff`,
  `TauCeti.isTransverseAt_subtype_val_comp_iff`, `TauCeti.isTransverse_subtype_val_comp_iff`:
  restricting the source to an open submanifold, or following maps into an open submanifold of the
  target by its inclusion, preserves transversality without differentiability assumptions.
* `TauCeti.IsTransverseAt.of_comp_left`, `TauCeti.isTransverseAt_comp_diffeomorph_left_iff`,
  `TauCeti.isTransverse_comp_diffeomorph_left_iff`,
  `TauCeti.isTransverseAt_comp_diffeomorph_right_iff`,
  `TauCeti.isTransverse_comp_diffeomorph_right_iff`,
  `TauCeti.isTransverseAt_diffeomorph_comp_iff`, `TauCeti.isTransverse_diffeomorph_comp_iff`:
  monotonicity along differentiable source maps and invariance under source and target
  diffeomorphisms, allowing changes of model with corners.
* `TauCeti.IsTransverseAt.of_boundary`, `TauCeti.IsTransverse.of_interior_and_boundary`: for a
  `C¹`-differentiable map on a half-space manifold `M` over `𝓡∂ (m + 1)`, transversality of the
  boundary restriction `f ∘ Subtype.val` at `p : ∂M` implies ambient transversality at `p`, and
  combining interior and boundary transversality yields global ambient transversality on `M`.

## References

* M. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976, Chapter 3,
  §2.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 6, pp. 143–149.
-/

public section

open Function Filter Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  {EY HY Y : Type*} [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
  {IY : ModelWithCorners 𝕜 EY HY} [TopologicalSpace Y] [ChartedSpace HY Y]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜 EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {f f' : X → N} {g g' : Y → N} {x : X} {y : Y} {s t : Set X}

private theorem tangentSpaceCast_self (a : N) (v : TangentSpace IN a) :
    tangentSpaceCast IN a a v = v :=
  rfl

private theorem tangentSpaceCast_trans (a b c : N) (v : TangentSpace IN a) :
    tangentSpaceCast IN b c (tangentSpaceCast IN a b v) = tangentSpaceCast IN a c v :=
  rfl

private theorem tangentSpaceCast_mfderiv_of_eq {EN' HN' N' : Type*}
    [NormedAddCommGroup EN'] [NormedSpace 𝕜 EN'] [TopologicalSpace HN']
    {IN' : ModelWithCorners 𝕜 EN' HN'} [TopologicalSpace N'] [ChartedSpace HN' N']
    (φ : N → N') {a b : N} (hab : a = b) (v : TangentSpace IN b) :
    tangentSpaceCast IN' (φ b) (φ a) (mfderiv IN IN' φ b v) =
      mfderiv IN IN' φ a (tangentSpaceCast IN b a v) := by
  subst hab
  rfl

variable (IX IY IN) in
/-- Two maps `f : X → N` and `g : Y → N` are *transverse* at `(x, y)` if whenever `f x = g y`,
the images of `mfderiv IX IN f x` and `mfderiv IY IN g y` span `TangentSpace IN (f x)`. -/
def IsTransverseAt (f : X → N) (g : Y → N) (x : X) (y : Y) : Prop :=
  f x = g y →
    (mfderiv IX IN f x).range ⊔
      (((tangentSpaceCast IN (g y) (f x)).toContinuousLinearMap).comp
        (mfderiv IY IN g y)).range = ⊤

variable (IX IY IN) in
/-- Two maps `f : X → N` and `g : Y → N` are *transverse on* `s ⊆ X` if they are transverse at
`(x, y)` for all `x ∈ s` and all `y : Y`. -/
def IsTransverseOn (f : X → N) (g : Y → N) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y, IsTransverseAt IX IY IN f g x y

variable (IX IY IN) in
/-- Two maps `f : X → N` and `g : Y → N` are *transverse* if they are transverse at every pair
`(x, y) : X × Y`. -/
def IsTransverse (f : X → N) (g : Y → N) : Prop :=
  ∀ x y, IsTransverseAt IX IY IN f g x y

/-- Unfolding characterization of `TauCeti.IsTransverseAt`. -/
theorem isTransverseAt_def :
    IsTransverseAt IX IY IN f g x y ↔
      (f x = g y →
        (mfderiv IX IN f x).range ⊔
          (((tangentSpaceCast IN (g y) (f x)).toContinuousLinearMap).comp
            (mfderiv IY IN g y)).range = ⊤) :=
  Iff.rfl

/-- Unfolding characterization of `TauCeti.IsTransverseOn`. -/
theorem isTransverseOn_def :
    IsTransverseOn IX IY IN f g s ↔ ∀ x ∈ s, ∀ y, IsTransverseAt IX IY IN f g x y :=
  Iff.rfl

/-- Unfolding characterization of `TauCeti.IsTransverse`. -/
theorem isTransverse_def :
    IsTransverse IX IY IN f g ↔ ∀ x y, IsTransverseAt IX IY IN f g x y :=
  Iff.rfl

/-- Extract the tangent-space spanning equality from `IsTransverseAt` at an incidence
`f x = g y`. -/
theorem IsTransverseAt.range_sup_eq_top (h : IsTransverseAt IX IY IN f g x y) (hxy : f x = g y) :
    (mfderiv IX IN f x).range ⊔
      (((tangentSpaceCast IN (g y) (f x)).toContinuousLinearMap).comp
        (mfderiv IY IN g y)).range = ⊤ :=
  h hxy

/-- Evaluate `IsTransverseOn` at `x ∈ s` and `y : Y`. -/
theorem IsTransverseOn.isTransverseAt (h : IsTransverseOn IX IY IN f g s) (hx : x ∈ s) (y : Y) :
    IsTransverseAt IX IY IN f g x y :=
  h x hx y

/-- Evaluate `IsTransverse` at `(x, y)`. -/
theorem IsTransverse.isTransverseAt (h : IsTransverse IX IY IN f g) (x : X) (y : Y) :
    IsTransverseAt IX IY IN f g x y :=
  h x y

/-- Pointwise vector characterization of transversality: every tangent vector at `f x` is the sum
of a tangent image from `f` at `x` and a tangent image from `g` at `y`. -/
theorem isTransverseAt_iff_forall :
    IsTransverseAt IX IY IN f g x y ↔
      (f x = g y → ∀ v : TangentSpace IN (f x), ∃ (u : TangentSpace IX x) (w : TangentSpace IY y),
        mfderiv IX IN f x u + tangentSpaceCast IN (g y) (f x) (mfderiv IY IN g y w) = v) := by
  refine forall_congr' fun _ ↦ ?_
  rw [← LinearMap.range_coprod, LinearMap.range_eq_top]
  constructor
  · intro h v
    obtain ⟨⟨u, w⟩, huv⟩ := h v
    exact ⟨u, w, huv⟩
  · intro h v
    obtain ⟨u, w, huv⟩ := h v
    exact ⟨(u, w), huv⟩

/-- Any two maps are vacuously transverse on the empty set. -/
@[simp]
theorem isTransverseOn_empty : IsTransverseOn IX IY IN f g ∅ :=
  fun _ hx ↦ hx.elim

/-- Transversality on `Set.univ` is global transversality. -/
@[simp]
theorem isTransverseOn_univ : IsTransverseOn IX IY IN f g univ ↔ IsTransverse IX IY IN f g := by
  simp [IsTransverseOn, IsTransverse]

/-- Transversality on a union splits as a conjunction. -/
@[simp]
theorem isTransverseOn_union :
    IsTransverseOn IX IY IN f g (s ∪ t) ↔
      IsTransverseOn IX IY IN f g s ∧ IsTransverseOn IX IY IN f g t :=
  ⟨fun h ↦ ⟨fun x hx ↦ h x (Or.inl hx), fun x hx ↦ h x (Or.inr hx)⟩,
    fun h x hx ↦ hx.elim (h.1 x) (h.2 x)⟩

/-- Transversality on `{x}` is transversality at `(x, y)` for all `y`. -/
@[simp]
theorem isTransverseOn_singleton :
    IsTransverseOn IX IY IN f g {x} ↔ ∀ y, IsTransverseAt IX IY IN f g x y := by
  simp [IsTransverseOn]

/-- Global transversality implies transversality on any subset `s`. -/
theorem IsTransverse.isTransverseOn (h : IsTransverse IX IY IN f g) (s : Set X) :
    IsTransverseOn IX IY IN f g s :=
  fun x _ y ↦ h x y

/-- Monotonicity of `IsTransverseOn` in the subset `s`. -/
theorem IsTransverseOn.mono (h : IsTransverseOn IX IY IN f g t) (hst : s ⊆ t) :
    IsTransverseOn IX IY IN f g s :=
  fun x hx ↦ h x (hst hx)

/-- Maps taking distinct values at `(x, y)` are vacuously transverse there. -/
theorem IsTransverseAt.of_ne (h : f x ≠ g y) : IsTransverseAt IX IY IN f g x y :=
  fun hxy ↦ (h hxy).elim

/-- Maps whose images on `s` and `Y` are disjoint are vacuously transverse on `s`. -/
theorem IsTransverseOn.of_disjoint_image_range (h : Disjoint (f '' s) (range g)) :
    IsTransverseOn IX IY IN f g s :=
  fun _ hx _ ↦ .of_ne fun hxy ↦ h.le_bot ⟨⟨_, hx, rfl⟩, ⟨_, hxy.symm⟩⟩

/-- Maps with disjoint ranges are vacuously transverse everywhere. -/
theorem IsTransverse.of_disjoint_range (h : Disjoint (range f) (range g)) :
    IsTransverse IX IY IN f g :=
  fun _ _ ↦ .of_ne fun hxy ↦ h.le_bot ⟨mem_range_self _, ⟨_, hxy.symm⟩⟩

/-- Transversality at a pair of points is symmetric in the two maps. -/
theorem IsTransverseAt.symm (h : IsTransverseAt IX IY IN f g x y) :
    IsTransverseAt IY IX IN g f y x := by
  rw [isTransverseAt_iff_forall] at h ⊢
  intro hyx v
  obtain ⟨u, w, huw⟩ := h hyx.symm (tangentSpaceCast IN (g y) (f x) v)
  refine ⟨w, u, ?_⟩
  have hcast := congrArg (tangentSpaceCast IN (f x) (g y)) huw
  rw [map_add, tangentSpaceCast_trans, tangentSpaceCast_self, tangentSpaceCast_trans,
    tangentSpaceCast_self, add_comm] at hcast
  exact hcast

/-- Symmetry equivalence for `IsTransverseAt`. -/
theorem isTransverseAt_comm : IsTransverseAt IX IY IN f g x y ↔ IsTransverseAt IY IX IN g f y x :=
  ⟨IsTransverseAt.symm, IsTransverseAt.symm⟩

/-- Global transversality is symmetric in the two maps. -/
theorem IsTransverse.symm (h : IsTransverse IX IY IN f g) : IsTransverse IY IX IN g f :=
  fun y x ↦ (h x y).symm

/-- Symmetry equivalence for `IsTransverse`. -/
theorem isTransverse_comm : IsTransverse IX IY IN f g ↔ IsTransverse IY IX IN g f :=
  ⟨IsTransverse.symm, IsTransverse.symm⟩

/-- A regular point of `f` is transverse to every map at every point. -/
theorem IsRegularPoint.isTransverseAt_left (hf : IsRegularPoint IX IN f x) (g : Y → N) (y : Y) :
    IsTransverseAt IX IY IN f g x y := by
  rw [isTransverseAt_iff_forall]
  intro _ v
  obtain ⟨u, rfl⟩ := isRegularPoint_iff.1 hf v
  exact ⟨u, 0, by simp⟩

/-- Every map is transverse at every point to a regular point of `g`. -/
theorem IsRegularPoint.isTransverseAt_right (hg : IsRegularPoint IY IN g y) (f : X → N) (x : X) :
    IsTransverseAt IX IY IN f g x y :=
  (hg.isTransverseAt_left f x).symm

/-- Transversality to a constant map at `(x, y)` is regularity of `f` at `x` whenever `f x = c`. -/
theorem isTransverseAt_const_iff {c : N} :
    IsTransverseAt IX IY IN f (fun _ : Y ↦ c) x y ↔ (f x = c → IsRegularPoint IX IN f x) := by
  rw [isTransverseAt_iff_forall]
  refine forall_congr' fun _ ↦ ?_
  simp only [mfderiv_const, zero_apply, map_zero, add_zero, exists_const,
    isRegularPoint_iff, Surjective]

/-- Transversality to a constant map from a nonempty space is regularity of that value. -/
theorem isTransverse_const_iff [Nonempty Y] {c : N} :
    IsTransverse IX IY IN f (fun _ : Y ↦ c) ↔ IsRegularValue IX IN f c := by
  simp only [IsTransverse, isTransverseAt_const_iff, isRegularValue_iff]
  exact ⟨fun h x hx ↦ h x (Classical.arbitrary Y) hx, fun h x _ hx ↦ h x hx⟩

/-- Transversality at `(x, y)` depends on `f` only through its germ at `x`. -/
theorem IsTransverseAt.congr_left (h : IsTransverseAt IX IY IN f g x y) (hf : f' =ᶠ[𝓝 x] f) :
    IsTransverseAt IX IY IN f' g x y := by
  rw [isTransverseAt_iff_forall] at h ⊢
  intro hf'g v
  have hfx : f' x = f x := hf.eq_of_nhds
  obtain ⟨u, w, huw⟩ := h (hfx.symm.trans hf'g) (tangentSpaceCast IN (f' x) (f x) v)
  refine ⟨u, w, ?_⟩
  have hcast := congrArg (tangentSpaceCast IN (f x) (f' x)) huw
  rw [map_add, tangentSpaceCast_trans, tangentSpaceCast_trans, tangentSpaceCast_self] at hcast
  rwa [hf.mfderiv_eq, ContinuousLinearMap.comp_apply]

/-- Transversality at `(x, y)` depends on `g` only through its germ at `y`. -/
theorem IsTransverseAt.congr_right (h : IsTransverseAt IX IY IN f g x y) (hg : g' =ᶠ[𝓝 y] g) :
    IsTransverseAt IX IY IN f g' x y :=
  (h.symm.congr_left hg).symm

/-- Transversality on an open set depends only on the values of `f` on that open set. -/
theorem IsTransverseOn.congr_of_isOpen (h : IsTransverseOn IX IY IN f g s) (hs : IsOpen s)
    (hfg : EqOn f' f s) : IsTransverseOn IX IY IN f' g s :=
  fun x hx y ↦ (h x hx y).congr_left (eventuallyEq_of_mem (hs.mem_nhds hx) hfg)

/-- Restricting the first map to an open subset preserves transversality at each point, with no
differentiability assumptions. -/
@[simp]
theorem isTransverseAt_comp_subtype_val_iff {U : Opens X} {u : U} :
    IsTransverseAt IX IY IN (f ∘ (Subtype.val : U → X)) g u y ↔
      IsTransverseAt IX IY IN f g (u : X) y := by
  simp only [IsTransverseAt, comp_apply]
  exact forall_congr' fun _ ↦ by
    rw [show (mfderiv IX IN (f ∘ (Subtype.val : U → X)) u).range =
        (mfderiv IX IN f (u : X)).range from
      TauCeti.Manifold.range_mfderiv_comp_subtype_val u]

/-- Restricting the first map to an open subset `U` is globally transverse to `g` if and only if
the ambient map is transverse to `g` on `U`. -/
@[simp]
theorem isTransverse_comp_subtype_val_iff {U : Opens X} :
    IsTransverse IX IY IN (f ∘ (Subtype.val : U → X)) g ↔ IsTransverseOn IX IY IN f g U :=
  ⟨fun h x hx y ↦ isTransverseAt_comp_subtype_val_iff.1 (h ⟨x, hx⟩ y),
    fun h u y ↦ isTransverseAt_comp_subtype_val_iff.2 (h u.1 u.2 y)⟩

private theorem tangentSpaceOpenEquiv_tangentSpaceCast {U : Opens N} {a b : U} (hab : a = b)
    (v : TangentSpace IN a) :
    tangentSpaceCast IN (a : N) (b : N) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := IN) a v) =
      TauCeti.Manifold.tangentSpaceOpenEquiv (I := IN) b (tangentSpaceCast IN a b v) := by
  subst hab
  rfl

/-- Following two maps into an open subset `U` of the target by the ambient inclusion preserves
transversality at each point, with no differentiability assumptions. -/
@[simp]
theorem isTransverseAt_subtype_val_comp_iff {U : Opens N} {f : X → U} {g : Y → U} :
    IsTransverseAt IX IY IN ((Subtype.val : U → N) ∘ f) ((Subtype.val : U → N) ∘ g) x y ↔
      IsTransverseAt IX IY IN f g x y := by
  rw [isTransverseAt_iff_forall, isTransverseAt_iff_forall]
  have hf (u : TangentSpace IX x) :
      mfderiv IX IN ((Subtype.val : U → N) ∘ f) x u =
        TauCeti.Manifold.tangentSpaceOpenEquiv (I := IN) (f x) (mfderiv IX IN f x u) :=
    (TauCeti.Manifold.mfderiv_subtype_val_comp_apply u).trans
      (TauCeti.Manifold.tangentSpaceOpenEquiv_apply _ _).symm
  have hg (w : TangentSpace IY y) :
      mfderiv IY IN ((Subtype.val : U → N) ∘ g) y w =
        TauCeti.Manifold.tangentSpaceOpenEquiv (I := IN) (g y) (mfderiv IY IN g y w) :=
    (TauCeti.Manifold.mfderiv_subtype_val_comp_apply w).trans
      (TauCeti.Manifold.tangentSpaceOpenEquiv_apply _ _).symm
  let e := TauCeti.Manifold.tangentSpaceOpenEquiv (I := IN) (f x)
  constructor
  · intro h hxy v
    obtain ⟨u, w, huw⟩ := h (congrArg Subtype.val hxy) (e v)
    rw [comp_apply, comp_apply, hf, hg, tangentSpaceOpenEquiv_tangentSpaceCast hxy.symm,
      ← map_add] at huw
    exact ⟨u, w, e.injective huw⟩
  · intro h hxy' v'
    have hxy : f x = g y := Subtype.ext hxy'
    obtain ⟨u, w, huw⟩ := h hxy (e.symm v')
    refine ⟨u, w, ?_⟩
    rw [comp_apply, comp_apply, hf, hg, tangentSpaceOpenEquiv_tangentSpaceCast hxy.symm,
      ← map_add, huw, e.apply_symm_apply]

/-- Following two maps into an open subset `U` of the target by the ambient inclusion preserves
global transversality, with no differentiability assumptions. -/
@[simp]
theorem isTransverse_subtype_val_comp_iff {U : Opens N} {f : X → U} {g : Y → U} :
    IsTransverse IX IY IN ((Subtype.val : U → N) ∘ f) ((Subtype.val : U → N) ∘ g) ↔
      IsTransverse IX IY IN f g :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ isTransverseAt_subtype_val_comp_iff

section Transport

variable {EX' HX' X' : Type*} [NormedAddCommGroup EX'] [NormedSpace 𝕜 EX'] [TopologicalSpace HX']
  {IX' : ModelWithCorners 𝕜 EX' HX'} [TopologicalSpace X'] [ChartedSpace HX' X']
  {EY' HY' Y' : Type*} [NormedAddCommGroup EY'] [NormedSpace 𝕜 EY'] [TopologicalSpace HY']
  {IY' : ModelWithCorners 𝕜 EY' HY'} [TopologicalSpace Y'] [ChartedSpace HY' Y']
  {EN' HN' N' : Type*} [NormedAddCommGroup EN'] [NormedSpace 𝕜 EN'] [TopologicalSpace HN']
  {IN' : ModelWithCorners 𝕜 EN' HN'} [TopologicalSpace N'] [ChartedSpace HN' N']
  {n : ℕ∞ω}

/-- If `f ∘ h` is transverse to `g` at `(x', y)` and both `h` at `x'` and `f` at `h x'` are
differentiable, then `f` is transverse to `g` at `(h x', y)`: the tangent image of `f ∘ h` is
contained in that of `f`. -/
theorem IsTransverseAt.of_comp_left {h : X' → X} {x' : X'}
    (ht : IsTransverseAt IX' IY IN (f ∘ h) g x' y) (hf : MDifferentiableAt IX IN f (h x'))
    (hh : MDifferentiableAt IX' IX h x') :
    IsTransverseAt IX IY IN f g (h x') y := by
  intro hxy
  have htop := ht hxy
  rw [mfderiv_comp x' hf hh] at htop
  exact eq_top_mono (sup_le_sup_right (LinearMap.range_comp_le_range _ _) _) htop

/-- Precomposing the first map with a `C^n` diffeomorphism (`n ≠ 0`) preserves transversality at a
point, even across a change of model with corners. -/
theorem isTransverseAt_comp_diffeomorph_left_iff (φ : X' ≃ₘ^n⟮IX', IX⟯ X) (hn : n ≠ 0)
    {x' : X'} :
    IsTransverseAt IX' IY IN (f ∘ φ) g x' y ↔ IsTransverseAt IX IY IN f g (φ x') y := by
  -- Where `f` is not differentiable at `φ x'`, neither is `f ∘ φ` at `x'`, so both differentials
  -- vanish and both sides reduce to the range of `dg_y` alone.
  have hrange : (mfderiv IX' IN (f ∘ φ) x').range = (mfderiv IX IN f (φ x')).range := by
    by_cases hfd : MDifferentiableAt IX IN f (φ x')
    · rw [mfderiv_comp x' hfd (φ.contMDiff.mdifferentiableAt hn)]
      ext v
      simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
      refine ⟨fun ⟨u, hu⟩ ↦ ⟨_, hu⟩, fun ⟨w, hw⟩ ↦ ?_⟩
      obtain ⟨u, rfl⟩ := (φ.isInvertible_mfderiv hn (x := x')).surjective w
      exact ⟨u, hw⟩
    · have hfd' : ¬ MDifferentiableAt IX' IN (f ∘ φ) x' := fun h ↦
        hfd ((((φ.left_inv x').symm ▸ h).comp (φ x')
          (φ.symm.contMDiff.mdifferentiableAt hn)).congr_of_eventuallyEq
            (.of_forall fun z ↦ congrArg f (φ.right_inv z).symm))
      rw [mfderiv_zero_of_not_mdifferentiableAt hfd, mfderiv_zero_of_not_mdifferentiableAt hfd']
      simp
  simp only [IsTransverseAt, comp_apply, hrange]

/-- Precomposing the first map with a `C^n` diffeomorphism (`n ≠ 0`) preserves global
transversality. -/
theorem isTransverse_comp_diffeomorph_left_iff (φ : X' ≃ₘ^n⟮IX', IX⟯ X) (hn : n ≠ 0) :
    IsTransverse IX' IY IN (f ∘ φ) g ↔ IsTransverse IX IY IN f g :=
  ⟨fun h x y ↦ by
    simpa [φ.right_inv x] using
      (isTransverseAt_comp_diffeomorph_left_iff φ hn (x' := φ.symm x)).1 (h (φ.symm x) y),
    fun h x' y ↦ (isTransverseAt_comp_diffeomorph_left_iff φ hn).2 (h (φ x') y)⟩

/-- Precomposing the second map with a `C^n` diffeomorphism (`n ≠ 0`) preserves transversality at a
point, even across a change of model with corners. -/
theorem isTransverseAt_comp_diffeomorph_right_iff (ψ : Y' ≃ₘ^n⟮IY', IY⟯ Y) (hn : n ≠ 0)
    {y' : Y'} :
    IsTransverseAt IX IY' IN f (g ∘ ψ) x y' ↔ IsTransverseAt IX IY IN f g x (ψ y') := by
  rw [isTransverseAt_comm, isTransverseAt_comp_diffeomorph_left_iff ψ hn, isTransverseAt_comm]

/-- Precomposing the second map with a `C^n` diffeomorphism (`n ≠ 0`) preserves global
transversality. -/
theorem isTransverse_comp_diffeomorph_right_iff (ψ : Y' ≃ₘ^n⟮IY', IY⟯ Y) (hn : n ≠ 0) :
    IsTransverse IX IY' IN f (g ∘ ψ) ↔ IsTransverse IX IY IN f g := by
  rw [isTransverse_comm, isTransverse_comp_diffeomorph_left_iff ψ hn, isTransverse_comm]

/-- Postcomposing two differentiable maps with a `C^n` diffeomorphism (`n ≠ 0`) of the target
preserves transversality at `(x, y)`, even across a change of model with corners. -/
theorem isTransverseAt_diffeomorph_comp_iff (χ : N ≃ₘ^n⟮IN, IN'⟯ N') (hn : n ≠ 0)
    (hf : MDifferentiableAt IX IN f x) (hg : MDifferentiableAt IY IN g y) :
    IsTransverseAt IX IY IN' (χ ∘ f) (χ ∘ g) x y ↔ IsTransverseAt IX IY IN f g x y := by
  rw [isTransverseAt_iff_forall, isTransverseAt_iff_forall]
  have hχf := χ.contMDiff.mdifferentiableAt hn (x := f x)
  have hχg := χ.contMDiff.mdifferentiableAt hn (x := g y)
  constructor
  · intro h hxy v
    obtain ⟨u, w, huw⟩ := h (congrArg χ hxy) (mfderiv IN IN' χ (f x) v)
    rw [comp_apply, comp_apply, mfderiv_comp_apply x hχf hf, mfderiv_comp_apply y hχg hg,
      tangentSpaceCast_mfderiv_of_eq χ hxy, ← map_add] at huw
    exact ⟨u, w, (χ.isInvertible_mfderiv hn).injective huw⟩
  · intro h hχxy v'
    have hxy : f x = g y := χ.injective hχxy
    obtain ⟨v, rfl⟩ := (χ.isInvertible_mfderiv hn (x := f x)).surjective v'
    obtain ⟨u, w, huw⟩ := h hxy v
    refine ⟨u, w, ?_⟩
    rw [comp_apply, comp_apply, mfderiv_comp_apply x hχf hf, mfderiv_comp_apply y hχg hg,
      tangentSpaceCast_mfderiv_of_eq χ hxy, ← map_add, huw]

/-- Postcomposing two differentiable maps with a `C^n` diffeomorphism (`n ≠ 0`) of the target
preserves global transversality. -/
theorem isTransverse_diffeomorph_comp_iff (χ : N ≃ₘ^n⟮IN, IN'⟯ N') (hn : n ≠ 0)
    (hf : MDifferentiable IX IN f) (hg : MDifferentiable IY IN g) :
    IsTransverse IX IY IN' (χ ∘ f) (χ ∘ g) ↔ IsTransverse IX IY IN f g :=
  forall_congr' fun x ↦ forall_congr' fun y ↦
    isTransverseAt_diffeomorph_comp_iff χ hn (hf x) (hg y)

end Transport

end General

section HalfSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
  [IsManifold (𝓡∂ (m + 1)) 1 M]
  {EY HY Y : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  {IY : ModelWithCorners ℝ EY HY} [TopologicalSpace Y] [ChartedSpace HY Y]
  {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
  {f : M → N} {g : Y → N}

/-- On a `C¹` half-space manifold `M`, a differentiable map `f : M → N` whose restriction to the
boundary manifold `∂M` is transverse to `g` at `(p, y)` is also ambiently transverse to `g` at
`((p : M), y)`. -/
theorem IsTransverseAt.of_boundary {p : ↥((𝓡∂ (m + 1)).boundary M)} {y : Y}
    (hf : MDifferentiableAt (𝓡∂ (m + 1)) IN f p)
    (hb : IsTransverseAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IY IN
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g p y) :
    IsTransverseAt (𝓡∂ (m + 1)) IY IN f g p y := by
  have := isManifold_boundary (n := m) (k := 1) M one_ne_zero
  exact hb.of_comp_left hf
    (((isSmoothEmbedding_subtypeVal_boundary (n := m) (k := 1) M one_ne_zero).contMDiff
      p).mdifferentiableAt one_ne_zero)

/-- On a `C¹` half-space manifold `M`, if `f : M → N` is differentiable, transverse to `g` on the
manifold interior, and its boundary restriction `f ∘ Subtype.val : ∂M → N` is transverse to `g`,
then `f` is ambiently transverse to `g` on all of `M`. -/
theorem IsTransverse.of_interior_and_boundary (hf : MDifferentiable (𝓡∂ (m + 1)) IN f)
    (hint : IsTransverseOn (𝓡∂ (m + 1)) IY IN f g ((𝓡∂ (m + 1)).interior M))
    (hbdy : IsTransverse 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) IY IN
      (f ∘ (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) g) :
    IsTransverse (𝓡∂ (m + 1)) IY IN f g := by
  rw [← isTransverseOn_univ, ← (𝓡∂ (m + 1)).interior_union_boundary_eq_univ, isTransverseOn_union]
  exact ⟨hint, fun x hx y ↦ IsTransverseAt.of_boundary (hf x) (hbdy ⟨x, hx⟩ y)⟩

end HalfSpace

end TauCeti
