/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.KreinMilman
import TauCeti.Analysis.Convex.Topology

/-!
# Extreme points maximizing a continuous linear functional, and Milman's converse

In a Hausdorff locally convex real space, a continuous linear functional `l` attains its maximum
on a nonempty compact set `s` at an extreme point of `s`
(`IsCompact.exists_mem_extremePoints_isMaxOn`), and likewise its minimum
(`IsCompact.exists_mem_extremePoints_isMinOn`). The maximizers of `l` form a compact exposed
subset of `s`, which has an extreme point by the Krein–Milman lemma
(`IsCompact.extremePoints_nonempty`), and extreme points of an extreme subset are extreme points
of `s`.

For a polytope this says that a linear functional is minimized at a vertex. This is what makes the
normal cones at the vertices of a polytope cover the whole space.

Milman's converse to the Krein–Milman theorem
(`TauCeti.extremePoints_closure_convexHull_subset_closure`): if the closed convex hull of a set `F`
is compact, every extreme point of it lies in the closure of `F`. Mathlib's
`closure_convexHull_extremePoints` says that a compact convex set is the closed convex hull of its
extreme points; the converse says that the closure of the extreme points is the smallest closed set
whose closed convex hull is the given set. In representation theory it shows that an extreme point
of a compact convex set of positive-definite functions, approximated by convex combinations of a
family of such functions, is approximated by single members of the family.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Section 32 (maxima of
  convex functions at extreme points, in finite dimension).
* R. R. Phelps, *Lectures on Choquet's Theorem*, second edition, Lecture Notes in Mathematics 1757,
  Springer, 2001, Proposition 1.5 (Milman's converse).
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press,
  2008, proof of Proposition F.1.4.
-/

public section

open Set
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s : Set E}

/-- A continuous linear functional attains its maximum on a nonempty compact set at an extreme
point of the set. -/
theorem IsCompact.exists_mem_extremePoints_isMaxOn (hs : IsCompact s) (hne : s.Nonempty)
    (l : StrongDual ℝ E) : ∃ x ∈ s.extremePoints ℝ, IsMaxOn l s x := by
  obtain ⟨x₀, hx₀, hmax⟩ := hs.exists_isMaxOn hne l.continuous.continuousOn
  -- The maximizers of `l` form a nonempty compact exposed subset of `s`.
  have hexp : IsExposed ℝ s (l.toExposed s) := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨x, hx⟩ := (hexp.isCompact hs).extremePoints_nonempty ⟨x₀, hx₀, fun w hw ↦ hmax hw⟩
  exact ⟨x, hexp.isExtreme.extremePoints_subset_extremePoints hx,
    fun w hw ↦ (extremePoints_subset hx).2 w hw⟩

/-- A continuous linear functional attains its minimum on a nonempty compact set at an extreme
point of the set. -/
theorem IsCompact.exists_mem_extremePoints_isMinOn (hs : IsCompact s) (hne : s.Nonempty)
    (l : StrongDual ℝ E) : ∃ x ∈ s.extremePoints ℝ, IsMinOn l s x := by
  obtain ⟨x, hx, hmax⟩ := hs.exists_mem_extremePoints_isMaxOn hne (-l)
  exact ⟨x, hx, fun w hw ↦ by simpa using hmax hw⟩

namespace TauCeti

/-- **Milman's converse to the Krein–Milman theorem**: in a Hausdorff locally convex real space, if
the closed convex hull of a set `F` is compact, then every extreme point of that closed convex hull
lies in the closure of `F`.

Compactness cannot be dropped: in `ℓ²` the closed convex hull of the standard basis vectors
contains `0` as an extreme point, but `0` is not in the closure of the basis vectors. -/
theorem extremePoints_closure_convexHull_subset_closure {F : Set E}
    (hF : IsCompact (closure (convexHull ℝ F))) :
    (closure (convexHull ℝ F)).extremePoints ℝ ⊆ closure F := by
  set C := closure (convexHull ℝ F)
  set K := closure F
  have hCconv : Convex ℝ C := (convex_convexHull ℝ F).closure
  have hKC : K ⊆ C := closure_mono (subset_convexHull ℝ F)
  intro x hx
  by_contra hxK
  -- A closed convex neighbourhood `U` of `0` with `x ∉ K + U`.
  have hW : {u : E | x - u ∉ K} ∈ 𝓝 (0 : E) :=
    (isClosed_closure.isOpen_compl.preimage (by fun_prop)).mem_nhds (by simpa using hxK)
  obtain ⟨V, hV, hVclosed, hVW⟩ := exists_mem_nhds_isClosed_subset hW
  obtain ⟨U₀, ⟨hU₀, hU₀conv⟩, hU₀V⟩ := (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.1 hV
  set U := closure U₀
  have hUW : U ⊆ {u : E | x - u ∉ K} := (closure_minimal hU₀V hVclosed).trans hVW
  -- Cover `K` by finitely many translates `y + U` with `y ∈ K`.
  set T : E → Set E := fun y ↦ (fun z ↦ z - y) ⁻¹' U
  have hTnhds : ∀ y, T y ∈ 𝓝 y := fun y ↦
    (continuous_sub_right y).continuousAt.preimage_mem_nhds (by
      simpa using Filter.mem_of_superset hU₀ subset_closure)
  have hTclosed : ∀ y, IsClosed (T y) := fun y ↦ isClosed_closure.preimage (by fun_prop)
  have hTconv : ∀ y, Convex ℝ (T y) := fun y ↦ by
    simpa only [T, sub_eq_add_neg] using hU₀conv.closure.translate_preimage_left (-y)
  obtain ⟨t, htK, hKt⟩ := (hF.of_isClosed_subset isClosed_closure hKC).elim_nhds_subcover T
    fun y _ ↦ hTnhds y
  -- The closed convex hulls of the pieces `K ∩ (y + U)` are compact convex subsets of `C`.
  set D : E → Set E := fun y ↦ closure (convexHull ℝ (K ∩ T y))
  have hDC : ∀ y, D y ⊆ C := fun y ↦ closure_minimal
    (convexHull_min (inter_subset_left.trans hKC) hCconv) isClosed_closure
  have hDT : ∀ y, D y ⊆ T y := fun y ↦
    closure_minimal (convexHull_min inter_subset_right (hTconv y)) (hTclosed y)
  have hDconv : ∀ y, Convex ℝ (D y) := fun y ↦ (convex_convexHull ℝ _).closure
  -- The convex hull of their union is compact, hence closed, so it is all of `C`.
  have hcomp : IsCompact (convexHull ℝ (⋃ y ∈ t, D y)) :=
    t.isCompact_convexHull_biUnion fun y _ ↦ by
      rw [(hDconv y).convexHull_eq]
      exact hF.of_isClosed_subset isClosed_closure (hDC y)
  have hFD : F ⊆ convexHull ℝ (⋃ y ∈ t, D y) := fun f hf ↦ by
    obtain ⟨y, hy, hfy⟩ := mem_iUnion₂.1 (hKt (subset_closure hf))
    exact subset_convexHull ℝ _ (mem_iUnion₂.2
      ⟨y, hy, subset_closure (subset_convexHull ℝ _ ⟨subset_closure hf, hfy⟩)⟩)
  have hxD : x ∈ convexHull ℝ (⋃ y ∈ t, D y) :=
    closure_minimal (convexHull_min hFD (convex_convexHull ℝ _)) hcomp.isClosed hx.1
  have hDC' : convexHull ℝ (⋃ y ∈ t, D y) ⊆ C :=
    convexHull_min (iUnion₂_subset fun y _ ↦ hDC y) hCconv
  -- An extreme point of the convex hull of the union lies in one of the pieces.
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (extremePoints_convexHull_subset
    (inter_extremePoints_subset_extremePoints_of_subset hDC' ⟨hxD, hx⟩))
  exact hUW (hDT y hxy) (by simpa using htK y hy)

end TauCeti
