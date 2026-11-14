/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BrouwerFixedPoint
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.Convex.PartitionOfUnity
import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# Schauder's fixed-point theorem

**Schauder's fixed-point theorem**: let `C` be a nonempty closed convex subset of a real normed
space and let `f` be a continuous self-map of `C` whose image `f '' C` has compact closure. Then
`f` has a fixed point (`TauCeti.schauderFixedPoint_closedConvex_continuousOn`). Neither
boundedness of `C` nor completeness of the space is needed: the closure of the image does the
work of both. In particular every continuous self-map of a nonempty compact convex set has a
fixed point (`TauCeti.schauderFixedPoint_compactConvex`), whatever the dimension of the ambient
space.

The proof is Schauder's. Let `K` be the compact closure of `f '' C`; it lies in `C` because `C`
is closed. For `ε > 0`, a partition of unity on `K` subordinate to a finite cover by `ε`-balls
gives a continuous map `P : K → E` into the convex hull `D` of finitely many points of `K` with
`dist (P y) y ≤ ε` (`ContinuousMap.exists_partitionOfUnity_dist_finsum_smul_le`). The set `D` is a
compact convex subset of `C` lying in a finite-dimensional subspace, and `P ∘ f` maps it into
itself, so Brouwer's theorem (`TauCeti.brouwerFixedPoint_compactConvex_finiteSpan`) gives an
`ε`-approximate fixed point of `f` (`TauCeti.exists_dist_le_of_isCompact_closure_image`). These
approximations are nonlinear convex combinations; no approximation property of the space is
used. Compactness of `K` extracts a convergent subsequence of approximate fixed points, whose
limit is a fixed point.

The **Leray–Schauder** form replaces the invariance of a set by a condition on the boundary of a
ball: if `T` is continuous on the closed ball of radius `R > 0` with relatively compact image,
and no `u` with `‖u‖ = R` solves `u = θ • T u` for `0 < θ < 1`, then `T` has a fixed point in
the ball (`TauCeti.leraySchauderFixedPoint_closedBall`). The proof applies Schauder's theorem to
`T` followed by the radial retraction onto the ball. **Schaefer's theorem** is the a priori
estimate form used for nonlinear elliptic equations: a continuous map sending bounded sets to
relatively compact sets, whose solutions of `u = θ • T u`, `0 < θ < 1`, form a bounded set, has
a fixed point (`TauCeti.schaeferFixedPoint`).

## Main results

* `TauCeti.exists_dist_le_of_isCompact_closure_image`: approximate fixed points.
* `TauCeti.schauderFixedPoint_closedConvex_continuousOn`: Schauder's theorem for a function of
  the ambient space.
* `TauCeti.schauderFixedPoint_closedConvex`: Schauder's theorem for a bundled self-map.
* `TauCeti.schauderFixedPoint_compactConvex`: Schauder's theorem for compact convex sets.
* `TauCeti.exists_sum_smul_apply_apply_eq_self`: if `g` maps a closed convex set `C` into a
  compact set covered by the preimages of the interior of `C` under finitely many maps `f i`,
  then some `x ∈ C` is a convex combination of the points `f i (g x)`.
* `TauCeti.leraySchauderFixedPoint_closedBall`: the Leray–Schauder boundary condition on a ball.
* `TauCeti.schaeferFixedPoint`: Schaefer's a priori bound form.

## References

* J. Schauder, *Der Fixpunktsatz in Funktionalräumen*, Studia Math. 2 (1930), 171–180.
* H. Schaefer, *Über die Methode der a priori-Schranken*, Math. Ann. 129 (1955), 415–416.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 11.1 and 11.3 and Corollary 11.2.
-/

public section

open Filter Function Metric Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- **Approximate fixed points**: a continuous self-map `f` of a nonempty closed convex set `C`
in a real normed space, whose image has compact closure, moves some point of `C` by at most `ε`,
for every `ε > 0`. -/
theorem exists_dist_le_of_isCompact_closure_image (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) {f : E → E} (hf : ContinuousOn f C) (hfC : MapsTo f C C)
    (hK : IsCompact (closure (f '' C))) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ C, dist (f x) x ≤ ε := by
  set K := closure (f '' C)
  have hKC : K ⊆ C := closure_minimal (image_subset_iff.2 hfC) hC
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- A partition of unity on `K` moves each point of `K` by at most `ε` into the convex hull `D`
  -- of the finitely many points `T` of `K` it is indexed by.
  obtain ⟨s, ρ, hρ⟩ := ContinuousMap.exists_partitionOfUnity_dist_finsum_smul_le
    ⟨((↑) : K → E), continuous_subtype_val⟩ hε
  let T : Set E := (↑) '' (s : Set K)
  let D := convexHull ℝ T
  let P : K → E := fun y ↦ ∑ᶠ k : s, ρ k y • ((k : K) : E)
  have hTfin : T.Finite := s.finite_toSet.image _
  have hP : ∀ y, P y ∈ D := fun y ↦ ρ.finsum_smul_mem_convex (g := fun k _ ↦ ((k : K) : E))
    (mem_univ y) (fun k _ ↦ subset_convexHull ℝ T ⟨k, k.2, rfl⟩) (convex_convexHull ℝ T)
  have hPc : Continuous P := by
    simp only [P, finsum_eq_sum_of_fintype]
    fun_prop
  have hDC : D ⊆ C := convexHull_min (image_subset_iff.2 fun k _ ↦ hKC k.2) hconv
  have hDK : MapsTo f D K := fun x hx ↦ subset_closure (mem_image_of_mem f (hDC hx))
  -- Brouwer's theorem on `D`, which lies in the finite-dimensional span of `T`, gives a fixed
  -- point of `P ∘ f`.
  have : FiniteDimensional ℝ (Submodule.span ℝ T) := FiniteDimensional.span_of_finite ℝ hTfin
  have hDV : D ⊆ Submodule.span ℝ T :=
    convexHull_min Submodule.subset_span (Submodule.span ℝ T).convex
  obtain ⟨y, hy⟩ := (hne.image f).closure
  obtain ⟨x, hx⟩ := brouwerFixedPoint_compactConvex_finiteSpan (Submodule.span ℝ T) hDV
    (hTfin.isCompact_convexHull (𝕜 := ℝ)) (convex_convexHull ℝ T) ⟨P ⟨y, hy⟩, hP _⟩
    ⟨fun x ↦ ⟨P (hDK.restrict f D K x), hP _⟩,
      (hPc.comp ((hf.mono hDC).mapsToRestrict hDK)).subtype_mk _⟩
  refine ⟨x, hDC x.2, ?_⟩
  have hx' : P (hDK.restrict f D K x) = x := congrArg Subtype.val hx
  calc dist (f x) x = dist (f x) (P (hDK.restrict f D K x)) := by rw [hx']
    _ ≤ ε := (dist_comm _ _).trans_le (hρ _)

/-- **Schauder's fixed-point theorem**: a continuous self-map `f` of a nonempty closed convex set
`C` in a real normed space, whose image has compact closure, has a fixed point. -/
theorem schauderFixedPoint_closedConvex_continuousOn (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) {f : E → E} (hf : ContinuousOn f C) (hfC : MapsTo f C C)
    (hK : IsCompact (closure (f '' C))) : ∃ x ∈ C, IsFixedPt f x := by
  choose x hxC hx using fun n : ℕ ↦ exists_dist_le_of_isCompact_closure_image hC hconv hne hf hfC
    hK (ε := 1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  obtain ⟨y, hyK, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n ↦ f (x n))
    fun n ↦ subset_closure (mem_image_of_mem f (hxC n))
  have hyC : y ∈ C := closure_minimal (image_subset_iff.2 hfC) hC hyK
  -- Along the subsequence, `x` has the same limit as `f ∘ x`, since `dist (f (x n)) (x n) → 0`.
  have hxlim : Tendsto (x ∘ φ) atTop (𝓝 y) :=
    hlim.congr_dist (squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ hx (φ n))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop))
  have hfy : Tendsto (f ∘ x ∘ φ) atTop (𝓝 (f y)) := (hf y hyC).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hxlim, Eventually.of_forall fun n ↦ hxC (φ n)⟩)
  exact ⟨y, hyC, tendsto_nhds_unique hfy hlim⟩

/-- **Schauder's fixed-point theorem**: a continuous self-map of a nonempty closed convex set `C`
in a real normed space, whose range has compact closure in the space, has a fixed point. -/
theorem schauderFixedPoint_closedConvex (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (f : C(C, C)) (hK : IsCompact (closure (range fun x ↦ (f x : E)))) :
    ∃ x, IsFixedPt f x := by
  classical
  -- Extend `f` to the ambient space by the identity off `C`.
  let g : E → E := fun x ↦ if hx : x ∈ C then f ⟨x, hx⟩ else x
  have hg : ∀ x : C, g x = f x := fun x ↦ by simp [g]
  have hgC : MapsTo g C C := fun x hx ↦ (hg ⟨x, hx⟩).symm ▸ (f ⟨x, hx⟩).2
  have hgc : ContinuousOn g C := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp f.continuous).congr fun x ↦ (hg x).symm
  have himage : g '' C = range fun x ↦ (f x : E) := by
    rw [image_eq_range]
    exact congrArg range (funext hg)
  obtain ⟨x, hx, hfx⟩ :=
    schauderFixedPoint_closedConvex_continuousOn hC hconv hne hgc hgC (himage ▸ hK)
  exact ⟨⟨x, hx⟩, Subtype.ext ((hg ⟨x, hx⟩).symm.trans hfx)⟩

/-- **Schauder's fixed-point theorem for compact convex sets**: every continuous self-map of a
nonempty compact convex subset of a real normed space has a fixed point. Unlike
`TauCeti.brouwerFixedPoint_compactConvex_finiteSpan`, the set need not lie in a
finite-dimensional subspace. -/
theorem schauderFixedPoint_compactConvex (hC : IsCompact C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) (f : C(C, C)) : ∃ x, IsFixedPt f x :=
  schauderFixedPoint_closedConvex hC.isClosed hconv hne f <| hC.of_isClosed_subset
    isClosed_closure (closure_minimal (range_subset_iff.2 fun x ↦ (f x).2) hC.isClosed)

/-- **Convex-combination fixed points**: let `g` map a nonempty closed convex set `C`
continuously into a compact set `S`, and let `f i` be finitely many continuous maps such that each
point of `S` is sent into the interior of `C` by some `f i`. Then some `x ∈ C` is a convex
combination of the points `f i (g x)`. This is the fixed-point step of Lomonosov's lemma. -/
theorem exists_sum_smul_apply_apply_eq_self {ι : Type*} [Fintype ι] (hC : IsClosed C)
    (hconv : Convex ℝ C) (hne : C.Nonempty) {f : ι → E → E} (hf : ∀ i, Continuous (f i))
    {g : E → E} (hg : ContinuousOn g C) {S : Set E} (hS : IsCompact S) (hgS : MapsTo g C S)
    (hcover : S ⊆ ⋃ i, f i ⁻¹' interior C) :
    ∃ x ∈ C, ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i = 1 ∧ ∑ i, c i • f i (g x) = x := by
  -- A partition of unity `w` on `S` subordinate to the cover averages the `f i` into a
  -- continuous self-map `Ψ` of `C`.
  obtain ⟨w, hw⟩ := PartitionOfUnity.exists_isSubordinate hS.isClosed
    (fun i ↦ f i ⁻¹' interior C) (fun i ↦ isOpen_interior.preimage (hf i)) hcover
  set Ψ : E → E := fun x ↦ ∑ᶠ i, w i (g x) • f i (g x)
  have hΨc : ContinuousOn Ψ C :=
    (w.continuous_finsum_smul fun i _ _ ↦ (hf i).continuousAt).comp_continuousOn hg
  have hΨC : MapsTo Ψ C C := fun x hx ↦
    w.finsum_smul_mem_convex (hgS hx) (fun i hi ↦ interior_subset (hw i (subset_tsupport _ hi)))
      hconv
  -- The image of `Ψ` lies in the compact image of `[0, 1]^ι × S` under `F`.
  set F : (ι → ℝ) × E → E := fun p ↦ ∑ i, p.1 i • f i p.2
  have hΨK : IsCompact (closure (Ψ '' C)) := by
    have hcpt : IsCompact (F '' (univ.pi (fun _ : ι ↦ Icc (0 : ℝ) 1) ×ˢ S)) :=
      ((isCompact_univ_pi fun _ ↦ isCompact_Icc).prod hS).image (by fun_prop)
    refine hcpt.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcpt.isClosed)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(fun i ↦ w i (g x), g x), ⟨fun i _ ↦ ⟨w.nonneg i _, w.le_one i _⟩, hgS hx⟩,
      (finsum_eq_sum_of_fintype _).symm⟩
  obtain ⟨x, hxC, hfix⟩ := schauderFixedPoint_closedConvex_continuousOn hC hconv hne hΨc hΨC hΨK
  refine ⟨x, hxC, fun i ↦ w i (g x), fun i ↦ w.nonneg i _, ?_, ?_⟩
  · rw [← finsum_eq_sum_of_fintype]
    exact w.sum_eq_one (hgS hxC)
  · rw [← finsum_eq_sum_of_fintype]
    exact hfix

/-- **The Leray–Schauder fixed-point theorem** on a ball: let `T` be continuous on the closed
ball of radius `R > 0` about the origin, with image of compact closure. If no `u` with
`‖u‖ = R` solves `u = θ • T u` for `0 < θ < 1`, then `T` has a fixed point in the ball. -/
theorem leraySchauderFixedPoint_closedBall {R : ℝ} (hR : 0 < R) {T : E → E}
    (hT : ContinuousOn T (closedBall 0 R)) (hK : IsCompact (closure (T '' closedBall 0 R)))
    (hbd : ∀ u, ‖u‖ = R → ∀ θ ∈ Ioo (0 : ℝ) 1, u ≠ θ • T u) :
    ∃ u ∈ closedBall 0 R, IsFixedPt T u := by
  -- Apply Schauder's theorem to `T` followed by the radial retraction onto the ball.
  have hr : Continuous (radialRetraction (E := E) R) :=
    (lipschitzWith_radialRetraction hR.le).continuous
  have hK' : IsCompact (closure ((radialRetraction R ∘ T) '' closedBall 0 R)) := by
    refine (hK.image hr).of_isClosed_subset isClosed_closure (closure_minimal ?_
      (hK.image hr).isClosed)
    rw [image_comp]
    exact image_mono subset_closure
  obtain ⟨v, hv, hfix⟩ := schauderFixedPoint_closedConvex_continuousOn isClosed_closedBall
    (convex_closedBall 0 R) (nonempty_closedBall.2 hR.le) (hr.comp_continuousOn hT)
    (fun x _ ↦ mapsTo_radialRetraction hR.le (mem_univ (T x))) hK'
  have hRv : radialRetraction R (T v) = v := hfix.eq
  refine ⟨v, hv, ?_⟩
  by_cases hTv : ‖T v‖ ≤ R
  · rwa [radialRetraction_of_norm_le hTv] at hRv
  -- Otherwise `v` is the retraction of `T v` to the sphere, which the boundary condition excludes.
  replace hTv := not_le.1 hTv
  have hpos : 0 < ‖T v‖ := hR.trans hTv
  have hv' : v = (R / ‖T v‖) • T v := by
    rw [radialRetraction_def, min_eq_right ((div_le_one hpos).2 hTv.le)] at hRv
    exact hRv.symm
  have hnorm : ‖v‖ = R := by
    rw [← hRv, norm_radialRetraction hR.le, min_eq_right hTv.le]
  exact absurd hv' (hbd v hnorm _ ⟨div_pos hR hpos, (div_lt_one hpos).2 hTv⟩)

/-- **Schaefer's fixed-point theorem**: a continuous map `T` of a real normed space that sends
bounded sets to sets with compact closure has a fixed point, provided the solutions `u` of
`u = θ • T u` with `0 < θ < 1` form a bounded set. The classical a priori bound over
`0 ≤ θ ≤ 1` implies this hypothesis. -/
theorem schaeferFixedPoint {T : E → E} (hT : Continuous T)
    (hK : ∀ s, Bornology.IsBounded s → IsCompact (closure (T '' s)))
    (hbd : Bornology.IsBounded {u | ∃ θ ∈ Ioo (0 : ℝ) 1, u = θ • T u}) :
    ∃ u, IsFixedPt T u := by
  obtain ⟨R₀, hR₀⟩ := hbd.subset_closedBall 0
  set R := max R₀ 0 + 1
  have hR : 0 < R := by positivity
  obtain ⟨u, -, hu⟩ := leraySchauderFixedPoint_closedBall hR hT.continuousOn
    (hK _ isBounded_closedBall) fun u hu θ hθ hθu ↦ by
      have : ‖u‖ ≤ R₀ := mem_closedBall_zero_iff.1 (hR₀ ⟨θ, hθ, hθu⟩)
      linarith [le_max_left R₀ 0]
  exact ⟨u, hu⟩

end TauCeti
