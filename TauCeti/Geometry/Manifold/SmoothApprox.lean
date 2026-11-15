/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.Homotopy.Path
import TauCeti.Topology.Homotopy.Homotopic.Rel

/-!
# Whitney approximation for maps into manifolds

A continuous map `f : N → M` between manifolds is homotopic to a smooth map. More precisely, if
`f` is already `C^n` on a neighbourhood of a closed set `S`, then it is homotopic relative to `S`
to a `C^n` map (`TauCeti.SmoothEmbedding.exists_contMDiff_homotopicRel`). This is the Whitney
approximation theorem for maps into manifolds, J. M. Lee, *Introduction to Smooth Manifolds*,
Theorem 6.26, here for a target `M` with a smooth embedding into a finite-dimensional real normed
space `V`. Consequently homotopic `C^n` maps are joined by a `C^n` homotopy
(`TauCeti.SmoothEmbedding.exists_contMDiff_homotopy`, Lee, Theorem 6.29), as needed to compare
integrals of closed forms along homotopic maps.

No embedding is needed among the hypotheses when the image of `f` has compact closure in a
Hausdorff target `M`, for instance when the source `N` is compact
(`ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`). Such an image lies in
an open submanifold of `M` with a smooth embedding into a Euclidean space
(`IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`), and the embedded case applies there.
In particular this holds for every map into a compact manifold. Continuous maps from a compact
manifold, such as the singular manifolds representing homology classes, can therefore be replaced
by homotopic smooth ones in an arbitrary boundaryless target.

The proof follows Lee. The intrinsic normal bundle of a smooth embedding `e` is diffeomorphic to
an open neighbourhood `W` of its image
(`TauCeti.SmoothEmbedding.exists_diffeomorph_normalBundle_subset`), so projecting to the base
gives a smooth retraction `r` of `W` onto the embedded manifold
(`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`). Mathlib's relative approximation
theorem for vector-valued maps (`Continuous.exists_contMDiff_approx_and_eqOn`) gives a `C^n` map
`G : N → V` equal to `e ∘ f` on `S`, and so close to it that every segment from `e (f x)` to `G x`
lies in `W`. Then `r ∘ G` is `C^n`, and `(t, x) ↦ r (e (f x) + t (G x - e (f x)))` is a homotopy
from `f` to `r ∘ G` which is constant on `S`.

The source `N` may have boundary or corners; it is Hausdorff and σ-compact, so that it has
smooth partitions of unity. The target `M` is boundaryless.

## Main results

* `TauCeti.SmoothEmbedding.exists_contMDiff_homotopicRel`: relative Whitney approximation into a
  manifold with a smooth embedding into a finite-dimensional normed space.
* `TauCeti.SmoothEmbedding.exists_contMDiff_homotopy`: homotopic `C^n` maps into such a manifold
  are `C^n` homotopic.
* `ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`,
  `ContinuousMap.exists_contMDiff_homotopic_of_isCompact_closure_range`,
  `ContinuousMap.Homotopy.exists_contMDiff_homotopy_of_isCompact_closure_range`: the same for maps
  and homotopies whose image has compact closure in a Hausdorff target.
* `ContinuousMap.exists_contMDiff_homotopicRel`, `ContinuousMap.exists_contMDiff_homotopic`,
  `ContinuousMap.Homotopic.exists_contMDiff_homotopy`: the same for a compact target.
* `Path.exists_homotopic_contMDiff_extend`: every path in a Hausdorff boundaryless manifold is
  homotopic, relative to its endpoints, to a path whose extension to `ℝ` is `C^n`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013,
  Theorems 6.21, 6.24, 6.26 and 6.29.
-/

public section

noncomputable section

open Bundle Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

section Approximation

variable {E F V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N] [T2Space N]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]

/-- **Relative Whitney approximation into an embedded manifold.** Let `M` be a boundaryless
manifold with a smooth embedding `e` into a finite-dimensional real normed space, and let
`f : N → M` be continuous and `C^n` on a neighbourhood `U` of a closed set `S`. Then `f` is
homotopic relative to `S` to a `C^n` map `g`; in particular `g = f` on `S`. -/
theorem exists_contMDiff_homotopicRel (e : SmoothEmbedding J 𝓘(ℝ, V) ∞ M V) (n : ℕ∞)
    (f : C(N, M)) {S U : Set N} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContMDiffOn I J n f U) :
    ∃ g : C(N, M), ContMDiff I J n g ∧ f.HomotopicRel g S := by
  rcases isEmpty_or_nonempty N with hN | hN
  · exact ⟨f, fun x ↦ isEmptyElim x, ⟨.refl f S⟩⟩
  have : Nonempty M := ⟨f hN.some⟩
  obtain ⟨W, hW, heW, -, r, hr, hre⟩ := e.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  let F : N → V := e ∘ f
  have hF : Continuous F := e.contMDiff.continuous.comp f.continuous
  have hFW (x : N) : F x ∈ W := heW (mem_range_self (f x))
  -- A continuous positive radius `ε` such that the `ε x`-ball about `F x` lies in `W`.
  obtain ⟨ε, hε, hεpos, hεW⟩ : ∃ ε : N → ℝ, Continuous ε ∧ (∀ x, 0 < ε x) ∧
      ∀ x y, dist y (F x) < ε x → y ∈ W := by
    rcases (Wᶜ).eq_empty_or_nonempty with h | h
    · exact ⟨fun _ ↦ 1, continuous_const, fun _ ↦ one_pos, fun _ y _ ↦ by
        simpa using congrArg (y ∈ ·) h⟩
    · refine ⟨fun x ↦ infDist (F x) Wᶜ, (continuous_infDist_pt _).comp hF,
        fun x ↦ (hW.isClosed_compl.notMem_iff_infDist_pos h).1 (not_not_intro (hFW x)),
        fun x y hy ↦ ?_⟩
      exact not_not.1 (notMem_of_dist_lt_infDist (dist_comm y (F x) ▸ hy))
  obtain ⟨G, hGF, hGS, -⟩ := hF.exists_contMDiff_approx_and_eqOn I n hε hεpos hS hU
    (e.contMDiff.of_le (WithTop.coe_le_coe.2 le_top) |>.comp_contMDiffOn hfU)
  -- The segment from `F x` to `G x` stays in `W`.
  let φ : unitInterval × N → V := fun p ↦ F p.2 + (p.1 : ℝ) • (G p.2 - F p.2)
  have hφ : Continuous φ := by fun_prop
  have hφW (p : unitInterval × N) : φ p ∈ W := by
    refine hεW p.2 _ ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg p.1.2.1, ← dist_eq_norm]
    exact (mul_le_of_le_one_left dist_nonneg p.1.2.2).trans_lt (hGF p.2)
  have hGW (x : N) : G x ∈ W := by simpa [φ] using hφW (1, x)
  have hrc : ContinuousOn r W := hr.continuousOn
  let g : C(N, M) := ⟨r ∘ G, hrc.comp_continuous G.contMDiff.continuous hGW⟩
  refine ⟨g, (hr.of_le (WithTop.coe_le_coe.2 le_top)).comp_contMDiff G.contMDiff hGW, ⟨?_⟩⟩
  refine
    { toFun := r ∘ φ
      continuous_toFun := hrc.comp_continuous hφ hφW
      map_zero_left := fun x ↦ by simp [φ, F, hre]
      map_one_left := fun x ↦ by simp [φ, g]
      prop' := fun t x hx ↦ ?_ }
  simp [φ, F, hGS hx, hre]

/-- **Homotopic `C^n` maps into an embedded manifold are `C^n` homotopic.** Let `M` be a
boundaryless manifold with a smooth embedding `e` into a finite-dimensional real normed space.
Two homotopic `C^n` maps `f₀ f₁ : N → M` are joined by a `C^n` map `K : N × ℝ → M` with
`K (x, 0) = f₀ x` and `K (x, 1) = f₁ x`. -/
theorem exists_contMDiff_homotopy (e : SmoothEmbedding J 𝓘(ℝ, V) ∞ M V) (n : ℕ∞)
    {f₀ f₁ : C(N, M)} (hf₀ : ContMDiff I J n f₀) (hf₁ : ContMDiff I J n f₁)
    (h : f₀.Homotopic f₁) :
    ∃ K : N × ℝ → M, ContMDiff (I.prod 𝓘(ℝ, ℝ)) J n K ∧ (∀ x, K (x, 0) = f₀ x) ∧
      ∀ x, K (x, 1) = f₁ x := by
  obtain ⟨H⟩ := h
  -- Reparametrize time so that the homotopy is `f₀` for `t < 1 / 3` and `f₁` for `t > 2 / 3`;
  -- it is then `C^n` near `N × {0, 1}`, and is smoothed relative to `N × {0, 1}`.
  let c : ℝ → unitInterval := fun t ↦ projIcc 0 1 zero_le_one (3 * t - 1)
  have hc₀ {t : ℝ} (ht : t < 1 / 3) : c t = 0 := by
    simp only [c]
    rw [projIcc_of_le_left _ (by linarith), Set.Icc.mk_zero]
  have hc₁ {t : ℝ} (ht : 2 / 3 < t) : c t = 1 := by
    simp only [c]
    rw [projIcc_of_right_le _ (by linarith), Set.Icc.mk_one]
  let H' : C(N × ℝ, M) := ⟨fun p ↦ H (c p.2, p.1), by fun_prop⟩
  let S : Set (N × ℝ) := univ ×ˢ {0, 1}
  let U : Set (N × ℝ) := univ ×ˢ (Iio (1 / 3) ∪ Ioi (2 / 3))
  have hU : IsOpen U := isOpen_univ.prod (isOpen_Iio.union isOpen_Ioi)
  have hSU : S ⊆ U := prod_mono subset_rfl (by
    rintro t (rfl | rfl)
    · exact Or.inl (by norm_num)
    · exact Or.inr (by norm_num))
  have hS : IsClosed S := isClosed_univ.prod (Finite.isClosed (by simp))
  have hH'U : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J n H' U := by
    rintro ⟨x, t⟩ ⟨-, ht | ht⟩
    · have hev : (f₀ ∘ Prod.fst : N × ℝ → M) =ᶠ[𝓝 (x, t)] H' := by
        filter_upwards [(isOpen_univ.prod isOpen_Iio).mem_nhds (mem_prod.2 ⟨mem_univ x, ht⟩)]
          with p hp
        simp [H', hc₀ hp.2]
      exact ((hf₀.comp contMDiff_fst).contMDiffAt.congr_of_eventuallyEq hev.symm).contMDiffWithinAt
    · have hev : (f₁ ∘ Prod.fst : N × ℝ → M) =ᶠ[𝓝 (x, t)] H' := by
        filter_upwards [(isOpen_univ.prod isOpen_Ioi).mem_nhds (mem_prod.2 ⟨mem_univ x, ht⟩)]
          with p hp
        simp [H', hc₁ hp.2]
      exact ((hf₁.comp contMDiff_fst).contMDiffAt.congr_of_eventuallyEq hev.symm).contMDiffWithinAt
  obtain ⟨K, hK, ⟨R⟩⟩ := e.exists_contMDiff_homotopicRel n H' hS (hU.mem_nhdsSet.2 hSU) hH'U
  refine ⟨K, hK, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← R.fst_eq_snd (show (x, (0 : ℝ)) ∈ S by simp [S])]
    simp [H', hc₀ (by norm_num : (0 : ℝ) < 1 / 3)]
  · rw [← R.fst_eq_snd (show (x, (1 : ℝ)) ∈ S by simp [S])]
    simp [H', hc₁ (by norm_num : (2 / 3 : ℝ) < 1)]

end Approximation

end TauCeti.SmoothEmbedding

namespace ContinuousMap

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N] [T2Space N]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]

/-- **Relative Whitney approximation with relatively compact image.** A continuous map `f` from a
σ-compact Hausdorff manifold, possibly with corners, into a Hausdorff boundaryless manifold, whose
image has compact closure and which is `C^n` on a neighbourhood `U` of a closed set `S`, is
homotopic relative to `S` to a `C^n` map. -/
theorem exists_contMDiff_homotopicRel_of_isCompact_closure_range (n : ℕ∞) (f : C(N, M))
    (hf : IsCompact (closure (range f))) {S U : Set N} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContMDiffOn I J n f U) :
    ∃ g : C(N, M), ContMDiff I J n g ∧ f.HomotopicRel g S := by
  -- `f` takes values in an open submanifold `W` with a smooth embedding into a Euclidean space.
  obtain ⟨W, hW, -, _, ⟨e⟩⟩ := hf.exists_opens_nonempty_smoothEmbedding_euclidean (I := J)
  let f' : C(N, W) := ⟨_, f.continuous.subtype_mk fun x ↦ hW (subset_closure (mem_range_self x))⟩
  obtain ⟨g', hg', hfg'⟩ := e.exists_contMDiff_homotopicRel n f' hS hU
    ((TauCeti.ContMDiffOn.subtypeVal_comp_iff W f' U).1 hfU)
  let i : C(W, M) := ⟨Subtype.val, continuous_subtype_val⟩
  have hif : i.comp f' = f := ContinuousMap.ext fun _ ↦ rfl
  exact ⟨i.comp g', contMDiff_subtype_val.comp hg', hif ▸ hfg'.comp_continuousMap i⟩

/-- **Whitney approximation with relatively compact image.** Every continuous map from a
σ-compact Hausdorff manifold, possibly with corners, into a Hausdorff boundaryless manifold, whose
image has compact closure, is homotopic to a `C^n` map. This applies to every continuous map from a
compact manifold. -/
theorem exists_contMDiff_homotopic_of_isCompact_closure_range (n : ℕ∞) (f : C(N, M))
    (hf : IsCompact (closure (range f))) :
    ∃ g : C(N, M), ContMDiff I J n g ∧ f.Homotopic g := by
  obtain ⟨g, hg, hfg⟩ := f.exists_contMDiff_homotopicRel_of_isCompact_closure_range (I := I) n hf
    isClosed_empty (U := ∅) (by simp) (contMDiffOn_empty (I' := J))
  exact ⟨g, hg, hfg.homotopic⟩

/-- **A `C^n` homotopy from a homotopy with relatively compact image.** If two `C^n` maps from a
σ-compact Hausdorff manifold, possibly with corners, into a Hausdorff boundaryless manifold are
joined by a homotopy whose image has compact closure, then they are joined by a `C^n` map
`K : N × ℝ → M` with `K (x, 0) = f₀ x` and `K (x, 1) = f₁ x`. This applies to every homotopy
between maps from a compact manifold. -/
theorem Homotopy.exists_contMDiff_homotopy_of_isCompact_closure_range {f₀ f₁ : C(N, M)}
    (H : f₀.Homotopy f₁) (hH : IsCompact (closure (range H))) (n : ℕ∞)
    (hf₀ : ContMDiff I J n f₀) (hf₁ : ContMDiff I J n f₁) :
    ∃ K : N × ℝ → M, ContMDiff (I.prod 𝓘(ℝ, ℝ)) J n K ∧ (∀ x, K (x, 0) = f₀ x) ∧
      ∀ x, K (x, 1) = f₁ x := by
  -- `H` takes values in an open submanifold `W` with a smooth embedding into a Euclidean space.
  obtain ⟨W, hW, -, _, ⟨e⟩⟩ := hH.exists_opens_nonempty_smoothEmbedding_euclidean (I := J)
  have hHW (p : unitInterval × N) : H p ∈ W := hW (subset_closure (mem_range_self p))
  let f₀' : C(N, W) := ⟨_, f₀.continuous.subtype_mk fun x ↦ by simpa using hHW (0, x)⟩
  let f₁' : C(N, W) := ⟨_, f₁.continuous.subtype_mk fun x ↦ by simpa using hHW (1, x)⟩
  let H' : f₀'.Homotopy f₁' :=
    { toContinuousMap := ⟨_, H.continuous.subtype_mk hHW⟩
      map_zero_left x := Subtype.ext (H.apply_zero x)
      map_one_left x := Subtype.ext (H.apply_one x) }
  obtain ⟨K', hK', hK'₀, hK'₁⟩ := e.exists_contMDiff_homotopy n
    ((TauCeti.ContMDiff.subtypeVal_comp_iff W f₀').1 hf₀)
    ((TauCeti.ContMDiff.subtypeVal_comp_iff W f₁').1 hf₁) ⟨H'⟩
  exact ⟨Subtype.val ∘ K', contMDiff_subtype_val.comp hK', fun x ↦ congr_arg Subtype.val (hK'₀ x),
    fun x ↦ congr_arg Subtype.val (hK'₁ x)⟩

/-- **Relative Whitney approximation into a compact manifold.** A continuous map `f` from a
σ-compact Hausdorff manifold, possibly with corners, into a compact boundaryless manifold which is
`C^n` on a neighbourhood `U` of a closed set `S` is homotopic relative to `S` to a `C^n` map. -/
theorem exists_contMDiff_homotopicRel [CompactSpace M] (n : ℕ∞) (f : C(N, M)) {S U : Set N}
    (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S) (hfU : ContMDiffOn I J n f U) :
    ∃ g : C(N, M), ContMDiff I J n g ∧ f.HomotopicRel g S :=
  f.exists_contMDiff_homotopicRel_of_isCompact_closure_range n
    isClosed_closure.isCompact hS hU hfU

/-- **Whitney approximation into a compact manifold.** Every continuous map from a σ-compact
Hausdorff manifold, possibly with corners, into a compact boundaryless manifold is homotopic to a
`C^n` map. -/
theorem exists_contMDiff_homotopic [CompactSpace M] (n : ℕ∞) (f : C(N, M)) :
    ∃ g : C(N, M), ContMDiff I J n g ∧ f.Homotopic g :=
  f.exists_contMDiff_homotopic_of_isCompact_closure_range n isClosed_closure.isCompact

/-- **Homotopic `C^n` maps into a compact manifold are `C^n` homotopic.** Two homotopic `C^n`
maps from a σ-compact Hausdorff manifold, possibly with corners, into a compact boundaryless
manifold are joined by a `C^n` map `K : N × ℝ → M` with `K (x, 0) = f₀ x` and
`K (x, 1) = f₁ x`. -/
theorem Homotopic.exists_contMDiff_homotopy [CompactSpace M] {f₀ f₁ : C(N, M)}
    (h : f₀.Homotopic f₁) (n : ℕ∞) (hf₀ : ContMDiff I J n f₀) (hf₁ : ContMDiff I J n f₁) :
    ∃ K : N × ℝ → M, ContMDiff (I.prod 𝓘(ℝ, ℝ)) J n K ∧ (∀ x, K (x, 0) = f₀ x) ∧
      ∀ x, K (x, 1) = f₁ x :=
  let ⟨H⟩ := h
  H.exists_contMDiff_homotopy_of_isCompact_closure_range isClosed_closure.isCompact n hf₀ hf₁

end ContinuousMap

namespace Path

variable {F G M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M] {x y : M}

/-- **Smooth representatives of path classes.** Every path in a Hausdorff boundaryless manifold
is homotopic, relative to its endpoints, to a path whose extension to `ℝ`, constant before `0`
and after `1`, is `C^n`. -/
theorem exists_homotopic_contMDiff_extend (n : ℕ∞) (γ : Path x y) :
    ∃ γ' : Path x y, γ.Homotopic γ' ∧ ContMDiff 𝓘(ℝ, ℝ) J n γ'.extend := by
  -- Run through `γ` on `[1/3, 2/3]`, so that the map is constant near `(-∞, 0] ∪ [1, ∞)`, and
  -- smooth it relative to that set.
  let f : C(ℝ, M) := ⟨fun t ↦ γ.extend (3 * t - 1), by fun_prop⟩
  have hf₀ {t : ℝ} (ht : t < 1 / 3) : f t = x := γ.extend_of_le_zero (by linarith)
  have hf₁ {t : ℝ} (ht : 2 / 3 < t) : f t = y := γ.extend_of_one_le (by linarith)
  set S : Set ℝ := Iic 0 ∪ Ici 1
  set U : Set ℝ := Iio (1 / 3) ∪ Ioi (2 / 3)
  have hSU : S ⊆ U := by
    rintro t (ht | ht)
    · exact Or.inl (lt_of_le_of_lt (mem_Iic.1 ht) (by norm_num))
    · exact Or.inr (lt_of_lt_of_le (by norm_num) (mem_Ici.1 ht))
  have hU : U ∈ 𝓝ˢ S := ((isOpen_Iio.union isOpen_Ioi).mem_nhdsSet).2 hSU
  have hfU : ContMDiffOn 𝓘(ℝ, ℝ) J n f U := by
    rintro t (ht | ht)
    · refine (contMDiffAt_const (c := x)).congr_of_eventuallyEq ?_ |>.contMDiffWithinAt
      filter_upwards [Iio_mem_nhds ht] with s hs using hf₀ hs
    · refine (contMDiffAt_const (c := y)).congr_of_eventuallyEq ?_ |>.contMDiffWithinAt
      filter_upwards [Ioi_mem_nhds ht] with s hs using hf₁ hs
  have hrange : range f ⊆ range γ := by
    rintro _ ⟨t, rfl⟩
    exact γ.extend_range ▸ mem_range_self _
  obtain ⟨g, hg, hfg⟩ := f.exists_contMDiff_homotopicRel_of_isCompact_closure_range
    (I := 𝓘(ℝ, ℝ)) n ((isCompact_range γ.continuous).closure_of_subset hrange)
    (isClosed_Iic.union isClosed_Ici) hU hfU
  have hg₀ {t : ℝ} (ht : t ≤ 0) : g t = x :=
    (hfg.fst_eq_snd (Or.inl ht)).symm.trans (hf₀ (by linarith))
  have hg₁ {t : ℝ} (ht : 1 ≤ t) : g t = y :=
    (hfg.fst_eq_snd (Or.inr ht)).symm.trans (hf₁ (by linarith))
  let ι : C(unitInterval, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let γ' : Path x y := ⟨g.comp ι, hg₀ le_rfl, hg₁ le_rfl⟩
  have hext : γ'.extend = g := by
    ext t
    rcases le_or_gt t 0 with h₀ | h₀
    · rw [γ'.extend_of_le_zero h₀, hg₀ h₀]
    rcases le_or_gt 1 t with h₁ | h₁
    · rw [γ'.extend_of_one_le h₁, hg₁ h₁]
    exact γ'.extend_apply ⟨h₀.le, h₁.le⟩
  refine ⟨γ', ?_, hext ▸ hg⟩
  -- `f` on the unit interval is a reparametrization of `γ`, and it is homotopic to `γ'`.
  let ρ : C(unitInterval, unitInterval) :=
    ⟨fun t ↦ projIcc 0 1 zero_le_one (3 * t - 1), by fun_prop⟩
  have hρ₀ : ρ 0 = 0 := Subtype.ext (by simp [ρ, projIcc_of_le_left])
  have hρ₁ : ρ 1 = 1 := Subtype.ext (by norm_num [ρ, projIcc_of_right_le])
  have hfx : f 0 = x := hf₀ (by norm_num)
  have hfy : f 1 = y := hf₁ (by norm_num)
  let γ₀ : Path x y := ⟨f.comp ι, hfx, hfy⟩
  have hfγ : γ.reparam ρ ρ.continuous hρ₀ hρ₁ = γ₀ :=
    -- `Path.extend` is defined as `IccExtend zero_le_one γ`, which `IccExtend_apply` rewrites as
    -- `γ ∘ projIcc 0 1 zero_le_one`; Mathlib proves `Path.extend_apply` in the same way.
    Path.ext (funext fun t ↦ by
      change γ (ρ t) = γ.extend (3 * t - 1)
      exact (IccExtend_apply zero_le_one γ _).symm)
  -- A homotopy of paths is by definition a homotopy relative to the endpoints `{0, 1}`.
  have hpath : γ₀.Homotopic γ' :=
    (hfg.precomp ι).mono fun t ht ↦ by
      rcases ht with rfl | rfl
      exacts [Or.inl le_rfl, Or.inr le_rfl]
  exact (hfγ ▸ ⟨Path.Homotopy.reparam γ ρ ρ.continuous hρ₀ hρ₁⟩ : γ.Homotopic γ₀).trans hpath

end Path
