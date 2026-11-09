/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Geometry.Manifold.WhitneyEmbedding
public import Mathlib.Topology.Homotopy.Basic

/-!
# Whitney approximation for maps into manifolds

A continuous map `f : N → M` between manifolds is homotopic to a smooth map. More precisely, if
`f` is already `C^n` on a neighbourhood of a closed set `S`, then it is homotopic relative to `S`
to a `C^n` map (`TauCeti.SmoothEmbedding.exists_contMDiff_homotopicRel`). This is the Whitney
approximation theorem for maps into manifolds, J. M. Lee, *Introduction to Smooth Manifolds*,
Theorem 6.26, here for a target `M` with a smooth embedding into a finite-dimensional real normed
space `V`. Every compact manifold has one, by Mathlib's Whitney embedding theorem
(`TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact`), which gives the compact case
`ContinuousMap.exists_contMDiff_homotopicRel` with no embedding among the hypotheses.
Consequently homotopic `C^n` maps are joined by a `C^n` homotopy
(`TauCeti.SmoothEmbedding.exists_contMDiff_homotopy`, Lee, Theorem 6.29), as needed to compare
integrals of closed forms along homotopic maps.

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

* `TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`: a smooth embedding into a second
  countable Hausdorff manifold has a smooth retraction from a neighbourhood of its image.
* `TauCeti.SmoothEmbedding.exists_contMDiff_homotopicRel`: relative Whitney approximation into a
  manifold with a smooth embedding into a finite-dimensional normed space.
* `TauCeti.SmoothEmbedding.exists_contMDiff_homotopy`: homotopic `C^n` maps into such a manifold
  are `C^n` homotopic.
* `ContinuousMap.exists_contMDiff_homotopicRel`, `ContinuousMap.exists_contMDiff_homotopic`,
  `ContinuousMap.Homotopic.exists_contMDiff_homotopy`: the same for a compact target.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013,
  Theorems 6.21, 6.24, 6.26 and 6.29.
-/

public section

noncomputable section

open Bundle Function Metric Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

section Retraction

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N] [SecondCountableTopology N]

/-- **Smooth retractions onto embedded submanifolds.** A smooth embedding `f : M → N` of a
nonempty boundaryless manifold into a second countable Hausdorff boundaryless manifold has a
smooth retraction `r : N → M` on an open neighbourhood `W` of its image, inside any prescribed
open neighbourhood `O` of the image: `r` is smooth on `W` and `r ∘ f = id`. Outside `W` the
values of `r` are arbitrary. -/
theorem exists_contMDiffOn_retraction [Nonempty M] (f : SmoothEmbedding I J ∞ M N) {O : Set N}
    (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ W : Set N, IsOpen W ∧ range f ⊆ W ∧ W ⊆ O ∧
      ∃ r : N → M, ContMDiffOn J I ∞ r W ∧ ∀ x, r (f x) = x := by
  classical
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let P := EuclideanSpace ℝ (Fin (Module.finrank ℝ V - Module.finrank ℝ E))
  have hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E :=
    finrank_euclideanSpace_fin
  let := f.normalSpaceFiberBundle hn hdim
  -- A tubular neighbourhood `Φ` of `f`; the retraction is its base projection.
  obtain ⟨W, hWO, Φ, hΦ⟩ := f.exists_diffeomorph_normalBundle_subset (P := P) hdim hO hfO
  let r : N → M := fun y ↦ if h : y ∈ W then (Φ.symm ⟨y, h⟩).proj else Classical.arbitrary M
  have hrW (w : W) : r w = (Φ.symm w).proj := by simp [r, w.2]
  have hfW (x : M) : f x ∈ W := by
    rw [← hΦ x]
    exact (Φ _).2
  refine ⟨W, W.isOpen, range_subset_iff.2 hfW, hWO, r, fun y hy ↦ ?_, fun x ↦ ?_⟩
  · have hsmooth : ContMDiff J I ∞ fun w : W ↦ r w := by
      simp only [hrW]
      exact (contMDiff_proj (fun x ↦ f.NormalSpace x hn)).comp Φ.symm.contMDiff
    exact (contMDiffAt_subtype_iff (x := ⟨y, hy⟩).1 (hsmooth _)).contMDiffWithinAt
  · have h : Φ.symm ⟨f x, hfW x⟩ = zeroSection P (fun x ↦ f.NormalSpace x hn) x :=
      Φ.symm_apply_eq.2 (Subtype.ext (hΦ x).symm)
    rw [hrW ⟨f x, hfW x⟩, h, zeroSection_proj]

end Retraction

section Euclidean

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A compact Hausdorff boundaryless manifold has a smooth embedding into a Euclidean space.
This is Mathlib's Whitney embedding theorem `exists_embedding_euclidean_of_compact`, with its
injective differential read as an immersion. -/
theorem exists_nonempty_euclidean_of_compact [CompactSpace M] [T2Space M] :
    ∃ n : ℕ, Nonempty (SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M
      (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨n, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  exact ⟨n, ⟨.ofIsSmoothEmbedding e
    ⟨he.isImmersion_of_injective_mfderiv (by simp) hinj, hemb.isEmbedding⟩⟩⟩

end Euclidean

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
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [CompactSpace M] [T2Space M]

/-- **Relative Whitney approximation into a compact manifold.** A continuous map `f` from a
σ-compact Hausdorff manifold, possibly with corners, into a compact boundaryless manifold which is
`C^n` on a neighbourhood `U` of a closed set `S` is homotopic relative to `S` to a `C^n` map. -/
theorem exists_contMDiff_homotopicRel (n : ℕ∞) (f : C(N, M)) {S U : Set N} (hS : IsClosed S)
    (hU : U ∈ 𝓝ˢ S) (hfU : ContMDiffOn I J n f U) :
    ∃ g : C(N, M), ContMDiff I J n g ∧ f.HomotopicRel g S := by
  obtain ⟨_, ⟨e⟩⟩ := TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact (I := J) (M := M)
  exact e.exists_contMDiff_homotopicRel n f hS hU hfU

/-- **Whitney approximation into a compact manifold.** Every continuous map from a σ-compact
Hausdorff manifold, possibly with corners, into a compact boundaryless manifold is homotopic to a
`C^n` map. -/
theorem exists_contMDiff_homotopic (n : ℕ∞) (f : C(N, M)) :
    ∃ g : C(N, M), ContMDiff I J n g ∧ f.Homotopic g := by
  obtain ⟨g, hg, hfg⟩ := f.exists_contMDiff_homotopicRel (I := I) n isClosed_empty
    (U := ∅) (by simp) (contMDiffOn_empty (I' := J))
  exact ⟨g, hg, hfg.homotopic⟩

/-- **Homotopic `C^n` maps into a compact manifold are `C^n` homotopic.** Two homotopic `C^n`
maps from a σ-compact Hausdorff manifold, possibly with corners, into a compact boundaryless
manifold are joined by a `C^n` map `K : N × ℝ → M` with `K (x, 0) = f₀ x` and
`K (x, 1) = f₁ x`. -/
theorem Homotopic.exists_contMDiff_homotopy {f₀ f₁ : C(N, M)} (h : f₀.Homotopic f₁) (n : ℕ∞)
    (hf₀ : ContMDiff I J n f₀) (hf₁ : ContMDiff I J n f₁) :
    ∃ K : N × ℝ → M, ContMDiff (I.prod 𝓘(ℝ, ℝ)) J n K ∧ (∀ x, K (x, 0) = f₀ x) ∧
      ∀ x, K (x, 1) = f₁ x := by
  obtain ⟨_, ⟨e⟩⟩ := TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact (I := J) (M := M)
  exact e.exists_contMDiff_homotopy n hf₀ hf₁ h

end ContinuousMap
