/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Leibniz
public import TauCeti.Analysis.Holder.Iterated
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Quantitative localization of finite-order Hölder maps

A globally smooth supported cutoff turns local `C^{k,α}` data on an open convex set into an
actual bounded `C^{k,α}` map on the ambient space. Only the top source jet needs an explicit
Hölder hypothesis; the lower jets are controlled by the mean-value inequality.

Convexity of the open set is only needed near the support of the cutoff: when the `δ`-thickening
of `tsupport χ` lies in the open set, the Leibniz bound on balls of radius `δ` centred in the
support, together with the supremum bound at larger distances, makes the top derivative of the
cutoff product globally Hölder
(`TauCeti.holderWith_iteratedFDeriv_cutoff_smul_of_thickening_subset`).

The same cutoff lowers the Hölder exponent of a derivative: a `C¹` map whose derivative is
`α`-Hölder on the whole space agrees on any ball with a `C¹` map whose derivative is `α'`-Hölder on
the whole space, for every `α' ≤ min α 1` (`ContDiff.exists_eqOn_ball_and_holderWith_fderiv`).
-/

public section

open Set Metric
open scoped NNReal Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The cutoff product has a bounded derivative of every available order, with the binomial
Leibniz bound. The source function is unrestricted outside the open set. -/
theorem norm_iteratedFDeriv_cutoff_smul_le {k j : ℕ} {s : Set E} {f : E → F} {χ : E → ℝ}
    {M N : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hχ : ContDiff ℝ k χ) (hs : IsOpen s)
    (hχs : tsupport χ ⊆ s) (hj : j ≤ k)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => χ y • f y) x‖ ≤ (2 : ℝ)^j * N * M := by
  by_cases hx : x ∈ s
  · have hjorder : (j : WithTop ℕ∞) ≤ k := by exact_mod_cast hj
    have h := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hf hs.uniqueDiffOn hx hjorder
    simp_rw [iteratedFDerivWithin_of_isOpen _ hs hx] at h
    refine h.trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * N * M := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        · exact hχb i (by have := Finset.mem_range.mp hi; omega) x
        · exact hfb (j-i) (by omega) x hx
      _ = (2 : ℝ)^j * N * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose j
  · have h0 : (fun y => χ y • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hχs h)] with y hy
      simp [hy]
    rw [(h0.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
    have hnonneg : (0 : ℝ) ≤ 2^j * N * M := by positivity
    simpa using hnonneg

/-- The top derivative of a cutoff product is globally Hölder. The constant involves only the
source jet bound, its top Hölder constant, and the cutoff jets through order `k + 1`. -/
theorem holderWith_iteratedFDeriv_cutoff_smul {k : ℕ} {s : Set E} {f : E → F} {χ : E → ℝ}
    {M N H α : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hχ : ContDiff ℝ (k + 1) χ)
    (hs : IsOpen s) (hc : Convex ℝ s) (hχs : tsupport χ ⊆ s) (hα : α ≤ 1)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N)
    (hfH : HolderOnWith H α (iteratedFDeriv ℝ k f) s) :
    HolderWith ((2 : ℝ≥0)^k * N * (H + 6 * M)) α
      (iteratedFDeriv ℝ k (fun x => χ x • f x)) := by
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip
  have hL : ‖L‖₊ ≤ 1 := by
    dsimp [L]
    rw [ContinuousLinearMap.opNNNorm_flip]
    exact ContinuousLinearMap.opNNNorm_lsmul_le
  have h := L.holderWith_iteratedFDeriv_of_tsupport_subset_right hf
    (hχ.of_le (by simp)) hs hχs hfb (fun i hi => hχb i (by omega))
    (fun j hj ↦ hf.holderOnWith_iteratedFDeriv_of_le hs hc hj hα hfb hfH)
    (fun j hj ↦ hχ.holderWith_iteratedFDeriv_of_le hj hα hχb)
  apply h.mono
  calc
    _ ≤ (2 : ℝ≥0)^k * 1 * (M * (3 * N) + N * (H + 3 * M)) := by
      gcongr
    _ = _ := by ring

/-- On a convex open set `s` on which `f` is `C^k`, with derivatives through order `k` bounded
by `M` and `k`-th derivative `α`-Hölder with constant `H`, the `k`-th derivative of the product
`χ f` with a `C^{k+1}` function `χ` whose derivatives through order `k + 1` are bounded by `N` is
`α`-Hölder on `s` with constant `2^k N (H + 6 M)`. -/
theorem holderOnWith_iteratedFDeriv_smul_of_convex {k : ℕ} {s : Set E} {f : E → F}
    {χ : E → ℝ} {M N H α : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hχ : ContDiff ℝ (k + 1) χ)
    (hs : IsOpen s) (hc : Convex ℝ s) (hα : α ≤ 1)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N)
    (hfH : HolderOnWith H α (iteratedFDeriv ℝ k f) s) :
    HolderOnWith ((2 : ℝ≥0) ^ k * N * (H + 6 * M)) α
      (iteratedFDeriv ℝ k (fun x ↦ χ x • f x)) s := by
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  have hL : ‖L‖₊ ≤ 1 := ContinuousLinearMap.opNNNorm_lsmul_le
  have h := L.holderOnWith_iteratedFDeriv_comp₂ (hχ.contDiffOn.of_le (by simp)) hf hs
    (fun j hj y _ ↦ hχb j (by omega) y) hfb
    (fun j hj ↦ (hχ.holderWith_iteratedFDeriv_of_le hj hα hχb).holderOnWith s)
    (fun j hj ↦ hf.holderOnWith_iteratedFDeriv_of_le hs hc hj hα hfb hfH)
  have hLf : (fun x ↦ L (χ x) (f x)) = fun x ↦ χ x • f x := by
    ext x
    simp [L]
  rw [hLf] at h
  refine h.mono_const ?_
  calc
    _ ≤ (2 : ℝ≥0) ^ k * 1 * (N * (H + 3 * M) + M * (3 * N)) := by gcongr
    _ = _ := by ring

/-- The `k`-th derivative of a cutoff product `χ f` is globally `α`-Hölder when the
`δ`-thickening of the support of the cutoff lies in an open set `s` on which `f` is `C^k`, with
derivatives through order `k` bounded by `M` and `k`-th derivative `α`-Hölder with constant `H`.
No convexity of `s` is needed: the lower derivatives of `f` are only used on balls of radius `δ`
centred in the support of `χ`. -/
theorem holderWith_iteratedFDeriv_cutoff_smul_of_thickening_subset {k : ℕ} {s : Set E}
    {f : E → F} {χ : E → ℝ} {M N H α δ : ℝ≥0} (hf : ContDiffOn ℝ k f s)
    (hχ : ContDiff ℝ (k + 1) χ) (hs : IsOpen s) (hδ : 0 < δ)
    (hχs : thickening δ (tsupport χ) ⊆ s) (hα : α ≤ 1)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ N)
    (hfH : HolderOnWith H α (iteratedFDeriv ℝ k f) s) :
    HolderWith ((2 : ℝ≥0) ^ k * N * (H + 6 * M + 2 * M * δ ^ (-(α : ℝ)))) α
      (iteratedFDeriv ℝ k (fun x ↦ χ x • f x)) := by
  have hts : tsupport χ ⊆ s := (self_subset_thickening (by exact_mod_cast hδ) _).trans hχs
  -- The derivative of the product vanishes outside the support of the cutoff.
  have hzero : ∀ x ∉ tsupport χ, iteratedFDeriv ℝ k (fun x ↦ χ x • f x) x = 0 := fun x hx ↦
    Function.notMem_support.1 fun h ↦
      hx (tsupport_smul_subset_left _ _ (support_iteratedFDeriv_subset k h))
  -- On a ball of radius `δ` centred in the support, the Leibniz rule gives a Hölder bound.
  have hball : ∀ x ∈ tsupport χ, HolderOnWith ((2 : ℝ≥0) ^ k * N * (H + 6 * M)) α
      (iteratedFDeriv ℝ k (fun x ↦ χ x • f x)) (ball x δ) := fun x hx ↦ by
    have hB : ball x δ ⊆ s := (ball_subset_thickening hx _).trans hχs
    exact holderOnWith_iteratedFDeriv_smul_of_convex (hf.mono hB) hχ isOpen_ball
      (convex_ball x δ) hα (fun j hj y hy ↦ hfb j hj y (hB hy)) hχb (hfH.mono hB)
  have hbd : ∀ x, ‖iteratedFDeriv ℝ k (fun x ↦ χ x • f x) x‖ ≤ (2 : ℝ) ^ k * N * M :=
    norm_iteratedFDeriv_cutoff_smul_le hf (hχ.of_le (by simp)) hs hts le_rfl hfb
      (fun i hi ↦ hχb i (by omega))
  have h := HolderOnWith.of_dist_lt_of_dist_le (s := univ) (r := α) (D := 2 * 2 ^ k * N * M) hδ
    (K := (2 : ℝ≥0) ^ k * N * (H + 6 * M))
    (f := iteratedFDeriv ℝ k (fun x ↦ χ x • f x)) (fun x _ y _ hxy ↦ ?_)
    (fun x _ y _ ↦ (dist_le_norm_add_norm _ _).trans (by
      push_cast
      linarith [hbd x, hbd y]))
  · refine holderOnWith_univ.mp (h.mono_const (le_of_eq ?_))
    ring
  · by_cases hx : x ∈ tsupport χ
    · exact (hball x hx).dist_le (mem_ball_self (by exact_mod_cast hδ))
        (by rwa [mem_ball, dist_comm])
    by_cases hy : y ∈ tsupport χ
    · rw [dist_comm x y, dist_comm (iteratedFDeriv ℝ k _ x)]
      exact (hball y hy).dist_le (mem_ball_self (by exact_mod_cast hδ)) (by rwa [mem_ball])
    rw [hzero x hx, hzero y hy, dist_self]
    positivity

/-- **Lowering the Hölder exponent of a derivative away from a ball.** Let `f` be `C¹` with
`α`-Hölder derivative on the whole space and let `α' ≤ α` with `α' ≤ 1`. On every ball, `f` agrees
with a `C¹` map whose derivative is `α'`-Hölder on the whole space. The derivative of `f` itself is
`α'`-Hölder only on bounded sets; the map is the product of `f` with a cutoff equal to one on the
ball. -/
theorem _root_.ContDiff.exists_eqOn_ball_and_holderWith_fderiv [FiniteDimensional ℝ E]
    {f : E → F} (hf : ContDiff ℝ 1 f) {K α α' : ℝ≥0} (hfK : HolderWith K α (fderiv ℝ f))
    (hα' : α' ≤ α) (hα'1 : α' ≤ 1) (x₀ : E) (R : ℝ) :
    ∃ (g : E → F) (K' : ℝ≥0), ContDiff ℝ 1 g ∧ EqOn g f (ball x₀ R) ∧
      HolderWith K' α' (fderiv ℝ g) := by
  set ρ : ℝ := |R| + 1
  have hρ : 0 < ρ := by positivity
  obtain ⟨ζ, Z, hζ⟩ := exists_forall_contDiff_cutoff_holderWith_and_norm_le (E := E)
    (show ρ < 2 * ρ by linarith) hα'1
  obtain ⟨hζs, hζ1, hζt, -, hζb⟩ := hζ x₀
  -- On `s = B(x₀, 3ρ)`, which contains the `ρ`-thickening of the support of the cutoff, `f` and
  -- `Df` are bounded and `Df` is `α'`-Hölder.
  set s := ball x₀ (3 * ρ)
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall x₀ (3 * ρ)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall x₀ (3 * ρ)).exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  have hfb : ∀ i ≤ 1, ∀ x ∈ s, ‖iteratedFDeriv ℝ i f x‖ ≤ max M₀.toNNReal M₁.toNNReal := by
    intro i hi x hx
    have hx' : x ∈ closedBall x₀ (3 * ρ) := ball_subset_closedBall hx
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      exact (hM₀ x hx').trans ((Real.le_coe_toNNReal _).trans (by simp))
    · rw [norm_iteratedFDeriv_one]
      exact (hM₁ x hx').trans ((Real.le_coe_toNNReal _).trans (by simp))
  have hζb' : ∀ i ≤ 1 + 1, ∀ x, ‖iteratedFDeriv ℝ i (ζ x₀) x‖ ≤ Z := fun i hi x => by
    interval_cases i
    · simpa using (hζb x).1
    · simpa using (hζb x).2.1
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]; exact (hζb x).2.2
  have hD : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ (6 * ρ).toNNReal := fun x hx y hy => by
    rw [edist_dist, ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal,
      Real.coe_toNNReal _ (by positivity)]
    linarith [dist_triangle_right x y x₀, mem_ball.1 hx, mem_ball.1 hy]
  -- The first iterated derivative is the derivative, up to the linear isometry
  -- `continuousMultilinearCurryFin1`.
  have hcurry := LinearIsometryEquiv.isometry (continuousMultilinearCurryFin1 ℝ E F)
  have hfH : HolderOnWith (K * (6 * ρ).toNNReal ^ ((α : ℝ) - α')) α' (iteratedFDeriv ℝ 1 f) s := by
    have h := (hfK.holderOnWith s).of_le hD hα'
    rw [fderiv_eq_continuousMultilinearCurryFin1_comp] at h
    exact fun x hx y hy => by simpa only [Function.comp_apply, hcurry.edist_eq] using h x hx y hy
  have hthick : thickening ((ρ.toNNReal : ℝ≥0) : ℝ) (tsupport (ζ x₀)) ⊆ s := by
    rw [Real.coe_toNNReal _ hρ.le]
    refine (thickening_subset_of_subset ρ hζt).trans ((Metric.thickening_ball _ _ _).trans
      (ball_subset_ball (by linarith)))
  have H := holderWith_iteratedFDeriv_cutoff_smul_of_thickening_subset (k := 1) hf.contDiffOn
    (hζs.of_le (by norm_cast)) isOpen_ball (by simpa using hρ) hthick hα'1 hfb hζb' hfH
  refine ⟨fun x => ζ x₀ x • f x, _, (hζs.of_le (by norm_cast)).smul hf, fun x hx => ?_,
    by rwa [fderiv_eq_continuousMultilinearCurryFin1_comp, hcurry.holderWith_comp_iff]⟩
  have h1 : ζ x₀ x = 1 := interior_subset (hζ1 (ball_subset_closedBall
    (ball_subset_ball (by linarith [le_abs_self R]) hx)))
  simp [h1]

namespace CkHolderSpace

variable {k : ℕ} {s : Set E} {f : E → F} {χ : E → ℝ} {M N H α : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hχ : ContDiff ℝ (k + 1) χ)
    (hs : IsOpen s) (hc : Convex ℝ s) (hχs : tsupport χ ⊆ s) (hα : α ≤ 1)
    (hfb : ∀ i ≤ k, ∀ x ∈ s, ‖_root_.iteratedFDeriv ℝ i f x‖ ≤ M)
    (hχb : ∀ i ≤ k + 1, ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ N)
    (hfH : HolderOnWith H α (_root_.iteratedFDeriv ℝ k f) s)

/-- Globalize local `C^{k,α}` data by multiplication by a supported `C^{k + 1}` cutoff.
The result is the actual product, with its actual iterated Fréchet derivatives. -/
noncomputable def cutoff : CkHolderSpace k α E F :=
  ofContDiff (fun x => χ x • f x)
    (hf.contDiff_smul_of_tsupport_subset hs (hχ.of_le (by simp)).contDiffOn hχs)
    (fun j hj => ⟨(2 : ℝ)^j * N * M,
      norm_iteratedFDeriv_cutoff_smul_le hf (hχ.of_le (by simp)) hs hχs hj hfb
        (fun i hi => hχb i (by omega))⟩)
    ⟨_, holderWith_iteratedFDeriv_cutoff_smul hf hχ hs hc hχs hα hfb hχb hfH⟩

@[simp]
theorem coe_cutoff : ⇑(cutoff hf hχ hs hc hχs hα hfb hχb hfH) = fun x => χ x • f x := by
  exact coe_ofContDiff _ _ _ _

@[simp]
theorem cutoff_apply (x : E) : cutoff hf hχ hs hc hχs hα hfb hχb hfH x = χ x • f x :=
  congrFun (coe_cutoff hf hχ hs hc hχs hα hfb hχb hfH) x

/-- Every derivative field of the localized map satisfies the quantitative Leibniz bound. -/
theorem norm_iteratedFDeriv_cutoff_le {j : ℕ} (hj : j ≤ k) (x : E) :
    ‖_root_.iteratedFDeriv ℝ j (cutoff hf hχ hs hc hχs hα hfb hχb hfH) x‖ ≤
      (2 : ℝ)^j * N * M := by
  rw [coe_cutoff]
  exact norm_iteratedFDeriv_cutoff_smul_le hf (hχ.of_le (by simp)) hs hχs hj hfb
    (fun i hi => hχb i (by omega)) x

/-- The complete native supremum-plus-top-seminorm is controlled by local data. -/
theorem norm_cutoff_le : ‖cutoff hf hχ hs hc hχs hα hfb hχb hfH‖ ≤
    (2 : ℝ)^k * N * (H + (k + 7) * M) := by
  let u := cutoff hf hχ hs hc hχs hα hfb hχb hfH
  have hb (i : Fin (k + 1)) : ‖u.iteratedFDeriv i‖ ≤ (2 : ℝ)^k * N * M := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro x
    rw [coe_iteratedFDeriv]
    exact (norm_iteratedFDeriv_cutoff_le hf hχ hs hc hχs hα hfb hχb hfH
      (by omega : i.val ≤ k) x).trans (by
        gcongr
        · norm_num
        · omega)
  have hh : (nnHolderNorm α (_root_.iteratedFDeriv ℝ k u) : ℝ) ≤
      (2 : ℝ)^k * N * (H + 6 * M) := by
    have h := (holderWith_iteratedFDeriv_cutoff_smul hf hχ hs hc hχs hα hfb hχb hfH).nnholderNorm_le
    rw [coe_cutoff]
    exact_mod_cast h
  rw [norm_eq]
  calc
    _ ≤ ∑ _ : Fin (k + 1), ((2 : ℝ)^k * N * M) + (2 : ℝ)^k * N * (H + 6 * M) :=
      add_le_add (Finset.sum_le_sum fun i _ => hb i) hh
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- The localized map has topological support inside that of the cutoff. -/
theorem tsupport_cutoff_subset : tsupport (cutoff hf hχ hs hc hχs hα hfb hχb hfH) ⊆
    tsupport χ := by
  rw [coe_cutoff]
  exact tsupport_smul_subset_left _ _

/-- Localization lands in the native submodule supported in the local domain. -/
theorem cutoff_mem_supported : cutoff hf hχ hs hc hχs hα hfb hχb hfH ∈
    supportedCkHolderSubmodule k α s := by
  rw [mem_supportedCkHolderSubmodule_iff]
  intro x hx
  rw [cutoff_apply, image_eq_zero_of_notMem_tsupport (fun h => hx (hχs h)), zero_smul]

/-- Where the cutoff is one on a neighborhood, localization preserves every actual derivative,
including derivatives beyond the regularity assumed in the construction. -/
theorem iteratedFDeriv_cutoff_eq {x : E} (hχone : χ =ᶠ[𝓝 x] 1) (j : ℕ) :
    _root_.iteratedFDeriv ℝ j (cutoff hf hχ hs hc hχs hα hfb hχb hfH) x =
      _root_.iteratedFDeriv ℝ j f x := by
  rw [coe_cutoff]
  have h : (fun y => χ y • f y) =ᶠ[𝓝 x] f := by
    filter_upwards [hχone] with y hy
    simp [hy]
  exact (h.iteratedFDeriv ℝ j).self_of_nhds

end CkHolderSpace

end TauCeti
