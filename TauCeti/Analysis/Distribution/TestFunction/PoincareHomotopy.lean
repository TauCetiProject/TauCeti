/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# Scalar multiples of the Poincaré homotopy operator on test forms

For a centre `x₀` in a real normed space `E` and a test `(k + 1)`-form `ω` on `Ω'`, the Poincaré
homotopy operator `TauCeti.poincareHomotopy x₀ ω` is smooth (`TauCeti.contDiff_poincareHomotopy`)
but need not be compactly supported: along every ray from `x₀` meeting the support of `ω`, the
radial integral can remain nonzero arbitrarily far from `x₀`.

Multiplying by a scalar test function `χ : 𝓓(Ω, ℝ)` restores compact support inside `Ω`, and
produces a continuous linear map `TestFunction.smulPoincareHomotopyCLM x₀ χ` from test
`(k + 1)`-forms on `Ω'` to test `k`-forms on `Ω` for the LF topologies. When `χ` is equal to `1`
near the support of a compactly supported `k`-current `T` on `Ω`, precomposing `T` with
`smulPoincareHomotopyCLM x₀ χ` defines the Euclidean cone current with apex `x₀`.

Where `χ = 1` near a set `s`, the operator satisfies the local germ homotopy identities
`d (χ • K ω) + χ • K (d ω) =ᶠ[𝓝ˢ s] ω` in positive degree and `χ • K (d f) =ᶠ[𝓝ˢ s] f - χ • f x₀`
in degree zero. Moreover, whenever the topological support of `ω` is disjoint from all segments
`[x₀, x]` for `x ∈ s`, the tube lemma along `[0, 1]` shows that `K ω` and `χ • K ω` vanish on a
neighbourhood of `s`.

## Main declarations

* `TestFunction.smulPoincareHomotopyCLM`: the continuous linear map `ω ↦ χ • poincareHomotopy x₀ ω`
  on test forms.
* `TestFunction.coe_smulPoincareHomotopyCLM`, `TestFunction.smulPoincareHomotopyCLM_apply`: its
  pointwise values.
* `TestFunction.tsupport_smulPoincareHomotopyCLM_subset_left`: its support lies in `tsupport χ`.
* `TauCeti.poincareHomotopy_eventuallyEq_zero_of_disjoint`,
  `TestFunction.smulPoincareHomotopyCLM_eventuallyEq_zero_of_disjoint`: vanishing in a
  neighbourhood of any set whose cone rays from `x₀` miss `tsupport ω`.
* `TestFunction.norm_smulPoincareHomotopyCLM_apply_le`: the sharp radial pointwise bound
  `‖χ x • K ω x‖ ≤ |χ x| * (B * ‖x - x₀‖ / (k + 1))`.
* `TestFunction.extDerivCLM_smulPoincareHomotopyCLM_add_eventuallyEq`,
  `TestFunction.smulPoincareHomotopyCLM_extDerivCLM_finZero_eventuallyEq`: the homotopy identities
  in `𝓝ˢ s` when `χ =ᶠ[𝓝ˢ s] 1`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.11 (cones over currents).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula and
  cone construction).
-/

public section

noncomputable section

open AffineMap Filter MeasureTheory Set TopologicalSpace TauCeti
open scoped Distributions Interval Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- If a closed set `C` misses every segment `[x₀, x]` for `x ∈ s`, then for all `y` in a
neighbourhood of `s`, the segment `[x₀, y]` also misses `C`. -/
private theorem eventually_lineMap_notMem_of_disjoint {x₀ : E} {C s : Set E} (hC : IsClosed C)
    (h : Disjoint C (⋃ x ∈ s, segment ℝ x₀ x)) :
    ∀ᶠ y in 𝓝ˢ s, ∀ t ∈ Icc (0 : ℝ) 1, lineMap x₀ y t ∉ C := by
  rw [eventually_iff_exists_mem]
  have hcont : Continuous (fun p : E × ℝ ↦ lineMap x₀ p.1 p.2) := by
    simp only [lineMap_apply_module']
    exact (continuous_snd.smul (continuous_fst.sub continuous_const)).add continuous_const
  have hO : IsOpen ((fun p : E × ℝ ↦ lineMap x₀ p.1 p.2) ⁻¹' Cᶜ) :=
    hC.isOpen_compl.preimage hcont
  refine ⟨{y : E | ∀ t ∈ Icc (0 : ℝ) 1, lineMap x₀ y t ∉ C}, ?_, fun _ hy ↦ hy⟩
  rw [mem_nhdsSet_iff_forall]
  intro x hxs
  have hsub : ({x} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ (fun p : E × ℝ ↦ lineMap x₀ p.1 p.2) ⁻¹' Cᶜ := by
    rintro ⟨y, t⟩ ⟨rfl : y = x, ht⟩ hmem
    exact h.le_bot ⟨hmem, mem_iUnion₂.2 ⟨y, hxs, lineMap_mem_segment ℝ x₀ y ht⟩⟩
  obtain ⟨u, v, huo, -, hxu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hO hsub
  refine Filter.mem_of_superset (huo.mem_nhds (hxu (mem_singleton x))) fun y hy t ht ↦ ?_
  simpa only [mem_preimage, mem_compl_iff] using huv (mk_mem_prod hy (hv ht))

/-- If the topological support of `ω` misses every segment `[x₀, x]` for `x ∈ s`, then
`poincareHomotopy x₀ ω` vanishes on a neighbourhood of `s`. No compactness assumption on `s` or
`tsupport ω` is needed: compactness of the parameter interval `[0, 1]` suffices via the tube
lemma at each point of `s`. -/
theorem poincareHomotopy_eventuallyEq_zero_of_disjoint {x₀ : E} {s : Set E}
    {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (h : Disjoint (tsupport ω) (⋃ x ∈ s, segment ℝ x₀ x)) :
    poincareHomotopy x₀ ω =ᶠ[𝓝ˢ s] 0 := by
  filter_upwards [eventually_lineMap_notMem_of_disjoint (isClosed_tsupport ω) h] with y hy
  rw [Pi.zero_apply, poincareHomotopy_congr (ω₂ := 0) fun z hz ↦ ?_, poincareHomotopy_zero,
    Pi.zero_apply]
  rcases segment_eq_image_lineMap ℝ x₀ y ▸ hz with ⟨t, ht, rfl⟩
  exact image_eq_zero_of_notMem_tsupport (hy t ht)

end TauCeti

namespace TestFunction

section BilinearIntegralBound

variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Pointwise spatial derivative bound for a bilinear radial integrand `t ^ k • L (ω (lineMap …)) V`
with `t ∈ [0, 1]`. Proved for abstract normed spaces `G, H` to avoid unfolding multilinear types. -/
private theorem norm_iteratedFDeriv_radialBilin_le (x₀ : E) (k : ℕ) (L : G →L[ℝ] E →L[ℝ] H)
    {V : E → E} (hV : ContDiff ℝ (⊤ : ℕ∞) V) {M : ℕ → ℝ}
    (hM : ∀ m y, ‖iteratedFDeriv ℝ m V y‖ ≤ M m) {ω : E → G} (hω : ContDiff ℝ (⊤ : ℕ∞) ω)
    {m : ℕ} {D : ℝ} (hD : ∀ j ≤ m, ∀ z, ‖iteratedFDeriv ℝ j ω z‖ ≤ D)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (y : E) :
    ‖iteratedFDeriv ℝ m (fun z ↦ t ^ k • L (ω (lineMap x₀ z t)) (V z)) y‖ ≤
      (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (‖L‖ * M (m - j))) * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (Nat.zero_le _) x₀)
  have ht_id : ‖t • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_right ht.1 ContinuousLinearMap.norm_id_le).trans ht.2
  have htk_id : ‖(t ^ k) • ContinuousLinearMap.id ℝ H‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ht.1 _)]
    exact (mul_le_of_le_one_right (pow_nonneg ht.1 _) ContinuousLinearMap.norm_id_le).trans
      (pow_le_one₀ ht.1 ht.2)
  have hray_cont : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ ω (lineMap x₀ z t)) := by
    simp only [lineMap_apply_module']
    exact hω.comp (((contDiff_id.sub contDiff_const).const_smul t).add contDiff_const)
  have hray_norm {j : ℕ} (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun z ↦ L (ω (lineMap x₀ z t))) y‖ ≤ ‖L‖ * D := by
    have hcompL : (fun z ↦ L (ω (lineMap x₀ z t))) = L ∘ (fun z ↦ ω (lineMap x₀ z t)) := rfl
    rw [hcompL]
    refine (L.norm_iteratedFDeriv_comp_left hray_cont.contDiffAt (by simp)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg L)
    have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ ω (z + (1 - t) • x₀)) :=
      hω.comp (contDiff_id.add contDiff_const)
    have hline : (fun z ↦ ω (lineMap x₀ z t)) =
        (fun z ↦ ω (z + (1 - t) • x₀)) ∘ (t • ContinuousLinearMap.id ℝ E) := by
      funext z
      simp [lineMap_apply_module, add_comm]
    rw [hline, (t • ContinuousLinearMap.id ℝ E).iteratedFDeriv_comp_right hshift y (by simp),
      iteratedFDeriv_comp_add_right]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hD j hj _)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) ht_id
  have hu_eq : (fun z ↦ t ^ k • L (ω (lineMap x₀ z t)) (V z)) =
      ((t ^ k) • ContinuousLinearMap.id ℝ H) ∘ fun z ↦ L (ω (lineMap x₀ z t)) (V z) := rfl
  have hclm_cont : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ L (ω (lineMap x₀ z t)) (V z)) :=
    (L.contDiff.comp hray_cont).clm_apply hV
  rw [hu_eq]
  refine (((t ^ k) • ContinuousLinearMap.id ℝ H).norm_iteratedFDeriv_comp_left
    hclm_cont.contDiffAt (by simp)).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) htk_id).trans ?_
  refine (norm_iteratedFDeriv_clm_apply (L.contDiff.comp hray_cont) hV y (by simp)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hMj : 0 ≤ M (m - j) := (norm_nonneg _).trans (hM (m - j) y)
  calc (m.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun z ↦ L (ω (lineMap x₀ z t))) y‖ *
        ‖iteratedFDeriv ℝ (m - j) V y‖
      ≤ (m.choose j : ℝ) * (‖L‖ * D) * M (m - j) := by
        gcongr
        exacts [hray_norm hjm, hM (m - j) y]
    _ = (m.choose j : ℝ) * (‖L‖ * M (m - j)) * D := by ring

/-- Absorbing a smooth compactly supported scalar multiplier `χ` into `V y = χ y • (y - x₀)` bounds
all spatial derivatives of `y ↦ ∫₀¹ t ^ k • L (ω (lineMap x₀ y t)) (V y) dt` globally in terms of
the first `i` derivatives of `ω`. -/
private theorem exists_norm_iteratedFDeriv_intervalIntegral_radialBilin_le [CompleteSpace H]
    (x₀ : E) (k : ℕ) (L : G →L[ℝ] E →L[ℝ] H) {χ : E → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (i : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ω : E → G), ContDiff ℝ (⊤ : ℕ∞) ω → HasCompactSupport ω → ∀ B : ℝ,
      (∀ j ≤ i, ∀ z, ‖iteratedFDeriv ℝ j ω z‖ ≤ B) →
      ∀ x, ‖iteratedFDeriv ℝ i
        (fun y ↦ ∫ t in (0 : ℝ)..1, t ^ k • L (ω (lineMap x₀ y t)) (χ y • (y - x₀))) x‖ ≤
        A * B := by
  let V : E → E := fun y ↦ χ y • (y - x₀)
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := hχ.smul (contDiff_id.sub contDiff_const)
  have hVc : HasCompactSupport V := hχc.smul_right
  have hVbd : ∀ m : ℕ, ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ m V y‖ ≤ M := fun m ↦
    Continuous.bounded_above_of_compact_support
      (hV.continuous_iteratedFDeriv (m := m) (by simp)) (hVc.iteratedFDeriv m)
  choose M hM using hVbd
  have hM0 (m : ℕ) : 0 ≤ M m := (norm_nonneg _).trans (hM m x₀)
  let A (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (‖L‖ * M (m - j))
  have hA0 (m : ℕ) : 0 ≤ A m :=
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (norm_nonneg L) (hM0 _))
  refine ⟨A i, hA0 i, fun ω hω hωc B hB x ↦ ?_⟩
  let u : ℝ → E → H := fun t y ↦ t ^ k • L (ω (lineMap x₀ y t)) (V y)
  have hωbd : ∀ j : ℕ, ∃ C : ℝ, ∀ z, ‖iteratedFDeriv ℝ j ω z‖ ≤ C := fun j ↦
    Continuous.bounded_above_of_compact_support
      (hω.continuous_iteratedFDeriv (m := j) (by simp)) (hωc.iteratedFDeriv j)
  choose Cω hCω using hωbd
  let Dω : ℝ := ∑ j ∈ Finset.range (i + 1), |Cω j|
  have hDω {j : ℕ} (hj : j ≤ i) (z : E) : ‖iteratedFDeriv ℝ j ω z‖ ≤ Dω :=
    (hCω j z).trans <| (le_abs_self _).trans <|
      Finset.single_le_sum (f := fun j ↦ |Cω j|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ u p.1 p.2) := by
    have hline_p : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ lineMap x₀ p.2 p.1) := by
      simp only [lineMap_apply_module']
      exact (contDiff_fst.smul (contDiff_snd.sub contDiff_const)).add contDiff_const
    exact (contDiff_fst.pow k).smul ((L.contDiff.comp (hω.comp hline_p)).clm_apply
      (hV.comp contDiff_snd))
  have hcont {m : ℕ} (z : E) : Continuous fun t : ℝ ↦ iteratedFDeriv ℝ m (u t) z :=
    (_root_.ContDiff.continuous_iteratedFDeriv_prod_right hG m (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hu_smooth (t : ℝ) : ContDiff ℝ i (u t) :=
    (hG.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hub (m : ℕ) (hm : m ≤ i) :
      ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ z, ‖iteratedFDeriv ℝ m (u t) z‖ ≤ A m * Dω := by
    rw [ae_restrict_iff' measurableSet_uIoc, uIoc_of_le zero_le_one]
    exact Eventually.of_forall fun t ht z ↦ norm_iteratedFDeriv_radialBilin_le x₀ k L hV hM hω
      (fun j hj w ↦ hDω (hj.trans hm) w) (Ioc_subset_Icc_self ht) z
  have hderiv := iteratedFDeriv_intervalIntegral (μ := volume) (a := 0) (b := 1)
    (u := u) (N := i) (Eventually.of_forall hu_smooth)
    (fun m _ z ↦ (hcont z).aestronglyMeasurable)
    (bound := fun m _ ↦ A m * Dω) (fun _ _ ↦ intervalIntegrable_const) hub le_rfl
  have hle : ∀ t ∈ Ι (0 : ℝ) 1, ‖iteratedFDeriv ℝ i (u t) x‖ ≤ A i * B := fun t ht ↦ by
    rw [uIoc_of_le zero_le_one] at ht
    exact norm_iteratedFDeriv_radialBilin_le x₀ k L hV hM hω hB (Ioc_subset_Icc_self ht) x
  rw [hderiv]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hle

end BilinearIntegralBound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω Ω' Ω₁ Ω₂ : Opens E} {k : ℕ}

section Bounds

variable [CompleteSpace F]

/-- The operator `ω ↦ χ • poincareHomotopy x₀ ω` on forms supported in a compact set `K`, landing
in forms supported in `tsupport χ`. -/
private def smulPoincareHomotopySupportedInCLM (x₀ : E) (χ : 𝓓(Ω, ℝ)) (K : Compacts E) :
    𝓓_{K}(E, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ]
      𝓓_{⟨tsupport χ, χ.hasCompactSupport⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
  letI P : 𝓓_{K}(E, E [⋀^Fin (k + 1)]→L[ℝ] F) →ₗ[ℝ]
      𝓓_{⟨tsupport χ, χ.hasCompactSupport⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
    { toFun ω := .of_support_subset
        (χ.contDiff.smul (contDiff_poincareHomotopy x₀ ω.contDiff))
        ((Function.support_smul_subset_left (χ : E → ℝ)
          (poincareHomotopy x₀ (ω : E → _))).trans (subset_tsupport _))
      map_add' ω η := ContDiffMapSupportedIn.ext fun x ↦ by
        simp [poincareHomotopy_add_apply ω.continuous.continuousOn η.continuous.continuousOn,
          smul_add]
      map_smul' c ω := ContDiffMapSupportedIn.ext fun x ↦ by
        simp [poincareHomotopy_smul, smul_comm (χ x) c] }
  { toLinearMap := P
    cont := by
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E) (F := F)
        (n := k)).toContinuousLinearMap
      obtain ⟨A, hA, h⟩ := exists_norm_iteratedFDeriv_intervalIntegral_radialBilin_le x₀ k L
        χ.contDiff χ.hasCompactSupport i
      refine ⟨Finset.range (i + 1), A, fun ω ↦ ((P ω).seminorm_le_iff ℝ
        (mul_nonneg hA (apply_nonneg _ _)) i).2 fun _ x _ ↦ ?_⟩
      have hP : (P ω : E → E [⋀^Fin k]→L[ℝ] F) = fun y ↦ χ y • poincareHomotopy x₀ ω y := rfl
      have heq : (fun y ↦ χ y • poincareHomotopy x₀ ω y) = fun y ↦
          ∫ t in (0 : ℝ)..1, t ^ k • L (ω (lineMap x₀ y t)) (χ y • (y - x₀)) := by
        funext y
        rw [poincareHomotopy_apply, ← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun t _ ↦ ?_
        rw [smul_comm (χ y), ← map_smul]
        rfl
      rw [hP, heq]
      refine h ω ω.contDiff ω.hasCompactSupport _ (fun j hj z ↦ ?_) x
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_range.2 (Nat.lt_succ_of_le hj))) }

/-- **Scalar multiple of the Poincaré homotopy operator on test forms.** Given a centre `x₀ : E`
and a scalar test function `χ : 𝓓(Ω, ℝ)`, `smulPoincareHomotopyCLM x₀ χ` sends a test
`(k + 1)`-form `ω` on `Ω'` to the test `k`-form `x ↦ χ x • poincareHomotopy x₀ ω x` on `Ω`,
continuously for the LF topologies. -/
def smulPoincareHomotopyCLM (x₀ : E) (χ : 𝓓(Ω, ℝ)) :
    𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  letI T (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
    ⟨fun x ↦ χ x • poincareHomotopy x₀ ω x,
      χ.contDiff.smul (contDiff_poincareHomotopy x₀ ω.contDiff),
      χ.hasCompactSupport.smul_right,
      (tsupport_smul_subset_left (χ : E → ℝ)
        (poincareHomotopy x₀ (ω : E → _))).trans χ.tsupport_subset⟩
  TestFunction.limitCLM ℝ T
    (fun K _ ↦ ofSupportedInCLM ℝ χ.tsupport_subset ∘L
      smulPoincareHomotopySupportedInCLM x₀ χ K)
    (fun _ _ _ ↦ rfl)

@[simp]
theorem coe_smulPoincareHomotopyCLM (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    ⇑(smulPoincareHomotopyCLM x₀ χ ω) = ⇑χ • poincareHomotopy x₀ ω :=
  (rfl)

theorem smulPoincareHomotopyCLM_apply (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    smulPoincareHomotopyCLM x₀ χ ω x = χ x • poincareHomotopy x₀ ω x :=
  (rfl)

@[simp]
theorem smulPoincareHomotopyCLM_zero (x₀ : E) :
    (smulPoincareHomotopyCLM x₀ (0 : 𝓓(Ω, ℝ)) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) = 0 := by
  ext ω x : 2
  simp

theorem smulPoincareHomotopyCLM_add (x₀ : E) (χ₁ χ₂ : 𝓓(Ω, ℝ)) :
    (smulPoincareHomotopyCLM x₀ (χ₁ + χ₂) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) =
      smulPoincareHomotopyCLM x₀ χ₁ + smulPoincareHomotopyCLM x₀ χ₂ := by
  ext ω x : 2
  simp [add_smul]

theorem smulPoincareHomotopyCLM_smul (x₀ : E) (c : ℝ) (χ : 𝓓(Ω, ℝ)) :
    (smulPoincareHomotopyCLM x₀ (c • χ) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) =
      c • smulPoincareHomotopyCLM x₀ χ := by
  ext ω x : 2
  simp [smul_smul]

/-- Extending the multiplier `χ` from `Ω₁` to `Ω₂` commutes with extending the resulting test
form. -/
theorem smulPoincareHomotopyCLM_monoCLM (x₀ : E) (χ : 𝓓(Ω₁, ℝ)) :
    (smulPoincareHomotopyCLM x₀ (monoCLM ℝ χ : 𝓓(Ω₂, ℝ)) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω₂, E [⋀^Fin k]→L[ℝ] F)) =
      (monoCLM ℝ : 𝓓(Ω₁, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω₂, E [⋀^Fin k]→L[ℝ] F)) ∘L
        (smulPoincareHomotopyCLM x₀ χ :
          𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω₁, E [⋀^Fin k]→L[ℝ] F)) := by
  ext ω x : 2
  by_cases h : Ω₁ ≤ Ω₂ <;> simp [monoCLM_apply, h]

/-- The topological support of `smulPoincareHomotopyCLM x₀ χ ω` lies in `tsupport χ`. -/
theorem tsupport_smulPoincareHomotopyCLM_subset_left (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (smulPoincareHomotopyCLM x₀ χ ω : E → E [⋀^Fin k]→L[ℝ] F) ⊆ tsupport χ := by
  rw [coe_smulPoincareHomotopyCLM]
  exact tsupport_smul_subset_left (χ : E → ℝ) (poincareHomotopy x₀ (ω : E → _))

/-- If the topological support of `ω` is disjoint from every segment `[x₀, x]` for `x ∈ s`, then
`smulPoincareHomotopyCLM x₀ χ ω` vanishes on a neighbourhood of `s`. -/
theorem smulPoincareHomotopyCLM_eventuallyEq_zero_of_disjoint (x₀ : E) (χ : 𝓓(Ω, ℝ)) {s : Set E}
    {ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)}
    (h : Disjoint (tsupport ω) (⋃ x ∈ s, segment ℝ x₀ x)) :
    (smulPoincareHomotopyCLM x₀ χ ω : E → E [⋀^Fin k]→L[ℝ] F) =ᶠ[𝓝ˢ s] 0 := by
  filter_upwards [poincareHomotopy_eventuallyEq_zero_of_disjoint h] with x hx
  simp [hx]

/-- Pointwise radial norm bound for `smulPoincareHomotopyCLM`: if `‖ω y‖ ≤ B` along `[x₀, x]`,
then `‖χ x • K ω x‖ ≤ |χ x| * (B * ‖x - x₀‖ / (k + 1))`. -/
theorem norm_smulPoincareHomotopyCLM_apply_le (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E} {B : ℝ}
    (h : ∀ y ∈ segment ℝ x₀ x, ‖ω y‖ ≤ B) :
    ‖smulPoincareHomotopyCLM x₀ χ ω x‖ ≤ |χ x| * (B * ‖x - x₀‖ / (k + 1)) := by
  rw [smulPoincareHomotopyCLM_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_poincareHomotopy_le h) (abs_nonneg _)

/-- **Local homotopy formula in positive degree.** Where `χ` is equal to `1` on a neighbourhood of
`s`, `d (χ • K ω) + χ • K (d ω)` agrees with `ω` on a neighbourhood of `s`. -/
theorem extDerivCLM_smulPoincareHomotopyCLM_add_eventuallyEq (x₀ : E) {χ : 𝓓(Ω, ℝ)} {s : Set E}
    (hχ : ∀ᶠ x in 𝓝ˢ s, χ x = 1) (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    (extDerivCLM (smulPoincareHomotopyCLM x₀ χ ω) +
      smulPoincareHomotopyCLM x₀ χ (extDerivCLM ω) : E → E [⋀^Fin (k + 1)]→L[ℝ] F) =ᶠ[𝓝ˢ s] ω := by
  filter_upwards [hχ, hχ.eventually_nhdsSet] with y hy1 hy_nhds
  have hloc : (smulPoincareHomotopyCLM x₀ χ ω : E → E [⋀^Fin k]→L[ℝ] F) =ᶠ[𝓝 y]
      poincareHomotopy x₀ ω :=
    hy_nhds.mono fun z hz ↦ by simp [hz]
  rw [Pi.add_apply, extDerivCLM_apply, smulPoincareHomotopyCLM_apply, coe_extDerivCLM, hy1,
    one_smul ℝ, hloc.extDeriv_eq]
  exact extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv x₀ (ω.contDiff.of_le (by simp)) y

/-- **Local homotopy formula in degree zero.** Where `χ` is equal to `1` on a neighbourhood of
`s`, `χ • K (d ω)` agrees on a neighbourhood of `s` with `ω - χ • ω x₀`, written using
`TestFunction.postcompCLM` so both terms are test `0`-forms on `Ω`. -/
theorem smulPoincareHomotopyCLM_extDerivCLM_finZero_eventuallyEq (x₀ : E) {χ : 𝓓(Ω, ℝ)}
    {s : Set E} (hχ : ∀ᶠ x in 𝓝ˢ s, χ x = 1) (ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F)) :
    (smulPoincareHomotopyCLM x₀ χ (extDerivCLM ω) : E → E [⋀^Fin 0]→L[ℝ] F) =ᶠ[𝓝ˢ s]
      ⇑(ω - postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (ω x₀)) χ) := by
  filter_upwards [hχ] with y hy
  rw [FunLike.coe_sub, Pi.sub_apply, smulPoincareHomotopyCLM_apply, coe_extDerivCLM,
    postcompCLM_apply, Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, hy,
    one_smul ℝ, one_smul ℝ]
  exact poincareHomotopy_extDeriv_eq_sub x₀ (ω.contDiff.of_le (by simp)) y

end Bounds

end TestFunction
