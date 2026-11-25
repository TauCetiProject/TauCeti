/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# The `W^{k,p}` size of a `Cᵏ` function

For a function `f` that is `Cᵏ` on an open planar set `S`, the classical derivative is a weak
derivative, so the extended `W^{k,p}(S)` norm `TauCeti.eLpNormWkp p S k f` is the sum of the
`Lᵖ(S)` norms of the classical iterated derivatives of `f` of orders `0` through `k`
(`TauCeti.eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv`).

This gives the Leibniz bound `TauCeti.eLpNormWkp_bilin_le`: if `V ⊆ U` are open, `a` and `f` are
`Cᵏ` on `U`, the derivatives of `a` of order at most `k` are bounded by `c` on `V`, and those of the
product `B (a y) (f y)` for a continuous bilinear map `B` vanish on `U \ V`, then
`‖B a f‖_{W^{k,p}(U)} ≤ C ‖f‖_{W^{k,p}(V)}`, with `C` depending on `k`, `‖B‖` and `c`. With
`V = U` it bounds multiplication by a coefficient with bounded derivatives; with a cutoff `a` that
vanishes near `U \ V` it localizes the norm of `a f` on `U` to that of `f` on `V`.

## Main results

* `IsCompact.exists_bound_iteratedFDeriv`: bounded derivatives on compact sets.
* `TauCeti.eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv`: the `W^{k,p}` norm of a `Cᵏ` function on an
  open set.
* `TauCeti.eLpNormWkp_bilin_le`: the Leibniz bound.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {p : ℝ≥0∞}

/-- The iterated derivatives of a function that is `Cᵐ` on an open set `S`, up to order `m`, are
almost everywhere strongly measurable on `S`. -/
theorem aestronglyMeasurable_iteratedFDeriv_of_contDiffOn {S : Set ℂ} (hS : IsOpen S) {m l : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}
    (hf : ContDiffOn ℝ m f S) (hl : l ≤ m) :
    AEStronglyMeasurable (iteratedFDeriv ℝ l f) (volume.restrict S) :=
  (ContinuousOn.continuousOn_iteratedFDeriv hf hS (by exact_mod_cast hl)).aestronglyMeasurable
    hS.measurableSet

/-- The `Lᵖ` norm of a function `Cᵐ` on an open set `S` is that of its zeroth derivative. -/
private theorem eLpNorm_eq_eLpNorm_iteratedFDeriv_zero {S : Set ℂ} (hS : IsOpen S) {m : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}
    (hf : ContDiffOn ℝ m f S) :
    eLpNorm f p (volume.restrict S) = eLpNorm (iteratedFDeriv ℝ 0 f) p (volume.restrict S) :=
  eLpNorm_congr_norm_ae (hf.continuousOn.aestronglyMeasurable hS.measurableSet)
    (aestronglyMeasurable_iteratedFDeriv_of_contDiffOn hS hf (Nat.zero_le m))
    (ae_of_all _ fun _ ↦ (norm_iteratedFDeriv_zero).symm)

/-- **The `W^{k,p}` norm of a `Cᵏ` function.** On an open set `S`, the `W^{k,p}(S)` norm of a
function that is `Cᵏ` on `S` is the sum of the `Lᵖ(S)` norms of its classical iterated derivatives
of orders `0` through `k`. -/
theorem eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv {S : Set ℂ} (hS : IsOpen S) (k : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F}
    (hf : ContDiffOn ℝ k f S) :
    eLpNormWkp p S k f =
      ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l f) p (volume.restrict S) := by
  induction k generalizing F f with
  | zero => rw [eLpNormWkp_zero, Finset.sum_range_one, eLpNorm_eq_eLpNorm_iteratedFDeriv_zero hS hf]
  | succ k ih =>
    have hD : HasWeakFDerivOn volume (⟨S, hS⟩ : TopologicalSpace.Opens ℂ) f (fderiv ℝ f) :=
      (hf.of_le (by exact_mod_cast Nat.le_add_left 1 k)).hasWeakFDerivOn_fderiv
    have hf' : ContDiffOn ℝ k (fderiv ℝ f) S :=
      hf.fderiv_of_isOpen hS (by exact_mod_cast le_rfl)
    have h := eLpNormWkp_succ_eq_of_hasWeakFDerivOn (p := p) (k := k) hD
    rw [TopologicalSpace.Opens.coe_mk] at h
    rw [h, ih hf', Finset.sum_range_succ' _ (k + 1), add_comm,
      eLpNorm_eq_eLpNorm_iteratedFDeriv_zero hS hf]
    congr 1
    refine Finset.sum_congr rfl fun l hl ↦ eLpNorm_congr_norm_ae
      (aestronglyMeasurable_iteratedFDeriv_of_contDiffOn hS hf' (Finset.mem_range_succ_iff.1 hl))
      (aestronglyMeasurable_iteratedFDeriv_of_contDiffOn hS hf
        (Nat.succ_le_succ (Finset.mem_range_succ_iff.1 hl)))
      (ae_of_all _ fun _ ↦ norm_iteratedFDeriv_fderiv)

/-- The iterated derivatives of order at most `m` of a function that is `Cᵐ` on an open set `O`
are bounded on every compact subset of `O`, by one constant. -/
theorem _root_.IsCompact.exists_bound_iteratedFDeriv {O K : Set ℂ} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℂ → F}
    (hg : ContDiffOn ℝ m g O) : ∃ c : ℝ≥0, ∀ x ∈ K, ∀ l ≤ m, ‖iteratedFDeriv ℝ l g x‖ ≤ c := by
  have h (l : ℕ) : ∃ C : ℝ, l ≤ m → ∀ x ∈ K, ‖iteratedFDeriv ℝ l g x‖ ≤ C := by
    by_cases hl : l ≤ m
    · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
        ((ContinuousOn.continuousOn_iteratedFDeriv hg hO (by exact_mod_cast hl)).mono hKO)
      exact ⟨C, fun _ ↦ hC⟩
    · exact ⟨0, fun h ↦ absurd h hl⟩
  choose C hC using h
  refine ⟨∑ l ∈ Finset.range (m + 1), ‖C l‖₊, fun x hx l hl ↦ ?_⟩
  calc ‖iteratedFDeriv ℝ l g x‖ ≤ C l := hC l hl x hx
    _ ≤ ‖C l‖₊ := Real.le_norm_self _
    _ ≤ _ := by
        exact_mod_cast Finset.single_le_sum (f := fun l ↦ ‖C l‖₊) (fun _ _ ↦ zero_le)
          (Finset.mem_range_succ_iff.2 hl)

variable {G₁ G₂ G₃ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [NormedAddCommGroup G₂]
  [NormedSpace ℝ G₂] [CompleteSpace G₂] [NormedAddCommGroup G₃] [NormedSpace ℝ G₃]
  [CompleteSpace G₃]

omit [CompleteSpace G₂] [CompleteSpace G₃] in
/-- The pointwise Leibniz bound behind `TauCeti.eLpNormWkp_bilin_le`. -/
private theorem norm_iteratedFDeriv_bilin_le (B : G₁ →L[ℝ] G₂ →L[ℝ] G₃) {U : Set ℂ}
    (hU : IsOpen U) {k : ℕ} {a : ℂ → G₁} {f : ℂ → G₂} (ha : ContDiffOn ℝ k a U)
    (hf : ContDiffOn ℝ k f U) {c : ℝ≥0} {x : ℂ} (hx : x ∈ U)
    (hc : ∀ l ≤ k, ‖iteratedFDeriv ℝ l a x‖ ≤ c) {l : ℕ} (hl : l ≤ k) :
    ‖iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y)) x‖ ≤
      ‖B‖ * c * 2 ^ k * ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j f x‖ := by
  set S := ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j f x‖
  have hW (n : ℕ) {g : ℂ → G₁} : iteratedFDerivWithin ℝ n g U x = iteratedFDeriv ℝ n g x :=
    iteratedFDerivWithin_of_isOpen n hU hx
  have hW₂ (n : ℕ) : iteratedFDerivWithin ℝ n f U x = iteratedFDeriv ℝ n f x :=
    iteratedFDerivWithin_of_isOpen n hU hx
  have hW₃ : iteratedFDerivWithin ℝ l (fun y ↦ B (a y) (f y)) U x =
      iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y)) x :=
    iteratedFDerivWithin_of_isOpen l hU hx
  have hS (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j f x‖ ≤ S :=
    Finset.single_le_sum (f := fun j ↦ ‖iteratedFDeriv ℝ j f x‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_range.2 (by omega))
  have hB := B.norm_iteratedFDerivWithin_le_of_bilinear ha hf hU.uniqueDiffOn hx
    (n := l) (by exact_mod_cast hl)
  rw [hW₃] at hB
  refine hB.trans ?_
  simp only [hW, hW₂]
  have hsum : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ *
      ‖iteratedFDeriv ℝ (l - i) f x‖ ≤ ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * c * S := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hi : i ≤ l := Finset.mem_range_succ_iff.1 hi
    have hc0 : (0 : ℝ) ≤ c := c.coe_nonneg
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hc i (hi.trans hl)) (Nat.cast_nonneg _))
      (hS _ (by omega)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hc0)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have h2 : (2 : ℝ) ^ l ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hl
  calc ‖B‖ * ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ *
        ‖iteratedFDeriv ℝ (l - i) f x‖
      ≤ ‖B‖ * ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * c * S :=
        mul_le_mul_of_nonneg_left hsum (ContinuousLinearMap.opNorm_nonneg B)
    _ = ‖B‖ * c * 2 ^ l * S := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ ‖B‖ * c * 2 ^ k * S := by
        have : 0 ≤ ‖B‖ * (c : ℝ) := mul_nonneg (ContinuousLinearMap.opNorm_nonneg B) c.coe_nonneg
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 this) hS0

/-- A function vanishing on `U \ V`, for open `V ⊆ U`, has the same `Lᵖ` norm on `U` and on
`V`. -/
private theorem eLpNorm_restrict_eq_of_eqOn_zero {E : Type*} [NormedAddCommGroup E] {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) {g : ℂ → E} (h0 : ∀ x ∈ U \ V, g x = 0) :
    eLpNorm g p (volume.restrict U) = eLpNorm g p (volume.restrict V) := by
  have hind : g =ᵐ[volume.restrict U] V.indicator g := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem hxV]
    · rw [indicator_of_notMem hxV, h0 x ⟨hx, hxV⟩]
  rw [eLpNorm_congr_ae hind, eLpNorm_indicator_eq_eLpNorm_restrict (f := g)
    (show NullMeasurableSet V (volume.restrict U) from hV.measurableSet.nullMeasurableSet),
    Measure.restrict_restrict hV.measurableSet, inter_eq_left.2 hVU]

/-- **The Leibniz bound for the `W^{k,p}` norm.** Let `V ⊆ U` be open, let `a` and `f` be `Cᵏ` on
`U`, and let `B` be a continuous bilinear map. If the derivatives of `a` of order at most `k` are
bounded by `c` on `V`, and those of `y ↦ B (a y) (f y)` vanish on `U \ V`, then the `W^{k,p}(U)`
norm of `y ↦ B (a y) (f y)` is at most `(k + 1) 2ᵏ ‖B‖ c` times the `W^{k,p}(V)`
norm of `f`. -/
theorem eLpNormWkp_bilin_le (hp : 1 ≤ p) (B : G₁ →L[ℝ] G₂ →L[ℝ] G₃) {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) {k : ℕ} {a : ℂ → G₁} {f : ℂ → G₂}
    (ha : ContDiffOn ℝ k a U) (hf : ContDiffOn ℝ k f U) {c : ℝ≥0}
    (hc : ∀ x ∈ V, ∀ l ≤ k, ‖iteratedFDeriv ℝ l a x‖ ≤ c)
    (h0 : ∀ x ∈ U \ V, ∀ l ≤ k, iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y)) x = 0) :
    eLpNormWkp p U k (fun y ↦ B (a y) (f y)) ≤
      ((k + 1) * (‖B‖₊ * c * 2 ^ k) : ℝ≥0) * eLpNormWkp p V k f := by
  have hBaf : ContDiffOn ℝ k (fun y ↦ B (a y) (f y)) U :=
    (B.contDiff.comp_contDiffOn ha).clm_apply hf
  set M : ℝ≥0 := ‖B‖₊ * c * 2 ^ k
  set W := eLpNormWkp p V k f
  have hW : W = ∑ j ∈ Finset.range (k + 1),
      eLpNorm (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) p (volume.restrict V) := by
    rw [show W = eLpNormWkp p V k f from rfl,
      eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv hV k (hf.mono hVU)]
    exact Finset.sum_congr rfl fun j hj ↦ (eLpNorm_norm _
      (aestronglyMeasurable_iteratedFDeriv_of_contDiffOn hV (hf.mono hVU)
        (Finset.mem_range_succ_iff.1 hj))).symm
  have hl (l : ℕ) (hl : l ≤ k) :
      eLpNorm (iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y))) p (volume.restrict U) ≤ M * W := by
    -- The derivative vanishes on `U \ V`, so only `V` contributes.
    rw [eLpNorm_restrict_eq_of_eqOn_zero hU hV hVU fun x hx ↦ h0 x hx l hl]
    have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y)))
        (volume.restrict V) :=
      ((ContinuousOn.continuousOn_iteratedFDeriv hBaf hU (by exact_mod_cast hl)).mono
        hVU).aestronglyMeasurable hV.measurableSet
    calc eLpNorm (iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y))) p (volume.restrict V)
        ≤ eLpNorm (fun x ↦ (M : ℝ) *
            ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j f x‖) p (volume.restrict V) := by
          refine eLpNorm_mono_ae_real hmeas ?_
          filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
          simpa [M] using norm_iteratedFDeriv_bilin_le B hU ha hf (hVU hx) (hc x hx) hl
      _ = M * eLpNorm (fun x ↦ ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j f x‖) p
            (volume.restrict V) := by
          rw [show (fun x ↦ (M : ℝ) * ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j f x‖) =
            (M : ℝ) • fun x ↦ ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j f x‖ from rfl,
            eLpNorm_const_smul]
          simp
      _ ≤ M * W := by
          gcongr
          rw [hW]
          refine (eLpNorm_sum_le hp).trans_eq' ?_
          congr 1
          ext x
          simp
  rw [eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv hU k hBaf]
  calc ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y))) p
        (volume.restrict U)
      ≤ ∑ _l ∈ Finset.range (k + 1), (M : ℝ≥0∞) * W :=
        Finset.sum_le_sum fun l hl' ↦ hl l (by have := Finset.mem_range.1 hl'; omega)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The Leibniz bound `TauCeti.eLpNormWkp_bilin_le` with its constant, which depends only on `B`,
`k` and `c`, chosen in advance. -/
theorem exists_eLpNormWkp_bilin_le (hp : 1 ≤ p) (B : G₁ →L[ℝ] G₂ →L[ℝ] G₃) (k : ℕ) (c : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {U V : Set ℂ} {a : ℂ → G₁} {f : ℂ → G₂}, IsOpen U → IsOpen V → V ⊆ U →
      ContDiffOn ℝ k a U → ContDiffOn ℝ k f U →
      (∀ x ∈ V, ∀ l ≤ k, ‖iteratedFDeriv ℝ l a x‖ ≤ c) →
      (∀ x ∈ U \ V, ∀ l ≤ k, iteratedFDeriv ℝ l (fun y ↦ B (a y) (f y)) x = 0) →
      eLpNormWkp p U k (fun y ↦ B (a y) (f y)) ≤ C * eLpNormWkp p V k f :=
  ⟨_, fun hU hV hVU ha hf hc h0 ↦ eLpNormWkp_bilin_le hp B hU hV hVU ha hf hc h0⟩

/-- The Leibniz bound for a field of continuous linear maps applied to a function, with its
constant, which depends only on `k` and `c`, chosen in advance. -/
theorem exists_eLpNormWkp_clm_apply_le (hp : 1 ≤ p) (k : ℕ) (c : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {U V : Set ℂ} {a : ℂ → G₂ →L[ℝ] G₃} {f : ℂ → G₂}, IsOpen U → IsOpen V → V ⊆ U →
      ContDiffOn ℝ k a U → ContDiffOn ℝ k f U →
      (∀ x ∈ V, ∀ l ≤ k, ‖iteratedFDeriv ℝ l a x‖ ≤ c) →
      (∀ x ∈ U \ V, ∀ l ≤ k, iteratedFDeriv ℝ l (fun y ↦ a y (f y)) x = 0) →
      eLpNormWkp p U k (fun y ↦ a y (f y)) ≤ C * eLpNormWkp p V k f :=
  exists_eLpNormWkp_bilin_le hp (ContinuousLinearMap.id ℝ (G₂ →L[ℝ] G₃)) k c

end TauCeti
