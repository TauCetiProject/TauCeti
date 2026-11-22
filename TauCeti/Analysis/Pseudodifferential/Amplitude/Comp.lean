/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Amplitudes from symbols in moving frequency coordinates

Let `b(z, η)` be a symbol of order `m` on `ℝⁿ`, let `κ : ℝⁿ → ℝⁿ` be smooth, let
`M(x, y)` be a smooth family of linear maps of `ℝⁿ`, and let `g(x, y)` be a smooth compactly
supported weight such that `M(x, y)` is invertible on the support of `g`. Then

`c(x, y, ξ) = g(x, y) • b(κ x, M(x, y) ξ)`

is an amplitude of order `m` (`TauCeti.Symbol.compAmplitude`) with proper input support.

Amplitudes of this form arise from changes of coordinates: if `κ` is a diffeomorphism, then
`κ x - κ y = Φ(x, y) (x - y)` for the averaged derivative `Φ(x, y)` of `κ` along the segment
from `y` to `x`, so the phase `⟪κ x - κ y, η⟫` becomes `⟪x - y, ξ⟫` after the frequency
substitution `η = M(x, y) ξ` with `M = (Φ*)⁻¹`. This is Kuranishi's trick; the operator in the new
coordinates is the quantization of an amplitude of the form above.

## The estimates

A derivative of `c` in a frequency direction `v` is `g(x, y) • ∂_η b(κ x, M ξ)[M v]`, a sum of
terms of the same form with `b` replaced by its frequency derivatives `∂_{η_k} b`, of order
`m - 1`. A derivative in a position direction differentiates `g`, the position argument `κ x` of
`b`, and the frequency argument `M(x, y) ξ`. In the last term the derivative `(∂M) ξ` is linear in
`ξ`, and on the support of `g` it equals `(∂M) M⁻¹ η` with `η = M ξ`; so it is a sum of terms of
the same form with `b` replaced by `η_r ∂_{η_k} b`, again of order `m`. By induction on the number
of derivatives, every mixed derivative `∂_x^α ∂_y^γ ∂_ξ^β c` is a finite sum of terms of the same
form of order `m - |β|`, and each such term is bounded by `C ⟨ξ⟩ ^ (m - |β|)`, since `⟨M ξ⟩` and
`⟨ξ⟩` are comparable on the compact support of the weight.

## Main declarations

* `TauCeti.Symbol.compAmplitude`: the amplitude `g(x, y) • b(κ x, M(x, y) ξ)`.
* `TauCeti.Symbol.coefficient_compAmplitude`: its coefficient.
* `TauCeti.Symbol.hasProperInputSupport_compAmplitude`: it has proper input support, since it
  vanishes for input positions outside a compact set.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, proof of
  Theorem 18.1.17.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open scoped ContDiff RealInnerProductSpace Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]
  {κ : CoordinateSpace n → CoordinateSpace n}
  {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}

/-! ### The terms of the expansion -/

/-- The function `(x, y, ξ) ↦ h(x, y) • b(κ x, M(x, y) ξ)`. Every derivative of such a function is
a finite sum of functions of the same form. -/
private def term (κ : CoordinateSpace n → CoordinateSpace n)
    (M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (h : CoordinateSpace n × CoordinateSpace n → ℝ) {m : ℝ} (b : Symbol n V W m) :
    CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
  fun p ↦ h (p.1, p.2.1) • b.coefficient (κ p.1, M (p.1, p.2.1) p.2.2)

private theorem contDiff_term (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {h : CoordinateSpace n × CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h) {m : ℝ}
    (b : Symbol n V W m) : ContDiff ℝ ∞ (term κ M h b) := by
  have hw : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      (p.1, p.2.1) := by fun_prop
  exact (hh.comp hw).smul (b.contDiff_coefficient.comp
    ((hκ.comp contDiff_fst).prodMk ((hM.comp hw).clm_apply (contDiff_snd.comp contDiff_snd))))

/-- The chain rule for a term. -/
private theorem fderiv_term (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {h : CoordinateSpace n × CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h) {m : ℝ}
    (b : Symbol n V W m) (p d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (term κ M h b) p d =
      fderiv ℝ h (p.1, p.2.1) (d.1, d.2.1) • b.coefficient (κ p.1, M (p.1, p.2.1) p.2.2) +
        h (p.1, p.2.1) • fderiv ℝ b.coefficient (κ p.1, M (p.1, p.2.1) p.2.2)
          (fderiv ℝ κ p.1 d.1,
            fderiv ℝ M (p.1, p.2.1) (d.1, d.2.1) p.2.2 + M (p.1, p.2.1) d.2.2) := by
  set w : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n →
      CoordinateSpace n × CoordinateSpace n := fun p ↦ (p.1, p.2.1)
  have hw : HasFDerivAt w ((ContinuousLinearMap.fst ℝ _ _).prod
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))) p :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_fst.comp p hasFDerivAt_snd)
  have hhw := ((hh.differentiable (by simp)) (w p)).hasFDerivAt.comp p hw
  have hMw := ((hM.differentiable (by simp)) (w p)).hasFDerivAt.comp p hw
  have hκ1 := ((hκ.differentiable (by simp)) p.1).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hMξ := hMw.clm_apply ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).snd)
  have hΨ := hκ1.prodMk hMξ
  have hb := ((b.contDiff_coefficient.differentiable (by simp)) _).hasFDerivAt.comp p hΨ
  have := hhw.smul hb
  have e : term κ M h b =
      (h ∘ w) • (b.coefficient ∘ fun x ↦ ((κ ∘ Prod.fst) x, ((M ∘ w) x) x.2.2)) := rfl
  rw [e, this.fderiv]
  simp [w, add_comm]

/-- The derivative of a term in a frequency direction. -/
private theorem fderiv_term_frequency (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {h : CoordinateSpace n × CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h) {m : ℝ}
    (b : Symbol n V W m) (v : CoordinateSpace n) :
    (fun p ↦ fderiv ℝ (term κ M h b) p (0, 0, v)) =
      ∑ k, term κ M (fun w ↦ h w * M w v k) (frequencyDeriv k b) := by
  funext p
  rw [fderiv_term hκ hM hh, Finset.sum_apply]
  simp [term, fderiv_coefficient_apply, Finset.smul_sum, smul_smul, mul_comm, Prod.mk_zero_zero]

/-- The coefficient `h(w) ⟪(∂_u M)(w) M(w)⁻¹ e_r, e_k⟫` of the term `η_r ∂_{η_k} b` in a position
derivative. -/
private def coeffInv (M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ]
    CoordinateSpace n) (h : CoordinateSpace n × CoordinateSpace n → ℝ)
    (u : CoordinateSpace n × CoordinateSpace n) (k r : Fin n) :
    CoordinateSpace n × CoordinateSpace n → ℝ :=
  fun w ↦ h w * fderiv ℝ M w u (Ring.inverse (M w) (EuclideanSpace.single r 1)) k

/-- The derivative of a term in a position direction. -/
private theorem fderiv_term_position (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {h : CoordinateSpace n × CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhM : ∀ w, h w ≠ 0 → IsUnit (M w)) {m : ℝ} (b : Symbol n V W m)
    (u : CoordinateSpace n × CoordinateSpace n) :
    (fun p ↦ fderiv ℝ (term κ M h b) p (u.1, u.2, 0)) =
      term κ M (fun w ↦ fderiv ℝ h w u) b +
        ∑ k, term κ M (fun w ↦ h w * fderiv ℝ κ w.1 u.1 k) (spatialDeriv k b) +
          ∑ k, ∑ r, term κ M (coeffInv M h u k r)
            ((ofInner (EuclideanSpace.single r 1)).comp (frequencyDeriv k b)) := by
  funext p
  set w := (p.1, p.2.1)
  rw [fderiv_term hκ hM hh]
  simp only [map_zero, add_zero, Prod.mk.eta, fderiv_coefficient_apply, Pi.add_apply,
    Finset.sum_apply, term]
  rw [smul_add, ← add_assoc]
  congr 1
  · congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [smul_smul, mul_comm]
  · by_cases hw : h w = 0
    · simp only [w] at hw
      simp [coeffInv, hw]
    have hu := hhM w hw
    -- On the support of `h`, `(∂_u M) ξ = (∂_u M) M⁻¹ η` with `η = M ξ`.
    have hv : ∀ k, fderiv ℝ M w u p.2.2 k = ∑ r, M w p.2.2 r *
        fderiv ℝ M w u (Ring.inverse (M w) (EuclideanSpace.single r 1)) k := by
      intro k
      conv_lhs => rw [← ContinuousLinearMap.ringInverse_apply_apply hu p.2.2,
        ← ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_eq_sum_single]
      simp
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hv k, Finset.sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    simp only [coeffInv, coefficient_comp, coefficient_ofInner, EuclideanSpace.inner_single_right,
      smul_smul]
    ext v
    simp [w, smul_smul, ← Complex.coe_smul]
    congr 1
    ring

/-! ### Smoothness of the coefficients -/

private theorem contDiff_apply_coord {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → CoordinateSpace n} (hf : ContDiff ℝ ∞ f) (k : Fin n) :
    ContDiff ℝ ∞ fun x ↦ f x k :=
  (EuclideanSpace.proj k : CoordinateSpace n →L[ℝ] ℝ).contDiff.comp hf

/-- The coefficient of a term in a position derivative involving `M⁻¹` is smooth, since `M` is
invertible near the support of `h`. -/
private theorem contDiff_coeffInv (hM : ContDiff ℝ ∞ M)
    {h : CoordinateSpace n × CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhM : tsupport h ⊆ {w | IsUnit (M w)}) (u : CoordinateSpace n × CoordinateSpace n)
    (k r : Fin n) : ContDiff ℝ ∞ (coeffInv M h u k r) := by
  have hU : IsOpen {w | IsUnit (M w)} := Units.isOpen.preimage hM.continuous
  have hg : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ M w u
      (Ring.inverse (M w) (EuclideanSpace.single r 1)) k) {w | IsUnit (M w)} := by
    intro w hw
    have hinv : ContDiffAt ℝ ∞ (fun w ↦ Ring.inverse (M w)) w := hM.contDiffAt.inverse hw
    have hd : ContDiffAt ℝ ∞ (fun w ↦ fderiv ℝ M w u) w :=
      ((hM.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).contDiffAt
    have := hd.clm_apply (hinv.clm_apply
      (contDiffAt_const (c := (EuclideanSpace.single r 1 : CoordinateSpace n))))
    exact ((EuclideanSpace.proj k : CoordinateSpace n →L[ℝ] ℝ).contDiff.contDiffAt.comp w
      this).contDiffWithinAt
  exact ContDiffOn.contDiff_smul_of_tsupport_subset hg hU hh.contDiffOn hhM

/-! ### The estimates -/

/-- A term is bounded by `C ⟨ξ⟩ ^ m`. -/
private theorem exists_norm_term_le (hκ : Continuous κ)
    {S : Set (CoordinateSpace n × CoordinateSpace n)} (hS : IsCompact S) {c : ℝ} (hc : 1 ≤ c)
    (hcS : ∀ w ∈ S, ∀ ξ, ‖M w ξ‖ ≤ c * ‖ξ‖ ∧ ‖ξ‖ ≤ c * ‖M w ξ‖)
    {h : CoordinateSpace n × CoordinateSpace n → ℝ} (hh : Continuous h) (hhS : tsupport h ⊆ S)
    {m : ℝ} (b : Symbol n V W m) :
    ∃ C, 0 ≤ C ∧ ∀ p, ‖term κ M h b p‖ ≤ C * (1 + ‖p.2.2‖ ^ 2) ^ (m / 2) := by
  obtain ⟨H, hH⟩ := hh.bounded_above_of_compact_support
    (hS.of_isClosed_subset (isClosed_tsupport h) hhS)
  obtain ⟨B, hB0, hB⟩ := b.exists_bound_coefficient (κ '' (Prod.fst '' S))
    ((hS.image continuous_fst).image hκ)
  refine ⟨max H 0 * B * c ^ |m|, by positivity, fun p ↦ ?_⟩
  by_cases hw : (p.1, p.2.1) ∈ S
  · have hz : κ p.1 ∈ κ '' (Prod.fst '' S) := ⟨p.1, ⟨_, hw, rfl⟩, rfl⟩
    calc ‖term κ M h b p‖
        = ‖h (p.1, p.2.1)‖ * ‖b.coefficient (κ p.1, M (p.1, p.2.1) p.2.2)‖ := norm_smul _ _
      _ ≤ max H 0 * (B * (1 + ‖M (p.1, p.2.1) p.2.2‖ ^ 2) ^ (m / 2)) :=
        mul_le_mul ((hH _).trans (le_max_left _ _)) (hB _ hz _) (norm_nonneg _) (by positivity)
      _ ≤ max H 0 * (B * (c ^ |m| * (1 + ‖p.2.2‖ ^ 2) ^ (m / 2))) := by
        gcongr
        exact one_add_norm_sq_rpow_le_of_norm_le_mul hc m (hcS _ hw _).1 (hcS _ hw _).2
      _ = max H 0 * B * c ^ |m| * (1 + ‖p.2.2‖ ^ 2) ^ (m / 2) := by ring
  · have : h (p.1, p.2.1) = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hw (hhS h')
    simp only [term, this, zero_smul, norm_zero]
    positivity

private theorem norm_sum_le_sum_mul {ι : Type*} (s : Finset ι) {A : Type*} [NormedAddCommGroup A]
    (f : ι → A) (C : ι → ℝ) {w : ℝ} (h : ∀ i ∈ s, ‖f i‖ ≤ C i * w) :
    ‖∑ i ∈ s, f i‖ ≤ (∑ i ∈ s, C i) * w := by
  rw [Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum h)

/-- **Estimates for the terms.** Every mixed derivative `∂_x^α ∂_y^γ ∂_ξ^β` of a term
`h(x, y) • b(κ x, M(x, y) ξ)` with `b` of order `m` is bounded by `C ⟨ξ⟩ ^ (m - |β|)`. -/
private theorem exists_norm_iteratedFDerivAlong_term_le (hκ : ContDiff ℝ ∞ κ)
    (hM : ContDiff ℝ ∞ M) {S : Set (CoordinateSpace n × CoordinateSpace n)} (hS : IsCompact S)
    (hSM : ∀ w ∈ S, IsUnit (M w)) (D : ℕ) :
    ∀ {m : ℝ} (b : Symbol n V W m) {h : CoordinateSpace n × CoordinateSpace n → ℝ},
      ContDiff ℝ ∞ h → tsupport h ⊆ S → ∀ α γ β : List (Fin n),
        α.length + γ.length + β.length = D → ∃ C, ∀ p,
          ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β) (term κ M h b) p‖ ≤
            C * (1 + ‖p.2.2‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨c, hc, hcS⟩ :=
    exists_norm_clm_apply_le_and_norm_le_of_isUnit hS hM.continuous.continuousOn hSM
  have hhU : ∀ {h : CoordinateSpace n × CoordinateSpace n → ℝ}, tsupport h ⊆ S →
      tsupport h ⊆ {w | IsUnit (M w)} := fun hhS w hw ↦ hSM w (hhS hw)
  have hne : ∀ {h : CoordinateSpace n × CoordinateSpace n → ℝ}, tsupport h ⊆ S →
      ∀ w, h w ≠ 0 → IsUnit (M w) := fun hhS w hw ↦ hSM w (hhS (subset_tsupport _ hw))
  induction D with
  | zero =>
    intro m b h hh hhS α γ β hD
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (α = [] ∧ γ = []) ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, -, hC⟩ := exists_norm_term_le hκ.continuous hS hc hcS hh.continuous hhS b
    exact ⟨C, fun p ↦ by simpa [amplitudeDirections_def] using hC p⟩
  | succ D ih =>
    intro m b h hh hhS α γ β hD
    -- The position step, used for the directions `(u, 0)` with `u = (e_j, 0)` or `(0, e_j)`.
    have hpos : ∀ (l : List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n))
        (u : CoordinateSpace n × CoordinateSpace n),
        (∀ {m' : ℝ} (b' : Symbol n V W m') {h' : CoordinateSpace n × CoordinateSpace n → ℝ},
          ContDiff ℝ ∞ h' → tsupport h' ⊆ S → ∃ C, ∀ p,
            ‖iteratedFDerivAlong ℝ l (term κ M h' b') p‖ ≤
              C * (1 + ‖p.2.2‖ ^ 2) ^ ((m' - β.length) / 2)) →
        ∃ C, ∀ p, ‖iteratedFDerivAlong ℝ (l ++ [(u.1, u.2, 0)]) (term κ M h b) p‖ ≤
          C * (1 + ‖p.2.2‖ ^ 2) ^ ((m - β.length) / 2) := by
      intro l u hl
      -- The weights of the three kinds of terms, and their smoothness.
      have hhA : ContDiff ℝ ∞ fun w ↦ fderiv ℝ h w u :=
        (hh.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have hhB : ∀ k, ContDiff ℝ ∞ fun w : CoordinateSpace n × CoordinateSpace n ↦
          h w * fderiv ℝ κ w.1 u.1 k := fun k ↦
        hh.mul (contDiff_apply_coord (((hκ.fderiv_right (m := ∞) (by simp)).comp
          contDiff_fst).clm_apply contDiff_const) k)
      have hhD : ∀ k r, ContDiff ℝ ∞ (coeffInv M h u k r) :=
        contDiff_coeffInv hM hh (hhU hhS) u
      obtain ⟨CA, hCA⟩ := hl b hhA ((tsupport_fderiv_apply_subset ℝ u).trans hhS)
      choose CB hCB using fun k ↦ hl (spatialDeriv k b) (hhB k)
        ((tsupport_mul_subset_left).trans hhS)
      choose CD hCD using fun k r ↦
        hl ((ofInner (EuclideanSpace.single r 1)).comp (frequencyDeriv k b)) (hhD k r)
          ((tsupport_mul_subset_left).trans hhS)
      refine ⟨CA + ∑ k, CB k + ∑ k, ∑ r, CD k r, fun p ↦ ?_⟩
      have hA := contDiff_term hκ hM hhA b
      have hBk := fun k ↦ contDiff_term hκ hM (hhB k) (spatialDeriv k b)
      have hDkr := fun k r ↦ contDiff_term hκ hM (hhD k r)
        ((ofInner (EuclideanSpace.single r 1)).comp (frequencyDeriv k b))
      have hDk : ∀ k, ContDiff ℝ ∞ (∑ r, term κ M (coeffInv M h u k r)
          ((ofInner (EuclideanSpace.single r 1)).comp (frequencyDeriv k b))) := fun k ↦ by
        simpa only [Finset.sum_fn] using ContDiff.sum fun r _ ↦ hDkr k r
      have hB : ContDiff ℝ ∞
          (∑ k, term κ M (fun w ↦ h w * fderiv ℝ κ w.1 u.1 k) (spatialDeriv k b)) := by
        simpa only [Finset.sum_fn] using ContDiff.sum fun k _ ↦ hBk k
      have hD : ContDiff ℝ ∞ (∑ k, ∑ r, term κ M (coeffInv M h u k r)
          ((ofInner (EuclideanSpace.single r 1)).comp (frequencyDeriv k b))) := by
        simpa only [Finset.sum_fn] using ContDiff.sum fun k _ ↦ hDk k
      have hAB : ContDiff ℝ ∞ (term κ M (fun w ↦ fderiv ℝ h w u) b +
          ∑ k, term κ M (fun w ↦ h w * fderiv ℝ κ w.1 u.1 k) (spatialDeriv k b)) := hA.add hB
      rw [iteratedFDerivAlong_append_singleton, fderiv_term_position hκ hM hh (hne hhS),
        iteratedFDerivAlong_add hAB hD _ (by simp),
        iteratedFDerivAlong_add hA hB _ (by simp),
        iteratedFDerivAlong_sum _ (fun k _ ↦ hBk k) _ (by simp),
        iteratedFDerivAlong_sum _ (fun k _ ↦ hDk k) _ (by simp)]
      simp only [Pi.add_apply, Finset.sum_apply]
      rw [add_mul, add_mul]
      refine (norm_add₃_le).trans (add_le_add_three (hCA p) ?_ ?_)
      · exact norm_sum_le_sum_mul _ _ _ fun k _ ↦ hCB k p
      · rw [Finset.sum_mul]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
        rw [iteratedFDerivAlong_sum _ (fun r _ ↦ hDkr k r) _ (by simp)]
        simp only [Finset.sum_apply]
        refine norm_sum_le_sum_mul _ _ _ fun r _ ↦ ?_
        have := hCD k r p
        rwa [show (1 + (m - 1) - (β.length : ℝ)) / 2 = (m - β.length) / 2 by ring] at this
    rcases List.eq_nil_or_concat' β with rfl | ⟨β, j, rfl⟩
    · rcases List.eq_nil_or_concat' γ with rfl | ⟨γ, j, rfl⟩
      · rcases List.eq_nil_or_concat' α with rfl | ⟨α, j, rfl⟩
        · simp at hD
        · rw [amplitudeDirections_append_singleton_left]
          exact hpos _ (EuclideanSpace.single j 1, 0) fun b' h' hh' hh'S ↦
            ih b' hh' hh'S α [] [] (by simp at hD ⊢; omega)
      · rw [amplitudeDirections_append_singleton_mid]
        exact hpos _ (0, EuclideanSpace.single j 1) fun b' h' hh' hh'S ↦
          ih b' hh' hh'S α γ [] (by simp at hD ⊢; omega)
    · -- The frequency step.
      have hhM : ∀ k, ContDiff ℝ ∞ fun w ↦ h w * M w (EuclideanSpace.single j 1) k := fun k ↦
        hh.mul (contDiff_apply_coord (hM.clm_apply contDiff_const) k)
      choose C hC using fun k ↦ ih (frequencyDeriv k b) (hhM k)
        ((tsupport_mul_subset_left).trans hhS) α γ β (by simp at hD ⊢; omega)
      refine ⟨∑ k, C k, fun p ↦ ?_⟩
      rw [amplitudeDirections_append_singleton_right, iteratedFDerivAlong_append_singleton,
        fderiv_term_frequency hκ hM hh,
        iteratedFDerivAlong_sum _ (fun k _ ↦ contDiff_term hκ hM (hhM k) (frequencyDeriv k b)) _
          (by simp)]
      simp only [Finset.sum_apply]
      refine norm_sum_le_sum_mul _ _ _ fun k _ ↦ ?_
      have := hC k p
      rwa [order_sub_one_sub_length] at this

/-! ### The amplitude -/

/-- The **amplitude `g(x, y) • b(κ x, M(x, y) ξ)`** of a symbol `b` of order `m`, for a smooth map
`κ`, a smooth family `M(x, y)` of linear maps of `ℝⁿ`, and a smooth compactly supported weight `g`
such that `M(x, y)` is invertible on the support of `g`. It is an amplitude of order `m` with
proper input support (`TauCeti.Symbol.hasProperInputSupport_compAmplitude`). -/
def compAmplitude {m : ℝ} (b : Symbol n V W m) (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {g : CoordinateSpace n × CoordinateSpace n → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) : Amplitude n V W m where
  coefficient := term κ M g b
  contDiff_coefficient := contDiff_term hκ hM hg b
  exists_bound _ _ α γ β := by
    obtain ⟨C, hC⟩ := exists_norm_iteratedFDerivAlong_term_le hκ hM hgc hgM _ b hg subset_rfl
      α γ β rfl
    exact ⟨max C 0, le_max_right _ _, fun x y _ ξ ↦ (hC (x, y, ξ)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩

@[simp]
theorem coefficient_compAmplitude {m : ℝ} (b : Symbol n V W m) (hκ : ContDiff ℝ ∞ κ)
    (hM : ContDiff ℝ ∞ M) {g : CoordinateSpace n × CoordinateSpace n → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w))
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (b.compAmplitude hκ hM hg hgc hgM).coefficient p =
      g (p.1, p.2.1) • b.coefficient (κ p.1, M (p.1, p.2.1) p.2.2) := (rfl)

/-- The amplitude `g(x, y) • b(κ x, M(x, y) ξ)` vanishes for input positions `y` outside the
projection of the compact support of `g`, so it has proper input support. -/
theorem hasProperInputSupport_compAmplitude {m : ℝ} (b : Symbol n V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) {g : CoordinateSpace n × CoordinateSpace n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) :
    (b.compAmplitude hκ hM hg hgc hgM).HasProperInputSupport := by
  refine Amplitude.hasProperInputSupport_iff.2 fun _ _ ↦
    ⟨Prod.snd '' tsupport g, hgc.image continuous_snd, fun x _ y hy ξ ↦ ?_⟩
  have : g (x, y) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hy ⟨_, h, rfl⟩
  simp [this]

end Symbol

end TauCeti
