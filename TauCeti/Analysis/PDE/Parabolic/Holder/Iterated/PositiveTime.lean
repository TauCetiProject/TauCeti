/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Restriction
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Solvability
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.SpaceIndependent
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.PDE.Parabolic.Holder.PositiveTime

/-!
# Parabolic Schauder estimates at positive times, at every order

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have scalar coefficients in the parabolic Hölder space `C_{par,b}^{k+α}`, `0 < α < 1`, with `a`
uniformly elliptic. The global Schauder estimate of order `k`
(`TauCeti.ParabolicCkHolderSpace.exists_norm_le_parabolicOperatorL`) bounds the norm of `u` in
`C_{par,b}^{k+2+α}` by `‖P u‖_{k+α}` and the `C^{k+2,α}` norm of the initial values `u(·, 0)`.
Away from the initial time no regularity of the initial values is needed: for every `δ > 0`
there is a constant `C` such that

`‖u‖_{k+2+α;[δ,T]} ≤ C (‖P u‖_{k+α} + sup |u(·, 0)|)`

for every `u ∈ C_{par,b}^{k+2+α}` on `ℝⁿ × [0, T]` with `δ < T`
(`TauCeti.ParabolicCkHolderSpace.exists_norm_restrictL_le_parabolicOperatorL`). Here
`‖u‖_{k+2+α;[δ,T]}` is the norm of the restriction of `u` to `ℝⁿ × [δ, T]`, and `C` depends only
on `n`, `k`, `α`, `δ`, the ellipticity constant, a bound on the norms of the coefficients and a
bound on the horizon. This is the form in which the Schauder theory of every order applies to
solutions with merely bounded initial values: the constant is uniform in `u`, and only the
supremum of the initial values enters. At order `k = 0` the sharp dependence
`δ^(1 + α/2)` of the constant on `δ` is
`TauCeti.ParabolicC2HolderSpace.exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL`;
at higher orders the constant is not tracked in `δ`.

## The argument

Fix a smooth step `ψ` and the time cutoffs `θ_s(t) = ψ(t / s - 1)`, vanishing up to time `s` and
equal to one from time `2 s` on. By induction on `k` we bound `‖θ_s u‖_{k+2+α}`, on the whole slab,
by `C (‖P u‖_{k+α} + sup |u(·, 0)|)`. The product `θ_s u` vanishes at the initial time, and

`P (θ_s u) = θ_s P u + θ_s' u`

(`ParabolicCkHolderSpace.parabolicOperatorL_compParabolicCkHolder₂_lsmul_compSlabTime_apply`),
so the global Schauder estimate bounds `‖θ_s u‖_{k+2+α}` by `‖θ_s P u‖_{k+α} + ‖θ_s' u‖_{k+α}`.

* **Order zero.** The derivative `θ_s'` vanishes before time `s`, so the Hölder norm of
  `θ_s' u` is bounded by the Hölder norm of `u` on `ℝⁿ × [s, T]` together with the supremum of
  `|u|` on the whole slab (`ContinuousLinearMap.norm_compHolder₂_valueHolderL_le_of_eq_zero`).
  The positive-time estimate of order two bounds the first, and the comparison principle the
  second, both by `‖P u‖` and `sup |u(·, 0)|`.
* **From `k` to `k + 1`.** Since `θ_{s/2} = 1` wherever `θ_s' ≠ 0`, the product `θ_s' u` equals
  `θ_s' (θ_{s/2} u)`, whose norm of order `k + 1` is at most a multiple of the norm of order
  `k + 2` of `θ_{s/2} u`, bounded by the induction hypothesis applied to `u` read at order
  `k + 2` with the coefficients read at order `k`.

Finally `u = θ_{δ/2} u` on `ℝⁿ × [δ, T]`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.exists_norm_restrictL_le_parabolicOperatorL`: the Schauder
  estimate of order `k` at positive times.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 3
  (Schauder estimates away from the initial time).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4
  (time localization for parabolic estimates).
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime Real
open scoped NNReal

/-! ### Time cutoffs -/

/-- The time cutoff at scale `s`: `t ↦ ψ (t / s - 1)` for the smooth step `ψ`, zero up to time
`s` and one from time `2 s` on. -/
private def cutoff (s t : ℝ) : ℝ :=
  smoothTransition (t / s - 1)

private theorem contDiff_cutoff (s : ℝ) {n : ℕ} : ContDiff ℝ n (cutoff s) :=
  smoothTransition.contDiff.comp ((contDiff_id.div_const s).sub contDiff_const)

private theorem contDiff_deriv_cutoff (s : ℝ) {n : ℕ} : ContDiff ℝ n (deriv (cutoff s)) :=
  (contDiff_succ_iff_deriv.1 (contDiff_cutoff s (n := n + 1))).2.2

private theorem cutoff_of_le {s t : ℝ} (hs : 0 < s) (ht : t ≤ s) : cutoff s t = 0 :=
  smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one hs]; exact ht)

private theorem cutoff_of_two_mul_le {s t : ℝ} (hs : 0 < s) (ht : 2 * s ≤ t) : cutoff s t = 1 :=
  smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ hs]; linarith)

/-- The cutoff is constant before time `s`, so its derivative vanishes there. -/
private theorem deriv_cutoff_of_lt {s t : ℝ} (hs : 0 < s) (ht : t < s) : deriv (cutoff s) t = 0 :=
  (Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ))
    (Filter.eventually_of_mem (Iio_mem_nhds ht) fun _ hτ ↦ cutoff_of_le hs (le_of_lt hτ))).trans
    (deriv_const _ _)

/-- The derivative of the cutoff at scale `s` is supported where the cutoff at scale `s / 2` is
one. -/
private theorem deriv_cutoff_mul_cutoff_half {s : ℝ} (hs : 0 < s) (t : ℝ) :
    deriv (cutoff s) t * cutoff (s / 2) t = deriv (cutoff s) t := by
  rcases lt_or_ge t s with ht | ht
  · rw [deriv_cutoff_of_lt hs ht, zero_mul]
  · rw [cutoff_of_two_mul_le (half_pos hs) (by linarith), mul_one]

/-! ### The estimate -/

section General

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product estimate for a scalar factor `g`: `‖g v‖ ≤ 21 (k + 1)² 2ᵏ ‖g‖ ‖v‖`. -/
private theorem norm_lsmul_le {k : ℕ} {a b : ℝ} {hab : a < b} (hα : α ≤ 1)
    (g v : ParabolicCkHolderSpace k α E ℝ hab) :
    ‖(ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα g v‖ ≤
      21 * (k + 1) ^ 2 * 2 ^ k * (‖g‖ * ‖v‖) := by
  refine (ContinuousLinearMap.norm_compParabolicCkHolder₂_apply_le _ hα g v).trans ?_
  have h₁ : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  have := mul_nonneg (norm_nonneg g) (norm_nonneg v)
  calc _ = 21 * (k + 1) ^ 2 * 2 ^ k * ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ *
        (‖g‖ * ‖v‖) := by ring
    _ ≤ 21 * (k + 1) ^ 2 * 2 ^ k * 1 * (‖g‖ * ‖v‖) := by gcongr
    _ = _ := by ring

/-- **The term `θ_s' u` at order zero.** For `u ∈ C_{par,b}^{2+α}` on `E × [0, T]` and `s < T`,
the norm in `C_{par,b}^{0+α}` of `θ_s' u` involves `u` only through its norm of order two on
`E × [s, T]` and its supremum, since `θ_s'` vanishes before time `s`. -/
private theorem norm_lsmul_compSlabTime_deriv_cutoff_le (hα : α ≤ 1) {T : ℝ} {hT : 0 < T} {s : ℝ}
    (hs : 0 < s) (hsT : s < T) (u : ParabolicCkHolderSpace 2 α E ℝ hT) :
    ‖(ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα
        (compSlabTime (k := 0) hα (contDiff_deriv_cutoff s))
        (inclusionOfLEL hα (Nat.zero_le 2) u)‖ ≤
      2 * ‖(compSlabTime (k := 0) (E := E) (hab := hT) hα (contDiff_deriv_cutoff s))‖ *
        (24 * ‖ParabolicC2HolderSpace.restrictL hs.le le_rfl hsT
            (equivParabolicC2HolderSpace u)‖ +
          ‖ParabolicC2HolderSpace.valueL (equivParabolicC2HolderSpace u)‖) := by
  set g := compSlabTime (k := 0) (E := E) (hab := hT) hα (contDiff_deriv_cutoff s)
  set v := equivParabolicC2HolderSpace u
  -- At order zero the product is the bounded Hölder product of `g` with the value of `u`.
  have hprod : equivHolderSpace ((ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα g
      (inclusionOfLEL hα (Nat.zero_le 2) u)) = (ContinuousLinearMap.lsmul ℝ ℝ).compHolder₂
        (equivHolderSpace g) (ParabolicC2HolderSpace.valueHolderL hα v) :=
    HolderSpace.ext fun p ↦ by
      simp [v, equivHolderSpace_apply, ContinuousLinearMap.compHolder₂_apply,
        ParabolicC2HolderSpace.valueHolderL_apply]
  have hg : ∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time < s →
      equivHolderSpace g p = 0 := fun p hp ↦ by
    rw [equivHolderSpace_apply, compSlabTime_apply, deriv_cutoff_of_lt hs hp]
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  have hg₁ : ‖(equivHolderSpace g).toBoundedContinuousFunction‖ ≤ ‖g‖ :=
    (HolderSpace.norm_toBoundedContinuousFunction_le _).trans (norm_equivHolderSpace_le g)
  have hg₂ : (nnHolderNorm α (equivHolderSpace g : slab (E := E) 0 T → ℝ) : ℝ) ≤ ‖g‖ := by
    have h := (equivHolderSpace g).nnHolderNorm_le
    rw [HolderSpace.coe_toBoundedContinuousFunction] at h
    exact h.trans (norm_equivHolderSpace_le g)
  have hloc := (ContinuousLinearMap.lsmul ℝ ℝ).norm_compHolder₂_valueHolderL_le_of_eq_zero hα
    hs.le hsT hg v
  have hR := ParabolicC2HolderSpace.norm_valueHolderL_le_mul hα
    (ParabolicC2HolderSpace.restrictL hs.le le_rfl hsT v)
  refine (norm_le_two_mul_norm_equivHolderSpace _).trans ?_
  rw [hprod]
  refine (mul_le_mul_of_nonneg_left hloc two_pos.le).trans ?_
  calc _ ≤ 2 * (1 * (‖g‖ * (24 * ‖ParabolicC2HolderSpace.restrictL hs.le le_rfl hsT v‖) +
        ‖g‖ * ‖ParabolicC2HolderSpace.valueL v‖)) := by gcongr
    _ = _ := by ring

end General

section Euclidean

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] {lam : ℝ}

-- Reuse the operator module's Hessian shortcuts for instance search in coefficient types.
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-- The localization `θ_s u` of `u ∈ C_{par,b}^{k+2+α}(ℝⁿ × [0, T])` by the time cutoff at scale
`s`. -/
private abbrev localize (hα : α ≤ 1) (k : ℕ) {T : ℝ} {hT : 0 < T} (s : ℝ)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT :=
  (ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα (compSlabTime hα (contDiff_cutoff s)) u

private theorem localize_apply (hα : α ≤ 1) (k : ℕ) {T : ℝ} {hT : 0 < T} (s : ℝ)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    localize hα k s u p = cutoff s (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time * u p := by
  simp [localize]

/-- The localization vanishes at the initial time. -/
private theorem spatialTrace_localize (hα : α ≤ 1) (k : ℕ) {T : ℝ} {hT : 0 < T} {s : ℝ}
    (hs : 0 < s) (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) :
    (localize hα k s u).spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 :=
  CkHolderSpace.ext fun x ↦ by
    rw [spatialTrace_apply, localize_apply, time_slabMk, cutoff_of_le hs hs.le, zero_mul]
    simp

variable [DecidableEq ι]

/-- **The localized equation.** `P (θ_s u) = θ_s P u + θ_s' w` for every `w` read at order `k`
that agrees with `u` where `θ_s' ≠ 0`. -/
private theorem parabolicOperatorL_localize (hα : α ≤ 1) (k : ℕ) {T : ℝ} {hT : 0 < T} (s : ℝ)
    (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT)
    (w : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
    (hw : ∀ p : slab (E := EuclideanSpace ℝ ι) 0 T,
      deriv (cutoff s) (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time * w p =
        deriv (cutoff s) (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).time * u p) :
    parabolicOperatorL hα (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
        (euclideanZerothOrderCoeff c) (localize hα k s u) =
      (ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα
          (compSlabTime hα (contDiff_cutoff s)) (parabolicOperatorL hα (euclideanSecondOrderCoeff a)
            (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u) +
        (ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα
          (compSlabTime hα (contDiff_deriv_cutoff s)) w :=
  ext fun p ↦ by
    rw [localize, parabolicOperatorL_compParabolicCkHolder₂_lsmul_compSlabTime_apply]
    simp [hw]

/-- The statement proved by induction on `k`: the localization at every scale `s` is bounded on
the whole slab by `‖P u‖` and the initial values. -/
private def LocalizedBound (hα₁ : α < 1) (lam : ℝ) (k : ℕ) : Prop :=
  ∀ (K T₀ : ℝ≥0) {s : ℝ}, 0 < s → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ → s < T →
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
          (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) →
          ‖localize hα₁.le k s u‖ ≤ C * (‖parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a)
            (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u‖ + M)

/-- **The term `θ_s' u` at order zero, bounded by the data.** For a solution of order two, the
positive-time estimate of order two and the comparison principle bound `‖θ_s' u‖_{0+α}` by
`‖P u‖_{0+α}` and the initial values. -/
private theorem exists_norm_lsmul_compSlabTime_deriv_cutoff_le (hα₀ : 0 < α) (hα₁ : α < 1)
    (hlam : 0 < lam) (K T₀ : ℝ≥0) {s : ℝ} (hs : 0 < s) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ → s < T →
      ∀ (a : ι → ι → ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace 0 α (EuclideanSpace ℝ ι) ℝ hT),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicCkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
          (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) →
          ‖(ContinuousLinearMap.lsmul ℝ ℝ).compParabolicCkHolder₂ hα₁.le
              (compSlabTime hα₁.le (contDiff_deriv_cutoff s))
              (inclusionOfLEL hα₁.le (Nat.zero_le 2) u)‖
            ≤ C * (‖parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a)
              (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u‖ + M) := by
  obtain ⟨C₁, hC₁, hest⟩ :=
    ParabolicC2HolderSpace.exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL (ι := ι)
      hα₀ hα₁ (Lam := ∑ _i : ι, ∑ _j : ι, (K : ℝ)) hlam K T₀
  obtain ⟨Cθ', hCθ'₀, hCθ'⟩ := exists_norm_compSlabTime_le (k := 0) (E := EuclideanSpace ℝ ι) hα₁.le
    (contDiff_deriv_cutoff s) 0 T₀
  set E₀ : ℝ := Real.exp (K * T₀) * (1 + T₀)
  set W : ℝ := s ^ (-(1 + (α : ℝ) / 2))
  refine ⟨2 * Cθ' * (24 * W * C₁ + E₀), by positivity,
    fun T hT hTT₀ hsT a b c ha hak hbk hck u M hM ↦ ?_⟩
  -- The problem read in the order-two space, with coefficients in `C_b^{α,α/2}`.
  set P := parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
    (euclideanZerothOrderCoeff c) u
  set v := equivParabolicC2HolderSpace u
  set a' := fun i j ↦ (equivHolderSpace (a i j) :)
  set b' := fun i ↦ (equivHolderSpace (b i) :)
  set c' := (equivHolderSpace c :)
  set P₂ := ParabolicC2HolderSpace.euclideanParabolicOperatorL hα₁.le a' b' c' v
  have hPeq : P₂ = equivHolderSpace P :=
    (equivHolderSpace_euclideanParabolicOperatorL hα₁.le a b c u).symm
  have hP : ‖P₂‖ ≤ ‖P‖ := by rw [hPeq]; exact norm_equivHolderSpace_le _
  have ha' : ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a' i j p).toQuadraticForm' ξ := by
    simpa [a', equivHolderSpace_apply] using ha
  have hak' : ∀ i j, ‖a' i j‖ ≤ K := fun i j ↦ (norm_equivHolderSpace_le _).trans (hak i j)
  have hck' : ‖c'‖ ≤ K := (norm_equivHolderSpace_le _).trans hck
  have hM' : ∀ x, |v (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M := fun x ↦ by
    simpa [v, equivParabolicC2HolderSpace_apply] using hM x
  -- The positive-time estimate of order two, with the upper ellipticity bound from `K`.
  have hR := hest T hT hTT₀ a' b' c' ha' (fun p ξ ↦ Matrix.toQuadraticForm'_le_of_forall_abs_le
      (fun i j ↦ by simpa only [Matrix.of_apply, Real.norm_eq_abs] using
        (HolderSpace.norm_apply_le (a' i j) p).trans (hak' i j)) ξ) hak'
    (fun i ↦ (norm_equivHolderSpace_le _).trans (hbk i)) hck' v hM' hs hsT
  have h₂ := norm_lsmul_compSlabTime_deriv_cutoff_le hα₁.le hs hsT u
  -- Name the restriction, so that unification does not unfold the order-two norm.
  obtain ⟨r, hr⟩ : ∃ r, ParabolicC2HolderSpace.restrictL hs.le le_rfl hsT v = r := ⟨_, rfl⟩
  rw [hr] at hR h₂
  have hr' : ‖r‖ ≤ W * (C₁ * (‖P‖ + M)) := by
    have hW : W * s ^ (1 + (α : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
    calc ‖r‖ = W * (s ^ (1 + (α : ℝ) / 2) * ‖r‖) := by rw [← mul_assoc, hW, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hR.trans (by gcongr)) (by positivity)
  -- The comparison principle bounds the supremum.
  have hV := ParabolicC2HolderSpace.norm_valueL_le_euclideanParabolicOperatorL_add_of_abs_le
    hα₁.le hTT₀ (b := b') (fun p ξ ↦ (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (ha' p ξ)) hck' v
    hM'
  have hθ' := hCθ' hT le_rfl (by exact_mod_cast hTT₀)
  have hv' : ‖ParabolicC2HolderSpace.valueL v‖ ≤ E₀ * (‖P‖ + M) := hV.trans (by gcongr)
  calc _ ≤ 2 * Cθ' * (24 * (W * (C₁ * (‖P‖ + M))) + E₀ * (‖P‖ + M)) := h₂.trans (by gcongr)
    _ = _ := by ring

/-- **Order zero.** The localization of a solution of order two is bounded by the global Schauder
estimate of order zero, with the term `θ_s' u` bounded by
`exists_norm_lsmul_compSlabTime_deriv_cutoff_le`. -/
private theorem localizedBound_zero (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam) :
    LocalizedBound (ι := ι) hα₁ lam 0 := by
  intro K T₀ s hs
  obtain ⟨C_S, hC_S, hS⟩ := exists_norm_le_parabolicOperatorL (ι := ι) hα₀ hα₁ hlam 0 K T₀
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_norm_lsmul_compSlabTime_deriv_cutoff_le (ι := ι) hα₀ hα₁ hlam K T₀ hs
  obtain ⟨Cθ, hCθ₀, hCθ⟩ := exists_norm_compSlabTime_le (k := 0) (E := EuclideanSpace ℝ ι) hα₁.le
    (contDiff_cutoff s) 0 T₀
  refine ⟨C_S * (21 * Cθ + C₂), by positivity,
    fun T hT hTT₀ hsT a b c ha hak hbk hck u M hM ↦ ?_⟩
  set P := parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
    (euclideanZerothOrderCoeff c) u
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hw := parabolicOperatorL_localize hα₁.le 0 s a b c u
    (inclusionOfLEL hα₁.le (Nat.zero_le 2) u) fun p ↦ by rw [inclusionOfLEL_apply]
  set θ := compSlabTime (k := 0) (E := EuclideanSpace ℝ ι) (hab := hT) hα₁.le (contDiff_cutoff s)
  have h₁ := norm_lsmul_le hα₁.le θ P
  have hθ : ‖θ‖ ≤ Cθ := hCθ hT le_rfl (by exact_mod_cast hTT₀)
  refine (hS T hT hTT₀ a b c ha hak hbk hck (localize hα₁.le 0 s u)).trans ?_
  rw [spatialTrace_localize hα₁.le 0 hs, norm_zero, add_zero, hw, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hC_S
  calc _ ≤ 21 * (‖θ‖ * ‖P‖) + C₂ * (‖P‖ + M) :=
        add_le_add (h₁.trans_eq (by norm_num)) (h₂ T hT hTT₀ hsT a b c ha hak hbk hck u hM)
    _ ≤ 21 * (Cθ * (‖P‖ + M)) + C₂ * (‖P‖ + M) := by gcongr; linarith
    _ = _ := by ring

/-- **The induction hypothesis read one order lower.** If the localized bound holds at order `k`,
then for `u` of order `k + 3` and coefficients of order `k + 1`, the localization at scale `s / 2`
of `u` read at order `k + 2` is bounded by the data of order `k + 1`. -/
private theorem exists_norm_localize_inclusionOfLEL_le (hα₁ : α < 1) {k : ℕ}
    (ih : LocalizedBound (ι := ι) hα₁ lam k) (K T₀ : ℝ≥0) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ → s < T →
      ∀ (a : ι → ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicCkHolderSpace (k + 1 + 2) α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
          (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) →
          ‖localize hα₁.le k (s / 2) (inclusionOfLEL hα₁.le (Nat.add_le_add_right
              (Nat.le_succ k) 2) u)‖ ≤
            C * (‖parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a)
              (euclideanFirstOrderCoeff b) (euclideanZerothOrderCoeff c) u‖ + M) := by
  -- Name the constant `8 (k + 1)²`, so that the inclusion bound can be rewritten into it after
  -- `push_cast` and the arithmetic below treats it as one atom.
  obtain ⟨N, hN⟩ : ∃ c : ℝ, c = 8 * ((k : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
  have hN₀ : 0 ≤ N := hN ▸ by positivity
  obtain ⟨C_I, hC_I, hI⟩ := ih ⟨N * K, by positivity⟩ T₀ (half_pos hs)
  refine ⟨C_I * (N + 1), by positivity, fun T hT hTT₀ hsT a b c ha hak hbk hck u M hM ↦ ?_⟩
  have hkk : k ≤ k + 1 := Nat.le_succ k
  -- Reading the coefficients one order lower multiplies their norms by at most `N`.
  have hNK : ∀ f : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ‖f‖ ≤ K →
      ‖inclusionOfLEL hα₁.le hkk f‖ ≤ ((⟨N * K, by positivity⟩ : ℝ≥0) : ℝ) := fun f hf ↦
    (norm_inclusionOfLEL_succ_apply_le hα₁.le f).trans (by
      push_cast
      rw [← hN]
      exact mul_le_mul_of_nonneg_left hf hN₀)
  have hv := hI T hT hTT₀ (by linarith) (fun i j ↦ inclusionOfLEL hα₁.le hkk (a i j))
    (fun i ↦ inclusionOfLEL hα₁.le hkk (b i)) (inclusionOfLEL hα₁.le hkk c)
    (by simpa [inclusionOfLEL_apply] using ha) (fun i j ↦ hNK _ (hak i j))
    (fun i ↦ hNK _ (hbk i)) (hNK _ hck) (inclusionOfLEL hα₁.le (Nat.add_le_add_right hkk 2) u)
    (M := M) (by simpa [inclusionOfLEL_apply] using hM)
  rw [← inclusionOfLEL_euclideanSecondOrderCoeff, ← inclusionOfLEL_euclideanFirstOrderCoeff,
    ← inclusionOfLEL_euclideanZerothOrderCoeff, ← inclusionOfLEL_parabolicOperatorL] at hv
  set P := parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
    (euclideanZerothOrderCoeff c) u
  have hι := norm_inclusionOfLEL_succ_apply_le hα₁.le P
  rw [← hN] at hι
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine hv.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC_I
  calc _ ≤ N * ‖P‖ + M := add_le_add_left hι M
    _ ≤ N * ‖P‖ + M + (‖P‖ + N * M) :=
        le_add_of_nonneg_right (add_nonneg (norm_nonneg P) (mul_nonneg hN₀ hM₀))
    _ = (N + 1) * (‖P‖ + M) := by ring

/-- **From order `k` to order `k + 1`.** Since `θ_s' u = θ_s' (θ_{s/2} u)`, the term `θ_s' u` of
order `k + 1` is bounded by the localization of order `k + 2` at scale `s / 2`, to which the
induction hypothesis applies with the coefficients read at order `k`. -/
private theorem localizedBound_succ (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam) {k : ℕ}
    (ih : LocalizedBound (ι := ι) hα₁ lam k) : LocalizedBound (ι := ι) hα₁ lam (k + 1) := by
  intro K T₀ s hs
  obtain ⟨C_S, hC_S, hS⟩ := exists_norm_le_parabolicOperatorL (ι := ι) hα₀ hα₁ hlam (k + 1) K T₀
  obtain ⟨C_I, hC_I, hI⟩ := exists_norm_localize_inclusionOfLEL_le hα₁ ih K T₀ hs
  obtain ⟨Cθ, hCθ₀, hCθ⟩ := exists_norm_compSlabTime_le (k := k + 1) (E := EuclideanSpace ℝ ι)
    hα₁.le (contDiff_cutoff s) 0 T₀
  obtain ⟨Cθ', hCθ'₀, hCθ'⟩ := exists_norm_compSlabTime_le (k := k + 1) (E := EuclideanSpace ℝ ι)
    hα₁.le (contDiff_deriv_cutoff s) 0 T₀
  -- Name the product and inclusion constants, so that the bounds can be rewritten into them after
  -- `push_cast` and the arithmetic below treats them as atoms.
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = 21 * ((k : ℝ) + 1 + 1) ^ 2 * 2 ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ c : ℝ, c = 8 * ((k : ℝ) + 1 + 1) ^ 2 := ⟨_, rfl⟩
  have hc₁₀ : 0 ≤ c₁ := hc₁ ▸ by positivity
  have hN'₀ : 0 ≤ N' := hN' ▸ by positivity
  refine ⟨C_S * (c₁ * Cθ + c₁ * Cθ' * N' * C_I), by positivity,
    fun T hT hTT₀ hsT a b c ha hak hbk hck u M hM ↦ ?_⟩
  set P := parabolicOperatorL hα₁.le (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
    (euclideanZerothOrderCoeff c) u
  set v := localize hα₁.le k (s / 2)
    (inclusionOfLEL hα₁.le (Nat.add_le_add_right (Nat.le_succ k) 2) u)
  have hv := hI T hT hTT₀ hsT a b c ha hak hbk hck u hM
  -- The localized equation at order `k + 1`, with `θ_s' u = θ_s' (θ_{s/2} u)`.
  have hw := parabolicOperatorL_localize hα₁.le (k + 1) s a b c u
    (inclusionOfLEL hα₁.le (Nat.le_succ (k + 1)) v) fun p ↦ by
      rw [inclusionOfLEL_apply, localize_apply, inclusionOfLEL_apply, ← mul_assoc,
        deriv_cutoff_mul_cutoff_half hs]
  have h₁ := norm_lsmul_le hα₁.le (compSlabTime (k := k + 1) hα₁.le (contDiff_cutoff s)) P
  have h₂ := norm_lsmul_le hα₁.le (compSlabTime (k := k + 1) hα₁.le (contDiff_deriv_cutoff s))
    (inclusionOfLEL hα₁.le (Nat.le_succ (k + 1)) v)
  have h₃ := norm_inclusionOfLEL_succ_apply_le hα₁.le v
  have hθ := hCθ hT le_rfl (by exact_mod_cast hTT₀)
  have hθ' := hCθ' hT le_rfl (by exact_mod_cast hTT₀)
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (hS T hT hTT₀ a b c ha hak hbk hck (localize hα₁.le (k + 1) s u)).trans ?_
  rw [spatialTrace_localize hα₁.le (k + 1) hs, norm_zero, add_zero, hw, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hC_S
  push_cast at h₁ h₂ h₃
  rw [← hc₁] at h₁ h₂
  rw [← hN'] at h₃
  calc _ ≤ c₁ * (‖compSlabTime (k := k + 1) (E := EuclideanSpace ℝ ι) (hab := hT) hα₁.le
          (contDiff_cutoff s)‖ * ‖P‖) + c₁ * (‖compSlabTime (k := k + 1) (E := EuclideanSpace ℝ ι)
          (hab := hT) hα₁.le (contDiff_deriv_cutoff s)‖ * (N' * ‖v‖)) :=
        add_le_add h₁ (h₂.trans (by gcongr))
    _ ≤ c₁ * (Cθ * (‖P‖ + M)) + c₁ * (Cθ' * (N' * (C_I * (‖P‖ + M)))) := by
        gcongr
        linarith
    _ = _ := by ring

/-- The localized bound holds at every order. -/
private theorem localizedBound (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam) :
    ∀ k, LocalizedBound (ι := ι) hα₁ lam k
  | 0 => localizedBound_zero hα₀ hα₁ hlam
  | k + 1 => localizedBound_succ hα₀ hα₁ hlam (localizedBound hα₀ hα₁ hlam k)

/-- **Interior Schauder estimate of order `k` at positive times.** For `0 < α < 1`, an ellipticity
constant `λ > 0`, `k : ℕ`, a bound `K` on the norms of the coefficients in `C_{par,b}^{k+α}`, a
bound `T₀` on the horizon and a time `δ > 0`, there is a constant `C` such that on
`ℝⁿ × [0, T]`, `δ < T ≤ T₀`, every `u ∈ C_{par,b}^{k+2+α}` with `|u(·, 0)| ≤ M` satisfies

`‖u‖_{k+2+α;[δ,T]} ≤ C (‖P u‖_{k+α} + M)`,

where `‖u‖_{k+2+α;[δ,T]}` is the norm of the restriction of `u` to `ℝⁿ × [δ, T]` and
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. Only the supremum of the initial values enters, not their
`C^{k+2,α}` norm; the constant depends on `δ`. -/
theorem exists_norm_restrictL_le_parabolicOperatorL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hlam : 0 < lam) (k : ℕ) (K T₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ → ∀ hδT : δ < T,
      ∀ (a : ι → ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (b : ι → ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT)
        (c : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
          (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) →
          ‖restrictL hδ.le le_rfl hδT u‖ ≤ C * (‖parabolicOperatorL hα₁.le
            (euclideanSecondOrderCoeff a) (euclideanFirstOrderCoeff b)
            (euclideanZerothOrderCoeff c) u‖ + M) := by
  obtain ⟨C, hC, h⟩ := localizedBound (ι := ι) hα₀ hα₁ hlam k K T₀ (half_pos hδ)
  refine ⟨C, hC, fun T hT hTT₀ hδT a b c ha hak hbk hck u M hM ↦ ?_⟩
  -- On `ℝⁿ × [δ, T]` the localization at scale `δ / 2` is `u`.
  have hu : restrictL hδ.le le_rfl hδT u =
      restrictL hδ.le le_rfl hδT (localize hα₁.le k (δ / 2) u) := ext fun p ↦ by
    rw [restrictL_apply, restrictL_apply, localize_apply, cutoff_of_two_mul_le (half_pos hδ)
      (by linarith [(mem_slab.1 p.property).1]), one_mul]
  rw [hu]
  exact ((restrictL hδ.le le_rfl hδT).le_of_opNorm_le (norm_restrictL_le _ _ _) _).trans
    ((one_mul _).trans_le (h T hT hTT₀ (by linarith) a b c ha hak hbk hck u hM))

end Euclidean

end TauCeti.ParabolicCkHolderSpace
