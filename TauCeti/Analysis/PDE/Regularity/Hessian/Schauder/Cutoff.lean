/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Operator.Holder

/-!
# Hölder bounds for cutoff products in the Schauder estimates

The Schauder estimates for `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` on small balls, in the interior and up to a flat
boundary, are localized by multiplying the solution `u` by a smooth cutoff `ζ` supported in a ball
`s`. By the second-order product rule,

`∂ᵢ∂ⱼ(ζ u) = ζ ∂ᵢ∂ⱼu + Tᵢⱼ`, where `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu`,

so `L (ζ u) = ζ L u + ∑ᵢⱼ aᵢⱼ Tᵢⱼ`. This file bounds the Hölder constants of these functions on a
set `t` in terms of bounds for `ζ` and its derivatives on the whole space and for `u` and its
derivatives on `s ∩ t` only. For the interior estimate `t` is the whole space; for the estimate up
to a flat boundary it is a half-space, and `u` need only be `C²` on an open set containing the part
of `t` where `ζ` does not vanish.

## Main declarations

* `TauCeti.PDE.exists_cutoff_holderWith_and_abs_le`: cutoffs about every centre, leaving the
  Hessian unchanged on a smaller ball, with one constant bounding them, their first and second
  partial derivatives, and the Hölder constants of these.
* `TauCeti.PDE.abs_fderiv_apply_single_le_and_abs_fderiv_fderiv_apply_single_le`: bounds on `Du`
  and `D²u` bound the partial derivatives of `u`.
* `TauCeti.PDE.holderOnWith_and_holderOnWith_fderiv_apply_single`: the lower-order factors `u` and
  `∂ᵢu` are Hölder on a convex subset of a ball where `Du` and `D²u` are bounded.
* `TauCeti.PDE.holderOnWith_fderiv_fderiv_cutoff_mul`: the Hessian entries of `ζ u` are Hölder
  and bounded on `t`.
* `TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul`: `L (ζ u)` is Hölder on `t`.
* `TauCeti.PDE.two_mul_mul_add_div_add_mul_le_toNNReal_mul`: the comparison of constants closing
  the localized estimates.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, proofs of Theorem 6.2 and Lemma 6.5 (localization of the Schauder estimates by
  cutoffs).
-/

public section

noncomputable section

open Metric Set ContinuousLinearMap
open scoped NNReal ENNReal ContDiff

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- Translating a cutoff keeps the global Hölder constant and the uniform bound of the cutoff and
of its first and second derivatives in the directions `e i`. -/
private theorem holderWith_translate_cutoff {ι : Type*} (e : ι → E) {α Z : ℝ≥0}
    {ζ₀ : E → ℝ} (x₀ : E) (hZ0 : HolderWith Z α ζ₀ ∧ ∀ x, |ζ₀ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ₀ x (e i)) ∧ ∀ x, |fderiv ℝ ζ₀ x (e i)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x => fderiv ℝ (fderiv ℝ ζ₀) x (e i) (e j)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ₀) x (e i) (e j)| ≤ Z) :
    (HolderWith Z α (fun x => ζ₀ (x - x₀)) ∧ ∀ x, |ζ₀ (x - x₀)| ≤ Z) ∧
    (∀ i, HolderWith Z α (fun x => fderiv ℝ (fun x => ζ₀ (x - x₀)) x (e i)) ∧
      ∀ x, |fderiv ℝ (fun x => ζ₀ (x - x₀)) x (e i)| ≤ Z) ∧
    ∀ i j, HolderWith Z α (fun x => fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) x (e i) (e j)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) x (e i) (e j)| ≤ Z := by
  have hD1 : fderiv ℝ (fun x => ζ₀ (x - x₀)) = fun x => fderiv ℝ ζ₀ (x - x₀) :=
    funext fun _ => fderiv_comp_sub x₀
  have hD2 : fderiv ℝ (fderiv ℝ fun x => ζ₀ (x - x₀)) =
      fun x => fderiv ℝ (fderiv ℝ ζ₀) (x - x₀) := by
    rw [hD1]
    exact funext fun _ => fderiv_comp_sub x₀
  have htr {g : E → ℝ} (h : HolderWith Z α g ∧ ∀ x, |g x| ≤ Z) :
      HolderWith Z α (fun x => g (x - x₀)) ∧ ∀ x, |g (x - x₀)| ≤ Z :=
    ⟨fun x y => by simpa only [edist_sub_right] using h.1 (x - x₀) (y - x₀), fun x => h.2 _⟩
  refine ⟨htr hZ0, fun i => ?_, fun i j => ?_⟩
  · rw [hD1]
    exact htr (hZ1 i)
  · rw [hD2]
    exact htr (hZ2 i j)

/-- The product of a factor `c`, Hölder and bounded on `t` and vanishing at the points of `t` off
`s`, with a factor `g` which is bounded and Hölder on `s ∩ t` is Hölder on `t`, and bounded there
by the product of the bounds. -/
private theorem holderOnWith_mul_and_abs_le {c g : E → ℝ} {s t : Set E} {α Kc Mc Kg Mg : ℝ≥0}
    (hc : HolderOnWith Kc α c t) (hcM : ∀ x ∈ t, |c x| ≤ Mc) (hc0 : ∀ x ∈ t, x ∉ s → c x = 0)
    (hg : HolderOnWith Kg α g (s ∩ t)) (hgM : ∀ x ∈ s ∩ t, |g x| ≤ Mg) :
    HolderOnWith (Mc * Kg + Mg * Kc) α (fun x => c x * g x) t ∧
      ∀ x ∈ t, |c x * g x| ≤ Mc * Mg := by
  have hcM' : ∀ x ∈ t, ‖c x‖ ≤ Mc := by simpa only [Real.norm_eq_abs] using hcM
  have hgM' : ∀ x ∈ s ∩ t, ‖g x‖ ≤ Mg := by simpa only [Real.norm_eq_abs] using hgM
  refine ⟨by simpa only [smul_eq_mul] using hc.smul_of_eq_zero hg hcM' hgM' hc0, fun x hx => ?_⟩
  by_cases hxs : x ∈ s
  · rw [abs_mul]
    exact mul_le_mul (hcM x hx) (hgM x ⟨hxs, hx⟩) (abs_nonneg _) Mc.coe_nonneg
  · simp only [hc0 x hx hxs, zero_mul, abs_zero]
    positivity

/-- A smooth function with compact support has one constant `Z` which bounds it, its first and
second derivatives along the coordinate directions, and the `α`-Hölder constants of all of
these. -/
private theorem exists_holderWith_and_abs_le_of_hasCompactSupport {α : ℝ≥0} (hα : α ≤ 1)
    {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) :
    ∃ Z : ℝ≥0, (HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z) ∧
      (∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
        ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z) ∧
      ∀ i j, HolderWith Z α (fun x =>
          fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
        ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z
      := by
  have key : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      ∃ C : ℝ≥0, HolderWith C α φ ∧ ∀ x, |φ x| ≤ C := fun φ hφ hφc => by
    simpa only [Real.norm_eq_abs] using hφ.exists_holderWith_and_norm_le_of_hasCompactSupport hφc hα
  obtain ⟨C₀, hC₀, hM₀⟩ := key ζ (hζ.of_le (by norm_cast)) hc
  choose C₁ hC₁ hM₁ using fun i : Fin (n + 1) =>
    key (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1))
      ((hζ.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const)
      (hc.fderiv_apply (𝕜 := ℝ) _)
  choose C₂ hC₂ hM₂ using fun i j : Fin (n + 1) =>
    key (fun x => fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      ((((hζ.fderiv_right (m := 2) (by norm_cast)).fderiv_right (m := 1)
        le_rfl).clm_apply contDiff_const).clm_apply contDiff_const)
      (((hc.fderiv (𝕜 := ℝ)).fderiv_apply (𝕜 := ℝ) _).comp_left
        (g := fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) rfl)
  set Z : ℝ≥0 := C₀ + ∑ i, C₁ i + ∑ i, ∑ j, C₂ i j
  have h₀ : C₀ ≤ Z := le_add_right (le_add_right le_rfl)
  have h₁ (i : Fin (n + 1)) : C₁ i ≤ Z :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      (le_add_right (le_add_self))
  have h₂ (i j : Fin (n + 1)) : C₂ i j ≤ Z :=
    ((Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, C₂ i j) (fun _ _ => zero_le)
        (Finset.mem_univ i))).trans le_add_self
  exact ⟨Z, ⟨hC₀.mono h₀, fun x => (hM₀ x).trans (by exact_mod_cast h₀)⟩,
    fun i => ⟨(hC₁ i).mono (h₁ i), fun x => (hM₁ i x).trans (by exact_mod_cast h₁ i)⟩,
    fun i j => ⟨(hC₂ i j).mono (h₂ i j), fun x => (hM₂ i j x).trans (by exact_mod_cast h₂ i j)⟩⟩

/-- **Cutoffs about every centre with one set of bounds.** For `ρ < R` and `α ≤ 1` there is a
constant `Z` such that about every centre `x₀` there is a `C²` function `ζ`, supported in
`ball x₀ R`, with `D²(ζ u) = D²u` on `closedBall x₀ ρ` for every `u`, and such that `ζ` and its
first and second partial derivatives are bounded by `Z` and globally `α`-Hölder with constant
`Z`. -/
theorem exists_cutoff_holderWith_and_abs_le {α : ℝ≥0} (hα : α ≤ 1) {ρ R : ℝ} (hρR : ρ < R) :
    ∃ Z : ℝ≥0, ∀ x₀ : E, ∃ ζ : E → ℝ, ContDiff ℝ 2 ζ ∧ tsupport ζ ⊆ ball x₀ R ∧
      (∀ (u : E → ℝ), ∀ x ∈ closedBall x₀ ρ,
        iteratedFDeriv ℝ 2 (ζ * u) x = iteratedFDeriv ℝ 2 u x) ∧
      (HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z) ∧
      (∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
        ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z) ∧
      ∀ i j, HolderWith Z α (fun x =>
          fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
        ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z
      := by
  obtain ⟨ζ₀, hζ₀, -, hζ₀1, hζ₀c, hζ₀s⟩ :=
    (isCompact_closedBall (0 : E) ρ).exists_contDiff_cutoff isOpen_ball
      (closedBall_subset_ball hρR)
  obtain ⟨Z, hZ0, hZ1, hZ2⟩ := exists_holderWith_and_abs_le_of_hasCompactSupport hα hζ₀ hζ₀c
  -- The cutoffs are the translates of one cutoff `ζ₀` about the origin, equal to one near
  -- `closedBall 0 ρ`, which is why `Z` does not depend on `x₀`.
  refine ⟨Z, fun x₀ => ⟨fun x => ζ₀ (x - x₀),
    (hζ₀.of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const), fun x hx => ?_,
    fun u x hx => ?_, holderWith_translate_cutoff (fun i => EuclideanSpace.single i 1) x₀ hZ0 hZ1
      hZ2⟩⟩
  · simpa [dist_eq_norm] using hζ₀s (tsupport_comp_subset_preimage ζ₀
      (continuous_id.sub continuous_const) hx)
  · have h1 := preimage_interior_subset_interior_preimage (continuous_id.sub continuous_const)
      (hζ₀1 (by simpa [dist_eq_norm] using hx))
    refine Filter.EventuallyEq.iteratedFDeriv_mul_eq ?_
    filter_upwards [mem_interior_iff_mem_nhds.1 h1] with y hy
    simpa using hy

/-- On a convex set `s` inside a ball `B_R`, contained in an open set where `u` is `C²`, a function
with `‖Du‖ ≤ N` and `‖D²u‖ ≤ N` on `s`, and each of its partial derivatives, are `α`-Hölder on `s`
with constant `N (2R)^(1 - α)`. -/
theorem holderOnWith_and_holderOnWith_fderiv_apply_single {u : E → ℝ} {s U : Set E}
    (hs : Convex ℝ s) {x₀ : E} {R : ℝ} (hsR : s ⊆ ball x₀ R) {N α : ℝ≥0} (hα : α ≤ 1)
    (hU : IsOpen U) (hsU : s ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hN1 : ∀ x ∈ s, ‖fderiv ℝ u x‖ ≤ N) (hN2 : ∀ x ∈ s, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α u s ∧
      ∀ i, HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α
        (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s := by
  have hHDu := hs.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le hsR hα hU hsU hu hN2
  refine ⟨hs.holderOnWith_of_norm_fderiv_le hsR hα (fun x hx =>
    (hu.differentiableOn two_ne_zero x (hsU hx)).differentiableAt (hU.mem_nhds (hsU hx))) hN1,
    fun i => ?_⟩
  have hev : LipschitzWith 1 fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1) :=
    LipschitzWith.of_dist_le_mul fun L L' => by
      rw [dist_eq_norm, dist_eq_norm, ← sub_apply, NNReal.coe_one, one_mul]
      exact (L - L').unit_le_opNorm _ (by simp)
  have h := (holderWith_one.2 hev).comp_holderOnWith hHDu
  simp only [NNReal.coe_one, NNReal.rpow_one, one_mul] at h
  exact h

/-- Bounds `‖Du‖ ≤ N` and `‖D²u‖ ≤ N` on a set `s` bound the first and second partial derivatives
of `u` along the coordinate directions by `N` on `s`. -/
theorem abs_fderiv_apply_single_le_and_abs_fderiv_fderiv_apply_single_le {u : E → ℝ} {s : Set E}
    {N : ℝ} (hN1 : ∀ x ∈ s, ‖fderiv ℝ u x‖ ≤ N) (hN2 : ∀ x ∈ s, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) :
    (∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N) ∧
      ∀ i j, ∀ x ∈ s,
        |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N :=
  ⟨fun i x hx => by
    simpa using ((fderiv ℝ u x).unit_le_opNorm (EuclideanSpace.single i 1) (by simp)).trans
      (hN1 x hx),
  fun i j x hx => by
    simpa [iteratedFDeriv_two_apply] using
      ((iteratedFDeriv ℝ 2 u x).norm_apply_orthonormalBasis_le
        (EuclideanSpace.basisFun _ ℝ) i j).trans (hN2 x hx)⟩

/-- The second-order product rule for a cutoff product `ζ u` at a point of `t`, when `ζ` is `C²`
and `u` is `C²` on an open set containing the points of `t` in the topological support of `ζ`. -/
private theorem fderiv_fderiv_cutoff_mul_apply {t U : Set E} (hU : IsOpen U) {ζ u : E → ℝ}
    (hζ : ContDiff ℝ 2 ζ) (hζU : tsupport ζ ∩ t ⊆ U) (hu : ContDiffOn ℝ 2 u U) {x : E}
    (hx : x ∈ t) (v w : E) :
    fderiv ℝ (fderiv ℝ (ζ * u)) x v w =
      ζ x * fderiv ℝ (fderiv ℝ u) x v w +
        (fderiv ℝ (fderiv ℝ ζ) x v w * u x + fderiv ℝ ζ x v * fderiv ℝ u x w +
          fderiv ℝ ζ x w * fderiv ℝ u x v) := by
  by_cases hxs : x ∈ tsupport ζ
  · rw [fderiv_fderiv_mul_apply hζ.contDiffAt (hu.contDiffAt (hU.mem_nhds (hζU ⟨hxs, hx⟩)))]
    ring
  · rw [fderiv_fderiv_mul_apply_of_notMem_tsupport hxs]
    ring

/-- The lower-order part `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu` of the Hessian entry `∂ᵢ∂ⱼ(ζ u)`
vanishes off `s`, and is Hölder and bounded on `t`, when the first and second derivatives of `ζ`
are globally Hölder and bounded with constant `Z` and `ζ` is supported in `s`, while `u` and its
first derivatives are bounded by `N` and Hölder with constant `H` on `s ∩ t`. -/
private theorem holderOnWith_cutoff_remainder {s t : Set E} {ζ u : E → ℝ} {α Z N H : ℝ≥0}
    (hζs : tsupport ζ ⊆ s)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hN0 : ∀ x ∈ s ∩ t, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s ∩ t, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hH0 : HolderOnWith H α u (s ∩ t))
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) (s ∩ t))
    (i j : Fin (n + 1)) :
    HolderOnWith (3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) t ∧
    (∀ x ∈ t, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
        u x + fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)| ≤
      3 * Z * N) ∧
    ∀ x ∉ s, fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1) =
      0 := by
  have hζ'0 (k : Fin (n + 1)) (x : E) (hx : x ∉ s) :
      fderiv ℝ ζ x (EuclideanSpace.single k 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ fun h => hx (hζs h), zero_apply]
  have hζ''0 (x : E) (hx : x ∉ s) :
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ fun h => hx (hζs (tsupport_fderiv_subset ℝ h)),
      zero_apply, zero_apply]
  obtain ⟨h1, b1⟩ := holderOnWith_mul_and_abs_le ((hZ2 i j).1.holderOnWith t)
    (fun x _ => (hZ2 i j).2 x) (fun x _ => hζ''0 x) hH0 hN0
  obtain ⟨h2, b2⟩ := holderOnWith_mul_and_abs_le ((hZ1 i).1.holderOnWith t)
    (fun x _ => (hZ1 i).2 x) (fun x _ => hζ'0 i x) (hH1 j) (hN1 j)
  obtain ⟨h3, b3⟩ := holderOnWith_mul_and_abs_le ((hZ1 j).1.holderOnWith t)
    (fun x _ => (hZ1 j).2 x) (fun x _ => hζ'0 j x) (hH1 i) (hN1 i)
  refine ⟨((h1.add h2).add h3).mono_const (le_of_eq (by ring)), fun x hx => ?_, fun x hx => ?_⟩
  · refine (abs_add_three _ _ _).trans
      ((add_le_add_three (b1 x hx) (b2 x hx) (b3 x hx)).trans_eq ?_)
    ring
  · simp only [hζ''0 x hx, hζ'0 i x hx, hζ'0 j x hx, zero_mul, add_zero]

/-- The Hessian entries `∂ᵢ∂ⱼ(ζ u) = ζ ∂ᵢ∂ⱼu + Tᵢⱼ` of a cutoff product are Hölder and bounded on
`t`, when `ζ` is `C²` and supported in `s` with `ζ` and its first and second derivatives globally
Hölder and bounded with constant `Z`, while `u` is `C²` on an open set containing the points of `t`
in the support of `ζ`, with `u` and its first and second derivatives bounded by `N` on `s ∩ t`, and
Hölder there with constants `H`, `H` and `V`. -/
theorem holderOnWith_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U) {ζ u : E → ℝ}
    {α Z N H V : ℝ≥0} (hζ : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ s) (hζU : tsupport ζ ∩ t ⊆ U)
    (hZ0 : HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hu : ContDiffOn ℝ 2 u U) (hN0 : ∀ x ∈ s ∩ t, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s ∩ t, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s ∩ t,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u (s ∩ t))
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) (s ∩ t))
    (hV : ∀ i j, HolderOnWith V α (fun x =>
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (s ∩ t))
    (i j : Fin (n + 1)) :
    HolderOnWith (Z * V + N * Z + 3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t ∧
    ∀ x ∈ t,
      |fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
        4 * Z * N := by
  obtain ⟨hT, bT, -⟩ := holderOnWith_cutoff_remainder hζs hZ1 hZ2 hN0 hN1 hH0 hH1 i j
  obtain ⟨h1, b1⟩ := holderOnWith_mul_and_abs_le (hZ0.1.holderOnWith t) (fun x _ => hZ0.2 x)
    (fun x _ hx => image_eq_zero_of_notMem_tsupport fun h => hx (hζs h)) (hV i j) (hN2 i j)
  have hW (x : E) (hx : x ∈ t) := fderiv_fderiv_cutoff_mul_apply hU hζ hζU hu hx
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  refine ⟨(h1.add hT).congr fun x hx => (hW x hx).symm, fun x hx => ?_⟩
  rw [hW x hx]
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ (Z * N : ℝ) + 3 * Z * N := add_le_add (b1 x hx) (bT x hx)
    _ = _ := by ring

/-- For a cutoff product `ζ u` as in `holderOnWith_fderiv_fderiv_cutoff_mul`, the operator
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` is Hölder on `t`, when the coefficients are
bounded by `M` and Hölder with constant `L` on `s ∩ t`, and `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` is Hölder with
constant `K` on `s ∩ t`. The Hessian of `u` need not be Hölder. -/
theorem holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U)
    {ζ u : E → ℝ} {α Z N H : ℝ≥0} (hζ : ContDiff ℝ 2 ζ) (hζs : tsupport ζ ⊆ s)
    (hζU : tsupport ζ ∩ t ⊆ U) (hZ0 : HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hu : ContDiffOn ℝ 2 u U) (hN0 : ∀ x ∈ s ∩ t, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s ∩ t, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s ∩ t,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u (s ∩ t))
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) (s ∩ t))
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {L M K : ℝ≥0}
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) (s ∩ t))
    (hM : ∀ x ∈ s ∩ t, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (s ∩ t)) :
    HolderOnWith (Z * K + (n + 1) ^ 2 * (M * N * Z + (3 * Z * N * L + M * (3 * (Z * H + N * Z)))))
      α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ (ζ * u)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t := by
  set f : E → ℝ := fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hfM (x : E) (hx : x ∈ s ∩ t) : |f x| ≤ ((n + 1) ^ 2 * M * N : ℝ≥0) := by
    calc |f x| ≤ ∑ i, ∑ j, |a x i j • fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), (M * N : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [smul_eq_mul, abs_mul]
          exact mul_le_mul (hM x hx i j) (hN2 i j x hx) (abs_nonneg _) M.coe_nonneg
      _ = _ := by simp; ring
  have heq (x : E) (hx : x ∈ t) : ∑ i, ∑ j, a x i j •
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      ζ x * f x + ∑ i, ∑ j,
        (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
          fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
          fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) *
        a x i j := by
    simp only [fderiv_fderiv_cutoff_mul_apply hU hζ hζU hu hx, smul_eq_mul, f,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨h1, -⟩ := holderOnWith_mul_and_abs_le (hZ0.1.holderOnWith t) (fun x _ => hZ0.2 x)
    (fun x _ hx => image_eq_zero_of_notMem_tsupport fun h => hx (hζs h)) hK hfM
  have h2 (i j : Fin (n + 1)) := by
    obtain ⟨hT, bT, hT0⟩ := holderOnWith_cutoff_remainder hζs hZ1 hZ2 hN0 hN1 hH0 hH1 i j
    exact (holderOnWith_mul_and_abs_le hT (Mc := 3 * Z * N) (by exact_mod_cast bT)
      (fun x _ => hT0 x) (hL i j) fun x hx => hM x hx i j).1
  have hC : Z * K + (n + 1) ^ 2 * M * N * Z + ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1),
      (3 * Z * N * L + M * (3 * (Z * H + N * Z))) =
      Z * K + (n + 1) ^ 2 * (M * N * Z + (3 * Z * N * L + M * (3 * (Z * H + N * Z)))) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  exact ((h1.add (HolderOnWith.sum (s := Finset.univ) fun i _ =>
    HolderOnWith.sum (s := Finset.univ) fun j _ => h2 i j)).mono_const hC.le).congr
    fun x hx => (heq x hx).symm

/-- The comparison of constants closing the localized Schauder estimates: if `X ≤ A N`, then
`2 κ ((Z K + N B) / λ + Q X) ≤ 2 κ (Z / λ + B / λ + Q A) (K + N)`. -/
theorem two_mul_mul_add_div_add_mul_le_toNNReal_mul {κ lam Q A X : ℝ} {Z B K N : ℝ≥0}
    (hκ : 0 ≤ κ) (hlam : 0 < lam) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hX : X ≤ A * N) :
    2 * κ * (((Z * K + N * B : ℝ≥0) : ℝ) / lam + Q * X) ≤
      ((2 * κ * (Z / lam + B / lam + Q * A)).toNNReal * (K + N) : ℝ≥0) := by
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
  push_cast
  have hdiv : ((Z : ℝ) * K + N * B) / lam = Z / lam * K + B / lam * N := by ring
  calc 2 * κ * ((Z * K + N * B) / lam + Q * X)
      ≤ 2 * κ * (Z / lam * K + B / lam * N + Q * A * N) := by
        rw [hdiv, mul_assoc Q A]
        gcongr
    _ ≤ 2 * κ * (Z / lam + B / lam + Q * A) * (K + N) := by
        rw [mul_assoc (2 * κ)]
        gcongr
        have : 0 ≤ (Z : ℝ) / lam := by positivity
        have : 0 ≤ (B : ℝ) / lam := by positivity
        have : 0 ≤ Q * A := mul_nonneg hQ hA
        have := K.coe_nonneg
        have := N.coe_nonneg
        nlinarith

end TauCeti.PDE
