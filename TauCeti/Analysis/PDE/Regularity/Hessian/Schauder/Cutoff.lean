/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder bounds for cutoff products in the Schauder estimates

The Schauder estimates on small balls and half-balls are localized by a smooth cutoff `ζ`: a
solution `u`, given only near the support of `ζ`, is replaced by the cutoff product `w = ζ u`, to
which an estimate for functions with compactly supported Hessian applies. By the second-order
product rule,

`∂ᵢ∂ⱼw = ζ ∂ᵢ∂ⱼu + Tᵢⱼ`, where `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu`,

so `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼw = ζ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ∑ᵢⱼ aᵢⱼ Tᵢⱼ`. Every term is a product of a factor built from
`ζ`, which vanishes off a set `s`, with a factor that is bounded and Hölder on `s`; such products
are Hölder (`HolderOnWith.smul_of_eq_zero`). This file proves these bounds on an arbitrary set `t`:
the data need only be given on `s ∩ t`. The interior estimate takes `t` to be the whole space. The
boundary estimate takes `t` to be the closed half-space for the Hessian entries of `w`, and the open
half-space for the operator applied to `w`.

## Main declarations

* `TauCeti.PDE.exists_forall_exists_cutoff`: smooth cutoffs about every centre, with one constant
  bounding them, their first and second coordinate derivatives and the Hölder constants of these.
* `TauCeti.PDE.abs_fderiv_apply_single_le_and_abs_fderiv_fderiv_apply_single_single_le`: norm
  bounds on the first and second derivatives bound the coordinate partial derivatives.
* `TauCeti.PDE.holderOnWith_fderiv_fderiv_cutoff_mul`: the Hessian entries of a cutoff product are
  Hölder and bounded on `t`.
* `TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul`: the operator `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ`
  applied to a cutoff product is Hölder on `t`.
* `TauCeti.PDE.two_mul_mul_add_div_add_mul_le`: the comparison of constants that closes the
  localized estimates.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, proofs of Theorem 6.2 and Lemma 6.4 (localization of the Schauder estimates by
  cutoffs).
-/

public section

noncomputable section

open Metric Set
open scoped NNReal ContDiff

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

/-- **Uniform cutoffs.** For `ρ < R` and `α ≤ 1` there is one constant `Z` such that about every
centre `x₀` some smooth cutoff `ζ`, equal to one near `closedBall x₀ ρ` and supported in
`ball x₀ R`, is bounded by `Z` together with its first and second derivatives along the coordinate
directions, all of which are `α`-Hölder with constant `Z`. The cutoffs are the translates of one
cutoff about the origin. -/
theorem exists_forall_exists_cutoff {α : ℝ≥0} (hα : α ≤ 1) {ρ R : ℝ} (hρR : ρ < R) :
    ∃ Z : ℝ≥0, ∀ x₀ : E, ∃ ζ : E → ℝ, ContDiff ℝ ∞ ζ ∧
      closedBall x₀ ρ ⊆ interior (ζ ⁻¹' {1}) ∧ tsupport ζ ⊆ ball x₀ R ∧
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
  refine ⟨Z, fun x₀ => ⟨fun x => ζ₀ (x - x₀), hζ₀.comp (contDiff_id.sub contDiff_const),
    fun x hx => ?_, fun x hx => ?_,
    holderWith_translate_cutoff (fun i => EuclideanSpace.single i 1) x₀ hZ0 hZ1 hZ2⟩⟩
  · exact preimage_interior_subset_interior_preimage (continuous_id.sub continuous_const)
      (hζ₀1 (by simpa [dist_eq_norm] using hx))
  · simpa [dist_eq_norm] using hζ₀s (tsupport_comp_subset_preimage ζ₀
      (continuous_id.sub continuous_const) hx)

/-- Bounds `‖Du‖ ≤ N` and `‖D²u‖ ≤ N` on a set `S` bound the first and second partial derivatives
of `u` along the coordinate directions by `N` on `S`. -/
theorem abs_fderiv_apply_single_le_and_abs_fderiv_fderiv_apply_single_single_le {u : E → ℝ}
    {S : Set E} {N : ℝ} (hN1 : ∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ S, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) :
    (∀ i, ∀ x ∈ S, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N) ∧
      ∀ i j, ∀ x ∈ S,
        |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N :=
  ⟨fun i x hx => by
    simpa using ((fderiv ℝ u x).unit_le_opNorm (EuclideanSpace.single i 1) (by simp)).trans
      (hN1 x hx),
  fun i j x hx => by
    simpa [iteratedFDeriv_two_apply] using
      ((iteratedFDeriv ℝ 2 u x).norm_apply_orthonormalBasis_le
        (EuclideanSpace.basisFun _ ℝ) i j).trans (hN2 x hx)⟩

/-- The product of a factor `c` which is Hölder and bounded on `t` and vanishes at the points of `t`
off `s` with a factor `g` which is Hölder and bounded on `s ∩ t` is Hölder on `t`, and bounded there
by the product of the bounds. -/
private theorem holderOnWith_mul_and_abs_le {c g : E → ℝ} {s t : Set E} {α Kc Mc Kg Mg : ℝ≥0}
    (hc : HolderOnWith Kc α c t) (hcM : ∀ x ∈ t, |c x| ≤ Mc) (hc0 : ∀ x ∈ t, x ∉ s → c x = 0)
    (hg : HolderOnWith Kg α g (s ∩ t)) (hgM : ∀ x ∈ s ∩ t, |g x| ≤ Mg) :
    HolderOnWith (Mc * Kg + Mg * Kc) α (fun x => c x * g x) t ∧
      ∀ x ∈ t, |c x * g x| ≤ Mc * Mg := by
  have hcM' : ∀ x ∈ t, ‖c x‖ ≤ Mc := by simpa only [Real.norm_eq_abs] using hcM
  have hgM' : ∀ x ∈ s ∩ t, ‖g x‖ ≤ Mg := by simpa only [Real.norm_eq_abs] using hgM
  refine ⟨by simpa only [smul_eq_mul] using hc.smul_of_eq_zero hg hcM' hgM' hc0, fun x hxt => ?_⟩
  by_cases hx : x ∈ s
  · rw [abs_mul]
    exact mul_le_mul (hcM x hxt) (hgM x ⟨hx, hxt⟩) (abs_nonneg _) Mc.coe_nonneg
  · simp only [hc0 x hxt hx, zero_mul, abs_zero]
    positivity

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
  have hglob {c : E → ℝ} (hc : HolderWith Z α c ∧ ∀ x, |c x| ≤ Z) (hc0 : ∀ x ∉ s, c x = 0) :
      HolderOnWith Z α c t ∧ (∀ x ∈ t, |c x| ≤ Z) ∧ ∀ x ∈ t, x ∉ s → c x = 0 :=
    ⟨hc.1.holderOnWith t, fun x _ => hc.2 x, fun x _ => hc0 x⟩
  obtain ⟨c1, c1M, c10⟩ := hglob (hZ2 i j) hζ''0
  obtain ⟨c2, c2M, c20⟩ := hglob (hZ1 i) (hζ'0 i)
  obtain ⟨c3, c3M, c30⟩ := hglob (hZ1 j) (hζ'0 j)
  obtain ⟨h1, b1⟩ := holderOnWith_mul_and_abs_le c1 c1M c10 hH0 hN0
  obtain ⟨h2, b2⟩ := holderOnWith_mul_and_abs_le c2 c2M c20 (hH1 j) (hN1 j)
  obtain ⟨h3, b3⟩ := holderOnWith_mul_and_abs_le c3 c3M c30 (hH1 i) (hN1 i)
  refine ⟨(((h1.add h2).add h3).mono_const (le_of_eq (by ring))), fun x hx => ?_, fun x hx => ?_⟩
  · refine (abs_add_three _ _ _).trans
      ((add_le_add_three (b1 x hx) (b2 x hx) (b3 x hx)).trans_eq ?_)
    ring
  · simp only [hζ''0 x hx, hζ'0 i x hx, hζ'0 j x hx, zero_mul, add_zero]

/-- **The Hessian of a cutoff product.** The Hessian entries `∂ᵢ∂ⱼ(ζ u) = ζ ∂ᵢ∂ⱼu + Tᵢⱼ` of a
cutoff product are Hölder and bounded on a set `t`, when `ζ` is supported in `s` and `ζ` and its
first and second derivatives are globally Hölder and bounded with constant `Z`, while `ζ` and `u`
are `C²` on an open set `U` containing `t ∩ tsupport ζ`, with `u` and its first and second
derivatives bounded by `N` on `s ∩ t`, and Hölder there with constants `H`, `H` and `V`. -/
theorem holderOnWith_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U) {ζ u : E → ℝ}
    {α Z N H V : ℝ≥0} (hζ : ContDiffOn ℝ 2 ζ U) (hζs : tsupport ζ ⊆ s) (htU : t ∩ tsupport ζ ⊆ U)
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
  have hW (x : E) (hx : x ∈ t) :
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        ζ x * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
          fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
          fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) := by
    rw [fderiv_fderiv_mul_apply_of_tsupport_subset hU hζ htU hu hx]
    ring
  refine ⟨(h1.add hT).congr fun x hx => (hW x hx).symm, fun x hx => ?_⟩
  rw [hW x hx]
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ (Z * N : ℝ) + 3 * Z * N := add_le_add (b1 x hx) (bT x hx)
    _ = _ := by ring

/-- **The operator applied to a cutoff product.** For a cutoff product `ζ u` as in
`holderOnWith_fderiv_fderiv_cutoff_mul`, the operator
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` is Hölder on `t`, when the coefficients are
bounded by `M` and Hölder with constant `L` on `s ∩ t`, and `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` is Hölder with constant
`K` on `s ∩ t`. The Hessian of `u` need not be Hölder. -/
theorem holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U)
    {ζ u : E → ℝ} {α Z N H : ℝ≥0} (hζ : ContDiffOn ℝ 2 ζ U) (hζs : tsupport ζ ⊆ s)
    (htU : t ∩ tsupport ζ ⊆ U)
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
  have heq : EqOn (fun x => ζ x * f x + ∑ i, ∑ j,
        (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
          fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
          fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) *
        a x i j) (fun x => ∑ i, ∑ j, a x i j •
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t := by
    intro x hx
    simp only [fderiv_fderiv_mul_apply_of_tsupport_subset hU hζ htU hu hx, smul_eq_mul, f,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨h1, -⟩ := holderOnWith_mul_and_abs_le (hZ0.1.holderOnWith t) (fun x _ => hZ0.2 x)
    (fun x _ hx => image_eq_zero_of_notMem_tsupport fun h => hx (hζs h)) hK hfM
  have h2 (i j : Fin (n + 1)) := by
    obtain ⟨hT, bT, hT0⟩ := holderOnWith_cutoff_remainder hζs hZ1 hZ2 hN0 hN1 hH0 hH1 i j
    exact (holderOnWith_mul_and_abs_le hT (Mc := 3 * Z * N) (by exact_mod_cast bT)
      (fun x _ hx => hT0 x hx) (hL i j) fun x hx => hM x hx i j).1
  have hsum : HolderOnWith (∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1),
      (3 * Z * N * L + M * (3 * (Z * H + N * Z)))) α (fun x => ∑ i, ∑ j,
        (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
          fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
          fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) *
        a x i j) t :=
    HolderWith.restrict_iff.1 (HolderWith.sum fun i _ => HolderWith.sum fun j _ =>
      (h2 i j).holderWith)
  refine ((h1.add hsum).congr heq).mono_const (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The comparison of constants closing the localized Schauder estimates: with
`κ = C₀ (Λ / λ)^e`, `0 ≤ C₀`, `0 < λ ≤ Λ`, `0 ≤ Q` and `0 ≤ A`, if `X ≤ A N` then
`2 κ ((Z K + N B) / λ + Q X) ≤ max (2 κ (Z / λ + B / λ + Q A)) 0 * (K + N)`. -/
theorem two_mul_mul_add_div_add_mul_le {C₀ lam Lam e Q A X : ℝ} {Z B K N : ℝ≥0} (hC₀ : 0 ≤ C₀)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hX : X ≤ A * N) :
    2 * (C₀ * (Lam / lam) ^ e) * (((Z * K + N * B : ℝ≥0) : ℝ) / lam + Q * X) ≤
      ((2 * (C₀ * (Lam / lam) ^ e) * (Z / lam + B / lam + Q * A)).toNNReal * (K + N) : ℝ≥0) := by
  have hκ : 0 ≤ C₀ * (Lam / lam) ^ e :=
    mul_nonneg hC₀ (Real.rpow_nonneg (div_nonneg (hlam.le.trans hlamLam) hlam.le) _)
  set κ := C₀ * (Lam / lam) ^ e
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
  push_cast
  have hdiv : ((Z : ℝ) * K + N * B) / lam = Z / lam * K + B / lam * N := by ring
  calc 2 * κ * (((Z : ℝ) * K + N * B) / lam + Q * X)
      ≤ 2 * κ * (Z / lam * K + B / lam * N + Q * A * N) := by
        rw [hdiv, mul_assoc Q A]
        gcongr
    _ ≤ 2 * κ * (Z / lam + B / lam + Q * A) * (K + N) := by
        rw [mul_assoc (2 * κ)]
        gcongr
        have : 0 ≤ (Z : ℝ) / lam := by positivity
        have : 0 ≤ (B : ℝ) / lam := by positivity
        have : 0 ≤ Q * A := mul_nonneg hQ hA
        have : 0 ≤ (K : ℝ) := K.coe_nonneg
        have : 0 ≤ (N : ℝ) := N.coe_nonneg
        nlinarith

end TauCeti.PDE
