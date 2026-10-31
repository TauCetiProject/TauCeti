/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CompactSupport
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.Support
import TauCeti.Topology.MetricSpace.Holder

/-!
# The interior Schauder estimate on small balls

Let `0 < α < 1`, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a non-divergence-form operator on `ℝ^{n+1}`
whose coefficients are `α`-Hölder with constant `L` on the closed ball `closedBall x₀ R`, and such
that `a(x₀)` has ellipticity constants `0 < λ ≤ Λ`. If `R` is small compared with the Hölder
modulus of the coefficients, in the sense of the scale condition of
`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_support_subset_closedBall`, then for every
`ρ < R` there is a constant `C`, independent of the solution, such that every `u` which is `C²` on
the open ball `B_R` with `α`-Hölder Hessian there satisfies

`[D²u]_{α; closedBall x₀ ρ} ≤ C ([L u]_{α; B_R} + N)`,

where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on `B_R`. The Hölder constant of the Hessian on `B_R`
enters only qualitatively: the estimate does not depend on it. This is the localized form of the
Schauder estimate used to pass from coefficients of small oscillation on a ball to Hölder
continuous coefficients on a domain, by covering a compact set with small balls.

## The argument

Choose a smooth cutoff `ζ` equal to one near `closedBall x₀ ρ` with support in `B_R`, and put
`w = ζ u`, which is `C²` on the whole space (`ContDiffOn.contDiff_smul_of_tsupport_subset`). By the
second-order product rule (`TauCeti.fderiv_fderiv_mul_apply_of_tsupport_subset`),

`∂ᵢ∂ⱼw = ζ ∂ᵢ∂ⱼu + Tᵢⱼ`, where `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu`,

so `L w = ζ L u + ∑ᵢⱼ aᵢⱼ Tᵢⱼ`. Every term is a product of a globally Hölder factor built from
`ζ`, vanishing off `B_R`, and a factor that is bounded and Hölder on `B_R`; such products are
globally Hölder (`HolderWith.smul_of_eq_zero`). On the ball the lower-order factors `u` and `∂ⱼu`
are Lipschitz, with constant `N`, hence `α`-Hölder. This bounds the Hölder constant of `L w` by
`C (K + N)`, where `K` is the Hölder constant of `L u`, and `‖D²w‖_{L²} ≤ C N`; the Hessian of
`w` is supported in `B_R` and globally Hölder a priori. The compact-support estimate then bounds the
Hölder constant of `D²w`, which equals `D²u` near `closedBall x₀ ρ`.

## Main declaration

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`: the
  interior Schauder estimate on small balls.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, proof of Theorem 6.2 (localization of the Schauder estimate by cutoffs).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The product of a globally Hölder factor `c` vanishing off `s` with a factor `g` which is
bounded and Hölder on `s` is globally Hölder, and bounded by the product of the bounds. -/
private theorem holderWith_mul_and_abs_le {c g : E → ℝ} {s : Set E} {α Kc Mc Kg Mg : ℝ≥0}
    (hc : HolderWith Kc α c) (hcM : ∀ x, |c x| ≤ Mc) (hc0 : ∀ x ∉ s, c x = 0)
    (hg : HolderOnWith Kg α g s) (hgM : ∀ x ∈ s, |g x| ≤ Mg) :
    HolderWith (Mc * Kg + Mg * Kc) α (fun x => c x * g x) ∧ ∀ x, |c x * g x| ≤ Mc * Mg := by
  have hcM' : ∀ x, ‖c x‖ ≤ Mc := by simpa only [Real.norm_eq_abs] using hcM
  have hgM' : ∀ x ∈ s, ‖g x‖ ≤ Mg := by simpa only [Real.norm_eq_abs] using hgM
  refine ⟨by simpa only [smul_eq_mul] using hc.smul_of_eq_zero hg hcM' hgM' hc0, fun x => ?_⟩
  by_cases hx : x ∈ s
  · rw [abs_mul]
    exact mul_le_mul (hcM x) (hgM x hx) (abs_nonneg _) Mc.coe_nonneg
  · simp only [hc0 x hx, zero_mul, abs_zero]
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

/-- On the ball `B_R`, a `C²` function with `‖Du‖ ≤ N` and `‖D²u‖ ≤ N`, and each of its partial
derivatives, are `α`-Hölder with constant `N (2R)^(1 - α)`: they are `N`-Lipschitz on the convex
set `B_R`, whose diameter is at most `2R`. -/
private theorem holderOnWith_ball_of_norm_le {u : E → ℝ} {x₀ : E} {R : ℝ} {N α : ℝ≥0}
    (hα : α ≤ 1) (hu : ContDiffOn ℝ 2 u (ball x₀ R))
    (hN1 : ∀ x ∈ ball x₀ R, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α u (ball x₀ R) ∧
      ∀ i, HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α
        (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) (ball x₀ R) := by
  have hA : ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, edist x y ≤ (2 * R).toNNReal := by
    intro x hx y hy
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [dist_triangle_right x y x₀, mem_ball.1 hx, mem_ball.1 hy]
  have hcda (x : E) (hx : x ∈ ball x₀ R) : ContDiffAt ℝ 2 u x :=
    hu.contDiffAt (isOpen_ball.mem_nhds hx)
  have hLu : LipschitzOnWith N u (ball x₀ R) :=
    (convex_ball x₀ R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx => (hcda x hx).differentiableAt (by norm_num))
      fun x hx => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hN1 x hx
  have hLDu : LipschitzOnWith N (fderiv ℝ u) (ball x₀ R) :=
    (convex_ball x₀ R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x hx => ((hcda x hx).fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num))
      fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
        exact hN2 x hx
  have hholder {g : E → ℝ} (hg : LipschitzOnWith N g (ball x₀ R)) :
      HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α g (ball x₀ R) := by
    simpa using (holderOnWith_one.2 hg).of_le hA hα
  refine ⟨hholder hLu, fun i => hholder (LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_)⟩
  rw [dist_eq_norm, ← sub_apply]
  calc ‖(fderiv ℝ u x - fderiv ℝ u y) (EuclideanSpace.single i 1)‖
      ≤ ‖fderiv ℝ u x - fderiv ℝ u y‖ := (fderiv ℝ u x - fderiv ℝ u y).unit_le_opNorm _ (by simp)
    _ ≤ N * dist x y := by
      rw [← dist_eq_norm]
      exact hLDu.dist_le_mul x hx y hy

/-- The lower-order part `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu` of the Hessian entry `∂ᵢ∂ⱼ(ζ u)`
vanishes off `s`, and is globally Hölder and bounded, when the first and second derivatives of `ζ`
are globally Hölder and bounded with constant `Z` and `ζ` is supported in `s`, while `u` and its
first derivatives are bounded by `N` and Hölder with constant `H` on `s`. -/
private theorem holderWith_cutoff_remainder {s : Set E} {ζ u : E → ℝ} {α Z N H : ℝ≥0}
    (hζs : tsupport ζ ⊆ s)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hN0 : ∀ x ∈ s, |u x| ≤ N) (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    (i j : Fin (n + 1)) :
    HolderWith (3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) ∧
    (∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
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
  obtain ⟨h1, b1⟩ := holderWith_mul_and_abs_le (hZ2 i j).1 (hZ2 i j).2 hζ''0 hH0 hN0
  obtain ⟨h2, b2⟩ := holderWith_mul_and_abs_le (hZ1 i).1 (hZ1 i).2 (hζ'0 i) (hH1 j) (hN1 j)
  obtain ⟨h3, b3⟩ := holderWith_mul_and_abs_le (hZ1 j).1 (hZ1 j).2 (hζ'0 j) (hH1 i) (hN1 i)
  refine ⟨((h1.add h2).add h3).mono (le_of_eq (by ring)), fun x => ?_, fun x hx => ?_⟩
  · refine (abs_add_three _ _ _).trans ((add_le_add_three (b1 x) (b2 x) (b3 x)).trans_eq ?_)
    ring
  · simp only [hζ''0 x hx, hζ'0 i x hx, hζ'0 j x hx, zero_mul, add_zero]

/-- The Hessian entries `∂ᵢ∂ⱼ(ζ u) = ζ ∂ᵢ∂ⱼu + Tᵢⱼ` of a cutoff product are globally Hölder and
bounded, when `ζ` is supported in the open set `s` and `ζ` and its first and second derivatives
are globally Hölder and bounded with constant `Z`, while `u` is `C²` on `s`, with `u` and its first
and second derivatives bounded by `N` there, and Hölder with constants `H`, `H` and `V`. -/
private theorem holderWith_fderiv_fderiv_cutoff_mul {s : Set E} (hs : IsOpen s) {ζ u : E → ℝ}
    {α Z N H V : ℝ≥0} (hζ : ContDiffOn ℝ 2 ζ s) (hζs : tsupport ζ ⊆ s)
    (hZ0 : HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hu : ContDiffOn ℝ 2 u s) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    (hV : ∀ i j, HolderOnWith V α (fun x =>
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s)
    (i j : Fin (n + 1)) :
    HolderWith (Z * V + N * Z + 3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
    ∀ x, |fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
      4 * Z * N := by
  obtain ⟨hT, bT, -⟩ := holderWith_cutoff_remainder hζs hZ1 hZ2 hN0 hN1 hH0 hH1 i j
  obtain ⟨h1, b1⟩ := holderWith_mul_and_abs_le hZ0.1 hZ0.2
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hζs h)) (hV i j) (hN2 i j)
  have hW (x : E) :
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        ζ x * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
          fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
          fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) := by
    rw [fderiv_fderiv_mul_apply_of_tsupport_subset hs hζ hζs hu]
    ring
  simp only [hW]
  refine ⟨h1.add hT, fun x => (abs_add_le _ _).trans ?_⟩
  calc _ ≤ (Z * N : ℝ) + 3 * Z * N := add_le_add (b1 x) (bT x)
    _ = _ := by ring

/-- For a cutoff product `ζ u` as in `holderWith_fderiv_fderiv_cutoff_mul`, the operator
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` is globally Hölder, when the coefficients
are bounded by `M` and Hölder with constant `L` on `s`, and `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` is Hölder with
constant `K` on `s`. The Hessian of `u` need not be Hölder. -/
private theorem holderWith_sum_smul_fderiv_fderiv_cutoff_mul {s : Set E} (hs : IsOpen s)
    {ζ u : E → ℝ} {α Z N H : ℝ≥0} (hζ : ContDiffOn ℝ 2 ζ s) (hζs : tsupport ζ ⊆ s)
    (hZ0 : HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hu : ContDiffOn ℝ 2 u s) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {L M K : ℝ≥0}
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) s) (hM : ∀ x ∈ s, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s) :
    HolderWith (Z * K + (n + 1) ^ 2 * (M * N * Z + (3 * Z * N * L + M * (3 * (Z * H + N * Z)))))
      α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ (ζ * u)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  set f : E → ℝ := fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hfM (x : E) (hx : x ∈ s) : |f x| ≤ ((n + 1) ^ 2 * M * N : ℝ≥0) := by
    calc |f x| ≤ ∑ i, ∑ j, |a x i j • fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), (M * N : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [smul_eq_mul, abs_mul]
          exact mul_le_mul (hM x hx i j) (hN2 i j x hx) (abs_nonneg _) M.coe_nonneg
      _ = _ := by simp; ring
  have heq : (fun x => ∑ i, ∑ j, a x i j •
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      fun x => ζ x * f x + ∑ i, ∑ j,
        (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
          fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
          fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) *
        a x i j := by
    funext x
    simp only [fderiv_fderiv_mul_apply_of_tsupport_subset hs hζ hζs hu, smul_eq_mul, f,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨h1, -⟩ := holderWith_mul_and_abs_le hZ0.1 hZ0.2
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hζs h)) hK hfM
  have h2 (i j : Fin (n + 1)) := by
    obtain ⟨hT, bT, hT0⟩ := holderWith_cutoff_remainder hζs hZ1 hZ2 hN0 hN1 hH0 hH1 i j
    exact (holderWith_mul_and_abs_le hT (Mc := 3 * Z * N) (by exact_mod_cast bT) hT0 (hL i j)
      fun x hx => hM x hx i j).1
  rw [heq]
  refine (h1.add (HolderWith.sum fun i _ => HolderWith.sum fun j _ => h2 i j)).mono
    (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The comparison of constants closing the interior estimate: if `X ≤ A N`, then
`2 κ ((Z K + N B) / λ + Q X) ≤ 2 κ (Z / λ + B / λ + Q A) (K + N)`. -/
private theorem interior_constant_le {κ lam Z B Q A K N X : ℝ} (hκ : 0 ≤ κ) (hlam : 0 < lam)
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (hX : X ≤ A * N) :
    2 * κ * ((Z * K + N * B) / lam + Q * X) ≤ 2 * κ * (Z / lam + B / lam + Q * A) * (K + N) := by
  have hdiv : (Z * K + N * B) / lam = Z / lam * K + B / lam * N := by ring
  calc 2 * κ * ((Z * K + N * B) / lam + Q * X)
      ≤ 2 * κ * (Z / lam * K + B / lam * N + Q * A * N) := by
        rw [hdiv, mul_assoc Q A]
        gcongr
    _ ≤ 2 * κ * (Z / lam + B / lam + Q * A) * (K + N) := by
        rw [mul_assoc (2 * κ)]
        gcongr
        have : 0 ≤ Z / lam := by positivity
        have : 0 ≤ B / lam := by positivity
        have : 0 ≤ Q * A := mul_nonneg hQ hA
        nlinarith

/-- **The interior Schauder estimate on small balls.** Let `0 < α < 1`. There is `C₀ > 0`,
depending only on dimension and `α`, with the following property. Let `a` be `α`-Hölder entrywise
with constant `L` on the closed ball `closedBall x₀ R`, where `R > 0`, and suppose `a x₀` has
ellipticity bounds `λ, Λ`, with `λ > 0`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu` and
`κ = C₀ (Λ / λ)^(1 + (n+1)/4 + α/2)`, and assume the scale condition

`2 κ (n+1)² (1 + 2ᵅ) L Rᵅ ≤ λ`.

Then for every `ρ < R` there is `C`, independent of `u`, with the following property. Let `u` be
`C²` on the open ball `B_R`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` there and with `D²u`
`α`-Hölder on `B_R` (with any constant). If `L u` is `α`-Hölder on `B_R` with constant `K`, then
`D²u` is `α`-Hölder on `closedBall x₀ ρ` with constant `C (K + N)`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E} {lam Lam : ℝ},
      0 < lam → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {L : ℝ≥0} {R : ℝ}, 0 < R →
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R)) →
      ∀ {ρ : ℝ}, ρ < R → ∃ C : ℝ≥0,
      ∀ {u : E → ℝ} {N K V : ℝ≥0}, ContDiffOn ℝ 2 u (ball x₀ R) →
        (∀ x ∈ ball x₀ R, |u x| ≤ N) → (∀ x ∈ ball x₀ R, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R) →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x₀ ρ) := by
  obtain ⟨C₀, hC₀, hCS⟩ :=
    exists_holderWith_iteratedFDeriv_two_of_support_subset_closedBall hα hα1 (n := n)
  refine ⟨C₀, hC₀, fun {a x₀ lam Lam} hlam hEll hEll' {L R} hR hsmall hL {ρ} hρR => ?_⟩
  -- The cutoff `ζ`, equal to one near `closedBall x₀ ρ` and supported in `B_R`, and its
  -- constant `Z`.
  obtain ⟨ζ, hζ, -, hζ1, hζc, hζs⟩ :=
    (isCompact_closedBall x₀ ρ).exists_contDiff_cutoff isOpen_ball (closedBall_subset_ball hρR)
  obtain ⟨Z, hZ0, hZ1, hZ2⟩ := exists_holderWith_and_abs_le_of_hasCompactSupport hα1.le hζ hζc
  have hζ2 : ContDiffOn ℝ 2 ζ (ball x₀ R) := (hζ.of_le (by norm_cast)).contDiffOn
  -- A bound `M` for the coefficients on `closedBall x₀ R`.
  choose Ma hMa using fun i j => (isCompact_closedBall x₀ R).exists_bound_of_continuousOn
    ((hL i j).continuousOn hα)
  set M : ℝ≥0 := ∑ i, ∑ j, (Ma i j).toNNReal
  have hM (x : E) (hx : x ∈ closedBall x₀ R) (i j : Fin (n + 1)) : |a x i j| ≤ M := by
    calc |a x i j| ≤ Ma i j := by simpa only [Real.norm_eq_abs] using hMa i j x hx
      _ ≤ (Ma i j).toNNReal := Real.le_coe_toNNReal _
      _ ≤ M := by
        exact_mod_cast (Finset.single_le_sum (f := fun j => (Ma i j).toNNReal)
          (fun _ _ => zero_le) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, (Ma i j).toNNReal) (fun _ _ => zero_le)
            (Finset.mem_univ i))
  -- The constants of the estimate, which do not depend on `u`.
  set δ : ℝ≥0 := (2 * R).toNNReal ^ ((1 : ℝ) - α)
  set κ : ℝ := C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  set Q : ℝ := ((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
      (volume (ball (0 : E) R) ^ (-((2 : ℝ)⁻¹))).toReal + R ^ (-(((n : ℝ) + 1) / 2 + α))
  set B₂ : ℝ≥0 := (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))
  set A₃ : ℝ := (volume (closedBall x₀ R)).toReal ^ (2⁻¹ : ℝ) * (((n : ℝ) + 1) ^ 2 * (4 * Z))
  refine ⟨(2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal,
    fun {u N K V} hu hN0 hN1 hN2 hV hK => ?_⟩
  -- Bounds and Hölder constants of `u` and its derivatives on `B_R`.
  have hsR : ball x₀ R ⊆ closedBall x₀ R := ball_subset_closedBall
  obtain ⟨hHu, hHdu⟩ := holderOnWith_ball_of_norm_le hα1.le hu hN1 hN2
  have hdu (i : Fin (n + 1)) (x : E) (hx : x ∈ ball x₀ R) :
      |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N := by
    simpa using ((fderiv ℝ u x).unit_le_opNorm (EuclideanSpace.single i 1) (by simp)).trans
      (hN1 x hx)
  have hd2u (i j : Fin (n + 1)) (x : E) (hx : x ∈ ball x₀ R) :
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N := by
    simpa [iteratedFDeriv_two_apply] using ((iteratedFDeriv ℝ 2 u x).norm_apply_orthonormalBasis_le
      (EuclideanSpace.basisFun _ ℝ) i j).trans (hN2 x hx)
  -- The cutoff product `w = ζ u`: Hölder bounds for its Hessian and for the operator applied to it.
  set w : E → ℝ := ζ * u
  have hw : ContDiff ℝ 2 w := hu.contDiff_smul_of_tsupport_subset isOpen_ball hζ2 hζs
  have hWH := holderWith_fderiv_fderiv_cutoff_mul isOpen_ball hζ2 hζs hZ0 hZ1 hZ2 hu hN0 hdu hd2u
    hHu hHdu fun i j => by
      simpa [iteratedFDeriv_two_apply] using
        hV.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j
  have hLw : HolderWith (Z * K + N * B₂) α (fun x => ∑ i, ∑ j, a x i j •
      fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) :=
    (holderWith_sum_smul_fderiv_fderiv_cutoff_mul isOpen_ball hζ2 hζs hZ0 hZ1 hZ2 hu hN0 hdu hd2u
      hHu hHdu (fun i j => (hL i j).mono hsR) (fun x hx => hM x (hsR hx)) hK).mono
      (le_of_eq (by simp only [B₂, δ]; ring))
  -- The compact-support estimate for `w`.
  have hsupp : Function.support (iteratedFDeriv ℝ 2 w) ⊆ closedBall x₀ R :=
    (support_iteratedFDeriv_subset 2).trans (tsupport_mul_subset_left.trans (hζs.trans hsR))
  have hsmall' : 2 * κ * ((n : ℝ) + 1) ^ 2 *
      (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * R ^ (α : ℝ)) ≤ lam := by
    convert hsmall using 2
    ring
  have key := hCS hlam hEll hEll' (L := L) (K := Z * K + N * B₂) (r := R) hR.le hR hsmall' hL hw
    (holderOnWith_univ.1 (.of_apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) fun i j =>
      by simpa [iteratedFDeriv_two_apply] using holderOnWith_univ.2 (hWH i j).1)).memHolder hsupp
    hLw
  -- The `L²` norm of `D²w`.
  have hnorm (x : E) : ‖iteratedFDeriv ℝ 2 w x‖ ≤ ((n : ℝ) + 1) ^ 2 * (4 * Z * N) := by
    refine ((iteratedFDeriv ℝ 2 w x).opNorm_le_card_sq_mul_of_norm_apply_le
      (EuclideanSpace.basisFun _ ℝ) (B := 4 * Z * N) fun i j => ?_).trans_eq (by simp)
    simpa [iteratedFDeriv_two_apply, w] using (hWH i j).2 x
  have hL2 : (eLpNorm (iteratedFDeriv ℝ 2 w) 2 volume).toReal ≤ A₃ * N := by
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
      measure_closedBall_lt_top.ne) ENNReal.ofReal_ne_top) (eLpNorm_le_of_ae_bound_of_support_subset
      (hw.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable hsupp (ae_of_all _ hnorm))).trans
      (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity)]
    simp only [A₃, ENNReal.toReal_ofNat]
    ring
  -- Comparison of the constants.
  have hlamLam : lam ≤ Lam := by
    have h := (hEll (EuclideanSpace.single 0 1)).trans (hEll' (EuclideanSpace.single 0 1))
    simpa using h
  have hκ : 0 ≤ κ := mul_nonneg hC₀.le
    (Real.rpow_nonneg (div_nonneg (hlam.le.trans hlamLam) hlam.le) _)
  have hQ : 0 ≤ Q := by positivity
  have hA₃ : 0 ≤ A₃ := by positivity
  have hbound : 2 * κ * (((Z * K + N * B₂ : ℝ≥0) : ℝ) / lam +
      Q * (eLpNorm (iteratedFDeriv ℝ 2 w) 2 volume).toReal) ≤
      ((2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal * (K + N) : ℝ≥0) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    push_cast
    exact interior_constant_le hκ hlam Z.coe_nonneg B₂.coe_nonneg hQ hA₃ K.coe_nonneg N.coe_nonneg
      hL2
  -- On a neighbourhood of `closedBall x₀ ρ` the cutoff is one, so `D²w = D²u` there.
  have hwu (x : E) (hx : x ∈ closedBall x₀ ρ) :
      iteratedFDeriv ℝ 2 w x = iteratedFDeriv ℝ 2 u x := by
    have hev : w =ᶠ[𝓝 x] u := by
      filter_upwards [mem_interior_iff_mem_nhds.1 (hζ1 hx)] with y hy
      simp only [w, Pi.mul_apply, show ζ y = 1 from hy, one_mul]
    exact (hev.iteratedFDeriv ℝ 2).eq_of_nhds
  intro x hx y hy
  rw [← hwu x hx, ← hwu y hy]
  refine (key x y).trans ?_
  gcongr
  exact Real.toNNReal_le_iff_le_coe.2 hbound

end TauCeti.PDE
