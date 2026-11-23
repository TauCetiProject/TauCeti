/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
import TauCeti.Analysis.Holder.Interpolation
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# The global Schauder estimate on the whole space

Let `0 < α < 1`, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a non-divergence-form operator on `ℝ^{n+1}`
whose coefficients are uniformly elliptic and bounded with constants `0 < λ ≤ Λ` on the whole
space (`TauCeti.PDE.UniformlyEllipticOn univ a λ Λ`) and globally `α`-Hölder with constant `L`.
This file proves the global Schauder estimate on the whole space: there is a constant `C`,
depending only on `n`, `α`, `λ`, `Λ` and `L`, such that every bounded `C²` function `u` with
globally `α`-Hölder Hessian satisfies

`‖Du‖_∞ + ‖D²u‖_∞ + [D²u]_α ≤ C ([L u]_α + ‖u‖_∞)`,

where `[·]_α` is the global `α`-Hölder constant
(`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv`), or in
terms of the norm of the bounded space `C_b^{2,α}(ℝ^{n+1})`,
`‖u‖_{C^{2,α}} ≤ C ([L u]_α + ‖u‖_∞)` (`TauCeti.PDE.exists_norm_le_of_sum_smul_fderiv_fderiv`).
The Hölder constant of the Hessian enters only qualitatively: the estimate does not depend on it.
Unlike the interior estimate on compact sets
(`PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderOnWith`),
the constant is uniform over the whole space, and only `‖u‖_∞` remains among the lower-order
terms.

## The argument

The interior estimate on small balls
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`) has a
constant that depends on the coefficients only through `λ`, `Λ`, `L` and a bound for their
entries, which uniform ellipticity bounds by `Λ`
(`TauCeti.PDE.UniformlyEllipticOn.abs_apply_le`). The global bounds therefore give one radius `R`,
satisfying the scale condition, with `R ≤ 1`, and one constant `C₁` for balls of radius `R` about
every point. Two points at distance less than `R / 2` lie in the half ball about one of them, where
the interior estimate is applied to `u` minus its first-order Taylor polynomial at the centre: this
has the same second derivatives, and by the mean value inequality it and its gradient are bounded
on the ball by the bound `N` of `‖D²u‖`, since `R ≤ 1`. At larger distances
`‖D²u(x) - D²u(y)‖ ≤ 2N ≤ 2N (R / 2)^(-α) ‖x - y‖^α`
(`HolderOnWith.of_dist_lt_of_dist_le`). This is the first estimate,
`[D²u]_α ≤ C (K + N)`
(`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith`), where
`K` is the Hölder constant of `L u`.

The bound of `‖D²u‖_∞` on the right side is then removed by interpolation. The inequalities
`‖D²u‖_∞ ≤ 32 ε⁻² ‖u‖_∞ + 2 ε^α [D²u]_α` and `‖Du‖_∞ ≤ 34 ε⁻¹ ‖u‖_∞ + 2 ε^(1+α) [D²u]_α`
(`HolderWith.norm_iteratedFDeriv_add_two_le_of_norm_le`,
`HolderWith.norm_iteratedFDeriv_succ_le_of_contDiff_of_norm_le`) give, for `ε ≤ 1`, the common bound
`(34 ε⁻¹ + 32 ε⁻²) ‖u‖_∞ + 2 ε^α [D²u]_α` of both
(`HolderWith.norm_fderiv_le_and_norm_iteratedFDeriv_two_le`); it bounds `‖D²u‖_∞` in the first
estimate and is also the bound on `‖Du‖_∞` in the conclusion. The finiteness of `‖D²u‖_∞` that
these inequalities need follows from `|u| ≤ N` and the Hölder bound
(`HolderWith.bddAbove_norm_iteratedFDeriv_add_two`). Taking for `[D²u]_α` the Hölder norm
`nnHolderNorm`, which is finite, and `ε` so small that `2 C ε^α ≤ 1 / 2`, the resulting multiple of
`[D²u]_α` is absorbed into the left side.

## Main declarations

* `TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith`: the
  global Hölder bound for the Hessian in terms of `[L u]_α` and a bound on `D²u`.
* `TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv`: the
  global Schauder estimate in terms of `[L u]_α` and `‖u‖_∞` alone.
* `TauCeti.PDE.exists_norm_le_of_sum_smul_fderiv_fderiv`: the same estimate for the norm of
  `CkHolderSpace 2 α`.

## References

* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, Graduate Studies
  in Mathematics 12, AMS, 1996 (a priori estimates in the whole space for equations with variable
  Hölder coefficients).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, Theorem 6.2 and Lemma 6.32 (interior estimates and interpolation).
-/

public section

noncomputable section

open Metric Set Filter Topology
open scoped NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The interior estimate on a small ball from a bound on `D²u` alone.** Let `C₁` be a constant
for the interior estimate for `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` from `ball x₀ R` to `closedBall x₀ ρ`, stated
with a common bound on `|u|`, `‖Du‖` and `‖D²u‖` on the ball. If `R ≤ 1` and `u` is globally `C²`
(`ContDiff ℝ 2 u`), the same estimate holds with `N` bounding `‖D²u‖` alone on the ball. -/
private theorem holderOnWith_iteratedFDeriv_two_closedBall_of_norm_iteratedFDeriv_two_le
    {α C₁ : ℝ≥0} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E} {R ρ : ℝ} (hR1 : R ≤ 1)
    (hC₁ : ∀ {u : E → ℝ} {N K V : ℝ≥0}, ContDiffOn ℝ 2 u (ball x₀ R) →
      (∀ x ∈ ball x₀ R, |u x| ≤ N) → (∀ x ∈ ball x₀ R, ‖fderiv ℝ u x‖ ≤ N) →
      (∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
      HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R) →
      HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R) →
      HolderOnWith (C₁ * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x₀ ρ))
    {u : E → ℝ} {N K V : ℝ≥0} (hu : ContDiff ℝ 2 u)
    (hN : ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N)
    (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R))
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R)) :
    HolderOnWith (C₁ * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x₀ ρ) := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  -- On the ball, `‖Du(x) - Du(x₀)‖ ≤ N ‖x - x₀‖ ≤ N`.
  have hRN : ∀ x ∈ ball x₀ R, (N : ℝ) * ‖x - x₀‖ ≤ N := fun x hx =>
    mul_le_of_le_one_right N.coe_nonneg ((mem_ball_iff_norm.1 hx).le.trans hR1)
  have hDuN : ∀ x ∈ ball x₀ R, ‖fderiv ℝ u x - fderiv ℝ u x₀‖ ≤ N := fun x hx =>
    ((convex_ball x₀ R).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hu.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero y) (fun y hy => by
        rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]; exact hN y hy)
      (mem_ball_self (pos_of_mem_ball hx)) hx).trans (hRN x hx)
  -- `v = u - u(x₀) - Du(x₀)(· - x₀)`, with `Dv = Du - Du(x₀)` and the second derivatives of `u`.
  set v : E → ℝ := fun x => u x - fderiv ℝ u x₀ x + (fderiv ℝ u x₀ x₀ - u x₀)
  have hDv : fderiv ℝ v = fun x => fderiv ℝ u x - fderiv ℝ u x₀ := by
    funext x
    rw [fderiv_add_const, fderiv_fun_sub (hu1 x) (fderiv ℝ u x₀).differentiableAt,
      ContinuousLinearMap.fderiv]
  have hD2v : fderiv ℝ (fderiv ℝ v) = fderiv ℝ (fderiv ℝ u) := by
    funext x
    rw [hDv, fderiv_sub_const]
  have hv2 : iteratedFDeriv ℝ 2 v = iteratedFDeriv ℝ 2 u := by
    funext x
    apply (continuousMultilinearCurryFin2 ℝ E ℝ).injective
    rw [continuousMultilinearCurryFin2_iteratedFDeriv_two,
      continuousMultilinearCurryFin2_iteratedFDeriv_two, hD2v]
  have hv0 : ∀ x ∈ ball x₀ R, |v x| ≤ N := fun x hx => by
    rw [← Real.norm_eq_abs]
    convert ((convex_ball x₀ R).norm_image_sub_le_of_norm_fderiv_le' (fun y _ => hu1 y) hDuN
      (mem_ball_self (pos_of_mem_ball hx)) hx).trans (hRN x hx) using 2
    simp only [v, map_sub]
    ring
  rw [← hv2]
  exact hC₁ ((hu.sub (fderiv ℝ u x₀).contDiff).add contDiff_const).contDiffOn hv0
    (fun x hx => by rw [hDv]; exact hDuN x hx) (fun x hx => by rw [hv2]; exact hN x hx)
    (by rwa [hv2]) (by rwa [hD2v])

/-- **The global Schauder estimate with a Hessian bound.** Let `α < 1`, and let `λ`, `Λ`
and `L` be given. Then there is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `L`, with
the following property. Let `a` be a matrix-valued coefficient on `ℝ^{n+1}` which is uniformly
elliptic and bounded with constants `0 < λ ≤ Λ` (`UniformlyEllipticOn univ a λ Λ`) and globally
`α`-Hölder entrywise with constant `L`, and put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. Let `u` be `C²`, with
`‖D²u‖` bounded by `N` and with `D²u` `α`-Hölder on every compact set (with any constants). If
`L u` is globally `α`-Hölder with constant `K`, then `D²u` is globally `α`-Hölder with constant
`C (K + N)`. No bound on `u` or `Du` is needed, since subtracting an affine function changes
neither `D²u` nor `L u`. -/
theorem exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith
    {α : ℝ≥0} (hα1 : α < 1) (lam Lam : ℝ) (L : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      UniformlyEllipticOn univ a lam Lam → (∀ i j, HolderWith L α (fun x => a x i j)) →
      ∀ {u : E → ℝ} {N K : ℝ≥0}, ContDiff ℝ 2 u → (∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
      (∀ S, IsCompact S → ∃ V : ℝ≥0, HolderOnWith V α (iteratedFDeriv ℝ 2 u) S) →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      HolderWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) := by
  -- For `α = 0` the Hölder condition is the bound `‖D²u‖ ≤ N`.
  rcases eq_or_ne α 0 with rfl | hα0
  · refine ⟨2, fun {a} _ _ {u N K} _ hN _ _ => holderWith_zero_of_nnnorm_le fun x => ?_⟩
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_add]
    exact (hN x).trans (le_add_of_nonneg_left K.coe_nonneg)
  have hα : 0 < α := pos_iff_ne_zero.2 hα0
  -- Without `0 < λ` no coefficient field is uniformly elliptic.
  rcases le_or_gt lam 0 with hlam | hlam
  · exact ⟨0, fun hA => absurd hA.pos (not_lt.2 hlam)⟩
  obtain ⟨C₀, -, hball⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  -- One radius `R` satisfying the scale condition, and one constant `C₁` for every centre.
  obtain ⟨R, hR, hR1, hscale⟩ := Real.exists_pos_le_one_mul_rpow_le
    (2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
      ((1 + 2 ^ (α : ℝ)) * L)) (NNReal.coe_pos.2 hα) hlam
  obtain ⟨C₁, hC₁⟩ := hball (L := L) (M := Lam.toNNReal) hlam
    (by simpa only [mul_assoc] using hscale) (half_lt_self hR)
  set δ : ℝ≥0 := ⟨R / 2, by positivity⟩
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; exact half_pos hR
  refine ⟨C₁ + 2 * δ ^ (-(α : ℝ)), fun {a} hA hL {u N K} hu hN₂ hV hK => ?_⟩
  -- Points at distance less than `R / 2` lie in the half ball about the first of them.
  have hloc : ∀ x ∈ univ, ∀ y ∈ univ, dist x y < δ → dist (iteratedFDeriv ℝ 2 u x)
      (iteratedFDeriv ℝ 2 u y) ≤ (C₁ * (K + N) : ℝ≥0) * dist x y ^ (α : ℝ) := by
    intro x _ y _ hxy
    obtain ⟨V, hV'⟩ := hV _ (isCompact_closedBall x R)
    have key := holderOnWith_iteratedFDeriv_two_closedBall_of_norm_iteratedFDeriv_two_le hR1
      (hC₁ (hA.lower_bound (mem_univ x)) (hA.toQuadraticForm'_le (mem_univ x))
        (fun i j => (hL i j).holderOnWith _)
        (fun z _ i j => (hA.abs_apply_le (mem_univ z) i j).trans (Real.le_coe_toNNReal _)))
      hu (fun z _ => hN₂ z) (hV'.mono ball_subset_closedBall) (hK.holderOnWith _)
    exact key.dist_le (mem_closedBall_self (by positivity))
      (by rw [mem_closedBall, dist_comm]; exact hxy.le)
  -- Points at larger distance are handled by the bound `‖D²u‖ ≤ N`.
  have hD : ∀ x ∈ univ, ∀ y ∈ univ,
      dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤ ((2 * N : ℝ≥0) : ℝ) := by
    intro x _ y _
    refine (dist_le_norm_add_norm _ _).trans ?_
    push_cast
    linarith [hN₂ x, hN₂ y]
  refine holderOnWith_univ.1 ((HolderOnWith.of_dist_lt_of_dist_le hδ hloc hD).mono_const ?_)
  calc C₁ * (K + N) + 2 * N * δ ^ (-(α : ℝ))
      ≤ C₁ * (K + N) + 2 * δ ^ (-(α : ℝ)) * (K + N) := by
        rw [mul_right_comm]
        gcongr
        exact le_add_self
    _ = (C₁ + 2 * δ ^ (-(α : ℝ))) * (K + N) := by ring

/-- **The global Schauder estimate on the whole space.** Let `0 < α < 1`, and let `λ`, `Λ` and
`L` be given. Then there is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `L`, with the
following property. Let `a` be a matrix-valued coefficient on `ℝ^{n+1}` which is uniformly
elliptic and bounded with constants `0 < λ ≤ Λ` (`UniformlyEllipticOn univ a λ Λ`) and globally
`α`-Hölder entrywise with constant `L`, and put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. Let `u` be `C²` with
`|u| ≤ N`, and with `D²u` globally `α`-Hölder (with any constant). If `L u` is globally
`α`-Hölder with constant `K`, then `D²u` is globally `α`-Hölder with constant `C (K + N)`, and
`‖Du‖` and `‖D²u‖` are bounded by `C (K + N)`. -/
theorem exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) (L : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      UniformlyEllipticOn univ a lam Lam → (∀ i j, HolderWith L α (fun x => a x i j)) →
      ∀ {u : E → ℝ} {N K : ℝ≥0}, ContDiff ℝ 2 u → (∀ x, |u x| ≤ N) →
      MemHolder α (iteratedFDeriv ℝ 2 u) →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      HolderWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) ∧
        (∀ x, ‖fderiv ℝ u x‖ ≤ C * (K + N)) ∧ ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ C * (K + N) := by
  obtain ⟨C₁, hC₁⟩ :=
    exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith hα1 lam Lam L
  -- The interpolation scale `ε`, small enough to absorb the Hölder norm of `D²u`.
  obtain ⟨ε, hε, hε1, hεC⟩ :=
    Real.exists_pos_le_one_mul_rpow_le (2 * C₁) (NNReal.coe_pos.2 hα)
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hεα : ε ^ (α : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1 α.coe_nonneg
  set c : ℝ := 34 / ε + 32 / ε ^ 2
  have hc : 0 ≤ c := by positivity
  set A : ℝ := 2 * C₁ * (1 + c)
  refine ⟨(3 * A + c).toNNReal, fun {a} hEll hL {u N K} hu hN hmem hK => ?_⟩
  -- The Hölder norm `H` of `D²u` and the interpolation inequalities at scale `ε`.
  set H := nnHolderNorm α (iteratedFDeriv ℝ 2 u)
  have hH : HolderWith H α (iteratedFDeriv ℝ 2 u) := hmem.holderWith
  obtain ⟨h1, h2⟩ := hH.norm_fderiv_le_and_norm_iteratedFDeriv_two_le hu
    (fun y => by simpa only [Real.norm_eq_abs] using hN y) hε hε1
  -- The first estimate with the bound `N₁ = c N + 2 H ε^α` of `‖D²u‖`.
  have hHε : 0 ≤ (H : ℝ) * ε ^ (α : ℝ) := by positivity
  have hcN : 0 ≤ c * N := by positivity
  set N₁ : ℝ := c * N + 2 * H * ε ^ (α : ℝ)
  have hN₁ : 0 ≤ N₁ := by positivity
  have hHN : H ≤ C₁ * (K + N₁.toNNReal) :=
    (hC₁ hEll hL hu (fun x => (h2 x).trans (Real.le_coe_toNNReal _))
      (fun S _ => ⟨H, hH.holderOnWith S⟩) hK).nnholderNorm_le
  -- Absorption: `H ≤ C₁ (K + c N) + 2 C₁ ε^α H` and `2 C₁ ε^α ≤ 1 / 2`.
  have hHA : (H : ℝ) ≤ A * (K + N) := by
    have h : (H : ℝ) ≤ C₁ * (K + N₁) := by
      have : (H : ℝ) ≤ ((C₁ * (K + N₁.toNNReal) : ℝ≥0) : ℝ) := by exact_mod_cast hHN
      rwa [NNReal.coe_mul, NNReal.coe_add, Real.coe_toNNReal _ hN₁] at this
    have habs : 2 * C₁ * ε ^ (α : ℝ) * H ≤ 1 / 2 * H :=
      mul_le_mul_of_nonneg_right hεC H.coe_nonneg
    have hC₁N : 0 ≤ (C₁ : ℝ) * N := by positivity
    have hC₁cK : 0 ≤ (C₁ : ℝ) * c * K := by positivity
    simp only [A] at h ⊢
    nlinarith
  have hKN : 0 ≤ (K : ℝ) + N := by positivity
  have hC : (3 * A + c) * (K + N) ≤ ((3 * A + c).toNNReal : ℝ) * (K + N) :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) hKN
  have hHε' : (H : ℝ) * ε ^ (α : ℝ) ≤ H := mul_le_of_le_one_right H.coe_nonneg hεα
  have hcK : 0 ≤ c * K := mul_nonneg hc K.coe_nonneg
  refine ⟨hH.mono ?_, fun x => (h1 x).trans ?_, fun x => (h2 x).trans ?_⟩
  · rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith
  · nlinarith
  · nlinarith

/-- **The global Schauder estimate in the `C_b^{2,α}` norm.** Let `0 < α < 1`, and let `λ`, `Λ`
and `L` be given. Then there is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `L`, with
the following property. Let `a` be a matrix-valued coefficient on `ℝ^{n+1}` which is uniformly
elliptic and bounded with constants `0 < λ ≤ Λ` (`UniformlyEllipticOn univ a λ Λ`) and globally
`α`-Hölder entrywise with constant `L`, and put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. Then every
`u ∈ C_b^{2,α}(ℝ^{n+1})` with `|u| ≤ N`, for which `L u` is globally `α`-Hölder with constant `K`,
satisfies `‖u‖_{C^{2,α}} ≤ C (K + N)`. -/
theorem exists_norm_le_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) (L : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      UniformlyEllipticOn univ a lam Lam → (∀ i j, HolderWith L α (fun x => a x i j)) →
      ∀ (u : CkHolderSpace 2 α E ℝ) {N K : ℝ≥0}, (∀ x, |u x| ≤ N) →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      ‖u‖ ≤ C * (K + N) := by
  obtain ⟨C, hC⟩ :=
    exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv hα hα1 lam Lam L
  refine ⟨3 * C + 1, fun {a} hA hL u N K hN hK => ?_⟩
  obtain ⟨hH, h1, h2⟩ := hC hA hL u.contDiff hN u.memHolder_iteratedFDeriv hK
  have hKN : (N : ℝ) ≤ K + N := le_add_of_nonneg_left K.coe_nonneg
  have hCKN : 0 ≤ (C : ℝ) * (K + N) := by positivity
  have b0 : ‖u.iteratedFDeriv 0‖ ≤ N := (BoundedContinuousFunction.norm_le N.coe_nonneg).2
    fun x => by
      rw [← CkHolderSpace.iteratedFDeriv_eq, Fin.val_zero, norm_iteratedFDeriv_zero]
      exact hN x
  have b1 : ‖u.iteratedFDeriv 1‖ ≤ C * (K + N) := (BoundedContinuousFunction.norm_le hCKN).2
    fun x => by
      rw [← CkHolderSpace.iteratedFDeriv_eq, Fin.val_one, norm_iteratedFDeriv_one]
      exact h1 x
  have b2 : ‖u.iteratedFDeriv 2‖ ≤ C * (K + N) := (BoundedContinuousFunction.norm_le hCKN).2
    fun x => by
      rw [← CkHolderSpace.iteratedFDeriv_eq, Fin.val_two]
      exact h2 x
  have b3 : (nnHolderNorm α (iteratedFDeriv ℝ 2 u) : ℝ) ≤ C * (K + N) := by
    exact_mod_cast hH.nnholderNorm_le
  rw [CkHolderSpace.norm_eq, Fin.sum_univ_three]
  push_cast
  linarith

end TauCeti.PDE
