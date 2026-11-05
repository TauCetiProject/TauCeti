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
depending only on `n`, `α`, `λ`, `Λ` and `L`, such that every `C²` function `u` with bounded,
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
satisfying the scale condition, and one constant `C₁` for balls of radius `R` about every point.
Two points at distance less than `R / 2` lie in the half ball about one of them, while at larger
distances
`‖D²u(x) - D²u(y)‖ ≤ 2N ≤ 2N (R / 2)^(-α) ‖x - y‖^α`
(`HolderOnWith.of_dist_lt_of_dist_le`), where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖`. This is the
first estimate,
`[D²u]_α ≤ C (K + N)`
(`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith`), where
`K` is the Hölder constant of `L u`.

The first and second derivatives are then removed from the right side by the interpolation
inequalities `‖D²u‖_∞ ≤ 32 ε⁻² ‖u‖_∞ + 2 ε^α [D²u]_α` and
`‖Du‖_∞ ≤ 34 ε⁻¹ ‖u‖_∞ + 2 ε^(1+α) [D²u]_α`
(`HolderWith.norm_iteratedFDeriv_add_two_le_of_norm_le`,
`HolderWith.norm_iteratedFDeriv_succ_le_of_norm_le_of_bddAbove`). Taking for `[D²u]_α` the Hölder
norm `nnHolderNorm`, which is finite, and `ε` so small that `4 C ε^α ≤ 1 / 2`, the resulting
multiple of `[D²u]_α` is absorbed into the left side.

## Main declarations

* `TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith`: the
  global Hölder bound for the Hessian in terms of `[L u]_α` and bounds on `u`, `Du` and `D²u`.
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

/-- **The global Schauder estimate with lower-order bounds.** Let `0 < α < 1`, and let `λ`, `Λ`
and `L` be given. Then there is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `L`, with
the following property. Let `a` be a matrix-valued coefficient on `ℝ^{n+1}` which is uniformly
elliptic and bounded with constants `0 < λ ≤ Λ` (`UniformlyEllipticOn univ a λ Λ`) and globally
`α`-Hölder entrywise with constant `L`, and put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. Let `u` be `C²`, with `|u|`,
`‖Du‖` and `‖D²u‖` bounded by `N` and with `D²u` `α`-Hölder on every compact set (with any
constants). If `L u` is globally `α`-Hölder with constant `K`, then `D²u` is globally `α`-Hölder
with constant `C (K + N)`. -/
theorem exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) (L : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      UniformlyEllipticOn univ a lam Lam → (∀ i j, HolderWith L α (fun x => a x i j)) →
      ∀ {u : E → ℝ} {N K : ℝ≥0}, ContDiff ℝ 2 u →
      (∀ x, |u x| ≤ N) → (∀ x, ‖fderiv ℝ u x‖ ≤ N) → (∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
      (∀ S, IsCompact S → ∃ V : ℝ≥0, HolderOnWith V α (iteratedFDeriv ℝ 2 u) S) →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      HolderWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) := by
  -- Without `0 < λ` no coefficient field is uniformly elliptic.
  rcases le_or_gt lam 0 with hlam | hlam
  · exact ⟨0, fun hA => absurd hA.pos (not_lt.2 hlam)⟩
  obtain ⟨C₀, -, hball⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  -- One radius `R` satisfying the scale condition, and one constant `C₁` for every centre.
  obtain ⟨R, hR, -, hscale⟩ := Real.exists_pos_le_one_mul_rpow_le
    (2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
      ((1 + 2 ^ (α : ℝ)) * L)) (NNReal.coe_pos.2 hα) hlam
  obtain ⟨C₁, hC₁⟩ := hball (L := L) (M := Lam.toNNReal) hlam hR
    (by simpa only [mul_assoc] using hscale) (half_lt_self hR)
  set δ : ℝ≥0 := ⟨R / 2, by positivity⟩
  have hδ : 0 < δ := by rw [← NNReal.coe_pos]; exact half_pos hR
  refine ⟨C₁ + 2 * δ ^ (-(α : ℝ)), fun {a} hA hL {u N K} hu hN₀ hN₁ hN₂ hV hK => ?_⟩
  -- Points at distance less than `R / 2` lie in the half ball about the first of them.
  have hloc : ∀ x ∈ univ, ∀ y ∈ univ, dist x y < δ → dist (iteratedFDeriv ℝ 2 u x)
      (iteratedFDeriv ℝ 2 u y) ≤ (C₁ * (K + N) : ℝ≥0) * dist x y ^ (α : ℝ) := by
    intro x _ y _ hxy
    obtain ⟨V, hV'⟩ := hV _ (isCompact_closedBall x R)
    have key := hC₁ (hA.lower_bound (mem_univ x)) (hA.toQuadraticForm'_le (mem_univ x))
      (fun i j => (hL i j).holderOnWith _)
      (fun z _ i j => (hA.abs_apply_le (mem_univ z) i j).trans (Real.le_coe_toNNReal _))
      hu.contDiffOn (fun z _ => hN₀ z) (fun z _ => hN₁ z) (fun z _ => hN₂ z)
      (hV'.mono ball_subset_closedBall) (hK.holderOnWith _)
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
`|u| ≤ N`, and with `D²u` bounded and globally `α`-Hölder (with any constant). If `L u` is globally
`α`-Hölder with constant `K`, then `D²u` is globally `α`-Hölder with constant `C (K + N)`, and
`‖Du‖` and `‖D²u‖` are bounded by `C (K + N)`. -/
theorem exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) (L : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      UniformlyEllipticOn univ a lam Lam → (∀ i j, HolderWith L α (fun x => a x i j)) →
      ∀ {u : E → ℝ} {N K : ℝ≥0}, ContDiff ℝ 2 u → (∀ x, |u x| ≤ N) →
      BddAbove (range fun x => ‖iteratedFDeriv ℝ 2 u x‖) → MemHolder α (iteratedFDeriv ℝ 2 u) →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) →
      HolderWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) ∧
        (∀ x, ‖fderiv ℝ u x‖ ≤ C * (K + N)) ∧ ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ C * (K + N) := by
  obtain ⟨C₁, hC₁⟩ :=
    exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderWith hα hα1 lam Lam L
  -- The interpolation scale `ε`, small enough to absorb the Hölder norm of `D²u`.
  obtain ⟨ε, hε, hε1, hεC⟩ :=
    Real.exists_pos_le_one_mul_rpow_le (4 * C₁) (NNReal.coe_pos.2 hα)
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hεα : ε ^ (α : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1 α.coe_nonneg
  set c : ℝ := 34 / ε + 32 / ε ^ 2
  have hc : 0 ≤ c := by positivity
  set A : ℝ := 2 * C₁ * (1 + c)
  have hA : 0 ≤ A := by positivity
  refine ⟨(3 * A + c).toNNReal, fun {a} hEll hL {u N K} hu hN hbdd hmem hK => ?_⟩
  -- The Hölder norm `H` of `D²u` and the interpolation inequalities at scale `ε`.
  set H := nnHolderNorm α (iteratedFDeriv ℝ 2 u)
  have hH : HolderWith H α (iteratedFDeriv ℝ 2 u) := hmem.holderWith
  have hN0 (y : E) : ‖iteratedFDeriv ℝ 0 u y‖ ≤ N := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hN y
  have h2 (x : E) : ‖iteratedFDeriv ℝ 2 u x‖ ≤ 32 * N / ε ^ 2 + 2 * H * ε ^ (α : ℝ) :=
    hH.norm_iteratedFDeriv_add_two_le_of_norm_le (k := 0) hu hN0 hbdd hε x
  have h1 (x : E) : ‖fderiv ℝ u x‖ ≤ 34 * N / ε + 2 * H * ε ^ (α : ℝ) := by
    have h := hH.norm_iteratedFDeriv_succ_le_of_norm_le_of_bddAbove (k := 0) hu hN0 hbdd hε x
    rw [zero_add, norm_iteratedFDeriv_one] at h
    have hε' : ε ^ (1 + (α : ℝ)) ≤ ε ^ (α : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
    nlinarith [H.coe_nonneg]
  -- The first estimate with `N₁ = (1 + c) N + 4 H ε^α`, which bounds `|u|`, `‖Du‖` and `‖D²u‖`.
  have hNN : 0 ≤ (N : ℝ) := N.coe_nonneg
  have hHε : 0 ≤ (H : ℝ) * ε ^ (α : ℝ) := by positivity
  have h34 : 0 ≤ 34 * (N : ℝ) / ε := by positivity
  have h32 : 0 ≤ 32 * (N : ℝ) / ε ^ 2 := by positivity
  have hcN : 34 * N / ε + 32 * N / ε ^ 2 = c * N := by simp only [c]; ring
  set N₁ : ℝ := (1 + c) * N + 4 * H * ε ^ (α : ℝ)
  have hN₁ : 0 ≤ N₁ := by positivity
  have hHN : H ≤ C₁ * (K + N₁.toNNReal) := by
    refine (hC₁ hEll hL hu (fun x => (hN x).trans ?_) (fun x => (h1 x).trans ?_)
      (fun x => (h2 x).trans ?_) (fun S _ => ⟨H, hH.holderOnWith S⟩) hK).nnholderNorm_le <;>
    · rw [Real.coe_toNNReal _ hN₁]
      simp only [N₁]
      nlinarith
  -- Absorption: `H ≤ C₁ (K + (1 + c) N) + 4 C₁ ε^α H` and `4 C₁ ε^α ≤ 1 / 2`.
  have hHA : (H : ℝ) ≤ A * (K + N) := by
    have h : (H : ℝ) ≤ C₁ * (K + N₁) := by
      have : (H : ℝ) ≤ ((C₁ * (K + N₁.toNNReal) : ℝ≥0) : ℝ) := by exact_mod_cast hHN
      rwa [NNReal.coe_mul, NNReal.coe_add, Real.coe_toNNReal _ hN₁] at this
    have habs : 4 * C₁ * ε ^ (α : ℝ) * H ≤ 1 / 2 * H :=
      mul_le_mul_of_nonneg_right hεC H.coe_nonneg
    have hKN : 0 ≤ (C₁ : ℝ) * (1 + c) * N := by positivity
    have hK0 : 0 ≤ (C₁ : ℝ) * K := by positivity
    simp only [A, N₁] at h ⊢
    nlinarith
  have hKN : 0 ≤ (K : ℝ) + N := by positivity
  have hC : (3 * A + c) * (K + N) ≤ ((3 * A + c).toNNReal : ℝ) * (K + N) :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) hKN
  have hHε' : (H : ℝ) * ε ^ (α : ℝ) ≤ H := mul_le_of_le_one_right H.coe_nonneg hεα
  have hA' : 0 ≤ A * (K + N) := mul_nonneg hA hKN
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
  obtain ⟨hH, h1, h2⟩ := hC hA hL u.contDiff hN
    ⟨‖u‖, by rintro _ ⟨x, rfl⟩; exact u.norm_iteratedFDeriv_apply_le le_rfl x⟩
    u.memHolder_iteratedFDeriv hK
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
