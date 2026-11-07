/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.HolderCoefficient
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.WholeSpace
import TauCeti.Analysis.Holder.Interpolation
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Topology.MetricSpace.Holder

/-!
# Schauder estimates with lower-order terms

Let `0 < α < 1`. This file extends the interior and the whole-space Schauder estimates for
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` to the general second-order operator in non-divergence form

`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + b · ∇u + c u`,

with a drift `b : ℝ^{n+1} → ℝ^{n+1}` and a potential `c`, both `α`-Hölder. The drift term is
written `fderiv ℝ u x (b x)`, as in the maximum principles for operators with lower-order terms.
No sign condition on `c` is needed for the estimates.

* The interior estimate,
  `exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul`,
  on a compact set `K` inside an open set `Ω`. If `a`, `b` and `c` are `α`-Hölder on a ball
  around each point of `K` and `a` is elliptic at each point of `K`, there is a constant `C` such
  that every `u` that is `C²` on `Ω` satisfies `[D²u]_{α; K} ≤ C ([L u]_{α; Ω} + N)`, where `N`
  bounds `|u|`, `‖Du‖` and `‖D²u‖` on `Ω`.
* The global estimate,
  `exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul`,
  on the whole space. For uniformly elliptic `a` and globally Hölder and bounded `a`, `b` and `c`,
  the Hölder constant of `D²u` and the bounds of `Du` and `D²u` are at most
  `C ([L u]_α + ‖u‖_∞)`, with `C` depending only on `n`, `α`, the ellipticity constants and the
  bounds on the coefficients.

## The argument

The lower-order part `b · ∇u + c u` is moved to the right side: `u` solves
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = L u - b · ∇u - c u`, and the Hölder constant of `b · ∇u + c u` is bounded by
products of the sup norms and the Hölder constants of the factors
(`ContinuousLinearMap.holderOnWith_comp₂`). The functions `u` and `Du` are bounded, with
derivatives bounded by the bounds on `Du` and `D²u`, so they are `α`-Hölder
(`TauCeti.holderOnWith_thickening_of_norm_fderiv_le`,
`TauCeti.holderWith_of_norm_le_of_norm_fderiv_le`).

In the interior estimate the principal-part estimate
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderOnWith`)
is applied on a thickening `U` of `K`. It is chosen so thin that the ball of the same radius about
each point of `U` stays in `Ω`, which makes `u` and `Du` Lipschitz between nearby points of `U`,
and so that the local Hölder bounds on `b` and `c` become uniform on `U`
(`IsCompact.exists_holderOnWith_thickening_and_norm_le`). All lower-order quantities are then
bounded by multiples of `N`.

On the whole space only `‖u‖_∞` is allowed on the right, so the bounds of `Du` and `D²u` entering
through the lower-order terms are removed by the interpolation inequalities
`‖Du‖_∞, ‖D²u‖_∞ ≤ C_ε ‖u‖_∞ + 2 ε^α [D²u]_α`
(`HolderWith.norm_iteratedFDeriv_succ_le_and_norm_iteratedFDeriv_add_two_le`), and the resulting
multiple of
`[D²u]_α` is absorbed into the global principal-part estimate
(`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv`) for
small `ε`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, Theorem 6.2 and the proof of Theorem 6.6 (lower-order terms by interpolation).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, Graduate Studies
  in Mathematics 12, AMS, 1996, Chapter 4 (a priori estimates in the whole space).
-/

public section

noncomputable section

open Metric Set Filter Topology
open scoped NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The Hölder constant of the lower-order part `b · ∇u + c u` on a set `s`, in terms of the
Hölder constants and bounds of `u`, `Du`, `b` and `c` on `s`. -/
private theorem holderOnWith_fderiv_apply_add_mul {s : Set E} {u : E → ℝ} {b : E → E}
    {c : E → ℝ} {α H₀ H₁ N₀ N₁ Lb Mb Lc Mc : ℝ≥0} (hu : HolderOnWith H₀ α u s)
    (hDu : HolderOnWith H₁ α (fderiv ℝ u) s) (hu0 : ∀ x ∈ s, |u x| ≤ N₀)
    (hDu0 : ∀ x ∈ s, ‖fderiv ℝ u x‖ ≤ N₁) (hb : HolderOnWith Lb α b s)
    (hbM : ∀ x ∈ s, ‖b x‖ ≤ Mb) (hc : HolderOnWith Lc α c s) (hcM : ∀ x ∈ s, |c x| ≤ Mc) :
    HolderOnWith (N₁ * Lb + Mb * H₁ + (Mc * H₀ + N₀ * Lc)) α
      (fun x => fderiv ℝ u x (b x) + c x * u x) s := by
  have h₁ := (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).holderOnWith_comp₂ hDu hb hDu0 hbM
  have h₂ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).holderOnWith_comp₂ hc hu
    (fun x hx => by simpa only [Real.norm_eq_abs] using hcM x hx)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hu0 x hx)
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at h₁ h₂
  refine (h₁.add h₂).mono_const (add_le_add ?_ ?_)
  · exact mul_le_of_le_one_left zero_le (by
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]; exact ContinuousLinearMap.norm_id_le)
  · exact mul_le_of_le_one_left zero_le ContinuousLinearMap.opNNNorm_lsmul_le

/-- The bookkeeping of constants in the interior estimate:
`C₀ (M + N P + N) ≤ C₀ (1 + P) (M + N)`. -/
private theorem mul_add_mul_add_le_mul_one_add_mul_add (C₀ M N P : ℝ≥0) :
    C₀ * (M + N * P + N) ≤ C₀ * (1 + P) * (M + N) := by
  calc C₀ * (M + N * P + N) ≤ C₀ * ((1 + P) * (M + N)) := by
        gcongr
        calc M + N * P + N = M + N * (1 + P) := by ring
          _ ≤ (1 + P) * M + (1 + P) * N := by
            rw [mul_comm N]
            gcongr
            exact le_mul_of_one_le_left zero_le le_self_add
          _ = (1 + P) * (M + N) := by ring
    _ = C₀ * (1 + P) * (M + N) := by ring

/-- If `u` is `C²` on the whole space, with `|u| ≤ N`, and `Du` and `D²u` are bounded by `P`, then
`u` and `Du` are globally `α`-Hölder, with constants `P + 2 N` and `P + 2 P`. -/
private theorem holderOnWith_univ_of_norm_le_of_norm_iteratedFDeriv_two_le {α N P : ℝ≥0}
    (hα1 : α < 1) {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hN : ∀ x, |u x| ≤ N)
    (h1 : ∀ x, ‖fderiv ℝ u x‖ ≤ P) (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ P) :
    HolderOnWith (P + 2 * N) α u univ ∧ HolderOnWith (P + 2 * P) α (fderiv ℝ u) univ := by
  refine ⟨(holderWith_of_norm_le_of_norm_fderiv_le hα1.le (hu.differentiable (by norm_num))
      (fun x => by rw [Real.norm_eq_abs]; exact hN x) h1).holderOnWith univ,
    (holderWith_of_norm_le_of_norm_fderiv_le hα1.le
      ((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) h1
      fun x => ?_).holderOnWith univ⟩
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact h2 x

/-- The interpolation inequalities at scale `0 < ε ≤ 1` for a `C²` function `u` with `|u| ≤ N` and
bounded, globally `α`-Hölder second derivative with Hölder constant `H`: both `‖Du‖` and `‖D²u‖`
are bounded by `(34 / ε + 32 / ε²) N + 2 H ε^α`. -/
private theorem norm_fderiv_le_and_norm_iteratedFDeriv_two_le {α H N : ℝ≥0} {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {u : E → ℝ} (hu : ContDiff ℝ 2 u) (hN : ∀ x, |u x| ≤ N)
    (hbdd : BddAbove (range fun x => ‖iteratedFDeriv ℝ 2 u x‖))
    (hH : HolderWith H α (iteratedFDeriv ℝ 2 u)) :
    (∀ x, ‖fderiv ℝ u x‖ ≤ (34 / ε + 32 / ε ^ 2) * N + 2 * H * ε ^ (α : ℝ)) ∧
      ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ (34 / ε + 32 / ε ^ 2) * N + 2 * H * ε ^ (α : ℝ) := by
  have hN0 (y : E) : ‖iteratedFDeriv ℝ 0 u y‖ ≤ N := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hN y
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have h := (hH.norm_iteratedFDeriv_succ_le_and_norm_iteratedFDeriv_add_two_le (k := 0) hu hN0
      hbdd hε hε1 x).1
    rwa [zero_add, norm_iteratedFDeriv_one] at h
  · exact (hH.norm_iteratedFDeriv_succ_le_and_norm_iteratedFDeriv_add_two_le (k := 0) hu hN0 hbdd hε
      hε1 x).2

/-- The absorption step of the global estimate: if `K₀ + N = K + γ N + 2 β ε^α H`, with
`H ≤ C₀ (K₀ + N)` and `2 C₀ β ε^α ≤ 1 / 2`, then `C₀ (K₀ + N) ≤ 2 C₀ (1 + γ) (K + N)`. -/
private theorem mul_le_two_mul_one_add_mul_of_absorb {C₀ K N γ β e H K₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hγ : 0 ≤ γ) (hK₀ : K₀ + N = K + γ * N + 2 * β * e * H)
    (hHle : H ≤ C₀ * (K₀ + N)) (habs : 2 * C₀ * β * e * H ≤ 1 / 2 * H) :
    C₀ * (K₀ + N) ≤ 2 * C₀ * (1 + γ) * (K + N) := by
  have hKγ : 0 ≤ C₀ * (K + γ * N) := by positivity
  rw [hK₀] at hHle ⊢
  have hγN : K + γ * N ≤ (1 + γ) * (K + N) := by nlinarith
  have hsplit : C₀ * (K + γ * N + 2 * β * e * H) = C₀ * (K + γ * N) + 2 * C₀ * β * e * H := by
    ring
  rw [hsplit] at hHle ⊢
  have hH2 : H ≤ 2 * (C₀ * (K + γ * N)) := by linarith
  have hC₀γ : C₀ * (K + γ * N) ≤ C₀ * ((1 + γ) * (K + N)) :=
    mul_le_mul_of_nonneg_left hγN hC₀
  linarith

/-- **The interior Schauder estimate with lower-order terms.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be open and `K ⊆ Ω` compact. Let `a` be a matrix-valued coefficient, `b` a
vector field and `c` a function, each `α`-Hölder on a ball around each `x ∈ K`, with `a x`
elliptic at each `x ∈ K`, that is, `λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + b · ∇u + c u`. Then there is a constant `C`, depending on `a`, `b`, `c`,
`K` and `Ω` but not on `u`, with the following property. Let `u` be `C²` on `Ω`, with `|u|`, `‖Du‖`
and `‖D²u‖` bounded by `N` on `Ω` and with `D²u` `α`-Hölder on every compact subset of `Ω` (with
any constants). If `L u` is `α`-Hölder on `Ω` with constant `M`, then `D²u` is `α`-Hölder on `K`
with constant `C (M + N)`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ}
    (ha : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j, HolderOnWith L α (fun y => a y i j) (ball x r))
    (hb : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α b (ball x r))
    (hc : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α c (ball x r))
    (hell : ∀ x ∈ K, ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ} {N M : ℝ≥0}, ContDiffOn ℝ 2 u Ω →
      (∀ x ∈ Ω, |u x| ≤ N) → (∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ N) →
      (∀ x ∈ Ω, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
      (∀ S ⊆ Ω, IsCompact S → ∃ V : ℝ≥0, HolderOnWith V α (iteratedFDeriv ℝ 2 u) S) →
      HolderOnWith M α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x) +
          c x * u x) Ω →
      HolderOnWith (C * (M + N)) α (iteratedFDeriv ℝ 2 u) K := by
  obtain ⟨δΩ, hδΩ, hΩδ⟩ := hK.exists_thickening_subset_open hΩ hKΩ
  obtain ⟨δb, hδb, Lb, Mb, hLb, hMb⟩ := hK.exists_holderOnWith_thickening_and_norm_le hb
  obtain ⟨δc, hδc, Lc, Mc, hLc, hMc⟩ := hK.exists_holderOnWith_thickening_and_norm_le hc
  -- The thickening `U = K_δ`, on which `b` and `c` are Hölder and bounded, with `K_{2δ} ⊆ Ω`.
  set δ : ℝ≥0 := ⟨min (δΩ / 2) (min δb δc), by positivity⟩
  have hδ : 0 < δ := by
    rw [← NNReal.coe_pos]
    exact lt_min (half_pos hδΩ) (lt_min hδb hδc)
  have hδΩ' : (δ : ℝ) ≤ δΩ / 2 := min_le_left _ _
  have hδb' : (δ : ℝ) ≤ δb := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : (δ : ℝ) ≤ δc := (min_le_right _ _).trans (min_le_right _ _)
  set U := thickening (δ : ℝ) K
  have h2U : thickening (2 * δ) K ⊆ Ω := (thickening_mono (by linarith) K).trans hΩδ
  have hUΩ : U ⊆ Ω := (thickening_mono (by linarith [δ.coe_nonneg]) K).trans h2U
  have hUb : U ⊆ thickening δb K := thickening_mono hδb' K
  have hUc : U ⊆ thickening δc K := thickening_mono hδc' K
  obtain ⟨C₀, hC₀⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderOnWith hα hα1
      isOpen_thickening hK (self_subset_thickening (by exact_mod_cast hδ) K) ha hell
  set Q : ℝ≥0 := δ ^ (1 - (α : ℝ)) + 2 * δ ^ (-(α : ℝ))
  set P : ℝ≥0 := Mb * Q + Lb + (Mc * Q + Lc)
  refine ⟨C₀ * (1 + P), fun {u N M} hu hN₀ hN₁ hN₂ hV hM => ?_⟩
  -- `u` and `Du` are `α`-Hölder on `U` with constant `N Q`.
  have hHu : HolderOnWith (N * Q) α u U := by
    refine (holderOnWith_thickening_of_norm_fderiv_le (N₀ := N) (N₁ := N) hδ hα1.le hΩ h2U
      (hu.differentiableOn (by norm_num)) (fun x hx => ?_) hN₁).mono_const (le_of_eq (by ring))
    rw [Real.norm_eq_abs]
    exact hN₀ x hx
  have hHDu : HolderOnWith (N * Q) α (fderiv ℝ u) U := by
    refine (holderOnWith_thickening_of_norm_fderiv_le (N₀ := N) (N₁ := N) hδ hα1.le hΩ h2U
      ((hu.fderiv_of_isOpen hΩ (m := 1) (by norm_num)).differentiableOn (by norm_num)) hN₁
      fun x hx => ?_).mono_const (le_of_eq (by ring))
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hN₂ x hx
  -- The principal part `L u - (b · ∇u + c u)` is `α`-Hölder on `U` with constant `M + N P`.
  have hlow := holderOnWith_fderiv_apply_add_mul hHu hHDu (fun x hx => hN₀ x (hUΩ hx))
    (fun x hx => hN₁ x (hUΩ hx)) (hLb.mono hUb) (fun x hx => hMb x (hUb hx)) (hLc.mono hUc)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hMc x (hUc hx))
  have hprin : HolderOnWith (M + N * P) α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) U := by
    have h := (hM.mono hUΩ).sub hlow
    simp only [Pi.sub_def, add_sub_add_right_eq_sub, add_sub_cancel_right] at h
    exact h.mono_const (le_of_eq (by ring))
  have key := hC₀ (hu.mono hUΩ) (fun x hx => hN₀ x (hUΩ hx)) (fun x hx => hN₁ x (hUΩ hx))
    (fun x hx => hN₂ x (hUΩ hx)) (fun S hS hSc => hV S (hS.trans hUΩ) hSc) hprin
  exact key.mono_const (mul_add_mul_add_le_mul_one_add_mul_add C₀ M N P)

/-- **The global Schauder estimate with lower-order terms on the whole space.** Let `0 < α < 1`,
and let `λ`, `Λ`, `L` and `B` be given. Then there is a constant `C`, depending only on `n`, `α`,
`λ`, `Λ`, `L` and `B`, with the following property. Let `a` be a matrix-valued coefficient on
`ℝ^{n+1}` which is uniformly elliptic and bounded with constants `0 < λ ≤ Λ`
(`UniformlyEllipticOn univ a λ Λ`) and globally `α`-Hölder entrywise with constant `L`, and let `b`
be a vector field and `c` a function, both globally `α`-Hölder with constant `L` and bounded by
`B`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + b · ∇u + c u`. Let `u` be `C²` with `|u| ≤ N`, and with `D²u`
bounded and globally `α`-Hölder (with any constant). If `L u` is globally `α`-Hölder with constant
`K`, then `D²u` is globally `α`-Hölder with constant `C (K + N)`, and `‖Du‖` and `‖D²u‖` are
bounded by `C (K + N)`. -/
theorem
    exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (lam Lam : ℝ) (L B : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ},
      UniformlyEllipticOn univ a lam Lam → (∀ i j, HolderWith L α (fun x => a x i j)) →
      HolderWith L α b → (∀ x, ‖b x‖ ≤ B) → HolderWith L α c → (∀ x, |c x| ≤ B) →
      ∀ {u : E → ℝ} {N K : ℝ≥0}, ContDiff ℝ 2 u → (∀ x, |u x| ≤ N) →
      BddAbove (range fun x => ‖iteratedFDeriv ℝ 2 u x‖) → MemHolder α (iteratedFDeriv ℝ 2 u) →
      HolderWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x) +
          c x * u x) →
      HolderWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) ∧
        (∀ x, ‖fderiv ℝ u x‖ ≤ C * (K + N)) ∧ ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ C * (K + N) := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_holderWith_iteratedFDeriv_two_and_norm_le_of_sum_smul_fderiv_fderiv hα hα1 lam Lam L
  -- `β` is the coefficient of the bound `P` of `Du` and `D²u` in the Hölder constant of
  -- `b · ∇u + c u`, and `ε` is an interpolation scale small enough to absorb `[D²u]_α`.
  set β : ℝ := 4 * B + L
  have hβ : 0 ≤ β := by positivity
  obtain ⟨ε, hε, hε1, hεC⟩ :=
    Real.exists_pos_le_one_mul_rpow_le (2 * C₀ * β) (NNReal.coe_pos.2 hα)
      (by norm_num : (0 : ℝ) < 1 / 2)
  set e : ℝ := ε ^ (α : ℝ)
  have he : 0 ≤ e := by positivity
  set c' : ℝ := 34 / ε + 32 / ε ^ 2
  have hc' : 0 ≤ c' := by positivity
  set γ : ℝ := β * c' + 2 * B + L + 1
  have hγ : 0 ≤ γ := by positivity
  refine ⟨(2 * C₀ * (1 + γ)).toNNReal,
    fun {a b c} hEll hLa hLb hBb hLc hBc {u N K} hu hN hbdd hmem hK => ?_⟩
  -- The Hölder norm `H` of `D²u`, and the bound `P = c' N + 2 H ε^α` of `Du` and `D²u` given by
  -- the interpolation inequalities at scale `ε`.
  set H := nnHolderNorm α (iteratedFDeriv ℝ 2 u)
  have hH : HolderWith H α (iteratedFDeriv ℝ 2 u) := hmem.holderWith
  set P : ℝ := c' * N + 2 * H * e
  have hP : 0 ≤ P := by positivity
  obtain ⟨h1, h2⟩ := norm_fderiv_le_and_norm_iteratedFDeriv_two_le hε hε1 hu hN hbdd hH
  set P' : ℝ≥0 := P.toNNReal
  have hPP' : (P' : ℝ) = P := Real.coe_toNNReal _ hP
  -- `u` and `Du` are bounded by `N` and `P'`, with derivatives bounded by `P'`, hence `α`-Hölder.
  obtain ⟨hHu, hHDu⟩ := holderOnWith_univ_of_norm_le_of_norm_iteratedFDeriv_two_le hα1 hu hN
    (fun x => (h1 x).trans hPP'.ge) fun x => (h2 x).trans hPP'.ge
  -- The principal part `L u - (b · ∇u + c u)` is globally `α`-Hölder with constant `K₀`.
  have hlow := holderOnWith_fderiv_apply_add_mul hHu hHDu (fun x _ => hN x)
    (fun x _ => (h1 x).trans hPP'.ge) (hLb.holderOnWith univ) (fun x _ => hBb x)
    (hLc.holderOnWith univ) (fun x _ => hBc x)
  set K₀ : ℝ≥0 := K + (P' * L + B * (P' + 2 * P') + (B * (P' + 2 * N) + N * L))
  have hprin : HolderWith K₀ α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
    have h := (hK.holderOnWith univ).sub hlow
    simp only [Pi.sub_def, add_sub_add_right_eq_sub, add_sub_cancel_right] at h
    exact holderOnWith_univ.1 h
  obtain ⟨hH₀, h₁, h₂⟩ := hC₀ hEll hLa hu hN hbdd hmem hprin
  -- Absorption: `C₀ (K₀ + N) = C₀ (K + γ N) + 2 C₀ β ε^α H` and `2 C₀ β ε^α ≤ 1 / 2`.
  have hK₀ : ((K₀ : ℝ) + N) = K + γ * N + 2 * β * e * H := by
    push_cast [K₀, γ, β, hPP', P]
    ring
  have hHle : (H : ℝ) ≤ C₀ * (K₀ + N) := by exact_mod_cast hH₀.nnholderNorm_le
  have habs : 2 * C₀ * β * e * H ≤ 1 / 2 * H := mul_le_mul_of_nonneg_right hεC H.coe_nonneg
  have hbound : (C₀ : ℝ) * (K₀ + N) ≤ 2 * C₀ * (1 + γ) * (K + N) :=
    mul_le_two_mul_one_add_mul_of_absorb C₀.coe_nonneg K.coe_nonneg N.coe_nonneg hγ hK₀
      hHle habs
  have hC : (2 * C₀ * (1 + γ)) * (K + N) ≤ (((2 * C₀ * (1 + γ)).toNNReal : ℝ≥0) : ℝ) * (K + N) :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity)
  refine ⟨hH.mono ?_, fun x => (h₁ x).trans ?_, fun x => (h₂ x).trans ?_⟩
  · rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  · linarith
  · linarith

end TauCeti.PDE
