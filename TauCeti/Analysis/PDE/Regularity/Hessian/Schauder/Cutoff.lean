/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.SecondDerivative

import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Cutoff products in the Schauder estimates

Let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a non-divergence-form operator on `ℝ^{n+1}`, let `ζ` be a smooth
cutoff and `u` a `C²` function. The localized Schauder estimates apply an estimate for functions
with Hessian supported in a ball to the cutoff product `w = ζ u`, whose Hessian entries are

`∂ᵢ∂ⱼw = ζ ∂ᵢ∂ⱼu + Tᵢⱼ`, where `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu`,

so that `L w = ζ L u + ∑ᵢⱼ aᵢⱼ Tᵢⱼ`. Every term is the product of a factor built from `ζ`, which
vanishes at the points of a set `t` outside a set `s`, with a factor that is bounded and Hölder on
`s`; such products are Hölder on `t` (`HolderOnWith.smul_of_eq_zero`). This file proves these
bounds relative to `t`. The interior estimate takes `t` to be the whole space and the estimate at
a flat boundary takes `t` to be a half-space.

## Main declarations

* `TauCeti.PDE.holderOnWith_cutoff_remainder`: the lower-order part `Tᵢⱼ` is Hölder and bounded
  on `t` and vanishes at the points of `t` outside `s`.
* `TauCeti.PDE.holderOnWith_fderiv_fderiv_cutoff_mul`: the Hessian entries of `ζ u` are Hölder
  and bounded on `t`.
* `TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul`: the operator applied to `ζ u` is
  Hölder on `t`.
* `TauCeti.PDE.holderOnWith_coordinates_of_convex_of_norm_le`: on a convex set inside a ball, the
  bounds on `Du` and `D²u` give the coordinate bounds and Hölder constants of `u` and its first
  two derivatives which the previous lemmas take.
* `TauCeti.PDE.cutoff_constant_le`: the comparison of constants which closes the cutoff argument.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, proof of Theorem 6.2 (localization of the Schauder estimate by cutoffs).
-/

public section

noncomputable section

open Metric Set
open scoped NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The lower-order part `Tᵢⱼ = ∂ᵢ∂ⱼζ u + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu` of the Hessian entry `∂ᵢ∂ⱼ(ζ u)` is
Hölder and bounded on `t` and vanishes at the points of `t` outside `s`, when the first and second
derivatives of `ζ` are globally Hölder and bounded with constant `Z`, the points of `t` outside
`s` lie outside the topological support of `ζ`, and `u` and its first derivatives are bounded by
`N` and Hölder with constant `H` on `s`. -/
theorem holderOnWith_cutoff_remainder {s t : Set E} {ζ u : E → ℝ} {α Z N H : ℝ≥0}
    (hZ1 : HolderWith Z α (fderiv ℝ ζ)) (hZ2 : HolderWith Z α (fderiv ℝ (fderiv ℝ ζ)))
    (hB1 : ∀ x, ‖fderiv ℝ ζ x‖ ≤ Z) (hB2 : ∀ x, ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ Z)
    (hζs : ∀ x ∈ t, x ∉ s → x ∉ tsupport ζ) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    (i j : Fin (n + 1)) :
    HolderOnWith (3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)) t ∧
    (∀ x ∈ t, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
        u x + fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)| ≤
      3 * Z * N) ∧
    ∀ x ∈ t, x ∉ s →
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1) =
      0 := by
  have he (k : Fin (n + 1)) : ‖(EuclideanSpace.single k 1 : E)‖ ≤ 1 := by simp
  -- The coordinate derivatives of `ζ`: Hölder and bounded by `Z`, and zero on `t` outside `s`.
  have h1 (k : Fin (n + 1)) := (hZ1.holderOnWith t).clm_apply_of_norm_le_one (he k)
  have h2 := ((hZ2.holderOnWith t).clm_apply_of_norm_le_one (he i)).clm_apply_of_norm_le_one (he j)
  have b1 (k : Fin (n + 1)) (x : E) : ‖fderiv ℝ ζ x (EuclideanSpace.single k 1)‖ ≤ Z :=
    ((fderiv ℝ ζ x).unit_le_opNorm _ (he k)).trans (hB1 x)
  have b2 (x : E) :
      ‖fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)‖ ≤ Z :=
    ((fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1)).unit_le_opNorm _ (he j)).trans
      (((fderiv ℝ (fderiv ℝ ζ) x).unit_le_opNorm _ (he i)).trans (hB2 x))
  have z1 (k : Fin (n + 1)) (x : E) (hx : x ∈ t) (hxs : x ∉ s) :
      fderiv ℝ ζ x (EuclideanSpace.single k 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (hζs x hx hxs), zero_apply]
  have z2 (x : E) (hx : x ∈ t) (hxs : x ∉ s) :
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
    rw [fderiv_fderiv_of_notMem_tsupport (hζs x hx hxs), zero_apply, zero_apply]
  have hN0' (x : E) (hx : x ∈ s) : ‖u x‖ ≤ N := hN0 x hx
  have hN1' (k : Fin (n + 1)) (x : E) (hx : x ∈ s) :
      ‖fderiv ℝ u x (EuclideanSpace.single k 1)‖ ≤ N := hN1 k x hx
  have hT0 (x : E) (hx : x ∈ t) (hxs : x ∉ s) :
      fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
        fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
        fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1) =
          0 := by
    simp only [z2 x hx hxs, z1 i x hx hxs, z1 j x hx hxs, zero_mul, add_zero]
  refine ⟨(((h2.smul_of_eq_zero hH0 (fun x _ => b2 x) hN0' z2).add
      ((h1 i).smul_of_eq_zero (hH1 j) (fun x _ => b1 i x) (hN1' j) (z1 i))).add
      ((h1 j).smul_of_eq_zero (hH1 i) (fun x _ => b1 j x) (hN1' i) (z1 j))).mono_const
      (le_of_eq (by ring)), fun x hx => ?_, hT0⟩
  by_cases hxs : x ∈ s
  · refine (abs_add_three _ _ _).trans ?_
    simp only [abs_mul]
    calc _ ≤ (Z : ℝ) * N + Z * N + Z * N := by
          gcongr
          exacts [b2 x, hN0 x hxs, b1 i x, hN1 j x hxs, b1 j x, hN1 i x hxs]
      _ = _ := by ring
  · rw [hT0 x hx hxs, abs_zero]
    positivity

/-- The Hessian entries `∂ᵢ∂ⱼ(ζ u) = ζ ∂ᵢ∂ⱼu + Tᵢⱼ` of a cutoff product are Hölder and bounded on
`t`, when each point of `t` lies in the open set `U` on which `u` is `C²` or outside the
topological support of `ζ`, the points of `t` outside `s` lie outside that support, `ζ` and its
first two derivatives are globally Hölder and bounded with constant `Z`, and `u` and its first
and second derivatives are bounded by `N` on `s` and Hölder there with constants `H`, `H` and
`V`. -/
theorem holderOnWith_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U)
    {ζ u : E → ℝ} {α Z N H V : ℝ≥0} (hζ : ContDiff ℝ 2 ζ) (hZ0 : HolderWith Z α ζ)
    (hZ1 : HolderWith Z α (fderiv ℝ ζ)) (hZ2 : HolderWith Z α (fderiv ℝ (fderiv ℝ ζ)))
    (hB : ∀ x, ‖ζ x‖ ≤ Z ∧ ‖fderiv ℝ ζ x‖ ≤ Z ∧ ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ Z)
    (htU : ∀ x ∈ t, x ∈ U ∨ x ∉ tsupport ζ) (hζs : ∀ x ∈ t, x ∉ s → x ∉ tsupport ζ)
    (hu : ContDiffOn ℝ 2 u U) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    (hV : ∀ i j, HolderOnWith V α (fun x =>
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s)
    (i j : Fin (n + 1)) :
    HolderOnWith (Z * V + N * Z + 3 * (Z * H + N * Z)) α (fun x =>
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t ∧
    ∀ x ∈ t, |fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)| ≤ 4 * Z * N := by
  obtain ⟨hT, bT, -⟩ := holderOnWith_cutoff_remainder hZ1 hZ2 (fun x => (hB x).2.1)
    (fun x => (hB x).2.2) hζs hN0 hN1 hH0 hH1 i j
  have hζ0 (x : E) (hx : x ∈ t) (hxs : x ∉ s) : ζ x = 0 :=
    image_eq_zero_of_notMem_tsupport (hζs x hx hxs)
  have h1 := (hZ0.holderOnWith t).smul_of_eq_zero (hV i j) (fun x _ => (hB x).1) (hN2 i j) hζ0
  have hW (x : E) (hx : x ∈ t) :
      fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        (ζ x * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          (fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
            u x + fderiv ℝ ζ x (EuclideanSpace.single i 1) *
              fderiv ℝ u x (EuclideanSpace.single j 1) +
            fderiv ℝ ζ x (EuclideanSpace.single j 1) *
              fderiv ℝ u x (EuclideanSpace.single i 1))) := by
    rw [fderiv_fderiv_mul_apply_of_mem_or_notMem_tsupport hU hζ.contDiffOn hu (htU x hx)]
    ring
  refine ⟨(h1.add hT).congr fun x hx => (hW x hx).symm, fun x hx => ?_⟩
  rw [hW x hx]
  have b1 : |ζ x * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)| ≤ Z * N := by
    by_cases hxs : x ∈ s
    · rw [abs_mul]
      exact mul_le_mul (hB x).1 (hN2 i j x hxs) (abs_nonneg _) Z.coe_nonneg
    · rw [hζ0 x hx hxs, zero_mul, abs_zero]
      positivity
  calc _ ≤ (Z * N : ℝ) + 3 * Z * N := (abs_add_le _ _).trans (add_le_add b1 (bT x hx))
    _ = _ := by ring

/-- For a cutoff product `ζ u` as in `holderOnWith_fderiv_fderiv_cutoff_mul`, the operator
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` is Hölder on `t`, when the coefficients are
bounded by `M` and Hölder with constant `L` on `s`, and `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` is Hölder with constant
`K` on `s`. The Hessian of `u` need not be Hölder. -/
theorem holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul {s t U : Set E} (hU : IsOpen U)
    {ζ u : E → ℝ} {α Z N H : ℝ≥0} (hζ : ContDiff ℝ 2 ζ) (hZ0 : HolderWith Z α ζ)
    (hZ1 : HolderWith Z α (fderiv ℝ ζ)) (hZ2 : HolderWith Z α (fderiv ℝ (fderiv ℝ ζ)))
    (hB : ∀ x, ‖ζ x‖ ≤ Z ∧ ‖fderiv ℝ ζ x‖ ≤ Z ∧ ‖fderiv ℝ (fderiv ℝ ζ) x‖ ≤ Z)
    (htU : ∀ x ∈ t, x ∈ U ∨ x ∉ tsupport ζ) (hζs : ∀ x ∈ t, x ∉ s → x ∉ tsupport ζ)
    (hu : ContDiffOn ℝ 2 u U) (hN0 : ∀ x ∈ s, |u x| ≤ N)
    (hN1 : ∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N)
    (hN2 : ∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N)
    (hH0 : HolderOnWith H α u s)
    (hH1 : ∀ i, HolderOnWith H α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {L M K : ℝ≥0}
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) s) (hM : ∀ x ∈ s, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s) :
    HolderOnWith (Z * K + (n + 1) ^ 2 * (M * N * Z + (3 * Z * N * L + M * (3 * (Z * H + N * Z)))))
      α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ (ζ * u)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) t := by
  set f : E → ℝ := fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hfM (x : E) (hx : x ∈ s) : ‖f x‖ ≤ ((n + 1) ^ 2 * M * N : ℝ≥0) := by
    rw [Real.norm_eq_abs]
    calc |f x| ≤ ∑ i, ∑ j, |a x i j • fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), (M * N : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [smul_eq_mul, abs_mul]
          exact mul_le_mul (hM x hx i j) (hN2 i j x hx) (abs_nonneg _) M.coe_nonneg
      _ = _ := by simp; ring
  -- On `t`, `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ f + ∑ᵢⱼ Tᵢⱼ aᵢⱼ`.
  set T : Fin (n + 1) → Fin (n + 1) → E → ℝ := fun i j x =>
    fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * u x +
      fderiv ℝ ζ x (EuclideanSpace.single i 1) * fderiv ℝ u x (EuclideanSpace.single j 1) +
      fderiv ℝ ζ x (EuclideanSpace.single j 1) * fderiv ℝ u x (EuclideanSpace.single i 1)
  have heq : EqOn (fun x => ζ x • f x + ∑ i, ∑ j, T i j x • a x i j)
      (fun x => ∑ i, ∑ j, a x i j •
        fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      t := fun x hx => by
    simp only [fderiv_fderiv_mul_apply_of_mem_or_notMem_tsupport hU hζ.contDiffOn hu (htU x hx),
      smul_eq_mul, f, T, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h1 := (hZ0.holderOnWith t).smul_of_eq_zero hK (fun x _ => (hB x).1) hfM
    fun x hx hxs => image_eq_zero_of_notMem_tsupport (hζs x hx hxs)
  have h2 (i j : Fin (n + 1)) : HolderOnWith (3 * Z * N * L + M * (3 * (Z * H + N * Z))) α
      (fun x => T i j x • a x i j) t := by
    obtain ⟨hT, bT, hT0⟩ := holderOnWith_cutoff_remainder hZ1 hZ2 (fun x => (hB x).2.1)
      (fun x => (hB x).2.2) hζs hN0 hN1 hH0 hH1 i j
    exact hT.smul_of_eq_zero (Mc := 3 * Z * N) (hL i j) (by exact_mod_cast bT)
      (fun x hx => hM x hx i j) hT0
  have hsum := HolderOnWith.sum (s := Finset.univ)
    (f := fun i x => ∑ j, T i j x • a x i j) fun i _ =>
      HolderOnWith.sum (s := Finset.univ) (f := fun j x => T i j x • a x i j) fun j _ => h2 i j
  refine ((h1.add hsum).congr heq).mono_const (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The coordinate bounds and Hölder constants of a function `u` which is `C²` at the points of a
convex set `s` inside the ball `B_R` on which `‖Du‖` and `‖D²u‖` are bounded by `N` and `D²u` is
Hölder with constant `V`: `u` and the partial derivatives `∂ᵢu` are Hölder on `s` with constant
`N (2R)^(1 - α)`, the `∂ᵢu` and `∂ᵢ∂ⱼu` are bounded by `N`, and the `∂ᵢ∂ⱼu` are Hölder with
constant `V`. -/
theorem holderOnWith_coordinates_of_convex_of_norm_le {u : E → ℝ} {s : Set E} {x₀ : E} {R : ℝ}
    {N V α : ℝ≥0} (hα : α ≤ 1) (hs : Convex ℝ s) (hsR : s ⊆ ball x₀ R)
    (hu : ∀ x ∈ s, ContDiffAt ℝ 2 u x) (hN1 : ∀ x ∈ s, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ s, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) s) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α u s ∧
    (∀ i, HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) s) ∧
    (∀ i, ∀ x ∈ s, |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ N) ∧
    (∀ i j, ∀ x ∈ s,
      |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ N) ∧
    ∀ i j, HolderOnWith V α (fun x =>
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) s := by
  have he (i : Fin (n + 1)) : ‖(EuclideanSpace.single i 1 : E)‖ ≤ 1 := by simp
  have hHDu := hs.holderOnWith_fderiv_of_norm_iteratedFDeriv_two_le hα hsR hu hN2
  refine ⟨hs.holderOnWith_of_norm_fderiv_le hα hsR
      (fun x hx => (hu x hx).differentiableAt two_ne_zero) hN1,
    fun i => hHDu.clm_apply_of_norm_le_one (he i),
    fun i x hx => ((fderiv ℝ u x).unit_le_opNorm _ (he i)).trans (hN1 x hx),
    fun i j x hx => ?_, fun i j => ?_⟩
  · simpa [iteratedFDeriv_two_apply] using
      ((iteratedFDeriv ℝ 2 u x).norm_apply_orthonormalBasis_le
        (EuclideanSpace.basisFun _ ℝ) i j).trans (hN2 x hx)
  · simpa [iteratedFDeriv_two_apply] using
      hV.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j

/-- The comparison of constants closing the cutoff argument of the Schauder estimates: if
`0 ≤ X ≤ A N`, then `2 κ ((Z K + N B) / λ + Q X) ≤ 2 κ (Z / λ + B / λ + Q A) (K + N)` after
truncation to `ℝ≥0`. -/
theorem cutoff_constant_le {κ lam Q A X : ℝ} {Z B K N : ℝ≥0} (hlam : 0 < lam) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hX₀ : 0 ≤ X) (hX : X ≤ A * N) :
    (2 * κ * (((Z * K + N * B : ℝ≥0) : ℝ) / lam + Q * X)).toNNReal ≤
      (2 * κ * (Z / lam + B / lam + Q * A)).toNNReal * (K + N) := by
  rcases lt_or_ge κ 0 with hκ | hκ
  · rw [Real.toNNReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))]
    exact zero_le
  rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity),
    mul_assoc (2 * κ) _ ((K + N : ℝ≥0) : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hQX : Q * X ≤ Q * A * N := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hX hQ
  have hZN : 0 ≤ (Z : ℝ) / lam * N := by positivity
  have hBK : 0 ≤ (B : ℝ) / lam * K := by positivity
  have hQAK : 0 ≤ Q * A * K := by positivity
  push_cast
  calc ((Z : ℝ) * K + N * B) / lam + Q * X = Z / lam * K + B / lam * N + Q * X := by ring
    _ ≤ (Z / lam + B / lam + Q * A) * (K + N) := by nlinarith

end TauCeti.PDE
