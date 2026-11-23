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
import TauCeti.Analysis.Calculus.SecondDerivative
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
are Hölder (`HolderOnWith.mul_of_eq_zero`). This file proves these bounds on an arbitrary set `t`:
the data need only be given on `s ∩ t`. The interior estimate takes `t` to be the whole space. The
boundary estimate takes `t` to be the closed half-space for the Hessian entries of `w`, and the open
half-space for the operator applied to `w`.

## Main declarations

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
  obtain ⟨h1, b1⟩ := HolderOnWith.mul_of_eq_zero c1 c1M c10 hH0 hN0
  obtain ⟨h2, b2⟩ := HolderOnWith.mul_of_eq_zero c2 c2M c20 (hH1 j) (hN1 j)
  obtain ⟨h3, b3⟩ := HolderOnWith.mul_of_eq_zero c3 c3M c30 (hH1 i) (hN1 i)
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
  obtain ⟨h1, b1⟩ := HolderOnWith.mul_of_eq_zero (hZ0.1.holderOnWith t) (fun x _ => hZ0.2 x)
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
  obtain ⟨h1, -⟩ := HolderOnWith.mul_of_eq_zero (hZ0.1.holderOnWith t) (fun x _ => hZ0.2 x)
    (fun x _ hx => image_eq_zero_of_notMem_tsupport fun h => hx (hζs h)) hK hfM
  have h2 (i j : Fin (n + 1)) := by
    obtain ⟨hT, bT, hT0⟩ := holderOnWith_cutoff_remainder hζs hZ1 hZ2 hN0 hN1 hH0 hH1 i j
    exact (HolderOnWith.mul_of_eq_zero hT (Mc := 3 * Z * N) (by exact_mod_cast bT)
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

/-- The comparison of constants closing the localized Schauder estimates: with `0 ≤ κ`, `0 ≤ λ`,
`0 ≤ Q` and `0 ≤ A`, if `X ≤ A N` then
`2 κ ((Z K + N B) / λ + Q X) ≤ max (2 κ (Z / λ + B / λ + Q A)) 0 * (K + N)`. -/
theorem two_mul_mul_add_div_add_mul_le {κ lam Q A X : ℝ} {Z B K N : ℝ≥0} (hκ : 0 ≤ κ)
    (hlam : 0 ≤ lam) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hX : X ≤ A * N) :
    2 * κ * (((Z * K + N * B : ℝ≥0) : ℝ) / lam + Q * X) ≤
      ((2 * κ * (Z / lam + B / lam + Q * A)).toNNReal * (K + N) : ℝ≥0) := by
  have hZ : 0 ≤ (Z : ℝ) / lam := div_nonneg Z.coe_nonneg hlam
  have hB : 0 ≤ (B : ℝ) / lam := div_nonneg B.coe_nonneg hlam
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
        have : 0 ≤ Q * A := mul_nonneg hQ hA
        have : 0 ≤ (K : ℝ) := K.coe_nonneg
        have : 0 ≤ (N : ℝ) := N.coe_nonneg
        nlinarith

end TauCeti.PDE
