/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
public import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Normed.Operator.Holder

/-!
# Entrywise Hölder estimates for matrix fields

If an invertible real matrix field has `(C, r)`-Hölder entries and inverse entries bounded
by `L`, the inverse entries are `((card ι)² L² C, r)`-Hölder
(`TauCeti.holderWith_matrix_inv_apply`). For `t ∈ [0, 1]`, a convex combination of two fields
with the same entrywise Hölder bound retains that bound
(`TauCeti.holderWith_one_sub_smul_add_smul_apply`). These estimates apply to inverse segments
before their entries are averaged. If two fields `A` and `W` have entries Hölder and bounded on a
set, so do the entries of `Wᵀ A W` (`TauCeti.holderOnWith_transpose_mul_mul_apply`), the form in
which coefficients of a second-order operator transform under a change of variables.

The estimates are adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

open Set
open scoped NNReal Matrix

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

namespace TauCeti

/--
If a field `P` of invertible matrices has `(C, r)`-Hölder entries and inverse entries bounded by
`L`, every entry of `P⁻¹` is `(n² L² C, r)`-Hölder. The constant is fixed before the entries
and the points. -/
theorem holderWith_matrix_inv_apply (P : X → Matrix ι ι ℝ)
    (C r L : ℝ≥0) (hP : ∀ x, IsUnit (P x)) (hb : ∀ x i j, |(P x)⁻¹ i j| ≤ L)
    (hc : ∀ i j, HolderWith C r (fun x => P x i j)) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r (fun x => (P x)⁻¹ i j) := by
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le ?_)
  intro x _ y _
  have h :=
    Matrix.abs_inv_sub_inv_apply_le (hP x) (hP y) (hb x) (hb y)
      (fun a b => by simpa only [Real.dist_eq] using (hc a b).dist_le x y) i j
  simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, mul_assoc] using
    h

omit [Fintype ι] [DecidableEq ι] in
/--
For `t ∈ [0, 1]`, the entries of `(1 − t) P + t Q` are `(C, r)`-Hölder when those of `P` and `Q`
are. -/
theorem holderWith_one_sub_smul_add_smul_apply (P Q : X → Matrix ι ι ℝ) (C r : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j)) {t : ℝ} (ht : t ∈ Icc 0 1) (i j : ι) :
    HolderWith C r (fun x => ((1 - t) • P x + t • Q x) i j) := by
  have h := ((hP i j).smul (1 - t)).add ((hQ i j).smul t)
  have heq : C * ‖1 - t‖₊ + C * ‖t‖₊ = C := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnNorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    ring
  rw [heq] at h
  convert h using 1
  funext x
  simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]

omit [DecidableEq ι] in
/-- If the entries of the matrix fields `A` and `W` are Hölder and bounded on `s`, then so are
the entries of `Wᵀ A W`, with constants depending only on `card ι` and those of `A` and `W`. -/
theorem holderOnWith_transpose_mul_mul_apply {s : Set X} {A W : X → Matrix ι ι ℝ}
    {α KA KW MA MW : ℝ≥0} (hA : ∀ i j, HolderOnWith KA α (fun y => A y i j) s)
    (hW : ∀ i j, HolderOnWith KW α (fun y => W y i j) s)
    (hMA : ∀ y ∈ s, ∀ i j, |A y i j| ≤ MA) (hMW : ∀ y ∈ s, ∀ i j, |W y i j| ≤ MW) (k l : ι) :
    HolderOnWith (Fintype.card ι * (Fintype.card ι * (MW * MA) * KW +
        MW * (Fintype.card ι * (MW * KA + MA * KW)))) α
        (fun y => ((W y)ᵀ * A y * W y) k l) s ∧
      ∀ y ∈ s, |((W y)ᵀ * A y * W y) k l| ≤
        ((Fintype.card ι * (Fintype.card ι * (MW * MA) * MW) : ℝ≥0) : ℝ) := by
  -- The inner sums `∑ᵢ Wᵢₖ Aᵢⱼ` and their bounds.
  have h1 (j : ι) := HolderOnWith.fintype_sum fun i =>
    (hW i k).smul_of_norm_le (hA i j) (fun y hy => hMW y hy i k) fun y hy => hMA y hy i j
  have h1b (j : ι) (y : X) (hy : y ∈ s) :
      ‖∑ i, W y i k * A y i j‖ ≤ ((Fintype.card ι * (MW * MA) : ℝ≥0) : ℝ) :=
    calc ‖∑ i, W y i k * A y i j‖ ≤ ∑ _ : ι, (MW * MA : ℝ) :=
          norm_sum_le_of_le _ fun i _ => by
            rw [norm_mul]
            exact mul_le_mul (hMW y hy i k) (hMA y hy i j) (norm_nonneg _) MW.coe_nonneg
      _ = _ := by simp
  have h2 := HolderOnWith.fintype_sum fun j =>
    (h1 j).smul_of_norm_le (hW j l) (h1b j) fun y hy => hMW y hy j l
  refine ⟨h2.congr fun y _ => ?_, fun y hy => ?_⟩
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, ← Real.norm_eq_abs]
    calc ‖∑ j, (∑ i, W y i k * A y i j) * W y j l‖ ≤
          ∑ _ : ι, ((Fintype.card ι * (MW * MA) : ℝ≥0) : ℝ) * MW :=
          norm_sum_le_of_le _ fun j _ => by
            rw [norm_mul]
            exact mul_le_mul (h1b j y hy) (hMW y hy j l) (norm_nonneg _) (by positivity)
      _ = _ := by simp [mul_assoc]

end TauCeti
