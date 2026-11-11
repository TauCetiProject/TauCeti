/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Entrywise Hölder estimates for matrix fields

If an invertible real matrix field has `(C, r)`-Hölder entries and inverse entries bounded
by `L`, the inverse entries are `((card ι)² L² C, r)`-Hölder
(`TauCeti.holderWith_matrix_inv_apply`). For `t ∈ [0, 1]`, a convex combination of two fields
with the same entrywise Hölder bound retains that bound
(`TauCeti.holderWith_one_sub_smul_add_smul_apply`). These estimates apply to inverse segments
before their entries are averaged.

The estimates are adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

open Set
open scoped NNReal

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
    simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    ring
  rw [heq] at h
  convert h using 1
  funext x
  simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]

end TauCeti
