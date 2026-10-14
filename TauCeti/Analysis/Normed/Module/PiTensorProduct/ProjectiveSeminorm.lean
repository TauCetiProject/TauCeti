/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm

/-!
# Projective tensor seminorms for arbitrary seminorms

For a finite family of modules and a seminorm on each factor, `projectiveSeminormOf`
is the largest seminorm whose value on a pure tensor is bounded by the product of the
factor seminorms. Its characteristic formula uses finite sums of scalar multiples of
pure tensors, so it also covers the empty family, whose tensor product is the scalar field.

The construction reuses Mathlib's `PiTensorProduct.projectiveSeminorm` from
`Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm`, by temporarily giving
each factor the seminormed structure induced by its chosen seminorm. No topology or
separation assumption on the original modules is required. The universal seminorm bound,
monotonicity and functorial estimate supply the estimates used to form locally convex
projective tensor topologies. Hausdorff completion and its continuous universal property
are separate constructions.

The universal estimate adapts the weighted-decomposition argument of Mathlib's
`PiTensorProduct.norm_eval_le_projectiveSeminorm` to an arbitrary target seminorm and
an explicit bound, without using an operator norm or a nontrivially normed field.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {ι 𝕜 : Type*} [Fintype ι] [NormedField 𝕜]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]

/-- The projective seminorm associated to one seminorm on each tensor factor. -/
noncomputable def projectiveSeminormOf (p : ∀ i, Seminorm 𝕜 (E i)) :
    Seminorm 𝕜 (⨂[𝕜] i, E i) := by
  letI : ∀ i, SeminormedAddCommGroup (E i) :=
    fun i => (p i).toAddGroupSeminorm.toSeminormedAddCommGroup
  letI : ∀ i, NormedSpace 𝕜 (E i) :=
    fun i => ⟨fun a x => (map_smul_eq_mul (p i) a x).le⟩
  exact projectiveSeminorm

/-- The projective seminorm is the infimum of the costs of all weighted pure-tensor
decompositions. Retaining scalar coefficients makes the formula valid for an empty family. -/
theorem projectiveSeminormOf_apply (p : ∀ i, Seminorm 𝕜 (E i)) (x : ⨂[𝕜] i, E i) :
    projectiveSeminormOf p x =
      ⨅ l : lifts x, (l.val.toList.map (fun a => ‖a.1‖ * ∏ i, p i (a.2 i))).sum := by
  rfl

/-- A pure tensor has projective seminorm at most the product of the factor seminorms. -/
theorem projectiveSeminormOf_tprod_le (p : ∀ i, Seminorm 𝕜 (E i)) (m : ∀ i, E i) :
    projectiveSeminormOf p (⨂ₜ[𝕜] i, m i) ≤ ∏ i, p i (m i) := by
  let : ∀ i, SeminormedAddCommGroup (E i) :=
    fun i => (p i).toAddGroupSeminorm.toSeminormedAddCommGroup
  let : ∀ i, NormedSpace 𝕜 (E i) :=
    fun i => ⟨fun a x => (map_smul_eq_mul (p i) a x).le⟩
  exact projectiveSeminorm_tprod_le m

/-- A bound for a tensor seminorm on pure tensors extends with the same nonnegative constant
to all tensors. This includes degenerate factor seminorms and the constant zero. -/
theorem seminorm_le_mul_projectiveSeminormOf (p : ∀ i, Seminorm 𝕜 (E i))
    (q : Seminorm 𝕜 (⨂[𝕜] i, E i)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ m : ∀ i, E i, q (⨂ₜ[𝕜] i, m i) ≤ C * ∏ i, p i (m i))
    (x : ⨂[𝕜] i, E i) :
    q x ≤ C * projectiveSeminormOf p x := by
  rw [projectiveSeminormOf_apply, Real.mul_iInf_of_nonneg hC]
  refine le_ciInf fun ⟨l, hl⟩ => ?_
  conv_lhs => rw [← (mem_lifts_iff x l).mp hl, ← Multiset.sum_coe]
  let := q.toAddGroupSeminorm.toSeminormedAddCommGroup
  have qnorm (z : ⨂[𝕜] i, E i) : ‖z‖ = q z := (rfl)
  refine (norm_multiset_sum_le (E := ⨂[𝕜] i, E i) _).trans ?_
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  refine List.Forall₂.sum_le_sum ?_
  simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro a ha
  simpa [qnorm, map_smul_eq_mul, mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left (h a.2) (norm_nonneg a.1)

/-- The projective seminorm is the largest seminorm bounded by the prescribed product
on pure tensors. -/
theorem le_projectiveSeminormOf_iff (p : ∀ i, Seminorm 𝕜 (E i))
    (q : Seminorm 𝕜 (⨂[𝕜] i, E i)) :
    q ≤ projectiveSeminormOf p ↔
      ∀ m : ∀ i, E i, q (⨂ₜ[𝕜] i, m i) ≤ ∏ i, p i (m i) := by
  constructor
  · intro h m
    exact (h _).trans (projectiveSeminormOf_tprod_le p m)
  · intro h x
    simpa using seminorm_le_mul_projectiveSeminormOf p q (C := 1) zero_le_one
      (by simpa using h) x

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F]

/-- A product-seminorm bound for a multilinear map extends to its canonical tensor lift
without enlarging the constant or requiring continuity hypotheses. -/
theorem seminorm_lift_le (p : ∀ i, Seminorm 𝕜 (E i)) (q : Seminorm 𝕜 F)
    (f : MultilinearMap 𝕜 E F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ m, q (f m) ≤ C * ∏ i, p i (m i)) (x : ⨂[𝕜] i, E i) :
    q (lift f x) ≤ C * projectiveSeminormOf p x :=
  seminorm_le_mul_projectiveSeminormOf p (q.comp (lift f)) hC (by simpa using h) x

/-- Increasing any factor seminorm increases the projective seminorm. -/
theorem projectiveSeminormOf_mono {p q : ∀ i, Seminorm 𝕜 (E i)} (h : ∀ i, p i ≤ q i) :
    projectiveSeminormOf p ≤ projectiveSeminormOf q := by
  apply (le_projectiveSeminormOf_iff q _).mpr
  intro m
  refine (projectiveSeminormOf_tprod_le p m).trans ?_
  exact Finset.prod_le_prod₀ (fun i _ => apply_nonneg (p i) _) (fun i _ => h i _)

variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module 𝕜 (G i)]

/-- Tensoring seminorm-bounded linear maps gives the product of their bounds. The input and
output factor seminorms may be unrelated to any previously chosen topology. -/
theorem projectiveSeminormOf_map_le (p : ∀ i, Seminorm 𝕜 (E i))
    (q : ∀ i, Seminorm 𝕜 (G i)) (f : ∀ i, E i →ₗ[𝕜] G i)
    {C : ι → ℝ} (hC : ∀ i, 0 ≤ C i) (h : ∀ i x, q i (f i x) ≤ C i * p i x)
    (x : ⨂[𝕜] i, E i) :
    projectiveSeminormOf q (map f x) ≤ (∏ i, C i) * projectiveSeminormOf p x := by
  apply seminorm_le_mul_projectiveSeminormOf p ((projectiveSeminormOf q).comp (map f))
    (Finset.prod_nonneg fun i _ => hC i) _ x
  intro m
  simp only [Seminorm.comp_apply, map_tprod]
  refine (projectiveSeminormOf_tprod_le q _).trans ?_
  simpa [Finset.prod_mul_distrib] using
    Finset.prod_le_prod₀ (fun i _ => apply_nonneg (q i) _) (fun i _ => h i (m i))

end PiTensorProduct
