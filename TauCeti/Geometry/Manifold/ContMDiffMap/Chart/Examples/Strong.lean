/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Strong
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms

/-!
# Strong Whitney neighbourhoods on `ℝ`, the circle and `ℝ ⊔ ℝ`

This file tests the strong Whitney topology `ContMDiffMap.manifoldStrongWhitneyTopology` on three
small manifolds, against the weak Whitney topology `ContMDiffMap.manifoldWeakWhitneyTopology`.

* **A tolerance tending to zero on `ℝ`.** For a `C^n` function `f` on `ℝ`, the functions `g` with
  `|g x - f x| < exp (-x²)` at every point form a strong neighbourhood of `f`
  (`ContMDiffMap.setOf_forall_abs_sub_lt_exp_neg_sq_mem_nhds_manifoldStrongWhitney`), an instance
  of `ContMDiffMap.setOf_forall_norm_sub_lt_mem_nhds_manifoldStrongWhitney`. It contains no
  perturbation `f + a` of `f` by a nonzero constant
  (`ContMDiffMap.add_const_mem_setOf_forall_abs_sub_lt_exp_neg_sq_iff`), and so it is not a weak
  neighbourhood (`ContMDiffMap.setOf_forall_abs_sub_lt_exp_neg_sq_notMem_nhds_manifoldWeakWhitney`):
  every weak neighbourhood of `f` contains `f + a` for all small `a`. The weak neighbourhood which
  asks for the same bound on `[-1, 1]` only
  (`ContMDiffMap.setOf_forall_mem_Icc_abs_sub_lt_exp_neg_sq_mem_nhds_manifoldWeakWhitney`)
  contains `f + a` whenever `|a| < exp (-1)`
  (`ContMDiffMap.add_const_mem_setOf_forall_mem_Icc_abs_sub_lt_exp_neg_sq`).
* **The circle.** The circle is compact, so the controls with finitely many compact coordinate
  sets already give a basis of strong neighbourhoods
  (`ContMDiffMap.hasBasis_nhds_manifoldStrongWhitney_finite`). A tolerance `ε` on a coordinate
  set bounds the difference of the values by `ε` there
  (`ContMDiffMap.StrongCkControl.norm_sub_lt_of_mem_ball`), as well as that of the coordinate
  derivatives through the order of the control
  (`ContMDiffMap.StrongCkControl.mem_ball_iff_forall_norm_sub_lt`).
* **A clopen summand.** The left summand of `ℝ ⊔ ℝ` is open and closed, so a locally finite family
  of compact coordinate sets in it stays locally finite in `ℝ ⊔ ℝ`, and restriction to it is
  continuous for the strong topologies (`ContMDiffMap.continuous_restrict_manifoldStrongWhitney`).
  By contrast, restriction from `ℝ` to `(0, 1)` is not
  (`ContMDiffMap.not_continuous_restrict_Ioo_manifoldStrongWhitney`).

On a single point the strong topology is the topology of the values
(`ContMDiffMap.isHomeomorph_eval_manifoldStrongWhitney`).

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, pp. 34–36, for the weak and strong
  `C^r` topologies.
-/

public section

open Set Filter Topology TopologicalSpace
open scoped Manifold

namespace ContMDiffMap

variable {n : WithTop ℕ∞}

/-! ### A tolerance tending to zero on `ℝ` -/

section Real

/-- The value of a perturbation of a function on `ℝ` by a constant. -/
private theorem add_const_apply_sub (f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) (a x : ℝ) :
    (f + const a : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) x - f x = a := by
  simp [const_apply]

/-- The tolerance `exp (-x²)` falls below any positive bound. -/
private theorem exists_exp_neg_sq_le {a : ℝ} (ha : 0 < a) : ∃ x : ℝ, Real.exp (-x ^ 2) ≤ a := by
  refine ⟨Real.sqrt |Real.log a|, ?_⟩
  rw [Real.sq_sqrt (abs_nonneg _)]
  calc Real.exp (-|Real.log a|) ≤ Real.exp (Real.log a) :=
        Real.exp_le_exp.mpr (by linarith [neg_abs_le (Real.log a)])
    _ = a := Real.exp_log ha

/-- **The functions within `exp (-x²)` of `f` form a strong neighbourhood of `f`.** -/
theorem setOf_forall_abs_sub_lt_exp_neg_sq_mem_nhds_manifoldStrongWhitney
    (f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) :
    {g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ | ∀ x, |g x - f x| < Real.exp (-x ^ 2)} ∈
      @nhds _ manifoldStrongWhitneyTopology f := by
  simpa only [Real.norm_eq_abs] using
    setOf_forall_norm_sub_lt_mem_nhds_manifoldStrongWhitney f (by fun_prop)
      fun x ↦ Real.exp_pos (-x ^ 2)

/-- **The tolerance `exp (-x²)` excludes every nonzero constant perturbation.** -/
theorem add_const_mem_setOf_forall_abs_sub_lt_exp_neg_sq_iff (f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯)
    (a : ℝ) :
    f + const a ∈ {g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ | ∀ x, |g x - f x| < Real.exp (-x ^ 2)} ↔
      a = 0 := by
  simp only [mem_ofPred_eq, add_const_apply_sub]
  refine ⟨fun h ↦ ?_, fun ha x ↦ by simpa [ha] using Real.exp_pos (-x ^ 2)⟩
  by_contra ha
  obtain ⟨x, hx⟩ := exists_exp_neg_sq_le (abs_pos.mpr ha)
  exact (h x).not_ge hx

open scoped TauCeti.ManifoldWeakWhitney in
/-- **The functions within `exp (-x²)` of `f` do not form a weak neighbourhood of `f`**: every weak
neighbourhood contains the perturbations of `f` by small nonzero constants. -/
theorem setOf_forall_abs_sub_lt_exp_neg_sq_notMem_nhds_manifoldWeakWhitney
    (f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) :
    {g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ | ∀ x, |g x - f x| < Real.exp (-x ^ 2)} ∉
      @nhds _ manifoldWeakWhitneyTopology f := by
  intro hS
  -- The perturbations `f + δ` tend to `f` in the weak topology as `δ → 0`.
  have hcont : Continuous fun δ : ℝ ↦ f + δ • (const 1 : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun δ : ℝ ↦ f + δ • (const 1 : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯)) (𝓝[≠] 0) (𝓝 f) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hδ0⟩ := ((ht.eventually hS).and self_mem_nhdsWithin).exists
  have hconst : δ • (const 1 : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) = const δ :=
    ContMDiffMap.ext fun _ ↦ by simp [const_apply]
  rw [hconst] at hδ
  exact hδ0 ((add_const_mem_setOf_forall_abs_sub_lt_exp_neg_sq_iff f δ).mp hδ)

/-- The functions within `exp (-x²)` of `f` on `[-1, 1]` form a weak neighbourhood of `f`. -/
theorem setOf_forall_mem_Icc_abs_sub_lt_exp_neg_sq_mem_nhds_manifoldWeakWhitney
    (f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯) :
    {g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ | ∀ x ∈ Icc (-1) 1, |g x - f x| < Real.exp (-x ^ 2)} ∈
      @nhds _ manifoldWeakWhitneyTopology f := by
  have h := eventually_forall_dist_lt f (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    (δ := fun x ↦ Real.exp (-x ^ 2)) (by fun_prop) fun x _ ↦ Real.exp_pos (-x ^ 2)
  simp only [Real.dist_eq] at h
  exact h

/-- **The weak neighbourhood controlling `[-1, 1]` only contains nonzero constant
perturbations.** -/
theorem add_const_mem_setOf_forall_mem_Icc_abs_sub_lt_exp_neg_sq (f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯)
    {a : ℝ} (ha : |a| < Real.exp (-1)) :
    f + const a ∈
      {g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ | ∀ x ∈ Icc (-1) 1, |g x - f x| < Real.exp (-x ^ 2)} := by
  intro x hx
  rw [add_const_apply_sub]
  refine ha.trans_le (Real.exp_le_exp.mpr (neg_le_neg ?_))
  nlinarith [hx.1, hx.2]

end Real

/-! ### The circle and a clopen summand -/

/-- On the compact circle finitely many compact coordinate sets give a basis of strong
neighbourhoods. -/
example (f : C^n⟮𝓡 1, Circle; 𝓘(ℝ), ℝ⟯) :
    (@nhds _ manifoldStrongWhitneyTopology f).HasBasis
      (fun c : StrongCkControl (𝓡 1) Circle n ↦ Finite c.ι) fun c ↦ c.ball f :=
  hasBasis_nhds_manifoldStrongWhitney_finite f

/-- Restriction to the clopen left summand of `ℝ ⊔ ℝ` is continuous for the strong topologies. -/
example :
    Continuous[manifoldStrongWhitneyTopology, manifoldStrongWhitneyTopology]
      fun f : C^n⟮𝓘(ℝ), ℝ ⊕ ℝ; 𝓘(ℝ), ℝ⟯ ↦ f.restrict ⟨range Sum.inl, isOpen_range_inl⟩ :=
  continuous_restrict_manifoldStrongWhitney _ isClosed_range_inl

end ContMDiffMap
