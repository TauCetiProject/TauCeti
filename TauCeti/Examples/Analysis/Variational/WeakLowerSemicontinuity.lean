/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.WeakSpace
public import TauCeti.Analysis.LocallyConvex.WeakSpace.Basic
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Topology.Semicontinuity.Sequences
import Mathlib.Analysis.Convex.Mul

/-!
# Checks: bounded sublevels and weak lower semicontinuity

The Checks of `TauCetiRoadmap/VariationalMethods/README.md` §1.1 and the first Check of §1.2.

On `ℝ`:

* `u²` has bounded sublevels (`hasBoundedSublevelsOn_sq`), while `u² − u⁴` does not: its
  sublevel `{u² − u⁴ ≤ 0}` contains every `u` with `|u| ≥ 1` (`not_hasBoundedSublevelsOn_sq_sub`);
* the sum of `u²` and `−u²` is `0`, whose sublevels are unbounded
  (`not_hasBoundedSublevelsOn_sq_add_neg_sq`), and `−u²` is not bounded below
  (`not_bddBelow_neg_sq`): the bounded-below hypothesis of
  `TauCeti.HasBoundedSublevelsOn.add_right_of_bddBelow` cannot be dropped.

On `ℓ²`, with the unit vectors `eₙ ⇀ 0` (`tendsto_toWeakSpace_e`):

* `−‖u‖` is norm continuous (`continuous_neg_norm`) but not sequentially weakly lower
  semicontinuous (`not_seqLowerSemicontinuous_neg_norm`), since `−‖eₙ‖ = −1 < 0`; the norm itself
  is weakly lower semicontinuous (`lowerSemicontinuous_norm`);
* `‖u‖²` is weakly lower semicontinuous (`lowerSemicontinuous_norm_sq`), while the concave
  `−‖u‖²` is not, even sequentially (`not_seqLowerSemicontinuous_neg_norm_sq`).
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti.VariationalChecks

/-! ### Bounded sublevels on `ℝ` -/

/-- `u²` has bounded sublevels on `ℝ`. -/
theorem hasBoundedSublevelsOn_sq : HasBoundedSublevelsOn (fun u : ℝ ↦ u ^ 2) univ := by
  refine hasBoundedSublevelsOn_iff.2 fun b ↦ ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := √|b|)).subset ?_
  rintro u ⟨-, hu⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact (Real.abs_le_sqrt hu).trans (Real.sqrt_le_sqrt (le_abs_self b))

/-- `u² − u⁴` does not have bounded sublevels on `ℝ`: `{u² − u⁴ ≤ 0}` contains `|u| ≥ 1`. -/
theorem not_hasBoundedSublevelsOn_sq_sub :
    ¬ HasBoundedSublevelsOn (fun u : ℝ ↦ u ^ 2 - u ^ 4) univ := by
  intro h
  obtain ⟨R, hR⟩ := (hasBoundedSublevelsOn_iff.1 h 0).subset_closedBall (0 : ℝ)
  have hu : |R| + 1 ∈ {u ∈ (univ : Set ℝ) | u ^ 2 - u ^ 4 ≤ 0} := by
    refine ⟨mem_univ _, ?_⟩
    have h1 : 1 ≤ |R| + 1 := by linarith [abs_nonneg R]
    nlinarith [mul_le_mul h1 h1 zero_le_one (by linarith)]
  have := hR hu
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_abs_self R, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |R| + 1)]

/-- The sum of `u²` and `−u²` does not have bounded sublevels on `ℝ`. -/
theorem not_hasBoundedSublevelsOn_sq_add_neg_sq :
    ¬ HasBoundedSublevelsOn (fun u : ℝ ↦ u ^ 2 + -u ^ 2) univ := by
  intro h
  have h0 := hasBoundedSublevelsOn_iff.1 h 0
  have hU : {u ∈ (univ : Set ℝ) | u ^ 2 + -u ^ 2 ≤ 0} = univ := by ext; simp
  rw [hU] at h0
  exact NormedSpace.unbounded_univ ℝ ℝ h0

/-- `−u²` is not bounded below on `ℝ`. -/
theorem not_bddBelow_neg_sq : ¬ BddBelow (range fun u : ℝ ↦ -u ^ 2) := by
  rintro ⟨m, hm⟩
  have := hm ⟨|m| + 1, rfl⟩
  nlinarith [le_abs_self m, neg_abs_le m, abs_nonneg m]

/-! ### Weak lower semicontinuity on `ℓ²` -/

/-- The unit vectors of `ℓ²`, as a Hilbert basis. -/
noncomputable def e : HilbertBasis ℕ ℝ (lp (fun _ : ℕ ↦ ℝ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)

/-- The `n`-th vector of `e` is the `n`-th unit vector of `ℓ²`. -/
theorem e_apply (n : ℕ) : e n = lp.single 2 n (1 : ℝ) := by
  classical
  exact ((HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ
    (lp (fun _ : ℕ ↦ ℝ) 2))).repr_symm_single n).symm

/-- The unit vectors of `ℓ²` converge weakly to `0`. -/
theorem tendsto_toWeakSpace_e :
    Tendsto (fun n ↦ toWeakSpace ℝ _ (e n)) atTop (𝓝 (toWeakSpace ℝ _ 0)) :=
  e.orthonormal.tendsto_toWeakSpace_atTop

/-- A function on the weak topology of `ℓ²` that is negative on every `eₙ` and vanishes at `0`
is not sequentially lower semicontinuous. -/
theorem not_seqLowerSemicontinuous_of_lt {f : lp (fun _ : ℕ ↦ ℝ) 2 → ℝ} {c : ℝ} (hc : c < 0)
    (hf0 : f 0 = 0) (hfe : ∀ n, f (e n) ≤ c) :
    ¬ SeqLowerSemicontinuous fun w : WeakSpace ℝ (lp (fun _ : ℕ ↦ ℝ) 2) ↦
      f ((toWeakSpace ℝ _).symm w) := by
  intro h
  have hev := seqLowerSemicontinuousAt_iff.1 (seqLowerSemicontinuous_iff.1 h (toWeakSpace ℝ _ 0))
    tendsto_toWeakSpace_e (c / 2) (by simp [hf0]; linarith)
  obtain ⟨n, hn⟩ := hev.exists
  simp only [LinearEquiv.symm_apply_apply] at hn
  linarith [hfe n]

/-- `−‖u‖` is continuous for the norm topology of `ℓ²`. -/
theorem continuous_neg_norm : Continuous fun u : lp (fun _ : ℕ ↦ ℝ) 2 ↦ -‖u‖ :=
  continuous_norm.neg

/-- `−‖u‖` is not sequentially weakly lower semicontinuous on `ℓ²`: `eₙ ⇀ 0` while
`−‖eₙ‖ = −1 < 0`. -/
theorem not_seqLowerSemicontinuous_neg_norm :
    ¬ SeqLowerSemicontinuous fun w : WeakSpace ℝ (lp (fun _ : ℕ ↦ ℝ) 2) ↦
      -‖(toWeakSpace ℝ _).symm w‖ :=
  not_seqLowerSemicontinuous_of_lt (f := fun u ↦ -‖u‖) (c := -1) (by norm_num) (by simp)
    fun n ↦ by simp [e.orthonormal.1 n]

/-- The norm of `ℓ²` is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_norm :
    LowerSemicontinuous fun w : WeakSpace ℝ (lp (fun _ : ℕ ↦ ℝ) 2) ↦
      ‖(toWeakSpace ℝ _).symm w‖ :=
  QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm (convexOn_univ_norm.quasiconvexOn)
    continuous_norm.lowerSemicontinuous

/-- `‖u‖²` is weakly lower semicontinuous on `ℓ²`. -/
theorem lowerSemicontinuous_norm_sq :
    LowerSemicontinuous fun w : WeakSpace ℝ (lp (fun _ : ℕ ↦ ℝ) 2) ↦
      ‖(toWeakSpace ℝ _).symm w‖ ^ 2 :=
  QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
    (ConvexOn.pow convexOn_univ_norm (fun _ _ ↦ norm_nonneg _) 2).quasiconvexOn
    (continuous_norm.pow 2).lowerSemicontinuous

/-- The concave `−‖u‖²` is not sequentially weakly lower semicontinuous on `ℓ²`. -/
theorem not_seqLowerSemicontinuous_neg_norm_sq :
    ¬ SeqLowerSemicontinuous fun w : WeakSpace ℝ (lp (fun _ : ℕ ↦ ℝ) 2) ↦
      -‖(toWeakSpace ℝ _).symm w‖ ^ 2 :=
  not_seqLowerSemicontinuous_of_lt (f := fun u ↦ -‖u‖ ^ 2) (c := -1) (by norm_num) (by simp)
    fun n ↦ by simp [e.orthonormal.1 n]

end TauCeti.VariationalChecks
