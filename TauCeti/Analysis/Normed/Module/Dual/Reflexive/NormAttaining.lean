/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Module.Dual.JamesBoundary
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian

/-!
# Norm-attaining functionals and James's theorem for separable spaces

A continuous linear functional `f` on a real or complex normed space `E` *attains its norm* if
`‖f x‖ = ‖f‖` for some `x` in the closed unit ball. Every functional on a reflexive space attains
its norm (`TauCeti.exists_norm_le_one_apply_eq_norm_of_surjective_inclusionInDoubleDual`).

When every functional on `E` attains its norm, the canonical image of the closed unit ball of `E`
in the bidual is a James boundary of `StrongDual 𝕜 E`, so the Rainwater–Simons theorem shows that
a bounded sequence of functionals converging weak-star also converges weakly
(`TauCeti.tendsto_toWeakSpace_strongDual_of_tendsto_apply`).

For a separable Banach space this gives **James's theorem**
(`TauCeti.surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm`): the space is
reflexive if and only if every continuous linear functional attains its norm on the closed unit
ball. Indeed, the sequential Banach–Alaoglu theorem makes the dual unit ball weak-star
sequentially compact, hence weakly sequentially compact, hence weakly compact by the
Eberlein–Šmulian theorem; so the dual, and with it the space, is reflexive.

## References

* R. C. James, *Characterizations of reflexivity*, Studia Math. **23** (1964), 205–216.
* S. Simons, *A convergence theorem with boundary*, Pacific J. Math. **40** (1972), 703–708.
* M. Fabian, P. Habala, P. Hájek, V. Montesinos and V. Zizler, *Banach Space Theory*,
  CMS Books in Mathematics, Springer (2011), Chapter 3.
-/

public section

open Bornology Filter Function Metric NormedSpace RCLike Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A functional attains its norm on the closed unit ball, up to a unimodular factor, exactly
when it takes the value `‖f‖` there. -/
theorem _root_.StrongDual.exists_norm_le_one_apply_eq_norm_iff (f : StrongDual 𝕜 E) :
    (∃ x : E, ‖x‖ ≤ 1 ∧ f x = ‖f‖) ↔ ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  refine ⟨fun ⟨x, hx, hfx⟩ ↦ ⟨x, hx, by simp [hfx]⟩, fun ⟨x, hx, hfx⟩ ↦ ?_⟩
  by_cases h0 : f x = 0
  · exact ⟨0, by simp, by rw [map_zero, ← hfx, h0, norm_zero, ofReal_zero]⟩
  refine ⟨((‖f x‖ / f x : 𝕜)) • x, ?_, ?_⟩
  · rw [norm_smul, norm_div, norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.2 h0), one_mul]
    exact hx
  · rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h0, hfx]

/-- Every continuous linear functional on a reflexive space takes the value `‖f‖` at some point
of the closed unit ball. -/
theorem exists_norm_le_one_apply_eq_norm_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) (f : StrongDual 𝕜 E) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ f x = ‖f‖ := by
  obtain ⟨Φ, hΦ, hΦf⟩ := exists_dual_vector'' 𝕜 f
  obtain ⟨x, rfl⟩ := hE Φ
  refine ⟨x, ?_, hΦf⟩
  rwa [← (inclusionInDoubleDualLi 𝕜 (E := E)).norm_map x]

end Seminormed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If every functional on `E` attains its norm on the closed unit ball, then a bounded sequence
of functionals that converges pointwise (weak-star) also converges weakly in `StrongDual 𝕜 E`.

This is the Rainwater–Simons theorem for the James boundary formed by the canonical image of the
closed unit ball of `E` in the bidual. -/
theorem tendsto_toWeakSpace_strongDual_of_tendsto_apply
    (hE : ∀ f : StrongDual 𝕜 E, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖)
    {u : ℕ → StrongDual 𝕜 E} (hu : IsBounded (range u)) {f : StrongDual 𝕜 E}
    (h : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (u n)) atTop
      (𝓝 (toWeakSpace 𝕜 (StrongDual 𝕜 E) f)) := by
  refine tendsto_toWeakSpace_of_forall_mem_tendsto
    (Y := StrongDual 𝕜 E) (B := inclusionInDoubleDual 𝕜 E '' closedBall 0 1) ?_ ?_ hu ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (double_dual_bound 𝕜 E x).trans (mem_closedBall_zero_iff.1 hx)
  · intro g
    obtain ⟨x, hx, hgx⟩ := g.exists_norm_le_one_apply_eq_norm_iff.2 (hE g)
    exact ⟨_, mem_image_of_mem _ (mem_closedBall_zero_iff.2 hx), by simp [dual_def, hgx]⟩
  · rintro _ ⟨x, -, rfl⟩
    simpa only [dual_def] using h x

section Separable

variable [TopologicalSpace.SeparableSpace E]

/-- In a separable space all of whose functionals attain their norms, the closed unit ball of
the dual is weakly compact. -/
theorem isCompact_toWeakSpace_closedBall_strongDual_of_forall_exists_norm_apply_eq_norm
    (hE : ∀ f : StrongDual 𝕜 E, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖) :
    IsCompact (toWeakSpace 𝕜 (StrongDual 𝕜 E) '' closedBall 0 1) := by
  refine (isCompact_toWeakSpace_iff_isSeqCompact (𝕜 := 𝕜) (E := StrongDual 𝕜 E)).2
    fun a ha ↦ ?_
  choose u hu hua using ha
  obtain ⟨φ, hφ, σ, hσ, hlim⟩ := WeakDual.isSeqCompact_closedBall (𝕜 := 𝕜) (E := E) 0 1
    (x := fun n ↦ StrongDual.toWeakDual (u n)) fun n ↦ hu n
  refine ⟨_, mem_image_of_mem _ hφ, σ, hσ, ?_⟩
  simp only [comp_def, ← hua]
  refine tendsto_toWeakSpace_strongDual_of_tendsto_apply hE ?_ fun x ↦ ?_
  · refine (isBounded_closedBall (x := (0 : StrongDual 𝕜 E)) (r := 1)).subset ?_
    rintro _ ⟨n, rfl⟩
    exact hu (σ n)
  · exact ((WeakDual.eval_continuous x).tendsto φ).comp hlim

/-- **James's theorem** for separable spaces. A separable real or complex Banach space is
reflexive if and only if every continuous linear functional attains its norm on the closed unit
ball. -/
theorem surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm
    [CompleteSpace E] :
    Surjective (inclusionInDoubleDual 𝕜 E) ↔
      ∀ f : StrongDual 𝕜 E, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  refine ⟨fun hE f ↦ f.exists_norm_le_one_apply_eq_norm_iff.1
    (exists_norm_le_one_apply_eq_norm_of_surjective_inclusionInDoubleDual hE f), fun hE ↦ ?_⟩
  exact surjective_inclusionInDoubleDual_of_strongDual
    (surjective_inclusionInDoubleDual_of_isCompact_toWeakSpace_closedBall
      (isCompact_toWeakSpace_closedBall_strongDual_of_forall_exists_norm_apply_eq_norm hE))

end Separable

end TauCeti
