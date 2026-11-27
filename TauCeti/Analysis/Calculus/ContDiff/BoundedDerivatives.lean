/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply

/-!
# Smooth functions with bounded derivatives

The smooth functions with globally bounded derivatives of each order form a vector subspace
`TauCeti.smoothBoundedDerivatives` of `E → F`. Each derivative has its own bound; no common bound
across orders is required.

On a set `s`, the predicate `TauCeti.BddDerivOn 𝕜 k f s` asks that `f` be `Cᵏ` on `s` with its
derivatives of order at most `k` bounded on `s` by one constant. On an open set it passes to
directional derivatives, one order lower (`TauCeti.BddDerivOn.fderiv_apply`), and to scalar
multiples and finite sums. A function that is `Cᵏ` on a set of unique differentiability containing
the compact closure of an open set `s` has this property on `s`
(`ContDiffOn.bddDerivOn_of_isCompact_closure`).

## Main declarations

* `TauCeti.smoothBoundedDerivatives`: smooth functions with globally bounded derivatives.
* `TauCeti.BddDerivOn`: `Cᵏ` on a set, with derivatives of order at most `k` bounded there.
-/

public section

open scoped ContDiff

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

/-- Smooth functions whose derivatives of every order are globally bounded, as a subspace of
`E → F`. The bounds may depend on the derivative order. -/
def smoothBoundedDerivatives : Submodule 𝕜 (E → F) where
  carrier := {f | ContDiff 𝕜 ∞ f ∧ ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv 𝕜 m f x‖ ≤ C}
  zero_mem' := ⟨contDiff_const, fun m => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro f g ⟨hf, hfb⟩ ⟨hg, hgb⟩
    refine ⟨hf.add hg, fun m => ?_⟩
    obtain ⟨C, hC⟩ := hfb m
    obtain ⟨D, hD⟩ := hgb m
    refine ⟨C + D, fun x => ?_⟩
    rw [iteratedFDeriv_add_apply (hf.of_le (by simp)).contDiffAt
      (hg.of_le (by simp)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
  smul_mem' := by
    rintro c f ⟨hf, hfb⟩
    refine ⟨hf.const_smul c, fun m => ?_⟩
    obtain ⟨C, hC⟩ := hfb m
    refine ⟨‖c‖ * C, fun x => ?_⟩
    rw [iteratedFDeriv_const_smul_apply (hf.of_le (by simp)).contDiffAt, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

/-- Membership is smoothness together with a global bound for each derivative order. -/
@[simp]
theorem mem_smoothBoundedDerivatives {f : E → F} :
    f ∈ smoothBoundedDerivatives 𝕜 E F ↔
      ContDiff 𝕜 ∞ f ∧ ∀ m : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv 𝕜 m f x‖ ≤ C :=
  Iff.rfl

/-! ### Derivatives bounded on a set -/

section BddDerivOn

variable {𝕜 E F}
variable {s : Set E} {k l : ℕ} {f : E → F}

variable (𝕜) in
/-- `f` is `Cᵏ` on `s`, and its derivatives of order at most `k` are bounded on `s` by a common
constant. -/
def BddDerivOn (k : ℕ) (f : E → F) (s : Set E) : Prop :=
  ContDiffOn 𝕜 k f s ∧ ∃ C : ℝ, ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C

/-- Unfolding `TauCeti.BddDerivOn`. -/
theorem bddDerivOn_iff : BddDerivOn 𝕜 k f s ↔
    ContDiffOn 𝕜 k f s ∧ ∃ C : ℝ, ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C :=
  Iff.rfl

/-- A function with bounded derivatives up to order `k` on `s` is `Cᵏ` on `s`. -/
theorem BddDerivOn.contDiffOn (h : BddDerivOn 𝕜 k f s) : ContDiffOn 𝕜 k f s :=
  h.1

/-- The derivatives of order at most `k` have a common bound on `s`. -/
theorem BddDerivOn.exists_bound (h : BddDerivOn 𝕜 k f s) :
    ∃ C : ℝ, ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv 𝕜 i f x‖ ≤ C :=
  h.2

/-- A function with bounded derivatives up to order `k` on `s` is bounded on `s`. -/
theorem BddDerivOn.exists_norm_le (h : BddDerivOn 𝕜 k f s) : ∃ M : ℝ, ∀ x ∈ s, ‖f x‖ ≤ M :=
  h.2.imp fun _ hC x hx => by simpa only [norm_iteratedFDeriv_zero] using hC 0 k.zero_le x hx

/-- Bounded derivatives on `s` are bounded on every subset of `s`. -/
theorem BddDerivOn.mono {t : Set E} (h : BddDerivOn 𝕜 k f s) (hts : t ⊆ s) :
    BddDerivOn 𝕜 k f t :=
  ⟨h.1.mono hts, h.2.imp fun _ hC i hi x hx => hC i hi x (hts hx)⟩

/-- Bounded derivatives up to order `k` are bounded up to every order `l ≤ k`. -/
theorem BddDerivOn.of_le (h : BddDerivOn 𝕜 k f s) (hl : l ≤ k) : BddDerivOn 𝕜 l f s :=
  ⟨h.1.of_le (by exact_mod_cast hl), h.2.imp fun _ hC i hi => hC i (hi.trans hl)⟩

/-- On an open set, a directional derivative of a function with bounded derivatives up to order
`k + 1` has bounded derivatives up to order `k`. -/
theorem BddDerivOn.fderiv_apply (hs : IsOpen s) (h : BddDerivOn 𝕜 (k + 1) f s) (v : E) :
    BddDerivOn 𝕜 k (fun y => fderiv 𝕜 f y v) s := by
  obtain ⟨C, hC⟩ := h.2
  exact ⟨h.1.fderiv_apply_of_isOpen hs (by norm_cast) v, ‖v‖ * C, fun i hi x hx =>
    (h.1.norm_iteratedFDeriv_fderiv_apply_le hs v hi hx).trans
      (mul_le_mul_of_nonneg_left (hC (i + 1) (by omega) x hx) (norm_nonneg v))⟩

/-- On an open set, a constant multiple of a function with bounded derivatives has bounded
derivatives. -/
theorem BddDerivOn.const_smul (hs : IsOpen s) (h : BddDerivOn 𝕜 k f s) (c : 𝕜) :
    BddDerivOn 𝕜 k (fun x => c • f x) s := by
  obtain ⟨C, hC⟩ := h.2
  refine ⟨h.1.const_smul c, ‖c‖ * C, fun i hi x hx => ?_⟩
  rw [iteratedFDeriv_const_smul_apply'
    ((h.1.of_le (by exact_mod_cast hi)).contDiffAt (hs.mem_nhds hx)), norm_smul]
  exact mul_le_mul_of_nonneg_left (hC i hi x hx) (norm_nonneg c)

/-- On an open set, a finite sum of functions with bounded derivatives has bounded derivatives. -/
theorem BddDerivOn.sum {ι : Type*} {t : Finset ι} (hs : IsOpen s) {f : ι → E → F}
    (h : ∀ j ∈ t, BddDerivOn 𝕜 k (f j) s) : BddDerivOn 𝕜 k (fun x => ∑ j ∈ t, f j x) s := by
  choose C hC using fun j (hj : j ∈ t) => (h j hj).2
  refine ⟨ContDiffOn.sum fun j hj => (h j hj).1, ∑ j ∈ t.attach, C j.val j.property,
    fun i hi x hx => ?_⟩
  rw [iteratedFDeriv_fun_sum_apply fun j hj =>
    ((h j hj).1.of_le (by exact_mod_cast hi)).contDiffAt (hs.mem_nhds hx), ← Finset.sum_attach]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hC j.val j.property i hi x hx)

end BddDerivOn

end TauCeti

/-- **Bounded derivatives from compact closure.** If `f` is `Cᵏ` on a set `U` of unique
differentiability containing the compact closure of an open set `s`, then the derivatives of `f`
of order at most `k` are bounded on `s`. -/
theorem ContDiffOn.bddDerivOn_of_isCompact_closure {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {U s : Set E} {k : ℕ} (hf : ContDiffOn 𝕜 k f U) (hU : UniqueDiffOn 𝕜 U)
    (hs : IsOpen s) (hcpt : IsCompact (closure s)) (hsU : closure s ⊆ U) :
    TauCeti.BddDerivOn 𝕜 k f s := by
  -- The derivatives within `U` have a common bound on the compact set `closure s`.
  obtain ⟨A, hA⟩ := hf.exists_bound_iteratedFDerivWithin hU hcpt hsU
  refine ⟨hf.mono (subset_closure.trans hsU), A, fun i hi x hx => ?_⟩
  -- On the open set `s ⊆ U`, the derivative within `U` is the derivative.
  have hxU : U =ᶠ[nhds x] (Set.univ : Set E) :=
    Filter.eventuallyEqSet_univ.2
      (Filter.mem_of_superset (hs.mem_nhds hx) (subset_closure.trans hsU))
  have h := hA i hi x (subset_closure hx)
  rwa [iteratedFDerivWithin_congr_set hxU, iteratedFDerivWithin_univ] at h
