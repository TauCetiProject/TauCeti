/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform bounds for derivatives of families

A family has uniform jets through order n on a set when each derivative up to that order
has one operator-norm bound shared by all members and evaluation points. Bounds are
preserved by pairing, composition, reindexing and differentiation. Smooth maps have such
bounds on compact sets. Smoothness is assumed at the evaluation points when needed;
the predicate itself records only bounds. This is a quantitative prerequisite for coordinate
transition estimates in pointed smooth Ricci-flow convergence.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {ι E F G : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- Each derivative through order `n` has a bound shared by the family on `s`. -/
def HasUniformJetBoundsOn (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (n : ℕ) (s : Set E) (f : ι → E → F) : Prop :=
  ∀ m : ℕ, m ≤ n → ∃ C : ℝ, ∀ i x, x ∈ s →
    ‖iteratedFDeriv 𝕜 m (f i) x‖ ≤ C

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- Characterize uniform jet bounds by bounds at each derivative order. -/
theorem hasUniformJetBoundsOn_iff {n : ℕ} {s : Set E} {f : ι → E → F} :
    HasUniformJetBoundsOn 𝕜 n s f ↔ ∀ m : ℕ, m ≤ n → ∃ C : ℝ,
      ∀ i x, x ∈ s → ‖iteratedFDeriv 𝕜 m (f i) x‖ ≤ C := Iff.rfl

/-- Order-zero jet bounds are uniform bounds on the values. -/
@[simp]
theorem hasUniformJetBoundsOn_zero_iff {s : Set E} {f : ι → E → F} :
    HasUniformJetBoundsOn 𝕜 0 s f ↔ ∃ C : ℝ, ∀ i x, x ∈ s → ‖f i x‖ ≤ C := by
  simp only [hasUniformJetBoundsOn_iff, Nat.le_zero, forall_eq, norm_iteratedFDeriv_zero]

/-- Restrict a uniformly bounded jet family to a smaller evaluation set. -/
theorem HasUniformJetBoundsOn.mono {n : ℕ} {s t : Set E} {f : ι → E → F} (hst : s ⊆ t)
    (h : HasUniformJetBoundsOn 𝕜 n t f) : HasUniformJetBoundsOn 𝕜 n s f := by
  intro m hm
  obtain ⟨C, hC⟩ := h m hm
  exact ⟨C, fun i x hx ↦ hC i x (hst hx)⟩

/-- A bound through one order includes every smaller finite order. -/
theorem HasUniformJetBoundsOn.mono_order {m n : ℕ} {s : Set E} {f : ι → E → F}
    (hmn : m ≤ n) (h : HasUniformJetBoundsOn 𝕜 n s f) : HasUniformJetBoundsOn 𝕜 m s f := by
  intro j hj
  exact h j (hj.trans hmn)

/-- Choose a nonnegative bound for one derivative order on the evaluation set. -/
theorem HasUniformJetBoundsOn.bound_nonneg {n : ℕ} {s : Set E} {f : ι → E → F}
    (h : HasUniformJetBoundsOn 𝕜 n s f)
    {m : ℕ} (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ s →
      ‖iteratedFDeriv 𝕜 m (f i) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := h m hm
  refine ⟨max C 0, le_max_right _ _, fun i x hx ↦ (hC i x hx).trans (le_max_left _ _)⟩

/-- One nonnegative constant controls all derivative orders through a fixed finite order. -/
theorem HasUniformJetBoundsOn.bound_all {n : ℕ} {s : Set E} {f : ι → E → F}
    (h : HasUniformJetBoundsOn 𝕜 n s f) {m : ℕ} (hm : m ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ m → ∀ i x, x ∈ s →
      ‖iteratedFDeriv 𝕜 j (f i) x‖ ≤ C := by
  classical
  choose c hc using fun j : Finset.range (m + 1) ↦ h j.1
    (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.1 j.2)) hm)
  let C : ℝ := ∑ j : Finset.range (m + 1), max (c j) 0
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ ↦ le_max_right _ _)
  refine ⟨C, hC, fun j hj i x hx ↦ ?_⟩
  have hj' : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hs : max (c ⟨j, hj'⟩) 0 ≤ C :=
    Finset.single_le_sum (fun k _ ↦ le_max_right _ _) (Finset.mem_univ _)
  exact (hc ⟨j, hj'⟩ i x hx).trans ((le_max_left _ _).trans hs)

/-- A value bound and derivative jets give one additional order on any set. -/
theorem HasUniformJetBoundsOn.succ_of_fderiv {n : ℕ} {s : Set E} {f : ι → E → F}
    (h0 : ∃ C : ℝ, ∀ i x, x ∈ s → ‖f i x‖ ≤ C)
    (h : HasUniformJetBoundsOn 𝕜 n s (fun i ↦ fderiv 𝕜 (f i))) :
    HasUniformJetBoundsOn 𝕜 (n + 1) s f := by
  intro m hm
  rcases m with _ | m
  · obtain ⟨C, hC⟩ := h0
    exact ⟨C, fun i x hx ↦ by rw [norm_iteratedFDeriv_zero]; exact hC i x hx⟩
  · obtain ⟨C, hC⟩ := h m (Nat.le_of_succ_le_succ hm)
    refine ⟨C, fun i x hx ↦ ?_⟩
    rw [← norm_iteratedFDeriv_fderiv]
    exact hC i x hx

/-- Bounds through order `n + 1` give bounds through order `n` for the Fréchet derivative family. -/
theorem HasUniformJetBoundsOn.fderiv {n : ℕ} {s : Set E} {f : ι → E → F}
    (h : HasUniformJetBoundsOn 𝕜 (n + 1) s f) :
    HasUniformJetBoundsOn 𝕜 n s (fun i ↦ fderiv 𝕜 (f i)) := by
  intro m hm
  obtain ⟨C, hC⟩ := h (m + 1) (Nat.add_le_add_right hm 1)
  refine ⟨C, fun i x hx ↦ ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hC i x hx

/-- Uniform derivative bounds are preserved by pairing families. -/
theorem HasUniformJetBoundsOn.prodMk {n : ℕ} {s : Set E}
    {f : ι → E → F} {g : ι → E → G}
    (hf : HasUniformJetBoundsOn 𝕜 n s f) (hg : HasUniformJetBoundsOn 𝕜 n s g)
    (hcf : ∀ i x, x ∈ s → ContDiffAt 𝕜 n (f i) x)
    (hcg : ∀ i x, x ∈ s → ContDiffAt 𝕜 n (g i) x) :
    HasUniformJetBoundsOn 𝕜 n s (fun i x ↦ (f i x, g i x)) := by
  intro m hm
  obtain ⟨Cf, hCf⟩ := hf m hm
  obtain ⟨Cg, hCg⟩ := hg m hm
  refine ⟨max Cf Cg, fun i x hx ↦ ?_⟩
  rw [iteratedFDeriv_prodMk (hcf i x hx) (hcg i x hx) (by exact_mod_cast hm),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le ((hCf i x hx).trans (le_max_left _ _))
    ((hCg i x hx).trans (le_max_right _ _))

/-- Uniform derivative bounds are preserved by composition on the mapped sets. Only smoothness at
the evaluation points is required. -/
theorem HasUniformJetBoundsOn.comp {n : ℕ} {U : Set E} {V : Set F}
    {f : ι → E → F} {g : ι → F → G}
    (hf : HasUniformJetBoundsOn 𝕜 n U f) (hg : HasUniformJetBoundsOn 𝕜 n V g)
    (hcf : ∀ i x, x ∈ U → ContDiffAt 𝕜 n (f i) x)
    (hcg : ∀ i y, y ∈ V → ContDiffAt 𝕜 n (g i) y)
    (hmap : ∀ i, MapsTo (f i) U V) :
    HasUniformJetBoundsOn 𝕜 n U (fun i ↦ g i ∘ f i) := by
  intro m hm
  obtain ⟨Af, hAf, hAf'⟩ := hf.bound_all hm
  obtain ⟨Ag, hAg, hAg'⟩ := hg.bound_all hm
  refine ⟨Nat.factorial m * Ag * (max Af 1) ^ m, fun i x hx ↦ ?_⟩
  apply norm_iteratedFDeriv_comp_le_of_contDiffAt
    ((hcg i (f i x) (hmap i hx)).of_le (by exact_mod_cast hm))
    ((hcf i x hx).of_le (by exact_mod_cast hm))
  · intro j hj
    exact hAg' j hj i (f i x) (hmap i hx)
  · intro j hj₁ hj
    exact (hAf' j hj i x hx).trans ((le_max_left Af 1).trans
      (le_self_pow₀ (le_max_right Af 1) (Nat.ne_of_gt hj₁)))

/-- Reindexing a family preserves its uniform derivative bounds. -/
theorem HasUniformJetBoundsOn.comp_index {n : ℕ} {s : Set E} {f : ι → E → F}
    (hf : HasUniformJetBoundsOn 𝕜 n s f) {κ : Type*} (a : κ → ι) :
    HasUniformJetBoundsOn 𝕜 n s (f ∘ a) := by
  intro m hm
  obtain ⟨C, hC⟩ := hf m hm
  exact ⟨C, fun i x hx ↦ hC (a i) x hx⟩

/-- A map smooth at every point of a compact set has uniformly bounded jets there. -/
theorem _root_.IsCompact.hasUniformJetBoundsOn {n : ℕ} {s : Set E} (hs : IsCompact s)
    {f : E → F} (hf : ∀ x ∈ s, ContDiffAt 𝕜 n f x) :
    HasUniformJetBoundsOn 𝕜 n s (fun _ : Unit ↦ f) := by
  intro m hm
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn
    (fun x hx ↦ ((hf x hx).continuousAt_iteratedFDeriv
      (by exact_mod_cast hm)).continuousWithinAt)
  exact ⟨C, fun _ x hx ↦ hC x hx⟩

/-- Eventual equality at every evaluation point preserves uniform derivative bounds. -/
theorem hasUniformJetBoundsOn_congr {n : ℕ} {s : Set E} {f g : ι → E → F}
    (hfg : ∀ i x, x ∈ s → f i =ᶠ[𝓝 x] g i) :
    HasUniformJetBoundsOn 𝕜 n s f ↔ HasUniformJetBoundsOn 𝕜 n s g := by
  constructor <;> intro h m hm <;> obtain ⟨C, hC⟩ := h m hm
  · refine ⟨C, fun i x hx ↦ ?_⟩
    rw [← ((hfg i x hx).iteratedFDeriv 𝕜 m).self_of_nhds]
    exact hC i x hx
  · refine ⟨C, fun i x hx ↦ ?_⟩
    rw [((hfg i x hx).iteratedFDeriv 𝕜 m).self_of_nhds]
    exact hC i x hx

end TauCeti
