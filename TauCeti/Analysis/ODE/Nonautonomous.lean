/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique
import TauCeti.Analysis.ODE.Gronwall.Interior

/-!
# Global solutions of state-Lipschitz nonautonomous ODEs

`ODE.globalSolution` solves autonomous initial value problems `γ' = v ∘ γ`, while
`TauCeti.timeDependentFlow` solves `γ' t = v t (γ t)` when the suspended map
`(t, x) ↦ (1, v t x)` is globally Lipschitz in both `t` and `x`. When `v` is driven by a sample
path `w` that is continuous in `t` but not Lipschitz—for instance `v t x = F (x + w t)` with `w` a
Brownian trajectory—the suspended field is not Lipschitz in time, yet global existence and
uniqueness still hold whenever `v` is continuous in `t` at each point and `K`-Lipschitz in `x` with
a constant `K` independent of `t`.

The construction steps Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`
along overlapping intervals of fixed half-width `δ = (4 (K + 1))⁻¹`. On `[c - 2 δ, c + 2 δ]` the
continuous curve `t ↦ ‖v t y‖` is bounded by some `a ≥ 0`, so on `closedBall y a` the field is
bounded by `L = (K + 1) a`, which satisfies `L · (2 δ) = a / 2 ≤ a` independently of `(c, y)`. The
local solution therefore has an unrestricted derivative on `[c - δ, c + δ]`, and overlapping steps
glue uniquely by `ODE.eqOn_Icc_of_hasDerivAt`.

## Main declarations

* `ODE.eqOn_Icc_of_lipschitzOnWith` and `ODE.eqOn_Icc_of_hasDerivAt`: two continuous curves on
  `[a, b]` solving `γ' t = v t (γ t)` on `(a, b)` and agreeing at any `c ∈ [a, b]` agree throughout
  `[a, b]`.
* `ODE.nonautonomousGlobalSolution`: the global solution of `γ' t = v t (γ t)` with `γ s = x`.
* `ODE.nonautonomousGlobalSolution_self` and `ODE.hasDerivAt_nonautonomousGlobalSolution`: it
  solves the initial value problem on all of `ℝ`.
* `ODE.continuous_nonautonomousGlobalSolution`: joint continuity in `(s, x, t)`.
* `ODE.nonautonomousGlobalSolution_eq_integral`: the integral equation from `s` to `t`.
* `ODE.eq_nonautonomousGlobalSolution`: global uniqueness.
* `ODE.nonautonomousGlobalSolution_congr`: independence of the continuity and Lipschitz witnesses.
* `ODE.nonautonomousGlobalSolution_trans`: two-time evolution law through an intermediate time.
* `ODE.dist_nonautonomousGlobalSolution_le`: Grönwall continuous dependence on the initial value.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, McGraw-Hill, 1955,
  Chapter 1.
-/

public section

open Function Filter MeasureTheory Metric Set Topology
open scoped NNReal

namespace ODE

/-- Uniform interior step half-width `(4 (K + 1))⁻¹` on which Picard--Lindelöf succeeds from any
initial point and time for a vector field that is `K`-Lipschitz in space. -/
private noncomputable def stepRadius (K : ℝ≥0) : ℝ :=
  (4 * ((K : ℝ) + 1))⁻¹

private theorem stepRadius_pos (K : ℝ≥0) : 0 < stepRadius K := by
  unfold stepRadius
  positivity

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two curves continuous on `[a, b]`, remaining inside `s t` and solving `γ' t = v t (γ t)` at
interior points `t ∈ (a, b)` where `v t` is `K`-Lipschitz on `s t`, agree throughout `[a, b]`
whenever they agree at an interior or boundary point `c ∈ [a, b]`. -/
theorem eqOn_Icc_of_lipschitzOnWith {a b c : ℝ} {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0}
    {f g : ℝ → E} (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t)) (hc : c ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hfs : ∀ t ∈ Ioo a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hgs : ∀ t ∈ Ioo a b, g t ∈ s t) (hfc : f c = g c) :
    EqOn f g (Icc a b) := fun t ht ↦ by
  have hle := TauCeti.norm_le_gronwallBound_of_norm_deriv_le (f := fun u ↦ f u - g u)
    (f' := fun u ↦ v u (f u) - v u (g u)) (δ := 0) (K := K) (ε := 0) hc (hf.sub hg)
    (fun u hu ↦ (hf' u hu).sub (hg' u hu)) (by simp [hfc])
    (fun u hu ↦ by
      simpa only [add_zero, dist_eq_norm] using
        (hv u hu).dist_le_mul (f u) (hfs u hu) (g u) (hgs u hu))
    t ht
  rw [gronwallBound_ε0_δ0] at hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- Two curves continuous on `[a, b]` that solve `γ' t = v t (γ t)` on `(a, b)` and agree at an
interior or boundary point `c ∈ [a, b]` agree throughout `[a, b]`. -/
theorem eqOn_Icc_of_hasDerivAt {a b c : ℝ} {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E}
    (hv : ∀ t ∈ Ioo a b, LipschitzWith K (v t)) (hc : c ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hfc : f c = g c) :
    EqOn f g (Icc a b) :=
  eqOn_Icc_of_lipschitzOnWith (s := fun _ ↦ univ) (fun t ht ↦ (hv t ht).lipschitzOnWith) hc
    hf hf' (fun _ _ ↦ trivial) hg hg' (fun _ _ ↦ trivial) hfc

end Normed

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One uniform Picard--Lindelöf step: solving on `[c - 2 δ, c + 2 δ]` gives an unrestricted
derivative on `[c - δ, c + δ]`. -/
private theorem exists_hasDerivAt_Icc_step {v : ℝ → E → E} (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (c : ℝ) (y : E) :
    ∃ α : ℝ → E, α c = y ∧
      ∀ t ∈ Icc (c - stepRadius K) (c + stepRadius K), HasDerivAt α (v t (α t)) t := by
  set δ := stepRadius K
  have hδ : 0 < δ := stepRadius_pos K
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (c - 2 * δ) (c + 2 * δ)) (f := fun t ↦ v t y) (hvc y).continuousOn
  set a : ℝ≥0 := Real.toNNReal (max M 0)
  have ha_coe : (a : ℝ) = max M 0 := Real.coe_toNNReal _ (le_max_right M 0)
  have hPL : IsPicardLindelof v (tmin := c - 2 * δ) (tmax := c + 2 * δ)
      ⟨c, ⟨by linarith, by linarith⟩⟩ y a 0 ((K + 1) * a) K :=
    { lipschitzOnWith := fun t _ ↦ (hv t).lipschitzOnWith
      continuousOn := fun x _ ↦ (hvc x).continuousOn
      norm_le := fun t ht x hx ↦ by
        have hxy : ‖v t x - v t y‖ ≤ (K : ℝ) * a :=
          ((hv t).norm_sub_le x y).trans
            (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hx) K.2)
        have hty : ‖v t y‖ ≤ a := (hM t ht).trans (ha_coe ▸ le_max_left M 0)
        calc ‖v t x‖ ≤ ‖v t x - v t y‖ + ‖v t y‖ := norm_le_norm_sub_add _ _
          _ ≤ (K : ℝ) * a + a := add_le_add hxy hty
          _ = (((K + 1) * a : ℝ≥0) : ℝ) := by push_cast; ring
      mul_max_le := by
        have hmax : max (c + 2 * δ - c) (c - (c - 2 * δ)) = 2 * δ := by
          rw [add_sub_cancel_left, sub_sub_cancel, max_self]
        have : (0 : ℝ) < (K : ℝ) + 1 := by positivity
        rw [hmax]
        push_cast
        dsimp only [δ, stepRadius]
        have hhalf : ((K : ℝ) + 1) * (a : ℝ) * (2 * (4 * ((K : ℝ) + 1))⁻¹) = (a : ℝ) / 2 := by
          field_simp
          ring
        linarith [NNReal.coe_nonneg a] }
  obtain ⟨α, hαc, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, hαc, fun t ht ↦ ?_⟩
  exact (hα t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

/-- Extending a solution on `[tL, tR]` by one `stepRadius K` at each end. -/
private theorem exists_hasDerivAt_Icc_widen {v : ℝ → E → E} (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) {s tL tR : ℝ} {x : E} {γ : ℝ → E}
    (hsL : tL + stepRadius K ≤ s) (hsR : s ≤ tR - stepRadius K) (hγs : γ s = x)
    (hγ : ∀ t ∈ Icc tL tR, HasDerivAt γ (v t (γ t)) t) :
    ∃ γ' : ℝ → E, γ' s = x ∧
      ∀ t ∈ Icc (tL - stepRadius K) (tR + stepRadius K), HasDerivAt γ' (v t (γ' t)) t := by
  set δ := stepRadius K
  have hδ : 0 < δ := stepRadius_pos K
  obtain ⟨αL, hαL₀, hαL⟩ := exists_hasDerivAt_Icc_step hvc hv tL (γ tL)
  obtain ⟨αR, hαR₀, hαR⟩ := exists_hasDerivAt_Icc_step hvc hv tR (γ tR)
  have hLeq : EqOn αL γ (Icc tL (tL + δ)) :=
    eqOn_Icc_of_hasDerivAt (a := tL) (b := tL + δ) (c := tL) (fun t _ ↦ hv t)
      ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩
      (HasDerivAt.continuousOn fun t ht ↦ hαL t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht ↦ hαL t ⟨by linarith [ht.1], ht.2.le⟩)
      (HasDerivAt.continuousOn fun t ht ↦ hγ t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht ↦ hγ t ⟨ht.1.le, by linarith [ht.2]⟩) hαL₀
  have hReq : EqOn γ αR (Icc (tR - δ) tR) :=
    eqOn_Icc_of_hasDerivAt (a := tR - δ) (b := tR) (c := tR) (fun t _ ↦ hv t)
      ⟨by linarith, le_rfl⟩
      (HasDerivAt.continuousOn fun t ht ↦ hγ t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht ↦ hγ t ⟨by linarith [ht.1], ht.2.le⟩)
      (HasDerivAt.continuousOn fun t ht ↦ hαR t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht ↦ hαR t ⟨ht.1.le, by linarith [ht.2]⟩) hαR₀.symm
  let γ' : ℝ → E := fun u ↦ if u < tL then αL u else if u ≤ tR then γ u else αR u
  refine ⟨γ', ?_, fun t ht ↦ ?_⟩
  · simp only [γ', not_lt.2 (by linarith : tL ≤ s), ↓reduceIte,
      (by linarith : s ≤ tR), hγs]
  · rcases lt_or_ge t (tL + δ) with hlt | hge
    · have hev : γ' =ᶠ[𝓝 t] αL := by
        filter_upwards [Iio_mem_nhds hlt] with u (hu : u < tL + δ)
        dsimp only [γ']
        split_ifs with h₁ h₂
        · rfl
        · exact (hLeq ⟨not_lt.1 h₁, hu.le⟩).symm
        · linarith
      have ht' : γ' t = αL t := hev.self_of_nhds
      exact ht' ▸ (hαL t ⟨ht.1, hlt.le⟩).congr_of_eventuallyEq hev
    · rcases lt_or_ge t tR with hltR | hgeR
      · have hev : γ' =ᶠ[𝓝 t] γ := by
          filter_upwards [Ioo_mem_nhds (by linarith : tL < t) hltR] with u hu
          simp [γ', not_lt.2 hu.1.le, hu.2.le]
        have ht' : γ' t = γ t := hev.self_of_nhds
        exact ht' ▸ (hγ t ⟨by linarith, hltR.le⟩).congr_of_eventuallyEq hev
      · have hev : γ' =ᶠ[𝓝 t] αR := by
          filter_upwards [Ioi_mem_nhds (by linarith : tR - δ < t)] with u (hu : tR - δ < u)
          dsimp only [γ']
          split_ifs with h₁ h₂
          · linarith
          · exact hReq ⟨hu.le, h₂⟩
          · rfl
        have ht' : γ' t = αR t := hev.self_of_nhds
        exact ht' ▸ (hαR t ⟨by linarith, ht.2⟩).congr_of_eventuallyEq hev

/-- Solution on `[s - (n + 1) δ, s + (n + 1) δ]` for every `n : ℕ`. -/
private theorem exists_hasDerivAt_Icc_nat {v : ℝ → E → E} (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (n : ℕ) :
    ∃ γ : ℝ → E, γ s = x ∧
      ∀ t ∈ Icc (s - (n + 1 : ℝ) * stepRadius K) (s + (n + 1 : ℝ) * stepRadius K),
        HasDerivAt γ (v t (γ t)) t := by
  induction n with
  | zero =>
    simpa using exists_hasDerivAt_Icc_step hvc hv s x
  | succ n ih =>
    obtain ⟨γ, hγs, hγ⟩ := ih
    have hδ : 0 < stepRadius K := stepRadius_pos K
    obtain ⟨γ', hγ's, hγ'⟩ := exists_hasDerivAt_Icc_widen hvc hv
      (tL := s - (n + 1 : ℝ) * stepRadius K) (tR := s + (n + 1 : ℝ) * stepRadius K)
      (by nlinarith) (by nlinarith) hγs hγ
    refine ⟨γ', hγ's, fun t ht ↦ hγ' t ⟨?_, ?_⟩⟩ <;> push_cast at ht <;> linarith [ht.1, ht.2]

private noncomputable def localSol {v : ℝ → E → E} (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (n : ℕ) : ℝ → E :=
  (exists_hasDerivAt_Icc_nat hvc hv s x n).choose

private theorem localSol_self {v : ℝ → E → E} (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (n : ℕ) :
    localSol hvc hv s x n s = x :=
  (exists_hasDerivAt_Icc_nat hvc hv s x n).choose_spec.1

private theorem hasDerivAt_localSol {v : ℝ → E → E} (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (s - (n + 1 : ℝ) * stepRadius K) (s + (n + 1 : ℝ) * stepRadius K)) :
    HasDerivAt (localSol hvc hv s x n) (v t (localSol hvc hv s x n t)) t :=
  (exists_hasDerivAt_Icc_nat hvc hv s x n).choose_spec.2 t ht

/-- **The global solution of a state-Lipschitz nonautonomous ODE.** For a vector field `v` on a
Banach space that is continuous in `t` at each fixed point and `K`-Lipschitz in `x` at each time,
`ODE.nonautonomousGlobalSolution v hvc hv s x` is the unique curve `γ : ℝ → E` on the whole line
with `γ s = x` and `γ' t = v t (γ t)` for every `t`. -/
noncomputable def nonautonomousGlobalSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (t : ℝ) : E :=
  localSol hvc hv s x ⌈|t - s| / stepRadius K⌉₊ t

private theorem nonautonomousGlobalSolution_eq_localSol (v : ℝ → E → E)
    (hvc : ∀ x, Continuous (v · x)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    (s : ℝ) (x : E) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (s - (n + 1 : ℝ) * stepRadius K) (s + (n + 1 : ℝ) * stepRadius K)) :
    nonautonomousGlobalSolution v hvc hv s x t = localSol hvc hv s x n t := by
  set δ := stepRadius K
  have hδ : 0 < δ := stepRadius_pos K
  set m := ⌈|t - s| / δ⌉₊
  have hm : |t - s| ≤ (m + 1 : ℝ) * δ := by
    have hceil : |t - s| ≤ m * δ := (div_le_iff₀ hδ).1 (Nat.le_ceil _)
    linarith
  have hmin : t ∈ Icc (s - (min m n + 1 : ℝ) * δ) (s + (min m n + 1 : ℝ) * δ) := by
    rcases le_total m n with hle | hle
    · rw [min_eq_left hle]
      have habs := abs_le.1 hm
      exact ⟨by linarith, by linarith⟩
    · rwa [min_eq_right hle]
  have hmL : ((min m n : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (min_le_left m n)
  have hnL : ((min m n : ℕ) : ℝ) ≤ n := Nat.cast_le.2 (min_le_right m n)
  have hm_sub : ∀ {u : ℝ}, u ∈ Icc (s - (min m n + 1 : ℝ) * δ) (s + (min m n + 1 : ℝ) * δ) →
      u ∈ Icc (s - (m + 1 : ℝ) * δ) (s + (m + 1 : ℝ) * δ) := fun hu ↦
    ⟨by dsimp only [δ] at hu; nlinarith [hu.1], by dsimp only [δ] at hu; nlinarith [hu.2]⟩
  have hn_sub : ∀ {u : ℝ}, u ∈ Icc (s - (min m n + 1 : ℝ) * δ) (s + (min m n + 1 : ℝ) * δ) →
      u ∈ Icc (s - (n + 1 : ℝ) * δ) (s + (n + 1 : ℝ) * δ) := fun hu ↦
    ⟨by dsimp only [δ] at hu; nlinarith [hu.1], by dsimp only [δ] at hu; nlinarith [hu.2]⟩
  exact eqOn_Icc_of_hasDerivAt
    (a := s - (min m n + 1 : ℝ) * δ) (b := s + (min m n + 1 : ℝ) * δ) (c := s)
    (fun u _ ↦ hv u) ⟨sub_le_self _ (by positivity), le_add_of_nonneg_right (by positivity)⟩
    (HasDerivAt.continuousOn fun u hu ↦ hasDerivAt_localSol hvc hv s x m (hm_sub hu))
    (fun u hu ↦ hasDerivAt_localSol hvc hv s x m (hm_sub (Ioo_subset_Icc_self hu)))
    (HasDerivAt.continuousOn fun u hu ↦ hasDerivAt_localSol hvc hv s x n (hn_sub hu))
    (fun u hu ↦ hasDerivAt_localSol hvc hv s x n (hn_sub (Ioo_subset_Icc_self hu)))
    (by rw [localSol_self, localSol_self]) hmin

/-- The global solution starts at the prescribed initial point at time `s`. -/
@[simp]
theorem nonautonomousGlobalSolution_self (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) :
    nonautonomousGlobalSolution v hvc hv s x s = x := by
  have hδ : 0 < stepRadius K := stepRadius_pos K
  rw [nonautonomousGlobalSolution_eq_localSol v hvc hv s x 0 (by simp [hδ.le]), localSol_self]

/-- **The global solution solves the nonautonomous differential equation** at every time. -/
theorem hasDerivAt_nonautonomousGlobalSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (nonautonomousGlobalSolution v hvc hv s x)
      (v t (nonautonomousGlobalSolution v hvc hv s x t)) t := by
  set δ := stepRadius K
  have hδ : 0 < δ := stepRadius_pos K
  set n := ⌈|t - s| / δ⌉₊
  have hceil : |t - s| ≤ n * δ := (div_le_iff₀ hδ).1 (Nat.le_ceil _)
  have habs := abs_le.1 hceil
  have hltL : s - (n + 1 : ℝ) * δ < t := by linarith
  have hltR : t < s + (n + 1 : ℝ) * δ := by linarith
  have hev : nonautonomousGlobalSolution v hvc hv s x =ᶠ[𝓝 t] localSol hvc hv s x n := by
    filter_upwards [Icc_mem_nhds hltL hltR] with u hu
    exact nonautonomousGlobalSolution_eq_localSol v hvc hv s x n hu
  rw [hev.self_of_nhds]
  exact (hasDerivAt_localSol hvc hv s x n ⟨hltL.le, hltR.le⟩).congr_of_eventuallyEq hev

/-- The global solution is an integral curve of `v`. -/
theorem isIntegralCurve_nonautonomousGlobalSolution (v : ℝ → E → E)
    (hvc : ∀ x, Continuous (v · x)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) :
    IsIntegralCurve (nonautonomousGlobalSolution v hvc hv s x) v :=
  hasDerivAt_nonautonomousGlobalSolution v hvc hv s x

/-- The global solution is continuous in time. -/
theorem continuous_nonautonomousGlobalSolution_apply (v : ℝ → E → E)
    (hvc : ∀ x, Continuous (v · x)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) :
    Continuous (nonautonomousGlobalSolution v hvc hv s x) :=
  continuous_iff_continuousAt.2 fun t ↦
    (hasDerivAt_nonautonomousGlobalSolution v hvc hv s x t).continuousAt

/-- **The integral equation** of the nonautonomous initial value problem. -/
theorem nonautonomousGlobalSolution_eq_integral (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (t : ℝ) :
    nonautonomousGlobalSolution v hvc hv s x t =
      x + ∫ τ in s..t, v τ (nonautonomousGlobalSolution v hvc hv s x τ) := by
  have hv_uncurry : Continuous (uncurry v) :=
    continuous_prod_of_dense_continuous_lipschitzWith' (uncurry v) K dense_univ hv fun y _ ↦ hvc y
  have hcomp : Continuous fun τ ↦ v τ (nonautonomousGlobalSolution v hvc hv s x τ) :=
    hv_uncurry.comp
      (continuous_id.prodMk (continuous_nonautonomousGlobalSolution_apply v hvc hv s x))
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun τ _ ↦ hasDerivAt_nonautonomousGlobalSolution v hvc hv s x τ)
    (hcomp.intervalIntegrable s t)
  rw [hint, nonautonomousGlobalSolution_self, add_sub_cancel]

/-- **Uniqueness.** Any curve defined on the whole line that solves `γ' t = v t (γ t)` equals
`ODE.nonautonomousGlobalSolution` through its value at any time `s`. -/
theorem eq_nonautonomousGlobalSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v t (γ t)) t) :
    γ = nonautonomousGlobalSolution v hvc hv s (γ s) :=
  ODE_solution_unique_univ (v := v) (s := fun _ ↦ univ) (t₀ := s)
    (fun t ↦ (hv t).lipschitzOnWith) (fun t ↦ ⟨hγ t, trivial⟩)
    (fun t ↦ ⟨hasDerivAt_nonautonomousGlobalSolution v hvc hv s (γ s) t, trivial⟩)
    (nonautonomousGlobalSolution_self v hvc hv s (γ s)).symm

/-- **Independence of the witnesses.** Two continuity and Lipschitz witnesses for the same vector
field produce the same global solution. -/
theorem nonautonomousGlobalSolution_congr (v : ℝ → E → E)
    (hvc : ∀ x, Continuous (v · x)) (hvc' : ∀ x, Continuous (v · x))
    {K K' : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (hv' : ∀ t, LipschitzWith K' (v t))
    (s : ℝ) (x : E) :
    nonautonomousGlobalSolution v hvc hv s x = nonautonomousGlobalSolution v hvc' hv' s x := by
  have h := eq_nonautonomousGlobalSolution v hvc' hv' s
    (hasDerivAt_nonautonomousGlobalSolution v hvc hv s x)
  rwa [nonautonomousGlobalSolution_self] at h

/-- **Two-time evolution law.** Evolving from `r` to `s` and then from `s` to `t` equals evolving
directly from `r` to `t`. -/
@[simp]
theorem nonautonomousGlobalSolution_trans (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (r s t : ℝ) (x : E) :
    nonautonomousGlobalSolution v hvc hv s
      (nonautonomousGlobalSolution v hvc hv r x s) t =
      nonautonomousGlobalSolution v hvc hv r x t :=
  (congrFun (eq_nonautonomousGlobalSolution v hvc hv s
    (hasDerivAt_nonautonomousGlobalSolution v hvc hv r x)) t).symm

/-- **Reversing time** around `0` solves the time-reversed negated field `t ↦ -v (-t) ·`. -/
theorem nonautonomousGlobalSolution_neg (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x : E) (t : ℝ) :
    nonautonomousGlobalSolution v hvc hv s x (-t) =
      nonautonomousGlobalSolution (fun u z ↦ -v (-u) z)
        (fun z ↦ ((hvc z).comp continuous_neg).neg) (fun u ↦ (hv (-u)).neg) (-s) x t := by
  have hγ : ∀ u, HasDerivAt (fun q ↦ nonautonomousGlobalSolution v hvc hv s x (-q))
      (-v (-u) (nonautonomousGlobalSolution v hvc hv s x (-u))) u := fun u ↦ by
    simpa only [Function.comp_def, neg_smul, one_smul] using
      (hasDerivAt_nonautonomousGlobalSolution v hvc hv s x (-u)).scomp u
        (hasDerivAt_neg u)
  have heq := congrFun (eq_nonautonomousGlobalSolution (fun u z ↦ -v (-u) z)
    (fun z ↦ ((hvc z).comp continuous_neg).neg) (fun u ↦ (hv (-u)).neg) (-s) hγ) t
  simpa using heq

private theorem dist_nonautonomousGlobalSolution_le_of_le (v : ℝ → E → E)
    (hvc : ∀ x, Continuous (v · x)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {s t : ℝ} (hst : s ≤ t) (x y : E) :
    dist (nonautonomousGlobalSolution v hvc hv s x t)
      (nonautonomousGlobalSolution v hvc hv s y t) ≤ dist x y * Real.exp (K * (t - s)) := by
  simpa using dist_le_of_trajectories_ODE (v := v) (K := K) (a := s) (b := t)
    (f := nonautonomousGlobalSolution v hvc hv s x)
    (g := nonautonomousGlobalSolution v hvc hv s y) (δ := dist x y)
    hv
    (continuous_nonautonomousGlobalSolution_apply v hvc hv s x).continuousOn
    (fun u _ ↦ (hasDerivAt_nonautonomousGlobalSolution v hvc hv s x u).hasDerivWithinAt)
    (continuous_nonautonomousGlobalSolution_apply v hvc hv s y).continuousOn
    (fun u _ ↦ (hasDerivAt_nonautonomousGlobalSolution v hvc hv s y u).hasDerivWithinAt)
    (by simp) t ⟨hst, le_rfl⟩

/-- **Continuous dependence on the initial value.** Two global solutions started at time `s` drift
apart at most exponentially in `|t - s|` at rate `K`. -/
theorem dist_nonautonomousGlobalSolution_le (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (s : ℝ) (x y : E) (t : ℝ) :
    dist (nonautonomousGlobalSolution v hvc hv s x t)
      (nonautonomousGlobalSolution v hvc hv s y t) ≤ dist x y * Real.exp (K * |t - s|) := by
  rcases le_total s t with hst | hts
  · simpa [abs_of_nonneg (sub_nonneg.2 hst)] using
      dist_nonautonomousGlobalSolution_le_of_le v hvc hv hst x y
  · have h := dist_nonautonomousGlobalSolution_le_of_le (fun u z ↦ -v (-u) z)
      (fun z ↦ ((hvc z).comp continuous_neg).neg) (fun u ↦ (hv (-u)).neg)
      (s := -s) (t := -t) (neg_le_neg hts) x y
    rw [← nonautonomousGlobalSolution_neg v hvc hv s x (-t),
      ← nonautonomousGlobalSolution_neg v hvc hv s y (-t), neg_neg] at h
    have habs : -t - -s = |t - s| := by
      rw [abs_of_nonpos (sub_nonpos.2 hts)]
      ring
    rwa [habs] at h

/-- **Joint continuity** of `ODE.nonautonomousGlobalSolution` in the initial time, initial value,
and evaluation time. -/
theorem continuous_nonautonomousGlobalSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous (v · x))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) :
    Continuous fun p : ℝ × E × ℝ ↦ nonautonomousGlobalSolution v hvc hv p.1 p.2.1 p.2.2 := by
  let φ := nonautonomousGlobalSolution v hvc hv
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, x₀, t₀⟩
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ p : ℝ × E × ℝ, dist (φ p.1 p.2.1 p.2.2) (φ s₀ x₀ t₀) ≤
      dist p.2.1 (φ s₀ x₀ p.1) * Real.exp (K * |s₀ - p.1|) * Real.exp (K * |p.2.2 - s₀|) +
        dist (φ s₀ x₀ p.2.2) (φ s₀ x₀ t₀) := by
    rintro ⟨s, x, t⟩
    have hx₀ : φ s (φ s₀ x₀ s) s₀ = x₀ := by
      simp [φ]
    have hs₀ : dist (φ s x s₀) x₀ ≤ dist x (φ s₀ x₀ s) * Real.exp (K * |s₀ - s|) := by
      simpa only [φ, hx₀] using dist_nonautonomousGlobalSolution_le v hvc hv s x (φ s₀ x₀ s) s₀
    have hst : dist (φ s x t) (φ s₀ x₀ t) ≤
        dist x (φ s₀ x₀ s) * Real.exp (K * |s₀ - s|) * Real.exp (K * |t - s₀|) := by
      calc dist (φ s x t) (φ s₀ x₀ t)
          = dist (φ s₀ (φ s x s₀) t) (φ s₀ x₀ t) := by simp [φ]
        _ ≤ dist (φ s x s₀) x₀ * Real.exp (K * |t - s₀|) :=
            dist_nonautonomousGlobalSolution_le v hvc hv s₀ (φ s x s₀) x₀ t
        _ ≤ dist x (φ s₀ x₀ s) * Real.exp (K * |s₀ - s|) * Real.exp (K * |t - s₀|) :=
            mul_le_mul_of_nonneg_right hs₀ (Real.exp_nonneg _)
    exact (dist_triangle (φ s x t) (φ s₀ x₀ t) (φ s₀ x₀ t₀)).trans (add_le_add hst le_rfl)
  have hcont : Continuous fun p : ℝ × E × ℝ ↦
      dist p.2.1 (φ s₀ x₀ p.1) * Real.exp (K * |s₀ - p.1|) * Real.exp (K * |p.2.2 - s₀|) +
        dist (φ s₀ x₀ p.2.2) (φ s₀ x₀ t₀) := by
    have hφ : Continuous (φ s₀ x₀) := continuous_nonautonomousGlobalSolution_apply v hvc hv s₀ x₀
    fun_prop
  have hzero : Tendsto (fun p : ℝ × E × ℝ ↦
      dist p.2.1 (φ s₀ x₀ p.1) * Real.exp (K * |s₀ - p.1|) * Real.exp (K * |p.2.2 - s₀|) +
        dist (φ s₀ x₀ p.2.2) (φ s₀ x₀ t₀)) (𝓝 (s₀, x₀, t₀)) (𝓝 0) := by
    simpa [φ, nonautonomousGlobalSolution_self] using
      (hcont.continuousAt (x := (s₀, x₀, t₀))).tendsto
  exact squeeze_zero (fun _ ↦ dist_nonneg) hbound hzero

end Complete

end ODE
