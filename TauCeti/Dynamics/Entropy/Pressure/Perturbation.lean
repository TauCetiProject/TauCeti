/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.Pressure
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Bounded perturbations of the potential

Topological pressure only sees the Birkhoff sums of a potential up to a bounded error: if
`birkhoffSum T φ n x ≤ birkhoffSum T ψ n x + C` for all `n` and `x`, then
`P(T, φ) ≤ P(T, ψ)`. This gives, for a map `T` of a uniform space:

* the Lipschitz bound: if `|φ x - ψ x| ≤ c` for all `x`, then `P(T, φ) ≤ P(T, ψ) + c`; for
  continuous potentials on a compact space this is `P(T, φ) ≤ P(T, ψ) + ‖φ - ψ‖`;
* a bounded potential has infinite pressure exactly when `coverEntropy T univ = ⊤`;
* invariance under bounded coboundaries: `P(T, φ + ψ ∘ T - ψ) = P(T, φ)` for bounded `ψ`, because
  the Birkhoff sums of `ψ ∘ T - ψ` telescope to `ψ (T^[n] x) - ψ x`.

## Main results

* `TauCeti.topologicalPressure_le_of_birkhoffSum_le`: pressure is monotone under domination of the
  Birkhoff sums up to a constant.
* `TauCeti.topologicalPressure_le_add_of_le`: `φ ≤ ψ + c` gives `P(T, φ) ≤ P(T, ψ) + c`.
* `TauCeti.topologicalPressure_le_add_norm_sub`: `P(T, φ) ≤ P(T, ψ) + ‖φ - ψ‖` for `φ ψ : C(X, ℝ)`
  on a compact space.
* `TauCeti.topologicalPressure_eq_top_iff`: a bounded potential has pressure `⊤` iff the
  topological entropy is `⊤`.
* `TauCeti.topologicalPressure_add_coboundary`: `P(T, φ + ψ ∘ T - ψ) = P(T, φ)` for bounded
  `ψ`.
* `TauCeti.topologicalPressure_id`: for the identity of a nonempty finite space,
  `P(id, φ) = max_x φ x`.

## References

These are items 2 and 3 and the first Check of §5.4 of the Tau Ceti roadmap
`ClassicalErgodicTheory`.
-/

public section

namespace TauCeti

open Dynamics Set Filter ExpGrowth
open scoped ENNReal Uniformity

variable {X : Type*} {T : X → X} {φ ψ : X → ℝ} {U : SetRel X X} {n : ℕ}

/-- If the Birkhoff sums of `φ` at time `n` are at most those of `ψ` plus `C`, then the pressure sum
of `φ` is at most `exp C` times that of `ψ`. -/
theorem pressureNetSum_le_exp_mul {C : ℝ}
    (h : ∀ x, birkhoffSum T φ n x ≤ birkhoffSum T ψ n x + C) :
    pressureNetSum T φ U n ≤ ENNReal.ofReal (Real.exp C) * pressureNetSum T ψ U n := by
  rw [pressureNetSum_le_iff]
  intro s hs
  refine le_trans ?_ (mul_le_mul_right hs.sum_le_pressureNetSum _)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [h x]))

/-- If the Birkhoff sums of `φ` are at most those of `ψ` plus a constant `C`, uniformly in time and
space, then the pressure of `φ` at every entourage is at most that of `ψ`. -/
theorem netPressureEntourage_le_of_birkhoffSum_le {C : ℝ}
    (h : ∀ n x, birkhoffSum T φ n x ≤ birkhoffSum T ψ n x + C) (U : SetRel X X) :
    netPressureEntourage T φ U ≤ netPressureEntourage T ψ U := by
  rw [netPressureEntourage_def, netPressureEntourage_def]
  exact expGrowthSup_le_of_eventually_le ENNReal.ofReal_ne_top
    (Eventually.of_forall fun n ↦ pressureNetSum_le_exp_mul (h n))

/-- If the Birkhoff sums of `φ` are at most those of `ψ` plus a constant `C`, uniformly in time and
space, then `P(T, φ) ≤ P(T, ψ)`. -/
theorem topologicalPressure_le_of_birkhoffSum_le [UniformSpace X] {C : ℝ}
    (h : ∀ n x, birkhoffSum T φ n x ≤ birkhoffSum T ψ n x + C) :
    topologicalPressure T φ ≤ topologicalPressure T ψ := by
  rw [topologicalPressure_def, topologicalPressure_def]
  exact iSup₂_mono fun U _ ↦ netPressureEntourage_le_of_birkhoffSum_le h U

/-- Potentials whose Birkhoff sums differ by a bounded amount have the same pressure. -/
theorem topologicalPressure_eq_of_abs_birkhoffSum_sub_le [UniformSpace X] {C : ℝ}
    (h : ∀ n x, |birkhoffSum T φ n x - birkhoffSum T ψ n x| ≤ C) :
    topologicalPressure T φ = topologicalPressure T ψ := by
  refine le_antisymm (topologicalPressure_le_of_birkhoffSum_le (C := C) fun n x ↦ ?_)
    (topologicalPressure_le_of_birkhoffSum_le (C := C) fun n x ↦ ?_)
  · linarith [le_abs_self (birkhoffSum T φ n x - birkhoffSum T ψ n x), h n x]
  · linarith [neg_abs_le (birkhoffSum T φ n x - birkhoffSum T ψ n x), h n x]

/-- If `φ ≤ ψ + c` pointwise, then `P(T, φ) ≤ P(T, ψ) + c`. -/
theorem topologicalPressure_le_add_of_le [UniformSpace X] {c : ℝ} (h : ∀ x, φ x ≤ ψ x + c) :
    topologicalPressure T φ ≤ topologicalPressure T ψ + c :=
  (topologicalPressure_mono h).trans_eq (topologicalPressure_add_const T ψ c)

/-- The Lipschitz bound for pressure: if `|φ x - ψ x| ≤ c` for every `x`, then
`P(T, φ) ≤ P(T, ψ) + c`. -/
theorem topologicalPressure_le_add_of_abs_sub_le [UniformSpace X] {c : ℝ}
    (h : ∀ x, |φ x - ψ x| ≤ c) :
    topologicalPressure T φ ≤ topologicalPressure T ψ + c :=
  topologicalPressure_le_add_of_le fun x ↦ by linarith [le_abs_self (φ x - ψ x), h x]

/-- The Lipschitz bound for pressure, in real form: if `|φ x - ψ x| ≤ c` for every `x` and the
pressure of `ψ` is finite, then the pressure of `φ` is finite and
`|P(T, φ) - P(T, ψ)| ≤ c`. -/
theorem abs_toReal_topologicalPressure_sub_le [UniformSpace X] {c : ℝ}
    (h : ∀ x, |φ x - ψ x| ≤ c) (hψ : topologicalPressure T ψ ≠ ⊤)
    (hψ' : topologicalPressure T ψ ≠ ⊥) :
    topologicalPressure T φ ≠ ⊤ ∧ topologicalPressure T φ ≠ ⊥ ∧
      |(topologicalPressure T φ).toReal - (topologicalPressure T ψ).toReal| ≤ c := by
  have h' : ∀ x, |ψ x - φ x| ≤ c := fun x ↦ abs_sub_comm (ψ x) (φ x) ▸ h x
  have h₁ := topologicalPressure_le_add_of_abs_sub_le (T := T) h
  have h₂ := topologicalPressure_le_add_of_abs_sub_le (T := T) h'
  have hp_top : topologicalPressure T φ ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.add_ne_top hψ (EReal.coe_ne_top c)) h₁
  have hp_bot : topologicalPressure T φ ≠ ⊥ := by
    rintro hp
    rw [hp, EReal.bot_add, le_bot_iff] at h₂
    exact hψ' h₂
  refine ⟨hp_top, hp_bot, ?_⟩
  rw [← EReal.coe_toReal hp_top hp_bot, ← EReal.coe_toReal hψ hψ'] at h₁ h₂
  have h₁' := EReal.coe_le_coe_iff.mp (by simpa only [← EReal.coe_add] using h₁)
  have h₂' := EReal.coe_le_coe_iff.mp (by simpa only [← EReal.coe_add] using h₂)
  rw [abs_le]
  constructor <;> linarith

/-- A potential bounded by `c` in absolute value has pressure `⊤` iff the topological entropy of
`T` is `⊤`. -/
theorem topologicalPressure_eq_top_iff [UniformSpace X] {c : ℝ} (h : ∀ x, |φ x| ≤ c) :
    topologicalPressure T φ = ⊤ ↔ coverEntropy T univ = ⊤ := by
  have h₁ : topologicalPressure T φ ≤ coverEntropy T univ + c := by
    rw [← topologicalPressure_zero]
    exact topologicalPressure_le_add_of_abs_sub_le fun x ↦ by simpa using h x
  have h₂ : coverEntropy T univ ≤ topologicalPressure T φ + c := by
    rw [← topologicalPressure_zero]
    exact topologicalPressure_le_add_of_abs_sub_le fun x ↦ by simpa using h x
  have hc := EReal.add_eq_top_iff_eq_top_left (x := coverEntropy T univ) (EReal.coe_ne_bot c)
    (EReal.coe_ne_top c)
  have hc' := EReal.add_eq_top_iff_eq_top_left (x := topologicalPressure T φ)
    (EReal.coe_ne_bot c) (EReal.coe_ne_top c)
  constructor
  · intro hφ
    rw [hφ, top_le_iff] at h₁
    exact hc.mp h₁
  · intro hT
    rw [hT, top_le_iff] at h₂
    exact hc'.mp h₂

/-- The Birkhoff sums of a coboundary `ψ ∘ T - ψ` telescope: at time `n` they equal
`ψ (T^[n] x) - ψ x`. -/
theorem birkhoffSum_comp_sub_self (T : X → X) (ψ : X → ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun y ↦ ψ (T y) - ψ y) n x = ψ (T^[n] x) - ψ x := by
  rw [← birkhoffSum_apply_sub_birkhoffSum, show (fun y ↦ ψ (T y) - ψ y) = ψ ∘ T - ψ from rfl,
    birkhoffSum_sub_apply, birkhoffSum_comp_apply]

/-- Invariance of pressure under bounded coboundaries: if `|ψ x| ≤ c` for every `x`, then
`P(T, φ + ψ ∘ T - ψ) = P(T, φ)`. -/
theorem topologicalPressure_add_coboundary [UniformSpace X] {c : ℝ} (hψ : ∀ x, |ψ x| ≤ c) :
    topologicalPressure T (fun x ↦ φ x + (ψ (T x) - ψ x)) = topologicalPressure T φ := by
  refine topologicalPressure_eq_of_abs_birkhoffSum_sub_le (C := 2 * c) fun n x ↦ ?_
  rw [show (fun x ↦ φ x + (ψ (T x) - ψ x)) = φ + fun y ↦ ψ (T y) - ψ y from rfl,
    birkhoffSum_add_apply, add_sub_cancel_left, birkhoffSum_comp_sub_self]
  exact (abs_sub _ _).trans (by linarith [hψ (T^[n] x), hψ x])

section Identity

/-- The pressure of the identity of a nonempty finite uniform space is the maximum of the
potential: `P(id, φ) = max_x φ x`. The singleton nets give the lower bound and the whole space
bounds every net. -/
theorem topologicalPressure_id [UniformSpace X] [Fintype X] [Nonempty X] (φ : X → ℝ) :
    topologicalPressure id φ = (Finset.univ.sup' Finset.univ_nonempty φ : ℝ) := by
  set M := Finset.univ.sup' Finset.univ_nonempty φ
  have hB : ∀ n x, birkhoffSum id φ n x = n * φ x := fun n x ↦ by
    rw [birkhoffSum_apply_of_comp_eq (f := id) rfl, nsmul_eq_mul]
  apply le_antisymm
  · rw [topologicalPressure_le_iff]
    intro U _
    rw [netPressureEntourage_def]
    refine (expGrowthSup_le_of_eventually_le (b := Fintype.card X) (ENNReal.natCast_ne_top _)
      (v := fun n : ℕ ↦ EReal.exp (M * n)) (Eventually.of_forall fun n ↦ ?_)).trans_eq
      (expGrowthSup_exp (a := M))
    rw [pressureNetSum_le_iff]
    intro s _
    calc ∑ x ∈ s, ENNReal.ofReal (Real.exp (birkhoffSum id φ n x))
        ≤ ∑ _x ∈ s, EReal.exp (M * n) := Finset.sum_le_sum fun x _ ↦ by
          rw [hB, ← EReal.coe_natCast, ← EReal.coe_mul, EReal.exp_coe, mul_comm]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            (Finset.le_sup' φ (Finset.mem_univ x)) n.cast_nonneg))
      _ = s.card * EReal.exp (M * n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card X * EReal.exp (M * n) := by
          gcongr
          exact_mod_cast s.card_le_univ
  · obtain ⟨x₀, -, hx₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty φ
    refine le_trans ?_ (netPressureEntourage_le_topologicalPressure (U := univ)
      Filter.univ_mem)
    rw [netPressureEntourage_def, show M = φ x₀ from hx₀]
    refine Frequently.le_expGrowthSup (Eventually.of_forall fun n ↦ ?_).frequently
    have hnet : IsDynNetIn (id : X → X) univ univ n ({x₀} : Finset X) :=
      ⟨subset_univ _, by simp⟩
    refine le_trans ?_ hnet.sum_le_pressureNetSum
    rw [Finset.sum_singleton, hB, ← EReal.coe_natCast, ← EReal.coe_mul, EReal.exp_coe, mul_comm]

end Identity

section Compact

variable [UniformSpace X] [CompactSpace X]

/-- The Lipschitz bound for continuous potentials on a compact space:
`P(T, φ) ≤ P(T, ψ) + ‖φ - ψ‖`. -/
theorem topologicalPressure_le_add_norm_sub (T : X → X) (φ ψ : C(X, ℝ)) :
    topologicalPressure T φ ≤ topologicalPressure T ψ + ‖φ - ψ‖ :=
  topologicalPressure_le_add_of_abs_sub_le fun x ↦ by
    simpa [Real.norm_eq_abs] using (φ - ψ).norm_coe_le_norm x

/-- On a compact space, a continuous potential has pressure `⊤` iff the topological entropy is
`⊤`. -/
theorem topologicalPressure_continuousMap_eq_top_iff (T : X → X) (φ : C(X, ℝ)) :
    topologicalPressure T φ = ⊤ ↔ coverEntropy T univ = ⊤ :=
  topologicalPressure_eq_top_iff (c := ‖φ‖) fun x ↦ by
    simpa [Real.norm_eq_abs] using φ.norm_coe_le_norm x

/-- Invariance of pressure under continuous coboundaries on a compact space:
`P(T, φ + ψ ∘ T - ψ) = P(T, φ)`. -/
theorem topologicalPressure_add_coboundary_continuousMap (T : X → X) (φ : X → ℝ)
    (ψ : C(X, ℝ)) :
    topologicalPressure T (fun x ↦ φ x + (ψ (T x) - ψ x)) = topologicalPressure T φ :=
  topologicalPressure_add_coboundary (c := ‖ψ‖) fun x ↦ by
    simpa [Real.norm_eq_abs] using ψ.norm_coe_le_norm x

end Compact

end TauCeti
