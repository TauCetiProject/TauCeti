/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import TauCeti.Combinatorics.GridPath.TwoGrid
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Composing transfers of periods along grid paths

For each path, a family of finite data with a prescribed bound determines a period at each
real point. Proportionality allows the factor to depend on the point but not on the twist or
on the forms being tested. A transfer sends data to the later path with a larger bound. A
proportionality statement on the later path then implies one on the earlier path, after dividing
by the transfer constant. Composing the local transfers uses each square exactly once.

The formulation follows `New.Data.IsProportional`, `New.Data.TransfersPeriods` and
`New.Data.exists_transfersPeriods_first_last` in `grh/src/New/Determinant/AuxiliaryForms/`
(`PathData.lean`, `Turns.lean` and `DiagonalTurns.lean`) of lsernau/grh-lean at `72fead1`.
-/

public section

open Finset

namespace TauCeti.TwoGridPath

variable {m : ℕ} {ι : Type*} {X : ι → Type*} {K : Type*} [CommMonoid K]
variable {Point Data : TwoGridPath m → Type*}

/-- A transfer from `Γ` to `Γ'`. For each datum on `Γ` admissible at bound `N`, it
supplies a single datum on `Γ'` admissible at bound `k * N`. If the latter period is proportional
to `Ξ` at every point, then the original period is proportional to `Ξ / c` at every point. The
proportionality scalar may depend on the point but must be uniform in `i` and `x : X i`. -/
def TransfersPeriods
    (admissible : ∀ Γ, (ι → ℕ) → Data Γ → Prop)
    (period : ∀ Γ, Data Γ → Point Γ → (i : ι) → X i → K)
    (Γ Γ' : TwoGridPath m) (k : ι → ℕ) (c : ι → Kˣ) : Prop :=
  ∀ (N : ι → ℕ) (y : Data Γ), admissible Γ N y →
    ∃ z : Data Γ', admissible Γ' (k * N) z ∧ ∀ (Ξ : (i : ι) → X i → K),
      (∀ g', ∃ b : K, ∀ i x, period Γ' z g' i x = b * Ξ i x) →
      ∀ g, ∃ b : K, ∀ i x, period Γ y g i x = b * (Ξ i x * (↑((c i)⁻¹) : K))

variable {admissible : ∀ Γ, (ι → ℕ) → Data Γ → Prop}
variable {period : ∀ Γ, Data Γ → Point Γ → (i : ι) → X i → K}

/-- Characterize a transfer by its bound and its implication on proportional periods. -/
theorem transfersPeriods_iff {Γ Γ' : TwoGridPath m} {k : ι → ℕ} {c : ι → Kˣ} :
    TransfersPeriods admissible period Γ Γ' k c ↔
      ∀ (N : ι → ℕ) (y : Data Γ), admissible Γ N y →
        ∃ z : Data Γ', admissible Γ' (k * N) z ∧ ∀ (Ξ : (i : ι) → X i → K),
          (∀ g', ∃ b : K, ∀ i x, period Γ' z g' i x = b * Ξ i x) →
          ∀ g, ∃ b : K, ∀ i x, period Γ y g i x = b * (Ξ i x * (↑((c i)⁻¹) : K)) := (Iff.rfl)

namespace TransfersPeriods

/-- The identity transfer preserves both the bound and the period. -/
theorem refl (Γ : TwoGridPath m) : TransfersPeriods admissible period Γ Γ 1 1 := by
  rw [transfersPeriods_iff]
  intro N y hy
  simp only [one_mul, Pi.one_apply, inv_one, Units.val_one, mul_one]
  exact ⟨y, hy, fun _ h ↦ h⟩

/-- With an upward-closed admissibility condition at the later path, a transfer remains
valid if its bound factor is increased. -/
theorem mono {Γ Γ' : TwoGridPath m} {k k' : ι → ℕ} {c : ι → Kˣ}
    (h : TransfersPeriods admissible period Γ Γ' k c) (hk : k ≤ k')
    (ha : ∀ z : Data Γ', Monotone (fun N ↦ admissible Γ' N z)) :
    TransfersPeriods admissible period Γ Γ' k' c := by
  rw [transfersPeriods_iff] at h ⊢
  intro N y hy
  obtain ⟨z, hz, hprop⟩ := h N y hy
  exact ⟨z, ha z (fun i ↦ Nat.mul_le_mul_right (N i) (hk i)) hz, hprop⟩

/-- Composing transfers multiplies both the bound factors and the proportionality constants. -/
theorem trans {Γ₀ Γ₁ Γ₂ : TwoGridPath m} {k₀ k₁ : ι → ℕ} {c₀ c₁ : ι → Kˣ}
    (h₀ : TransfersPeriods admissible period Γ₀ Γ₁ k₀ c₀)
    (h₁ : TransfersPeriods admissible period Γ₁ Γ₂ k₁ c₁) :
    TransfersPeriods admissible period Γ₀ Γ₂ (k₀ * k₁) (c₀ * c₁) := by
  rw [transfersPeriods_iff] at h₀ h₁ ⊢
  intro N y hy
  obtain ⟨z, hz, hzprop⟩ := h₀ N y hy
  obtain ⟨w, hw, hwprop⟩ := h₁ (k₀ * N) z hz
  refine ⟨w, by rwa [mul_comm k₀ k₁, mul_assoc], fun Ξ hΞ ↦ ?_⟩
  have h := hzprop (fun i x ↦ Ξ i x * (↑((c₁ i)⁻¹) : K)) (hwprop Ξ hΞ)
  simpa only [Pi.mul_apply, mul_inv_rev, Units.val_mul, mul_assoc] using h

/-- A transfer across every turn gives a transfer between the first and last paths. The total
bound factor and normalization are the products over the full grid; in particular, if the
bound factor of one turn is always `k`, the total is pointwise `k ^ (m * m)`. -/
theorem first_last {k : (ℕ × ℕ) → ι → ℕ} {c : (ℕ × ℕ) → ι → Kˣ}
    (h : ∀ {Γ Γ' : TwoGridPath m} {s : ℕ × ℕ}, Γ.Turn s Γ' →
      TransfersPeriods admissible period Γ Γ' (k s) (c s)) :
    TransfersPeriods admissible period (first m) (last m)
      (∏ s ∈ range m ×ˢ range m, k s) (∏ s ∈ range m ×ˢ range m, c s) := by
  apply turn_induction (motive := fun Γ T ↦
    TransfersPeriods admissible period Γ (last m) (∏ s ∈ T, k s) (∏ s ∈ T, c s))
  · simpa using refl (admissible := admissible) (period := period) (last m)
  · intro Γ s Γ' T hturn hs hT
    simpa only [prod_insert hs] using (h hturn).trans hT

end TransfersPeriods

end TauCeti.TwoGridPath
