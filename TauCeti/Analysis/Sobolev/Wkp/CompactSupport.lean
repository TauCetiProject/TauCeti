/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ApproximateIdentity
public import TauCeti.Analysis.Sobolev.Wkp.Zero

/-!
# Mollification of compactly supported higher-order Sobolev functions

The first-order part of a `W^{k+1,p}` function records its value and weak gradient. If this
jet vanishes almost everywhere outside a compact set, a smooth mollification is a test
function. The resulting equality holds in the full `W^{k+1,p}` space: uniqueness of weak
derivatives determines all its higher components from its value.

This supplies the compact-support step in the density of test functions in whole-space
Sobolev spaces. The remaining step is to approximate arbitrary higher-order Sobolev
functions by compactly supported ones.

The mollification argument follows Evans, *Partial Differential Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Forget the derivatives above first order in a higher-order Sobolev function. -/
def firstOrder : (k : ℕ) → Wkp mu Omega p (k + 1) → W1p mu Omega p
  | 0, u => u
  | k + 1, u => firstOrder k (lowerOrder (k + 1) u)

/-- The first-order part of a first-order Sobolev function is itself. -/
@[simp] theorem firstOrder_zero (u : Wkp mu Omega p 1) : firstOrder 0 u = u := by
  simp only [firstOrder]

/-- Forgetting one derivative before taking the first-order part has no effect. -/
@[simp] theorem firstOrder_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    firstOrder (k + 1) u = firstOrder k (lowerOrder (k + 1) u) := by
  simp only [firstOrder]

/-- Forgetting higher derivatives preserves the `Lᵖ` value. -/
@[simp] theorem value_firstOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    W1p.value (firstOrder k u) = value (k + 1) u := by
  induction k with
  | zero => exact (value_one u).symm
  | succ k ih =>
      calc
        W1p.value (firstOrder (k + 1) u) =
            value (k + 1) (lowerOrder (k + 1) u) := ih _
        _ = value (k + 1 + 1) u := (value_succ (k + 1) u).symm

/-- First-order projection commutes with whole-space mollification. -/
theorem firstOrder_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    firstOrder k (normedBumpL hp phi (k + 1) u) =
      W1p.normedBumpL hp phi (firstOrder k u) := by
  induction k with
  | zero => simpa only [firstOrder] using congrArg (fun f => f u) (normedBumpL_one hp phi)
  | succ k ih =>
      rw [firstOrder, lowerOrder_normedBumpL, ih, firstOrder]

/-- Mollification of a higher-order Sobolev function whose first-order jet has compact
support is the image of a smooth compactly supported test function. -/
theorem normedBumpL_mem_range_of_ae_eq_zero (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (k : ℕ) (u : Wkp mu ⊤ p (k + 1))
    {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      (firstOrder k u : Sobolev1JetLp mu ⊤ p) x = 0) :
    normedBumpL hp phi (k + 1) u ∈
      LinearMap.range (ofTestFunctionₗ (mu := mu) (Omega := ⊤) (p := p) (k + 1)) := by
  obtain ⟨psi, hpsi⟩ := W1p.normedBumpL_mem_range_of_ae_eq_zero hp phi hK hu
  refine ⟨psi, ext (k + 1) ?_⟩
  calc
    value (k + 1) (ofTestFunctionₗ (mu := mu) (Omega := (⊤ : Opens E)) (p := p)
        (k + 1) psi) = W1p.value (W1p.ofTestFunctionₗ mu ⊤ p psi) := by
          exact (Wkp.value_ofTestFunctionₗ (mu := mu) (Omega := (⊤ : Opens E))
            (p := p) (k + 1) psi).trans (W1p.value_ofTestFunctionₗ (mu := mu)
              (Omega := (⊤ : Opens E)) (p := p) psi).symm
    _ = W1p.value (W1p.normedBumpL hp phi (firstOrder k u)) := congrArg W1p.value hpsi
    _ = value (k + 1) (normedBumpL hp phi (k + 1) u) := by
      rw [← firstOrder_normedBumpL, value_firstOrder]

/-- A whole-space higher-order Sobolev function whose first-order jet vanishes outside a
compact set belongs to the closure of test functions in the full higher-order norm. -/
theorem mem_wkp0Submodule_top_of_firstOrder_ae_eq_zero (hp : p ≠ ∞)
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      (firstOrder k u : Sobolev1JetLp mu ⊤ p) x = 0) :
    u ∈ wkp0Submodule mu ⊤ p (k + 1) := by
  let phi : ℕ → ContDiffBump (0 : E) := fun j =>
    ⟨1 / ((j : ℝ) + 1) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun j => (phi j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact (wkp0Submodule mu ⊤ p (k + 1)).isClosed.mem_of_tendsto
    (tendsto_normedBumpL hp hphi (k + 1) u) (Eventually.of_forall fun j => by
      obtain ⟨psi, hpsi⟩ :=
        normedBumpL_mem_range_of_ae_eq_zero hp (phi j) k u hK hu
      rw [← hpsi]
      exact ofTestFunctionₗ_mem_wkp0Submodule (mu := mu) (Omega := (⊤ : Opens E))
        (p := p) (k + 1) psi)

end TauCeti.Wkp

end
