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

The first-order part of a `W^{k+1,p}` function records its value and weak gradient. If the
value vanishes almost everywhere outside a compact set, the gradient vanishes there too,
since the complement is open. A smooth mollification is then a test function. The resulting
equality holds in the full `W^{k+1,p}` space: uniqueness of weak derivatives determines all
its higher components from its value.

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

/-- First-order projection commutes with whole-space mollification. -/
theorem firstOrder_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) :
    firstOrder k (normedBumpL hp phi (k + 1) u) =
      W1p.normedBumpL hp phi (firstOrder k u) := by
  induction k with
  | zero => simpa only [firstOrder_zero] using congrArg (fun f => f u) (normedBumpL_one hp phi)
  | succ k ih =>
      rw [firstOrder_succ, lowerOrder_normedBumpL, ih, firstOrder_succ]

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

/-- If the value vanishes almost everywhere on an open subset, so does its first-order jet. -/
theorem firstOrder_ae_eq_zero_of_value_ae_eq_zero
    (k : ℕ) (u : Wkp mu Omega p (k + 1)) {V : Opens E} (hV : V ≤ Omega)
    (hu : ∀ᵐ x ∂mu.restrict (V : Set E), value (k + 1) u x = 0) :
    ∀ᵐ x ∂mu.restrict (V : Set E),
      (firstOrder k u : Sobolev1JetLp mu Omega p) x = 0 := by
  let v := firstOrder k u
  have hval : ∀ᵐ x ∂mu.restrict (V : Set E), W1p.value v x = 0 := by
    simpa only [v, value_firstOrder] using hu
  have hgrad := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero hV hval
  have hvalmu := (ae_restrict_iff' V.isOpen.measurableSet).1 hval
  have hgradmu := (ae_restrict_iff' V.isOpen.measurableSet).1 hgrad
  have hvalApply := (ae_restrict_iff' Omega.isOpen.measurableSet).1
    (W1p.value_apply_ae v)
  have hgradApply := (ae_restrict_iff' Omega.isOpen.measurableSet).1
    (W1p.gradient_apply_ae v)
  rw [ae_restrict_iff' V.isOpen.measurableSet]
  filter_upwards [hvalmu, hgradmu, hvalApply, hgradApply] with
    x hv hg hv' hg' hxV
  exact (WithLp.ext_iff _).2 (Prod.ext ((hv' (hV hxV)).symm.trans (hv hxV))
    ((hg' (hV hxV)).symm.trans (hg hxV)))

private theorem firstOrder_ae_eq_zero_of_value_ae_eq_zero_of_isCompact
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      value (k + 1) u x = 0) :
    ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      (firstOrder k u : Sobolev1JetLp mu ⊤ p) x = 0 := by
  let V : Opens E := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  have hvalmu : ∀ᵐ x ∂mu, x ∉ K → value (k + 1) u x = 0 := by
    simpa using hu
  have hvalV : ∀ᵐ x ∂mu.restrict (V : Set E), value (k + 1) u x = 0 := by
    rw [ae_restrict_iff' V.isOpen.measurableSet]
    filter_upwards [hvalmu] with x hx hxV
    exact hx hxV
  have hjetV := (ae_restrict_iff' V.isOpen.measurableSet).1
    (firstOrder_ae_eq_zero_of_value_ae_eq_zero k u le_top hvalV)
  simpa [V] using hjetV

/-- Mollifying a higher-order Sobolev function supported in a compact set produces a test
function representing the same higher-order Sobolev element. -/
theorem normedBumpL_mem_range_of_value_ae_eq_zero (hp : p ≠ ∞)
    (phi : ContDiffBump (0 : E)) (k : ℕ) (u : Wkp mu ⊤ p (k + 1))
    {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      value (k + 1) u x = 0) :
    normedBumpL hp phi (k + 1) u ∈
      LinearMap.range (ofTestFunctionₗ (mu := mu) (Omega := ⊤) (p := p) (k + 1)) :=
  normedBumpL_mem_range_of_ae_eq_zero hp phi k u hK
    (firstOrder_ae_eq_zero_of_value_ae_eq_zero_of_isCompact k u hK hu)

/-- A compactly supported whole-space higher-order Sobolev function belongs to the closure
of test functions in the full higher-order norm. -/
theorem mem_wkp0Submodule_top_of_value_ae_eq_zero (hp : p ≠ ∞)
    (k : ℕ) (u : Wkp mu ⊤ p (k + 1)) {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      value (k + 1) u x = 0) :
    u ∈ wkp0Submodule mu ⊤ p (k + 1) :=
  mem_wkp0Submodule_top_of_firstOrder_ae_eq_zero hp k u hK
    (firstOrder_ae_eq_zero_of_value_ae_eq_zero_of_isCompact k u hK hu)

end TauCeti.Wkp

end
