/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ApproximateIdentity
public import TauCeti.Analysis.Sobolev.Wkp.Zero
import TauCeti.Analysis.Sobolev.SmoothCutoff
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin

/-!
# Compactly supported higher-order Sobolev functions

The first-order part of a `W^{k+1,p}` function records its value and weak gradient. If the
value vanishes almost everywhere outside a compact set, the gradient vanishes there too,
since the complement is open. A smooth mollification on the whole space is then a test function.
The resulting equality holds in the full `W^{k+1,p}` space: uniqueness of weak derivatives
determines all its higher components from its value.

On an arbitrary open set `Ω` and for `1 ≤ p < ∞`, multiplying a `C^∞(Ω)` Sobolev representative by
expanding smooth cutoffs approximates it in `W^{k,p}(Ω)` by elements vanishing almost everywhere on
`Ω` outside compact subsets of `E`. Combined with Meyers–Serrin smooth density on `Ω`, such
bounded-support elements are dense in `W^{k,p}(Ω)` without any boundedness or boundary regularity
assumption on `Ω` (`TauCeti.Wkp.dense_exists_isCompact_value_ae_eq_zero`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §§5.3.1–5.3.2.
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
  | zero =>
      simp only [firstOrder_zero]
      exact congrArg (fun f => f u) (normedBumpL_one hp phi)
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
  exact W1p.coe_ae_eq_zero_of_value_ae_eq_zero hV (by simpa only [value_firstOrder] using hu)

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

/-- Expanding smooth cutoffs approximate any `W^{k,p}(Ω)` element represented by a smooth function
on `Ω` by elements whose values vanish almost everywhere outside compact subsets of `E`. -/
private theorem exists_tendsto_value_ae_eq_zero_of_contDiffOn (hp : p ≠ ∞) (k : ℕ)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    ∃ (v : ℕ → Wkp mu Omega p k) (K : ℕ → Set E), (∀ n, IsCompact (K n)) ∧
      (∀ n, ∀ᵐ x ∂mu.restrict Omega, x ∉ K n → value k (v n) x = 0) ∧
      Tendsto v atTop (𝓝 u) := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  choose B hB using fun i : ℕ =>
    (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (χ.hasCompactSupport.iteratedFDeriv i)
  let χn (n : ℕ) (x : E) : ℝ := χ (((n : ℝ) + 1)⁻¹ • x)
  have hχn (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χn n) := χ.contDiff.comp (contDiff_const_smul _)
  have hcpt (n : ℕ) : HasCompactSupport (χn n) := χ.hasCompactSupport.comp_smul (by positivity)
  choose v hv using fun n => exists_value_ae_eq_mul_of_hasCompactSupport k (hχn n) (hcpt n) u
  refine ⟨v, fun n => tsupport (χn n), fun n => (hcpt n).isCompact, fun n => ?_, ?_⟩
  · filter_upwards [hv n] with x hx hxK
    rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul]
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hfk : ContDiffOn ℝ k f Omega := hf.of_le (mod_cast le_top)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k (v n - u)
        (f := fun x => χn n x • f x - f x)
        ((((hχn n).of_le (mod_cast le_top)).contDiffOn.smul hfk).sub hfk) ?_) ?_
    · filter_upwards [value_sub k (v n) u ▸ Lp.coeFn_sub (value k (v n)) (value k u),
        hv n, hu] with x hsub hvn hux
      simp only [hsub, Pi.sub_apply, hvn, hux, smul_eq_mul]
    · rw [← Finset.sum_const_zero (s := Finset.range (k + 1))]
      refine tendsto_finsetSum (Finset.range (k + 1)) fun i hi => ?_
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hfi : ContDiffOn ℝ i f Omega := hf.of_le (mod_cast le_top)
      have he := tendsto_eLpNorm_iteratedFDeriv_cutoff_sub_of_isOpen Omega.isOpen hp
        (r := fun n : ℕ => (n : ℝ) + 1)
        (tendsto_atTop_mono (fun n : ℕ => by linarith) tendsto_natCast_atTop_atTop)
        (χ.contDiff.of_le (mod_cast le_top)) χ.eventuallyEq_one (fun j _ x => hB j x) hfi
        (fun j hj => memLp_iteratedFDeriv_of_contDiffOn k u hfk hu j (hj.trans hi'))
      have hcongr (n : ℕ) :
          eLpNorm (iteratedFDeriv ℝ i (fun x => χn n x • f x - f x)) p (mu.restrict Omega) =
            eLpNorm (iteratedFDeriv ℝ i (fun x => χn n x • f x) - iteratedFDeriv ℝ i f) p
              (mu.restrict Omega) :=
        eLpNorm_congr_ae (by
          filter_upwards [ae_restrict_mem Omega.isOpen.measurableSet] with x hx
          have hfx := hfi.contDiffAt (Omega.isOpen.mem_nhds hx)
          exact fun_iteratedFDeriv_sub_apply
            ((((hχn n).of_le (mod_cast le_top)).contDiffAt).smul hfx) hfx)
      simpa only [Function.comp_def, ← toReal_eLpNorm, hcongr, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he

/-- On an arbitrary open set `Ω` and for `1 ≤ p < ∞`, elements of `W^{k,p}(Ω)` whose value
vanishes almost everywhere outside a compact subset of `E` are dense in `W^{k,p}(Ω)`. -/
theorem dense_exists_isCompact_value_ae_eq_zero (hp : p ≠ ∞) (k : ℕ) :
    Dense {u : Wkp mu Omega p k | ∃ K : Set E, IsCompact K ∧
      ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k u x = 0} := by
  intro u
  have hsub : {v : Wkp mu Omega p k | ∃ f : E → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f Omega ∧
      (value k v : E → ℝ) =ᵐ[mu.restrict Omega] f} ⊆
        closure {v : Wkp mu Omega p k | ∃ K : Set E, IsCompact K ∧
          ∀ᵐ x ∂mu.restrict Omega, x ∉ K → value k v x = 0} := by
    rintro v ⟨f, hf, hvf⟩
    obtain ⟨w, K, hK, hvan, hw⟩ := exists_tendsto_value_ae_eq_zero_of_contDiffOn hp k v hf hvf
    exact mem_closure_of_tendsto hw (Eventually.of_forall fun n => ⟨K n, hK n, hvan n⟩)
  have hcl := closure_minimal hsub isClosed_closure
  rw [(dense_contDiffOn_representatives (mu := mu) (Omega := Omega) hp k).closure_eq] at hcl
  exact hcl (mem_univ u)

end TauCeti.Wkp

end
