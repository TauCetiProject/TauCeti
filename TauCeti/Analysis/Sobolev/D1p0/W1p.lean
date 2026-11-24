/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.D1p0.Basic
public import TauCeti.Analysis.Sobolev.W1p.Zero
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# `W^{1,p}_0(Ω)` inside `D^{1,p}_0(Ω)`

An element `u` of `W^{1,p}_0(Ω)` is a limit of test functions `φₖ` in the graph norm, so the
gradients `∇φₖ` converge to `∇u` in `Lᵖ(Ω, E)`. Hence `∇u` lies in `D^{1,p}_0(Ω)`, the closure of
the test-function gradients. For a Haar measure and the Sobolev conjugate `1/p⋆ + 1/n = 1/p` with
`p⋆ ≠ ∞`, the Sobolev embedding sends this element to `u` itself: it is the `L^{p⋆}` limit of the
`φₖ`, which also converge to `u` in `Lᵖ`, and two limits in measure agree almost everywhere. In
particular every element of `W^{1,p}_0(Ω)` lies in `L^{p⋆}(Ω)`, with the
Gagliardo--Nirenberg--Sobolev bound `‖u‖_{p⋆} ≤ C ‖∇u‖_p`.

On the whole space `W^{1,p}_0 = W^{1,p}` for `p < ∞` (`TauCeti.w1p0Submodule_top_eq_top`), so every
element of `W^{1,p}(E)` lies in the range of the Sobolev embedding of `D^{1,p}_0(E)`.

## Main definitions

* `TauCeti.W1p.toD1p0`: the gradient of an element of `W^{1,p}_0(Ω)`, as an element of
  `D^{1,p}_0(Ω)`.

## Main results

* `TauCeti.W1p.sobolevEmbeddingL_toD1p0_ae_eq`: the Sobolev embedding sends `W1p.toD1p0 u` to
  the value of `u`.
* `TauCeti.W1p.exists_d1p0_of_top`: on the whole space, every element of `W^{1,p}(E)` is the
  image under the Sobolev embedding of an element of `D^{1,p}_0(E)` with the same gradient.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set Filter TopologicalSpace
open scoped Distributions ENNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Test functions converging to `u ∈ W^{1,p}_0(Ω)` in the graph norm. -/
private theorem W1p.exists_seq_tendsto {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    ∃ phi : ℕ → 𝓓(Omega, ℝ),
      Tendsto (fun k => W1p.ofTestFunctionₗ mu Omega p (phi k)) atTop (𝓝 u) := by
  rw [← SetLike.mem_coe, coe_w1p0Submodule, mem_closure_iff_seq_limit] at hu
  obtain ⟨w, hw, hlim⟩ := hu
  choose phi hphi using hw
  exact ⟨phi, by simpa only [hphi] using hlim⟩

/-- The gradient of an element of `W^{1,p}_0(Ω)` lies in `D^{1,p}_0(Ω)`. -/
theorem W1p.gradient_mem_d1p0Submodule {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.gradient u ∈ d1p0Submodule mu Omega p := by
  obtain ⟨phi, hphi⟩ := W1p.exists_seq_tendsto hu
  have hgrad := ((W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).continuous.tendsto u).comp
    hphi
  simp only [Function.comp_def, W1p.gradientL_apply, W1p.gradient_ofTestFunctionₗ] at hgrad
  rw [← SetLike.mem_coe, coe_d1p0Submodule]
  refine isClosed_closure.mem_of_tendsto hgrad (Eventually.of_forall fun k => subset_closure ?_)
  exact ⟨phi k, rfl⟩

/-- **`W^{1,p}_0(Ω) ⊆ D^{1,p}_0(Ω)`**: the gradient of an element of `W^{1,p}_0(Ω)`, as an
element of `D^{1,p}_0(Ω)`. -/
def W1p.toD1p0 (u : w1p0Submodule mu Omega p) : D1p0 mu Omega p :=
  ⟨W1p.gradient (u : W1p mu Omega p), W1p.gradient_mem_d1p0Submodule u.property⟩

@[simp]
theorem W1p.coe_toD1p0 (u : w1p0Submodule mu Omega p) :
    (W1p.toD1p0 u : Lp E p (mu.restrict Omega)) = W1p.gradient (u : W1p mu Omega p) :=
  (rfl)

variable {pstar : ENNReal}

/-- **The Sobolev embedding on `W^{1,p}_0(Ω)`**: for the Sobolev conjugate `p⋆ ≠ ∞`, the Sobolev
embedding of `D^{1,p}_0(Ω)` sends the gradient of `u ∈ W^{1,p}_0(Ω)` to the value of `u`. -/
theorem W1p.sobolevEmbeddingL_toD1p0_ae_eq (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : w1p0Submodule mu Omega p) :
    (D1p0.sobolevEmbeddingL hexp (W1p.toD1p0 u) : E → ℝ) =ᵐ[mu.restrict Omega]
      W1p.value (u : W1p mu Omega p) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨phi, hphi⟩ := W1p.exists_seq_tendsto u.property
  -- The values converge in `Lᵖ`.
  have hval := ((W1p.valueL (mu := mu) (Omega := Omega) (p := p)).continuous.tendsto _).comp hphi
  -- The gradients converge in `D^{1,p}_0(Ω)`, so the embedded test functions converge in
  -- `L^{p⋆}`.
  have hgrad : Tendsto (fun k => D1p0.ofTestFunctionₗ mu Omega p (phi k)) atTop
      (𝓝 (W1p.toD1p0 u)) := by
    apply tendsto_subtype_rng.mpr
    have := ((W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).continuous.tendsto _).comp hphi
    simpa [Function.comp_def, D1p0.coe_ofTestFunctionₗ, W1p.gradientL_apply] using this
  have hemb := ((D1p0.sobolevEmbeddingL (mu := mu) (Omega := Omega) hexp).continuous.tendsto
    _).comp hgrad
  simp only [Function.comp_def, D1p0.sobolevEmbeddingL_ofTestFunctionₗ hpstar] at hemb
  simp only [Function.comp_def, W1p.valueL_apply, W1p.value_ofTestFunctionₗ] at hval
  -- Both sequences are almost everywhere the test functions themselves.
  have hm1 : TendstoInMeasure (mu.restrict Omega) (fun k => (phi k : E → ℝ)) atTop
      (D1p0.sobolevEmbeddingL hexp (W1p.toD1p0 u)) :=
    (tendstoInMeasure_of_tendsto_Lp hemb).congr_left fun k => testFunctionLp_apply_ae pstar _
  have hm2 : TendstoInMeasure (mu.restrict Omega) (fun k => (phi k : E → ℝ)) atTop
      (W1p.value (u : W1p mu Omega p)) :=
    (tendstoInMeasure_of_tendsto_Lp hval).congr_left fun k => testFunctionLp_apply_ae p _
  exact tendstoInMeasure_ae_unique hm1 hm2

/-- **`W^{1,p}(E)` inside the range of the Sobolev embedding.** On the whole space, for `1 ≤ p`
and the Sobolev conjugate `p⋆ ≠ ∞` (which force `p < ∞`), every `u ∈ W^{1,p}(E)` is the image
under the Sobolev embedding of an element of `D^{1,p}_0(E)` whose gradient is the weak gradient
of `u`. -/
theorem W1p.exists_d1p0_of_top (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (u : W1p mu ⊤ p) :
    ∃ v : D1p0 mu ⊤ p, (v : Lp E p (mu.restrict ⊤)) = W1p.gradient u ∧
      (D1p0.sobolevEmbeddingL hexp v : E → ℝ) =ᵐ[mu.restrict ⊤] W1p.value u := by
  have hp : p ≠ ∞ := by
    rintro rfl
    simp at hexp
  exact ⟨W1p.toD1p0 ⟨u, W1p.mem_w1p0Submodule_top hp u⟩, rfl,
    W1p.sobolevEmbeddingL_toD1p0_ae_eq hpstar hexp ⟨u, W1p.mem_w1p0Submodule_top hp u⟩⟩

end TauCeti
