/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Translation
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
public import TauCeti.MeasureTheory.Function.Lp.MollificationBridge

/-!
# Mollification on `W^{1,p}(ℝⁿ)`

The smooth approximate identity `TauCeti.normedBumpLp` averages the translates of an `Lᵖ` class
against a normalized bump.  Applied to value-gradient jets it preserves `W^{1,p}(ℝⁿ)`: translation
preserves the weak-derivative identities on the whole space
(`TauCeti.Sobolev1JetLp.translateLp_mem_w1pSubmodule`), and the average is a Bochner integral of
translates, which stays in the closed subspace `W^{1,p}(ℝⁿ)`.  This gives the mollification
operator `TauCeti.W1p.normedBumpL` on `W^{1,p}(ℝⁿ)`, and the strong convergence of the
approximate identity on jets is exactly its convergence to the identity in the Sobolev norm
(`TauCeti.W1p.tendsto_normedBumpL`).  No commutation of derivatives with convolution is needed:
the weak gradient is mollified together with the value because both are components of one jet.

If the jet of `u` vanishes outside a compact set, the mollified jet has a smooth compactly
supported representative (`TauCeti.normedBumpLp_ae_eq_convolution`), so the mollification is a
test function (`TauCeti.W1p.normedBumpL_mem_range_of_ae_eq_zero`).

The ambient space is any finite-dimensional real inner product space `E` with an additive Haar
measure; `ℝⁿ` stands for the whole-space case `Ω = ⊤`.

## Main declarations

* `TauCeti.Sobolev1JetLp.normedBumpLp_mem_w1pSubmodule`: mollification preserves `W^{1,p}(ℝⁿ)`.
* `TauCeti.W1p.normedBumpL`: mollification by a normalized smooth bump, as a continuous linear
  operator on `W^{1,p}(ℝⁿ)`.
* `TauCeti.W1p.norm_normedBumpL_le_one`: this operator is a contraction.
* `TauCeti.W1p.tendsto_normedBumpL`: mollifications with shrinking bumps converge in `W^{1,p}`.
* `TauCeti.W1p.normedBumpL_mem_range_of_ae_eq_zero`: mollifying a Sobolev function whose jet
  vanishes outside a compact set produces a test function.

## References

L. C. Evans, *Partial Differential Equations*, §5.3.1; H. Brezis, *Functional Analysis, Sobolev
Spaces and Partial Differential Equations*, Theorem 9.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions ENNReal Topology

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- The whole-space restriction of an additive Haar measure is the measure itself. -/
local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

/-- **Mollification preserves `W^{1,p}(ℝⁿ)`.**  The mollified jet is a Bochner integral of
translates of the jet, each of which lies in the closed subspace `W^{1,p}(ℝⁿ)`. -/
theorem Sobolev1JetLp.normedBumpLp_mem_w1pSubmodule (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {J : Sobolev1JetLp mu ⊤ p} (hJ : J ∈ w1pSubmodule mu ⊤ p) :
    normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) J ∈ w1pSubmodule mu ⊤ p := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E)
  let S := (w1pSubmodule mu ⊤ p).toSubmodule
  let g : E → S := fun t =>
    ⟨phi.normed nu t • nu.translateLp p (-t) J,
      S.smul_mem _ (Sobolev1JetLp.translateLp_mem_w1pSubmodule (-t) hJ)⟩
  have hint : normedBumpLp hp phi nu J = S.subtypeₗᵢ (∫ t, g t ∂nu) := by
    rw [← LinearIsometry.integral_comp_comm, normedBumpLp_apply]
    simp only [g, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype]
  rw [hint]
  exact (∫ t, g t ∂nu).2

/-- **Mollification on `W^{1,p}(ℝⁿ)`**: averaging the translates of a Sobolev function against
the normalized form of a smooth bump, as a continuous linear operator.  The value and the weak
gradient are mollified together, as the two components of one `Lᵖ` jet. -/
def W1p.normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    W1p mu ⊤ p →L[ℝ] W1p mu ⊤ p :=
  ContinuousLinearMap.codRestrict
    ((normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E))).comp
      (w1pSubmodule mu ⊤ p).toSubmodule.subtypeL)
    (w1pSubmodule mu ⊤ p).toSubmodule
    fun u => Sobolev1JetLp.normedBumpLp_mem_w1pSubmodule hp phi u.2

/-- The jet of the mollification is the mollification of the jet. -/
theorem W1p.coe_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (u : W1p mu ⊤ p) :
    ((W1p.normedBumpL hp phi u : W1p mu ⊤ p) : Sobolev1JetLp mu ⊤ p) =
      normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (u : Sobolev1JetLp mu ⊤ p) :=
  (rfl)

/-- Mollification by a normalized nonnegative bump does not increase the `W^{1,p}` norm when
`p < ∞`. -/
theorem W1p.norm_normedBumpL_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    ‖W1p.normedBumpL (mu := mu) hp phi‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [← Submodule.norm_coe, W1p.coe_normedBumpL, ← Submodule.norm_coe u]
  exact ContinuousLinearMap.le_of_opNorm_le _ (norm_normedBumpLp_le_one hp phi) _

/-- **Mollification converges in `W^{1,p}(ℝⁿ)`.**  For `1 ≤ p < ∞`, mollifying a Sobolev
function with normalized smooth bumps whose radii shrink to zero converges to it in the Sobolev
norm. -/
theorem W1p.tendsto_normedBumpL (hp : p ≠ ∞) {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)} (hphi : Tendsto (fun i => (phi i).rOut) l (𝓝 0))
    (u : W1p mu ⊤ p) :
    Tendsto (fun i => W1p.normedBumpL hp (phi i) u) l (𝓝 u) := by
  rw [tendsto_subtype_rng]
  exact tendsto_normedBumpLp hp hphi (u : Sobolev1JetLp mu ⊤ p)

/-- **A compactly supported Sobolev function mollifies to a test function.**  If the jet of `u`
vanishes almost everywhere outside a compact set, its mollification has a smooth compactly
supported representative. -/
theorem W1p.normedBumpL_mem_range_of_ae_eq_zero (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {u : W1p mu ⊤ p} {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      (u : Sobolev1JetLp mu ⊤ p) x = 0) :
    W1p.normedBumpL hp phi u ∈ LinearMap.range (W1p.ofTestFunctionₗ mu ⊤ p) := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E)
  set J : Sobolev1JetLp mu ⊤ p := u.1 with hJdef
  let Jt : E → Sobolev1Jet E := K.indicator J
  have hJt_mem : MemLp Jt p nu := (Lp.memLp J).indicator hK.measurableSet
  have hJt_cpt : HasCompactSupport Jt :=
    HasCompactSupport.intro hK fun x hx => indicator_of_notMem hx _
  have hJ_eq : hJt_mem.toLp Jt = J := by
    apply Lp.ext
    filter_upwards [hJt_mem.coeFn_toLp, hu] with x hx hux
    rw [hx]
    by_cases hxK : x ∈ K
    · exact indicator_of_mem hxK _
    · simp only [Jt, indicator_of_notMem hxK, hux hxK]
  let conv : E → Sobolev1Jet E := phi.normed nu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, nu] Jt
  have hbridge : ((W1p.normedBumpL hp phi u : W1p mu ⊤ p) : Sobolev1JetLp mu ⊤ p) =ᵐ[nu] conv := by
    rw [W1p.coe_normedBumpL, ← hJdef, ← hJ_eq]
    exact normedBumpLp_ae_eq_convolution hp phi hJt_mem hJt_cpt
  have hconv_smooth : ContDiff ℝ (⊤ : ℕ∞) conv :=
    phi.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      phi.contDiff_normed (hJt_mem.locallyIntegrable Fact.out)
  have hconv_cpt : HasCompactSupport conv :=
    phi.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hJt_cpt
  let Phi : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨fun x => WithLp.fstL 2 ℝ ℝ E (conv x), (WithLp.fstL 2 ℝ ℝ E).contDiff.comp hconv_smooth,
      hconv_cpt.comp_left (map_zero _), subset_univ _⟩
  refine ⟨Phi, W1p.ext_value (Lp.ext ?_)⟩
  rw [W1p.value_ofTestFunctionₗ]
  filter_upwards [testFunctionLp_apply_ae (mu := mu) p Phi,
    W1p.value_apply_ae (W1p.normedBumpL hp phi u), hbridge] with x hPhi hvalue hconv
  rw [hPhi, hvalue, hconv]
  rfl

end TauCeti
