/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Haar invariance, linear transport, and sharpness of local Sobolev classes

On a finite-dimensional real normed space `E`, any two Borel additive Haar measures differ by a
positive finite scalar (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Consequently weak
derivatives (`TauCeti.HasWeakLineDerivOn`, `TauCeti.HasWeakFDerivOn`), local `Lᵖ` membership
(`TauCeti.MemLpLoc`), and local Sobolev membership (`TauCeti.MemWkpLoc`) of every order `k` and
every exponent `0 ≤ p ≤ ∞` are independent of the chosen additive Haar measure.

Because the pushforward of an additive Haar measure along a continuous linear equivalence
`A : E ≃L[ℝ] E'` is again an additive Haar measure (`ContinuousLinearEquiv.isAddHaarMeasure_map`),
testing against transported compactly supported smooth functions
(`ContinuousLinearEquiv.transportTestFunction`) pulls back weak derivatives and all local Lebesgue
and Sobolev classes along real-affine maps `x ↦ A x + b` between *arbitrary* finite-dimensional
real normed spaces `E` and `E'` equipped with additive Haar volumes — with no inner-product
structure on either space. This identifies local Sobolev classes across non-Euclidean models such
as `ℝ × ℝ`, `Fin n → ℝ`, and `EuclideanSpace ℝ (Fin n)`.

Finally, this file records sharpness and non-vacuity witnesses across dimensions and codomains:

* **Locality at infinity:** while `TauCeti.memWkpLoc_id` places `id : E → E` in every local
  Sobolev class, `TauCeti.memLp_id_univ_iff` shows `MemLp (id : E → E) p volume ↔ p = 0` on every
  nontrivial finite-dimensional space.
* **Dimension-dependent radial singularity:** `TauCeti.memLpLoc_norm_inv_iff_lt_finrank` shows
  `x ↦ ‖x‖⁻¹` lies in `MemLpLoc p U` near the origin of a nontrivial space `E` if and only if
  `p < Module.finrank ℝ E` (in particular `p < 3` on `EuclideanSpace ℝ (Fin 3)`), and
  `TauCeti.memLpLoc_norm_rpow_iff_gt_neg_finrank` gives the general threshold
  `-(Module.finrank ℝ E : ℝ) < s * p.toReal` for `x ↦ ‖x‖ ^ s`.
* **Non-Euclidean domain transport:** `(x, y) ↦ max |x| |y|` is the norm of `ℝ × ℝ`, hence lies in
  `W^{1,p}_loc` on `ℝ × ℝ` and transports across `EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ`.
* **Non-separable Banach codomains:** for `H = lp (fun _ : ℝ => ℝ) ∞`, the unit-basis map
  `x ↦ lp.single ∞ x 1` has `x ↦ ℓ (lp.single ∞ x 1)` vanishing outside a countable set — hence in
  `MemWkpLoc p U k` of every order `k` and exponent `p` — for every continuous linear functional
  `ℓ : StrongDual ℝ H` (`TauCeti.memWkpLoc_strongDual_comp_lp_single`), yet fails strong
  measurability and therefore lies outside `MemLpLoc p U` for *every* `0 ≤ p ≤ ∞` on any set `U`
  with nonempty interior (`TauCeti.not_memLpLoc_lp_single`).

## References

* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology Distributions

namespace TauCeti

/-! ### Measure scaling and additive Haar independence -/

section SmulMeasure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {Ω : Opens E} {u u' : E → F} {U : E → E →L[ℝ] F} {v : E} {c : ℝ≥0∞}

/-- Scaling the reference measure by a finite constant preserves weak directional derivatives. -/
theorem HasWeakLineDerivOn.smul_measure (h : HasWeakLineDerivOn μ Ω u u' v) (hc : c ≠ ∞) :
    HasWeakLineDerivOn (c • μ) Ω u u' v := by
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨h.completeSpace, h.locallyIntegrableOn.smul_measure hc,
      h.locallyIntegrableOn_deriv.smul_measure hc, fun φ => ?_⟩
  rw [integral_smul_measure, integral_smul_measure,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, smul_neg]

/-- Scaling the reference measure by a positive finite constant preserves and reflects weak
directional derivatives. -/
theorem HasWeakLineDerivOn.smul_measure_iff (hc₀ : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakLineDerivOn (c • μ) Ω u u' v ↔ HasWeakLineDerivOn μ Ω u u' v := by
  refine ⟨fun h => ?_, fun h => h.smul_measure hc⟩
  have h' := h.smul_measure (c := c⁻¹) (ENNReal.inv_ne_top.2 hc₀)
  rwa [smul_smul, ENNReal.inv_mul_cancel hc₀ hc, one_smul] at h'

/-- Scaling the reference measure by a finite constant preserves weak Fréchet derivatives. -/
theorem HasWeakFDerivOn.smul_measure (h : HasWeakFDerivOn μ Ω u U) (hc : c ≠ ∞) :
    HasWeakFDerivOn (c • μ) Ω u U :=
  hasWeakFDerivOn_iff.2 fun v => (h.hasWeakLineDerivOn v).smul_measure hc

/-- Scaling the reference measure by a positive finite constant preserves and reflects weak
Fréchet derivatives. -/
theorem HasWeakFDerivOn.smul_measure_iff (hc₀ : c ≠ 0) (hc : c ≠ ∞) :
    HasWeakFDerivOn (c • μ) Ω u U ↔ HasWeakFDerivOn μ Ω u U := by
  simp only [hasWeakFDerivOn_iff, HasWeakLineDerivOn.smul_measure_iff hc₀ hc]

end SmulMeasure

section HaarIndependence

/-- On a second-countable locally compact additive group, `Lᵖ` membership does not depend on the
choice of Borel additive Haar measure. -/
theorem _root_.MeasureTheory.MemLp.of_isAddHaarMeasure {G F : Type*} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
    {μ : Measure G} [μ.IsAddHaarMeasure] (ν : Measure G) [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {f : G → F} (hf : MemLp f p μ) : MemLp f p ν := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact hf.smul_measure ENNReal.coe_ne_top

/-- Equivalence form of `MeasureTheory.MemLp.of_isAddHaarMeasure`. -/
theorem _root_.MeasureTheory.memLp_iff_of_isAddHaarMeasure {G F : Type*} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {p : ℝ≥0∞} {f : G → F} :
    MemLp f p μ ↔ MemLp f p ν :=
  ⟨fun h => h.of_isAddHaarMeasure ν, fun h => h.of_isAddHaarMeasure μ⟩

/-- Restricted `Lᵖ` membership on any subset `s` is independent of the choice of Borel additive
Haar measure. -/
theorem _root_.MeasureTheory.memLp_restrict_iff_of_isAddHaarMeasure {G F : Type*} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {s : Set G} {f : G → F} :
    MemLp f p (μ.restrict s) ↔ MemLp f p (ν.restrict s) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Measure.isAddLeftInvariant_eq_smul ν μ, Measure.restrict_smul]
    exact h.smul_measure ENNReal.coe_ne_top
  · rw [Measure.isAddLeftInvariant_eq_smul μ ν, Measure.restrict_smul]
    exact h.smul_measure ENNReal.coe_ne_top

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Weak directional derivatives on a finite-dimensional real normed space do not depend on the
choice of Borel additive Haar measure. -/
theorem HasWeakLineDerivOn.of_isAddHaarMeasure [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure]
    {Ω : Opens E} {u u' : E → F} {v : E} (h : HasWeakLineDerivOn μ Ω u u' v) :
    HasWeakLineDerivOn ν Ω u u' v := by
  rw [Measure.isAddLeftInvariant_eq_smul ν μ]
  exact h.smul_measure ENNReal.coe_ne_top

/-- Equivalence form of `HasWeakLineDerivOn.of_isAddHaarMeasure`. -/
theorem hasWeakLineDerivOn_iff_of_isAddHaarMeasure [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {Ω : Opens E} {u u' : E → F} {v : E} :
    HasWeakLineDerivOn μ Ω u u' v ↔ HasWeakLineDerivOn ν Ω u u' v :=
  ⟨fun h => h.of_isAddHaarMeasure ν, fun h => h.of_isAddHaarMeasure μ⟩

/-- Weak Fréchet derivatives on a finite-dimensional real normed space do not depend on the choice
of Borel additive Haar measure. -/
theorem HasWeakFDerivOn.of_isAddHaarMeasure [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure]
    {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    HasWeakFDerivOn ν Ω u U :=
  hasWeakFDerivOn_iff.2 fun v => (h.hasWeakLineDerivOn v).of_isAddHaarMeasure ν

/-- Equivalence form of `HasWeakFDerivOn.of_isAddHaarMeasure`. -/
theorem hasWeakFDerivOn_iff_of_isAddHaarMeasure [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {Ω : Opens E} {u : E → F} {U : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u U ↔ HasWeakFDerivOn ν Ω u U :=
  ⟨fun h => h.of_isAddHaarMeasure ν, fun h => h.of_isAddHaarMeasure μ⟩

/-- On any locally compact topological additive group (without second-countability), restricted
`Lᵖ` membership on a compact set `K` is independent of the Borel additive Haar measure. -/
theorem _root_.MeasureTheory.memLp_restrict_isCompact_iff_of_isAddHaarMeasure {G F : Type*}
    [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ℝ≥0∞} {K : Set G} (hK : IsCompact K) {f : G → F} :
    MemLp f p (μ.restrict K) ↔ MemLp f p (ν.restrict K) := by
  have hrestrict (ρ σ : Measure G) [ρ.IsAddHaarMeasure] [σ.IsAddHaarMeasure] :
      ρ.restrict K = Measure.addHaarScalarFactor ρ σ • σ.restrict K := by
    ext t ht
    rw [Measure.restrict_apply ht, smul_apply, Measure.restrict_apply ht]
    exact Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ρ σ
      (hK.closure.of_isClosed_subset isClosed_closure (closure_mono inter_subset_right))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hrestrict ν μ]
    exact h.smul_measure ENNReal.coe_ne_top
  · rw [hrestrict μ ν]
    exact h.smul_measure ENNReal.coe_ne_top

/-- Local `Lᵖ` membership on a locally compact topological additive group is independent of the
Borel additive Haar `MeasureSpace` instance (without assuming second-countability). -/
theorem memLpLoc_iff_of_isAddHaarMeasure {G F : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup F] (m₁ m₂ : MeasureSpace G)
    [hb₁ : @BorelSpace G _ m₁.toMeasurableSpace] [hb₂ : @BorelSpace G _ m₂.toMeasurableSpace]
    [hh₁ : @Measure.IsAddHaarMeasure G _ _ m₁.toMeasurableSpace m₁.volume]
    [hh₂ : @Measure.IsAddHaarMeasure G _ _ m₂.toMeasurableSpace m₂.volume]
    {p : ℝ≥0∞} {U : Set G} {f : G → F} :
    @MemLpLoc G F _ m₁ _ p U f ↔ @MemLpLoc G F _ m₂ _ p U f := by
  obtain @⟨ms₁, μ₁⟩ := m₁
  obtain @⟨ms₂, μ₂⟩ := m₂
  cases hb₁.measurable_eq
  cases hb₂.measurable_eq
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have : μ₁.IsAddHaarMeasure := hh₁
  have : μ₂.IsAddHaarMeasure := hh₂
  let m₁' : MeasureSpace G := @MeasureSpace.mk G (borel G) μ₁
  let m₂' : MeasureSpace G := @MeasureSpace.mk G (borel G) μ₂
  rw [@memLpLoc_iff G F _ m₁' _, @memLpLoc_iff G F _ m₂' _]
  exact forall₃_congr fun _ _ hK => memLp_restrict_isCompact_iff_of_isAddHaarMeasure μ₁ μ₂ hK

private theorem memWkpLoc_iff_of_isAddHaarMeasure_aux.{u, w} {E : Type u} {F : Type (max u w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (m₁ m₂ : MeasureSpace E)
    [hb₁ : @BorelSpace E _ m₁.toMeasurableSpace] [hb₂ : @BorelSpace E _ m₂.toMeasurableSpace]
    [hh₁ : @Measure.IsAddHaarMeasure E _ _ m₁.toMeasurableSpace m₁.volume]
    [hh₂ : @Measure.IsAddHaarMeasure E _ _ m₂.toMeasurableSpace m₂.volume]
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ m₁ p U k F _ _ f ↔ @MemWkpLoc E _ _ m₂ p U k F _ _ f := by
  obtain @⟨ms₁, μ₁⟩ := m₁
  obtain @⟨ms₂, μ₂⟩ := m₂
  cases hb₁.measurable_eq
  cases hb₂.measurable_eq
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have : μ₁.IsAddHaarMeasure := hh₁
  have : μ₂.IsAddHaarMeasure := hh₂
  let m₁' : MeasureSpace E := @MeasureSpace.mk E (borel E) μ₁
  let m₂' : MeasureSpace E := @MeasureSpace.mk E (borel E) μ₂
  induction k generalizing F with
  | zero =>
    rw [@memWkpLoc_zero_iff E F _ _ m₁', @memWkpLoc_zero_iff E F _ _ m₂']
    exact memLpLoc_iff_of_isAddHaarMeasure (F := F) m₁' m₂'
  | succ k ih =>
    rw [@memWkpLoc_succ_iff E F _ _ m₁', @memWkpLoc_succ_iff E F _ _ m₂']
    exact and_congr (memLpLoc_iff_of_isAddHaarMeasure (F := F) m₁' m₂')
      (exists_congr fun D => and_congr (hasWeakFDerivOn_iff_of_isAddHaarMeasure μ₁ μ₂) ih)

/-- Local Sobolev membership of every order `k` and exponent `p` on a finite-dimensional real
normed space is independent of the Borel additive Haar `MeasureSpace` instance. -/
theorem memWkpLoc_iff_of_isAddHaarMeasure.{u, v} {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (m₁ m₂ : MeasureSpace E)
    [hb₁ : @BorelSpace E _ m₁.toMeasurableSpace] [hb₂ : @BorelSpace E _ m₂.toMeasurableSpace]
    [hh₁ : @Measure.IsAddHaarMeasure E _ _ m₁.toMeasurableSpace m₁.volume]
    [hh₂ : @Measure.IsAddHaarMeasure E _ _ m₂.toMeasurableSpace m₂.volume]
    {p : ℝ≥0∞} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ m₁ p U k F _ _ f ↔ @MemWkpLoc E _ _ m₂ p U k F _ _ f := by
  have ho₁ : @OpensMeasurableSpace E _ m₁.toMeasurableSpace :=
    @BorelSpace.opensMeasurable E _ m₁.toMeasurableSpace hb₁
  have ho₂ : @OpensMeasurableSpace E _ m₂.toMeasurableSpace :=
    @BorelSpace.opensMeasurable E _ m₂.toMeasurableSpace hb₂
  rw [← @ulift_memWkpLoc_iff.{u, v, u} E F _ _ m₁ ho₁ _ _,
    ← @ulift_memWkpLoc_iff.{u, v, u} E F _ _ m₂ ho₂ _ _]
  exact @memWkpLoc_iff_of_isAddHaarMeasure_aux.{u, v} E (ULift.{u, v} F) _ _ _ _ _
    m₁ m₂ hb₁ hb₂ hh₁ hh₂ _ _ _ _

end HaarIndependence

/-! ### Pullback along continuous linear equivalences and affine maps -/

section LinearEquivTransport

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Pullback of a weak directional derivative from the pushforward measure.** For any continuous
linear equivalence `e : E ≃L[ℝ] E'` between real normed spaces (without finite-dimensionality or
Haar hypotheses) mapping `V` into `Ω`, a weak derivative in direction `e v` with respect to
`μ.map e` pulls back to a weak derivative in direction `v` with respect to `μ`. -/
theorem HasWeakLineDerivOn.comp_continuousLinearEquiv_map [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace E'] [BorelSpace E'] {μ : Measure E} {V : Opens E} {Ω : Opens E'}
    {u u' : E' → F} {v : E} (e : E ≃L[ℝ] E')
    (hu : HasWeakLineDerivOn (μ.map e) Ω u u' (e v)) (hVΩ : MapsTo e V Ω) :
    HasWeakLineDerivOn μ V (fun x => u (e x)) (fun x => u' (e x)) v := by
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hli : ∀ {w : E' → F}, LocallyIntegrableOn w Ω (μ.map e) →
      LocallyIntegrableOn (fun x => w (e x)) V μ := fun hw x hx => by
    obtain ⟨s, hs, hws⟩ := hw (e x) (hVΩ hx)
    exact ⟨e ⁻¹' s, e.continuous.continuousWithinAt.tendsto_nhdsWithin hVΩ hs,
      hemb.integrableOn_map_iff.1 hws⟩
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨hu.completeSpace, hli hu.locallyIntegrableOn, hli hu.locallyIntegrableOn_deriv, fun φ => ?_⟩
  let ψ : 𝓓(Ω, ℝ) := e.transportTestFunction hVΩ φ
  have hline (x : E) :
      lineDeriv ℝ (ψ : E' → ℝ) (e x) (e v) = lineDeriv ℝ (φ : E → ℝ) x v := by
    rw [(ψ.contDiff.differentiable (by simp) (e x)).lineDeriv_eq_fderiv,
      (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv,
      e.fderiv_transportTestFunction hVΩ φ (e x), ContinuousLinearMap.comp_apply]
    simp
  have hleft : ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u (e x) ∂μ =
      ∫ y, lineDeriv ℝ (ψ : E' → ℝ) y (e v) • u y ∂(μ.map e) := by
    have hint := integrable_lineDeriv_smul_of_locallyIntegrableOn hu.locallyIntegrableOn ψ (e v)
    rw [integral_map e.continuous.measurable.aemeasurable hint.aestronglyMeasurable]
    simp_rw [hline]
  have hright : ∫ x, (φ : E → ℝ) x • u' (e x) ∂μ =
      ∫ y, (ψ : E' → ℝ) y • u' y ∂(μ.map e) := by
    rw [integral_map e.continuous.measurable.aemeasurable
      (ψ.integrable_smul hu.locallyIntegrableOn_deriv).aestronglyMeasurable]
    simp [ψ]
  rw [hleft, hright, hu.integral_lineDeriv_smul_eq_neg_integral_smul ψ]

/-- **Pullback of a weak directional derivative along `e : E ≃L[ℝ] E'` for additive Haar
measures.** Neither `E` nor `E'` need carry an inner product, and the Haar normalizations on `E`
and `E'` are arbitrary. -/
theorem HasWeakLineDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace E'] [BorelSpace E'] {μ : Measure E} {ν : Measure E'}
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {V : Opens E} {Ω : Opens E'}
    {u u' : E' → F} {v : E} (e : E ≃L[ℝ] E')
    (hu : HasWeakLineDerivOn ν Ω u u' (e v)) (hVΩ : MapsTo e V Ω) :
    HasWeakLineDerivOn μ V (fun x => u (e x)) (fun x => u' (e x)) v := by
  have : FiniteDimensional ℝ E' := Module.Finite.equiv e.toLinearEquiv
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  exact (hu.of_isAddHaarMeasure (μ.map e)).comp_continuousLinearEquiv_map e hVΩ

/-- **Pullback of a weak Fréchet derivative along `e : E ≃L[ℝ] E'` for additive Haar measures.** -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_of_isAddHaarMeasure
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace E'] [BorelSpace E'] {μ : Measure E} {ν : Measure E'}
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {V : Opens E} {Ω : Opens E'}
    {u : E' → F} {U : E' → E' →L[ℝ] F} (e : E ≃L[ℝ] E')
    (hu : HasWeakFDerivOn ν Ω u U) (hVΩ : MapsTo e V Ω) :
    HasWeakFDerivOn μ V (fun x => u (e x)) (fun x => (U (e x)).comp (e : E →L[ℝ] E')) :=
  hasWeakFDerivOn_iff.2 fun v =>
    (hu.hasWeakLineDerivOn (e v)).comp_continuousLinearEquiv_of_isAddHaarMeasure e hVΩ

/-- **Pullback of a weak Fréchet derivative along an affine equivalence `x ↦ e x + b`.** -/
theorem HasWeakFDerivOn.comp_continuousLinearEquiv_add_of_isAddHaarMeasure
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace E'] [BorelSpace E'] {μ : Measure E} {ν : Measure E'}
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {V : Opens E} {Ω : Opens E'}
    {u : E' → F} {U : E' → E' →L[ℝ] F}
    (hu : HasWeakFDerivOn ν Ω u U) (e : E ≃L[ℝ] E') (b : E')
    (hVΩ : MapsTo (fun x => e x + b) V Ω) :
    HasWeakFDerivOn μ V (fun x => u (e x + b)) (fun x => (U (e x + b)).comp (e : E →L[ℝ] E')) := by
  let Ω' : Opens E' := ⟨(· + b) ⁻¹' Ω, (continuous_add_const b).isOpen_preimage _ Ω.isOpen⟩
  exact (hu.comp_add_right (V := Ω') (h := b) fun _ hy => hy)
    |>.comp_continuousLinearEquiv_of_isAddHaarMeasure e hVΩ

/-- When `e : E ≃L[ℝ] E'` maps `V` onto `Ω`, weak Fréchet differentiability of `u ∘ e` on `V` is
equivalent to weak Fréchet differentiability of `u` on `Ω`. -/
theorem _root_.ContinuousLinearEquiv.hasWeakFDerivOn_comp_iff_of_isAddHaarMeasure
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace E'] [BorelSpace E'] {μ : Measure E} {ν : Measure E'}
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] {V : Opens E} {Ω : Opens E'}
    {u : E' → F} {U : E' → E' →L[ℝ] F} (e : E ≃L[ℝ] E')
    (hVΩ : MapsTo e V Ω) (hΩV : MapsTo e.symm Ω V) :
    HasWeakFDerivOn μ V (fun x => u (e x)) (fun x => (U (e x)).comp (e : E →L[ℝ] E')) ↔
      HasWeakFDerivOn ν Ω u U := by
  have : FiniteDimensional ℝ E' := Module.Finite.equiv e.toLinearEquiv
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv_of_isAddHaarMeasure e hVΩ⟩
  have h' := h.comp_continuousLinearEquiv_of_isAddHaarMeasure (μ := ν) e.symm hΩV
  convert h' using 1
  · ext y; simp
  · ext y w; simp

omit [NormedSpace ℝ F] in
/-- **Real-affine maps between finite-dimensional spaces preserve `MemLpLoc`.** For
`A : E ≃L[ℝ] E'`, `b : E'`, and `x ↦ A x + b` mapping `U` into `V`, precomposition maps
`MemLpLoc p V` into `MemLpLoc p U` for every exponent `0 ≤ p ≤ ∞`. -/
theorem MemLpLoc.comp_continuousLinearEquiv_add
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {u : E' → F}
    (hu : MemLpLoc p V u) (A : E ≃L[ℝ] E') (b : E')
    (hmaps : MapsTo (fun x => A x + b) U V) :
    MemLpLoc p U (fun x => u (A x + b)) := by
  have : FiniteDimensional ℝ E' := Module.Finite.equiv A.toLinearEquiv
  let φ : E ≃ₜ E' := A.toHomeomorph.trans (Homeomorph.addRight b)
  have hφ_eq : (φ : E → E') = (· + b) ∘ A := rfl
  have : (volume.map A : Measure E').IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  have : (volume.map φ : Measure E').IsAddHaarMeasure := by
    rw [hφ_eq, ← Measure.map_map (measurable_add_const b) A.continuous.measurable,
      map_add_right_eq_self]
    infer_instance
  refine memLpLoc_iff.2 fun K hKU hK => ?_
  have hφK : MemLp u p (volume.restrict (φ '' K)) :=
    memLpLoc_iff.1 hu (φ '' K) ((image_mono hKU).trans hmaps.image_subset) (hK.image φ.continuous)
  have hmapK : MemLp u p (((volume : Measure E).restrict K).map φ) := by
    rw [← φ.preimage_image K, ← φ.measurableEmbedding.restrict_map]
    exact (memLp_restrict_iff_of_isAddHaarMeasure (volume : Measure E') (volume.map φ)).1 hφK
  exact φ.measurableEmbedding.memLp_map_measure_iff.1 hmapK

omit [NormedSpace ℝ F] in
/-- Continuous linear equivalences between finite-dimensional spaces preserve `MemLpLoc`. -/
theorem MemLpLoc.comp_continuousLinearEquiv
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {u : E' → F}
    (hu : MemLpLoc p V u) (A : E ≃L[ℝ] E') (hmaps : MapsTo A U V) :
    MemLpLoc p U (fun x => u (A x)) := by
  simpa only [add_zero] using
    hu.comp_continuousLinearEquiv_add A 0 (by simpa only [add_zero] using hmaps)

omit [NormedSpace ℝ F] in
/-- A continuous linear equivalence mapping `U` onto `V` preserves and reflects `MemLpLoc`. -/
theorem _root_.ContinuousLinearEquiv.memLpLoc_comp_iff
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {u : E' → F}
    (A : E ≃L[ℝ] E') (hUV : MapsTo A U V) (hVU : MapsTo A.symm V U) :
    MemLpLoc p U (fun x => u (A x)) ↔ MemLpLoc p V u := by
  have : FiniteDimensional ℝ E' := Module.Finite.equiv A.toLinearEquiv
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv A hUV⟩
  simpa only [A.apply_symm_apply] using h.comp_continuousLinearEquiv A.symm hVU

private theorem comp_continuousLinearEquiv_add_aux.{u₁, u₂, w}
    {E : Type u₁} {E' : Type u₂} {F : Type (max u₁ u₂ w)}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {k : ℕ} {u : E' → F}
    (hu : MemWkpLoc p V k u) (A : E ≃L[ℝ] E') (b : E')
    (hmaps : MapsTo (fun z => A z + b) U V) :
    MemWkpLoc p U k (fun z => u (A z + b)) := by
  have : FiniteDimensional ℝ E' := Module.Finite.equiv A.toLinearEquiv
  let φ : E ≃ₜ E' := A.toHomeomorph.trans (Homeomorph.addRight b)
  have hint : MapsTo (fun z => A z + b) (Opens.interior U) (Opens.interior V) := by
    intro x hx
    exact interior_maximal ((image_mono interior_subset).trans hmaps.image_subset)
      (φ.isOpenMap _ isOpen_interior) ⟨x, hx, rfl⟩
  induction k generalizing F with
  | zero =>
    exact memWkpLoc_zero_iff.2
      ((memWkpLoc_zero_iff.1 hu).comp_continuousLinearEquiv_add A b hmaps)
  | succ k ih =>
    obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
    have := hD.completeSpace
    refine memWkpLoc_succ_iff.2
      ⟨hLp.comp_continuousLinearEquiv_add A b hmaps,
        fun z => ((ContinuousLinearMap.compL ℝ E E' F).flip (A : E →L[ℝ] E')) (D (A z + b)),
        ?_, (ih hk).clm_comp _⟩
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] using
      hD.comp_continuousLinearEquiv_add_of_isAddHaarMeasure A b hint

/-- **Real-affine changes of variables between finite-dimensional spaces preserve every Sobolev
order.** For `A : E ≃L[ℝ] E'`, `b : E'`, and `x ↦ A x + b` mapping `U` into `V`, precomposition
maps `MemWkpLoc p V k` into `MemWkpLoc p U k` for every `k : ℕ` and every `0 ≤ p ≤ ∞`, without
requiring an inner product on `E` or `E'`. -/
theorem MemWkpLoc.comp_continuousLinearEquiv_add.{u₁, u₂, v}
    {E : Type u₁} {E' : Type u₂} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {k : ℕ} {u : E' → F}
    (hu : MemWkpLoc p V k u) (A : E ≃L[ℝ] E') (b : E')
    (hmaps : MapsTo (fun z => A z + b) U V) :
    MemWkpLoc p U k (fun z => u (A z + b)) :=
  (ulift_memWkpLoc_iff.{u₁, v, max u₁ u₂}).1 <|
    comp_continuousLinearEquiv_add_aux.{u₁, u₂, v}
      ((ulift_memWkpLoc_iff.{u₂, v, max u₁ u₂}).2 hu) A b hmaps

/-- Continuous linear equivalences between finite-dimensional spaces preserve every order of
`MemWkpLoc`. -/
theorem MemWkpLoc.comp_continuousLinearEquiv
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {k : ℕ} {u : E' → F}
    (hu : MemWkpLoc p V k u) (A : E ≃L[ℝ] E') (hmaps : MapsTo A U V) :
    MemWkpLoc p U k (fun z => u (A z)) := by
  simpa only [add_zero] using
    hu.comp_continuousLinearEquiv_add A 0 (by simpa only [add_zero] using hmaps)

/-- A continuous linear equivalence mapping `U` onto `V` preserves and reflects `MemWkpLoc` of
every order `k` and exponent `p`. -/
theorem _root_.ContinuousLinearEquiv.memWkpLoc_comp_iff
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
    [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
    {p : ℝ≥0∞} {U : Set E} {V : Set E'} {k : ℕ} {u : E' → F}
    (A : E ≃L[ℝ] E') (hUV : MapsTo A U V) (hVU : MapsTo A.symm V U) :
    MemWkpLoc p U k (fun z => u (A z)) ↔ MemWkpLoc p V k u := by
  have : FiniteDimensional ℝ E' := Module.Finite.equiv A.toLinearEquiv
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv A hUV⟩
  simpa only [A.apply_symm_apply] using h.comp_continuousLinearEquiv A.symm hVU

end LinearEquivTransport

/-! ### Non-vacuity, dimension-dependent singularities, and non-separable codomains -/

section SharpnessAndChecks

section FiniteDimChecks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **Failure of global `Lᵖ` integrability of the identity.** On any nontrivial finite-dimensional
real normed space with additive Haar volume, `id : E → E` is not in `MemLp _ p volume` for any
`p ≠ 0` (including `p = ∞`), contrasting with `TauCeti.memWkpLoc_id`. -/
theorem not_memLp_id_univ [Nontrivial E] {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    ¬ MemLp (id : E → E) p (volume : Measure E) := by
  intro h
  rcases eq_or_ne p ∞ with rfl | hptop
  · set R : ℝ := (eLpNorm (id : E → E) ⊤ (volume : Measure E)).toReal + 1
    have hlt : eLpNorm (id : E → E) ⊤ (volume : Measure E) < ENNReal.ofReal R := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
        ENNReal.ofReal_toReal h.eLpNorm_ne_top]
      exact ENNReal.lt_add_right h.eLpNorm_ne_top (by simp)
    rw [eLpNorm_exponent_top h.aestronglyMeasurable, eLpNormEssSup] at hlt
    have hae : ∀ᵐ x ∂(volume : Measure E), ‖x‖ₑ < ENNReal.ofReal R := ae_lt_of_essSup_lt hlt
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    let x₀ : E := ((R + 1) / ‖v‖) • v
    have hx₀ : ‖x₀‖ = R + 1 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hvpos.ne']
    have hball : ∀ x ∈ ball x₀ (1 / 2), ¬ ‖x‖ₑ < ENNReal.ofReal R := fun x hx => by
      rw [not_lt, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hdist : ‖x₀ - x‖ < 1 / 2 := by simpa [dist_eq_norm'] using mem_ball.1 hx
      have htri : ‖x₀‖ - ‖x₀ - x‖ ≤ ‖x‖ := by
        simpa only [sub_sub_cancel] using norm_sub_norm_le x₀ (x₀ - x)
      linarith
    exact absurd (measure_mono_null (fun x hx => hball x hx) (ae_iff.1 hae))
      (Metric.measure_ball_pos volume x₀ one_half_pos).ne'
  · exact Measure.not_integrable_norm_sub_rpow (volume : Measure E) p.toReal (0 : E)
      (by simpa only [sub_zero, id_eq] using
        (integrable_norm_rpow_iff h.aestronglyMeasurable hp0 hptop).2 h)

/-- On a nontrivial finite-dimensional real normed space with additive Haar volume, `id : E → E`
belongs to the global space `Lᵖ(E)` if and only if `p = 0`. -/
@[simp]
theorem memLp_id_univ_iff [Nontrivial E] {p : ℝ≥0∞} :
    MemLp (id : E → E) p (volume : Measure E) ↔ p = 0 :=
  ⟨fun h => by_contra fun hp0 => not_memLp_id_univ hp0 h,
    fun hp => hp ▸ memLp_zero_iff_aestronglyMeasurable.2 measurable_id.aestronglyMeasurable⟩

/-- **Dimension-dependent local `Lᵖ` threshold for `‖x‖⁻¹`.** On a nontrivial finite-dimensional
real normed space `E` with additive Haar volume and a neighbourhood `U` of `0`, `x ↦ ‖x‖⁻¹` lies in
`MemLpLoc p U` if and only if `p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv_iff_lt_finrank [Nontrivial E] {p : ℝ≥0∞} {U : Set E} (hU : U ∈ 𝓝 0) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK => hK.memLp_norm_inv_restrict h⟩
  by_contra! hp
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hp (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

/-- **Dimension-dependent local `Lᵖ` threshold for radial powers `‖x‖ ^ s`.** On a nontrivial
finite-dimensional real normed space `E` with additive Haar volume, `0 < p < ∞`, and `U ∈ 𝓝 0`,
`x ↦ ‖x‖ ^ s` lies in `MemLpLoc p U` if and only if `-(Module.finrank ℝ E : ℝ) < s * p.toReal`. -/
theorem memLpLoc_norm_rpow_iff_gt_neg_finrank [Nontrivial E] {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hptop : p ≠ ∞) {U : Set E} (hU : U ∈ 𝓝 0) {s : ℝ} :
    MemLpLoc p U (fun x : E => ‖x‖ ^ s) ↔ -(Module.finrank ℝ E : ℝ) < s * p.toReal := by
  constructor
  · intro h
    by_contra! hs
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 hU
    have hint : IntegrableOn (fun x : E => ‖‖x‖ ^ s‖ ^ p.toReal) (closedBall 0 r) volume :=
      (memLpLoc_iff.1 h _ hrU (isCompact_closedBall 0 r)).integrable_norm_rpow hp0 hptop
    have heq : (fun x : E => ‖‖x‖ ^ s‖ ^ p.toReal) = fun x => ‖x‖ ^ (s * p.toReal) := by
      funext x
      rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg x), abs_norm,
        ← Real.rpow_mul (norm_nonneg x)]
    rw [heq] at hint
    exact not_lt.2 hs
      ((integrableOn_norm_rpow_ball_iff hr).1 (hint.mono_set ball_subset_closedBall))
  · intro hs
    refine memLpLoc_iff.2 fun K _ hc => ?_
    rw [← integrable_norm_rpow_iff (measurable_norm.pow_const s).aestronglyMeasurable hp0 hptop]
    simp only [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), abs_norm,
      ← Real.rpow_mul (norm_nonneg _)]
    have hloc : LocallyIntegrable (fun x : E => ‖x‖ ^ (s * p.toReal)) volume := by
      simpa only [zero_sub, norm_neg] using
        locallyIntegrable_norm_sub_rpow (mu := (volume : Measure E)) hs (0 : E)
    exact hloc.integrableOn_isCompact hc

end FiniteDimChecks

/-- In dimension `3`, `x ↦ ‖x‖⁻¹` on `EuclideanSpace ℝ (Fin 3)` lies in `MemLpLoc p U` near the
origin if and only if `p < 3` (in particular for `p = 2`, unlike in dimension `2`). -/
theorem memLpLoc_norm_inv_euclideanSpace_fin_three_iff {p : ℝ≥0∞}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ∈ 𝓝 0) :
    MemLpLoc p U (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) ↔ p < 3 := by
  simpa [finrank_euclideanSpace_fin] using memLpLoc_norm_inv_iff_lt_finrank hU

/-- On the non-inner-product domain `ℝ × ℝ` (whose norm is `(x, y) ↦ max |x| |y|`), the `L^∞`
norm lies in `MemWkpLoc p U 1` for every `p` and every `U ⊆ ℝ × ℝ`. -/
theorem memWkpLoc_one_max_abs_prod {p : ℝ≥0∞} {U : Set (ℝ × ℝ)} :
    MemWkpLoc p U 1 (fun x : ℝ × ℝ => max |x.1| |x.2|) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  simpa only [Prod.norm_def, Real.norm_eq_abs] using
    (memWkpLoc_one_norm (E := ℝ × ℝ) (p := p) (U := U))

/-- Transporting `memWkpLoc_one_max_abs_prod` along the continuous linear equivalence
`EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ` places `x ↦ max |x 0| |x 1|` in `MemWkpLoc p U 1` on
`EuclideanSpace ℝ (Fin 2)` without recomputing weak derivatives. -/
theorem memWkpLoc_one_supNorm_euclideanSpace_fin_two {p : ℝ≥0∞}
    {U : Set (EuclideanSpace ℝ (Fin 2))} :
    MemWkpLoc p U 1 (fun x : EuclideanSpace ℝ (Fin 2) => max |x 0| |x 1|) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  exact (memWkpLoc_one_max_abs_prod (p := p) (U := Set.univ)).comp_continuousLinearEquiv e
    (mapsTo_univ _ _)

section NonSeparableCodomain

/-- Every continuous linear functional `ℓ` on the non-separable Banach space
`lp (fun _ : ℝ => ℝ) ∞` vanishes on `lp.single ∞ x 1` outside a countable set of `x : ℝ`. -/
private theorem countable_support_strongDual_lp_single
    (ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) ∞)) :
    Set.Countable {x : ℝ | ℓ (lp.single ∞ x 1) ≠ 0} := by
  have hsub : {x : ℝ | ℓ (lp.single ∞ x 1) ≠ 0} ⊆
      ⋃ n : ℕ, {x : ℝ | ((n : ℝ) + 1)⁻¹ ≤ |ℓ (lp.single ∞ x 1)|} := fun x hx => by
    obtain ⟨n, hn⟩ := exists_nat_gt |ℓ (lp.single ∞ x 1)|⁻¹
    exact mem_iUnion.2
      ⟨n, (inv_le_comm₀ (by positivity) (abs_pos.2 hx)).2 (hn.le.trans (by linarith))⟩
  refine Set.Countable.mono hsub (countable_iUnion fun n => Set.Finite.countable ?_)
  by_contra hinf
  obtain ⟨s, hs, hscard⟩ :=
    Set.Infinite.exists_subset_card_eq hinf (⌊‖ℓ‖ * ((n : ℝ) + 1)⌋₊ + 1)
  let ε : ℝ → ℝ := fun x => if 0 ≤ ℓ (lp.single ∞ x 1) then 1 else -1
  let v : lp (fun _ : ℝ => ℝ) ∞ := ∑ x ∈ s, lp.single ∞ x (ε x)
  have hv_norm : ‖v‖ ≤ 1 := by
    refine (lp.isLUB_norm v).2 ?_
    rintro _ ⟨y, rfl⟩
    simp only [v, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
    split_ifs <;> simp [ε]; split_ifs <;> norm_num
  have hsum : (s.card : ℝ) * ((n : ℝ) + 1)⁻¹ ≤ ℓ v := by
    calc (s.card : ℝ) * ((n : ℝ) + 1)⁻¹
        = ∑ _x ∈ s, ((n : ℝ) + 1)⁻¹ := by simp
      _ ≤ ∑ x ∈ s, |ℓ (lp.single ∞ x 1)| := Finset.sum_le_sum fun x hx => hs hx
      _ = ℓ v := by
          simp only [v, map_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          have hsmul : lp.single (E := fun _ : ℝ => ℝ) ∞ x (ε x) = ε x • lp.single ∞ x 1 := by
            rw [← lp.single_smul, smul_eq_mul, mul_one]
          rw [hsmul, map_smul, smul_eq_mul]
          dsimp [ε]
          split_ifs with h0
          · simp [abs_of_nonneg h0]
          · simp [abs_of_neg (not_le.1 h0)]
  have hlv : ℓ v ≤ ‖ℓ‖ :=
    (le_abs_self _).trans ((ℓ.le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg ℓ) hv_norm))
  have hcard : (s.card : ℝ) ≤ ‖ℓ‖ * ((n : ℝ) + 1) := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc (s.card : ℝ) = (s.card : ℝ) * ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) := by
          rw [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      _ ≤ ‖ℓ‖ * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (hsum.trans hlv) hpos.le
  exact absurd (Nat.le_floor hcard) (by omega)

/-- **Scalar weak Sobolev regularity without Bochner measurability.** For the non-separable Banach
codomain `lp (fun _ : ℝ => ℝ) ∞`, composing `x ↦ lp.single ∞ x 1` with *every* continuous linear
functional `ℓ` produces an almost-everywhere zero function, hence a member of `MemWkpLoc p U k` for
every `p`, `U`, and `k`. -/
theorem memWkpLoc_strongDual_comp_lp_single (p : ℝ≥0∞) (U : Set ℝ) (k : ℕ)
    (ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) ∞)) :
    MemWkpLoc p U k (fun x : ℝ => ℓ (lp.single ∞ x 1)) := by
  have hae : (0 : ℝ → ℝ) =ᵐ[volume.restrict U] fun x : ℝ => ℓ (lp.single ∞ x 1) :=
    ae_restrict_of_ae <| ae_iff.2 <|
      measure_mono_null (t := {x : ℝ | ℓ (lp.single ∞ x 1) ≠ 0}) (fun x hx h0 => hx h0.symm) <|
        (countable_support_strongDual_lp_single ℓ).measure_zero volume
  exact memWkpLoc_zero_fun.congr_ae hae

/-- **Failure of `MemLpLoc` for a scalarly smooth map into a non-separable Banach space.** On any
subset `U ⊆ ℝ` with nonempty interior, `x ↦ lp.single ∞ x 1` does not belong to `MemLpLoc p U` for
*any* exponent `0 ≤ p ≤ ∞`: strong measurability on a compact interval inside `U` would force an
uncountable `1`-separated set in `lp (fun _ : ℝ => ℝ) ∞` to be separable. -/
theorem not_memLpLoc_lp_single {p : ℝ≥0∞} {U : Set ℝ} (hU : (interior U).Nonempty) :
    ¬ MemLpLoc p U (fun x : ℝ => lp.single (E := fun _ : ℝ => ℝ) ∞ x 1) := by
  intro hf
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  have hKsub : Icc x₀ (x₀ + r / 2) ⊆ U := fun x hx => interior_subset <| hrU <| by
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hx.1)]
    linarith [hx.2]
  set f : ℝ → lp (fun _ : ℝ => ℝ) ∞ := fun x => lp.single ∞ x 1
  have hsm : AEStronglyMeasurable f (volume.restrict (Icc x₀ (x₀ + r / 2))) :=
    (memLpLoc_iff.1 hf _ hKsub isCompact_Icc).aestronglyMeasurable
  let g := hsm.mk f
  let S : Set ℝ := {x ∈ Icc x₀ (x₀ + r / 2) | f x = g x}
  have hcompl : volume (Icc x₀ (x₀ + r / 2) \ S) = 0 := by
    have hae := (ae_restrict_iff' measurableSet_Icc).1 hsm.ae_eq_mk
    exact measure_mono_null (fun x hx => fun h => hx.2 ⟨hx.1, h hx.1⟩) (ae_iff.1 hae)
  obtain ⟨D, hDc, hD⟩ := (hsm.stronglyMeasurable_mk.isSeparable_range.mono
    (show f '' S ⊆ range g by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx.2.symm⟩))
  have hdist : ∀ x y : ℝ, x ≠ y → 1 ≤ dist (f x) (f y) := fun x y hxy => by
    rw [dist_eq_norm]
    have hx1 : ‖(f x - f y) x‖ = 1 := by simp [f, Pi.single_eq_of_ne hxy]
    exact hx1 ▸ (lp.isLUB_norm (f x - f y)).1 ⟨x, rfl⟩
  have hSc : S.Countable := by
    have hnear : ∀ x : S, ∃ d : D, dist (f x.1) d.1 < 1 / 2 := fun x => by
      obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hD ⟨x.1, x.2, rfl⟩) (1 / 2) one_half_pos
      exact ⟨⟨d, hdD⟩, hd⟩
    choose d hd using hnear
    have hinj : Function.Injective d := fun x y hxy => Subtype.ext <| by
      by_contra hne
      have h1 := hdist x.1 y.1 hne
      have hdy : dist (d x).1 (f y.1) < 1 / 2 := by rw [hxy, dist_comm]; exact hd y
      linarith [dist_triangle (f x.1) (d x).1 (f y.1), hd x]
    have : Countable D := hDc.to_subtype
    have : Countable S := hinj.countable
    exact Set.to_countable S
  have hvol0 : volume (Icc x₀ (x₀ + r / 2)) = 0 :=
    measure_mono_null
      (fun x hx => by by_cases hxS : x ∈ S <;> [exact Or.inl hxS; exact Or.inr ⟨hx, hxS⟩])
      (measure_union_null (hSc.measure_zero volume) hcompl)
  rw [Real.volume_Icc, add_sub_cancel_left] at hvol0
  exact (ENNReal.ofReal_pos.2 (half_pos hr)).ne' hvol0

end NonSeparableCodomain

end SharpnessAndChecks

end TauCeti
