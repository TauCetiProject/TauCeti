/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.W1p.BoundedContinuous
import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The `L∞` boundary trace on a bounded Lipschitz domain

`W1p.frontierTraceTop` sends a `W^{1,∞}` class to the boundary values of its Lipschitz
representative, as an `L∞` class for normalized Euclidean Hausdorff measure on the frontier.
The trace is characterized by agreement with every continuous representative on the closure.
Its norm is at most the essential supremum of the value on the domain, and it agrees with
all finite-exponent traces after lowering the Sobolev exponent.

The closure-defined `W^{1,∞}_0` lies in the trace kernel. No converse is asserted: even on
an interval, zero endpoint values do not imply approximation in the full `W^{1,∞}` norm.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §4.7.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §§5.4–5.5.
-/

public section

noncomputable section

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti.W1p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

private def frontierExtensionL
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    W1p volume Ω ∞ →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) ∞ :=
  (exists_extensionL_of_isLipschitzDomainWith (p := ∞) hΩ hb).choose

private theorem restrictL_frontierExtensionL
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    restrictL le_top (frontierExtensionL hΩ hb u) = u := by
  simpa only [frontierExtensionL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using
    congrArg (fun T ↦ T u)
      (exists_extensionL_of_isLipschitzDomainWith (p := ∞) hΩ hb).choose_spec

private def frontierRepresentativeL
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    W1p volume Ω ∞ →L[ℝ] (WithLp 2 (ℝ × E) →ᵇ ℝ) :=
  boundedContinuousRepresentativeL.comp (frontierExtensionL hΩ hb)

private theorem value_ae_eq_frontierRepresentativeL
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] frontierRepresentativeL hΩ hb u := by
  have hval := value_restrictL_ae (le_top : Ω ≤ ⊤) (frontierExtensionL hΩ hb u)
  rw [restrictL_frontierExtensionL] at hval
  rw [frontierRepresentativeL, ContinuousLinearMap.comp_apply]
  exact hval.trans
    ((value_ae_eq_boundedContinuousRepresentativeL (frontierExtensionL hΩ hb u)).filter_mono
      (ae_mono Measure.restrict_le_self))

/-- The boundary trace of a `W^{1,∞}` class on a bounded Lipschitz domain, with values in
`L∞` for normalized Euclidean Hausdorff measure on the frontier. -/
def frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    W1p volume Ω ∞ →L[ℝ]
      Lp ℝ ∞ ((μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))) :=
  (BoundedContinuousFunction.toLpTop _ ℝ).comp (frontierRepresentativeL hΩ hb)

/-- The `L∞` trace agrees with the boundary restriction of any continuous representative
on the closure, independently of the extension used to construct the trace. -/
theorem frontierTraceTop_ae_eq_of_continuousOn
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω ∞}
    {f : WithLp 2 (ℝ × E) → ℝ}
    (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
    (hu : value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) :
    frontierTraceTop hΩ hb u =ᵐ[
      (μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f := by
  have heq := Ω.isOpen.ext_closure_of_ae_eq
    ((frontierRepresentativeL hΩ hb u).continuous.comp continuous_subtype_val)
    hf.domRestrict
    ((ae_restrict_iff' Ω.isOpen.measurableSet).1
      ((value_ae_eq_frontierRepresentativeL hΩ hb u).symm.trans hu))
  filter_upwards [BoundedContinuousFunction.coeFn_toLpTop
      ((μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))) (𝕜 := ℝ) (frontierRepresentativeL hΩ hb u),
    ae_restrict_mem isClosed_frontier.measurableSet] with x hx hxF
  exact hx.trans (congrFun heq ⟨x, frontier_subset_closure hxF⟩)

/-- Every `W^{1,∞}` class has a globally Lipschitz extension whose boundary values give
its `L∞` trace. -/
theorem exists_lipschitzWith_ae_eq_frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    ∃ (f : WithLp 2 (ℝ × E) →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f ∧
      (value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) ∧
      (frontierTraceTop hΩ hb u =ᵐ[
        (μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
          (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f) := by
  refine ⟨frontierRepresentativeL hΩ hb u, ‖gradient (frontierExtensionL hΩ hb u)‖₊, ?_,
    value_ae_eq_frontierRepresentativeL hΩ hb u,
    frontierTraceTop_ae_eq_of_continuousOn hΩ hb
      (frontierRepresentativeL hΩ hb u).continuous.continuousOn
      (value_ae_eq_frontierRepresentativeL hΩ hb u)⟩
  simpa only [frontierRepresentativeL, ContinuousLinearMap.comp_apply] using
    lipschitzWith_boundedContinuousRepresentativeL (frontierExtensionL hΩ hb u)

/-- Taking the boundary trace does not increase the essential supremum of the value. -/
theorem norm_frontierTraceTop_le
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    ‖frontierTraceTop hΩ hb u‖ ≤ ‖value u‖ := by
  let f := frontierRepresentativeL hΩ hb u
  have hc : IsClosed {x | ‖f x‖ ≤ ‖value u‖} :=
    isClosed_le f.continuous.norm continuous_const
  have hbound : ∀ᵐ x ∂volume, x ∈ Ω → ‖f x‖ ≤ ‖value u‖ := by
    apply (ae_restrict_iff' Ω.isOpen.measurableSet).1
    filter_upwards [value_ae_eq_frontierRepresentativeL hΩ hb u,
      Lp.ae_norm_le_norm_top (value u)] with x hx hnorm
    exact hx ▸ hnorm
  have hclosure : closure (Ω : Set (WithLp 2 (ℝ × E))) ⊆ {x | ‖f x‖ ≤ ‖value u‖} :=
    closure_minimal ((Ω.isOpen.subset_closure_of_ae_le
      (t := {x | ‖f x‖ ≤ ‖value u‖}) hbound).trans hc.closure_subset) hc
  apply Lp.norm_top_le_of_ae_bound (norm_nonneg _)
  filter_upwards [frontierTraceTop_ae_eq_of_continuousOn hΩ hb f.continuous.continuousOn
      (value_ae_eq_frontierRepresentativeL hΩ hb u),
    ae_restrict_mem isClosed_frontier.measurableSet] with x hx hxF
  rw [hx]
  exact hclosure (frontier_subset_closure hxF)

/-- The `L∞` trace has operator norm at most one in the Sobolev norm. -/
theorem opNorm_frontierTraceTop_le
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ‖frontierTraceTop hΩ hb‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa only [one_mul] using (norm_frontierTraceTop_le hΩ hb u).trans (norm_value_le u)

/-- The boundary-value characterization uniquely determines the `L∞` trace. Unlike finite
exponents, it is not enough to test agreement only on smooth functions. -/
theorem eq_frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (T : W1p volume Ω ∞ →L[ℝ]
      Lp ℝ ∞ ((μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))))
    (hT : ∀ (u : W1p volume Ω ∞) (f : WithLp 2 (ℝ × E) → ℝ),
      ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))) →
      value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f →
      T u =ᵐ[(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f) :
    T = frontierTraceTop hΩ hb := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨f, _, _, hu, hf⟩ := exists_lipschitzWith_ae_eq_frontierTraceTop hΩ hb u
  exact Lp.ext ((hT u f f.continuous.continuousOn hu).trans hf.symm)

/-- The `L∞` trace agrees almost everywhere with every finite-exponent trace of the same
Sobolev class. -/
theorem frontierTrace_ofExponentLE_ae_eq_frontierTraceTop {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    letI : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
      isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
    frontierTrace hp hΩ hb (ofExponentLE le_top u) =ᵐ[
      (μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] frontierTraceTop hΩ hb u := by
  let : IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  obtain ⟨f, _, _, hu, hf⟩ := exists_lipschitzWith_ae_eq_frontierTraceTop hΩ hb u
  exact (frontierTrace_ae_eq_of_continuousOn hp hΩ hb f.continuous.continuousOn
    ((value_ofExponentLE_ae le_top u).trans hu)).trans hf.symm

/-- The full-norm closure of test functions has zero `L∞` trace. The converse is false. -/
theorem w1p0Submodule_le_ker_frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    (w1p0Submodule volume Ω ∞ : Submodule ℝ (W1p volume Ω ∞)) ≤
      (frontierTraceTop hΩ hb).ker := by
  intro u hu
  refine w1p0Submodule_subset_of_isClosed (frontierTraceTop hΩ hb).isClosed_ker
    (fun φ ↦ ?_) hu
  rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  apply Lp.ext
  filter_upwards [frontierTraceTop_ae_eq_of_continuousOn hΩ hb φ.continuous.continuousOn
      (value_ofTestFunctionₗ_ae φ),
    ae_restrict_mem isClosed_frontier.measurableSet,
    Lp.coeFn_zero ℝ ∞ ((μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E)))))] with x hx hxF hx0
  rw [hx, hx0]
  exact image_eq_zero_of_notMem_tsupport fun hxφ ↦
    (Ω.isOpen.frontier_eq ▸ hxF).2 (φ.tsupport_subset hxφ)

end TauCeti.W1p
