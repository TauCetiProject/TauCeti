/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
import TauCeti.Analysis.Sobolev.W1p.BoundedContinuous
import TauCeti.Analysis.Sobolev.W1p.Infinity
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The trace of `W^{1,∞}` on a bounded Lipschitz domain

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain and let `σ` be normalized `dim E`-dimensional
Euclidean Hausdorff measure restricted to `frontier Ω`. For `1 ≤ p < ∞` the trace operator
`TauCeti.W1p.frontierTrace : W^{1,p}(Ω) → Lᵖ(frontier Ω, σ)` is determined by its values on
functions smooth up to the boundary, which are dense in `W^{1,p}(Ω)`. At `p = ∞` they are not
dense, and this file constructs the trace from the Lipschitz representative instead.

Every `u ∈ W^{1,∞}(Ω)` agrees almost everywhere on `Ω` with a Lipschitz function on `ℝ × E` whose
Lipschitz constant and supremum are at most `C ‖u‖`, with `C` depending only on `Ω`
(`TauCeti.W1p.exists_lipschitzWith_ae_eq_of_isLipschitzDomainWith`). Restricting it to the
frontier gives the bounded **trace operator at the infinite exponent**

`TauCeti.W1p.frontierTraceTop : W^{1,∞}(Ω) →L[ℝ] L^∞(frontier Ω, σ)`,

the unique map sending each `u` with a representative `f` continuous on `closure Ω` to the
restriction of `f` to the frontier (`TauCeti.W1p.frontierTraceTop_ae_eq_of_continuousOn`,
`TauCeti.W1p.eq_frontierTraceTop`). It agrees with the traces at the finite exponents: on the
bounded set `Ω`, `W^{1,∞}(Ω) ⊆ W^{1,p}(Ω)`, and the `W^{1,p}` trace of `u` is its `W^{1,∞}` trace
(`TauCeti.W1p.frontierTrace_ae_eq_frontierTraceTop`). The trace does not increase the essential
supremum of the value (`TauCeti.W1p.norm_frontierTraceTop_le`) and commutes with multiplication
by a smooth cutoff (`TauCeti.W1p.frontierTraceTop_contDiffSMul_ae`).

The closure `W^{1,∞}_0(Ω)` of the test functions lies in the kernel of the trace
(`TauCeti.W1p.w1p0Submodule_le_ker_frontierTraceTop`). Unlike for `p < ∞`, where the kernel is
exactly `W^{1,p}_0(Ω)` (`TauCeti.W1p.ker_frontierTrace`), the inclusion is strict for every
nonempty `Ω` (`TauCeti.W1p.w1p0Submodule_lt_ker_frontierTraceTop`): the distance to the complement
of `Ω` has zero trace but stays at distance at least `1` from `W^{1,∞}_0(Ω)`
(`TauCeti.W1p.one_le_dist_of_value_ae_eq_infDist_compl`).

The Lipschitz representative is built by extension: the extension operator
`TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith` is bounded on `W^{1,∞}`, and on the whole
space the bounded continuous representative of a `W^{1,∞}` function has Lipschitz constant at
most the essential supremum of its gradient
(`TauCeti.W1p.lipschitzWith_boundedContinuousRepresentativeL`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5 (traces) and §5.8.2, Theorems 4
  and 5 (`W^{1,∞}` functions are Lipschitz).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3, for the distinction between
  zero trace and approximation by test functions at the infinite exponent.
-/

public section

noncomputable section

open Bornology MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- **Lipschitz representatives on a bounded Lipschitz domain.** There is a constant `C` such that
every `u ∈ W^{1,∞}(Ω)` agrees almost everywhere on `Ω` with a function on `ℝ × E` which is
Lipschitz with constant `C ‖u‖` and bounded by `C ‖u‖`. -/
theorem W1p.exists_lipschitzWith_ae_eq_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ C : ℝ≥0, ∀ u : W1p volume Ω ∞, ∃ f : WithLp 2 (ℝ × E) → ℝ,
      LipschitzWith (C * ‖u‖₊) f ∧ (∀ x, ‖f x‖ ≤ C * ‖u‖) ∧
        W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f := by
  obtain ⟨X, hX, -⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := ∞) hΩ hb
  refine ⟨‖X‖₊, fun u ↦ ⟨W1p.boundedContinuousRepresentativeL (X u), ?_, fun x ↦ ?_, ?_⟩⟩
  · refine (W1p.lipschitzWith_boundedContinuousRepresentativeL (X u)).weaken ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    exact (W1p.norm_gradient_le (X u)).trans (X.le_opNorm u)
  · calc
      ‖W1p.boundedContinuousRepresentativeL (X u) x‖ ≤
          ‖W1p.boundedContinuousRepresentativeL (X u)‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ x
      _ = ‖W1p.value (X u)‖ := W1p.norm_boundedContinuousRepresentativeL _
      _ ≤ ‖X u‖ := W1p.norm_value_le _
      _ ≤ ‖X‖₊ * ‖u‖ := X.le_opNorm u
  · exact (W1p.value_ae_eq_of_restrictL_comp_eq_id (le_top : Ω ≤ ⊤) hX u).symm.trans
      (ae_restrict_of_ae (W1p.value_ae_eq_boundedContinuousRepresentativeL (X u)))

/-- **Existence of the trace at the infinite exponent.** On a bounded Lipschitz domain there is a
bounded linear operator `W^{1,∞}(Ω) → L^∞(frontier Ω)`, for normalized Euclidean Hausdorff measure
on the frontier, sending every function continuous up to the boundary to its restriction to the
frontier. -/
theorem W1p.exists_frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : W1p volume Ω ∞ →L[ℝ] Lp ℝ ∞ ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))),
      ∀ (u : W1p volume Ω ∞) (f : WithLp 2 (ℝ × E) → ℝ),
        ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))) →
        W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f →
        T u =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
          (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f := by
  set σ := (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
    (frontier (Ω : Set (WithLp 2 (ℝ × E))))
  obtain ⟨C, hC⟩ := W1p.exists_lipschitzWith_ae_eq_of_isLipschitzDomainWith hΩ hb
  choose F hFlip hFbd hFae using hC
  have hmem (u : W1p volume Ω ∞) : MemLp (F u) ∞ σ :=
    memLp_top_of_bound (hFlip u).continuous.aestronglyMeasurable _ (ae_of_all _ (hFbd u))
  -- Two functions continuous on `closure Ω` and almost everywhere equal on `Ω` agree on the
  -- closure, hence on the frontier.
  have hF (u : W1p volume Ω ∞) (f : WithLp 2 (ℝ × E) → ℝ)
      (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
      (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) :
      (hmem u).toLp (F u) =ᵐ[σ] f := by
    have heq : EqOn (F u) f (closure (Ω : Set (WithLp 2 (ℝ × E)))) :=
      (Measure.eqOn_open_of_ae_eq ((hFae u).symm.trans hu) Ω.isOpen
        (hFlip u).continuous.continuousOn (hf.mono subset_closure)).of_subset_closure
          (hFlip u).continuous.continuousOn hf subset_closure subset_rfl
    filter_upwards [(hmem u).coeFn_toLp, ae_restrict_mem isClosed_frontier.measurableSet]
      with x hx hxF
    rw [hx]
    exact heq (frontier_subset_closure hxF)
  let T : W1p volume Ω ∞ →ₗ[ℝ] Lp ℝ ∞ σ :=
    { toFun := fun u ↦ (hmem u).toLp (F u)
      map_add' := fun u v ↦ by
        refine Lp.ext ((hF _ _ ((hFlip u).continuous.add (hFlip v).continuous).continuousOn
          ((W1p.value_add_ae u v).trans ((hFae u).add (hFae v)))).trans ?_)
        filter_upwards [Lp.coeFn_add ((hmem u).toLp (F u)) ((hmem v).toLp (F v)),
          (hmem u).coeFn_toLp, (hmem v).coeFn_toLp] with x hx hu hv
        simp only [hx, Pi.add_apply, hu, hv]
      map_smul' := fun c u ↦ by
        refine Lp.ext ((hF _ _ ((hFlip u).continuous.const_smul c).continuousOn
          ((W1p.value_smul_ae c u).trans ((hFae u).const_smul c))).trans ?_)
        filter_upwards [Lp.coeFn_smul c ((hmem u).toLp (F u)), (hmem u).coeFn_toLp]
          with x hx hu
        simp only [RingHom.id_apply, hx, Pi.smul_apply, hu] }
  refine ⟨T.mkContinuous C fun u ↦ Lp.norm_le_of_ae_bound_top (by positivity) ?_, hF⟩
  filter_upwards [(hmem u).coeFn_toLp] with x hx
  simpa [T, hx] using hFbd u x

/-- **The trace operator at the infinite exponent** of a bounded Lipschitz domain,
`W^{1,∞}(Ω) → L^∞(frontier Ω)` for normalized `dim E`-dimensional Euclidean Hausdorff measure on
the frontier. It is characterized by `TauCeti.W1p.frontierTraceTop_ae_eq_of_continuousOn` and
`TauCeti.W1p.eq_frontierTraceTop`: it sends every `u` with a representative continuous on
`closure Ω` to the restriction of that representative to the frontier. -/
def W1p.frontierTraceTop (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    W1p volume Ω ∞ →L[ℝ] Lp ℝ ∞ ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))) :=
  (W1p.exists_frontierTraceTop hΩ hb).choose

/-- **The trace of a function continuous up to the boundary is its boundary restriction.** If
`u ∈ W^{1,∞}(Ω)` agrees almost everywhere on `Ω` with a function `f` continuous on `closure Ω`,
then the trace of `u` is `f` almost everywhere on the frontier for surface measure. -/
theorem W1p.frontierTraceTop_ae_eq_of_continuousOn
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω ∞}
    {f : WithLp 2 (ℝ × E) → ℝ} (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) :
    W1p.frontierTraceTop hΩ hb u =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f :=
  (W1p.exists_frontierTraceTop hΩ hb).choose_spec u f hf hu

/-- Every `W^{1,∞}` class has a globally Lipschitz, bounded continuous representative whose
boundary values give its `L∞` trace. -/
theorem W1p.exists_lipschitzWith_ae_eq_frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    ∃ (f : WithLp 2 (ℝ × E) →ᵇ ℝ) (K : ℝ≥0), LipschitzWith K f ∧
      (W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f) ∧
      (W1p.frontierTraceTop hΩ hb u =ᵐ[
        (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
          (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f) := by
  obtain ⟨C, hC⟩ := W1p.exists_lipschitzWith_ae_eq_of_isLipschitzDomainWith hΩ hb
  obtain ⟨f, hf, hbound, hu⟩ := hC u
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous _ hbound,
    C * ‖u‖₊, ?_⟩
  simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  exact ⟨hf, hu, W1p.frontierTraceTop_ae_eq_of_continuousOn hΩ hb hf.continuous.continuousOn hu⟩

open scoped ContDiff Gradient in
/-- The `L∞` trace commutes with multiplication by a smooth function bounded together
with its gradient on the domain. -/
theorem W1p.frontierTraceTop_contDiffSMul_ae
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ} (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (u : W1p volume Ω ∞) :
    W1p.frontierTraceTop hΩ hb (W1p.contDiffSMul ψ hψ hM hψM hgM u) =ᵐ[
      (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))]
      fun x ↦ ψ x * W1p.frontierTraceTop hΩ hb u x := by
  obtain ⟨f, _, _, hu, hf⟩ := W1p.exists_lipschitzWith_ae_eq_frontierTraceTop hΩ hb u
  have hprod := Filter.EventuallyEq.trans (W1p.value_contDiffSMul_ae hψ hM hψM hgM u)
    (Filter.EventuallyEq.rfl.smul hu)
  exact (W1p.frontierTraceTop_ae_eq_of_continuousOn hΩ hb
    (hψ.continuous.mul f.continuous).continuousOn hprod).trans
      (Filter.EventuallyEq.rfl.mul hf.symm)

/-- Taking the boundary trace does not increase the essential supremum of the value. -/
theorem W1p.norm_frontierTraceTop_le
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    ‖W1p.frontierTraceTop hΩ hb u‖ ≤ ‖W1p.value u‖ := by
  obtain ⟨f, _, _, hu, hf⟩ := W1p.exists_lipschitzWith_ae_eq_frontierTraceTop hΩ hb u
  have hc : IsClosed {x | ‖f x‖ ≤ ‖W1p.value u‖} :=
    isClosed_le f.continuous.norm continuous_const
  have hbound : ∀ᵐ x ∂volume, x ∈ Ω → ‖f x‖ ≤ ‖W1p.value u‖ := by
    apply (ae_restrict_iff' Ω.isOpen.measurableSet).1
    filter_upwards [hu, Lp.ae_norm_le_norm_top (W1p.value u)] with x hx hnorm
    exact hx ▸ hnorm
  have hclosure : closure (Ω : Set (WithLp 2 (ℝ × E))) ⊆ {x | ‖f x‖ ≤ ‖W1p.value u‖} :=
    closure_minimal ((Ω.isOpen.subset_closure_of_ae_le
      (t := {x | ‖f x‖ ≤ ‖W1p.value u‖}) hbound).trans hc.closure_subset) hc
  apply Lp.norm_le_of_ae_bound_top (norm_nonneg _)
  filter_upwards [hf, ae_restrict_mem isClosed_frontier.measurableSet] with x hx hxF
  rw [hx]
  exact hclosure (frontier_subset_closure hxF)

/-- The `L∞` trace has operator norm at most one in the Sobolev norm. -/
theorem W1p.opNorm_frontierTraceTop_le
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ‖W1p.frontierTraceTop hΩ hb‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa only [one_mul] using (W1p.norm_frontierTraceTop_le hΩ hb u).trans (W1p.norm_value_le u)

/-- **Uniqueness of the trace at the infinite exponent.** A bounded linear operator
`W^{1,∞}(Ω) → L^∞(frontier Ω)` sending every function continuous up to the boundary to its
restriction to the frontier is the trace operator. -/
theorem W1p.eq_frontierTraceTop (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (T : W1p volume Ω ∞ →L[ℝ] Lp ℝ ∞ ((μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))))
    (hT : ∀ (u : W1p volume Ω ∞) (f : WithLp 2 (ℝ × E) → ℝ),
      ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))) →
      W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f →
      T u =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] f) :
    T = W1p.frontierTraceTop hΩ hb := by
  ext1 u
  obtain ⟨C, hC⟩ := W1p.exists_lipschitzWith_ae_eq_of_isLipschitzDomainWith hΩ hb
  obtain ⟨f, hf, -, hu⟩ := hC u
  exact Lp.ext ((hT u f hf.continuous.continuousOn hu).trans
    (W1p.frontierTraceTop_ae_eq_of_continuousOn hΩ hb hf.continuous.continuousOn hu).symm)

/-- **The trace does not depend on the Lipschitz constant** used to construct it: the trace
operators at the infinite exponent built from two Lipschitz bounds of the same bounded domain
agree. -/
theorem W1p.frontierTraceTop_eq_of_isLipschitzDomainWith {L' : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hΩ' : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L')
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    W1p.frontierTraceTop hΩ hb = W1p.frontierTraceTop hΩ' hb :=
  W1p.eq_frontierTraceTop hΩ' hb _ fun _ _ hf hu ↦
    W1p.frontierTraceTop_ae_eq_of_continuousOn hΩ hb hf hu

/-- **Agreement with the traces at finite exponents.** If `v ∈ W^{1,p}(Ω)`, `p < ∞`, and
`u ∈ W^{1,∞}(Ω)` have the same value almost everywhere on `Ω`, then the `W^{1,p}` trace of `v` is
the `W^{1,∞}` trace of `u`. -/
theorem W1p.frontierTrace_ae_eq_frontierTraceTop {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω ∞} {v : W1p volume Ω p}
    (huv : W1p.value v =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u) :
    W1p.frontierTrace hp hΩ hb v =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
      (frontier (Ω : Set (WithLp 2 (ℝ × E))))] W1p.frontierTraceTop hΩ hb u := by
  obtain ⟨C, hC⟩ := W1p.exists_lipschitzWith_ae_eq_of_isLipschitzDomainWith hΩ hb
  obtain ⟨f, hf, -, hu⟩ := hC u
  exact (W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb hf.continuous.continuousOn
    (huv.trans hu)).trans
      (W1p.frontierTraceTop_ae_eq_of_continuousOn hΩ hb hf.continuous.continuousOn hu).symm

/-- The `W^{1,p}` trace of `u ∈ W^{1,∞}(Ω)`, viewed in `W^{1,p}(Ω)` for `p < ∞` through the
inclusion `TauCeti.W1p.ofExponentLE`, is its `W^{1,∞}` trace. -/
theorem W1p.frontierTrace_ofExponentLE_ae_eq_frontierTraceTop {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [IsFiniteMeasure (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))] (hp : p ≠ ∞)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (u : W1p volume Ω ∞) :
    W1p.frontierTrace hp hΩ hb (W1p.ofExponentLE le_top u) =ᵐ[
      (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))] W1p.frontierTraceTop hΩ hb u :=
  W1p.frontierTrace_ae_eq_frontierTraceTop hp hΩ hb
    (W1p.coeFn_value_ofExponentLE le_top u).eventuallyEq

/-- **A function continuous up to the boundary and vanishing on it has zero trace.** If
`u ∈ W^{1,∞}(Ω)` agrees almost everywhere on `Ω` with a function `f` continuous on `closure Ω`
that vanishes on `frontier Ω`, then the trace of `u` is zero. -/
theorem W1p.frontierTraceTop_eq_zero_of_continuousOn
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {u : W1p volume Ω ∞}
    {f : WithLp 2 (ℝ × E) → ℝ} (hf : ContinuousOn f (closure (Ω : Set (WithLp 2 (ℝ × E)))))
    (hu : W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] f)
    (hf0 : ∀ x ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))), f x = 0) :
    W1p.frontierTraceTop hΩ hb u = 0 := by
  refine Lp.ext ((W1p.frontierTraceTop_ae_eq_of_continuousOn hΩ hb hf hu).trans ?_)
  filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet,
    (Lp.coeFn_zero ℝ ∞ _).symm] with x hxF hx0
  rw [← hx0]
  exact hf0 x hxF

/-- **Functions in `W^{1,∞}_0(Ω)` have zero trace.** -/
theorem W1p.w1p0Submodule_le_ker_frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    (w1p0Submodule volume Ω ∞ : Submodule ℝ (W1p volume Ω ∞)) ≤
      LinearMap.ker (W1p.frontierTraceTop hΩ hb).toLinearMap := by
  -- The kernel is closed, so it suffices to treat test functions supported in `Ω`.
  intro u hu
  refine w1p0Submodule_subset_of_isClosed (W1p.frontierTraceTop hΩ hb).isClosed_ker
    (fun φ ↦ ?_) hu
  rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  -- A test function supported in the open set `Ω` vanishes on its frontier.
  exact W1p.frontierTraceTop_eq_zero_of_continuousOn hΩ hb φ.continuous.continuousOn
    (W1p.value_ofTestFunctionₗ_ae φ) fun x hxF ↦ image_eq_zero_of_notMem_tsupport fun hxs ↦
      (Ω.isOpen.frontier_eq ▸ hxF).2 (φ.tsupport_subset hxs)

/-- **The kernel of the trace is larger than `W^{1,∞}_0(Ω)`.** On a nonempty bounded Lipschitz
domain, the closure `W^{1,∞}_0(Ω)` of the test functions is a proper subspace of the kernel of the
trace at the infinite exponent: the distance to the complement of `Ω` has zero trace but does not
lie in `W^{1,∞}_0(Ω)`. -/
theorem W1p.w1p0Submodule_lt_ker_frontierTraceTop
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hne : (Ω : Set (WithLp 2 (ℝ × E))).Nonempty) :
    (w1p0Submodule volume Ω ∞ : Submodule ℝ (W1p volume Ω ∞)) <
      LinearMap.ker (W1p.frontierTraceTop hΩ hb).toLinearMap := by
  refine lt_of_le_of_ne (W1p.w1p0Submodule_le_ker_frontierTraceTop hΩ hb) fun heq ↦ ?_
  obtain ⟨u, hu⟩ := W1p.exists_value_ae_eq_infDist_compl (mu := volume) hb
  have hker : u ∈ LinearMap.ker (W1p.frontierTraceTop hΩ hb).toLinearMap := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    -- The distance to the complement vanishes on the frontier, which lies outside `Ω`.
    exact W1p.frontierTraceTop_eq_zero_of_continuousOn hΩ hb
      (lipschitz_infDist_pt _).continuous.continuousOn hu fun x hxF ↦
        infDist_zero_of_mem (Ω.isOpen.frontier_eq ▸ hxF).2
  refine W1p.notMem_w1p0Submodule_of_value_ae_eq_infDist_compl hne
    (fun h ↦ NormedSpace.unbounded_univ ℝ (WithLp 2 (ℝ × E)) (h ▸ hb)) hu ?_
  rw [← heq] at hker
  exact hker

end TauCeti
