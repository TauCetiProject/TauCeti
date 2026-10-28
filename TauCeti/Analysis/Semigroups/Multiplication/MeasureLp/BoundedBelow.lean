/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Multiplication.MeasureLp.Generator
import TauCeti.Analysis.Semigroups.Generator.ExponentialShift
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Shift
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Measure-space Lᵖ multiplication semigroups with multipliers bounded below

For an almost everywhere measurable real multiplier `m` with almost everywhere lower bound `b`,
`S(t)f = exp (-t * m) • f` defines a C₀-semigroup on `Lᵖ(μ; E)`, `1 ≤ p < ∞`.
Its growth exponent is `-b`, its generator acts as multiplication by `-m`, and its generator
domain is exactly the vectors for which `m • f` belongs to Lᵖ. For `λ > -b`, the resolvent
is multiplication by `(λ + m)⁻¹`. The measure is arbitrary and the multiplier may be unbounded
above or negative on a set of positive measure.

The construction exponentially shifts the nonnegative multiplication semigroup for `(m - b)⁺`.
All action formulas hold almost everywhere; changing the multiplier on a null set or choosing
a different lower bound does not change the semigroup. The argument uses the same exponential
shift as the discrete ℓᵖ construction in
`TauCeti.Analysis.Semigroups.Multiplication.Lp.BoundedBelow`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section I.4.c (multiplication semigroups).
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] {m : α → ℝ}

/-- Multiplication by `exp (-t * m)` on measure-space Lᵖ for a real multiplier with an
almost everywhere lower bound. No upper bound or finiteness of the measure is required. -/
def ofMeasureLpMultiplication (hm : AEMeasurable m μ) (hp : p ≠ ∞) (b : ℝ)
    (_hb : ∀ᵐ a ∂μ, b ≤ m a) : StronglyContinuousSemigroup (Lp E p μ) :=
  (ContractionSemigroup.ofMeasureLpMultiplication
    (m := fun a => (m a - b).toNNReal) (by fun_prop) hp).toStronglyContinuousSemigroup.expShift b

/-- The real multiplication semigroup acts by `exp (-t * m)` almost everywhere. -/
@[simp]
theorem ofMeasureLpMultiplication_apply_apply_ae (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (b : ℝ) (hb : ∀ᵐ a ∂μ, b ≤ m a) (t : ℝ≥0) (f : Lp E p μ) :
    ofMeasureLpMultiplication hm hp b hb t f =ᵐ[μ]
      fun a => Real.exp (-((t : ℝ) * m a)) • f a := by
  rw [ofMeasureLpMultiplication, expShift_apply_apply,
    ContractionSemigroup.toStronglyContinuousSemigroup_apply]
  filter_upwards [Lp.coeFn_smul (Real.exp (-(b * t)))
      (ContractionSemigroup.ofMeasureLpMultiplication
        (m := fun a => (m a - b).toNNReal) (by fun_prop) hp t f),
    ContractionSemigroup.ofMeasureLpMultiplication_apply_apply_ae
      (m := fun a => (m a - b).toNNReal) (by fun_prop) hp t f, hb] with a hs hS ha
  simp only [hs, Pi.smul_apply, hS, Real.coe_toNNReal _ (sub_nonneg.mpr ha),
    smul_smul, ← Real.exp_add]
  congr 2
  ring

/-- Almost everywhere equal multipliers and any choices of their lower bounds give the same
semigroup. In particular, the semigroup is independent of the lower bound used to construct it. -/
theorem ofMeasureLpMultiplication_congr_ae {n : α → ℝ}
    (hm : AEMeasurable m μ) (hn : AEMeasurable n μ) (hp : p ≠ ∞) (b c : ℝ)
    (hb : ∀ᵐ a ∂μ, b ≤ m a) (hc : ∀ᵐ a ∂μ, c ≤ n a) (hmn : m =ᵐ[μ] n) :
    ofMeasureLpMultiplication (E := E) hm hp b hb = ofMeasureLpMultiplication hn hp c hc := by
  apply StronglyContinuousSemigroup.ext
  intro t
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [ofMeasureLpMultiplication_apply_apply_ae hm hp b hb t f,
    ofMeasureLpMultiplication_apply_apply_ae hn hp c hc t f, hmn] with a hS hT ha
  rw [hS, hT, ha]

/-- A lower bound `b` on the multiplier gives growth exponent `-b` and growth constant one. -/
theorem ofMeasureLpMultiplication_hasGrowthBound (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (b : ℝ) (hb : ∀ᵐ a ∂μ, b ≤ m a) :
    (ofMeasureLpMultiplication (E := E) hm hp b hb).HasGrowthBound (-b) 1 := by
  rw [ofMeasureLpMultiplication]
  simpa only [zero_sub] using
    (ContractionSemigroup.ofMeasureLpMultiplication (E := E) (p := p)
      (m := fun a => (m a - b).toNNReal) (by fun_prop) hp).hasGrowthBound.expShift (lambda := b)

/-- The generator acts as multiplication by `-m` almost everywhere. -/
@[simp]
theorem ofMeasureLpMultiplication_generator_apply_ae (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (b : ℝ) (hb : ∀ᵐ a ∂μ, b ≤ m a)
    (f : (ofMeasureLpMultiplication (E := E) hm hp b hb).generator.domain) :
    (ofMeasureLpMultiplication hm hp b hb).generator f =ᵐ[μ]
      fun a => -(m a • (f : Lp E p μ) a) := by
  let S := (ContractionSemigroup.ofMeasureLpMultiplication (E := E) (p := p)
    (m := fun a => (m a - b).toNNReal) (by fun_prop) hp).toStronglyContinuousSemigroup
  have hgen : (ofMeasureLpMultiplication hm hp b hb).generator =
      LinearPMap.subScalar S.generator b := by
    rw [ofMeasureLpMultiplication, generator_expShift]
  have hd : (ofMeasureLpMultiplication hm hp b hb).generator.domain = S.generator.domain :=
    (congrArg _root_.LinearPMap.domain hgen).trans (LinearPMap.subScalar_domain _ _)
  have hf : (f : Lp E p μ) ∈ S.generator.domain := hd ▸ f.property
  let f' : S.generator.domain := ⟨f, hf⟩
  rw [LinearPMap.congr_fun hgen f.property (hgen ▸ f.property), LinearPMap.subScalar_apply]
  filter_upwards [ContractionSemigroup.ofMeasureLpMultiplication_generator_apply_ae
      (m := fun a => (m a - b).toNNReal) (by fun_prop) hp f',
    Lp.coeFn_sub (S.generator f') (b • (f : Lp E p μ)),
    Lp.coeFn_smul b (f : Lp E p μ), hb] with a hg hsub hs ha
  rw [hsub, Pi.sub_apply, hs, Pi.smul_apply, hg,
    Real.coe_toNNReal _ (sub_nonneg.mpr ha)]
  module

/-- The generator domain consists exactly of the vectors whose product with `m` belongs to Lᵖ.
Neither boundedness of `m` nor finiteness of the measure is needed. -/
@[simp]
theorem ofMeasureLpMultiplication_mem_domain_iff (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (b : ℝ) (hb : ∀ᵐ a ∂μ, b ≤ m a) (f : Lp E p μ) :
    f ∈ (ofMeasureLpMultiplication hm hp b hb).domain ↔ MemLp (fun a => m a • f a) p μ := by
  rw [← generator_domain, ofMeasureLpMultiplication, generator_expShift,
    LinearPMap.subScalar_domain, generator_domain,
    ContractionSemigroup.ofMeasureLpMultiplication_mem_domain_iff]
  have heq : (fun a => ((m a - b).toNNReal : ℝ) • f a) =ᵐ[μ]
      fun a => m a • f a - b • f a := by
    filter_upwards [hb] with a ha
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr ha), sub_smul]
  rw [memLp_congr_ae heq]
  have hf := (Lp.memLp f).const_smul b
  constructor
  · intro h
    convert h.add hf using 1
    ext a
    simp
  · intro h
    exact h.sub hf

variable [CompleteSpace E]

/-- Above the growth exponent, the generator resolvent multiplies by `(λ + m)⁻¹`
almost everywhere. The spectral parameter need not be positive. -/
@[simp]
theorem ofMeasureLpMultiplication_generator_resolvent_apply_ae (hm : AEMeasurable m μ)
    (hp : p ≠ ∞) (b : ℝ) (hb : ∀ᵐ a ∂μ, b ≤ m a) {c : ℝ} (hc : -b < c)
    (f : Lp E p μ) :
    LinearPMap.resolvent (ofMeasureLpMultiplication hm hp b hb).generator c f =ᵐ[μ]
      fun a => (c + m a)⁻¹ • f a := by
  let S := ContractionSemigroup.ofMeasureLpMultiplication (E := E) (p := p)
    (m := fun a => (m a - b).toNNReal) (by fun_prop) hp
  have hcb : 0 < c + b := by linarith
  have hρ := S.toStronglyContinuousSemigroup.mem_resolventSet_generator S.hasGrowthBound hcb
  rw [ofMeasureLpMultiplication, generator_expShift, LinearPMap.resolvent_subScalar hρ,
    generator_resolvent_eq _ S.hasGrowthBound hcb,
    ← ContractionSemigroup.resolvent_eq_stronglyContinuousSemigroup_resolvent]
  filter_upwards [ContractionSemigroup.ofMeasureLpMultiplication_resolvent_apply_ae
    (m := fun a => (m a - b).toNNReal) (by fun_prop) hp hcb f, hb] with a hr ha
  rw [hr, Real.coe_toNNReal _ (sub_nonneg.mpr ha)]
  congr 2
  ring

/-- The pointwise Laplace resolvent has the same multiplication formula above the
growth exponent. -/
@[simp]
theorem ofMeasureLpMultiplication_resolvent_apply_ae (hm : AEMeasurable m μ) (hp : p ≠ ∞)
    (b : ℝ) (hb : ∀ᵐ a ∂μ, b ≤ m a) {c : ℝ} (hc : -b < c) (f : Lp E p μ) :
    (ofMeasureLpMultiplication hm hp b hb).resolvent
        (ofMeasureLpMultiplication_hasGrowthBound hm hp b hb) c hc f =ᵐ[μ]
      fun a => (c + m a)⁻¹ • f a := by
  rw [← generator_resolvent_eq]
  exact ofMeasureLpMultiplication_generator_resolvent_apply_ae hm hp b hb hc f

end TauCeti.Semigroups.StronglyContinuousSemigroup
