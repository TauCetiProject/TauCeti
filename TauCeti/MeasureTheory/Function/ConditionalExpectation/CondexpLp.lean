/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Conditional expectation as a contraction of `Lᵖ`

For a finite measure `μ` and `1 ≤ p ≤ ∞`, the conditional expectation `μ[f | m]` of a function
`f ∈ Lᵖ(μ)` is again in `Lᵖ(μ)`, with no larger norm (Mathlib's `MeasureTheory.MemLp.condExp` and
`MeasureTheory.eLpNorm_condExp_le_eLpNorm`). Since `Lᵖ(μ) ⊆ L¹(μ)` for finite `μ`, conditional
expectation is linear on `Lᵖ(μ)`, so it is a continuous linear map of norm at most one. This
complements Mathlib's `MeasureTheory.condExpL1CLM` and `MeasureTheory.condExpL2`, which treat the
exponents one and two.

When the σ-algebra `m` is pulled back from a finite discrete space along a measurable map `g`,
every `m`-measurable function factors through `g`, so the conditional expectation has
finite-dimensional range when the values lie in a finite-dimensional space. Such finite-rank
contractions are the approximating operators for the metric approximation property of `Lᵖ`.

## Main definitions

* `MeasureTheory.condExpLpCLM`: the conditional expectation as a continuous linear map
  `Lp F p μ →L[𝕜] Lp F p μ`.

## Main results

* `MeasureTheory.coeFn_condExpLpCLM`: `condExpLpCLM 𝕜 p m μ f` is a.e. equal to `μ[f | m]`.
* `MeasureTheory.aestronglyMeasurable_condExpLpCLM`,
  `MeasureTheory.condExpLpCLM_of_aestronglyMeasurable'` and
  `MeasureTheory.condExpLpCLM_comp_self`: the conditional expectation is a projection onto the
  classes of `m`-measurable functions.
* `MeasureTheory.norm_condExpLpCLM_le`: the conditional expectation is a contraction of `Lᵖ`.
* `MeasureTheory.hasFiniteRange_condExpLpCLM`: conditioning on a σ-algebra pulled back from a
  finite discrete space gives a finite-rank operator.
-/

public section

noncomputable section

open Filter

open scoped ENNReal

namespace MeasureTheory

-- `m0` comes after `m` so that it is the measurable-space instance used for `α`.
variable {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : MeasurableSpace α) {m0 : MeasurableSpace α} (μ : Measure α)
  [IsFiniteMeasure μ]

/-- The conditional expectation with respect to a σ-algebra `m`, as a continuous linear map of
`Lᵖ(μ)` for a finite measure `μ` and `1 ≤ p ≤ ∞`. It sends the class of `f` to the class of
`μ[f | m]`; see `MeasureTheory.coeFn_condExpLpCLM`. -/
def condExpLpCLM : Lp F p μ →L[𝕜] Lp F p μ :=
  LinearMap.mkContinuous
    { toFun f := ((Lp.memLp f).condExp Fact.out).toLp (μ[f | m])
      map_add' f g := by
        have hint (h : Lp F p μ) : Integrable h μ := (Lp.memLp h).integrable Fact.out
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).condExp (m := m) Fact.out),
          MemLp.coeFn_toLp ((Lp.memLp f).condExp (m := m) Fact.out),
          MemLp.coeFn_toLp ((Lp.memLp g).condExp (m := m) Fact.out),
          Lp.coeFn_add (((Lp.memLp f).condExp (m := m) Fact.out).toLp _)
            (((Lp.memLp g).condExp (m := m) Fact.out).toLp _),
          condExp_congr_ae (m := m) (Lp.coeFn_add f g),
          condExp_add (hint f) (hint g) m] with x hfg hf hg hadd hcongr hsum
        simp only [hfg, hadd, Pi.add_apply, hf, hg, hcongr, hsum]
      map_smul' c f := by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).condExp (m := m) Fact.out),
          MemLp.coeFn_toLp ((Lp.memLp f).condExp (m := m) Fact.out),
          Lp.coeFn_smul c (((Lp.memLp f).condExp (m := m) Fact.out).toLp _),
          condExp_congr_ae (m := m) (Lp.coeFn_smul c f),
          condExp_smul (m := m) (μ := μ) c f] with x hcf hf hsmul hcongr hc
        simp only [hcf, hsmul, Pi.smul_apply, hf, hcongr, hc, RingHom.id_apply] }
    1 fun f => by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_condExp_le_eLpNorm _ Fact.out)

variable {𝕜 p m μ}

/-- The conditional expectation on `Lᵖ` is represented by `μ[f | m]`. -/
theorem coeFn_condExpLpCLM (f : Lp F p μ) : condExpLpCLM 𝕜 p m μ f =ᵐ[μ] μ[f | m] :=
  MemLp.coeFn_toLp ((Lp.memLp f).condExp Fact.out)

/-- The conditional expectation of the class of `f ∈ Lᵖ` is the class of `μ[f | m]`. -/
theorem condExpLpCLM_toLp {f : α → F} (hf : MemLp f p μ) :
    condExpLpCLM 𝕜 p m μ (hf.toLp f) = (hf.condExp Fact.out).toLp (μ[f | m]) :=
  Lp.ext <| (coeFn_condExpLpCLM _).trans <|
    (condExp_congr_ae hf.coeFn_toLp).trans (MemLp.coeFn_toLp _).symm

/-- The conditional expectation on `Lᵖ` takes values in `m`-measurable classes. -/
theorem aestronglyMeasurable_condExpLpCLM (f : Lp F p μ) :
    AEStronglyMeasurable[m] (condExpLpCLM 𝕜 p m μ f) μ :=
  ⟨μ[f | m], stronglyMeasurable_condExp, coeFn_condExpLpCLM f⟩

/-- The conditional expectation on `Lᵖ` fixes the classes of `m`-measurable functions. -/
theorem condExpLpCLM_of_aestronglyMeasurable' (hm : m ≤ m0) {f : Lp F p μ}
    (hf : AEStronglyMeasurable[m] f μ) : condExpLpCLM 𝕜 p m μ f = f :=
  Lp.ext <| (coeFn_condExpLpCLM f).trans <|
    condExp_of_aestronglyMeasurable' hm hf ((Lp.memLp f).integrable Fact.out)

/-- The conditional expectation on `Lᵖ` is idempotent. -/
@[simp]
theorem condExpLpCLM_condExpLpCLM (f : Lp F p μ) :
    condExpLpCLM 𝕜 p m μ (condExpLpCLM 𝕜 p m μ f) = condExpLpCLM 𝕜 p m μ f := by
  by_cases hm : m ≤ m0
  · exact condExpLpCLM_of_aestronglyMeasurable' hm (aestronglyMeasurable_condExpLpCLM f)
  · -- If `m` is not a sub-σ-algebra, the conditional expectation vanishes.
    have h0 : condExpLpCLM 𝕜 p m μ f = 0 := by
      refine Lp.ext <| (coeFn_condExpLpCLM f).trans ?_
      rw [condExp_of_not_le hm]
      exact (Lp.coeFn_zero ..).symm
    rw [h0, map_zero]

/-- The conditional expectation on `Lᵖ` is a projection. -/
theorem condExpLpCLM_comp_self :
    (condExpLpCLM 𝕜 p m μ : Lp F p μ →L[𝕜] Lp F p μ).comp (condExpLpCLM 𝕜 p m μ) =
      condExpLpCLM 𝕜 p m μ :=
  ContinuousLinearMap.ext condExpLpCLM_condExpLpCLM

/-- The conditional expectation is a contraction of `Lᵖ`. -/
theorem norm_condExpLpCLM_le : ‖(condExpLpCLM 𝕜 p m μ : Lp F p μ →L[𝕜] Lp F p μ)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Conditioning on a σ-algebra pulled back from a finite discrete space along a measurable map
gives a finite-rank operator on `Lᵖ` with values in a finite-dimensional space: its values are
classes of functions that factor through the map. -/
theorem hasFiniteRange_condExpLpCLM [FiniteDimensional 𝕜 F] {ι : Type*} [Finite ι]
    [mι : MeasurableSpace ι] [DiscreteMeasurableSpace ι] {g : α → ι} (hg : Measurable g)
    (hm : m ≤ mι.comap g) :
    (condExpLpCLM 𝕜 p m μ : Lp F p μ →L[𝕜] Lp F p μ).toLinearMap.HasFiniteRange := by
  -- Composition with `g` is a linear map from the finite-dimensional space `ι → F` to `Lᵖ`.
  have hmem (h : ι → F) : MemLp (h ∘ g) p μ := by
    have : Fintype ι := Fintype.ofFinite ι
    refine MemLp.of_bound (StronglyMeasurable.of_discrete.comp_measurable hg).aestronglyMeasurable
      (∑ i, ‖h i‖) (ae_of_all _ fun x => ?_)
    exact Finset.single_le_sum (f := fun i => ‖h i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (g x))
  let Ψ : (ι → F) →ₗ[𝕜] Lp F p μ :=
    { toFun h := (hmem h).toLp (h ∘ g)
      map_add' h h' := MemLp.toLp_add (hmem h) (hmem h')
      map_smul' c h := MemLp.toLp_const_smul c (hmem h) }
  -- Each conditional expectation is `m`-measurable, hence a function of `g`.
  have hle : LinearMap.range (condExpLpCLM 𝕜 p m μ : Lp F p μ →L[𝕜] Lp F p μ).toLinearMap ≤
      LinearMap.range Ψ := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨h, -, hh⟩ :=
      (stronglyMeasurable_condExp (m := m) (μ := μ) (f := f)).mono hm |>.exists_eq_measurable_comp
    refine ⟨h, Lp.ext ?_⟩
    filter_upwards [MemLp.coeFn_toLp (hmem h), coeFn_condExpLpCLM (𝕜 := 𝕜) f] with x hx hx'
    exact hx.trans ((congrFun hh x).symm.trans hx'.symm)
  exact (Submodule.fg_iff_finiteDimensional _).2 (Submodule.finiteDimensional_of_le hle)

end MeasureTheory
