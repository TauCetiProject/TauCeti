/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Complexification
public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear
public import TauCeti.Analysis.Semigroups.GrowthBound

/-!
# Complexification of strongly continuous semigroups

A strongly continuous semigroup on a real Banach space extends componentwise to the normed
complexification of that space.  The resulting semigroup is complex linear.  Because the Taylor
norm makes complexification isometric on bounded operators, this extension preserves every
operator norm and hence every exponential growth bound without changing its constants.

This construction is the real-to-complex bridge for applying complex spectral theory to a real
semigroup.  In particular, it allows complex resolvent results for complex-linear semigroups to be
transported back to real Banach spaces without weakening Hille--Yosida estimates.

## Main declarations

* `StronglyContinuousSemigroup.complexify`: the componentwise complexification of a real
  strongly continuous semigroup.
* `StronglyContinuousSemigroup.isComplexLinear_complexify`: the complexified semigroup is
  complex linear.
* `StronglyContinuousSemigroup.hasGrowthBound_complexify_iff`: complexification preserves a
  growth bound with exactly the same constants.
* `StronglyContinuousSemigroup.mem_complexify_domain_iff`: the generator domain is described
  componentwise.
* `StronglyContinuousSemigroup.complexify_generator_apply`: the generator acts componentwise.
* `StronglyContinuousSemigroup.mem_complexify_generator_graph_iff`: the generator graph is the
  componentwise complexification of the original graph.
* `ContractionSemigroup.complexify`: complexification of a contraction semigroup.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section II.2.1.
-/

public section

noncomputable section

open Filter
open scoped NNReal Topology

namespace TauCeti.Semigroups

open TauCeti.Complexification

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

/-- The componentwise complexification of a strongly continuous semigroup on a real Banach
space.  At time `t`, its complex-linear operator is the complexification of `S t`. -/
def complexify (S : StronglyContinuousSemigroup X) :
    StronglyContinuousSemigroup (TauCeti.Complexification X) where
  toFun t := (S t).complexify.restrictScalars ℝ
  map_zero' := by
    rw [S.map_zero, ContinuousLinearMap.complexify_id]
    apply ContinuousLinearMap.ext
    intro z
    rfl
  map_add' s t := by
    rw [S.map_add, ContinuousLinearMap.complexify_comp]
    apply ContinuousLinearMap.ext
    intro z
    rfl
  continuousAt_zero' z := by
    have h := (S.continuousAt_zero z.re).prodMk (S.continuousAt_zero z.im)
    have hc := (TauCeti.Complexification.equivProd X).symm.continuous.continuousAt.tendsto.comp h
    have heq : (fun t => (S t).complexify.restrictScalars ℝ z) =
        fun t => (TauCeti.Complexification.equivProd X).symm (S t z.re, S t z.im) := by
      funext t
      apply TauCeti.Complexification.ext <;> simp
    rw [heq]
    exact hc

omit [CompleteSpace X] in
/-- The real part of the complexified orbit is the original orbit of the real part. -/
@[simp]
theorem complexify_apply_re (S : StronglyContinuousSemigroup X) (t : ℝ≥0)
    (z : TauCeti.Complexification X) :
    (S.complexify t z).re = S t z.re := by
  exact ContinuousLinearMap.complexify_apply_re (S t) z

omit [CompleteSpace X] in
/-- The imaginary part of the complexified orbit is the original orbit of the imaginary part. -/
@[simp]
theorem complexify_apply_im (S : StronglyContinuousSemigroup X) (t : ℝ≥0)
    (z : TauCeti.Complexification X) :
    (S.complexify t z).im = S t z.im := by
  exact ContinuousLinearMap.complexify_apply_im (S t) z

omit [CompleteSpace X] in
/-- The complexified semigroup extends the original semigroup along the real embedding. -/
@[simp]
theorem complexify_apply_ofReal (S : StronglyContinuousSemigroup X) (t : ℝ≥0) (x : X) :
    S.complexify t (ofReal x) = ofReal (S t x) :=
  ContinuousLinearMap.complexify_ofReal (S t) x

omit [CompleteSpace X] in
/-- The operator norm at each time is unchanged by complexification. -/
@[simp]
theorem norm_complexify_apply (S : StronglyContinuousSemigroup X) (t : ℝ≥0) :
    ‖S.complexify t‖ = ‖S t‖ :=
  (ContinuousLinearMap.norm_restrictScalars ((S t).complexify)).trans
    (ContinuousLinearMap.norm_complexify (S t))

omit [CompleteSpace X] in
/-- The complexification commutes with the real-time operator shim. -/
@[simp]
theorem complexify_realOperator (S : StronglyContinuousSemigroup X) (t : ℝ) :
    S.complexify.realOperator t = (S.realOperator t).complexify.restrictScalars ℝ := by
  rw [S.complexify.realOperator_def, S.realOperator_def]
  apply ContinuousLinearMap.ext
  intro z
  apply TauCeti.Complexification.ext
  · exact (S.complexify_apply_re t.toNNReal z).trans
      (ContinuousLinearMap.complexify_apply_re (S t.toNNReal) z).symm
  · exact (S.complexify_apply_im t.toNNReal z).trans
      (ContinuousLinearMap.complexify_apply_im (S t.toNNReal) z).symm

omit [CompleteSpace X] in
/-- The real-time operator norm is unchanged by complexification. -/
theorem norm_complexify_realOperator (S : StronglyContinuousSemigroup X) (t : ℝ) :
    ‖S.complexify.realOperator t‖ = ‖S.realOperator t‖ := by
  rw [S.complexify_realOperator, ContinuousLinearMap.norm_restrictScalars,
    ContinuousLinearMap.norm_complexify]

omit [CompleteSpace X] in
/-- The complexified semigroup is complex linear. -/
theorem isComplexLinear_complexify (S : StronglyContinuousSemigroup X) :
    S.complexify.IsComplexLinear := by
  rw [isComplexLinear_iff]
  intro t z x
  exact (S t).complexify.map_smul z x

omit [CompleteSpace X] in
/-- Bundling an operator of the complexified semigroup as complex linear recovers the
complexification of the corresponding original operator. -/
@[simp]
theorem complexLinearOperator_complexify (S : StronglyContinuousSemigroup X) (t : ℝ≥0) :
    S.complexify.complexLinearOperator S.isComplexLinear_complexify t = (S t).complexify := by
  apply ContinuousLinearMap.ext
  intro z
  rw [S.complexify.complexLinearOperator_apply S.isComplexLinear_complexify]
  rfl

omit [CompleteSpace X] in
/-- Complexification preserves exponential growth bounds, with exactly the same exponent and
multiplicative constant. -/
theorem hasGrowthBound_complexify_iff (S : StronglyContinuousSemigroup X) (ω M : ℝ) :
    S.complexify.HasGrowthBound ω M ↔ S.HasGrowthBound ω M := by
  constructor
  · intro h
    refine hasGrowthBound_of_bound h.one_le fun t ht => ?_
    simpa using h.bound t ht
  · intro h
    refine hasGrowthBound_of_bound h.one_le fun t ht => ?_
    simpa using h.bound t ht

omit [CompleteSpace X] in
/-- Every growth bound of a real semigroup is a growth bound of its complexification. -/
theorem HasGrowthBound.complexify {S : StronglyContinuousSemigroup X} {ω M : ℝ}
    (h : S.HasGrowthBound ω M) : S.complexify.HasGrowthBound ω M :=
  (S.hasGrowthBound_complexify_iff ω M).2 h

omit [CompleteSpace X] in
/-- Convergence of the generator difference quotient for the complexified semigroup is
equivalent to convergence of both component difference quotients. -/
private theorem tendsto_complexify_genQuot_iff (S : StronglyContinuousSemigroup X)
    (z w : TauCeti.Complexification X) :
    Tendsto (fun t : ℝ => (1 / t) • (S.complexify.realOperator t z - z))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds w) ↔
      Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t z.re - z.re))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds w.re) ∧
      Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t z.im - z.im))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds w.im) := by
  change Filter.map _ _ ≤ nhds w ↔ _
  rw [← Filter.map_le_map_iff (TauCeti.Complexification.equivProd X).injective,
    (TauCeti.Complexification.equivProd X).map_nhds_eq, Filter.map_map]
  have hquot :
      (TauCeti.Complexification.equivProd X ∘ fun t : ℝ =>
          (1 / t) • (S.complexify.realOperator t z - z)) =
        fun t : ℝ => ((1 / t) • (S.realOperator t z.re - z.re),
          (1 / t) • (S.realOperator t z.im - z.im)) := by
    funext t
    apply Prod.ext <;> simp
  rw [hquot]
  rw [TauCeti.Complexification.equivProd_apply]
  change Tendsto (fun t : ℝ =>
      ((1 / t) • (S.realOperator t z.re - z.re),
        (1 / t) • (S.realOperator t z.im - z.im)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (w.re, w.im)) ↔ _
  exact Prod.tendsto_iff _ _

omit [CompleteSpace X] in
/-- Membership in the generator domain of the complexified semigroup is componentwise membership
in the original generator domain. -/
@[simp]
theorem mem_complexify_domain_iff (S : StronglyContinuousSemigroup X)
    (z : TauCeti.Complexification X) :
    z ∈ S.complexify.domain ↔ z.re ∈ S.domain ∧ z.im ∈ S.domain := by
  rw [S.complexify.mem_domain_iff_tendsto]
  constructor
  · rintro ⟨w, hw⟩
    have hparts := (S.tendsto_complexify_genQuot_iff z w).mp hw
    constructor
    · rw [S.mem_domain_iff_tendsto]
      exact ⟨w.re, hparts.1⟩
    · rw [S.mem_domain_iff_tendsto]
      exact ⟨w.im, hparts.2⟩
  · rintro ⟨hre, him⟩
    refine ⟨⟨S.generator ⟨z.re, by simpa using hre⟩,
      S.generator ⟨z.im, by simpa using him⟩⟩, ?_⟩
    exact (S.tendsto_complexify_genQuot_iff z _).mpr
      ⟨S.generator_tendsto ⟨z.re, hre⟩, S.generator_tendsto ⟨z.im, him⟩⟩

omit [CompleteSpace X] in
/-- The generator of the complexified semigroup acts componentwise on its domain. -/
theorem complexify_generator_apply (S : StronglyContinuousSemigroup X)
    {z : TauCeti.Complexification X} (hz : z ∈ S.complexify.domain) :
    S.complexify.generator ⟨z, by
      rw [S.complexify.generator_domain]
      exact hz⟩ =
      ⟨S.generator ⟨z.re, by
          rw [S.generator_domain]
          exact ((S.mem_complexify_domain_iff z).mp hz).1⟩,
        S.generator ⟨z.im, by
          rw [S.generator_domain]
          exact ((S.mem_complexify_domain_iff z).mp hz).2⟩⟩ := by
  have hparts := (S.mem_complexify_domain_iff z).mp hz
  have htendsto := (S.tendsto_complexify_genQuot_iff z _).mp
    (S.complexify.generator_tendsto ⟨z, hz⟩)
  apply TauCeti.Complexification.ext
  · exact tendsto_nhds_unique htendsto.1 (S.generator_tendsto ⟨z.re, hparts.1⟩)
  · exact tendsto_nhds_unique htendsto.2 (S.generator_tendsto ⟨z.im, hparts.2⟩)

omit [CompleteSpace X] in
/-- The real part of the complexified generator is the original generator on the real part. -/
@[simp]
theorem complexify_generator_apply_re (S : StronglyContinuousSemigroup X)
    {z : TauCeti.Complexification X} (hz : z ∈ S.complexify.domain) :
    (S.complexify.generator ⟨z, by
      rw [S.complexify.generator_domain]
      exact hz⟩).re =
      S.generator ⟨z.re, by
        rw [S.generator_domain]
        exact ((S.mem_complexify_domain_iff z).mp hz).1⟩ := by
  rw [S.complexify_generator_apply hz]

omit [CompleteSpace X] in
/-- The imaginary part of the complexified generator is the original generator on the imaginary
part. -/
@[simp]
theorem complexify_generator_apply_im (S : StronglyContinuousSemigroup X)
    {z : TauCeti.Complexification X} (hz : z ∈ S.complexify.domain) :
    (S.complexify.generator ⟨z, by
      rw [S.complexify.generator_domain]
      exact hz⟩).im =
      S.generator ⟨z.im, by
        rw [S.generator_domain]
        exact ((S.mem_complexify_domain_iff z).mp hz).2⟩ := by
  rw [S.complexify_generator_apply hz]

omit [CompleteSpace X] in
/-- The graph of the generator of the complexified semigroup is obtained by complexifying the
graph of the original generator componentwise. Thus `Aℂ (x + i y) = A x + i A y`, with the
domain condition on both components included in the statement. -/
@[simp]
theorem mem_complexify_generator_graph_iff (S : StronglyContinuousSemigroup X)
    (z w : TauCeti.Complexification X) :
    (z, w) ∈ S.complexify.generator.graph ↔
      (z.re, w.re) ∈ S.generator.graph ∧ (z.im, w.im) ∈ S.generator.graph := by
  constructor
  · rw [LinearPMap.mem_graph_iff]
    rintro ⟨u, rfl, rfl⟩
    have hu : (u : TauCeti.Complexification X) ∈ S.complexify.domain := by
      simpa only [S.complexify.generator_domain] using u.property
    have hparts := (S.mem_complexify_domain_iff u).mp hu
    constructor
    · rw [LinearPMap.mem_graph_iff]
      refine ⟨⟨u.val.re, by simpa only [S.generator_domain] using hparts.1⟩, rfl, ?_⟩
      exact (S.complexify_generator_apply_re hu).symm
    · rw [LinearPMap.mem_graph_iff]
      refine ⟨⟨u.val.im, by simpa only [S.generator_domain] using hparts.2⟩, rfl, ?_⟩
      exact (S.complexify_generator_apply_im hu).symm
  · rintro ⟨hre, him⟩
    rw [LinearPMap.mem_graph_iff] at hre him ⊢
    obtain ⟨x, hx, hAx⟩ := hre
    obtain ⟨y, hy, hAy⟩ := him
    have hx' : (x : X) = z.re := hx
    have hAx' : S.generator x = w.re := hAx
    have hy' : (y : X) = z.im := hy
    have hAy' : S.generator y = w.im := hAy
    have hxdom : (x : X) ∈ S.domain := by
      rw [← S.generator_domain]
      exact x.property
    have hydom : (y : X) ∈ S.domain := by
      rw [← S.generator_domain]
      exact y.property
    have hz : z ∈ S.complexify.domain := (S.mem_complexify_domain_iff z).mpr
      ⟨by rw [← hx']; exact hxdom, by rw [← hy']; exact hydom⟩
    refine ⟨⟨z, by simpa only [S.complexify.generator_domain] using hz⟩, rfl, ?_⟩
    apply TauCeti.Complexification.ext
    · rw [S.complexify_generator_apply_re hz, ← hAx']
      congr 1
      exact Subtype.ext hx'.symm
    · rw [S.complexify_generator_apply_im hz, ← hAy']
      congr 1
      exact Subtype.ext hy'.symm

omit [CompleteSpace X] in
/-- The graph of the complex-linear generator is the componentwise complexification of the
original real generator graph. This is the complex-linear form of
`mem_complexify_generator_graph_iff`. -/
@[simp]
theorem mem_complexify_complexGenerator_graph_iff (S : StronglyContinuousSemigroup X)
    (z w : TauCeti.Complexification X) :
    (z, w) ∈ (S.complexify.complexGenerator S.isComplexLinear_complexify).graph ↔
      (z.re, w.re) ∈ S.generator.graph ∧ (z.im, w.im) ∈ S.generator.graph := by
  -- Expose graph membership as set membership so the scalar-restriction graph equality rewrites.
  change (z, w) ∈
      (((S.complexify.complexGenerator S.isComplexLinear_complexify).graph :
        Submodule ℂ _) : Set _) ↔ _
  rw [← LinearPMap.restrictScalars_coe_graph (S := ℝ)]
  rw [S.complexify.complexGenerator_restrictScalars]
  exact S.mem_complexify_generator_graph_iff z w

end StronglyContinuousSemigroup

namespace ContractionSemigroup

/-- The componentwise complexification of a contraction semigroup. -/
def complexify (S : ContractionSemigroup X) :
    ContractionSemigroup (TauCeti.Complexification X) where
  toStronglyContinuousSemigroup := S.toStronglyContinuousSemigroup.complexify
  contracting t := by
    exact (StronglyContinuousSemigroup.norm_complexify_apply
      S.toStronglyContinuousSemigroup t).trans_le (S.contracting t)

omit [CompleteSpace X] in
/-- The underlying C₀-semigroup of a complexified contraction semigroup is the
complexification of the underlying C₀-semigroup. -/
@[simp]
theorem complexify_toStronglyContinuousSemigroup (S : ContractionSemigroup X) :
    S.complexify.toStronglyContinuousSemigroup = S.toStronglyContinuousSemigroup.complexify :=
  (rfl)

omit [CompleteSpace X] in
/-- The real part of a complexified contraction-semigroup orbit is the original orbit of the
real part. -/
@[simp]
theorem complexify_apply_re (S : ContractionSemigroup X) (t : ℝ≥0)
    (z : TauCeti.Complexification X) :
    (S.complexify t z).re = S t z.re := by
  exact StronglyContinuousSemigroup.complexify_apply_re S.toStronglyContinuousSemigroup t z

omit [CompleteSpace X] in
/-- The imaginary part of a complexified contraction-semigroup orbit is the original orbit of
the imaginary part. -/
@[simp]
theorem complexify_apply_im (S : ContractionSemigroup X) (t : ℝ≥0)
    (z : TauCeti.Complexification X) :
    (S.complexify t z).im = S t z.im := by
  exact StronglyContinuousSemigroup.complexify_apply_im S.toStronglyContinuousSemigroup t z

omit [CompleteSpace X] in
/-- The complexified contraction semigroup extends the original one along the real embedding. -/
@[simp]
theorem complexify_apply_ofReal (S : ContractionSemigroup X) (t : ℝ≥0) (x : X) :
    S.complexify t (ofReal x) = ofReal (S t x) :=
  StronglyContinuousSemigroup.complexify_apply_ofReal S.toStronglyContinuousSemigroup t x

omit [CompleteSpace X] in
/-- The underlying C₀-semigroup of a complexified contraction semigroup is complex linear. -/
theorem isComplexLinear_complexify (S : ContractionSemigroup X) :
    S.complexify.toStronglyContinuousSemigroup.IsComplexLinear :=
  StronglyContinuousSemigroup.isComplexLinear_complexify S.toStronglyContinuousSemigroup

omit [CompleteSpace X] in
/-- Complexification preserves the operator norm of a contraction semigroup at every time. -/
@[simp]
theorem norm_complexify_apply (S : ContractionSemigroup X) (t : ℝ≥0) :
    ‖S.complexify t‖ = ‖S t‖ :=
  StronglyContinuousSemigroup.norm_complexify_apply S.toStronglyContinuousSemigroup t

end ContractionSemigroup

end TauCeti.Semigroups

end
