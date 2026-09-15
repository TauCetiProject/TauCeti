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
* `StronglyContinuousSemigroup.mem_complexify_domain_iff`: the generator domain is determined
  componentwise.
* `StronglyContinuousSemigroup.complexify_complexGenerator_apply`: the complex generator acts
  componentwise.
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
private theorem tendsto_complexify_genQuot_iff (S : StronglyContinuousSemigroup X)
    (z y : TauCeti.Complexification X) :
    Tendsto
        (fun t : ℝ => (1 / t) • (S.complexify.realOperator t z - z))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 y) ↔
      Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t z.re - z.re))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 y.re) ∧
        Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t z.im - z.im))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 y.im) := by
  rw [(equivProd X).toHomeomorph.isEmbedding.tendsto_nhds_iff, Prod.tendsto_iff]
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply, equivProd_apply,
    real_smul_re, real_smul_im, sub_re, sub_im, complexify_realOperator,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.complexify_apply_re,
    ContinuousLinearMap.complexify_apply_im]

omit [CompleteSpace X] in
/-- A vector belongs to the generator domain of the complexified semigroup exactly when its real
and imaginary parts belong to the generator domain of the original semigroup. -/
@[simp]
theorem mem_complexify_domain_iff (S : StronglyContinuousSemigroup X)
    (z : TauCeti.Complexification X) :
    z ∈ S.complexify.domain ↔ z.re ∈ S.domain ∧ z.im ∈ S.domain := by
  rw [S.complexify.mem_domain_iff_tendsto, S.mem_domain_iff_tendsto,
    S.mem_domain_iff_tendsto]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨y.re, (S.tendsto_complexify_genQuot_iff z y).mp hy |>.1⟩,
      ⟨y.im, (S.tendsto_complexify_genQuot_iff z y).mp hy |>.2⟩⟩
  · rintro ⟨⟨yre, hre⟩, ⟨yim, him⟩⟩
    exact ⟨⟨yre, yim⟩, (S.tendsto_complexify_genQuot_iff z ⟨yre, yim⟩).mpr ⟨hre, him⟩⟩

omit [CompleteSpace X] in
/-- The real generator of the complexified semigroup acts componentwise by the original
generator. -/
@[simp]
theorem complexify_generator_apply (S : StronglyContinuousSemigroup X)
    (z : S.complexify.domain) :
    S.complexify.generator
        ⟨z, by rw [S.complexify.generator_domain]; exact z.property⟩ =
      ⟨S.generator ⟨(z : TauCeti.Complexification X).re,
          by rw [S.generator_domain]
             exact (S.mem_complexify_domain_iff z).mp z.property |>.1⟩,
        S.generator ⟨(z : TauCeti.Complexification X).im,
          by rw [S.generator_domain]
             exact (S.mem_complexify_domain_iff z).mp z.property |>.2⟩⟩ := by
  have hz := (S.mem_complexify_domain_iff z).mp z.property
  let zre : S.domain := ⟨(z : TauCeti.Complexification X).re, hz.1⟩
  let zim : S.domain := ⟨(z : TauCeti.Complexification X).im, hz.2⟩
  apply S.complexify.generator_eq_of_tendsto z.property
  apply (S.tendsto_complexify_genQuot_iff z _).mpr
  simpa only [zre, zim, Subtype.coe_mk] using
    And.intro (S.generator_tendsto zre) (S.generator_tendsto zim)

omit [CompleteSpace X] in
/-- The complex generator of the complexified semigroup acts componentwise by the original real
generator. -/
theorem complexify_complexGenerator_apply (S : StronglyContinuousSemigroup X)
    (z : (S.complexify.complexGenerator S.isComplexLinear_complexify).domain) :
    S.complexify.complexGenerator S.isComplexLinear_complexify z =
      ⟨S.generator ⟨(z : TauCeti.Complexification X).re,
          by rw [S.generator_domain]
             exact (S.mem_complexify_domain_iff z).mp (by
               rw [← S.complexify.mem_complexDomain_iff S.isComplexLinear_complexify,
                 ← S.complexify.complexGenerator_domain S.isComplexLinear_complexify]
               exact z.property) |>.1⟩,
        S.generator ⟨(z : TauCeti.Complexification X).im,
          by rw [S.generator_domain]
             exact (S.mem_complexify_domain_iff z).mp (by
               rw [← S.complexify.mem_complexDomain_iff S.isComplexLinear_complexify,
                 ← S.complexify.complexGenerator_domain S.isComplexLinear_complexify]
               exact z.property) |>.2⟩⟩ := by
  rw [S.complexify.complexGenerator_apply S.isComplexLinear_complexify]
  let zdom : S.complexify.domain := ⟨z, by
    rw [← S.complexify.mem_complexDomain_iff S.isComplexLinear_complexify,
      ← S.complexify.complexGenerator_domain S.isComplexLinear_complexify]
    exact z.property⟩
  simpa only [zdom, Subtype.coe_mk] using S.complexify_generator_apply zdom

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
