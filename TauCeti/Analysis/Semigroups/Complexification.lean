/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Complexification
public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear

/-!
# Complexification of strongly continuous semigroups

This file extends a strongly continuous semigroup on a real normed space to the normed
complexification of that space.  The extension acts componentwise,

`S_ℂ(t)(x + i y) = S(t)x + i S(t)y`.

The Taylor norm on `Complexification X` makes complexification preserve operator norms, so every
growth bound passes to the extended semigroup with the same constants.  The extended semigroup is
complex linear, and its generator domain consists exactly of the vectors whose real and imaginary
parts belong to the original generator domain.  Its complex generator acts componentwise by the
original generator.  These facts provide the generator bridge needed to transfer real resolvent
estimates to a complex resolvent and use complex-analytic resolvent theory.

## Main declarations

* `StronglyContinuousSemigroup.complexify`: the componentwise complexification of a C₀-semigroup.
* `StronglyContinuousSemigroup.isComplexLinear_complexify`: the extension is complex linear.
* `StronglyContinuousSemigroup.hasGrowthBound_complexify_iff`: complexification preserves growth
  bounds with exactly the same constants.
* `StronglyContinuousSemigroup.mem_complexify_domain_iff`: the generator domain is determined
  componentwise.
* `StronglyContinuousSemigroup.complexGenerator_complexify_apply`: the complex generator acts by
  applying the original real generator to both components.
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

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem restrictScalars_complexify_apply_re (T : X →L[ℝ] X)
    (z : TauCeti.Complexification X) :
    ((T.complexify.restrictScalars ℝ) z).re = T z.re := by
  -- Restricting scalars changes only the bundled scalar structure, so expose the original map.
  change (T.complexify z).re = T z.re
  exact ContinuousLinearMap.complexify_apply_re T z

private theorem restrictScalars_complexify_apply_im (T : X →L[ℝ] X)
    (z : TauCeti.Complexification X) :
    ((T.complexify.restrictScalars ℝ) z).im = T z.im := by
  -- Restricting scalars changes only the bundled scalar structure, so expose the original map.
  change (T.complexify z).im = T z.im
  exact ContinuousLinearMap.complexify_apply_im T z

namespace StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The componentwise complexification of a strongly continuous semigroup:
`S_ℂ(t)(x + i y) = S(t)x + i S(t)y`. -/
def complexify (S : StronglyContinuousSemigroup X) :
    StronglyContinuousSemigroup (TauCeti.Complexification X) where
  toFun t := (S t).complexify.restrictScalars ℝ
  map_zero' := by
    ext z <;> simp
  map_add' s t := by
    ext z <;> simp [S.map_add]
  continuousAt_zero' z := by
    rw [ContinuousAt]
    have happly : (fun t : ℝ≥0 => ((S t).complexify.restrictScalars ℝ) z) =
        fun t => (⟨S t z.re, S t z.im⟩ : TauCeti.Complexification X) := by
      funext t
      ext <;> simp
    have hzero : ((S 0).complexify.restrictScalars ℝ) z = z := by
      ext <;> simp
    have hprod := (S.continuousAt_zero_tendsto z.re).prodMk_nhds
      (S.continuousAt_zero_tendsto z.im)
    rw [happly, hzero]
    rw [(equivProd X).toHomeomorph.isEmbedding.tendsto_nhds_iff]
    have heq : (⇑(equivProd X).toHomeomorph ∘
        fun t : ℝ≥0 => (⟨S t z.re, S t z.im⟩ : TauCeti.Complexification X)) =
        fun t => (S t z.re, S t z.im) := by
      funext t
      rw [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply, equivProd_apply]
    rw [heq]
    have htarget : (equivProd X).toHomeomorph z = (z.re, z.im) := by
      -- The homeomorphism and continuous-linear-equivalence coercions have the same function.
      change equivProd X z = (z.re, z.im)
      exact equivProd_apply z
    rw [htarget]
    exact hprod

/-- The operator of the complexified semigroup is the complexification of the original operator,
viewed as a real-linear map. -/
@[simp]
theorem complexify_apply (S : StronglyContinuousSemigroup X) (t : ℝ≥0) :
    S.complexify t = (S t).complexify.restrictScalars ℝ :=
  (rfl)

/-- The real part of the complexified semigroup action is the original action on the real part. -/
theorem complexify_apply_re (S : StronglyContinuousSemigroup X) (t : ℝ≥0)
    (z : TauCeti.Complexification X) : (S.complexify t z).re = S t z.re :=
  by
    rw [complexify_apply]
    exact restrictScalars_complexify_apply_re (S t) z

/-- The imaginary part of the complexified semigroup action is the original action on the
imaginary part. -/
theorem complexify_apply_im (S : StronglyContinuousSemigroup X) (t : ℝ≥0)
    (z : TauCeti.Complexification X) : (S.complexify t z).im = S t z.im :=
  by
    rw [complexify_apply]
    exact restrictScalars_complexify_apply_im (S t) z

/-- The complexified semigroup extends the original semigroup along the real embedding. -/
theorem complexify_apply_ofReal (S : StronglyContinuousSemigroup X) (t : ℝ≥0) (x : X) :
    S.complexify t (ofReal x) = ofReal (S t x) := by
  ext <;> simp

/-- The real-time operator of the complexified semigroup is the complexification of the original
real-time operator, viewed as a real-linear map. -/
@[simp]
theorem complexify_realOperator (S : StronglyContinuousSemigroup X) (t : ℝ) :
    S.complexify.realOperator t = (S.realOperator t).complexify.restrictScalars ℝ :=
  by rw [S.complexify.realOperator_def, S.realOperator_def, complexify_apply]

/-- The real-time action of the complexified semigroup extends the original real-time action. -/
theorem complexify_realOperator_apply_ofReal (S : StronglyContinuousSemigroup X) (t : ℝ)
    (x : X) : S.complexify.realOperator t (ofReal x) = ofReal (S.realOperator t x) := by
  ext <;> simp

/-- The real part of the complexified real-time action is the original action on the real part. -/
theorem complexify_realOperator_apply_re (S : StronglyContinuousSemigroup X) (t : ℝ)
    (z : TauCeti.Complexification X) :
    (S.complexify.realOperator t z).re = S.realOperator t z.re := by
  rw [S.complexify_realOperator]
  exact restrictScalars_complexify_apply_re (S.realOperator t) z

/-- The imaginary part of the complexified real-time action is the original action on the
imaginary part. -/
theorem complexify_realOperator_apply_im (S : StronglyContinuousSemigroup X) (t : ℝ)
    (z : TauCeti.Complexification X) :
    (S.complexify.realOperator t z).im = S.realOperator t z.im := by
  rw [S.complexify_realOperator]
  exact restrictScalars_complexify_apply_im (S.realOperator t) z

/-- Complexifying a semigroup preserves the operator norm at every nonnegative time. -/
theorem norm_complexify_apply (S : StronglyContinuousSemigroup X) (t : ℝ≥0) :
    ‖S.complexify t‖ = ‖S t‖ := by
  rw [S.complexify_apply]
  exact ContinuousLinearMap.norm_restrictScalars _ |>.trans
    (ContinuousLinearMap.norm_complexify (S t))

/-- Complexifying a semigroup preserves the operator norm of its real-time extension. -/
theorem norm_complexify_realOperator (S : StronglyContinuousSemigroup X) (t : ℝ) :
    ‖S.complexify.realOperator t‖ = ‖S.realOperator t‖ := by
  rw [S.complexify_realOperator]
  exact ContinuousLinearMap.norm_restrictScalars _ |>.trans
    (ContinuousLinearMap.norm_complexify (S.realOperator t))

/-- The componentwise complexification is a complex-linear semigroup. -/
theorem isComplexLinear_complexify (S : StronglyContinuousSemigroup X) :
    S.complexify.IsComplexLinear := by
  rw [S.complexify.isComplexLinear_iff]
  intro t c z
  ext <;> simp

/-- A growth bound for a real semigroup passes unchanged to its complexification. -/
theorem HasGrowthBound.complexify {S : StronglyContinuousSemigroup X} {ω M : ℝ}
    (hS : S.HasGrowthBound ω M) : S.complexify.HasGrowthBound ω M := by
  apply StronglyContinuousSemigroup.hasGrowthBound_of_bound hS.one_le
  intro t ht
  rw [S.norm_complexify_realOperator]
  exact hS.bound t ht

/-- Complexification preserves a specified semigroup growth bound in both directions. -/
@[simp]
theorem hasGrowthBound_complexify_iff (S : StronglyContinuousSemigroup X) (ω M : ℝ) :
    S.complexify.HasGrowthBound ω M ↔ S.HasGrowthBound ω M := by
  refine ⟨fun hS => StronglyContinuousSemigroup.hasGrowthBound_of_bound hS.one_le fun t ht => ?_,
    HasGrowthBound.complexify⟩
  simpa using hS.bound t ht

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
    restrictScalars_complexify_apply_re, restrictScalars_complexify_apply_im]

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

/-- The real generator of the complexified semigroup acts componentwise by the original
generator. -/
@[simp]
theorem generator_complexify_apply (S : StronglyContinuousSemigroup X)
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

/-- The complex generator of the complexified semigroup acts componentwise by the original real
generator. -/
theorem complexGenerator_complexify_apply (S : StronglyContinuousSemigroup X)
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
  simpa only [zdom, Subtype.coe_mk] using S.generator_complexify_apply zdom

end StronglyContinuousSemigroup

namespace ContractionSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The componentwise complexification of a contraction semigroup. -/
def complexify (S : ContractionSemigroup X) :
    ContractionSemigroup (TauCeti.Complexification X) where
  toStronglyContinuousSemigroup := S.toStronglyContinuousSemigroup.complexify
  contracting t := by
    -- The structure field is displayed through `toFun`; expose the underlying semigroup operator.
    change ‖S.toStronglyContinuousSemigroup.complexify t‖ ≤ 1
    rw [StronglyContinuousSemigroup.norm_complexify_apply]
    exact S.contracting t

/-- The C₀-semigroup underlying the complexification of a contraction semigroup is the
complexification of its underlying C₀-semigroup. -/
@[simp]
theorem complexify_toStronglyContinuousSemigroup (S : ContractionSemigroup X) :
    S.complexify.toStronglyContinuousSemigroup = S.toStronglyContinuousSemigroup.complexify :=
  (rfl)

/-- The operator of the complexified contraction semigroup is the complexification of the
original operator, viewed as a real-linear map. -/
@[simp]
theorem complexify_apply (S : ContractionSemigroup X) (t : ℝ≥0) :
    S.complexify t = (S t).complexify.restrictScalars ℝ :=
  (rfl)

end ContractionSemigroup

end TauCeti.Semigroups

end
