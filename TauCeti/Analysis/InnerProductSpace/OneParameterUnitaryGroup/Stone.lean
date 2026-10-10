/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.SemigroupBridge
public import TauCeti.Analysis.Semigroups.Resolvent.Basic

/-!
# Stone's theorem, forward direction

The generator of a one-parameter unitary group is self-adjoint.

`OneParameterUnitaryGroup.generator U` is defined as the limit of
`(U t ψ - ψ) / (i t)`, so `U t = exp (i t A)` and the expected conclusion is
that `A` is *self-adjoint* — not merely symmetric.  Symmetry alone is cheap and
was already available (`generator_isFormalAdjoint`); self-adjointness is the
statement with content, and it is the hypothesis that every spectral-calculus
consumer actually needs, since a spectral measure is built from a self-adjoint
operator and not from a symmetric one.

## The route, and why the hard step is missing

Textbook Stone runs through a mollification (Gårding) argument to show the
generator domain is dense, then produces the resolvent.  **Neither half is done
that way here.**

* **Density is free.**  If `A` is symmetric and `A + i` is *surjective*, then
  `Dom A` is dense: for `x ⊥ Dom A` pick `ψ` with `A ψ + i ψ = x`; then
  `0 = ⟪ψ, x⟫ = ⟪ψ, A ψ⟫ + i ‖ψ‖²`, whose imaginary part is `‖ψ‖²` because
  symmetry makes `⟪ψ, A ψ⟫` real.  So `ψ = 0` and hence `x = 0`.  This is
  `dense_domain_of_surjective_add_I`, and it removes the mollifier entirely.
* **Surjectivity is upstream.**  Tau Ceti's C₀-semigroup library already proves
  the Hille–Yosida resolvent identity `(λ - A) R(λ) x = x`
  (`StronglyContinuousSemigroup.resolventRightInv`).  Restricting `U` to `t ≥ 0`
  is a contraction semigroup, so `λ = 1` is admissible, and running the identity
  for `U` and for the time-reversed group `reversedGroup U` gives surjectivity of
  `A + i` and of `A - i` respectively.

What has to be supplied here is the *converse* of the Wave 3 generator bridge:
the semigroup only sees `t → 0⁺`, so its domain is a priori larger than the
group's.  For a unitary group it is not, because

`genDiffQuot U ψ (-t) = U (-t) (genDiffQuot U ψ t)`

(`genDiffQuot_neg`) and `U (-t) → 1` strongly, so a right-hand limit forces the
two-sided one.  `SemigroupBridge` flagged exactly this as the missing direction.

Note that no linearity of the resolvent over `ℂ` is used — the upstream
resolvent is only `ℝ`-linear.  The two surjectivity statements are obtained by
*choosing the input vector*, `∓i • φ`, rather than by moving a scalar through
`R`.

## Provenance

*New.*  The group structure and von Neumann's criterion come from
`OneParameterUnitaryGroup/Basic.lean` (ported from Spectra); the semigroup
resolvent is upstream Tau Ceti's.  Spectra reaches the spectral measure of a
unitary group through Bochner's theorem and a GNS construction instead, and
none of that subtree is used or needed here.
-/

public section

noncomputable section

open InnerProductSpace Complex Filter Topology
open scoped ComplexConjugate NNReal

namespace TauCeti
namespace OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Density of the domain is a consequence of surjectivity -/

/-- **A symmetric operator with `A + i` surjective has dense domain.**  This is
the step that normally requires a mollification argument for Stone's theorem;
here it is three lines of inner-product algebra, and it is what lets
`isSelfAdjoint_of_surjective_addSub` be applied without separately establishing
density. -/
theorem dense_domain_of_surjective_add_I (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    Dense (A.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨ψ, hψ⟩ := hplus x
  -- `x` is orthogonal to the domain, and `ψ` lies in it.
  have hx0 : ⟪(ψ : H), x⟫_ℂ = 0 := (Submodule.mem_orthogonal _ x).mp hx (ψ : H) ψ.2
  -- Symmetry makes the diagonal form real.
  have hreal : ((starRingEnd ℂ) ⟪(ψ : H), A ψ⟫_ℂ) = ⟪(ψ : H), A ψ⟫_ℂ := by
    rw [inner_conj_symm]; exact hsym ψ ψ
  have hIm : (⟪(ψ : H), A ψ⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
  -- Expand `0 = ⟪ψ, A ψ + i ψ⟫` and read off the imaginary part.
  have hexp : ⟪(ψ : H), A ψ⟫_ℂ + I * ⟪(ψ : H), (ψ : H)⟫_ℂ = 0 := by
    rw [← hψ, inner_add_right, inner_smul_right] at hx0
    exact hx0
  have hself : ⟪(ψ : H), (ψ : H)⟫_ℂ = 0 := by
    have him : (⟪(ψ : H), (ψ : H)⟫_ℂ).re = 0 := by
      have := congrArg Complex.im hexp
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.zero_im,
        hIm, zero_mul, one_mul, zero_add] at this
      exact this
    have hii : (⟪(ψ : H), (ψ : H)⟫_ℂ).im = 0 :=
      Complex.conj_eq_iff_im.mp (inner_conj_symm _ _)
    exact Complex.ext (by simpa using him) (by simpa using hii)
  have hψ0 : (ψ : H) = 0 := inner_self_eq_zero.mp hself
  have : ψ = 0 := Subtype.ext hψ0
  rw [this] at hψ
  simpa using hψ.symm

/-! ### A right-hand limit is two-sided -/

/-- The negative-time difference quotient is the positive-time one transported by
`U (-t)`.  This is the whole reason a unitary group has no one-sided pathology. -/
theorem genDiffQuot_neg (U : OneParameterUnitaryGroup (H := H)) (ψ : H) (t : ℝ) :
    genDiffQuot U ψ (-t) = U.U (-t) (genDiffQuot U ψ t) := by
  have hinv : U.U (-t) (U.U t ψ) = ψ := by
    have h := U.group_law (-t) t
    rw [show -t + t = 0 by ring, U.identity] at h
    simpa using DFunLike.congr_fun h.symm ψ
  simp only [genDiffQuot_apply, map_smul, map_sub, hinv]
  rw [Complex.ofReal_neg, mul_neg, inv_neg, neg_smul, ← smul_neg]
  congr 1
  abel

/-- Negation is a self-map of the punctured neighbourhood of `0`. -/
private theorem tendsto_neg_nhdsNE :
    Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

/-- Negation maps the left punctured neighbourhood of `0` to the right one. -/
private theorem tendsto_neg_nhdsLT :
    Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

/-- **The one-sided limit is enough.**  If the difference quotient converges as
`t → 0⁺` then it converges as `t → 0`, to the same vector. -/
theorem tendsto_genDiffQuot_of_tendsto_nhdsGT (U : OneParameterUnitaryGroup (H := H))
    (ψ : H) {η : H} (h : Tendsto (genDiffQuot U ψ) (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    Tendsto (genDiffQuot U ψ) (𝓝[≠] (0 : ℝ)) (𝓝 η) := by
  -- The transported quotient converges too, because `U (-t) → 1` strongly.
  have hmirror : Tendsto (fun t : ℝ => genDiffQuot U ψ (-t)) (𝓝[>] (0 : ℝ)) (𝓝 η) := by
    have hgroup : Tendsto (fun t : ℝ => U.U (-t) η) (𝓝[>] (0 : ℝ)) (𝓝 η) := by
      have hcont : Continuous fun t : ℝ => U.U (-t) η :=
        (U.strong_continuous η).comp continuous_neg
      have h0 : Tendsto (fun t : ℝ => U.U (-t) η) (𝓝 (0 : ℝ)) (𝓝 (U.U (-0 : ℝ) η)) :=
        hcont.tendsto 0
      rw [show U.U (-0 : ℝ) η = η by simp [U.identity]] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hsum : Tendsto (fun t : ℝ => ‖genDiffQuot U ψ t - η‖ + ‖U.U (-t) η - η‖)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h).add
        (tendsto_iff_norm_sub_tendsto_zero.mp hgroup)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hsum
    calc ‖genDiffQuot U ψ (-t) - η‖
        = ‖U.U (-t) (genDiffQuot U ψ t - η) + (U.U (-t) η - η)‖ := by
          rw [genDiffQuot_neg, map_sub]; congr 1; abel
      _ ≤ ‖U.U (-t) (genDiffQuot U ψ t - η)‖ + ‖U.U (-t) η - η‖ := norm_add_le _ _
      _ = ‖genDiffQuot U ψ t - η‖ + ‖U.U (-t) η - η‖ := by rw [norm_preserving]
  rw [← nhdsLT_sup_nhdsGT, tendsto_sup]
  refine ⟨(hmirror.comp tendsto_neg_nhdsLT).congr fun s => ?_, h⟩
  rw [Function.comp_apply, neg_neg]

/-- The converse of the Wave 3 generator bridge: the semigroup domain of a
unitary group is contained in the group's generator domain. -/
theorem mem_generatorDomain_of_mem_domain_toSemigroup (U : OneParameterUnitaryGroup H) {x : H}
    (hx : x ∈ (toSemigroup U).domain) : x ∈ generatorDomain U := by
  obtain ⟨y, hy⟩ := ((toSemigroup U).mem_domain_iff_tendsto x).mp hx
  -- Undo the factor `i` relating the two difference quotients.
  have hquot : Tendsto (genDiffQuot U x) (𝓝[>] (0 : ℝ)) (𝓝 ((-I) • y)) := by
    have hy' : Tendsto (fun t : ℝ => I • genDiffQuot U x t) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
      refine hy.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact realQuot_eq_smul_genDiffQuot U x ht
    have := hy'.const_smul (-I)
    refine this.congr ?_
    intro t
    rw [smul_smul]
    simp [Complex.I_mul_I]
  exact ⟨(-I) • y, tendsto_genDiffQuot_of_tendsto_nhdsGT U x hquot⟩

/-- On the semigroup domain, the semigroup generator is `i` times the group
generator — the Wave 3 bridge, now with the membership hypothesis on the
semigroup side. -/
theorem generator_toSemigroup' (U : OneParameterUnitaryGroup H) {x : H}
    (hx : x ∈ (toSemigroup U).domain) :
    (toSemigroup U).generator ⟨x, by rwa [Semigroups.StronglyContinuousSemigroup.generator_domain]⟩
      = I • (generator U ⟨x, mem_generatorDomain_of_mem_domain_toSemigroup U hx⟩) :=
  generator_toSemigroup U (mem_generatorDomain_of_mem_domain_toSemigroup U hx)

/-! ### The time-reversed generator -/

/-- The reversed group has the same generator domain. -/
theorem generatorDomain_reversedGroup (U : OneParameterUnitaryGroup (H := H)) :
    generatorDomain (reversedGroup U) = generatorDomain U := by
  ext ψ
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨-η, ?_⟩
    have := (hη.comp tendsto_neg_nhdsNE).neg
    refine this.congr ?_
    intro t
    rw [Function.comp_apply, genDiffQuot_reversedGroup, neg_neg, neg_neg]
  · rintro ⟨η, hη⟩
    refine ⟨-η, ?_⟩
    have := (hη.comp tendsto_neg_nhdsNE).neg
    refine this.congr ?_
    intro t
    rw [Function.comp_apply, genDiffQuot_reversedGroup]

/-- The generator of the time-reversed group is the negation of the generator. -/
theorem generator_reversedGroup (U : OneParameterUnitaryGroup (H := H)) {x : H}
    (hx : x ∈ (generator (reversedGroup U)).domain) (hx' : x ∈ (generator U).domain) :
    generator (reversedGroup U) ⟨x, hx⟩ = -generator U ⟨x, hx'⟩ := by
  refine tendsto_nhds_unique (generator_tendsto (reversedGroup U) ⟨x, hx⟩) ?_
  refine ((generator_tendsto U ⟨x, hx'⟩).comp tendsto_neg_nhdsNE).neg.congr fun t => ?_
  rw [Function.comp_apply, genDiffQuot_reversedGroup]

/-! ### Surjectivity of `A ± i` -/

/-- A unitary group restricted to `t ≥ 0` is a contraction semigroup. -/
theorem hasGrowthBound_toSemigroup (U : OneParameterUnitaryGroup H) :
    (toSemigroup U).HasGrowthBound 0 1 := by
  refine Semigroups.StronglyContinuousSemigroup.hasGrowthBound_of_bound le_rfl fun t ht => ?_
  rw [zero_mul, Real.exp_zero, mul_one]
  have ht' : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht
  rw [← ht', Semigroups.StronglyContinuousSemigroup.realOperator_coe]
  exact norm_toSemigroup_le U t.toNNReal

/-- The `λ = 1` Hille–Yosida resolvent of a unitary group, as a plain
existence statement about the *group* generator. -/
private theorem exists_generator_sub_I_smul (U : OneParameterUnitaryGroup H) (x : H) :
    ∃ ψ : (generator U).domain,
      (ψ : H) - I • (generator U ψ) = x := by
  set S := toSemigroup U with hS
  set R := S.resolvent (hasGrowthBound_toSemigroup U) 1 zero_lt_one x with hR
  have hmemS : R ∈ S.domain := S.resolvent_mem_domain _ 1 zero_lt_one x
  have hmem : R ∈ generatorDomain U := mem_generatorDomain_of_mem_domain_toSemigroup U hmemS
  refine ⟨⟨R, hmem⟩, ?_⟩
  have hid := S.resolventRightInv (hasGrowthBound_toSemigroup U) 1 zero_lt_one x
  rw [generator_toSemigroup U hmem, one_smul] at hid
  exact hid

/-- **`A + i` is surjective.** -/
theorem exists_generator_add_I (U : OneParameterUnitaryGroup H) (φ : H) :
    ∃ ψ : (generator U).domain, generator U ψ + I • (ψ : H) = φ := by
  obtain ⟨ψ, hψ⟩ := exists_generator_sub_I_smul U ((-I) • φ)
  refine ⟨ψ, ?_⟩
  -- Multiply `ψ - i A ψ = -i φ` through by `i`.
  have h2 : I • ((ψ : H) - I • (generator U ψ)) = I • ((-I) • φ) := by rw [hψ]
  simp only [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add,
    show I * -I = (1 : ℂ) by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul] at h2
  rw [← h2]
  abel

/-- **`A - i` is surjective.**  Read off from the time-reversed group. -/
theorem exists_generator_sub_I (U : OneParameterUnitaryGroup H) (φ : H) :
    ∃ ψ : (generator U).domain, generator U ψ - I • (ψ : H) = φ := by
  obtain ⟨⟨y, hy⟩, hψ⟩ := exists_generator_sub_I_smul (reversedGroup U) (I • φ)
  have hmem : y ∈ (generator U).domain := by
    have h0 : y ∈ generatorDomain (reversedGroup U) := hy
    rw [generatorDomain_reversedGroup] at h0
    exact h0
  refine ⟨⟨y, hmem⟩, ?_⟩
  rw [generator_reversedGroup U hy hmem] at hψ
  -- `hψ : y - i • (-(A y)) = i φ`, i.e. `y + i A y = i φ`; multiply through by `i`.
  dsimp only at hψ ⊢
  rw [smul_neg, sub_neg_eq_add] at hψ
  have h2 : I • (y + I • (generator U ⟨y, hmem⟩)) = I • (I • φ) := by rw [hψ]
  rw [smul_add, smul_smul, smul_smul, Complex.I_mul_I, neg_one_smul, neg_one_smul] at h2
  calc generator U ⟨y, hmem⟩ - I • y
      = -(I • y + -(generator U ⟨y, hmem⟩)) := by abel
    _ = -(-φ) := by rw [h2]
    _ = φ := neg_neg φ

/-! ### Stone's theorem -/

/-- **Stone's theorem, forward direction: the generator of a one-parameter
unitary group is self-adjoint.**

This is the statement every spectral consumer needs: `spectralPVM` and the Borel
functional calculus are built from a self-adjoint `LinearPMap`, and until now
nothing in the tree could produce one from a unitary group. -/
theorem isSelfAdjoint_generator (U : OneParameterUnitaryGroup H) :
    IsSelfAdjoint (generator U) :=
  isSelfAdjoint_of_surjective_addSub _ (generator_isFormalAdjoint U)
    (dense_domain_of_surjective_add_I _ (generator_isFormalAdjoint U)
      (exists_generator_add_I U))
    (exists_generator_add_I U) (exists_generator_sub_I U)

end OneParameterUnitaryGroup
end TauCeti

end
