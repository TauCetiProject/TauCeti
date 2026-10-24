/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.CountableType
public import TauCeti.Analysis.Normed.Module.Bases.PotentiallyONable
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Model spaces from `t`-orthogonal bases

A `t`-orthogonal basis whose vector norms are bounded above and bounded away from zero gives
continuous linear coordinates in `C₀(I, K)`. The inverse coordinate map is the unconditional
sum against the chosen basis. Every `t`-orthogonal basis over a nontrivially normed field can be
rescaled to satisfy these bounds, using powers of a fixed scalar of norm strictly between zero
and one.

Consequently every complete ultrametric space of countable type over a complete nontrivially
normed field is potentially orthonormalisable. In infinite dimension its model is `C₀(ℕ, K)`.
No discreteness assumption on the value group is needed. These coordinates allow the lifting
property of model spaces to be applied to spaces of countable type.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §10.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty NNReal ENNReal

namespace TauCeti

universe u v

variable {K : Type v} [NontriviallyNormedField K] [CompleteSpace K]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
  {I : Type*} {t : ℝ≥0} {e : I → E}

namespace IsTOrthogonalBasis

section Bounded

variable [TopologicalSpace I] [DiscreteTopology I]
  (he : IsTOrthogonalBasis K t e) (ht : 0 < t)
  (hb : Memℓp e ∞) {δ : ℝ} (hδ : 0 < δ) (hl : ∀ i, δ ≤ ‖e i‖)

include he ht hδ hl in
/-- For a basis with vector norms bounded away from zero, every vector has coefficients
vanishing at infinity. -/
theorem exists_zeroAtInfty_hasSum (x : E) :
    ∃ a : C₀(I, K), HasSum (fun i ↦ a i • e i) x := by
  let a := fun i ↦ (he.toUnconditionalSchauderBasis ht).coord i x
  have hdecay : Tendsto a cofinite (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    refine squeeze_zero (fun i ↦ norm_nonneg (a i))
      (g := fun i ↦ δ⁻¹ * (‖a i‖ * ‖e i‖)) (fun i ↦ ?_) ?_
    · rw [← div_eq_inv_mul, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left (hl i) (norm_nonneg _)
    · simpa only [mul_zero] using (he.tendsto_norm_coord_mul_norm ht x).const_mul δ⁻¹
  exact ⟨mkOfDiscrete a hdecay, by
    simpa only [coe_mkOfDiscrete, coe_toUnconditionalSchauderBasis] using
      (he.toUnconditionalSchauderBasis ht).expansion x⟩

variable [CompleteSpace E]

include he ht hδ hl in
/-- The linear combination map of a bounded `t`-orthogonal basis bounded away from zero is
bijective. -/
theorem linearCombination_bijective : Function.Bijective (linearCombination K ⟨e, hb⟩) := by
  constructor
  · refine (linearCombination K ⟨e, hb⟩).toLinearMap.ker_eq_bot.1 ?_
    rw [LinearMap.ker_eq_bot']
    intro a ha
    have hc := he.eq_of_hasSum ht (b := 0)
      (ha ▸ hasSum_linearCombination (R := K) ⟨e, hb⟩ a) (by simp)
    exact ZeroAtInftyContinuousMap.ext (fun i ↦ by simpa using congrFun hc i)
  · intro x
    obtain ⟨a, ha⟩ := he.exists_zeroAtInfty_hasSum ht hδ hl x
    exact ⟨a, (hasSum_linearCombination (R := K) ⟨e, hb⟩ a).unique ha⟩

/-- Continuous linear coordinates for a bounded `t`-orthogonal basis whose vector norms are
bounded away from zero. The inverse is summation against the specified basis. -/
noncomputable def equivZeroAtInfty : E ≃L[K] C₀(I, K) :=
  (ContinuousLinearEquiv.ofBijective (linearCombination K ⟨e, hb⟩)
    (LinearMap.ker_eq_bot.2 (he.linearCombination_bijective ht hb hδ hl).1)
    (LinearMap.range_eq_top.2 (he.linearCombination_bijective ht hb hδ hl).2)).symm

/-- The inverse coordinate map is the linear combination map of the chosen basis. -/
@[simp]
theorem equivZeroAtInfty_symm_apply (a : C₀(I, K)) :
    (he.equivZeroAtInfty ht hb hδ hl).symm a = ∑' i, a i • e i := by
  simp only [equivZeroAtInfty, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.coeFn_ofBijective, linearCombination_apply]

/-- Coordinates reconstruct the vector by unconditional summation. -/
theorem hasSum_equivZeroAtInfty (x : E) :
    HasSum (fun i ↦ he.equivZeroAtInfty ht hb hδ hl x i • e i) x := by
  simpa only [← equivZeroAtInfty_symm_apply he ht hb hδ hl,
    ContinuousLinearEquiv.symm_apply_apply] using
    (summable_smul (he.equivZeroAtInfty ht hb hδ hl x) ⟨e, hb⟩).hasSum

/-- The model-space coordinates agree with those of the associated unconditional Schauder basis. -/
theorem equivZeroAtInfty_apply (x : E) (i : I) :
    he.equivZeroAtInfty ht hb hδ hl x i = (he.toUnconditionalSchauderBasis ht).coord i x :=
  (he.coord_eq_of_hasSum ht (he.hasSum_equivZeroAtInfty ht hb hδ hl x) i).symm

/-- The norm of the coordinate vector is controlled by the orthogonality constant and the
uniform lower bound on the basis-vector norms. -/
theorem norm_equivZeroAtInfty_apply_le (x : E) :
    ‖he.equivZeroAtInfty ht hb hδ hl x‖ ≤ ((t : ℝ) * δ)⁻¹ * ‖x‖ := by
  have htd : 0 < (t : ℝ) * δ := mul_pos (by exact_mod_cast ht) hδ
  refine (norm_le (by positivity)).2 fun i ↦ ?_
  rw [← div_eq_inv_mul, le_div_iff₀ htd]
  rw [equivZeroAtInfty_apply]
  calc
    ‖(he.toUnconditionalSchauderBasis ht).coord i x‖ * ((t : ℝ) * δ) =
        (t : ℝ) * ‖(he.toUnconditionalSchauderBasis ht).coord i x‖ * δ := by ring
    _ ≤ (t : ℝ) * ‖(he.toUnconditionalSchauderBasis ht).coord i x‖ * ‖e i‖ :=
      mul_le_mul_of_nonneg_left (hl i) (by positivity)
    _ ≤ ‖x‖ := he.mul_norm_coord_mul_norm_le ht i x

/-- The coordinate isomorphism sends each basis vector to the corresponding unit vector. -/
@[simp]
theorem equivZeroAtInfty_apply_basis [DecidableEq I] (i : I) :
    he.equivZeroAtInfty ht hb hδ hl (e i) = single i 1 := by
  apply (he.equivZeroAtInfty ht hb hδ hl).symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply, equivZeroAtInfty_symm_apply]
  simpa only [linearCombination_apply, one_smul] using
    (linearCombination_single (R := K) ⟨e, hb⟩ i 1).symm

/-- The coordinates are the coefficients of every unconditional expansion in the basis. -/
theorem equivZeroAtInfty_apply_eq_of_hasSum {a : I → K} {x : E}
    (ha : HasSum (fun i ↦ a i • e i) x) (i : I) :
    he.equivZeroAtInfty ht hb hδ hl x i = a i := by
  rw [equivZeroAtInfty_apply, he.coord_eq_of_hasSum ht ha]

end Bounded

/-- Every complete ultrametric space with a `t`-orthogonal basis, `t > 0`, is continuously
linearly equivalent to the model space with the same index type. -/
theorem nonempty_equivZeroAtInfty [CompleteSpace E] [TopologicalSpace I] [DiscreteTopology I]
    (he : IsTOrthogonalBasis K t e) (ht : 0 < t) : Nonempty (E ≃L[K] C₀(I, K)) := by
  obtain ⟨ϖ⟩ := NormedRing.IsTate.nonempty_pseudoUniformizer (R := K)
  -- Powers of a fixed small scalar put all basis vectors in the same norm shell.
  choose n hn using fun i ↦
    ExistsUnique.exists (ϖ.existsUnique_norm_zpow_smul_mem_Ioc (norm_ne_zero_iff.2 (he.ne_zero i)))
  let a (i : I) : Kˣ := ϖ.unit ^ n i
  let f (i : I) : E := (a i : K) • e i
  have hf : IsTOrthogonalBasis K t f :=
    { isTOrthogonalFamily := isTOrthogonalFamily_def.2 fun s b ↦ by
        simpa only [f, mul_smul] using
          isTOrthogonalFamily_def.1 he.isTOrthogonalFamily s (fun i ↦ b i * (a i : K))
      ne_zero := fun i ↦ (smul_ne_zero_iff_ne (a i)).2 (he.ne_zero i)
      dense_span := by
        simpa only [f, Submodule.span_range_eq_iSup,
          Submodule.span_singleton_smul_eq (a _).isUnit] using he.dense_span }
  have hb : Memℓp f ∞ := memℓp_infty ⟨1, by rintro _ ⟨i, rfl⟩; exact (hn i).2⟩
  exact ⟨hf.equivZeroAtInfty ht hb ϖ.norm_pos (fun i ↦ (hn i).1.le)⟩

end IsTOrthogonalBasis

/-- An infinite-dimensional ultrametric Banach space of countable type (some sequence has dense
span) over a complete nontrivially normed field is continuously linearly equivalent to
`C₀(ℕ, K)`. -/
theorem nonempty_continuousLinearEquiv_zeroAtInfty_nat_of_dense_span [CompleteSpace E]
    (hE : ¬FiniteDimensional K E) {v : ℕ → E}
    (hv : Dense (Submodule.span K (Set.range v) : Set E)) : Nonempty (E ≃L[K] C₀(ℕ, K)) := by
  obtain ⟨e, he⟩ := exists_isTOrthogonalBasis_nat_of_dense_span hE hv
    (t := (1 / 2 : ℝ≥0)) (by norm_num)
  exact he.nonempty_equivZeroAtInfty (by norm_num)

/-- Every ultrametric Banach space of countable type over a complete nontrivially normed field is
potentially orthonormalisable, including finite-dimensional and zero spaces. -/
theorem isPotentiallyONable_of_dense_span [CompleteSpace E] {v : ℕ → E}
    (hv : Dense (Submodule.span K (Set.range v) : Set E)) : IsPotentiallyONable K E := by
  obtain ⟨S, e, he⟩ := exists_isTOrthogonalBasis_of_dense_span hv
    (t := (1 / 2 : ℝ≥0)) (by norm_num)
  let I := ULift.{u} S
  let : TopologicalSpace I := ⊥
  have : DiscreteTopology I := ⟨rfl⟩
  apply (isPotentiallyONable_def K E).2
  exact ⟨I, inferInstance, inferInstance,
    (he.comp_equiv Equiv.ulift).nonempty_equivZeroAtInfty (by norm_num)⟩

end TauCeti
