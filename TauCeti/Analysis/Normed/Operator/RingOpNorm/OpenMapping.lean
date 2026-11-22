/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RingOpNorm
public import TauCeti.Topology.MetricSpace.Algebra
import TauCeti.Topology.Algebra.OpenMapping.BanachSchauder

/-!
# Quantitative mapping theorems over Tate rings

`TauCeti.HasZeroSequenceOfUnits.isOpenMap` proves Henkel's topological open mapping theorem for
surjective equivariant additive maps out of a complete first-countable uniform additive group into
a `T₀` Baire topological additive group over any scalar monoid admitting a zero sequence of units,
assuming continuity of the map at zero, continuity at zero in the scalar variable on the source, and
continuity of each fixed scalar action on the target.
`TauCeti.Topology.Algebra.OpenMapping.BanachSchauder` packages the qualitative Banach–Schauder
theorems (open mapping, continuous inverse, closed graph, and closed-range strictness) for
complete first-countable uniform modules, while `ContinuousLinearMap.equivRangeOfIsStrictMap` in
`TauCeti.Topology.Maps.Strict.Module` promotes an injective strict continuous linear map to a
continuous linear equivalence onto its range. When the scalar ring is a Tate normed ring
(`TauCeti.NormedRing.IsTate`), the powers of a multiplicative pseudo-uniformiser supply that zero
sequence of units, and exact scaling by integer powers of the pseudo-uniformiser turns topological
openness into quantitative linear preimage bounds.

This file develops those quantitative mapping theorems and their finite-free consequences over any
Tate seminormed ring `R` (no commutativity or ultrametric hypothesis is needed):

* **Quantitative preimage bounds from openness**: if `ϖ` is a multiplicative pseudo-uniformiser on
  `R` and the image of `ball (0 : M) R₀` under `f : M →ₗ[R] N` contains `ball (0 : N) δ` with
  `‖(ϖ.unit : R)‖ ^ k < δ`, then `f` is surjective onto the normed module `N` and every `y : N`
  admits a preimage `x` with `‖x‖ ≤ R₀ * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖y‖`
  (`TauCeti.NormedRing.PseudoUniformizer.exists_preimage_norm_le_of_ball_subset`). Consequently,
  any open linear map into a normed module over a Tate ring is surjective with a linear preimage
  bound (`LinearMap.exists_preimage_norm_le_of_isOpenMap`).
* **Quantitative Banach open mapping**: a surjective continuous linear map `f : M →L[R] N` from a
  complete seminormed module to a complete normed module over a Tate ring admits a constant `C > 0`
  such that every `y : N` lifts to `x : M` with `‖x‖ ≤ C * ‖y‖`
  (`ContinuousLinearMap.exists_preimage_norm_le_of_isTate`).
* **Closed-range preimage bounds and antilipschitz criteria**: a continuous linear map with closed
  range from a complete seminormed module to a complete normed module over a Tate ring admits linear
  preimage bounds on its range
  (`ContinuousLinearMap.exists_preimage_norm_le_of_isClosed_range_of_isTate`); if it is also
  injective, it is antilipschitz
  (`ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range_of_isTate`). When the source
  is a complete *normed* module, closedness of the range is equivalent to being antilipschitz
  (`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective_of_isTate`).
* **Quantitative finite spanning**: any finite family `v : ι → N` satisfying
  `Submodule.span R (Set.range v) = ⊤` in a complete normed module over a complete Tate ring admits
  a constant `C > 0` representing every `y : N` as `∑ i, c i • v i` with `‖c‖ ≤ C * ‖y‖`
  (`TauCeti.exists_linearCombination_eq_and_norm_le`).

The antilipschitz closed-range characterization is adapted from
`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective` in
`Mathlib/Analysis/Normed/Operator/Banach.lean`.

## References

* K. Buzzard, *The Analytic Continuation of p-adic Modular Forms* (eigenbook), §2.
* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  arXiv:1407.5647.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §8.
-/

public section

open Filter Function Metric Set Topology
open scoped NNReal TauCeti.RingOpNorm

namespace TauCeti.NormedRing.PseudoUniformizer

variable {R M N : Type*} [SeminormedRing R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- **Quantitative preimage bound from ball containment.** If `ϖ` is a multiplicative
pseudo-uniformiser on `R`, `‖(ϖ.unit : R)‖ ^ k < δ`, and `ball (0 : N) δ ⊆ f '' ball (0 : M) R₀`,
then every `y : N` admits `x : M` with `f x = y` and
`‖x‖ ≤ R₀ * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖y‖`. -/
theorem exists_preimage_norm_le_of_ball_subset (ϖ : PseudoUniformizer R) (f : M →ₗ[R] N)
    {δ R₀ : ℝ} (k : ℤ) (hδ : ‖(ϖ.unit : R)‖ ^ k < δ)
    (hball : ball (0 : N) δ ⊆ f '' ball (0 : M) R₀) (y : N) :
    ∃ x : M, f x = y ∧ ‖x‖ ≤ R₀ * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, map_zero f, by simp⟩
  obtain ⟨n, hn, hscale⟩ := ϖ.exists_zpow_mul_norm_lt (norm_ne_zero_iff.mpr hy0) k hδ
  have hmem : ((ϖ.unit ^ n : Rˣ) : R) • y ∈ ball (0 : N) δ := by
    rwa [mem_ball_zero_iff, ϖ.norm_zpow_smul]
  obtain ⟨x₀, hx₀, hfx₀⟩ := hball hmem
  rw [mem_ball_zero_iff] at hx₀
  have hR₀ : 0 ≤ R₀ := (norm_nonneg x₀).trans hx₀.le
  refine ⟨((ϖ.unit ^ (-n) : Rˣ) : R) • x₀, ?_, ?_⟩
  · rw [map_smul, hfx₀]
    simp [← mul_smul, ← Units.val_mul]
  · rw [ϖ.norm_zpow_smul, zpow_neg]
    calc (‖(ϖ.unit : R)‖ ^ n)⁻¹ * ‖x₀‖
        ≤ (‖(ϖ.unit : R)‖ ^ n)⁻¹ * R₀ :=
          mul_le_mul_of_nonneg_left hx₀.le (inv_nonneg.mpr (zpow_nonneg ϖ.norm_pos.le _))
      _ ≤ ((‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖y‖) * R₀ :=
          mul_le_mul_of_nonneg_right hscale hR₀
      _ = R₀ * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖y‖ := by ring

end TauCeti.NormedRing.PseudoUniformizer

namespace LinearMap

section Tate

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

/-- If the image of the unit ball under `f : M →ₗ[R] N` is a neighbourhood of `0` in a normed
module `N` over a Tate ring `R`, then `f` is surjective and admits a constant `C > 0` such that
every `y : N` lifts to `x : M` with `‖x‖ ≤ C * ‖y‖`. -/
theorem exists_preimage_norm_le_of_nhds_zero (f : M →ₗ[R] N)
    (hnhds : f '' ball (0 : M) 1 ∈ 𝓝 (0 : N)) :
    ∃ C > 0, ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨ϖ⟩ := TauCeti.NormedRing.IsTate.nonempty_pseudoUniformizer (R := R)
  have hr0 : 0 < ‖(ϖ.unit : R)‖ := ϖ.norm_pos
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(ϖ.unit : R)‖ ^ k < δ :=
    exists_pow_lt_of_lt_one hδ ϖ.norm_lt_one
  refine ⟨1 * (‖(ϖ.unit : R)‖ ^ ((k : ℤ) + 1))⁻¹, by positivity, fun y ↦ ?_⟩
  exact ϖ.exists_preimage_norm_le_of_ball_subset f k (by simpa using hk) hball y

/-- Any open linear map into a normed module over a Tate ring is surjective and admits a linear
preimage bound `‖x‖ ≤ C * ‖y‖` with `C > 0`. -/
theorem exists_preimage_norm_le_of_isOpenMap (f : M →ₗ[R] N) (hopen : IsOpenMap f) :
    ∃ C > 0, ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  f.exists_preimage_norm_le_of_nhds_zero <|
    (hopen _ isOpen_ball).mem_nhds ⟨0, mem_ball_self one_pos, map_zero f⟩

end Tate

section CompleteSource

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- **Quantitative Open Mapping Theorem** for linear maps over a Tate ring: every surjective
continuous linear map from a complete seminormed module to a complete normed module admits a
constant `C > 0` such that every `y : N` lifts to `x : M` with `‖x‖ ≤ C * ‖y‖`. -/
theorem exists_preimage_norm_le_of_surjective (f : M →ₗ[R] N) (hf : Continuous f)
    (hsurj : Surjective f) :
    ∃ C > 0, ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  f.exists_preimage_norm_le_of_isOpenMap (f.isOpenMap_of_complete hsurj hf.continuousAt)

end CompleteSource

end LinearMap

namespace ContinuousLinearMap

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- **Quantitative Open Mapping Theorem**: for a surjective continuous linear map `f : M →L[R] N`
from a complete seminormed module to a complete normed module over a Tate ring, there exists `C > 0`
such that every `y : N` lifts to `x : M` with `‖x‖ ≤ C * ‖y‖`. -/
theorem exists_preimage_norm_le_of_isTate (f : M →L[R] N) (hsurj : Surjective f) :
    ∃ C > 0, ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  f.toLinearMap.exists_preimage_norm_le_of_surjective f.continuous hsurj

/-- **Quantitative preimage bound for closed-range operators**: if `f : M →L[R] N` from a complete
seminormed module to a complete normed module over a Tate ring has closed range, there exists
`C > 0` such that every `y ∈ Set.range f` lifts to `x : M` with `f x = y` and `‖x‖ ≤ C * ‖y‖`. -/
theorem exists_preimage_norm_le_of_isClosed_range_of_isTate (f : M →L[R] N)
    (hclosed : IsClosed (Set.range f)) :
    ∃ C > 0, ∀ y ∈ Set.range f, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  have hclosed' : IsClosed (f.range : Set N) := by rwa [LinearMap.coe_range]
  have : CompleteSpace f.range := hclosed'.completeSpace_coe
  obtain ⟨C, hC, hlift⟩ :=
    f.rangeRestrict.exists_preimage_norm_le_of_isTate f.toLinearMap.surjective_rangeRestrict
  refine ⟨C, hC, fun y hy ↦ ?_⟩
  obtain ⟨x, hx, hnorm⟩ := hlift ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx, hnorm⟩

/-- If `f : M →L[R] N` from a complete seminormed module to a complete normed module over a Tate
ring is injective and has closed range, then `‖x‖ ≤ C * ‖f x‖` for some `C > 0`. -/
theorem exists_norm_le_of_injective_of_isClosed_range_of_isTate (f : M →L[R] N) (hinj : Injective f)
    (hclosed : IsClosed (Set.range f)) :
    ∃ C > 0, ∀ x : M, ‖x‖ ≤ C * ‖f x‖ := by
  obtain ⟨C, hC, hlift⟩ := f.exists_preimage_norm_le_of_isClosed_range_of_isTate hclosed
  refine ⟨C, hC, fun x ↦ ?_⟩
  obtain ⟨x', hx', hnorm⟩ := hlift (f x) ⟨x, rfl⟩
  rwa [hinj hx'] at hnorm

/-- If `f : M →L[R] N` from a complete seminormed module to a complete normed module over a Tate
ring is injective and has closed range, then `f` is `AntilipschitzWith K` for some `K ≠ 0`. -/
theorem antilipschitz_of_injective_of_isClosed_range_of_isTate (f : M →L[R] N)
    (hinj : Injective f) (hclosed : IsClosed (Set.range f)) :
    ∃ K : ℝ≥0, K ≠ 0 ∧ AntilipschitzWith K f := by
  obtain ⟨C, hC, hbound⟩ := f.exists_norm_le_of_injective_of_isClosed_range_of_isTate hinj hclosed
  refine ⟨⟨C, hC.le⟩, NNReal.coe_ne_zero.mp hC.ne', ?_⟩
  exact AddMonoidHomClass.antilipschitz_of_bound f hbound

/-- For an injective continuous linear map `f : M' →L[R] N` from a complete normed module to a
complete normed module over a Tate ring, the range of `f` is closed if and only if `f` is
antilipschitz. -/
theorem isClosed_range_iff_antilipschitz_of_injective_of_isTate
    {M' : Type*} [NormedAddCommGroup M'] [CompleteSpace M']
    [Module R M'] [IsBoundedSMul R M'] (f : M' →L[R] N) (hinj : Injective f) :
    IsClosed (Set.range f) ↔ ∃ K : ℝ≥0, AntilipschitzWith K f :=
  ⟨fun hclosed ↦
    let ⟨K, _, hK⟩ := f.antilipschitz_of_injective_of_isClosed_range_of_isTate hinj hclosed
    ⟨K, hK⟩,
    fun ⟨_, hK⟩ ↦ hK.isClosed_range f.uniformContinuous⟩

end ContinuousLinearMap

/-! ### Quantitative finite spanning -/

namespace TauCeti

variable {R N ι : Type*} [Fintype ι] [SeminormedRing R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- **Quantitative finite spanning over a complete Tate ring.**
If a finite family `v : ι → N` spans a complete normed module `N` over a complete Tate ring `R`,
then there exists `C > 0` such that every `y : N` can be written as `∑ i, c i • v i` with
`‖c‖ ≤ C * ‖y‖` (and hence `‖c i‖ ≤ C * ‖y‖` for every `i`). -/
theorem exists_linearCombination_eq_and_norm_le (v : ι → N)
    (hspan : Submodule.span R (Set.range v) = ⊤) :
    ∃ C > 0, ∀ y : N, ∃ c : ι → R, (∑ i : ι, c i • v i) = y ∧ ‖c‖ ≤ C * ‖y‖ := by
  have hsurj : Surjective (Fintype.linearCombination R v) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).mp hspan
  exact (Fintype.linearCombination R v).exists_preimage_norm_le_of_surjective
    (Fintype.linearCombination R v).continuous_on_pi hsurj

end TauCeti
