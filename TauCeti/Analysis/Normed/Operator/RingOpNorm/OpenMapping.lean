/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Module
public import TauCeti.Analysis.Normed.Group.Submodule
public import TauCeti.Analysis.Normed.Operator.RingOpNorm
public import TauCeti.Topology.MetricSpace.Ultra.Prod
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Ultra.Pi
import TauCeti.Topology.Algebra.OpenMapping.Henkel

/-!
# Quantitative mapping theorems over Tate rings

`TauCeti.HasZeroSequenceOfUnits.isOpenMap` proves Henkel's topological open mapping theorem for
surjective equivariant additive maps out of a complete first-countable non-archimedean group into a
Baire target over any scalar ring admitting a zero sequence of units. When the scalar ring is a
Tate normed ring (`TauCeti.NormedRing.IsTate`), the powers of a multiplicative pseudo-uniformiser
supply that zero sequence of units, and exact scaling by integer powers of the pseudo-uniformiser
turns topological openness into quantitative linear preimage bounds.

This file develops those quantitative mapping theorems and their finite-free consequences over any
Tate seminormed ring `R` (no commutativity or ultrametric hypothesis on `R` is needed unless `R^n`
itself serves as the ultrametric domain):

* **Quantitative preimage bounds from openness**: if `ϖ` is a multiplicative pseudo-uniformiser on
  `R` and the image of `ball (0 : M) R₀` under `f : M →ₗ[R] N` contains `ball (0 : N) δ` with
  `‖(ϖ.unit : R)‖ ^ k < δ`, then `f` is surjective onto the normed module `N` and every `y : N`
  admits a preimage `x` with `‖x‖ ≤ R₀ * (‖(ϖ.unit : R)‖ ^ (k + 1))⁻¹ * ‖y‖`
  (`TauCeti.NormedRing.PseudoUniformizer.exists_preimage_norm_le_of_ball_subset`). Consequently,
  any open linear map into a normed module over a Tate ring is surjective with a linear preimage
  bound (`LinearMap.exists_preimage_norm_le_of_isOpenMap`).
* **Quantitative Banach open mapping**: a surjective continuous linear map `f : M →L[R] N` from a
  complete ultrametric seminormed module to a complete normed module over a Tate ring is an open
  quotient map and admits a constant `C > 0` such that every `y : N` lifts to `x : M` with
  `‖x‖ ≤ C * ‖y‖` (`ContinuousLinearMap.exists_preimage_norm_le_of_isTate`).
* **Closed-range strictness and antilipschitz criteria**: a continuous linear map with closed range
  from a complete ultrametric seminormed module to a complete normed module over a Tate ring
  is strict and admits linear preimage bounds on its range; if it is also injective, it is
  antilipschitz and induces a `ContinuousLinearEquiv` onto its range
  (`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective_of_isTate`,
  `ContinuousLinearMap.equivRangeOfIsTate`).
* **Bounded inverse and closed graph theorems** packaged for `ContinuousLinearEquiv` and
  `ContinuousLinearMap` over Tate rings (`LinearEquiv.toContinuousLinearEquivOfContinuousOfIsTate`,
  `ContinuousLinearEquiv.ofBijectiveOfIsTate`, `ContinuousLinearMap.isUnit_iff_bijective_of_isTate`,
  `LinearMap.continuous_of_isClosed_graph_of_isTate`,
  `LinearMap.continuous_of_seq_closed_graph_of_isTate`,
  `ContinuousLinearMap.ofIsClosedGraphOfIsTate`, and
  `ContinuousLinearMap.ofSeqClosedGraphOfIsTate`).
* **Quantitative finite spanning**: any finite family `v : ι → N` satisfying
  `Submodule.span R (Set.range v) = ⊤` in a complete normed module over a complete
  ultrametric Tate ring admits a constant `C > 0`
  representing every `y : N` as `∑ i, c i • v i` with `‖c‖ ≤ C * ‖y‖`
  (`TauCeti.exists_linearCombination_eq_and_norm_le`).

The API and the bounded-inverse, range-equivalence, bijective-map, unit and closed-graph
packaging are adapted from `Mathlib/Analysis/Normed/Operator/Banach.lean`, in particular
`LinearEquiv.continuous_symm`, `LinearEquiv.toContinuousLinearEquivOfContinuous`,
`ContinuousLinearMap.equivRange`,
`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective`,
`ContinuousLinearEquiv.ofBijective`, `ContinuousLinearMap.isUnit_iff_bijective`,
`ContinuousLinearMap.ofIsClosedGraph` and `ContinuousLinearMap.ofSeqClosedGraph`.

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

section UltrametricSource

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- **Open Mapping Theorem for normed modules over a Tate ring.**
A surjective continuous linear map from a complete ultrametric seminormed module to a complete
normed module over a Tate ring is an open map. -/
theorem isOpenMap_of_isTate (f : M →ₗ[R] N) (hf : Continuous f) (hsurj : Surjective f) :
    IsOpenMap f :=
  TauCeti.HasZeroSequenceOfUnits.isOpenMap f hsurj hf.continuousAt
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **Quantitative Open Mapping Theorem** for linear maps over a Tate ring: every surjective
continuous linear map from a complete ultrametric seminormed module to a complete normed module
admits a constant `C > 0` such that every `y : N` lifts to `x : M` with `‖x‖ ≤ C * ‖y‖`. -/
theorem exists_preimage_norm_le_of_surjective (f : M →ₗ[R] N) (hf : Continuous f)
    (hsurj : Surjective f) :
    ∃ C > 0, ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  f.exists_preimage_norm_le_of_isOpenMap (f.isOpenMap_of_isTate hf hsurj)

end UltrametricSource

end LinearMap

namespace LinearEquiv

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- **Bounded Inverse Theorem** for linear equivalences over a Tate ring: the inverse of a
continuous linear equivalence from a complete ultrametric seminormed module to a complete normed
module is continuous. -/
theorem continuous_symm_of_isTate (e : M ≃ₗ[R] N) (he : Continuous e) :
    Continuous e.symm :=
  continuous_def.mpr fun s hs ↦
    e.toEquiv.image_eq_preimage_symm s ▸ e.toLinearMap.isOpenMap_of_isTate he e.surjective s hs

/-- Promote a continuous linear equivalence `e : M ≃ₗ[R] N` from a complete ultrametric seminormed
module to a complete normed module over a Tate ring to a bundled `ContinuousLinearEquiv`. -/
def toContinuousLinearEquivOfContinuousOfIsTate (e : M ≃ₗ[R] N) (he : Continuous e) :
    M ≃L[R] N where
  toLinearEquiv := e
  continuous_toFun := he
  continuous_invFun := e.continuous_symm_of_isTate he

@[simp]
theorem toLinearEquiv_toContinuousLinearEquivOfContinuousOfIsTate (e : M ≃ₗ[R] N)
    (he : Continuous e) :
    (e.toContinuousLinearEquivOfContinuousOfIsTate he).toLinearEquiv = e :=
  (rfl)

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuousOfIsTate (e : M ≃ₗ[R] N) (he : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuousOfIsTate he) = e :=
  (rfl)

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuousOfIsTate_symm (e : M ≃ₗ[R] N)
    (he : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuousOfIsTate he).symm = e.symm :=
  (rfl)

@[simp]
theorem toContinuousLinearEquivOfContinuousOfIsTate_apply (e : M ≃ₗ[R] N) (he : Continuous e)
    (x : M) :
    e.toContinuousLinearEquivOfContinuousOfIsTate he x = e x :=
  (rfl)

@[simp]
theorem toContinuousLinearEquivOfContinuousOfIsTate_symm_apply (e : M ≃ₗ[R] N) (he : Continuous e)
    (y : N) :
    (e.toContinuousLinearEquivOfContinuousOfIsTate he).symm y = e.symm y :=
  (rfl)

end LinearEquiv

namespace ContinuousLinearEquiv

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- **Bounded Inverse Theorem**: a bijective continuous linear map from a complete ultrametric
seminormed module to a complete normed module over a Tate ring is a continuous linear
equivalence. -/
noncomputable def ofBijectiveOfIsTate (f : M →L[R] N) (hf : Bijective f) :
    M ≃L[R] N :=
  (LinearEquiv.ofBijective f.toLinearMap hf).toContinuousLinearEquivOfContinuousOfIsTate
    f.continuous

@[simp]
theorem coeFn_ofBijectiveOfIsTate (f : M →L[R] N) (hf : Bijective f) :
    ⇑(ofBijectiveOfIsTate f hf) = f :=
  (rfl)

@[simp]
theorem coe_ofBijectiveOfIsTate (f : M →L[R] N) (hf : Bijective f) :
    (ofBijectiveOfIsTate f hf : M →L[R] N) = f := by
  ext
  rfl

@[simp]
theorem ofBijectiveOfIsTate_apply (f : M →L[R] N) (hf : Bijective f) (x : M) :
    ofBijectiveOfIsTate f hf x = f x :=
  (rfl)

@[simp]
theorem ofBijectiveOfIsTate_symm_apply_apply (f : M →L[R] N) (hf : Bijective f) (x : M) :
    (ofBijectiveOfIsTate f hf).symm (f x) = x :=
  (ofBijectiveOfIsTate f hf).symm_apply_apply x

@[simp]
theorem ofBijectiveOfIsTate_apply_symm_apply (f : M →L[R] N) (hf : Bijective f) (y : N) :
    f ((ofBijectiveOfIsTate f hf).symm y) = y :=
  (ofBijectiveOfIsTate f hf).apply_symm_apply y

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- A surjective continuous linear map from a complete ultrametric seminormed module to a complete
normed module over a Tate ring is an open map. -/
theorem isOpenMap_of_isTate (f : M →L[R] N) (hsurj : Surjective f) : IsOpenMap f :=
  f.toLinearMap.isOpenMap_of_isTate f.continuous hsurj

/-- A surjective continuous linear map from a complete ultrametric seminormed module to a complete
normed module over a Tate ring is a quotient map. -/
theorem isQuotientMap_of_isTate (f : M →L[R] N) (hsurj : Surjective f) : IsQuotientMap f :=
  TauCeti.HasZeroSequenceOfUnits.isQuotientMap f hsurj f.continuous.continuousAt
    fun _ ↦ (continuous_id.smul continuous_const).continuousAt

/-- **Quantitative Open Mapping Theorem**: for a surjective continuous linear map `f : M →L[R] N`
from a complete ultrametric seminormed module to a complete normed module over a Tate ring, there
exists `C > 0` such that every `y : N` lifts to `x : M` with `‖x‖ ≤ C * ‖y‖`. -/
theorem exists_preimage_norm_le_of_isTate (f : M →L[R] N) (hsurj : Surjective f) :
    ∃ C > 0, ∀ y : N, ∃ x : M, f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  f.toLinearMap.exists_preimage_norm_le_of_surjective f.continuous hsurj

/-- A continuous linear map `f : M →L[R] N` with closed range from a complete ultrametric
seminormed module to a complete normed module over a Tate ring is a strict morphism
(`Topology.IsStrictMap`). -/
theorem isStrictMap_of_isClosed_range_of_isTate (f : M →L[R] N)
    (hclosed : IsClosed (Set.range f)) : Topology.IsStrictMap f :=
  TauCeti.HasZeroSequenceOfUnits.isStrictMap_of_isClosed_range f.toLinearMap
    f.continuous.continuousAt
    (fun _ ↦ (continuous_id.smul continuous_const).continuousAt)
    (by rwa [LinearMap.coe_range])

/-- A continuous linear map `f : M →L[R] N` with closed range from a complete ultrametric
seminormed module to a complete normed module over a Tate ring is open onto its range. -/
theorem isOpenMap_rangeRestrict_of_isClosed_range_of_isTate (f : M →L[R] N)
    (hclosed : IsClosed (Set.range f)) : IsOpenMap f.rangeRestrict :=
  (LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp
    (f.isStrictMap_of_isClosed_range_of_isTate hclosed)).isOpenMap

/-- **Quantitative preimage bound for closed-range operators**: if `f : M →L[R] N` from a complete
ultrametric seminormed module to a complete normed module over a Tate ring has closed range,
there exists `C > 0` such that every `y ∈ Set.range f` lifts to `x : M` with `f x = y` and
`‖x‖ ≤ C * ‖y‖`. -/
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

/-- If `f : M →L[R] N` from a complete ultrametric seminormed module to a complete normed module
over a Tate ring is injective and has closed range, then `‖x‖ ≤ C * ‖f x‖` for some `C > 0`. -/
theorem exists_norm_le_of_injective_of_isClosed_range_of_isTate (f : M →L[R] N) (hinj : Injective f)
    (hclosed : IsClosed (Set.range f)) :
    ∃ C > 0, ∀ x : M, ‖x‖ ≤ C * ‖f x‖ := by
  obtain ⟨C, hC, hlift⟩ := f.exists_preimage_norm_le_of_isClosed_range_of_isTate hclosed
  refine ⟨C, hC, fun x ↦ ?_⟩
  obtain ⟨x', hx', hnorm⟩ := hlift (f x) ⟨x, rfl⟩
  rwa [hinj hx'] at hnorm

/-- If `f : M →L[R] N` from a complete ultrametric seminormed module to a complete normed module
over a Tate ring is injective and has closed range, then `f` is `AntilipschitzWith K` for some
`K ≠ 0`. -/
theorem antilipschitz_of_injective_of_isClosed_range_of_isTate (f : M →L[R] N)
    (hinj : Injective f) (hclosed : IsClosed (Set.range f)) :
    ∃ K : ℝ≥0, K ≠ 0 ∧ AntilipschitzWith K f := by
  obtain ⟨C, hC, hbound⟩ := f.exists_norm_le_of_injective_of_isClosed_range_of_isTate hinj hclosed
  refine ⟨⟨C, hC.le⟩, NNReal.coe_ne_zero.mp hC.ne', ?_⟩
  exact AddMonoidHomClass.antilipschitz_of_bound f hbound

/-- For an injective continuous linear map `f : M' →L[R] N` from a complete ultrametric normed
module to a complete normed module over a Tate ring, the range of `f` is closed if and only if `f`
is antilipschitz. -/
theorem isClosed_range_iff_antilipschitz_of_injective_of_isTate
    {M' : Type*} [NormedAddCommGroup M'] [IsUltrametricDist M'] [CompleteSpace M']
    [Module R M'] [IsBoundedSMul R M'] (f : M' →L[R] N) (hinj : Injective f) :
    IsClosed (Set.range f) ↔ ∃ K : ℝ≥0, AntilipschitzWith K f :=
  ⟨fun hclosed ↦
    let ⟨K, _, hK⟩ := f.antilipschitz_of_injective_of_isClosed_range_of_isTate hinj hclosed
    ⟨K, hK⟩,
    fun ⟨_, hK⟩ ↦ hK.isClosed_range f.uniformContinuous⟩

/-- An injective continuous linear map with closed range from a complete ultrametric seminormed
module to a complete normed module over a Tate ring induces a continuous linear equivalence onto
its range. -/
noncomputable def equivRangeOfIsTate (f : M →L[R] N) (hinj : Injective f)
    (hclosed : IsClosed (Set.range f)) :
    M ≃L[R] f.range := by
  have hclosed' : IsClosed (f.range : Set N) := by rwa [LinearMap.coe_range]
  haveI : CompleteSpace f.range := hclosed'.completeSpace_coe
  exact ContinuousLinearEquiv.ofBijectiveOfIsTate f.rangeRestrict
    ⟨fun x y hxy ↦ hinj (congrArg Subtype.val hxy), f.toLinearMap.surjective_rangeRestrict⟩

@[simp]
theorem coeFn_equivRangeOfIsTate (f : M →L[R] N) (hinj : Injective f)
    (hclosed : IsClosed (Set.range f)) :
    ⇑(f.equivRangeOfIsTate hinj hclosed) = f.rangeRestrict := by
  rfl

@[simp]
theorem coe_equivRangeOfIsTate (f : M →L[R] N) (hinj : Injective f)
    (hclosed : IsClosed (Set.range f)) :
    (f.equivRangeOfIsTate hinj hclosed : M →L[R] f.range) = f.rangeRestrict := by
  ext
  rfl

@[simp]
theorem equivRangeOfIsTate_apply (f : M →L[R] N) (hinj : Injective f)
    (hclosed : IsClosed (Set.range f)) (x : M) :
    f.equivRangeOfIsTate hinj hclosed x = f.rangeRestrict x := by
  rfl

@[simp]
theorem equivRangeOfIsTate_symm_apply_apply (f : M →L[R] N) (hinj : Injective f)
    (hclosed : IsClosed (Set.range f)) (x : M) :
    (f.equivRangeOfIsTate hinj hclosed).symm ⟨f x, f.mem_range_self x⟩ = x :=
  (f.equivRangeOfIsTate hinj hclosed).symm_apply_apply x

/-- A continuous linear endomorphism of a complete ultrametric normed module over a Tate ring is a
unit in `N →L[R] N` if and only if it is bijective. -/
theorem isUnit_iff_bijective_of_isTate [IsUltrametricDist N] (f : N →L[R] N) :
    IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, hu⟩ ↦ hu ▸ (ContinuousLinearEquiv.ofUnit u).bijective,
    fun hf ↦ ⟨(ContinuousLinearEquiv.ofBijectiveOfIsTate f hf).toUnit,
      ContinuousLinearEquiv.coe_ofBijectiveOfIsTate f hf⟩⟩

end ContinuousLinearMap

/-! ### Closed graph theorem -/

namespace LinearMap

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [IsUltrametricDist N] [CompleteSpace N]
  [Module R N] [IsBoundedSMul R N]

-- Adapted from `LinearMap.continuous_of_isClosed_graph` in
-- `Mathlib/Analysis/Normed/Operator/Banach.lean`.
/-- **Closed Graph Theorem** for normed modules over a Tate ring: a linear map from a complete
ultrametric normed module to a complete ultrametric seminormed module whose graph is closed is
continuous. -/
theorem continuous_of_isClosed_graph_of_isTate (f : M →ₗ[R] N)
    (hg : IsClosed (f.graph : Set (M × N))) :
    Continuous f := by
  have : CompleteSpace f.graph := hg.completeSpace_coe
  let φ₀ : M →ₗ[R] M × N := LinearMap.id.prod f
  have hleft : LeftInverse Prod.fst φ₀ := fun _ ↦ rfl
  let φ : M ≃ₗ[R] f.graph :=
    (LinearEquiv.ofLeftInverse hleft).trans (LinearEquiv.ofEq _ _ f.graph_eq_range_prod.symm)
  have hφ : Continuous φ :=
    φ.symm.continuous_symm_of_isTate continuous_subtype_val.fst
  exact (continuous_subtype_val.comp hφ).snd

-- Adapted from `LinearMap.continuous_of_seq_closed_graph` in
-- `Mathlib/Analysis/Normed/Operator/Banach.lean`.
/-- **Sequential Closed Graph Theorem** for normed modules over a Tate ring: a linear map from a
complete ultrametric normed module to a complete ultrametric seminormed module whose graph is
sequentially closed is continuous. -/
theorem continuous_of_seq_closed_graph_of_isTate (f : M →ₗ[R] N)
    (hg : ∀ (u : ℕ → M) (x : M) (y : N),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    Continuous f := by
  refine f.continuous_of_isClosed_graph_of_isTate (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have hcomp : f ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [hcomp]
  exact (continuous_snd.tendsto _).comp hφ

end LinearMap

namespace ContinuousLinearMap

variable {R M N : Type*} [SeminormedRing R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
  [Module R M] [IsBoundedSMul R M]
  [SeminormedAddCommGroup N] [IsUltrametricDist N] [CompleteSpace N]
  [Module R N] [IsBoundedSMul R N]
  {f : M →ₗ[R] N}

/-- Construct a bundled continuous linear map from a linear map with closed graph over a Tate
ring. -/
def ofIsClosedGraphOfIsTate (hg : IsClosed (f.graph : Set (M × N))) :
    M →L[R] N where
  toLinearMap := f
  cont := f.continuous_of_isClosed_graph_of_isTate hg

@[simp]
theorem coeFn_ofIsClosedGraphOfIsTate (hg : IsClosed (f.graph : Set (M × N))) :
    ⇑(ofIsClosedGraphOfIsTate hg) = f :=
  (rfl)

@[simp]
theorem coe_ofIsClosedGraphOfIsTate (hg : IsClosed (f.graph : Set (M × N))) :
    (ofIsClosedGraphOfIsTate hg : M →ₗ[R] N) = f :=
  (rfl)

@[simp]
theorem ofIsClosedGraphOfIsTate_apply (hg : IsClosed (f.graph : Set (M × N))) (x : M) :
    ofIsClosedGraphOfIsTate hg x = f x :=
  (rfl)

/-- Construct a bundled continuous linear map from a linear map with sequentially closed graph over
a Tate ring. -/
def ofSeqClosedGraphOfIsTate
    (hg : ∀ (u : ℕ → M) (x : M) (y : N),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    M →L[R] N where
  toLinearMap := f
  cont := f.continuous_of_seq_closed_graph_of_isTate hg

@[simp]
theorem coeFn_ofSeqClosedGraphOfIsTate
    (hg : ∀ (u : ℕ → M) (x : M) (y : N),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    ⇑(ofSeqClosedGraphOfIsTate hg) = f :=
  (rfl)

@[simp]
theorem coe_ofSeqClosedGraphOfIsTate
    (hg : ∀ (u : ℕ → M) (x : M) (y : N),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) :
    (ofSeqClosedGraphOfIsTate hg : M →ₗ[R] N) = f :=
  (rfl)

@[simp]
theorem ofSeqClosedGraphOfIsTate_apply
    (hg : ∀ (u : ℕ → M) (x : M) (y : N),
      Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 y) → y = f x) (x : M) :
    ofSeqClosedGraphOfIsTate hg x = f x :=
  (rfl)

end ContinuousLinearMap

/-! ### Quantitative finite spanning -/

namespace TauCeti

variable {R N ι : Type*} [Fintype ι] [SeminormedRing R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [NormedAddCommGroup N] [CompleteSpace N] [Module R N] [IsBoundedSMul R N]

/-- **Quantitative finite spanning over a complete ultrametric Tate ring.**
If a finite family `v : ι → N` spans a complete normed module `N` over a complete ultrametric
Tate ring `R`, then there exists `C > 0` such that every `y : N` can be written as
`∑ i, c i • v i` with `‖c‖ ≤ C * ‖y‖` (and hence `‖c i‖ ≤ C * ‖y‖` for every `i`). -/
theorem exists_linearCombination_eq_and_norm_le (v : ι → N)
    (hspan : Submodule.span R (Set.range v) = ⊤) :
    ∃ C > 0, ∀ y : N, ∃ c : ι → R, (∑ i : ι, c i • v i) = y ∧ ‖c‖ ≤ C * ‖y‖ := by
  have hsurj : Surjective (Fintype.linearCombination R v) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination R v).mp hspan
  exact (Fintype.linearCombination R v).exists_preimage_norm_le_of_surjective
    (Fintype.linearCombination R v).continuous_on_pi hsurj

end TauCeti
