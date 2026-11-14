/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
public import TauCeti.Topology.Compactification.OnePoint.ComplSingleton
public import TauCeti.Topology.ContinuousMap.Ideals
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

import TauCeti.Topology.Compactness.Compact

/-!
# Functions vanishing at infinity on one-point compactifications and punctured compact spaces

Mathlib constructs the zero-extension
`ZeroAtInftyContinuousMap.toOnePoint : C₀(X, R) → C(OnePoint X, R)` for an `R₁` space `X`, and
`TauCeti.onePointComplSingletonHomeomorph` identifies `OnePoint {x : K // x ≠ x₀}` with any compact
Hausdorff space `K` by sending `∞` to `x₀`.

This file supplies the metric, norm, and star-algebraic bridges needed to pass between `C₀` on a
punctured compact space `{x : K // x ≠ x₀}` and the evaluation-kernel subalgebra
`{F ∈ C(K, A) : F x₀ = 0}` of continuous functions vanishing at `x₀` (which is a maximal ideal when
`A` is a field such as `ℂ`):

* `ZeroAtInftyContinuousMap.range_toOnePoint`, `ZeroAtInftyContinuousMap.isometry_toOnePoint`, and
  `ZeroAtInftyContinuousMap.norm_toOnePoint`: the image of `toOnePoint` is the set of continuous
  functions vanishing at `∞`, and `toOnePoint` is an isometry preserving the supremum norm;
* `ContinuousMap.restrictComplSingleton` and `ZeroAtInftyContinuousMap.extendZero`: restriction of
  `F : C(K, β)` with `F x₀ = 0` to `C₀({x : K // x ≠ x₀}, β)` (on any compact space `K`) and
  extension of `g : C₀({x : K // x ≠ x₀}, β)` by zero at `x₀` to `C(K, β)` (for compact Hausdorff
  `K`), with continuity of `Function.extend`, algebraic simp lemmas, two-sided inverse identities,
  and metric isometry / norm preservation;
* `ContinuousMap.restrictComplSingletonStarAlgEquiv`: the isometric star-algebra isomorphism
  `evalKerSubalgebra S A x₀ ≃⋆ₐ[S] C₀({x : K // x ≠ x₀}, A)`.
-/

public section

open Filter Function Set Topology OnePoint
open scoped ZeroAtInfty BoundedContinuousFunction

namespace ZeroAtInftyContinuousMap

section OnePoint

variable {X β E : Type*} [TopologicalSpace X] [R1Space X]

/-- The image of `ZeroAtInftyContinuousMap.toOnePoint` consists precisely of the continuous
functions on `OnePoint X` that vanish at `∞`. -/
theorem range_toOnePoint [TopologicalSpace β] [Zero β] :
    Set.range (toOnePoint : C₀(X, β) → C(OnePoint X, β)) = {g : C(OnePoint X, β) | g ∞ = 0} := by
  ext g
  refine ⟨?_, fun hg ↦ ?_⟩
  · rintro ⟨f, rfl⟩
    exact toOnePoint_infty f
  · refine ⟨⟨g.comp ⟨(↑), OnePoint.continuous_coe⟩, ?_⟩, ?_⟩
    · rw [← coclosedCompact_eq_cocompact, ← hg]
      exact (g.continuous.tendsto ∞).comp OnePoint.tendsto_coe_infty
    · ext p
      induction p using OnePoint.rec with
      | infty => exact hg.symm
      | coe x => rfl

/-- Extension by zero to `OnePoint X` is an isometry. -/
theorem isometry_toOnePoint [PseudoMetricSpace β] [Zero β] :
    Isometry (toOnePoint : C₀(X, β) → C(OnePoint X, β)) :=
  Isometry.of_dist_eq fun f g ↦ by
    refine le_antisymm ((ContinuousMap.dist_le dist_nonneg).2 fun p ↦ ?_) ?_
    · induction p using OnePoint.rec with
      | infty => simp [dist_nonneg]
      | coe x =>
        rw [← dist_toBCF_eq_dist]
        exact BoundedContinuousFunction.dist_coe_le_dist (f := f.toBCF) (g := g.toBCF) x
    · rw [← dist_toBCF_eq_dist]
      exact (BoundedContinuousFunction.dist_le dist_nonneg).2 fun x ↦
        ContinuousMap.dist_apply_le_dist (f := f.toOnePoint) (g := g.toOnePoint) (x : OnePoint X)

/-- Extension by zero to the one-point compactification preserves the supremum norm. -/
@[simp]
theorem norm_toOnePoint [SeminormedAddCommGroup E] (f : C₀(X, E)) :
    ‖f.toOnePoint‖ = ‖f‖ :=
  isometry_toOnePoint.norm_map_of_map_zero toOnePoint_zero f

end OnePoint

end ZeroAtInftyContinuousMap

section PuncturedCompact

namespace ContinuousMap

section Compact

variable {K β : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Restricting any `F : C(K, β)` to `{x : K // x ≠ x₀}` approaches `F x₀` along the cocompact
filter. -/
theorem tendsto_restrict_complSingleton_cocompact [TopologicalSpace β] (F : C(K, β)) (x₀ : K) :
    Tendsto (fun x : {x : K // x ≠ x₀} ↦ F x.1) (cocompact {x : K // x ≠ x₀}) (𝓝 (F x₀)) :=
  (F.continuous.tendsto x₀).comp (TauCeti.tendsto_subtypeVal_cocompact_nhds x₀)

/-- Restricting `F : C(K, β)` with `F x₀ = 0` to the punctured space `{x : K // x ≠ x₀}` produces a
continuous function vanishing at infinity. -/
def restrictComplSingleton [TopologicalSpace β] [Zero β] (F : C(K, β)) {x₀ : K} (hF : F x₀ = 0) :
    C₀({x : K // x ≠ x₀}, β) where
  toFun x := F x.1
  continuous_toFun := F.continuous.comp continuous_subtype_val
  zero_at_infty' := hF ▸ F.tendsto_restrict_complSingleton_cocompact x₀

/-- `F.restrictComplSingleton hF` evaluates as `F` on `{x : K // x ≠ x₀}`. -/
@[simp]
theorem restrictComplSingleton_apply [TopologicalSpace β] [Zero β] (F : C(K, β)) {x₀ : K}
    (hF : F x₀ = 0) (x : {x : K // x ≠ x₀}) :
    F.restrictComplSingleton hF x = F x.1 := (rfl)

/-- When `{x : K // x ≠ x₀}` is compact, `restrictComplSingleton` agrees with ordinary subtype
restriction lifted through `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty`. -/
theorem restrictComplSingleton_eq_liftZeroAtInfty [TopologicalSpace β] [Zero β]
    {x₀ : K} [CompactSpace {x : K // x ≠ x₀}] (F : C(K, β)) (hF : F x₀ = 0) :
    F.restrictComplSingleton hF =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
        (F.comp ⟨Subtype.val, continuous_subtype_val⟩) := by
  ext x
  simp

end Compact

end ContinuousMap

namespace ZeroAtInftyContinuousMap

variable {K β E : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- Extension by zero of `g : C₀({x : K // x ≠ x₀}, β)` across the puncture `x₀ : K`, yielding a
continuous function on `K` that vanishes at `x₀`. -/
noncomputable def extendZero [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) : C(K, β) :=
  g.toOnePoint.comp (TauCeti.onePointComplSingletonHomeomorph x₀).symm

/-- `g.extendZero` is `g.toOnePoint` composed with `(onePointComplSingletonHomeomorph x₀).symm`. -/
theorem extendZero_def [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) :
    g.extendZero = g.toOnePoint.comp (TauCeti.onePointComplSingletonHomeomorph x₀).symm := (rfl)

/-- `g.extendZero` vanishes at the puncture `x₀`. -/
@[simp]
theorem extendZero_apply_self [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) :
    g.extendZero x₀ = 0 := by
  simp [extendZero]

/-- Away from `x₀`, `g.extendZero` agrees with `g`. -/
theorem extendZero_apply_of_ne [TopologicalSpace β] [Zero β] {x₀ x : K} (hx : x ≠ x₀)
    (g : C₀({x : K // x ≠ x₀}, β)) :
    g.extendZero x = g ⟨x, hx⟩ := by
  simp [extendZero, TauCeti.onePointComplSingletonHomeomorph_symm_apply_of_ne hx]

/-- On `{x : K // x ≠ x₀}`, `g.extendZero` agrees with `g`. -/
@[simp]
theorem extendZero_apply_coe [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) (x : {x : K // x ≠ x₀}) :
    g.extendZero x.1 = g x :=
  g.extendZero_apply_of_ne x.2

/-- As a bare function `K → β`, `g.extendZero` is `Function.extend Subtype.val g 0`. -/
theorem coe_extendZero_eq_extend [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) :
    ⇑g.extendZero = Function.extend (Subtype.val : {x : K // x ≠ x₀} → K) g 0 := by
  ext x
  by_cases hx : x = x₀
  · subst hx
    rw [extendZero_apply_self, Function.extend_apply']
    · rfl
    · rintro ⟨y, hy⟩
      exact y.2 hy
  · rw [extendZero_apply_of_ne hx]
    exact (Subtype.val_injective.extend_apply g 0 (⟨x, hx⟩ : {x : K // x ≠ x₀})).symm

/-- Extending `g : C₀({x : K // x ≠ x₀}, β)` by `0` at `x₀` is continuous on `K`. -/
theorem continuous_extend_zero [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) :
    Continuous (Function.extend (Subtype.val : {x : K // x ≠ x₀} → K) g 0) := by
  rw [← coe_extendZero_eq_extend]
  exact g.extendZero.continuous

/-- Restricting `g.extendZero` back to `{x : K // x ≠ x₀}` recovers `g`. -/
@[simp]
theorem restrictComplSingleton_extendZero [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) :
    g.extendZero.restrictComplSingleton g.extendZero_apply_self = g := by
  ext x
  simp

/-- Extending the restriction of `F : C(K, β)` with `F x₀ = 0` by zero recovers `F`. -/
@[simp]
theorem extendZero_restrictComplSingleton [TopologicalSpace β] [Zero β] {F : C(K, β)} {x₀ : K}
    (hF : F x₀ = 0) :
    (F.restrictComplSingleton hF).extendZero = F := by
  ext x
  by_cases hx : x = x₀
  · subst hx
    exact ((F.restrictComplSingleton hF).extendZero_apply_self).trans hF.symm
  · simp [extendZero_apply_of_ne hx]

/-- Extension by zero from `{x : K // x ≠ x₀}` to `K` is injective. -/
theorem extendZero_injective [TopologicalSpace β] [Zero β] (x₀ : K) :
    Function.Injective (extendZero (x₀ := x₀) (β := β)) := fun f g h ↦ by
  ext x
  simpa using DFunLike.congr_fun h x.1

/-- The image of `extendZero` is the set of continuous functions on `K` vanishing at `x₀`. -/
theorem range_extendZero [TopologicalSpace β] [Zero β] (x₀ : K) :
    Set.range (extendZero (x₀ := x₀) (β := β)) = {F : C(K, β) | F x₀ = 0} := by
  ext F
  exact ⟨by rintro ⟨g, rfl⟩; exact g.extendZero_apply_self,
    fun hF ↦ ⟨F.restrictComplSingleton hF, extendZero_restrictComplSingleton hF⟩⟩

/-- Extending the zero map by zero gives `0`. -/
@[simp]
theorem extendZero_zero [TopologicalSpace β] [Zero β] {x₀ : K} :
    (0 : C₀({x : K // x ≠ x₀}, β)).extendZero = 0 := by
  simp [extendZero]

/-- `extendZero` distributes over addition. -/
@[simp]
theorem extendZero_add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β] {x₀ : K}
    (f g : C₀({x : K // x ≠ x₀}, β)) :
    (f + g).extendZero = f.extendZero + g.extendZero := by
  simp [extendZero, ContinuousMap.add_comp]

/-- `extendZero` commutes with negation. -/
@[simp]
theorem extendZero_neg [TopologicalSpace β] [AddGroup β] [IsTopologicalAddGroup β] {x₀ : K}
    (f : C₀({x : K // x ≠ x₀}, β)) :
    (-f).extendZero = -f.extendZero := by
  simp [extendZero, ContinuousMap.neg_comp]

/-- `extendZero` distributes over subtraction. -/
@[simp]
theorem extendZero_sub [TopologicalSpace β] [AddGroup β] [IsTopologicalAddGroup β] {x₀ : K}
    (f g : C₀({x : K // x ≠ x₀}, β)) :
    (f - g).extendZero = f.extendZero - g.extendZero := by
  simp [extendZero, ContinuousMap.sub_comp]

/-- `extendZero` distributes over multiplication. -/
@[simp]
theorem extendZero_mul [TopologicalSpace β] [MulZeroClass β] [ContinuousMul β] {x₀ : K}
    (f g : C₀({x : K // x ≠ x₀}, β)) :
    (f * g).extendZero = f.extendZero * g.extendZero := by
  simp [extendZero, ContinuousMap.mul_comp]

/-- `extendZero` commutes with scalar multiplication. -/
@[simp]
theorem extendZero_smul {S : Type*} [TopologicalSpace β] [Zero β] [SMulZeroClass S β]
    [ContinuousConstSMul S β] {x₀ : K} (c : S) (f : C₀({x : K // x ≠ x₀}, β)) :
    (c • f).extendZero = c • f.extendZero := by
  simp [extendZero, ContinuousMap.smul_comp]

/-- `extendZero` commutes with pointwise `star`. -/
@[simp]
theorem extendZero_star [TopologicalSpace β] [AddMonoid β] [StarAddMonoid β] [ContinuousStar β]
    {x₀ : K} (f : C₀({x : K // x ≠ x₀}, β)) :
    (star f).extendZero = star f.extendZero := by
  ext x
  simp [extendZero]

/-- Extension by zero from `{x : K // x ≠ x₀}` to `K` is an isometry. -/
theorem isometry_extendZero [PseudoMetricSpace β] [Zero β] (x₀ : K) :
    Isometry (extendZero (x₀ := x₀) (β := β)) :=
  Isometry.of_dist_eq fun f g ↦ by
    simp only [extendZero_def]
    refine le_antisymm
      ((ContinuousMap.dist_le dist_nonneg).2 fun x ↦
        (ContinuousMap.dist_apply_le_dist (f := f.toOnePoint) (g := g.toOnePoint)
          ((TauCeti.onePointComplSingletonHomeomorph x₀).symm x)).trans
          (isometry_toOnePoint.dist_eq f g).le)
      ((isometry_toOnePoint.dist_eq f g).symm ▸
        (ContinuousMap.dist_le dist_nonneg).2 fun p ↦ ?_)
    simpa using ContinuousMap.dist_apply_le_dist
      (f := f.toOnePoint.comp (TauCeti.onePointComplSingletonHomeomorph x₀).symm)
      (g := g.toOnePoint.comp (TauCeti.onePointComplSingletonHomeomorph x₀).symm)
      (TauCeti.onePointComplSingletonHomeomorph x₀ p)

/-- Extension by zero from `{x : K // x ≠ x₀}` to `K` preserves the supremum norm. -/
@[simp]
theorem norm_extendZero [SeminormedAddCommGroup E] {x₀ : K} (g : C₀({x : K // x ≠ x₀}, E)) :
    ‖g.extendZero‖ = ‖g‖ :=
  (isometry_extendZero x₀).norm_map_of_map_zero extendZero_zero g

end ZeroAtInftyContinuousMap

namespace ContinuousMap

section RestrictComplEquiv

variable {K S E A : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- Restricting `F : C(K, E)` with `F x₀ = 0` to `{x : K // x ≠ x₀}` preserves the supremum
norm. -/
@[simp]
theorem norm_restrictComplSingleton [SeminormedAddCommGroup E] (F : C(K, E)) {x₀ : K}
    (hF : F x₀ = 0) :
    ‖F.restrictComplSingleton hF‖ = ‖F‖ := by
  simpa only [ZeroAtInftyContinuousMap.norm_extendZero] using
    congrArg norm (ZeroAtInftyContinuousMap.extendZero_restrictComplSingleton hF)

variable (S A) in
/-- Restriction to `{x : K // x ≠ x₀}` is a star-algebra isomorphism from
`{F ∈ C(K, A) : F x₀ = 0}` onto `C₀({x : K // x ≠ x₀}, A)`, with inverse given by extension by
zero. -/
noncomputable def restrictComplSingletonStarAlgEquiv [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    evalKerSubalgebra S A x₀ ≃⋆ₐ[S] C₀({x : K // x ≠ x₀}, A) where
  toFun F := F.1.restrictComplSingleton (mem_evalKerSubalgebra.mp F.2)
  invFun g := ⟨g.extendZero, mem_evalKerSubalgebra.mpr g.extendZero_apply_self⟩
  left_inv F := Subtype.ext <|
    ZeroAtInftyContinuousMap.extendZero_restrictComplSingleton (mem_evalKerSubalgebra.mp F.2)
  right_inv g := g.restrictComplSingleton_extendZero
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- `restrictComplSingletonStarAlgEquiv S A x₀` applies `ContinuousMap.restrictComplSingleton` to
the underlying continuous map. -/
@[simp]
theorem restrictComplSingletonStarAlgEquiv_apply [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) (F : evalKerSubalgebra S A x₀) :
    restrictComplSingletonStarAlgEquiv S A x₀ F =
      F.1.restrictComplSingleton (mem_evalKerSubalgebra.mp F.2) := (rfl)

/-- The inverse of `restrictComplSingletonStarAlgEquiv S A x₀` coerces to `extendZero`. -/
@[simp]
theorem coe_restrictComplSingletonStarAlgEquiv_symm_apply [CommSemiring S]
    [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [IsTopologicalSemiring A] [StarAddMonoid A]
    [ContinuousStar A] [Module S A] [ContinuousConstSMul S A] (x₀ : K)
    (g : C₀({x : K // x ≠ x₀}, A)) :
    ((restrictComplSingletonStarAlgEquiv S A x₀).symm g : C(K, A)) = g.extendZero := (rfl)

/-- `restrictComplSingletonStarAlgEquiv` preserves the supremum norm. -/
theorem norm_restrictComplSingletonStarAlgEquiv [CommRing S]
    [NonUnitalSeminormedRing E] [StarAddMonoid E] [ContinuousStar E] [Module S E]
    [ContinuousConstSMul S E] (x₀ : K) (F : evalKerSubalgebra S E x₀) :
    ‖restrictComplSingletonStarAlgEquiv S E x₀ F‖ = ‖F‖ :=
  F.1.norm_restrictComplSingleton (mem_evalKerSubalgebra.mp F.2)

/-- `restrictComplSingletonStarAlgEquiv` is an isometry. -/
theorem isometry_restrictComplSingletonStarAlgEquiv [CommRing S]
    [NonUnitalSeminormedRing E] [StarAddMonoid E] [ContinuousStar E] [Module S E]
    [ContinuousConstSMul S E] (x₀ : K) :
    Isometry (restrictComplSingletonStarAlgEquiv S E x₀) :=
  AddMonoidHomClass.isometry_of_norm (restrictComplSingletonStarAlgEquiv S E x₀)
    (norm_restrictComplSingletonStarAlgEquiv x₀)

end RestrictComplEquiv

end ContinuousMap

end PuncturedCompact
