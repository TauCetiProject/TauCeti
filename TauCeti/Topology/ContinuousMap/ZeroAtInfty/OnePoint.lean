/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Functions vanishing at infinity on one-point compactifications and punctured compact spaces

Mathlib constructs the zero-extension
`ZeroAtInftyContinuousMap.toOnePoint : C₀(X, R) → C(OnePoint X, R)` for an `R₁` space `X` and
identifies `OnePoint X` with any compact Hausdorff space `K` in which `X` embeds as the complement
of a single point (`OnePoint.equivOfIsEmbeddingOfRangeEq`).

This file supplies the metric, norm, and star-algebraic bridges needed to pass between `C₀` on a
punctured compact Hausdorff space `K \ {x₀}` and the maximal ideal `{F ∈ C(K, R) : F x₀ = 0}` of
continuous functions vanishing at `x₀`:

* `ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv` and
  `ContinuousMap.liftZeroAtInftyStarAlgEquiv`: star-algebraic reindexing of `C₀` along
  homeomorphisms, together with the isometric star isomorphism `C(α, A) ≃⋆ₐ[R] C₀(α, A)` on compact
  spaces;
* `ZeroAtInftyContinuousMap.range_toOnePoint`, `ZeroAtInftyContinuousMap.norm_toOnePoint`, and
  `ZeroAtInftyContinuousMap.isometry_toOnePoint`: the image of `toOnePoint` is the set of
  continuous functions vanishing at `∞`, and `toOnePoint` preserves the supremum norm;
* `OnePoint.homeomorphComplSingleton` and `TauCeti.tendsto_subtypeVal_cocompact_nhds`: for compact
  Hausdorff `K` and `x₀ : K`, the locally compact Hausdorff complement `{x : K // x ≠ x₀}` has `K`
  as its one-point compactification with `∞` sent to `x₀` (even when `x₀` is isolated), and the
  inclusion tends to `x₀` along the cocompact filter;
* `ContinuousMap.restrictComplSingleton` and `ZeroAtInftyContinuousMap.extendZero`: restriction of
  `F : C(K, β)` with `F x₀ = 0` to `C₀({x : K // x ≠ x₀}, β)` and extension of
  `g : C₀({x : K // x ≠ x₀}, β)` by zero at `x₀` to `C(K, β)`, with continuity at `x₀`, two-sided
  inverse identities, and norm preservation;
* `ContinuousMap.evalKerSubalgebra` and `ContinuousMap.restrictComplSingletonStarAlgEquiv`: the
  isometric star-algebra isomorphism `{F ∈ C(K, A) : F x₀ = 0} ≃⋆ₐ[S] C₀({x : K // x ≠ x₀}, A)`,
  together with the isolated-point characterization
  `TauCeti.compactSpace_complSingleton_iff_isOpen_singleton`.
-/

public section

open Filter Function Set Topology OnePoint
open scoped ZeroAtInfty BoundedContinuousFunction

namespace ZeroAtInftyContinuousMap

section StarFunctoriality

variable {R α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

variable (R δ) in
/-- Reindexing `C₀(α, δ)` along a homeomorphism `e : α ≃ₜ β` as a star-algebra equivalence
`f ↦ f ∘ e.symm`, matching `ZeroAtInftyContinuousMap.congrLeft`. -/
def congrLeftStarAlgEquiv [Zero R] [NonUnitalNonAssocSemiring δ] [IsTopologicalSemiring δ]
    [StarRing δ] [ContinuousStar δ] [SMulWithZero R δ] [ContinuousConstSMul R δ]
    (e : α ≃ₜ β) : C₀(α, δ) ≃⋆ₐ[R] C₀(β, δ) where
  toFun f := f.comp e.symm.toCocompactMap
  invFun f := f.comp e.toCocompactMap
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem congrLeftStarAlgEquiv_apply [Zero R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [StarRing δ] [ContinuousStar δ] [SMulWithZero R δ]
    [ContinuousConstSMul R δ] (e : α ≃ₜ β) (f : C₀(α, δ)) (y : β) :
    congrLeftStarAlgEquiv R δ e f y = f (e.symm y) := (rfl)

@[simp]
theorem congrLeftStarAlgEquiv_symm [Zero R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [StarRing δ] [ContinuousStar δ] [SMulWithZero R δ]
    [ContinuousConstSMul R δ] (e : α ≃ₜ β) :
    (congrLeftStarAlgEquiv R δ e).symm = congrLeftStarAlgEquiv R δ e.symm := (rfl)

@[simp]
theorem congrLeftStarAlgEquiv_refl [Zero R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [StarRing δ] [ContinuousStar δ] [SMulWithZero R δ]
    [ContinuousConstSMul R δ] :
    congrLeftStarAlgEquiv R δ (Homeomorph.refl α) = StarAlgEquiv.refl R C₀(α, δ) := (rfl)

theorem congrLeftStarAlgEquiv_trans [Zero R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [StarRing δ] [ContinuousStar δ] [SMulWithZero R δ]
    [ContinuousConstSMul R δ] (e : α ≃ₜ β) (e' : β ≃ₜ γ) :
    congrLeftStarAlgEquiv R δ (e.trans e') =
      (congrLeftStarAlgEquiv R δ e).trans (congrLeftStarAlgEquiv R δ e') := (rfl)

/-- Reindexing `C₀` along a homeomorphism preserves the supremum norm. -/
@[simp]
theorem norm_congrLeftStarAlgEquiv {E : Type*} [NonUnitalSeminormedRing E] [StarRing E]
    [ContinuousStar E] [Zero R] [SMulWithZero R E] [ContinuousConstSMul R E]
    (e : α ≃ₜ β) (f : C₀(α, E)) :
    ‖congrLeftStarAlgEquiv R E e f‖ = ‖f‖ :=
  norm_comp_toCocompactMap f e.symm

end StarFunctoriality

section OnePoint

variable {X β E : Type*} [TopologicalSpace X] [R1Space X]

/-- The image of `ZeroAtInftyContinuousMap.toOnePoint` consists precisely of the continuous
functions on `OnePoint X` that vanish at `∞`. -/
theorem range_toOnePoint [TopologicalSpace β] [Zero β] :
    Set.range (toOnePoint : C₀(X, β) → C(OnePoint X, β)) = {g : C(OnePoint X, β) | g ∞ = 0} := by
  ext g
  refine ⟨?_, fun hg => ?_⟩
  · rintro ⟨f, rfl⟩
    exact toOnePoint_infty f
  · refine ⟨⟨g.comp ⟨(↑), OnePoint.continuous_coe⟩, ?_⟩, ?_⟩
    · rw [← coclosedCompact_eq_cocompact, ← hg]
      exact (g.continuous.tendsto ∞).comp OnePoint.tendsto_coe_infty
    · ext p
      induction p using OnePoint.rec with
      | infty => exact hg.symm
      | coe x => rfl

/-- Extension by zero to the one-point compactification preserves the supremum norm. -/
@[simp]
theorem norm_toOnePoint [SeminormedAddCommGroup E] (f : C₀(X, E)) :
    ‖f.toOnePoint‖ = ‖f‖ := by
  refine le_antisymm
    ((ContinuousMap.norm_le _ (norm_nonneg f)).2 fun p => ?_)
    ((norm_le (norm_nonneg f.toOnePoint)).2 fun x => ContinuousMap.norm_coe_le_norm f.toOnePoint x)
  induction p using OnePoint.rec with
  | infty => simp [norm_nonneg f]
  | coe x => exact norm_coe_le_norm f x

/-- Extension by zero to `OnePoint X` is an isometry. -/
theorem isometry_toOnePoint [SeminormedAddCommGroup E] :
    Isometry (toOnePoint : C₀(X, E) → C(OnePoint X, E)) :=
  AddMonoidHomClass.isometry_of_norm (toOnePointAddMonoidHom X E) norm_toOnePoint

end OnePoint

end ZeroAtInftyContinuousMap

namespace ContinuousMap

section CompactLift

variable {R α β E A : Type*} [TopologicalSpace α] [CompactSpace α]

/-- On a compact space, `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty` is an isometry. -/
theorem isometry_liftZeroAtInfty [PseudoMetricSpace β] [Zero β] :
    Isometry (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty : C(α, β) → C₀(α, β)) :=
  fun _ _ => rfl

/-- On a compact space, `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty` preserves the
supremum norm. -/
@[simp]
theorem norm_liftZeroAtInfty [SeminormedAddCommGroup E] (f : C(α, E)) :
    ‖ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f‖ = ‖f‖ :=
  le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg f)).2 fun x => norm_coe_le_norm f x)
    ((norm_le _ (norm_nonneg _)).2 fun x =>
      ZeroAtInftyContinuousMap.norm_coe_le_norm
        (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f) x)

variable (R α A) in
/-- On a compact space `α`, `C(α, A)` and `C₀(α, A)` are canonically isomorphic as star
algebras via `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty`. -/
def liftZeroAtInftyStarAlgEquiv [Zero R] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [SMulWithZero R A]
    [ContinuousConstSMul R A] : C(α, A) ≃⋆ₐ[R] C₀(α, A) where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem coe_liftZeroAtInftyStarAlgEquiv [Zero R] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [SMulWithZero R A]
    [ContinuousConstSMul R A] :
    ⇑(liftZeroAtInftyStarAlgEquiv R α A) = ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty :=
  (rfl)

@[simp]
theorem liftZeroAtInftyStarAlgEquiv_symm_apply [Zero R] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A]
    [SMulWithZero R A] [ContinuousConstSMul R A] (f : C₀(α, A)) :
    (liftZeroAtInftyStarAlgEquiv R α A).symm f = f.toContinuousMap := (rfl)

end CompactLift

end ContinuousMap

section PuncturedCompact

/-- Removing a point from a locally compact `T₁` space yields a locally compact subspace. -/
instance Subtype.instLocallyCompactSpaceNe {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [T1Space X] {x₀ : X} : LocallyCompactSpace {x : X // x ≠ x₀} :=
  isClosed_singleton.isOpen_compl.locallyCompactSpace

namespace TauCeti

/-- In a compact Hausdorff space `K`, the punctured space `{x : K // x ≠ x₀}` is compact if and
only if `x₀` is an isolated point (`{x₀}` is open). -/
theorem compactSpace_complSingleton_iff_isOpen_singleton {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] {x₀ : K} :
    CompactSpace {x : K // x ≠ x₀} ↔ IsOpen ({x₀} : Set K) := by
  refine ⟨fun _ => ?_, fun hx => ?_⟩
  · rw [← isClosed_compl_iff]
    have hrange : Set.range (Subtype.val : {x : K // x ≠ x₀} → K) = {x₀}ᶜ := by
      ext x
      simp
    rw [← hrange]
    exact (isCompact_range continuous_subtype_val).isClosed
  · exact isCompact_iff_compactSpace.mp hx.isClosed_compl.isCompact

end TauCeti

namespace OnePoint

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- Every compact Hausdorff space `K` is canonically homeomorphic to the one-point extension
`OnePoint {x : K // x ≠ x₀}` of the complement of any point `x₀ : K`, with `∞` sent to `x₀`
(including when `K` is a singleton or `x₀` is isolated). -/
noncomputable def homeomorphComplSingleton (x₀ : K) : OnePoint {x : K // x ≠ x₀} ≃ₜ K :=
  equivOfIsEmbeddingOfRangeEq x₀ Subtype.val Topology.IsEmbedding.subtypeVal <| by
    ext x
    simp

@[simp]
theorem homeomorphComplSingleton_apply_coe (x₀ : K) (x : {x : K // x ≠ x₀}) :
    homeomorphComplSingleton x₀ x = x.1 := (rfl)

@[simp]
theorem homeomorphComplSingleton_apply_infty (x₀ : K) :
    homeomorphComplSingleton x₀ ∞ = x₀ := (rfl)

@[simp]
theorem homeomorphComplSingleton_symm_apply_self (x₀ : K) :
    (homeomorphComplSingleton x₀).symm x₀ = ∞ := by
  rw [Homeomorph.symm_apply_eq]
  rfl

theorem homeomorphComplSingleton_symm_apply_of_ne {x₀ x : K} (hx : x ≠ x₀) :
    (homeomorphComplSingleton x₀).symm x = (⟨x, hx⟩ : {x : K // x ≠ x₀}) := by
  rw [Homeomorph.symm_apply_eq]
  rfl

@[simp]
theorem homeomorphComplSingleton_symm_apply_coe (x₀ : K) (x : {x : K // x ≠ x₀}) :
    (homeomorphComplSingleton x₀).symm x.1 = x :=
  homeomorphComplSingleton_symm_apply_of_ne x.2

end OnePoint

namespace TauCeti

/-- In a compact Hausdorff space `K`, the inclusion of `{x : K // x ≠ x₀}` into `K` tends to `x₀`
along the cocompact filter. -/
theorem tendsto_subtypeVal_cocompact_nhds {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K] (x₀ : K) :
    Tendsto (Subtype.val : {x : K // x ≠ x₀} → K) (cocompact {x : K // x ≠ x₀}) (𝓝 x₀) := by
  rw [← coclosedCompact_eq_cocompact]
  have hcomp :
      (OnePoint.homeomorphComplSingleton x₀ ∘
        (OnePoint.some : {x : K // x ≠ x₀} → OnePoint {x : K // x ≠ x₀})) = Subtype.val := by
    ext x
    simp
  rw [← hcomp]
  simpa using ((OnePoint.homeomorphComplSingleton x₀).continuous.tendsto ∞).comp
    OnePoint.tendsto_coe_infty

end TauCeti

namespace ContinuousMap

variable {K β : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- Restricting any `F : C(K, β)` to `{x : K // x ≠ x₀}` approaches `F x₀` along the cocompact
filter. -/
theorem tendsto_restrict_complSingleton_cocompact [TopologicalSpace β] (F : C(K, β)) (x₀ : K) :
    Tendsto (fun x : {x : K // x ≠ x₀} => F x.1) (cocompact {x : K // x ≠ x₀}) (𝓝 (F x₀)) :=
  (F.continuous.tendsto x₀).comp (TauCeti.tendsto_subtypeVal_cocompact_nhds x₀)

/-- Restricting `F : C(K, β)` with `F x₀ = 0` to the punctured space `{x : K // x ≠ x₀}` produces a
continuous function vanishing at infinity. -/
def restrictComplSingleton [TopologicalSpace β] [Zero β] (F : C(K, β)) {x₀ : K} (hF : F x₀ = 0) :
    C₀({x : K // x ≠ x₀}, β) where
  toFun x := F x.1
  continuous_toFun := F.continuous.comp continuous_subtype_val
  zero_at_infty' := hF ▸ F.tendsto_restrict_complSingleton_cocompact x₀

@[simp]
theorem restrictComplSingleton_apply [TopologicalSpace β] [Zero β] (F : C(K, β)) {x₀ : K}
    (hF : F x₀ = 0) (x : {x : K // x ≠ x₀}) :
    F.restrictComplSingleton hF x = F x.1 := (rfl)

end ContinuousMap

namespace ZeroAtInftyContinuousMap

variable {K β E : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- Extension by zero of `g : C₀({x : K // x ≠ x₀}, β)` across the puncture `x₀ : K`, yielding a
continuous function on `K` that vanishes at `x₀`. -/
noncomputable def extendZero [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) : C(K, β) :=
  g.toOnePoint.comp (OnePoint.homeomorphComplSingleton x₀).symm

@[simp]
theorem extendZero_apply_self [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) :
    g.extendZero x₀ = 0 := by
  simp [extendZero]

theorem extendZero_apply_of_ne [TopologicalSpace β] [Zero β] {x₀ x : K} (hx : x ≠ x₀)
    (g : C₀({x : K // x ≠ x₀}, β)) :
    g.extendZero x = g ⟨x, hx⟩ := by
  simp [extendZero, OnePoint.homeomorphComplSingleton_symm_apply_of_ne hx]

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

/-- Extending `g : C₀({x : K // x ≠ x₀}, β)` by `0` at `x₀` is continuous at `x₀`. -/
theorem continuousAt_extend_zero [TopologicalSpace β] [Zero β] {x₀ : K}
    (g : C₀({x : K // x ≠ x₀}, β)) :
    ContinuousAt (Function.extend (Subtype.val : {x : K // x ≠ x₀} → K) g 0) x₀ :=
  g.continuous_extend_zero.continuousAt

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
    Function.Injective (extendZero (x₀ := x₀) (β := β)) := fun f g h => by
  ext x
  simpa using DFunLike.congr_fun h x.1

/-- The image of `extendZero` is the set of continuous functions on `K` vanishing at `x₀`. -/
theorem range_extendZero [TopologicalSpace β] [Zero β] (x₀ : K) :
    Set.range (extendZero (x₀ := x₀) (β := β)) = {F : C(K, β) | F x₀ = 0} := by
  ext F
  exact ⟨by rintro ⟨g, rfl⟩; exact g.extendZero_apply_self,
    fun hF => ⟨F.restrictComplSingleton hF, extendZero_restrictComplSingleton hF⟩⟩

@[simp]
theorem extendZero_zero [TopologicalSpace β] [Zero β] {x₀ : K} :
    (0 : C₀({x : K // x ≠ x₀}, β)).extendZero = 0 := by
  simp [extendZero]

@[simp]
theorem extendZero_add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β] {x₀ : K}
    (f g : C₀({x : K // x ≠ x₀}, β)) :
    (f + g).extendZero = f.extendZero + g.extendZero := by
  simp [extendZero, ContinuousMap.add_comp]

/-- Extension by zero from `{x : K // x ≠ x₀}` to `K` preserves the supremum norm. -/
@[simp]
theorem norm_extendZero [SeminormedAddCommGroup E] {x₀ : K} (g : C₀({x : K // x ≠ x₀}, E)) :
    ‖g.extendZero‖ = ‖g‖ := by
  refine le_antisymm
    ((ContinuousMap.norm_le _ (norm_nonneg g)).2 fun x => ?_)
    ((norm_le (norm_nonneg _)).2 fun x => by
      simpa using ContinuousMap.norm_coe_le_norm g.extendZero x.1)
  by_cases hx : x = x₀
  · subst hx
    simp [norm_nonneg g]
  · simpa [extendZero_apply_of_ne hx] using norm_coe_le_norm g ⟨x, hx⟩

/-- Extension by zero from `{x : K // x ≠ x₀}` to `K` is an isometry. -/
theorem isometry_extendZero [SeminormedAddCommGroup E] (x₀ : K) :
    Isometry (extendZero (x₀ := x₀) (β := E)) :=
  AddMonoidHomClass.isometry_of_norm
    ({ toFun := extendZero
       map_zero' := extendZero_zero
       map_add' := extendZero_add } : C₀({x : K // x ≠ x₀}, E) →+ C(K, E))
    norm_extendZero

/-- Restricting `F : C(K, E)` with `F x₀ = 0` to `{x : K // x ≠ x₀}` preserves the supremum
norm. -/
@[simp]
theorem norm_restrictComplSingleton [SeminormedAddCommGroup E] (F : C(K, E)) {x₀ : K}
    (hF : F x₀ = 0) :
    ‖F.restrictComplSingleton hF‖ = ‖F‖ := by
  simpa only [norm_extendZero] using congrArg norm (extendZero_restrictComplSingleton hF)

end ZeroAtInftyContinuousMap

namespace ContinuousMap

section EvalKer

variable {K S A : Type*} [TopologicalSpace K]

variable (S A) in
/-- The nonunital star subalgebra `{F ∈ C(K, A) : F x₀ = 0}` of continuous functions vanishing at a
point `x₀ : K`. -/
def evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    NonUnitalStarSubalgebra S C(K, A) where
  carrier := {F : C(K, A) | F x₀ = 0}
  mul_mem' {f g} hf hg := by simp_all
  add_mem' {f g} hf hg := by simp_all
  zero_mem' := rfl
  smul_mem' c {f} hf := by simp_all
  star_mem' {f} hf := by simp_all

@[simp]
theorem mem_evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] {x₀ : K} {F : C(K, A)} :
    F ∈ evalKerSubalgebra S A x₀ ↔ F x₀ = 0 :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    (evalKerSubalgebra S A x₀ : Set C(K, A)) = {F : C(K, A) | F x₀ = 0} := (rfl)

/-- For `T₁` codomain `A`, `evalKerSubalgebra S A x₀` is closed in `C(K, A)`. -/
theorem isClosed_evalKerSubalgebra [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [T1Space A] [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A]
    [Module S A] [ContinuousConstSMul S A] (x₀ : K) :
    IsClosed (evalKerSubalgebra S A x₀ : Set C(K, A)) :=
  isClosed_singleton.preimage (continuous_eval_const x₀)

/-- When `A` is unital, `evalKerSubalgebra S A x₀` has the same carrier as Mathlib's maximal-ideal
construction `ContinuousMap.idealOfSet A ({x₀}ᶜ)`. -/
theorem coe_evalKerSubalgebra_eq_idealOfSet [CommSemiring S] [Semiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    (evalKerSubalgebra S A x₀ : Set C(K, A)) = (idealOfSet A ({x₀}ᶜ : Set K) : Set C(K, A)) := by
  ext F
  simp

end EvalKer

section RestrictComplEquiv

variable {K S A : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

variable (S A) in
/-- Restriction to `{x : K // x ≠ x₀}` is a star-algebra isomorphism from
`{F ∈ C(K, A) : F x₀ = 0}` onto `C₀({x : K // x ≠ x₀}, A)`, with inverse given by extension by
zero. -/
noncomputable def restrictComplSingletonStarAlgEquiv [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) :
    evalKerSubalgebra S A x₀ ≃⋆ₐ[S] C₀({x : K // x ≠ x₀}, A) where
  toFun F := F.1.restrictComplSingleton F.2
  invFun g := ⟨g.extendZero, g.extendZero_apply_self⟩
  left_inv F := Subtype.ext <| ZeroAtInftyContinuousMap.extendZero_restrictComplSingleton F.2
  right_inv g := g.restrictComplSingleton_extendZero
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem restrictComplSingletonStarAlgEquiv_apply [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [StarRing A] [ContinuousStar A] [Module S A]
    [ContinuousConstSMul S A] (x₀ : K) (F : evalKerSubalgebra S A x₀)
    (x : {x : K // x ≠ x₀}) :
    restrictComplSingletonStarAlgEquiv S A x₀ F x = F.1 x.1 := (rfl)

@[simp]
theorem coe_restrictComplSingletonStarAlgEquiv_symm_apply [CommSemiring S]
    [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [IsTopologicalSemiring A] [StarRing A]
    [ContinuousStar A] [Module S A] [ContinuousConstSMul S A] (x₀ : K)
    (g : C₀({x : K // x ≠ x₀}, A)) :
    ((restrictComplSingletonStarAlgEquiv S A x₀).symm g : C(K, A)) = g.extendZero := (rfl)

/-- `restrictComplSingletonStarAlgEquiv` preserves the supremum norm. -/
@[simp]
theorem norm_restrictComplSingletonStarAlgEquiv {E : Type*} [CommRing S]
    [NonUnitalSeminormedRing E] [StarRing E] [ContinuousStar E] [Module S E]
    [ContinuousConstSMul S E] (x₀ : K) (F : evalKerSubalgebra S E x₀) :
    ‖restrictComplSingletonStarAlgEquiv S E x₀ F‖ = ‖F‖ :=
  ZeroAtInftyContinuousMap.norm_restrictComplSingleton F.1 F.2

/-- `restrictComplSingletonStarAlgEquiv` is an isometry. -/
theorem isometry_restrictComplSingletonStarAlgEquiv {E : Type*} [CommRing S]
    [NonUnitalSeminormedRing E] [StarRing E] [ContinuousStar E] [Module S E]
    [ContinuousConstSMul S E] (x₀ : K) :
    Isometry (restrictComplSingletonStarAlgEquiv S E x₀) :=
  AddMonoidHomClass.isometry_of_norm (restrictComplSingletonStarAlgEquiv S E x₀)
    (norm_restrictComplSingletonStarAlgEquiv x₀)

/-- When `{x : K // x ≠ x₀}` is compact (equivalently, `x₀` is isolated in `K`),
`restrictComplSingleton` agrees with ordinary subtype restriction lifted through
`ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty`. -/
theorem restrictComplSingleton_eq_liftZeroAtInfty {β : Type*} [TopologicalSpace β] [Zero β]
    {x₀ : K} [CompactSpace {x : K // x ≠ x₀}] (F : C(K, β)) (hF : F x₀ = 0) :
    F.restrictComplSingleton hF =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
        (F.comp ⟨Subtype.val, continuous_subtype_val⟩) := by
  ext x
  simp

end RestrictComplEquiv

end ContinuousMap

end PuncturedCompact
