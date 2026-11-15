/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Continuous functions vanishing at infinity on punctured compact Hausdorff spaces

For a compact Hausdorff space `K` and a basepoint `x₀ : K`, the punctured space `({x₀}ᶜ : Set K)` is
locally compact Hausdorff and embeds into `K` with complement `{x₀}`, identifying `K` with the
one-point compactification `OnePoint ({x₀}ᶜ : Set K)` via
`OnePoint.equivOfIsEmbeddingOfRangeEq`. Consequently, the cocompact filter on `({x₀}ᶜ : Set K)` is
the pullback of `𝓝 x₀`, and extending by `0` at `x₀` identifies `C₀(({x₀}ᶜ : Set K), E)`
isometrically and `⋆`-isomorphically with the hyperplane `{F : C(K, E) | F x₀ = 0}` of continuous
functions on `K` vanishing at `x₀`.

This punctured-compact identification is the topological core of nonunital Gelfand duality: for a
nonunital commutative C⋆-algebra `A`, the character space of the minimal unitization `A⁺¹` is a
compact Hausdorff space with a canonical scalar-projection character, and `A` is identified with the
continuous functions on `characterSpace ℂ A⁺¹` vanishing at that point.

## Main declarations

* `TauCeti.cocompact_compl_singleton` and `TauCeti.tendsto_cocompact_compl_singleton_iff`: in a
  compact Hausdorff space `K`, `cocompact ({x₀}ᶜ : Set K) = Filter.comap Subtype.val (𝓝 x₀)`, so a
  map on `{x₀}ᶜ` vanishes at infinity if and only if it tends to `0` along `𝓝 x₀`.
* `TauCeti.isOpen_singleton_iff_compactSpace_compl`: `{x₀}` is open in a compact Hausdorff space `K`
  if and only if `({x₀}ᶜ : Set K)` is compact.
* `ContinuousMap.restrictComplSingleton`: restricts `F : C(K, E)` with `F x₀ = 0` on compact `K` to
  `C₀(({x₀}ᶜ : Set K), E)` without altering its supremum norm.
* `ZeroAtInftyContinuousMap.extendComplSingleton`: extends `f : C₀(({x₀}ᶜ : Set K), E)` on compact
  Hausdorff `K` by `0` at `x₀` to `C(K, E)`, together with bundled homomorphisms
  `extendComplSingletonLinearIsometry`, `extendComplSingletonNonUnitalAlgHom`, and
  `extendComplSingletonNonUnitalStarAlgHom`.
* `ContinuousMap.kerEvalCLMLinearIsometryEquiv`: the linear isometry equivalence
  `(ContinuousMap.evalCLM R x₀).ker ≃ₗᵢ[R] C₀(({x₀}ᶜ : Set K), E)`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.2.2.
* G. J. Murphy, *C*-Algebras and Operator Theory*, §2.1.
* Built on Mathlib's `OnePoint.equivOfIsEmbeddingOfRangeEq`
  (`Mathlib.Topology.Compactification.OnePoint.Basic`), `ZeroAtInftyContinuousMap.toOnePoint`
  (`Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization`), and `ContinuousMap.idealOfSet`
  (`Mathlib.Topology.ContinuousMap.Ideals`).
-/

public section

open Filter Topology OnePoint
open scoped ZeroAtInfty

namespace TauCeti

section Filter

variable {K : Type*} [TopologicalSpace K]

/-- In a compact space `K`, the cocompact filter on the punctured space `({x₀}ᶜ : Set K)` is bounded
above by the pullback of `𝓝 x₀`. -/
theorem cocompact_compl_singleton_le [CompactSpace K] (x₀ : K) :
    cocompact ({x₀}ᶜ : Set K) ≤ Filter.comap (Subtype.val : ({x₀}ᶜ : Set K) → K) (𝓝 x₀) := by
  intro s hs
  obtain ⟨u, hu, hus⟩ := Filter.mem_comap.mp hs
  obtain ⟨v, hvu, hv_open, hx₀v⟩ := mem_nhds_iff.mp hu
  refine Filter.mem_cocompact.mpr ⟨Subtype.val ⁻¹' vᶜ, ?_, ?_⟩
  · rw [IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe]
    have hv_sub : vᶜ ⊆ ({x₀}ᶜ : Set K) :=
      Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx₀v)
    rw [Set.inter_eq_right.mpr hv_sub]
    exact hv_open.isClosed_compl.isCompact
  · exact (Set.preimage_mono (compl_compl v ▸ hvu)).trans hus

/-- In a compact Hausdorff space `K`, the cocompact filter on the punctured space `({x₀}ᶜ : Set K)`
coincides with the pullback of `𝓝 x₀` along the subtype inclusion. -/
theorem cocompact_compl_singleton [CompactSpace K] [T2Space K] (x₀ : K) :
    cocompact ({x₀}ᶜ : Set K) = Filter.comap (Subtype.val : ({x₀}ᶜ : Set K) → K) (𝓝 x₀) := by
  refine le_antisymm (cocompact_compl_singleton_le x₀) ?_
  intro s hs
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp hs
  have ht_closed : IsClosed (Subtype.val '' t) := (ht.image continuous_subtype_val).isClosed
  have hx₀ : x₀ ∉ Subtype.val '' t := by
    rintro ⟨⟨y, hy⟩, _, hyx₀⟩
    exact hy hyx₀
  refine Filter.mem_comap.mpr ⟨(Subtype.val '' t)ᶜ, ht_closed.isOpen_compl.mem_nhds hx₀, ?_⟩
  rw [Set.preimage_compl, Subtype.val_injective.preimage_image]
  exact hts

/-- On the complement of a point `x₀` in a compact Hausdorff space `K`, convergence along the
cocompact filter is equivalent to convergence along the pullback of `𝓝 x₀`. -/
theorem tendsto_cocompact_compl_singleton_iff {α : Type*} [CompactSpace K] [T2Space K]
    {x₀ : K} {f : ({x₀}ᶜ : Set K) → α} {l : Filter α} :
    Tendsto f (cocompact ({x₀}ᶜ : Set K)) l ↔
      Tendsto f (Filter.comap (Subtype.val : ({x₀}ᶜ : Set K) → K) (𝓝 x₀)) l := by
  rw [cocompact_compl_singleton x₀]

/-- A singleton `{x₀}` in a compact Hausdorff space `K` is open (that is, `x₀` is isolated) if and
only if its complement `({x₀}ᶜ : Set K)` is compact. -/
theorem isOpen_singleton_iff_compactSpace_compl [CompactSpace K] [T2Space K] (x₀ : K) :
    IsOpen ({x₀} : Set K) ↔ CompactSpace ({x₀}ᶜ : Set K) := by
  rw [← isCompact_iff_compactSpace (s := ({x₀}ᶜ : Set K)), ← isClosed_compl_iff]
  exact ⟨IsClosed.isCompact, IsCompact.isClosed⟩

end Filter

end TauCeti

namespace ContinuousMap

section RestrictComplSingleton

variable {S K E : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Restrict a continuous map `F : C(K, E)` on a compact space `K` that vanishes at `x₀` to a
continuous map vanishing at infinity on `({x₀}ᶜ : Set K)`. -/
def restrictComplSingleton [TopologicalSpace E] [Zero E] (F : C(K, E)) {x₀ : K} (hF : F x₀ = 0) :
    C₀(({x₀}ᶜ : Set K), E) where
  toFun y := F y
  continuous_toFun := F.continuous.comp continuous_subtype_val
  zero_at_infty' := by
    have hlim : Tendsto (fun y : ({x₀}ᶜ : Set K) => F y)
        (Filter.comap Subtype.val (𝓝 x₀)) (𝓝 0) :=
      hF ▸ (F.continuous.tendsto x₀).comp tendsto_comap
    exact hlim.mono_left (TauCeti.cocompact_compl_singleton_le x₀)

@[simp]
theorem restrictComplSingleton_apply [TopologicalSpace E] [Zero E] (F : C(K, E)) {x₀ : K}
    (hF : F x₀ = 0) (y : ({x₀}ᶜ : Set K)) :
    F.restrictComplSingleton hF y = F y := (rfl)

@[simp]
theorem restrictComplSingleton_zero [TopologicalSpace E] [Zero E] (x₀ : K) :
    (0 : C(K, E)).restrictComplSingleton (x₀ := x₀) rfl = 0 := by
  ext
  rfl

@[simp]
theorem restrictComplSingleton_add [TopologicalSpace E] [AddZeroClass E] [ContinuousAdd E]
    (F G : C(K, E)) {x₀ : K} (hF : F x₀ = 0) (hG : G x₀ = 0) :
    (F + G).restrictComplSingleton (by simp [hF, hG]) =
      F.restrictComplSingleton hF + G.restrictComplSingleton hG := by
  ext
  rfl

@[simp]
theorem restrictComplSingleton_neg [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E]
    (F : C(K, E)) {x₀ : K} (hF : F x₀ = 0) :
    (-F).restrictComplSingleton (by simp [hF]) = -F.restrictComplSingleton hF := by
  ext
  rfl

@[simp]
theorem restrictComplSingleton_sub [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E]
    (F G : C(K, E)) {x₀ : K} (hF : F x₀ = 0) (hG : G x₀ = 0) :
    (F - G).restrictComplSingleton (by simp [hF, hG]) =
      F.restrictComplSingleton hF - G.restrictComplSingleton hG := by
  ext
  rfl

@[simp]
theorem restrictComplSingleton_smul [TopologicalSpace E] [Zero E] [SMulZeroClass S E]
    [ContinuousConstSMul S E] (c : S) (F : C(K, E)) {x₀ : K} (hF : F x₀ = 0) :
    (c • F).restrictComplSingleton (by simp [hF]) = c • F.restrictComplSingleton hF := by
  ext
  rfl

@[simp]
theorem restrictComplSingleton_mul [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E]
    (F G : C(K, E)) {x₀ : K} (hF : F x₀ = 0) (hG : G x₀ = 0) :
    (F * G).restrictComplSingleton (by simp [hF]) =
      F.restrictComplSingleton hF * G.restrictComplSingleton hG := by
  ext
  rfl

@[simp]
theorem restrictComplSingleton_star [TopologicalSpace E] [AddMonoid E] [StarAddMonoid E]
    [ContinuousStar E] (F : C(K, E)) {x₀ : K} (hF : F x₀ = 0) :
    (star F).restrictComplSingleton (by simp [hF]) = star (F.restrictComplSingleton hF) := by
  ext
  rfl

/-- Restricting `F : C(K, E)` with `F x₀ = 0` to `C₀(({x₀}ᶜ : Set K), E)` preserves the supremum
norm, including when `{x₀}ᶜ` is empty. -/
@[simp]
theorem norm_restrictComplSingleton [SeminormedAddCommGroup E] (F : C(K, E)) {x₀ : K}
    (hF : F x₀ = 0) : ‖F.restrictComplSingleton hF‖ = ‖F‖ := by
  refine le_antisymm
    ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg F)).2 fun y => F.norm_coe_le_norm y) ?_
  refine (F.norm_le (norm_nonneg _)).2 fun x => ?_
  by_cases hx : x = x₀
  · simp [hx, hF]
  · exact (F.restrictComplSingleton hF).norm_coe_le_norm ⟨x, hx⟩

end RestrictComplSingleton

end ContinuousMap

namespace ZeroAtInftyContinuousMap

section ExtendComplSingleton

variable {S K E : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] {x₀ : K}

/-- Extend `f : C₀(({x₀}ᶜ : Set K), E)` on the complement of a point `x₀` in a compact Hausdorff
space `K` to a continuous map on `K` taking the value `0` at `x₀`. -/
noncomputable def extendComplSingleton [TopologicalSpace E] [Zero E]
    (f : C₀(({x₀}ᶜ : Set K), E)) : C(K, E) :=
  f.toOnePoint.comp
    ((OnePoint.equivOfIsEmbeddingOfRangeEq x₀ (Subtype.val : ({x₀}ᶜ : Set K) → K)
      IsEmbedding.subtypeVal Subtype.range_coe).symm : C(K, OnePoint ({x₀}ᶜ : Set K)))

@[simp]
theorem extendComplSingleton_apply_self [TopologicalSpace E] [Zero E]
    (f : C₀(({x₀}ᶜ : Set K), E)) : f.extendComplSingleton x₀ = 0 := by
  let e := OnePoint.equivOfIsEmbeddingOfRangeEq x₀ (Subtype.val : ({x₀}ᶜ : Set K) → K)
    IsEmbedding.subtypeVal Subtype.range_coe
  have he : e.symm x₀ = ∞ := e.symm_apply_eq.mpr
    (OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty x₀ (Subtype.val : ({x₀}ᶜ : Set K) → K)
      IsEmbedding.subtypeVal Subtype.range_coe).symm
  rw [extendComplSingleton, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, he,
    toOnePoint_infty]

@[simp]
theorem extendComplSingleton_apply_coe [TopologicalSpace E] [Zero E]
    (f : C₀(({x₀}ᶜ : Set K), E)) (y : ({x₀}ᶜ : Set K)) :
    f.extendComplSingleton y = f y := by
  let e := OnePoint.equivOfIsEmbeddingOfRangeEq x₀ (Subtype.val : ({x₀}ᶜ : Set K) → K)
    IsEmbedding.subtypeVal Subtype.range_coe
  have he : e.symm (y : K) = (y : OnePoint ({x₀}ᶜ : Set K)) := e.symm_apply_eq.mpr
    (OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe x₀ (Subtype.val : ({x₀}ᶜ : Set K) → K)
      IsEmbedding.subtypeVal Subtype.range_coe y).symm
  rw [extendComplSingleton, ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, he, toOnePoint_coe]

theorem extendComplSingleton_apply_of_ne [TopologicalSpace E] [Zero E]
    (f : C₀(({x₀}ᶜ : Set K), E)) {x : K} (hx : x ≠ x₀) :
    f.extendComplSingleton x = f ⟨x, hx⟩ :=
  f.extendComplSingleton_apply_coe ⟨x, hx⟩

/-- Every `f : C₀(({x₀}ᶜ : Set K), E)` tends to `0` as the argument approaches `x₀` in `K`. -/
theorem tendsto_comap_nhds_zero [TopologicalSpace E] [Zero E]
    (f : C₀(({x₀}ᶜ : Set K), E)) :
    Tendsto f (Filter.comap (Subtype.val : ({x₀}ᶜ : Set K) → K) (𝓝 x₀)) (𝓝 0) :=
  (TauCeti.tendsto_cocompact_compl_singleton_iff).mp (zero_at_infty f)

@[simp]
theorem restrictComplSingleton_extendComplSingleton [TopologicalSpace E] [Zero E]
    (f : C₀(({x₀}ᶜ : Set K), E)) :
    f.extendComplSingleton.restrictComplSingleton f.extendComplSingleton_apply_self = f := by
  ext y
  simp

@[simp]
theorem _root_.ContinuousMap.extendComplSingleton_restrictComplSingleton
    [TopologicalSpace E] [Zero E] (F : C(K, E)) (hF : F x₀ = 0) :
    (F.restrictComplSingleton hF).extendComplSingleton = F := by
  ext x
  by_cases hx : x = x₀
  · rw [hx, extendComplSingleton_apply_self, hF]
  · exact ((F.restrictComplSingleton hF).extendComplSingleton_apply_of_ne hx).trans rfl

theorem extendComplSingleton_injective [TopologicalSpace E] [Zero E] :
    Function.Injective (extendComplSingleton (K := K) (E := E) (x₀ := x₀)) := by
  intro f g h
  ext y
  simpa using congrArg (fun F : C(K, E) => F y) h

@[simp]
theorem exists_extendComplSingleton_eq [TopologicalSpace E] [Zero E] {F : C(K, E)} :
    (∃ f : C₀(({x₀}ᶜ : Set K), E), f.extendComplSingleton = F) ↔ F x₀ = 0 :=
  ⟨fun ⟨f, hf⟩ => hf ▸ f.extendComplSingleton_apply_self,
    fun hF => ⟨F.restrictComplSingleton hF, F.extendComplSingleton_restrictComplSingleton hF⟩⟩

theorem range_extendComplSingleton [TopologicalSpace E] [Zero E] :
    Set.range (extendComplSingleton (K := K) (E := E) (x₀ := x₀)) = {F : C(K, E) | F x₀ = 0} :=
  Set.ext fun _ => Set.mem_range.trans exists_extendComplSingleton_eq

@[simp]
theorem extendComplSingleton_zero [TopologicalSpace E] [Zero E] :
    (0 : C₀(({x₀}ᶜ : Set K), E)).extendComplSingleton = 0 := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp [extendComplSingleton_apply_of_ne _ hx]

@[simp]
theorem extendComplSingleton_add [TopologicalSpace E] [AddZeroClass E] [ContinuousAdd E]
    (f g : C₀(({x₀}ᶜ : Set K), E)) :
    (f + g).extendComplSingleton = f.extendComplSingleton + g.extendComplSingleton := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp [extendComplSingleton_apply_of_ne _ hx]

@[simp]
theorem extendComplSingleton_neg [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E]
    (f : C₀(({x₀}ᶜ : Set K), E)) :
    (-f).extendComplSingleton = -f.extendComplSingleton := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp [extendComplSingleton_apply_of_ne _ hx]

@[simp]
theorem extendComplSingleton_sub [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E]
    (f g : C₀(({x₀}ᶜ : Set K), E)) :
    (f - g).extendComplSingleton = f.extendComplSingleton - g.extendComplSingleton := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp [extendComplSingleton_apply_of_ne _ hx]

@[simp]
theorem extendComplSingleton_smul [TopologicalSpace E] [Zero E] [SMulZeroClass S E]
    [ContinuousConstSMul S E] (c : S) (f : C₀(({x₀}ᶜ : Set K), E)) :
    (c • f).extendComplSingleton = c • f.extendComplSingleton := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp [extendComplSingleton_apply_of_ne _ hx]

@[simp]
theorem extendComplSingleton_mul [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E]
    (f g : C₀(({x₀}ᶜ : Set K), E)) :
    (f * g).extendComplSingleton = f.extendComplSingleton * g.extendComplSingleton := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp [extendComplSingleton_apply_of_ne _ hx]

@[simp]
theorem extendComplSingleton_star [TopologicalSpace E] [AddMonoid E] [StarAddMonoid E]
    [ContinuousStar E] (f : C₀(({x₀}ᶜ : Set K), E)) :
    (star f).extendComplSingleton = star f.extendComplSingleton := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simp [extendComplSingleton_apply_of_ne _ hx]

/-- Extending `f : C₀(({x₀}ᶜ : Set K), E)` by `0` at `x₀` preserves the supremum norm. -/
@[simp]
theorem norm_extendComplSingleton [SeminormedAddCommGroup E] (f : C₀(({x₀}ᶜ : Set K), E)) :
    ‖f.extendComplSingleton‖ = ‖f‖ := by
  simpa using (f.extendComplSingleton.norm_restrictComplSingleton
    f.extendComplSingleton_apply_self).symm

theorem isometry_extendComplSingleton [SeminormedAddCommGroup E] :
    Isometry (extendComplSingleton (K := K) (E := E) (x₀ := x₀)) :=
  AddMonoidHomClass.isometry_of_norm
    (⟨⟨extendComplSingleton, extendComplSingleton_zero⟩, extendComplSingleton_add⟩ :
      C₀(({x₀}ᶜ : Set K), E) →+ C(K, E))
    norm_extendComplSingleton

variable (S K E)

/-- `ZeroAtInftyContinuousMap.extendComplSingleton` bundled as a linear isometry into `C(K, E)`. -/
noncomputable def extendComplSingletonLinearIsometry [Semiring S] [SeminormedAddCommGroup E]
    [Module S E] [ContinuousConstSMul S E] (x₀ : K) :
    C₀(({x₀}ᶜ : Set K), E) →ₗᵢ[S] C(K, E) where
  toFun := extendComplSingleton
  map_add' := extendComplSingleton_add
  map_smul' := extendComplSingleton_smul
  norm_map' := norm_extendComplSingleton

@[simp]
theorem coe_extendComplSingletonLinearIsometry [Semiring S] [SeminormedAddCommGroup E]
    [Module S E] [ContinuousConstSMul S E] (x₀ : K) :
    ⇑(extendComplSingletonLinearIsometry S K E x₀) = extendComplSingleton := (rfl)

/-- `ZeroAtInftyContinuousMap.extendComplSingleton` bundled as a nonunital algebra homomorphism into
`C(K, E)`. -/
noncomputable def extendComplSingletonNonUnitalAlgHom [Semiring S] [TopologicalSpace E]
    [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E] [Module S E] [ContinuousConstSMul S E]
    (x₀ : K) : C₀(({x₀}ᶜ : Set K), E) →ₙₐ[S] C(K, E) where
  toFun := extendComplSingleton
  map_smul' := extendComplSingleton_smul
  map_zero' := extendComplSingleton_zero
  map_add' := extendComplSingleton_add
  map_mul' := extendComplSingleton_mul

@[simp]
theorem coe_extendComplSingletonNonUnitalAlgHom [Semiring S] [TopologicalSpace E]
    [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E] [Module S E] [ContinuousConstSMul S E]
    (x₀ : K) :
    ⇑(extendComplSingletonNonUnitalAlgHom S K E x₀) = extendComplSingleton := (rfl)

/-- The range of `extendComplSingletonNonUnitalAlgHom` has the same underlying set as Mathlib's
closed ideal `ContinuousMap.idealOfSet E ({x₀}ᶜ : Set K)`. -/
theorem coe_range_extendComplSingletonNonUnitalAlgHom_eq_idealOfSet [CommSemiring S]
    [TopologicalSpace E] [Semiring E] [IsTopologicalSemiring E] [Module S E]
    [ContinuousConstSMul S E] (x₀ : K) :
    ((extendComplSingletonNonUnitalAlgHom S K E x₀).range : Set C(K, E)) =
      ContinuousMap.idealOfSet E ({x₀}ᶜ : Set K) := by
  ext F
  rw [SetLike.mem_coe, NonUnitalAlgHom.mem_range]
  simp

/-- `ZeroAtInftyContinuousMap.extendComplSingleton` bundled as a nonunital `⋆`-algebra homomorphism
into `C(K, E)`. -/
noncomputable def extendComplSingletonNonUnitalStarAlgHom [Semiring S] [TopologicalSpace E]
    [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E] [Module S E] [ContinuousConstSMul S E]
    [StarRing E] [ContinuousStar E] (x₀ : K) :
    C₀(({x₀}ᶜ : Set K), E) →⋆ₙₐ[S] C(K, E) where
  __ := extendComplSingletonNonUnitalAlgHom S K E x₀
  map_star' := extendComplSingleton_star

@[simp]
theorem coe_extendComplSingletonNonUnitalStarAlgHom [Semiring S] [TopologicalSpace E]
    [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E] [Module S E] [ContinuousConstSMul S E]
    [StarRing E] [ContinuousStar E] (x₀ : K) :
    ⇑(extendComplSingletonNonUnitalStarAlgHom S K E x₀) = extendComplSingleton := (rfl)

theorem mem_range_extendComplSingletonNonUnitalStarAlgHom [CommSemiring S] [TopologicalSpace E]
    [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E] [Module S E] [ContinuousConstSMul S E]
    [StarRing E] [ContinuousStar E] (x₀ : K) {F : C(K, E)} :
    F ∈ (extendComplSingletonNonUnitalStarAlgHom S K E x₀).range ↔ F x₀ = 0 := by
  rw [NonUnitalStarAlgHom.mem_range]
  simp

end ExtendComplSingleton

end ZeroAtInftyContinuousMap

namespace ContinuousMap

section KerEvalCLM

variable (R K E : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [Ring R] [SeminormedAddCommGroup E] [Module R E] [ContinuousConstSMul R E]

/-- The linear isometry equivalence identifying the kernel of point evaluation
`ContinuousMap.evalCLM R x₀ : C(K, E) →L[R] E` with `C₀(({x₀}ᶜ : Set K), E)`. -/
noncomputable def kerEvalCLMLinearIsometryEquiv (x₀ : K) :
    (ContinuousMap.evalCLM R (α := K) (M := E) x₀).ker ≃ₗᵢ[R] C₀(({x₀}ᶜ : Set K), E) where
  toFun F := F.1.restrictComplSingleton F.2
  invFun f := ⟨f.extendComplSingleton, f.extendComplSingleton_apply_self⟩
  left_inv F := Subtype.ext (F.1.extendComplSingleton_restrictComplSingleton F.2)
  right_inv f := f.restrictComplSingleton_extendComplSingleton
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' F := F.1.norm_restrictComplSingleton F.2

@[simp]
theorem kerEvalCLMLinearIsometryEquiv_apply
    (x₀ : K) (F : (ContinuousMap.evalCLM R (α := K) (M := E) x₀).ker)
    (y : ({x₀}ᶜ : Set K)) :
    kerEvalCLMLinearIsometryEquiv R K E x₀ F y = F.1 y := (rfl)

@[simp]
theorem kerEvalCLMLinearIsometryEquiv_symm_coe
    (x₀ : K) (f : C₀(({x₀}ᶜ : Set K), E)) :
    ((kerEvalCLMLinearIsometryEquiv R K E x₀).symm f : C(K, E)) = f.extendComplSingleton := (rfl)

end KerEvalCLM

end ContinuousMap
