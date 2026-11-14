/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Extension by zero of functions vanishing at infinity along open embeddings

Given an open embedding `e : X → Y` into an `R₁` space `Y`, every continuous function vanishing at
infinity `f : C₀(X, R)` extends by `0` outside `Set.range e` to a continuous function vanishing at
infinity `ZeroAtInftyContinuousMap.extendByZero he f : C₀(Y, R)`. In the opposite direction, for any
topological embedding `e : X → Y` (with no separation assumption on `Y`), restricting a function
`g : C₀(Y, R)` that vanishes outside `Set.range e` along `e` produces a function
`ZeroAtInftyContinuousMap.restrictOfEqZero he g hg : C₀(X, R)`.

Together these operations identify `C₀(X, R)` isometrically with the subspace of `C₀(Y, R)`
consisting of functions vanishing outside `Set.range e`. Key instances are the inclusions of open
intervals `(0, 1) ↪ (0, 1] ↪ [0, 1]`, which identify the suspension and cone of a normed or
C⋆-algebra with the endpoint-vanishing ideals of the cone and path algebras.

## Main declarations

* `ZeroAtInftyContinuousMap.extendByZero`: extend `f : C₀(X, R)` by `0` outside the range of an
  open embedding `e : X → Y` into an `R₁` space `Y`.
* `ZeroAtInftyContinuousMap.norm_extendByZero` and `ZeroAtInftyContinuousMap.isometry_extendByZero`:
  extension by zero preserves the supremum norm and is an isometry.
* `ZeroAtInftyContinuousMap.restrictOfEqZero`: restrict `g : C₀(Y, R)` vanishing outside
  `Set.range e` along an embedding `e : X → Y` to `C₀(X, R)`.
* `ZeroAtInftyContinuousMap.range_extendByZero`: the range of `extendByZero he` is
  `{g : C₀(Y, R) | ∀ y ∉ Set.range e, g y = 0}`.
-/

public section

open Filter Set Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

section Topological

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]

section Extend

variable [R1Space Y] [Zero R] {e : X → Y}

/-- Extend `f : C₀(X, R)` by `0` outside `Set.range e` along an open embedding `e : X → Y` into an
`R₁` space `Y`. -/
noncomputable def extendByZero (he : IsOpenEmbedding e) (f : C₀(X, R)) : C₀(Y, R) where
  toFun := Function.extend e f (0 : Y → R)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ range e
    · obtain ⟨x, rfl⟩ := hy
      rw [ContinuousAt, he.injective.extend_apply, ← he.map_nhds_eq x, tendsto_map'_iff]
      have hcomp : Function.extend e f (0 : Y → R) ∘ e = f :=
        funext (he.injective.extend_apply f (0 : Y → R))
      rw [hcomp]
      exact f.continuous.tendsto x
    · rw [ContinuousAt, Function.extend_apply' f (0 : Y → R) y hy, Pi.zero_apply, tendsto_def]
      intro V hV
      obtain ⟨K, hK, hKV⟩ := mem_cocompact.mp (zero_at_infty f hV)
      have hKe : IsCompact (e '' K) := hK.image he.continuous
      have hcl : closure (e '' K) ⊆ range e :=
        hKe.closure_subset_of_isOpen he.isOpen_range (image_subset_range e K)
      have hmem : (closure (e '' K))ᶜ ∈ 𝓝 y :=
        isClosed_closure.isOpen_compl.mem_nhds fun hyc => hy (hcl hyc)
      refine mem_of_superset hmem fun z hz => ?_
      by_cases hze : z ∈ range e
      · obtain ⟨x, rfl⟩ := hze
        have hxK : x ∉ K := fun hx => hz (subset_closure (mem_image_of_mem e hx))
        simpa only [mem_preimage, he.injective.extend_apply] using hKV hxK
      · simpa only [mem_preimage, Function.extend_apply' f (0 : Y → R) z hze, Pi.zero_apply]
          using mem_of_mem_nhds hV
  zero_at_infty' := by
    intro V hV
    obtain ⟨K, hK, hKV⟩ := mem_cocompact.mp (zero_at_infty f hV)
    refine mem_cocompact.mpr ⟨e '' K, hK.image he.continuous, fun z hz => ?_⟩
    by_cases hze : z ∈ range e
    · obtain ⟨x, rfl⟩ := hze
      have hxK : x ∉ K := fun hx => hz (mem_image_of_mem e hx)
      simpa only [mem_preimage, he.injective.extend_apply] using hKV hxK
    · simpa only [mem_preimage, Function.extend_apply' f (0 : Y → R) z hze, Pi.zero_apply]
        using mem_of_mem_nhds hV

theorem coe_extendByZero (he : IsOpenEmbedding e) (f : C₀(X, R)) :
    ⇑(extendByZero he f) = Function.extend e f (0 : Y → R) :=
  (rfl)

@[simp]
theorem extendByZero_apply_mem (he : IsOpenEmbedding e) (f : C₀(X, R)) (x : X) :
    extendByZero he f (e x) = f x :=
  he.injective.extend_apply f (0 : Y → R) x

theorem extendByZero_apply_of_notMem (he : IsOpenEmbedding e) (f : C₀(X, R)) {y : Y}
    (hy : y ∉ range e) : extendByZero he f y = 0 :=
  Function.extend_apply' f (0 : Y → R) y hy

theorem extendByZero_injective (he : IsOpenEmbedding e) :
    Function.Injective (extendByZero (R := R) he) := fun f g h =>
  ext fun x => by
    rw [← extendByZero_apply_mem he f x, ← extendByZero_apply_mem he g x, h]

@[simp]
theorem extendByZero_inj (he : IsOpenEmbedding e) {f g : C₀(X, R)} :
    extendByZero he f = extendByZero he g ↔ f = g :=
  (extendByZero_injective he).eq_iff

@[simp]
theorem extendByZero_zero (he : IsOpenEmbedding e) :
    extendByZero he (0 : C₀(X, R)) = 0 := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [extendByZero_apply_of_notMem he _ hy]

@[simp]
theorem extendByZero_eq_zero_iff (he : IsOpenEmbedding e) {f : C₀(X, R)} :
    extendByZero he f = 0 ↔ f = 0 := by
  rw [← extendByZero_zero he, extendByZero_inj]

end Extend

section Restrict

variable [Zero R] {e : X → Y}

/-- Restrict `g : C₀(Y, R)` vanishing outside `Set.range e` along an embedding `e : X → Y` to
`C₀(X, R)`. -/
def restrictOfEqZero (he : IsEmbedding e) (g : C₀(Y, R)) (hg : ∀ y ∉ range e, g y = 0) :
    C₀(X, R) where
  toFun x := g (e x)
  continuous_toFun := g.continuous.comp he.continuous
  zero_at_infty' := by
    rw [(nhds_basis_opens (0 : R)).tendsto_right_iff]
    rintro V ⟨hV0, hVopen⟩
    obtain ⟨K, hK, hKV⟩ := mem_cocompact.mp (zero_at_infty g (hVopen.mem_nhds hV0))
    have hclosed : IsClosed (g ⁻¹' V)ᶜ := (hVopen.preimage g.continuous).isClosed_compl
    have hsubK : (g ⁻¹' V)ᶜ ⊆ K := compl_subset_comm.mp hKV
    have hC_compact : IsCompact (g ⁻¹' V)ᶜ := hK.of_isClosed_subset hclosed hsubK
    have hC_range : (g ⁻¹' V)ᶜ ⊆ range e := fun y hy => by
      by_contra hye
      exact hy (by simpa only [mem_preimage, hg y hye] using hV0)
    have hpre_compact : IsCompact (e ⁻¹' (g ⁻¹' V)ᶜ) :=
      he.isCompact_iff.mpr (by rwa [image_preimage_eq_of_subset hC_range])
    exact mem_cocompact.mpr ⟨e ⁻¹' (g ⁻¹' V)ᶜ, hpre_compact, fun x hx => not_not.mp hx⟩

@[simp]
theorem restrictOfEqZero_apply (he : IsEmbedding e) (g : C₀(Y, R))
    (hg : ∀ y ∉ range e, g y = 0) (x : X) :
    restrictOfEqZero he g hg x = g (e x) :=
  (rfl)

@[simp]
theorem restrictOfEqZero_zero (he : IsEmbedding e) :
    restrictOfEqZero he (0 : C₀(Y, R)) (fun _ _ => rfl) = 0 := by
  ext
  rfl

@[simp]
theorem restrictOfEqZero_extendByZero [R1Space Y] (he : IsOpenEmbedding e) (f : C₀(X, R)) :
    restrictOfEqZero he.isEmbedding (extendByZero he f)
      (fun _ hy => extendByZero_apply_of_notMem he f hy) = f := by
  ext x
  exact extendByZero_apply_mem he f x

@[simp]
theorem extendByZero_restrictOfEqZero [R1Space Y] (he : IsOpenEmbedding e) (g : C₀(Y, R))
    (hg : ∀ y ∉ range e, g y = 0) :
    extendByZero he (restrictOfEqZero he.isEmbedding g hg) = g := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    exact extendByZero_apply_mem he _ x
  · rw [extendByZero_apply_of_notMem he _ hy, hg y hy]

theorem range_extendByZero [R1Space Y] (he : IsOpenEmbedding e) :
    range (extendByZero (R := R) he) = {g : C₀(Y, R) | ∀ y ∉ range e, g y = 0} := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩ _ hy
    exact extendByZero_apply_of_notMem he f hy
  · intro hg
    exact ⟨restrictOfEqZero he.isEmbedding g hg, extendByZero_restrictOfEqZero he g hg⟩

end Restrict

section Algebraic

variable [R1Space Y] {e : X → Y}

@[simp]
theorem extendByZero_add [AddZeroClass R] [ContinuousAdd R] (he : IsOpenEmbedding e)
    (f g : C₀(X, R)) :
    extendByZero he (f + g) = extendByZero he f + extendByZero he g := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [extendByZero_apply_of_notMem he _ hy]

@[simp]
theorem extendByZero_neg [AddGroup R] [IsTopologicalAddGroup R] (he : IsOpenEmbedding e)
    (f : C₀(X, R)) :
    extendByZero he (-f) = -extendByZero he f := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [extendByZero_apply_of_notMem he _ hy]

@[simp]
theorem extendByZero_sub [AddGroup R] [IsTopologicalAddGroup R] (he : IsOpenEmbedding e)
    (f g : C₀(X, R)) :
    extendByZero he (f - g) = extendByZero he f - extendByZero he g := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [extendByZero_apply_of_notMem he _ hy]

@[simp]
theorem extendByZero_mul [MulZeroClass R] [ContinuousMul R] (he : IsOpenEmbedding e)
    (f g : C₀(X, R)) :
    extendByZero he (f * g) = extendByZero he f * extendByZero he g := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [extendByZero_apply_of_notMem he _ hy]

@[simp]
theorem extendByZero_smul {S : Type*} [Zero R] [SMulZeroClass S R] [ContinuousConstSMul S R]
    (he : IsOpenEmbedding e) (c : S) (f : C₀(X, R)) :
    extendByZero he (c • f) = c • extendByZero he f := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [extendByZero_apply_of_notMem he _ hy]

@[simp]
theorem extendByZero_star [AddMonoid R] [StarAddMonoid R] [ContinuousStar R]
    (he : IsOpenEmbedding e) (f : C₀(X, R)) :
    extendByZero he (star f) = star (extendByZero he f) := by
  ext y
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · simp [extendByZero_apply_of_notMem he _ hy]

end Algebraic

end Topological

section Normed

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SeminormedAddCommGroup E]
  {e : X → Y}

@[simp]
theorem norm_extendByZero [R1Space Y] (he : IsOpenEmbedding e) (f : C₀(X, E)) :
    ‖extendByZero he f‖ = ‖f‖ := by
  refine le_antisymm ((norm_le (norm_nonneg f)).mpr fun y => ?_)
    ((norm_le (norm_nonneg _)).mpr fun x => by
      simpa only [extendByZero_apply_mem] using norm_coe_le_norm (extendByZero he f) (e x))
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simpa only [extendByZero_apply_mem] using norm_coe_le_norm f x
  · simp [extendByZero_apply_of_notMem he f hy]

theorem isometry_extendByZero [R1Space Y] (he : IsOpenEmbedding e) :
    Isometry (extendByZero (R := E) he) :=
  Isometry.of_dist_eq fun f g => by
    rw [dist_eq_norm, dist_eq_norm, ← extendByZero_sub, norm_extendByZero]

@[simp]
theorem norm_restrictOfEqZero (he : IsEmbedding e) (g : C₀(Y, E)) (hg : ∀ y ∉ range e, g y = 0) :
    ‖restrictOfEqZero he g hg‖ = ‖g‖ := by
  refine le_antisymm ((norm_le (norm_nonneg g)).mpr fun x => norm_coe_le_norm g (e x))
    ((norm_le (norm_nonneg _)).mpr fun y => ?_)
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    exact norm_coe_le_norm (restrictOfEqZero he g hg) x
  · simp [hg y hy]

end Normed

end ZeroAtInftyContinuousMap
