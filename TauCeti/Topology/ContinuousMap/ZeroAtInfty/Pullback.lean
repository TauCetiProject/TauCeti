/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Character
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Pullbacks of `C₀` into bounded continuous functions

Precomposition along a continuous map `h : C(X, Y)` defines a non-unital `⋆`-algebra homomorphism
`ContinuousMap.compZeroAtInftyToBCF : C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A)` without requiring `h` to be
proper.

When `𝕜` is an `RCLike` field and `Y` is weakly locally compact Hausdorff, every
pointwise-nonvanishing `⋆`-homomorphism `φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)` induces a nonzero
character `f ↦ φ f x` at each `x : X`. By
`ZeroAtInftyContinuousMap.existsUnique_eq_evalNonUnitalAlgHom`, these characters recover a unique
continuous map `h : C(X, Y)` with `φ f = f ∘ h`, establishing the bijection
`ContinuousMap.bcfMorphismEquiv`.

Finally, when `Y` is weakly locally compact Hausdorff and `A` is nontrivial, `h` is proper if and
only if `f ∘ h` vanishes at infinity for every `f : C₀(Y, A)`
(`ContinuousMap.isProperMap_iff_forall_tendsto_cocompact_nhds_zero`), equivalently if and only if
`h.compZeroAtInftyToBCF 𝕜 A` lands in the canonical image of `C₀(X, A)` inside `X →ᵇ A`
(`ContinuousMap.isProperMap_iff_range_compZeroAtInftyToBCF_subset`).

## Main definitions

* `ContinuousMap.compZeroAtInftyToBCF`: pullback `C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A)` along `h : C(X, Y)`.
* `ContinuousMap.bcfMorphismEquiv`: bijection between `C(X, Y)` and pointwise-nonvanishing
  `⋆`-homomorphisms `C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)`.

## Main results

* `ContinuousMap.compZeroAtInftyToBCF_id`: pullback along the identity is
  `ZeroAtInftyContinuousMap.toBCFNonUnitalStarAlgHom`.
* `ContinuousMap.isProperMap_iff_forall_tendsto_cocompact_nhds_zero`,
  `ContinuousMap.isProperMap_iff_range_compZeroAtInftyToBCF_subset`: characterizations of proper
  continuous maps via pullbacks of `C₀(Y, A)`.

## References

* E. Christopher Lance, *Hilbert C*-Modules*, Chapter 2.
* Dana P. Williams, *Crossed Products of C*-Algebras*, Section 2.3.
-/

public section

noncomputable section

open Filter Topology
open scoped BoundedContinuousFunction ZeroAtInfty

namespace ContinuousMap

section ToBCF

variable {𝕜 X Y A : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [SeminormedRing 𝕜] [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A]
  [Module 𝕜 A] [IsBoundedSMul 𝕜 A]

variable (𝕜 A) in
/-- Precomposition by a continuous map `h : C(X, Y)` defines a non-unital `⋆`-algebra homomorphism
`C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A)`. -/
def compZeroAtInftyToBCF (h : C(X, Y)) : C₀(Y, A) →⋆ₙₐ[𝕜] (X →ᵇ A) where
  toFun f := f.toBCF.compContinuous h
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- Applying `compZeroAtInftyToBCF` precomposes `f.toBCF` with `h`. -/
@[simp]
theorem compZeroAtInftyToBCF_apply (h : C(X, Y)) (f : C₀(Y, A)) :
    h.compZeroAtInftyToBCF 𝕜 A f = f.toBCF.compContinuous h :=
  (rfl)

/-- Pullback along the identity map is the canonical inclusion `C₀(X, A) →⋆ₙₐ[𝕜] (X →ᵇ A)`. -/
@[simp]
theorem compZeroAtInftyToBCF_id :
    (ContinuousMap.id X).compZeroAtInftyToBCF 𝕜 A =
      ZeroAtInftyContinuousMap.toBCFNonUnitalStarAlgHom 𝕜 X A := by
  ext f x
  simp

end ToBCF

section CharacterRecovery

variable {𝕜 X Y : Type*} [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]

/-- Pointwise evaluation character `f ↦ φ f x` associated with `φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)`. -/
private def evalChar (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) (x : X) : C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜 where
  toFun f := φ f x
  map_smul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp

private theorem evalChar_ne_zero (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) (hφ : ∀ x, ∃ f, φ f x ≠ 0)
    (x : X) : evalChar φ x ≠ 0 := by
  intro hev
  obtain ⟨f, hf⟩ := hφ x
  exact hf (congr($hev f))

variable [WeaklyLocallyCompactSpace Y] [T2Space Y]

private def recoverFun (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) (hφ : ∀ x, ∃ f, φ f x ≠ 0) (x : X) :
    Y :=
  (ZeroAtInftyContinuousMap.existsUnique_eq_evalNonUnitalAlgHom
    (evalChar φ x) (evalChar_ne_zero φ hφ x)).choose

private theorem recoverFun_eq (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) (hφ : ∀ x, ∃ f, φ f x ≠ 0)
    (x : X) :
    evalChar φ x = ZeroAtInftyContinuousMap.evalNonUnitalAlgHom 𝕜 (recoverFun φ hφ x) :=
  (ZeroAtInftyContinuousMap.existsUnique_eq_evalNonUnitalAlgHom
    (evalChar φ x) (evalChar_ne_zero φ hφ x)).choose_spec.1

private theorem recoverFun_spec (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) (hφ : ∀ x, ∃ f, φ f x ≠ 0)
    (f : C₀(Y, 𝕜)) (x : X) : φ f x = f (recoverFun φ hφ x) := by
  simpa [evalChar] using congr($(recoverFun_eq φ hφ x) f)

private theorem continuous_recoverFun (φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜))
    (hφ : ∀ x, ∃ f, φ f x ≠ 0) : Continuous (recoverFun φ hφ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_nhds]
  intro U hU hxU
  obtain ⟨f, hf1, hf0, -, -⟩ := ZeroAtInftyContinuousMap.exists_eqOn_const_zero_of_isCompact
    (isCompact_singleton (x := recoverFun φ hφ x)) hU.isClosed_compl
    (Set.disjoint_singleton_left.2 (Set.notMem_compl_iff.2 hxU)) (1 : 𝕜)
  have hmem : {x' : X | φ f x' ≠ 0} ∈ 𝓝 x :=
    (isOpen_ne.preimage (φ f).continuous).mem_nhds <| by
      simp only [Set.mem_preimage, Set.mem_ofPred]
      rw [recoverFun_spec φ hφ f x, hf1 rfl]
      exact one_ne_zero
  filter_upwards [hmem] with x' hx'
  by_contra hx'U
  apply hx'
  rw [recoverFun_spec φ hφ f x']
  exact hf0 hx'U

private theorem exists_apply_ne_zero_of_compZeroAtInftyToBCF (h : C(X, Y)) (x : X) :
    ∃ f : C₀(Y, 𝕜), h.compZeroAtInftyToBCF 𝕜 𝕜 f x ≠ 0 := by
  obtain ⟨f, hf1, -⟩ := ZeroAtInftyContinuousMap.exists_apply_eq_norm_le (h x) (1 : 𝕜)
  exact ⟨f, by simp [hf1]⟩

variable (𝕜 X Y) in
/-- Bijection between continuous maps `C(X, Y)` and pointwise-nonvanishing `⋆`-homomorphisms
`C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)` for an `RCLike` field `𝕜`, any topological space `X`, and a weakly
locally compact Hausdorff space `Y`. -/
def bcfMorphismEquiv :
    C(X, Y) ≃ {φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜) // ∀ x, ∃ f, φ f x ≠ 0} where
  toFun h := ⟨h.compZeroAtInftyToBCF 𝕜 𝕜, exists_apply_ne_zero_of_compZeroAtInftyToBCF h⟩
  invFun φ := ⟨recoverFun φ.1 φ.2, continuous_recoverFun φ.1 φ.2⟩
  left_inv h := by
    ext x
    have heq : evalChar (h.compZeroAtInftyToBCF 𝕜 𝕜) x =
        ZeroAtInftyContinuousMap.evalNonUnitalAlgHom 𝕜 (h x) := by
      ext f
      simp [evalChar]
    exact ZeroAtInftyContinuousMap.evalNonUnitalAlgHom_injective
      ((recoverFun_eq (h.compZeroAtInftyToBCF 𝕜 𝕜)
        (exists_apply_ne_zero_of_compZeroAtInftyToBCF h) x).symm.trans heq)
  right_inv φ := by
    apply Subtype.ext
    ext f x
    exact (recoverFun_spec φ.1 φ.2 f x).symm

/-- Applying `bcfMorphismEquiv` gives `ContinuousMap.compZeroAtInftyToBCF`. -/
@[simp]
theorem bcfMorphismEquiv_apply (h : C(X, Y)) :
    (bcfMorphismEquiv 𝕜 X Y h : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜)) = h.compZeroAtInftyToBCF 𝕜 𝕜 :=
  (rfl)

/-- Evaluating `f` at the recovered continuous map `(bcfMorphismEquiv 𝕜 X Y).symm φ x` returns
`φ.1 f x`. -/
@[simp]
theorem bcfMorphismEquiv_symm_apply_spec
    (φ : {φ : C₀(Y, 𝕜) →⋆ₙₐ[𝕜] (X →ᵇ 𝕜) // ∀ x, ∃ f, φ f x ≠ 0}) (f : C₀(Y, 𝕜)) (x : X) :
    f ((bcfMorphismEquiv 𝕜 X Y).symm φ x) = φ.1 f x :=
  (recoverFun_spec φ.1 φ.2 f x).symm

end CharacterRecovery

section Properness

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [WeaklyLocallyCompactSpace Y] [T2Space Y]

/-- A continuous map `h : C(X, Y)` into a weakly locally compact Hausdorff space is proper if and
only if `f ∘ h` vanishes at infinity for every `f : C₀(Y, A)`. -/
theorem isProperMap_iff_forall_tendsto_cocompact_nhds_zero (A : Type*) [TopologicalSpace A]
    [T1Space A] [Zero A] [MulActionWithZero ℝ A] [ContinuousSMul ℝ A] [Nontrivial A]
    (h : C(X, Y)) :
    IsProperMap h ↔ ∀ f : C₀(Y, A), Tendsto (f ∘ h) (cocompact X) (𝓝 0) := by
  refine ⟨fun hh f => (zero_at_infty f).comp (isProperMap_iff_tendsto_cocompact.1 hh).2,
    fun H => ?_⟩
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨h.continuous, fun K hK => ?_⟩
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨f, hfK, -, -, -⟩ := ZeroAtInftyContinuousMap.exists_eqOn_const_zero_of_isCompact
    hK isClosed_empty (Set.disjoint_empty K) a
  obtain ⟨L, hL, hLf⟩ := mem_cocompact.1 (H f (isOpen_compl_singleton.mem_nhds (Ne.symm ha)))
  refine hL.of_isClosed_subset (hK.isClosed.preimage h.continuous) fun x hx => ?_
  by_contra hxL
  exact hLf hxL (hfK hx)

/-- A continuous map `h : C(X, Y)` into a weakly locally compact Hausdorff space is proper if and
only if `h.compZeroAtInftyToBCF 𝕜 A` lands in the canonical image of `C₀(X, A)` inside `X →ᵇ A`. -/
theorem isProperMap_iff_range_compZeroAtInftyToBCF_subset (𝕜 A : Type*) [SeminormedRing 𝕜]
    [NonUnitalSeminormedRing A] [T1Space A] [StarRing A] [NormedStarGroup A] [Module 𝕜 A]
    [IsBoundedSMul 𝕜 A] [MulActionWithZero ℝ A] [ContinuousSMul ℝ A] [Nontrivial A] (h : C(X, Y)) :
    IsProperMap h ↔
      Set.range (h.compZeroAtInftyToBCF 𝕜 A) ⊆
        Set.range (ZeroAtInftyContinuousMap.toBCF : C₀(X, A) → (X →ᵇ A)) := by
  rw [isProperMap_iff_forall_tendsto_cocompact_nhds_zero A h]
  refine ⟨fun H _ ⟨f, hf⟩ => hf ▸
      ⟨{ toFun := f ∘ h, continuous_toFun := f.continuous.comp h.continuous,
         zero_at_infty' := H f }, by ext x; simp⟩,
    fun H f => ?_⟩
  obtain ⟨g, hg⟩ := H ⟨f, rfl⟩
  have heq : (f ∘ h : X → A) = g := funext fun x => by simpa using (congr($hg x)).symm
  rw [heq]
  exact zero_at_infty g

end Properness

end ContinuousMap
