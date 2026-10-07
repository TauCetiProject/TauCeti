/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Decomposition groups at infinite places

An automorphism carrying an infinite place `w` to `w'` extends continuously to an
isomorphism of their completions. For places over `v`, this is an isomorphism over `K_v`.
When `L/K` is Galois, the stabilizer of `w` is thereby identified with `Aut(L_w/K_v)`.
This is the archimedean decomposition-group comparison needed to compute the cohomology
of the semi-local multiplicative groups by Shapiro's lemma.

## References

The completion transport and decomposition-group API adapt the formal pattern of
`completionCongr`, `decompositionHom`, and `decompositionEquiv` in
`TauCeti/NumberTheory/NumberField/LocalGlobal/DecompositionGroup.lean`.

* J. S. Milne, *Class Field Theory*, Chapter VII, §2 and Proposition 2.7.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §8.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace
open scoped NumberField.LiesOver

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem isometry_withAbsCongr (σ : L ≃ₐ[K] L)
    {w w' : InfinitePlace L} (h : w' = σ • w) :
    Isometry (WithAbs.congr w.1 w'.1 σ.toRingEquiv) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  simp only [WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
  rw [← InfinitePlace.coe_apply, ← InfinitePlace.coe_apply, h,
    InfinitePlace.smul_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.symm_apply_apply]

/-- Transport between archimedean completions along an automorphism carrying `w` to `w'`.
It extends `σ` and fixes the completion of the base field. -/
def infiniteCompletionCongr (v : InfinitePlace K) (σ : L ≃ₐ[K] L)
    {w w' : InfinitePlace L} [w.LiesOver v] [w'.LiesOver v] (h : w' = σ • w) :
    w.Completion ≃ₐ[v.Completion] w'.Completion := by
  let e := WithAbs.congr w.1 w'.1 σ.toRingEquiv
  have he := isometry_withAbsCongr σ h
  have hei : Isometry e.symm :=
    isometry_withAbsCongr σ⁻¹ (by rw [h, inv_smul_smul])
  let E : w.Completion ≃+* w'.Completion :=
    (Completion.equiv w).trans
      ((UniformSpace.Completion.mapRingEquiv e he.continuous hei.continuous).trans
        (Completion.equiv w').symm)
  have hE (x : L) : E (algebraMap L w.Completion x) = algebraMap L w'.Completion (σ x) := by
    apply (Completion.equiv w').injective
    -- The completion equivalences are type-synonym adapters; no application lemma
    -- exposes their compatibility with `mapRingEquiv`.
    change UniformSpace.Completion.mapRingHom e.toRingHom he.continuous
      (WithAbs.toAbs w.1 x) = (WithAbs.toAbs w'.1 (σ x) : w'.1.Completion)
    exact UniformSpace.Completion.mapRingHom_coe he.continuous
      (WithAbs.toAbs w.1 x)
  have hc : Continuous E :=
    (Completion.continuous_ofCompletion w').comp
      ((UniformSpace.Completion.continuous_map).comp (Completion.continuous_toCompletion w))
  refine AlgEquiv.ofRingEquiv (f := E) ?_
  intro a
  induction a using Completion.induction_on with
  | hp =>
    exact isClosed_eq (hc.comp (LiesOver.continuous_completionMap v w))
      (LiesOver.continuous_completionMap v w')
  | ih x =>
    -- The dense coercion agrees with the field algebra map by construction.
    change E (algebraMap v.Completion w.Completion (algebraMap K v.Completion x.ofAbs)) =
      algebraMap v.Completion w'.Completion (algebraMap K v.Completion x.ofAbs)
    rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
      ← IsScalarTower.algebraMap_apply K v.Completion w'.Completion,
      IsScalarTower.algebraMap_apply K L w.Completion,
      IsScalarTower.algebraMap_apply K L w'.Completion, hE, AlgEquiv.commutes]

variable (v : InfinitePlace K) {w w' : InfinitePlace L} [w.LiesOver v] [w'.LiesOver v]

/-- Completion transport agrees with the given automorphism on the dense field. -/
-- Apply before `Completion.algebraMap_apply` expands the dense field embedding.
@[simp↓]
theorem infiniteCompletionCongr_algebraMap (σ : L ≃ₐ[K] L) (h : w' = σ • w) (x : L) :
    infiniteCompletionCongr v σ h (algebraMap L w.Completion x) =
      algebraMap L w'.Completion (σ x) := by
  apply (Completion.equiv w').injective
  -- Unfold only the type-synonym adapters to apply the completion map's coercion lemma.
  change UniformSpace.Completion.mapRingHom
    (WithAbs.congr w.1 w'.1 σ.toRingEquiv).toRingHom
    (isometry_withAbsCongr σ h).continuous (WithAbs.toAbs w.1 x) =
      (WithAbs.toAbs w'.1 (σ x) : w'.1.Completion)
  exact UniformSpace.Completion.mapRingHom_coe
    (isometry_withAbsCongr σ h).continuous (WithAbs.toAbs w.1 x)

/-- Transport between archimedean completions is continuous. -/
@[fun_prop]
theorem continuous_infiniteCompletionCongr (σ : L ≃ₐ[K] L) (h : w' = σ • w) :
    Continuous (infiniteCompletionCongr v σ h) :=
  (Completion.continuous_ofCompletion w').comp
    (UniformSpace.Completion.continuous_map.comp (Completion.continuous_toCompletion w))

/-- Completion transport is the unique continuous ring homomorphism extending `σ`. -/
theorem eq_infiniteCompletionCongr_of_continuous (σ : L ≃ₐ[K] L) (h : w' = σ • w)
    (f : w.Completion →+* w'.Completion) (hf : Continuous f)
    (hfσ : ∀ x : L, f (algebraMap L w.Completion x) =
      algebraMap L w'.Completion (σ x)) :
    f = (infiniteCompletionCongr v σ h).toRingEquiv.toRingHom := by
  apply DFunLike.coe_injective
  apply (Completion.denseRange_coe w).equalizer hf (continuous_infiniteCompletionCongr v σ h)
  funext x
  exact (hfσ x.ofAbs).trans (infiniteCompletionCongr_algebraMap v σ h x.ofAbs).symm

/-- Completion transport along the identity is the identity. -/
@[simp]
theorem infiniteCompletionCongr_one :
    infiniteCompletionCongr v (1 : L ≃ₐ[K] L) (w := w) (w' := w) (one_smul _ _).symm =
      AlgEquiv.refl := by
  apply AlgEquiv.coe_fun_injective
  apply (Completion.denseRange_coe w).equalizer
    (continuous_infiniteCompletionCongr v _ _) continuous_id
  funext x
  exact (infiniteCompletionCongr_algebraMap v (1 : L ≃ₐ[K] L) _ x.ofAbs).trans
    (congrArg (algebraMap L w.Completion) (AlgEquiv.one_apply x.ofAbs))

/-- Completion transport respects composition of automorphisms. -/
@[simp]
theorem infiniteCompletionCongr_trans {w'' : InfinitePlace L} [w''.LiesOver v]
    (σ τ : L ≃ₐ[K] L) (hσ : w' = σ • w) (hτ : w'' = τ • w') :
    (infiniteCompletionCongr v σ hσ).trans (infiniteCompletionCongr v τ hτ) =
      infiniteCompletionCongr v (τ * σ) (by rw [hτ, hσ, mul_smul]) := by
  apply AlgEquiv.coe_fun_injective
  apply (Completion.denseRange_coe w).equalizer
    ((continuous_infiniteCompletionCongr v τ hτ).comp
      (continuous_infiniteCompletionCongr v σ hσ))
    (continuous_infiniteCompletionCongr v _ _)
  funext x
  -- Express the dense coercion as the algebra map so transport's defining equation applies.
  change infiniteCompletionCongr v τ hτ
    (infiniteCompletionCongr v σ hσ (algebraMap L w.Completion x.ofAbs)) =
      infiniteCompletionCongr v (τ * σ) _ (algebraMap L w.Completion x.ofAbs)
  simp only [infiniteCompletionCongr_algebraMap, AlgEquiv.mul_apply]

/-- Inverting completion transport inverts the field automorphism. -/
@[simp]
theorem infiniteCompletionCongr_symm (σ : L ≃ₐ[K] L) (h : w' = σ • w) :
    (infiniteCompletionCongr v σ h).symm =
      infiniteCompletionCongr v σ⁻¹ (by rw [h, inv_smul_smul]) := by
  apply AlgEquiv.ext
  intro x
  apply (infiniteCompletionCongr v σ h).injective
  simp [← AlgEquiv.trans_apply]

variable (w)

/-- The action of the stabilizer of an infinite place on its completion, fixing `K_v`. -/
def infiniteDecompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w →* (w.Completion ≃ₐ[v.Completion] w.Completion) where
  toFun σ := infiniteCompletionCongr v (σ : L ≃ₐ[K] L)
    (MulAction.mem_stabilizer_iff.mp σ.2).symm
  map_one' := infiniteCompletionCongr_one v
  map_mul' σ τ := (infiniteCompletionCongr_trans v (τ : L ≃ₐ[K] L) (σ : L ≃ₐ[K] L)
    (MulAction.mem_stabilizer_iff.mp τ.2).symm
    (MulAction.mem_stabilizer_iff.mp σ.2).symm).symm

/-- The stabilizer acts by completion transport. -/
theorem infiniteDecompositionHom_apply (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    infiniteDecompositionHom v w σ = infiniteCompletionCongr v (σ : L ≃ₐ[K] L)
      (MulAction.mem_stabilizer_iff.mp σ.2).symm :=
  (rfl)

/-- The decomposition-group action extends the automorphism of the field. -/
-- Apply before `Completion.algebraMap_apply` expands the dense field embedding.
@[simp↓]
theorem infiniteDecompositionHom_algebraMap
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (x : L) :
    infiniteDecompositionHom v w σ (algebraMap L w.Completion x) =
      algebraMap L w.Completion ((σ : L ≃ₐ[K] L) x) :=
  infiniteCompletionCongr_algebraMap v (σ : L ≃ₐ[K] L)
    (MulAction.mem_stabilizer_iff.mp σ.2).symm x

/-- Every element of the decomposition group acts continuously on the completion. -/
@[fun_prop]
theorem continuous_infiniteDecompositionHom (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) :
    Continuous (infiniteDecompositionHom v w σ) := by
  rw [infiniteDecompositionHom_apply]
  exact continuous_infiniteCompletionCongr v _ _

/-- The stabilizer acts faithfully on its archimedean completion. -/
theorem infiniteDecompositionHom_injective : Function.Injective (infiniteDecompositionHom v w) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  ext x
  have h := congrArg (fun e ↦ e (algebraMap L w.Completion x)) hσ
  rw [infiniteDecompositionHom_algebraMap, AlgEquiv.one_apply] at h
  exact (algebraMap L w.Completion).injective h

variable [IsGalois K L]

/-- The order of an archimedean decomposition group is the completed extension degree. -/
theorem card_stabilizer_eq_finrank_completion :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) =
      Module.finrank v.Completion w.Completion := by
  classical
  rw [InfinitePlace.card_stabilizer]
  split_ifs with h
  · exact (h.finrank_eq_one v).symm
  · exact (InfinitePlace.IsRamified.finrank_eq_two v h).symm

/-- Every automorphism of `L_w/K_v` comes from the stabilizer of `w` in `Gal(L/K)`. -/
theorem infiniteDecompositionHom_surjective :
    Function.Surjective (infiniteDecompositionHom v w) := by
  refine ((Nat.bijective_iff_injective_and_card (infiniteDecompositionHom v w)).mpr
    ⟨infiniteDecompositionHom_injective v w, le_antisymm ?_ ?_⟩).surjective
  · exact Nat.card_le_card_of_injective _ (infiniteDecompositionHom_injective v w)
  · rw [card_stabilizer_eq_finrank_completion v w]
    exact Nat.card_eq_fintype_card.trans_le AlgEquiv.card_le

/-- The decomposition group at an infinite place of a Galois extension is the Galois group
of the completed extension. -/
def infiniteDecompositionEquiv :
    MulAction.stabilizer (L ≃ₐ[K] L) w ≃*
      (w.Completion ≃ₐ[v.Completion] w.Completion) :=
  MulEquiv.ofBijective (infiniteDecompositionHom v w)
    ⟨infiniteDecompositionHom_injective v w, infiniteDecompositionHom_surjective v w⟩

/-- The decomposition-group equivalence is the continuous extension action. -/
@[simp]
theorem coe_infiniteDecompositionEquiv :
    ⇑(infiniteDecompositionEquiv v w) = infiniteDecompositionHom v w :=
  (rfl)

/-- The decomposition-group equivalence extends the action on the field. -/
-- Apply before `Completion.algebraMap_apply` expands the dense field embedding.
@[simp↓]
theorem infiniteDecompositionEquiv_algebraMap
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (x : L) :
    infiniteDecompositionEquiv v w σ (algebraMap L w.Completion x) =
      algebraMap L w.Completion ((σ : L ≃ₐ[K] L) x) := by
  rw [coe_infiniteDecompositionEquiv, infiniteDecompositionHom_algebraMap]

end TauCeti
