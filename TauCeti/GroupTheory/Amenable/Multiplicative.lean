/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Multiplicative

/-!
# Amenability of `Multiplicative` and `Additive` type tags

The algebra equivalences `TauCeti.UCB.multiplicativeAlgEquiv` and `TauCeti.AddUCB.additiveAlgEquiv`
preserve positivity, normalization and left translations, so they induce bijections between means
and between left-invariant means:

* `TauCeti.Mean.multiplicativeEquiv A : Mean (Multiplicative A) ≃ AddMean A`
* `TauCeti.AddMean.additiveEquiv G : AddMean (Additive G) ≃ Mean G`

Consequently, `Amenable (Multiplicative A) ↔ AddAmenable A` and
`AddAmenable (Additive G) ↔ Amenable G` for every additive topological group `A` and every
multiplicative topological group `G`.
-/

public section

noncomputable section

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

namespace TauCeti

section Multiplicative

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

namespace Mean

variable (A) in
/-- Means on `UCB (Multiplicative A)` correspond bijectively to means on `AddUCB A`. -/
def multiplicativeEquiv : Mean (Multiplicative A) ≃ AddMean A where
  toFun m :=
    AddMean.mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ
        (UCB.multiplicativeAlgEquiv A).symm.toLinearMap)
      (fun f hf => map_nonneg m <| by
        simpa using (UCB.multiplicativeAlgEquiv_symm_le_iff (f := 0) (g := f)).2 hf) (by simp)
  invFun m :=
    mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.multiplicativeAlgEquiv A).toLinearMap)
      (fun f hf => map_nonneg m <| by
        simpa using (UCB.multiplicativeAlgEquiv_le_iff (f := 0) (g := f)).2 hf) (by simp)
  left_inv m := ext fun f => by simp
  right_inv m := AddMean.ext fun f => by simp

@[simp]
theorem multiplicativeEquiv_apply (m : Mean (Multiplicative A)) (f : AddUCB A) :
    multiplicativeEquiv A m f = m ((UCB.multiplicativeAlgEquiv A).symm f) := by
  simp [multiplicativeEquiv]

@[simp]
theorem multiplicativeEquiv_symm_apply (m : AddMean A) (f : UCB (Multiplicative A)) :
    (multiplicativeEquiv A).symm m f = m (UCB.multiplicativeAlgEquiv A f) := by
  simp [multiplicativeEquiv]

@[simp]
theorem isLeftInvariant_multiplicativeEquiv_iff {m : Mean (Multiplicative A)} :
    (multiplicativeEquiv A m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [AddMean.isLeftInvariant_iff, isLeftInvariant_iff]
  refine ⟨fun hm g f => ?_, fun hm a f => ?_⟩
  · simpa [← UCB.multiplicativeAlgEquiv_leftTranslation] using
      hm g.toAdd (UCB.multiplicativeAlgEquiv A f)
  · simpa using hm (ofAdd a) ((UCB.multiplicativeAlgEquiv A).symm f)

@[simp]
theorem isLeftInvariant_multiplicativeEquiv_symm_iff {m : AddMean A} :
    ((multiplicativeEquiv A).symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_multiplicativeEquiv_iff, Equiv.apply_symm_apply]

/-- Pushing forward a mean along `φ.toMultiplicative` corresponds to pushing forward its additive
mean along `φ`. -/
theorem multiplicativeEquiv_map (φ : A →ₜ+ B) (m : Mean (Multiplicative A)) :
    multiplicativeEquiv B (m.map φ.toMultiplicative) = (multiplicativeEquiv A m).map φ :=
  AddMean.ext fun f => by simp [UCB.multiplicativeAlgEquiv_symm_compRightAlgHom]

end Mean

/-- `Multiplicative A` is amenable exactly when `A` is additively amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative A) ↔ AddAmenable A := by
  rw [amenable_iff, addAmenable_iff]
  exact (Mean.multiplicativeEquiv A).exists_congr fun _ =>
    Mean.isLeftInvariant_multiplicativeEquiv_iff.symm

/-- `Multiplicative A` is amenable whenever `A` is additively amenable. -/
instance Amenable.multiplicative [AddAmenable A] : Amenable (Multiplicative A) :=
  amenable_multiplicative_iff.2 ‹_›

end Multiplicative

section Additive

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

namespace AddMean

variable (G) in
/-- Means on `AddUCB (Additive G)` correspond bijectively to means on `UCB G`. -/
def additiveEquiv : AddMean (Additive G) ≃ Mean G where
  toFun m :=
    Mean.mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ
        (AddUCB.additiveAlgEquiv G).symm.toLinearMap)
      (fun f hf => map_nonneg m <| by
        simpa using (AddUCB.additiveAlgEquiv_symm_le_iff (f := 0) (g := f)).2 hf) (by simp)
  invFun m :=
    mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.additiveAlgEquiv G).toLinearMap)
      (fun f hf => map_nonneg m <| by
        simpa using (AddUCB.additiveAlgEquiv_le_iff (f := 0) (g := f)).2 hf) (by simp)
  left_inv m := ext fun f => by simp
  right_inv m := Mean.ext fun f => by simp

@[simp]
theorem additiveEquiv_apply (m : AddMean (Additive G)) (f : UCB G) :
    additiveEquiv G m f = m ((AddUCB.additiveAlgEquiv G).symm f) := by
  simp [additiveEquiv]

@[simp]
theorem additiveEquiv_symm_apply (m : Mean G) (f : AddUCB (Additive G)) :
    (additiveEquiv G).symm m f = m (AddUCB.additiveAlgEquiv G f) := by
  simp [additiveEquiv]

@[simp]
theorem isLeftInvariant_additiveEquiv_iff {m : AddMean (Additive G)} :
    (additiveEquiv G m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [Mean.isLeftInvariant_iff, isLeftInvariant_iff]
  refine ⟨fun hm a f => ?_, fun hm g f => ?_⟩
  · simpa [← AddUCB.additiveAlgEquiv_leftTranslation] using
      hm a.toMul (AddUCB.additiveAlgEquiv G f)
  · simpa using hm (ofMul g) ((AddUCB.additiveAlgEquiv G).symm f)

@[simp]
theorem isLeftInvariant_additiveEquiv_symm_iff {m : Mean G} :
    ((additiveEquiv G).symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_additiveEquiv_iff, Equiv.apply_symm_apply]

/-- Pushing forward an additive mean along `φ.toAdditive` corresponds to pushing forward its
multiplicative mean along `φ`. -/
theorem additiveEquiv_map (φ : G →ₜ* H) (m : AddMean (Additive G)) :
    additiveEquiv H (m.map φ.toAdditive) = (additiveEquiv G m).map φ :=
  Mean.ext fun f => by simp [AddUCB.additiveAlgEquiv_symm_compRightAlgHom]

end AddMean

/-- `Additive G` is additively amenable exactly when `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff : AddAmenable (Additive G) ↔ Amenable G := by
  rw [addAmenable_iff, amenable_iff]
  exact (AddMean.additiveEquiv G).exists_congr fun _ =>
    AddMean.isLeftInvariant_additiveEquiv_iff.symm

/-- `Additive G` is additively amenable whenever `G` is amenable. -/
instance AddAmenable.additive [Amenable G] : AddAmenable (Additive G) :=
  addAmenable_additive_iff.2 ‹_›

end Additive

end TauCeti
