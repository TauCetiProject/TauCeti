/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Additive
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Type-tag equivalences for additive and multiplicative amenable groups

This file identifies means and amenability across the `Multiplicative` and `Additive` type tags:
precomposition with `AddUCB.equivMultiplicative.symm` gives a left-invariance-preserving bijection
`AddMean A ≃ Mean (Multiplicative A)`, and composing its inverse with pushforward along
`ContinuousMulEquiv.multiplicativeAdditive G : Multiplicative (Additive G) ≃ₜ* G` gives the
symmetric bijection `Mean G ≃ AddMean (Additive G)`. Consequently,
`Amenable (Multiplicative A) ↔ AddAmenable A` and `AddAmenable (Additive G) ↔ Amenable G`.

## Main definitions

* `TauCeti.AddMean.equivMultiplicative`: the bijection `AddMean A ≃ Mean (Multiplicative A)`.
* `TauCeti.Mean.equivAdditive`: the bijection `Mean G ≃ AddMean (Additive G)`.

## Main results

* `TauCeti.AddMean.isLeftInvariant_equivMultiplicative_iff`,
  `TauCeti.Mean.isLeftInvariant_equivAdditive_iff`: the type-tag bijections preserve and reflect
  left invariance.
* `TauCeti.amenable_multiplicative_iff`, `TauCeti.addAmenable_additive_iff`: compatibility of
  `Amenable` and `AddAmenable` across `Multiplicative` and `Additive`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1.
-/

public section

noncomputable section

open Multiplicative Additive

namespace TauCeti

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

namespace AddMean

/-- Precomposition with `AddUCB.equivMultiplicative.symm` (and its inverse
`AddUCB.equivMultiplicative`) identifies additive means on `AddUCB A` with means on
`UCB (Multiplicative A)`. -/
def equivMultiplicative : AddMean A ≃ Mean (Multiplicative A) where
  toFun m := Mean.mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ AddUCB.equivMultiplicative.symm.toLinearMap)
    (fun _ hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap,
        AlgEquiv.toLinearMap_apply]
      exact map_nonneg m (by
        simpa only [map_zero] using
          AddUCB.equivMultiplicative_symm_le_equivMultiplicative_symm_iff.2 hf))
    (by simp)
  invFun m := mk₀
    (m.toPositiveLinearMap.toLinearMap ∘ₗ AddUCB.equivMultiplicative.toLinearMap)
    (fun _ hf => by
      simp only [LinearMap.comp_apply, PositiveLinearMap.coe_toLinearMap,
        Mean.coe_toPositiveLinearMap, AlgEquiv.toLinearMap_apply]
      exact map_nonneg m (by
        simpa only [map_zero] using
          AddUCB.equivMultiplicative_le_equivMultiplicative_iff.2 hf))
    (by simp)
  left_inv m := ext fun f => by simp [mk₀_apply, Mean.mk₀_apply]
  right_inv m := Mean.ext fun f => by simp [mk₀_apply, Mean.mk₀_apply]

@[simp]
theorem equivMultiplicative_apply (m : AddMean A) (f : UCB (Multiplicative A)) :
    equivMultiplicative m f = m (AddUCB.equivMultiplicative.symm f) :=
  Mean.mk₀_apply _ _ _ f

@[simp]
theorem equivMultiplicative_symm_apply (m : Mean (Multiplicative A)) (f : AddUCB A) :
    equivMultiplicative.symm m f = m (AddUCB.equivMultiplicative f) :=
  mk₀_apply _ _ _ f

/-- `equivMultiplicative` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivMultiplicative_iff {m : AddMean A} :
    (equivMultiplicative m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  simp only [Mean.isLeftInvariant_iff, isLeftInvariant_iff, equivMultiplicative_apply,
    AddUCB.equivMultiplicative_symm_leftTranslation]
  exact ⟨fun h a f => by simpa using h (ofAdd a) (AddUCB.equivMultiplicative f),
    fun h g f => h g.toAdd (AddUCB.equivMultiplicative.symm f)⟩

/-- `equivMultiplicative.symm` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivMultiplicative_symm_iff {m : Mean (Multiplicative A)} :
    (equivMultiplicative.symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_equivMultiplicative_iff, Equiv.apply_symm_apply]

end AddMean

namespace Mean

section Additive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Precomposition with `UCB.equivAdditive.symm` (and its inverse `UCB.equivAdditive`) identifies
means on `UCB G` with additive means on `AddUCB (Additive G)`. -/
def equivAdditive : Mean G ≃ AddMean (Additive G) :=
  Equiv.trans
    { toFun m := m.map ((ContinuousMulEquiv.multiplicativeAdditive G).symm :
        G →ₜ* Multiplicative (Additive G))
      invFun m := m.map (ContinuousMulEquiv.multiplicativeAdditive G :
        Multiplicative (Additive G) →ₜ* G)
      left_inv m := by
        ext f
        simp only [map_apply]
        congr 1
        ext x
        simp
      right_inv m := by
        ext f
        simp only [map_apply]
        congr 1
        ext x
        simp }
    (AddMean.equivMultiplicative (A := Additive G)).symm

@[simp]
theorem equivAdditive_apply (m : Mean G) (f : AddUCB (Additive G)) :
    equivAdditive m f = m (UCB.equivAdditive.symm f) := by
  simp only [equivAdditive, Equiv.trans_apply, Equiv.coe_fn_mk,
    AddMean.equivMultiplicative_symm_apply, map_apply]
  congr 1
  ext x
  simp

@[simp]
theorem equivAdditive_symm_apply (m : AddMean (Additive G)) (f : UCB G) :
    equivAdditive.symm m f = m (UCB.equivAdditive f) := by
  simp only [equivAdditive, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_symm_mk,
    map_apply, AddMean.equivMultiplicative_apply]
  congr 1
  ext x
  simp

/-- `equivAdditive` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivAdditive_iff {m : Mean G} :
    (equivAdditive m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  let e := ContinuousMulEquiv.multiplicativeAdditive G
  simp only [equivAdditive, Equiv.trans_apply, Equiv.coe_fn_mk,
    AddMean.isLeftInvariant_equivMultiplicative_symm_iff]
  refine ⟨fun hm => ?_, fun hm =>
    hm.map (φ := (e.symm : G →ₜ* Multiplicative (Additive G))) e.symm.surjective.denseRange⟩
  have h := hm.map (φ := (e : Multiplicative (Additive G) →ₜ* G)) e.surjective.denseRange
  have hid : (m.map (e.symm : G →ₜ* Multiplicative (Additive G))).map
      (e : Multiplicative (Additive G) →ₜ* G) = m := by
    ext f
    simp only [map_apply]
    congr 1
    ext x
    simp [e]
  rwa [hid] at h

/-- `equivAdditive.symm` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivAdditive_symm_iff {m : AddMean (Additive G)} :
    (equivAdditive.symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_equivAdditive_iff, Equiv.apply_symm_apply]

end Additive

end Mean

/-- `Multiplicative A` is amenable if and only if `A` is additively amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative A) ↔ AddAmenable A :=
  ⟨fun ⟨⟨_, hm⟩⟩ => ⟨⟨_, AddMean.isLeftInvariant_equivMultiplicative_symm_iff.2 hm⟩⟩,
    fun ⟨⟨_, hm⟩⟩ => ⟨⟨_, AddMean.isLeftInvariant_equivMultiplicative_iff.2 hm⟩⟩⟩

/-- `Additive G` is additively amenable if and only if `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : AddAmenable (Additive G) ↔ Amenable G := by
  rw [← amenable_multiplicative_iff, (ContinuousMulEquiv.multiplicativeAdditive G).amenable_iff]

instance [AddAmenable A] : Amenable (Multiplicative A) :=
  amenable_multiplicative_iff.2 ‹_›

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Amenable G] :
    AddAmenable (Additive G) :=
  addAmenable_additive_iff.2 ‹_›

end TauCeti
