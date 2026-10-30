/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Rename

/-!
# Renaming the variables of Gauss-normed restricted series

An embedding `e : Fin k ↪ Fin n` of variables renames unit-radius restricted series in `k`
variables to unit-radius restricted series in `n` variables, `Xᵢ ↦ X_{e i}`. On underlying power
series this is Mathlib's `MvPowerSeries.rename`. The resulting continuous `R`-algebra homomorphism
`R⟨X₁, …, Xₖ⟩ → R⟨X₁, …, Xₙ⟩` of Gauss-normed algebras is the Huber renaming
`TauCeti.Huber.weightedRenameAlgHom` at the trivial weight, carried along the identity comparison
`TauCeti.Huber.restrictedMvPowerSeriesGaussAlgEquiv`.

The two embeddings `Fin.castAddEmb` and `Fin.natAddEmb` give the inclusions of `R⟨X₁, …, Xₘ⟩` and
`R⟨Y₁, …, Yₖ⟩` into `R⟨X₁, …, Xₘ, Y₁, …, Yₖ⟩` used to present tensor products of affinoid
algebras.

## Main definitions

* `TauCeti.MvPowerSeries.restrictedRename`: the renaming homomorphism
  `R⟨X₁, …, Xₖ⟩ →ₐ[R] R⟨X₁, …, Xₙ⟩`.

## Main results

* `TauCeti.MvPowerSeries.coe_restrictedRename`: it is `MvPowerSeries.rename` on underlying series.
* `TauCeti.MvPowerSeries.restrictedRename_X`: it sends `Xᵢ` to `X_{e i}`.
* `TauCeti.MvPowerSeries.continuous_restrictedRename`: it is continuous.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries TauCeti.Huber

variable {k n : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- **Renaming the variables of restricted series** along an embedding `e : Fin k ↪ Fin n`: the
`R`-algebra homomorphism `R⟨X₁, …, Xₖ⟩ → R⟨X₁, …, Xₙ⟩` given by `MvPowerSeries.rename e` on
underlying series (`TauCeti.MvPowerSeries.coe_restrictedRename`). -/
noncomputable def restrictedRename (e : Fin k ↪ Fin n) :
    IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →ₐ[R]
      IsRestricted.subring (R := R) (fun _ : Fin n ↦ 1) :=
  (restrictedMvPowerSeriesGaussAlgEquiv.toAlgHom.comp
    (weightedRenameAlgHom e isWeightFamily_one_weight isWeightFamily_one_weight
      fun _ ↦ subset_rfl)).comp restrictedMvPowerSeriesGaussAlgEquiv.symm.toAlgHom

/-- `restrictedRename e` is `MvPowerSeries.rename e` on underlying power series. -/
@[simp]
theorem coe_restrictedRename (e : Fin k ↪ Fin n)
    (f : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    (restrictedRename e f : MvPowerSeries (Fin n) R) = rename e (f : MvPowerSeries (Fin k) R) := by
  simp [restrictedRename]

/-- `restrictedRename e` sends each variable `Xᵢ` to `X_{e i}`. -/
@[simp]
theorem restrictedRename_X (e : Fin k ↪ Fin n) (i : Fin k) :
    restrictedRename (R := R) e ⟨X i, isRestricted_X _ i⟩ = ⟨X (e i), isRestricted_X _ (e i)⟩ :=
  Subtype.ext (by simp)

/-- `restrictedRename e` is continuous for the Gauss norms. -/
theorem continuous_restrictedRename (e : Fin k ↪ Fin n) :
    Continuous (restrictedRename (R := R) e) := by
  have h : ⇑(restrictedRename (R := R) e) = restrictedMvPowerSeriesGaussEquiv ∘
      weightedRename e isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ subset_rfl) ∘
        restrictedMvPowerSeriesGaussEquiv.symm := by
    funext f
    simp [restrictedRename]
  rw [h]
  exact continuous_restrictedMvPowerSeriesGaussEquiv.comp <|
    (continuous_weightedRename _ _ _ _).comp continuous_restrictedMvPowerSeriesGaussEquiv_symm

end TauCeti.MvPowerSeries
