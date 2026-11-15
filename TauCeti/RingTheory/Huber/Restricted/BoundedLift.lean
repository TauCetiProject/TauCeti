/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Comparison
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Quotient

import TauCeti.Logic.Equiv.Basic

/-!
# Kernels and bounded lifts across the Huber–Gauss restricted-series comparison

Under the unit-radius Gauss comparisons `restrictedMvPowerSeriesGaussEquiv` and
`restrictedMvPowerSeriesCompletionGaussEquiv`, coefficientwise kernels, continuous additive
lifts, and norm-controlled preimages of restricted power series transport directly between
Mathlib's Gauss-normed subring `MvPowerSeries.IsRestricted.subring` and the Huber carriers
`weightedRestrictedSubring` and `restrictedMvPowerSeriesCompletion`:

* **Coefficientwise kernels and injectivity on completions:** over complete ultrametric normed
  commutative rings, `weightedMapCompletion` kills an element of `R⟨X₁, …, Xₖ⟩` if and only if
  every coefficient of its compared series lies in `RingHom.ker φ`
  (`mem_ker_weightedMapCompletion_iff`), so injective bounded coefficient maps remain injective
  after completion (`weightedMapCompletion_injective`).
* **Continuous additive lifts:** a bounded additive map `ψ : S →+ R` induces continuous additive
  maps `weightedAddMap` on `weightedRestrictedSubring` and `weightedAddMapCompletion` on
  `restrictedMvPowerSeriesCompletion` (defined without completeness hypotheses via
  `AddMonoidHom.completion`). Both commute with the Gauss comparisons
  (`restrictedMvPowerSeriesGaussEquiv_weightedAddMap`,
  `restrictedMvPowerSeriesCompletionGaussEquiv_weightedAddMapCompletion`), obey the same norm
  bound `L`, and furnish continuous additive right inverses when `ψ` is a right inverse to `φ`
  (`rightInverse_weightedAddMap`, `rightInverse_weightedAddMapCompletion`).
* **Bounded, sharp approximate, and exact Gauss-norm lifts:** uniformly `L`-bounded, sharp
  `(1 + ε)`-approximate, and exact norm-attaining coefficient lifts transfer across both Huber
  carriers with the same compared Gauss-norm bounds.

## Main definitions

* `TauCeti.Huber.weightedAddMap`: the continuous additive map on trivial-weight Huber restricted
  series induced by a bounded additive map `ψ : S →+ R`.
* `TauCeti.Huber.weightedAddMapCompletion`: its continuous extension to completed Huber
  restricted-series algebras `S⟨X₁, …, Xₖ⟩ →+ R⟨X₁, …, Xₖ⟩`.

## Main results

* `TauCeti.Huber.mem_ker_weightedMapCompletion_iff` and
  `TauCeti.Huber.weightedMapCompletion_injective`: coefficientwise kernel and injectivity of
  `weightedMapCompletion` over complete ultrametric bases.
* `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv_weightedAddMap` and
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv_weightedAddMapCompletion`: naturality
  of `weightedAddMap` and `weightedAddMapCompletion` under the Gauss comparisons.
* `TauCeti.Huber.rightInverse_weightedAddMap` and
  `TauCeti.Huber.rightInverse_weightedAddMapCompletion`: continuous additive sections of
  `weightedMap` and `weightedMapCompletion`.
* `TauCeti.Huber.exists_weightedMapCompletion_eq_and_norm_le`,
  `TauCeti.Huber.exists_weightedMapCompletion_eq_and_norm_lt_add`, and
  `TauCeti.Huber.exists_weightedMapCompletion_eq_and_norm_eq`: bounded, sharp approximate, and
  exact Gauss-norm lifts on completed Huber restricted-series algebras.
-/

public section

namespace TauCeti.Huber

open _root_.MvPowerSeries TauCeti.MvPowerSeries
open scoped Topology

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S]

section Kernels

variable {φ : R →+* S} {C : ℝ} (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

/-- The kernel of `weightedMap` at trivial weights is the preimage under the Gauss comparison of
the kernel of `restrictedMap`. -/
theorem ker_weightedMap_eq_comap_restrictedMvPowerSeriesGaussEquiv :
    RingHom.ker (weightedMap (k := k) hφc isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp)) =
      (RingHom.ker (restrictedMap (c := fun _ : Fin k ↦ (1 : ℝ)) φ hφ)).comap
        (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)) := by
  ext f
  simp only [Ideal.mem_comap, RingHom.mem_ker,
    ← restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ]
  exact (restrictedMvPowerSeriesGaussEquiv (n := k) (R := S)).map_eq_zero_iff.symm

variable [CompleteSpace R] [CompleteSpace S]

/-- Over complete ultrametric normed commutative rings, the kernel of `weightedMapCompletion` at
trivial weights is the preimage under the completed Gauss comparison of the kernel of
`restrictedMap`. -/
theorem ker_weightedMapCompletion_eq_comap_restrictedMvPowerSeriesCompletionGaussEquiv :
    RingHom.ker (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp)) =
      (RingHom.ker (restrictedMap (c := fun _ : Fin k ↦ (1 : ℝ)) φ hφ)).comap
        (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)) := by
  ext f
  simp only [Ideal.mem_comap, RingHom.mem_ker,
    ← restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ]
  exact (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := S)).map_eq_zero_iff.symm

include hφ in
/-- **Coefficientwise kernel of `weightedMapCompletion`.** Over complete ultrametric normed
commutative rings, an element of `R⟨X₁, …, Xₖ⟩` lies in `RingHom.ker (weightedMapCompletion …)`
if and only if every coefficient of its compared series lies in `RingHom.ker φ`. -/
theorem mem_ker_weightedMapCompletion_iff (f : restrictedMvPowerSeriesCompletion k R) :
    f ∈ RingHom.ker (weightedMapCompletion hφc isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp)) ↔
      ∀ ν, coeff ν (restrictedMvPowerSeriesCompletionGaussEquiv f :
        MvPowerSeries (Fin k) R) ∈ RingHom.ker φ := by
  rw [ker_weightedMapCompletion_eq_comap_restrictedMvPowerSeriesCompletionGaussEquiv hφc hφ,
    Ideal.mem_comap, mem_ker_restrictedMap_iff]

include hφ in
/-- Over complete ultrametric normed commutative rings, an injective bounded coefficient
homomorphism induces an injective homomorphism `R⟨X₁, …, Xₖ⟩ →+* S⟨X₁, …, Xₖ⟩` on completed
Huber restricted-series algebras. -/
theorem weightedMapCompletion_injective (hφinj : Function.Injective φ) :
    Function.Injective (weightedMapCompletion (k := k) hφc isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp)) := by
  intro f g h
  apply restrictedMvPowerSeriesCompletionGaussEquiv.injective
  refine restrictedMap_injective φ hφ hφinj ?_
  simpa only [restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ] using
    congrArg restrictedMvPowerSeriesCompletionGaussEquiv h

end Kernels

section AdditiveLift

variable (ψ : S →+ R) {L : ℝ} (hψ : ∀ b, ‖ψ b‖ ≤ L * ‖b‖)

/-- **Continuous additive lift on Huber restricted series.** A bounded additive map `ψ : S →+ R`
acts coefficientwise on the trivial-weight Huber restricted-series subring, transported from
`TauCeti.MvPowerSeries.restrictedAddMap` across the identity Gauss comparison. -/
noncomputable def weightedAddMap :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight →+
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight :=
  (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).symm.toAddMonoidHom.comp
    ((restrictedAddMap (c := fun _ : Fin k ↦ (1 : ℝ)) ψ hψ).comp
      (restrictedMvPowerSeriesGaussEquiv (n := k) (R := S)).toAddMonoidHom)

/-- The Gauss comparison intertwines `weightedAddMap` with `restrictedAddMap`. -/
@[simp]
theorem restrictedMvPowerSeriesGaussEquiv_weightedAddMap
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight) :
    restrictedMvPowerSeriesGaussEquiv (weightedAddMap ψ hψ g) =
      restrictedAddMap ψ hψ (restrictedMvPowerSeriesGaussEquiv g) :=
  (restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)).apply_symm_apply _

/-- `weightedAddMap` applies `ψ` to each power-series coefficient. -/
@[simp]
theorem coeff_weightedAddMap
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight)
    (ν : Fin k →₀ ℕ) :
    coeff ν (weightedAddMap ψ hψ g : MvPowerSeries (Fin k) R) =
      ψ (coeff ν (g : MvPowerSeries (Fin k) S)) := by
  rw [← coe_restrictedMvPowerSeriesGaussEquiv, restrictedMvPowerSeriesGaussEquiv_weightedAddMap,
    coeff_restrictedAddMap, coe_restrictedMvPowerSeriesGaussEquiv]

/-- `weightedAddMap` is continuous for the Huber restricted-series topologies. -/
@[continuity]
theorem continuous_weightedAddMap :
    Continuous (weightedAddMap (k := k) ψ hψ) :=
  continuous_restrictedMvPowerSeriesGaussEquiv_symm.comp
    ((continuous_restrictedAddMap ψ hψ).comp continuous_restrictedMvPowerSeriesGaussEquiv)

/-- `weightedAddMap` obeys the same Gauss-norm bound `L` as `ψ`. -/
theorem norm_restrictedMvPowerSeriesGaussEquiv_weightedAddMap_le
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight) :
    ‖restrictedMvPowerSeriesGaussEquiv (weightedAddMap ψ hψ g)‖ ≤
      L * ‖restrictedMvPowerSeriesGaussEquiv g‖ := by
  rw [restrictedMvPowerSeriesGaussEquiv_weightedAddMap]
  exact norm_restrictedAddMap_le ψ hψ _

/-- A bounded additive right inverse `ψ` to a continuous ring homomorphism `φ` induces a
continuous additive right inverse to `weightedMap`. -/
theorem rightInverse_weightedAddMap {φ : R →+* S} (hφc : Continuous φ)
    (hinv : Function.RightInverse ψ φ) :
    Function.RightInverse (weightedAddMap (k := k) ψ hψ)
      (weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp)) :=
  fun g ↦ Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
    rw [coe_weightedMap, coeff_map, coeff_weightedAddMap, hinv]

/-- **Continuous additive lift on completed Huber restricted-series algebras.** The continuous
extension of `weightedAddMap ψ hψ` to `S⟨X₁, …, Xₖ⟩ →+ R⟨X₁, …, Xₖ⟩`, defined without requiring
completeness of `R` or `S`. -/
noncomputable def weightedAddMapCompletion :
    restrictedMvPowerSeriesCompletion k S →+ restrictedMvPowerSeriesCompletion k R :=
  (weightedAddMap (k := k) ψ hψ).completion (continuous_weightedAddMap ψ hψ)

/-- On the canonical image of an uncompleted restricted series, `weightedAddMapCompletion` agrees
with `weightedAddMap`. -/
@[simp]
theorem weightedAddMapCompletion_coe
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight) :
    weightedAddMapCompletion ψ hψ (g : restrictedMvPowerSeriesCompletion k S) =
      (weightedAddMap ψ hψ g : restrictedMvPowerSeriesCompletion k R) :=
  AddMonoidHom.completion_coe _ _ g

/-- `weightedAddMapCompletion` is continuous on the completed Huber restricted-series algebras. -/
@[continuity]
theorem continuous_weightedAddMapCompletion :
    Continuous (weightedAddMapCompletion (k := k) ψ hψ) :=
  AddMonoidHom.continuous_completion _ _

/-- A bounded additive right inverse `ψ` to a continuous ring homomorphism `φ` induces a
continuous additive right inverse to `weightedMapCompletion`, without completeness assumptions on
`R` or `S`. -/
theorem rightInverse_weightedAddMapCompletion {φ : R →+* S} (hφc : Continuous φ)
    (hinv : Function.RightInverse ψ φ) :
    Function.RightInverse (weightedAddMapCompletion (k := k) ψ hψ)
      (weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp)) := by
  intro g
  refine UniformSpace.Completion.induction_on g (isClosed_eq
    ((continuous_weightedMapCompletion ..).comp (continuous_weightedAddMapCompletion ψ hψ))
    continuous_id) fun f ↦ ?_
  rw [weightedAddMapCompletion_coe, weightedMapCompletion_coe,
    rightInverse_weightedAddMap ψ hψ hφc hinv]

variable [CompleteSpace R] [CompleteSpace S]

/-- Over complete ultrametric normed commutative rings, the completed Gauss comparison intertwines
`weightedAddMapCompletion` with `restrictedAddMap`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussEquiv_weightedAddMapCompletion
    (g : restrictedMvPowerSeriesCompletion k S) :
    restrictedMvPowerSeriesCompletionGaussEquiv (weightedAddMapCompletion ψ hψ g) =
      restrictedAddMap ψ hψ (restrictedMvPowerSeriesCompletionGaussEquiv g) := by
  refine UniformSpace.Completion.induction_on g (isClosed_eq
    (continuous_restrictedMvPowerSeriesCompletionGaussEquiv.comp
      (continuous_weightedAddMapCompletion ψ hψ))
    ((continuous_restrictedAddMap ψ hψ).comp
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv)) fun f ↦ ?_
  rw [weightedAddMapCompletion_coe, restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    restrictedMvPowerSeriesGaussEquiv_weightedAddMap]

/-- Over complete ultrametric normed commutative rings, `weightedAddMapCompletion` obeys the same
bound `L` in the compared Gauss norms as `ψ`. -/
theorem norm_restrictedMvPowerSeriesCompletionGaussEquiv_weightedAddMapCompletion_le
    (g : restrictedMvPowerSeriesCompletion k S) :
    ‖restrictedMvPowerSeriesCompletionGaussEquiv (weightedAddMapCompletion ψ hψ g)‖ ≤
      L * ‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ := by
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_weightedAddMapCompletion]
  exact norm_restrictedAddMap_le ψ hψ _

end AdditiveLift

section BoundedAndSharpLifts

variable {φ : R →+* S} {C : ℝ} (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

include hφ in
/-- Uniformly `L`-bounded coefficient lifts produce Huber restricted-series preimages with the
same bound `L` in the compared Gauss norms. -/
theorem exists_weightedMap_eq_and_norm_le {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight) :
    ∃ f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight,
      weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp) f = g ∧
      ‖restrictedMvPowerSeriesGaussEquiv f‖ ≤ L * ‖restrictedMvPowerSeriesGaussEquiv g‖ :=
  (restrictedMvPowerSeriesGaussEquiv.toEquiv.exists_eq_and_iff_of_injective
    restrictedMvPowerSeriesGaussEquiv.injective
    (restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ)).mpr
    (exists_restrictedMap_eq_and_norm_le φ hφ hlift (restrictedMvPowerSeriesGaussEquiv g))

include hφ in
/-- Sharp approximate coefficient lifts produce Huber restricted-series preimages of compared Gauss
norm strictly below `‖restrictedMvPowerSeriesGaussEquiv g‖ + ε`. -/
theorem exists_weightedMap_eq_and_norm_lt_add
    (hlift : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε)
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight,
      weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp) f = g ∧
      ‖restrictedMvPowerSeriesGaussEquiv f‖ < ‖restrictedMvPowerSeriesGaussEquiv g‖ + ε :=
  (restrictedMvPowerSeriesGaussEquiv.toEquiv.exists_eq_and_iff_of_injective
    restrictedMvPowerSeriesGaussEquiv.injective
    (restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ)).mpr
    (exists_restrictedMap_eq_and_norm_lt_add φ hφ hlift (restrictedMvPowerSeriesGaussEquiv g) hε)

/-- Exact norm-attaining lifts for a contractive `φ` produce Huber restricted-series preimages of
the exact same compared Gauss norm. -/
theorem exists_weightedMap_eq_and_norm_eq (hφ1 : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖)
    (g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set S)) isWeightFamily_one_weight) :
    ∃ f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight,
      weightedMap hφc isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp) f = g ∧
      ‖restrictedMvPowerSeriesGaussEquiv f‖ = ‖restrictedMvPowerSeriesGaussEquiv g‖ :=
  let hφ1' : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖ := fun r ↦ (one_mul ‖r‖).symm ▸ hφ1 r
  (restrictedMvPowerSeriesGaussEquiv.toEquiv.exists_eq_and_iff_of_injective
    restrictedMvPowerSeriesGaussEquiv.injective
    (restrictedMvPowerSeriesGaussEquiv_weightedMap hφc hφ1')).mpr
    (exists_restrictedMap_eq_and_norm_eq φ hφ1' hφ1 hlift (restrictedMvPowerSeriesGaussEquiv g))

variable [CompleteSpace R] [CompleteSpace S]

include hφ in
/-- Over complete ultrametric normed commutative rings, uniformly `L`-bounded coefficient lifts
produce preimages in `R⟨X₁, …, Xₖ⟩` along `weightedMapCompletion` with the same bound `L` in the
compared Gauss norms. -/
theorem exists_weightedMapCompletion_eq_and_norm_le {L : ℝ}
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ L * ‖b‖)
    (g : restrictedMvPowerSeriesCompletion k S) :
    ∃ f : restrictedMvPowerSeriesCompletion k R,
      weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp) f = g ∧
      ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ ≤
        L * ‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ :=
  (restrictedMvPowerSeriesCompletionGaussEquiv.toEquiv.exists_eq_and_iff_of_injective
    restrictedMvPowerSeriesCompletionGaussEquiv.injective
    (restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ)).mpr
    (exists_restrictedMap_eq_and_norm_le φ hφ hlift
      (restrictedMvPowerSeriesCompletionGaussEquiv g))

include hφ in
/-- Over complete ultrametric normed commutative rings, sharp approximate coefficient lifts
produce preimages in `R⟨X₁, …, Xₖ⟩` along `weightedMapCompletion` of compared Gauss norm strictly
below `‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ + ε`. -/
theorem exists_weightedMapCompletion_eq_and_norm_lt_add
    (hlift : ∀ b, ∀ ε > 0, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖ + ε)
    (g : restrictedMvPowerSeriesCompletion k S) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : restrictedMvPowerSeriesCompletion k R,
      weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp) f = g ∧
      ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ <
        ‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ + ε :=
  (restrictedMvPowerSeriesCompletionGaussEquiv.toEquiv.exists_eq_and_iff_of_injective
    restrictedMvPowerSeriesCompletionGaussEquiv.injective
    (restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ)).mpr
    (exists_restrictedMap_eq_and_norm_lt_add φ hφ hlift
      (restrictedMvPowerSeriesCompletionGaussEquiv g) hε)

/-- Over complete ultrametric normed commutative rings, exact norm-attaining coefficient lifts for
a contractive `φ` produce preimages in `R⟨X₁, …, Xₖ⟩` along `weightedMapCompletion` of the exact
same compared Gauss norm. -/
theorem exists_weightedMapCompletion_eq_and_norm_eq (hφ1 : ∀ r, ‖φ r‖ ≤ ‖r‖)
    (hlift : ∀ b, ∃ a, φ a = b ∧ ‖a‖ ≤ ‖b‖)
    (g : restrictedMvPowerSeriesCompletion k S) :
    ∃ f : restrictedMvPowerSeriesCompletion k R,
      weightedMapCompletion hφc isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ by simp) f = g ∧
      ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ =
        ‖restrictedMvPowerSeriesCompletionGaussEquiv g‖ :=
  let hφ1' : ∀ r, ‖φ r‖ ≤ 1 * ‖r‖ := fun r ↦ (one_mul ‖r‖).symm ▸ hφ1 r
  (restrictedMvPowerSeriesCompletionGaussEquiv.toEquiv.exists_eq_and_iff_of_injective
    restrictedMvPowerSeriesCompletionGaussEquiv.injective
    (restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion hφc hφ1')).mpr
    (exists_restrictedMap_eq_and_norm_eq φ hφ1' hφ1 hlift
      (restrictedMvPowerSeriesCompletionGaussEquiv g))

end BoundedAndSharpLifts

end TauCeti.Huber
