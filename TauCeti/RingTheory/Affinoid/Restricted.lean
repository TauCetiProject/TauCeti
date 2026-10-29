/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.FiniteQuotient
public import TauCeti.RingTheory.Affinoid.Continuity
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Sum
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner

/-!
# Restricted series over an affinoid algebra

Let `A` be an affinoid algebra over a complete nonarchimedean field `K`, carrying a complete
ultrametric algebra norm, and let `A⟨X₁, …, Xₘ⟩` be the Gauss-normed ring of unit-radius
restricted series over `A`. This file proves that `A⟨X₁, …, Xₘ⟩` is again affinoid, and that
`K`-algebra maps from it to a completely normed affinoid algebra `B` correspond to `K`-algebra
maps `A → B` together with power-bounded images of the variables.

For a Tate presentation `π : K⟨Y₁, …, Yₙ⟩ → A`, automatic continuity makes `π` bounded and the
open mapping theorem gives lifts of controlled norm. Applying `π` to coefficients is then a
surjection `K⟨Y⟩⟨X⟩ → A⟨X⟩` (`TauCeti.MvPowerSeries.restrictedMap_surjective`), and the iteration
isomorphism `K⟨X, Y⟩ ≅ K⟨Y⟩⟨X⟩` (`TauCeti.MvPowerSeries.restrictedSumAlgEquiv`) presents `A⟨X⟩` as
a quotient of the Tate algebra in `m + n` variables.

The universal property needs no continuity hypothesis: algebra homomorphisms from the noetherian
Banach algebras `A` and `A⟨X⟩` into a completely normed affinoid algebra are automatically
continuous, so the continuous universal property
`TauCeti.MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring` applies. The images
of the variables need only be power-bounded, not of norm at most one.

## Main definitions

* `TauCeti.IsAffinoidAlgebra.restrictedLift`: the `K`-algebra map `A⟨X₁, …, Xₘ⟩ →ₐ[K] B` extending
  `φ : A →ₐ[K] B` and sending `Xᵢ` to a power-bounded `bᵢ`.

## Main results

* `TauCeti.IsAffinoidAlgebra.isRestricted_subring`: `A⟨X₁, …, Xₘ⟩` is affinoid.
* `TauCeti.IsAffinoidAlgebra.algHom_ext_isRestricted_subring`: `K`-algebra maps
  `A⟨X₁, …, Xₘ⟩ → B` agreeing on `A` and on the variables are equal.
* `TauCeti.IsAffinoidAlgebra.existsUnique_algHom_isRestricted_subring`: a `K`-algebra map
  `φ : A → B` into an affinoid algebra and power-bounded `b₁, …, bₘ ∈ B` extend uniquely to a
  `K`-algebra map `A⟨X₁, …, Xₘ⟩ → B` sending `Xᵢ` to `bᵢ`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§1.4, 6.1.1
  and 6.1.3.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries TauCeti.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- **Restricted series over an affinoid algebra form an affinoid algebra.** For an affinoid
algebra `A` with a complete ultrametric algebra norm, the Gauss-normed algebra `A⟨X₁, …, Xₘ⟩` of
unit-radius restricted series is affinoid: a Tate presentation `K⟨Y₁, …, Yₙ⟩ → A` induces a
presentation `K⟨X₁, …, Xₘ, Y₁, …, Yₙ⟩ → A⟨X₁, …, Xₘ⟩`. -/
theorem isRestricted_subring {τ : Type*} [Finite τ] (hA : IsAffinoidAlgebra K A) :
    IsAffinoidAlgebra K (IsRestricted.subring (R := A) (fun _ : τ ↦ 1)) := by
  classical
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  have := isNoetherianRing_isRestricted_subring (K := K) (c := fun _ : Fin n ↦ (1 : ℝ))
  let πL : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →L[K] A :=
    ⟨π.toLinearMap, hA.continuous_algHom π⟩
  obtain ⟨C, -, hC⟩ := πL.exists_preimage_norm_le hπ
  let π' : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1) →+* A := π
  have hπ' (r : IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) : ‖π' r‖ ≤ ‖πL‖ * ‖r‖ :=
    πL.le_opNorm r
  -- apply `π` to the coefficients of series in `X` over `K⟨Y⟩`
  let Φ := restrictedMap (c := fun _ : τ ↦ 1) π' hπ'
  let e := restrictedSumAlgEquiv (S := K) (R := K) (c := fun _ : τ ↦ (1 : ℝ))
    (d := fun _ : Fin n ↦ 1)
  have hΦ (r : K) : Φ (e (algebraMap K _ r)) = algebraMap K _ r := by
    rw [e.commutes, IsScalarTower.algebraMap_apply K
      (IsRestricted.subring (R := K) fun _ : Fin n ↦ (1 : ℝ)), restrictedMap_algebraMap]
    exact (congrArg _ (π.commutes r)).trans (IsScalarTower.algebraMap_apply K A _ r).symm
  let ψ : IsRestricted.subring (R := K) (Sum.elim (fun _ : τ ↦ (1 : ℝ)) fun _ : Fin n ↦ 1) →ₐ[K]
      IsRestricted.subring (R := A) (fun _ : τ ↦ 1) :=
    { Φ.comp (e : _ →+* _) with commutes' := hΦ }
  have hrad : (Sum.elim (fun _ : τ ↦ (1 : ℝ)) fun _ : Fin n ↦ 1) = fun _ ↦ 1 := by
    funext i
    cases i <;> rfl
  have hT : IsAffinoidAlgebra K
      (IsRestricted.subring (R := K) (Sum.elim (fun _ : τ ↦ (1 : ℝ)) fun _ : Fin n ↦ 1)) :=
    hrad ▸ isAffinoidAlgebra_tate
  exact hT.of_surjective ψ ((restrictedMap_surjective _ _ hC).comp e.surjective)

variable {k : ℕ} (hA : IsAffinoidAlgebra K A) {B : Type*} [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B] (hB : IsAffinoidAlgebra K B)

include hA hB in
/-- **`K`-algebra maps out of `A⟨X₁, …, Xₖ⟩` are determined on `A` and the variables.** Let `A`
and `B` be affinoid algebras with complete ultrametric algebra norms. Two `K`-algebra maps
`A⟨X₁, …, Xₖ⟩ → B` that agree on `A` and on every `Xᵢ` are equal. No continuity is assumed: it is
automatic (`TauCeti.IsAffinoidAlgebra.continuous_algHom`). -/
theorem algHom_ext_isRestricted_subring
    {ψ₁ ψ₂ : IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1) →ₐ[K] B}
    (hC : ∀ a, ψ₁ (algebraMap A _ a) = ψ₂ (algebraMap A _ a))
    (hX : ∀ i, ψ₁ ⟨X i, isRestricted_X _ i⟩ = ψ₂ ⟨X i, isRestricted_X _ i⟩) : ψ₁ = ψ₂ :=
  have := (hA.isRestricted_subring (τ := Fin k)).isNoetherianRing
  AlgHom.toRingHom_injective <| isRestricted_subring_ringHom_ext_of_continuous
    (hB.continuous_algHom ψ₁) (hB.continuous_algHom ψ₂) hC hX

/-- **The extension of a `K`-algebra map `φ : A → B` to `A⟨X₁, …, Xₖ⟩` sending each `Xᵢ` to
`bᵢ`**, for affinoid algebras `A` and `B` with complete ultrametric algebra norms and
power-bounded `b₁, …, bₖ ∈ B`. It is the continuous extension
`TauCeti.MvPowerSeries.restrictedLift`, which applies because `φ` is automatically continuous. -/
noncomputable def restrictedLift (φ : A →ₐ[K] B) {b : Fin k → B}
    (hb : ∀ i, Huber.IsPowerBounded (b i)) :
    IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1) →ₐ[K] B :=
  have := hA.isNoetherianRing
  { MvPowerSeries.restrictedLift (φ := (φ : A →+* B)) (hB.continuous_algHom φ) hb with
    commutes' r := by
      rw [IsScalarTower.algebraMap_apply K A (IsRestricted.subring (R := A) _)]
      exact (MvPowerSeries.restrictedLift_algebraMap _ hb _).trans (φ.commutes r) }

variable (φ : A →ₐ[K] B) {b : Fin k → B} (hb : ∀ i, Huber.IsPowerBounded (b i))

/-- `restrictedLift` extends `φ` on `A`. -/
@[simp]
theorem restrictedLift_algebraMap (a : A) :
    restrictedLift hA hB φ hb (algebraMap A _ a) = φ a :=
  MvPowerSeries.restrictedLift_algebraMap _ hb a

/-- `restrictedLift` sends each variable `Xᵢ` to `bᵢ`. -/
@[simp]
theorem restrictedLift_X (i : Fin k) : restrictedLift hA hB φ hb ⟨X i, isRestricted_X _ i⟩ = b i :=
  MvPowerSeries.restrictedLift_X _ hb i

include hA hB hb in
/-- **The universal property of restricted series over an affinoid algebra.** Let `A` and `B` be
affinoid algebras with complete ultrametric algebra norms. A `K`-algebra map `φ : A → B` and
power-bounded `b₁, …, bₖ ∈ B` extend to exactly one `K`-algebra map `A⟨X₁, …, Xₖ⟩ → B` sending
each `Xᵢ` to `bᵢ`, namely `TauCeti.IsAffinoidAlgebra.restrictedLift`. It is continuous, as is every
algebra map between such algebras (`TauCeti.IsAffinoidAlgebra.continuous_algHom`). -/
theorem existsUnique_algHom_isRestricted_subring :
    ∃! ψ : IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1) →ₐ[K] B,
      (∀ a, ψ (algebraMap A _ a) = φ a) ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i :=
  ⟨restrictedLift hA hB φ hb, ⟨restrictedLift_algebraMap hA hB φ hb, restrictedLift_X hA hB φ hb⟩,
    fun _ ⟨hC, hX⟩ ↦ algHom_ext_isRestricted_subring hA hB
      (fun a ↦ by rw [hC, restrictedLift_algebraMap]) (fun i ↦ by rw [hX, restrictedLift_X])⟩

end TauCeti.IsAffinoidAlgebra
