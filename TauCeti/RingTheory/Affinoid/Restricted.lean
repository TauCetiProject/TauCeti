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
`MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring` applies. The images of the
variables need only be power-bounded, not of norm at most one.

## Main results

* `TauCeti.IsAffinoidAlgebra.isRestricted_subring`: `A⟨X₁, …, Xₘ⟩` is affinoid.
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
  let e := restrictedSumAlgEquiv (R := K) (c := fun _ : τ ↦ (1 : ℝ)) (d := fun _ : Fin n ↦ 1)
  have hΦ (r : K) : Φ (e (algebraMap K _ r)) = algebraMap K _ r := by
    refine Subtype.ext (ext fun t ↦ ?_)
    simp only [Φ]
    rw [e.commutes, coeff_restrictedMap, coe_algebraMap_isRestrictedSubring_apply,
      coe_algebraMap_isRestrictedSubring_apply, coeff_C, coeff_C]
    by_cases ht : t = 0
    · simp [ht, π']
    · simp [ht]
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

/-- **The universal property of restricted series over an affinoid algebra.** Let `A` and `B` be
affinoid algebras with complete ultrametric algebra norms. A `K`-algebra map `φ : A → B` and
power-bounded `b₁, …, bₖ ∈ B` extend to exactly one `K`-algebra map `A⟨X₁, …, Xₖ⟩ → B` sending
each `Xᵢ` to `bᵢ`. It is continuous, as is every algebra map between such algebras
(`TauCeti.IsAffinoidAlgebra.continuous_algHom`). -/
theorem existsUnique_algHom_isRestricted_subring {k : ℕ} (hA : IsAffinoidAlgebra K A)
    {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
    (hB : IsAffinoidAlgebra K B) (φ : A →ₐ[K] B) {b : Fin k → B}
    (hb : ∀ i, Huber.IsPowerBounded (b i)) :
    ∃! ψ : IsRestricted.subring (R := A) (fun _ : Fin k ↦ 1) →ₐ[K] B,
      (∀ a, ψ (algebraMap A _ a) = φ a) ∧ ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  have := hA.isNoetherianRing
  have := (hA.isRestricted_subring (τ := Fin k)).isNoetherianRing
  obtain ⟨ψ, ⟨-, hψC, hψX⟩, huniq⟩ :=
    existsUnique_continuous_ringHom_isRestricted_subring (φ := (φ : A →+* B))
      (hB.continuous_algHom φ) hb
  refine ⟨{ ψ with commutes' r := ?_ }, ⟨hψC, hψX⟩, fun ψ' ⟨hψ'C, hψ'X⟩ ↦
    AlgHom.toRingHom_injective (huniq ψ' ⟨hB.continuous_algHom ψ', hψ'C, hψ'X⟩)⟩
  simpa [IsScalarTower.algebraMap_apply K A (IsRestricted.subring (R := A) _)] using
    hψC (algebraMap K A r)

end TauCeti.IsAffinoidAlgebra
