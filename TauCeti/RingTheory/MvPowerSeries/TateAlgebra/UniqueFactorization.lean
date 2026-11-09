/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Rueckert

/-!
# Tate algebras are unique factorisation domains

Over a complete nonarchimedean field `K`, the Tate algebra `K⟨X₁, …, Xₙ⟩` is a unique
factorisation domain. By Mathlib's `UniqueFactorizationMonoid.instIsIntegrallyClosed` it is
therefore integrally closed, so Mathlib's going-down theorem applies to every integral extension
of a Tate algebra by a domain, such as the Noether normalisation of an affinoid domain.

The proof is by induction on the number of variables, writing `K⟨X, Y⟩` as the univariate Tate
algebra `K⟨X⟩⟨Y⟩`. The inclusion `K⟨X⟩[Y] → K⟨X⟩⟨Y⟩` satisfies the Rückert hypotheses for the
Weierstrass polynomials (`TauCeti.MvPowerSeries.isRueckert_polynomialToRestricted`), and
Rückert's factorial descent (`RingHom.IsRueckert.uniqueFactorizationMonoid`) passes unique
factorisation from `K⟨X⟩` to `K⟨X⟩⟨Y⟩`.

## Main results

* `TauCeti.MvPowerSeries.uniqueFactorizationMonoid`: the Tate algebra in finitely many variables
  over a complete nonarchimedean field is a unique factorisation domain.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.6,
  Theorem 1, using the descent of §5.2.5.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- The inductive step: if the Tate algebra `K⟨X⟩` is a unique factorisation domain, so is
`K⟨X, Y⟩`. -/
private theorem uniqueFactorizationMonoid_option {σ : Type*} [Finite σ]
    [UniqueFactorizationMonoid (Tate σ)] : UniqueFactorizationMonoid (Tate (Option σ)) := by
  have := (isRueckert_polynomialToRestricted (K := K) (σ := σ)).uniqueFactorizationMonoid
  exact (restrictedOptionEquiv (R := K) (σ := σ) (c := fun _ ↦ 1)).symm.toMulEquiv
    |>.uniqueFactorizationMonoid this

/-- **Tate algebras are unique factorisation domains.** Over a complete nonarchimedean field `K`,
the Tate algebra `K⟨X₁, …, Xₙ⟩` in finitely many variables is a unique factorisation domain. -/
instance uniqueFactorizationMonoid {σ : Type*} [Finite σ] :
    UniqueFactorizationMonoid (Tate σ) := by
  refine Finite.induction_empty_option (P := fun σ ↦ UniqueFactorizationMonoid (Tate σ))
    (fun {α β} e h ↦ ?_) ?_ (fun _ ↦ uniqueFactorizationMonoid_option) σ
  · -- Renaming the variables along `e : α ≃ β` is a ring isomorphism of Tate algebras.
    exact (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1).toMulEquiv.uniqueFactorizationMonoid h
  · -- Without variables every series is a constant, so the Tate algebra is isomorphic to `K`.
    exact (RingEquiv.ofBijective (algebraMap K (Tate PEmpty))
      ⟨(algebraMap K _).injective, algebraMap_isRestrictedSubring_surjective⟩).toMulEquiv
      |>.uniqueFactorizationMonoid inferInstance

end TauCeti.MvPowerSeries
