/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
public import TauCeti.RingTheory.MvPowerSeries.NonZeroDivisors
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Tate algebras are unique factorisation domains

Over a complete nonarchimedean field `K`, the Tate algebra `K⟨X₁, …, Xₙ⟩` is a unique
factorisation domain. By Mathlib's `UniqueFactorizationMonoid.instIsIntegrallyClosed` it is
therefore integrally closed, so Mathlib's going-down theorem applies to every integral extension
of a Tate algebra by a domain, such as the Noether normalisation of an affinoid domain.

The proof is by induction on the number of variables, writing `K⟨X, Y⟩` as the univariate Tate
algebra `K⟨X⟩⟨Y⟩`. Since `K⟨X, Y⟩` is a noetherian domain, it suffices to show that every
irreducible element `f` is prime. An automorphism makes `f` distinguished in `Y` with a unit
dominant coefficient, and Weierstrass preparation writes it as a unit multiple of a monic
polynomial `ω ∈ K⟨X⟩[Y]`. Weierstrass division identifies `K⟨X⟩[Y] ⧸ (ω)` with
`K⟨X⟩⟨Y⟩ ⧸ (ω)`. This comparison shows that `ω` is irreducible in `K⟨X⟩[Y]`, hence prime, because
`K⟨X⟩[Y]` is a unique factorisation domain by induction and Gauss's lemma. So both quotients are
domains, and `f` is prime.

## Main results

* `TauCeti.MvPowerSeries.uniqueFactorizationMonoid`: the Tate algebra in finitely many variables
  over a complete nonarchimedean field is a unique factorisation domain.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.6,
  Theorem 1. The argument here replaces the Rückert-interface descent of §5.2.5 by the
  Weierstrass quotient comparison.
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
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let ι := PowerSeries.polynomialToRestricted (R := R) 1
  have : IsNoetherianRing (Tate (Option σ)) := isNoetherianRing_isRestricted_subring
  refine { irreducible_iff_prime := fun {f} ↦ ⟨fun hf ↦ ?_, Prime.irreducible⟩ }
  -- Make `f` distinguished in `Y`, and pass to its image `g` in `S = R⟨Y⟩`.
  obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit f hf.ne_zero
  let Φ : Tate (Option σ) ≃+* S := Huber.restrictedOptionEquiv
  let E : Tate (Option σ) ≃+* S := (e : Tate (Option σ) ≃+* Tate (Option σ)).trans Φ
  have hE : E f = Φ (e f) := by simp [E]
  rw [← MulEquiv.prime_iff E, hE]
  rw [← MulEquiv.irreducible_iff E, hE] at hf
  set g : S := Φ (e f)
  -- Weierstrass preparation: `g = u * ι ω` with `u` a unit and `ω` monic.
  obtain ⟨u, ω, hu', hm, hmul⟩ := hd.exists_isUnit_isMonicOfDegree_mul_eq hu zero_lt_one g.2
  have hg : g = u * ι ω := Subtype.ext (by simpa [ι] using hmul.symm)
  have hassoc : Associated (ι ω) g := by
    rw [hg, mul_comm]
    exact associated_mul_unit_right _ _ hu'
  have hω : PowerSeries.IsDistinguished 1 s (ω : PowerSeries R) :=
    (hmul.symm ▸ hd).of_isUnit_mul zero_lt_one hu'
  -- `ω` is irreducible, hence prime, in the unique factorisation domain `R[Y]`.
  have hωp : Prime ω := UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (hω.irreducible_of_irreducible_polynomialToRestricted zero_lt_one hm
      (hassoc.symm.irreducible hf))
  -- So `S ⧸ (ι ω) ≃ R[Y] ⧸ (ω)` is a domain, and `ι ω` is prime.
  have : IsDomain (Polynomial R ⧸ Ideal.span {ω}) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr
      ((Ideal.span_singleton_prime hωp.ne_zero).mpr hωp)
  have : IsDomain (S ⧸ Ideal.span {ι ω}) :=
    (hω.polynomialQuotientEquiv zero_lt_one hm).symm.toMulEquiv.isDomain _
  exact hassoc.prime ((Ideal.span_singleton_prime (hassoc.symm.irreducible hf).ne_zero).mp
    ((Ideal.Quotient.isDomain_iff_prime _).mp this))

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
