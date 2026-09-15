/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# How many primes carry a given Frobenius element

Let `L / K` be a finite Galois extension of number fields, `𝔭` an ideal of `𝓞 K` and `σ` an
element of `Gal(L/K)`. The primes of `𝓞 L` above `𝔭` at which `σ` is an arithmetic Frobenius form
the *fiber* of `σ`, and `Ideal.frobenius_fiber_card_eq_of_isConj` shows that conjugate elements
have fibers of the same size. This file computes that size, at a prime where `σ` is a Frobenius
and `L / K` is unramified:

```text
#(fiber of σ) * orderOf σ = #Centralizer_{Gal(L/K)}(σ)
```

The reason is that the fiber is a single orbit. `Gal(L/K)` acts transitively on the primes above
`𝔭`, and the Frobenius at `τ • Q` is `τ σ τ⁻¹`, so the elements carrying `Q` to another member of
the fiber are exactly those commuting with `σ`. The stabilizer of `Q` inside that centralizer is
the decomposition group `⟨σ⟩`, whose order is `orderOf σ`, and the orbit-stabilizer theorem gives
the count.

The identity is stated as a product rather than as `#Centralizer(σ) / orderOf σ` so that it says
something without a separate divisibility: `orderOf σ` divides the centralizer's order because
`⟨σ⟩` is a subgroup of it, and `ConjClasses.card_carrier_mul_orderOf_dvd` records the companion
divisibility for a whole conjugacy class.

## Main results

* `Ideal.frobenius_fiber_eq_orbit_centralizer`: the fiber of `σ` above `𝔭` is the orbit of any of
  its members under the centralizer of `σ`.
* `Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer`: its size, times `orderOf σ`, is
  the order of that centralizer.
* `Ideal.heightOneFrobeniusFiberEquiv`: the height-one-prime and ideal representations of the
  fiber are equivalent.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

public section

open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

-- Source. The count is specified by the Chebotarev roadmap:
-- `TauCetiRoadmap/Chebotarev/README.md` §8.2, which displays the fibre size as
-- `#G / (#C * f) = #Centralizer_G(σ) / f` with `f = orderOf σ`. The theorems below count the
-- primes of `𝓞 L`; the roadmap's own statement counts primes of the fixed field `L ^ ⟨σ⟩`, and
-- reaches this one through the residue degree of a fixed-field prime.

/-- **The Frobenius fiber is an orbit of the centralizer.** Let `Q` be a prime of `𝓞 L` above an
ideal `𝔭` of `𝓞 K`, unramified over `𝓞 K`, with `σ` an arithmetic Frobenius at `Q`. Then
the primes above `𝔭` admitting `σ` as a Frobenius are exactly the translates of `Q` by elements
commuting with `σ`.

Both inclusions come from `Ideal.isArithFrobAt_pointwise_smul_iff_eq_conj`, which says the
Frobenius elements at `τ • Q` are the conjugates `τ σ τ⁻¹`: an element of `Gal(L/K)` carries `Q`
into the fiber exactly when conjugation by it fixes `σ`. Transitivity of the action on the primes
above `𝔭` is what makes every member of the fiber such a translate. -/
theorem frobenius_fiber_eq_orbit_centralizer (𝔭 : Ideal (𝓞 K)) {σ : L ≃ₐ[K] L}
    (Q : Ideal (𝓞 L)) [IsGalois K L] [Q.IsPrime] [Q.LiesOver 𝔭]
    [Algebra.IsUnramifiedAt (𝓞 K) Q]
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    {P : Ideal (𝓞 L) | ∃ (_ : P.IsPrime) (_ : P.LiesOver 𝔭) (_ : P ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ P}
      = MulAction.orbit (Subgroup.centralizer {σ}) Q := by
  ext P
  constructor
  · rintro ⟨_, _, -, hfrob⟩
    obtain ⟨τ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭 Q P (L ≃ₐ[K] L)
    have h := (Q.isArithFrobAt_pointwise_smul_iff_eq_conj hσ τ σ).mp hfrob
    exact ⟨⟨τ, Subgroup.mem_centralizer_singleton_iff.mpr (eq_mul_inv_iff_mul_eq.mp h).symm⟩,
      Subgroup.smul_def _ Q⟩
  · rintro ⟨⟨τ, hτ⟩, hP⟩
    simp only [Subgroup.smul_def] at hP
    subst hP
    have hconj : τ * σ * τ⁻¹ = σ := by
      rw [mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff.mp hτ]
    exact ⟨inferInstance, inferInstance, by simpa using (MulAction.injective τ).ne hσ.ne_bot,
      (Q.isArithFrobAt_pointwise_smul_iff_eq_conj hσ τ σ).mpr hconj.symm⟩

/-- **The size of a Frobenius fiber.** At an unramified prime `Q` above an ideal `𝔭` with
arithmetic Frobenius `σ`, the number of primes above `𝔭` admitting `σ` as a Frobenius, times the
order of `σ`, is the order of the centralizer of `σ` in `Gal(L/K)`.

This is the orbit-stabilizer theorem applied to `frobenius_fiber_eq_orbit_centralizer`: the
stabilizer of `Q` in the centralizer is the decomposition group `⟨σ⟩`, of order `orderOf σ`.

Compare `Ideal.frobenius_fiber_card_eq_of_isConj`, which says fibers of conjugate elements have
equal size without saying what that size is. -/
theorem frobenius_fiber_card_mul_orderOf_eq_card_centralizer (𝔭 : Ideal (𝓞 K))
    {σ : L ≃ₐ[K] L} (Q : Ideal (𝓞 L)) [IsGalois K L] [Q.IsPrime] [Q.LiesOver 𝔭]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    Nat.card {P : Ideal (𝓞 L) // ∃ (_ : P.IsPrime) (_ : P.LiesOver 𝔭) (_ : P ≠ ⊥),
        IsArithFrobAt (𝓞 K) σ P} * orderOf σ
      = Nat.card (Subgroup.centralizer {σ}) := by
  have hle : Subgroup.zpowers σ ≤ Subgroup.centralizer {σ} :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hstab : MulAction.stabilizer (Subgroup.centralizer {σ}) Q
      = (Subgroup.zpowers σ).subgroupOf (Subgroup.centralizer {σ}) := by
    ext τ
    rw [Subgroup.mem_subgroupOf, Q.zpowers_eq_stabilizer_of_isArithFrobAt hσ.ne_bot hσ,
      MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have key := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Subgroup.centralizer {σ}) Q)
  rw [Nat.card_prod, hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_zpowers] at key
  have hcard : Nat.card {P : Ideal (𝓞 L) // ∃ (_ : P.IsPrime) (_ : P.LiesOver 𝔭) (_ : P ≠ ⊥),
      IsArithFrobAt (𝓞 K) σ P}
      = Nat.card (MulAction.orbit (Subgroup.centralizer {σ}) Q) :=
    Nat.card_congr (Set.equivOfEq (frobenius_fiber_eq_orbit_centralizer 𝔭 Q hσ))
  rw [hcard]
  exact key

/-- The equivalence between the height-one-prime and ideal representations of a Frobenius fiber
above `p`, induced by `HeightOneSpectrum.asIdeal`. -/
noncomputable def heightOneFrobeniusFiberEquiv
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 L) //
        Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal} ≃
      {Q : Ideal (𝓞 L) // ∃ (_ : Q.IsPrime) (_ : Q.LiesOver p.asIdeal) (_ : Q ≠ ⊥),
        IsArithFrobAt (𝓞 K) sigma Q} := by
  let hdiv : ∀ Q : HeightOneSpectrum (𝓞 L),
      Q.under (𝓞 K) = p ↔
        Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal := fun Q ↦ by
    rw [← Ideal.liesOver_iff_dvd_map Q.isPrime.ne_top]
    exact ⟨fun h ↦ ⟨(congrArg HeightOneSpectrum.asIdeal h).symm⟩,
      fun h ↦ HeightOneSpectrum.ext h.over.symm⟩
  let domainEquiv :
      {Q : HeightOneSpectrum (𝓞 L) //
          Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal} ≃
        {Q : {Q : HeightOneSpectrum (𝓞 L) //
            Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal} //
          IsArithFrobAt (𝓞 K) sigma Q.1.asIdeal} :=
    { toFun Q := ⟨⟨Q.1, (hdiv Q).mp Q.2.1⟩, Q.2.2⟩
      invFun Q := ⟨Q.1.1, ⟨(hdiv Q.1.1).mpr Q.1.2, Q.2⟩⟩
      left_inv Q := Subtype.ext rfl
      right_inv Q := Subtype.ext (Subtype.ext rfl) }
  let coreEquiv :
      {Q : {Q : HeightOneSpectrum (𝓞 L) //
          Q.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p.asIdeal} //
        IsArithFrobAt (𝓞 K) sigma Q.1.asIdeal} ≃
        {Q : p.asIdeal.primesOver (𝓞 L) // IsArithFrobAt (𝓞 K) sigma Q.1} :=
    (HeightOneSpectrum.equivPrimesOver (𝓞 L) p.ne_bot).subtypeEquiv fun _ ↦ Iff.rfl
  let codomainEquiv :
      {Q : p.asIdeal.primesOver (𝓞 L) // IsArithFrobAt (𝓞 K) sigma Q.1} ≃
        {Q : Ideal (𝓞 L) // ∃ (_ : Q.IsPrime) (_ : Q.LiesOver p.asIdeal) (_ : Q ≠ ⊥),
          IsArithFrobAt (𝓞 K) sigma Q} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun Q : Ideal (𝓞 L) ↦ Q ∈ p.asIdeal.primesOver (𝓞 L))
      (fun Q ↦ IsArithFrobAt (𝓞 K) sigma Q)).trans
      (Equiv.subtypeEquivRight fun Q ↦ by
        constructor
        · rintro ⟨hQ, hfrob⟩
          exact ⟨hQ.1, hQ.2, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ, hfrob⟩
        · rintro ⟨hprime, hover, -, hfrob⟩
          exact ⟨⟨hprime, hover⟩, hfrob⟩)
  exact domainEquiv.trans (coreEquiv.trans codomainEquiv)

@[simp]
theorem heightOneFrobeniusFiberEquiv_apply
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K))
    (Q : {Q : HeightOneSpectrum (𝓞 L) //
      Q.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) sigma Q.asIdeal}) :
    (heightOneFrobeniusFiberEquiv sigma p Q : Ideal (𝓞 L)) = Q.1.asIdeal := by
  change ((HeightOneSpectrum.equivPrimesOver (𝓞 L) p.ne_bot) _ : Ideal (𝓞 L)) =
    Q.1.asIdeal
  rw [HeightOneSpectrum.equivPrimesOver_apply]
  rfl

@[simp]
theorem heightOneFrobeniusFiberEquiv_symm_apply_asIdeal
    (sigma : L ≃ₐ[K] L) (p : HeightOneSpectrum (𝓞 K))
    (Q : {Q : Ideal (𝓞 L) // ∃ (_ : Q.IsPrime) (_ : Q.LiesOver p.asIdeal) (_ : Q ≠ ⊥),
      IsArithFrobAt (𝓞 K) sigma Q}) :
    ((heightOneFrobeniusFiberEquiv sigma p).symm Q).1.asIdeal = Q.1 := by
  calc
    ((heightOneFrobeniusFiberEquiv sigma p).symm Q).1.asIdeal =
        (heightOneFrobeniusFiberEquiv sigma p
          ((heightOneFrobeniusFiberEquiv sigma p).symm Q) : Ideal (𝓞 L)) :=
      (heightOneFrobeniusFiberEquiv_apply sigma p _).symm
    _ = Q.1 := congrArg Subtype.val
      ((heightOneFrobeniusFiberEquiv sigma p).apply_symm_apply Q)

end Ideal
