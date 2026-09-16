/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius

/-!
# Frobenius fibres in a cyclotomic compositum

Let `L / K` be a Galois extension of number fields and let `M = L(μ_m)`, with `M / K` Galois. An
automorphism `ρ` of `M / K` is determined by two coordinates: its restriction to `L`, and its
cyclotomic character `IsPrimitiveRoot.autToPow`, which records how it moves the `m`-th roots of
unity. This file computes both coordinates of the Artin class of a prime `𝔭` of `𝓞 K` that is
unramified in `M` and does not divide `m`: the first is the Artin class of `𝔭` in `L / K`, with no
power taken, and the second is `𝔑𝔭 mod m`.

So the fibre of `[ρ]` over `M` is cut out of the fibre of `[ρ|_L]` over `L` by the congruence
`𝔑𝔭 ≡ autToPow ρ (mod m)`. Since the character lands in the commutative group `(ZMod m)ˣ`, its
value is a single residue even though the Artin class is only a conjugacy class. In the joint
coordinates `Gal(M/K) ≃ Gal(L/K) × (ZMod m)ˣ` of `IsCyclotomicExtension.galEquivProd`, the fibre
of the class of `(σ, τ)` consists of the primes in the fibre of `[σ]` over `L` with `𝔑𝔭 ≡ τ`.

This is the Frobenius compatibility on which the cyclotomic crossing argument for the Chebotarev
density theorem rests: it identifies which primes of `K` a Frobenius fibre of the compositum
counts.

Unramifiedness in `M` and `𝔭 ∤ m` are hypotheses. The second cannot be dropped: for `m = 2` the
field `M` is `L`, a prime above `2` may be unramified, and `𝔑𝔭` is then not a unit modulo `m`.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow`: for `𝔭`
  unramified in `M` with `𝔭 ∤ m`, the prime lies in the fibre of `[ρ]` over `M` exactly when it
  lies in the fibre of `[ρ|_L]` over `L` and `autToPow ρ = 𝔑𝔭` in `ZMod m`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_galEquivProd_symm_iff`: the same statement in the
  coordinates of `IsCyclotomicExtension.galEquivProd`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, for Frobenius elements in towers.
* R. Sharifi, *Algebraic Number Theory*, Proposition 7.2.1 and the proof of Theorem 7.2.2, where
  the Frobenius of a cyclotomic compositum is read off from its restriction and its action on
  roots of unity.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L]
  [IsGalois K M] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} L M]

/-- **The Frobenius fibre of the cyclotomic compositum.** Let `M = L(μ_m)` for a Galois extension
`L / K`, let `ζ` be a primitive `m`-th root of unity in `M`, and let `𝔭` be a prime of `𝓞 K` that
is unramified in `M` and does not divide `m`. Then `𝔭` lies in the fibre of the class of
`ρ : Gal(M/K)` exactly when it lies in the fibre of the class of `ρ|_L` over `L` and the cyclotomic
character of `ρ` is `𝔑𝔭 mod m`.

The class of `ρ` is recovered from those two coordinates although only the first is a conjugacy
class: the second lives in a commutative group, and an automorphism of `M` is determined by its
restriction to `L` together with its cyclotomic character. -/
theorem mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (hur : ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) (ρ : Gal(M/K)) :
    𝔭 ∈ frobeniusPrimeSet K M (ConjClasses.mk ρ) ↔
      𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk (ρ.restrictNormal L)) ∧
        (hζ.autToPow K ρ : ZMod m) = Ideal.absNorm 𝔭.asIdeal := by
  -- The forward direction holds for every class, and is reused for a Frobenius below.
  have forward : ∀ φ : Gal(M/K), 𝔭 ∈ frobeniusPrimeSet K M (ConjClasses.mk φ) →
      𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk (φ.restrictNormal L)) ∧
        (hζ.autToPow K φ : ZMod m) = Ideal.absNorm 𝔭.asIdeal := by
    intro φ h
    obtain ⟨Q, hφ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h
    have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
    have hL := frobeniusPrimeSet_subset_map_restrictNormalHom (M := L) _ h
    rw [ConjClasses.map_mk, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply] at hL
    exact ⟨hL, hφ.autToPow_eq_absNorm hζ 𝔭 hm Q.1⟩
  refine ⟨forward ρ, fun ⟨hL, hτ⟩ ↦ ?_⟩
  -- Take a Frobenius `φ` at a prime above `𝔭`; its two coordinates are those of `ρ` up to
  -- conjugating the first, and a lift of the conjugator conjugates `φ` to `ρ`.
  let Q : 𝔭.asIdeal.primesOver (𝓞 M) := Classical.choice inferInstance
  have : Q.1.IsPrime := Q.2.1
  have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
  obtain ⟨φ, hφ⟩ := exists_isArithFrobAt K Q.1
    (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)
  have hφM := mem_frobeniusPrimeSet_mk_of_isArithFrobAt hur Q.1 hφ
  obtain ⟨hφL, hφτ⟩ := forward φ hφM
  have hclass : ConjClasses.mk (φ.restrictNormal L) = ConjClasses.mk (ρ.restrictNormal L) := by
    by_contra hne
    exact Set.disjoint_left.mp (disjoint_frobeniusPrimeSet hne) hφL hL
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) M c
  have hconj : g * φ * g⁻¹ = ρ := by
    refine IsCyclotomicExtension.restrictNormalHom_prod_autToPow_injective K L M m hζ ?_
    simp only [map_mul, map_inv, MonoidHom.prod_apply, Prod.mk_mul_mk, Prod.inv_mk,
      mul_inv_cancel_comm, Prod.mk.injEq]
    refine ⟨?_, Units.ext (hφτ.trans hτ.symm)⟩
    -- `restrictNormalHom` is `MonoidHom.mk'` around `restrictNormal`, in which `hc` is stated.
    simpa only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply] using hc
  rw [← hconj, ← ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)]
  exact hφM

/-- **The tagged Frobenius fibre of the cyclotomic compositum.** In the coordinates
`Gal(M/K) ≃ Gal(L/K) × (ZMod m)ˣ` of `IsCyclotomicExtension.galEquivProd`, a prime `𝔭` of `𝓞 K`
unramified in `M` and not dividing `m` lies in the fibre of the class of `(σ, τ)` exactly when it
lies in the fibre of `[σ]` over `L` and `𝔑𝔭 ≡ τ (mod m)`. -/
theorem mem_frobeniusPrimeSet_galEquivProd_symm_iff
    (hcop : ((NumberField.discr L).natAbs).Coprime m) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (hur : ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    {ζ : M} (hζ : IsPrimitiveRoot ζ m) (σ : Gal(L/K)) (τ : (ZMod m)ˣ) :
    𝔭 ∈ frobeniusPrimeSet K M
        (ConjClasses.mk ((IsCyclotomicExtension.galEquivProd K L M m hcop hζ).symm (σ, τ))) ↔
      𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) ∧ (τ : ZMod m) = Ideal.absNorm 𝔭.asIdeal := by
  rw [mem_frobeniusPrimeSet_mk_iff_restrictNormal_autToPow (L := L) hm hur hζ,
    IsCyclotomicExtension.restrictNormal_galEquivProd_symm,
    IsCyclotomicExtension.autToPow_galEquivProd_symm]

end NumberField.Chebotarev
