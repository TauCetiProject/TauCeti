/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# Inertness in a CM field through complex conjugation

Let `K` be a CM field with maximal real subfield `K⁺`, so that `K / K⁺` is Galois with group
`{1, c}`, `c` the complex conjugation (`NumberField.IsCMField.complexConj`). For a prime `P` of
`𝓞 K` unramified over `K⁺`, the decomposition group of `P` has order the inertia degree of `P`
over `K⁺` (`Ideal.card_stabilizer_eq_ramificationIdx_mul_inertiaDeg`). So the place of `K⁺` below
`P` is inert in `K`, that is `P` has inertia degree `2 = [K : K⁺]`, exactly when the decomposition
group is all of `{1, c}`, that is when `c` fixes `P`.

By multiplicativity of inertia degrees in the tower `ℤ ⊆ 𝓞 K⁺ ⊆ 𝓞 K`, for `P` unramified over `ℚ`
the condition `f(P | ℤ) = 2 f(w | ℤ)` on the place `w` of `K⁺` below `P`, which is the form of
inertness in `IsDedekindDomain.HeightOneSpectrum.IsFriendly`, holds exactly when `c` fixes `P`.
This is the relative form, for the CM field `E_K` over `K⁺`, of the decomposition-group description
of friendly places (Lawrence–Venkatesh, §2.4, Definition 2.7).

## Main results

* `Ideal.inertiaDeg_eq_natCard_iff_forall_smul_eq`: in a Galois extension with group `G`, a prime
  unramified over the base has inertia degree `|G|` exactly when `G` fixes it.
* `NumberField.IsCMField.inertiaDeg_eq_two_iff_complexConj_smul_eq`: a prime of a CM field
  unramified over `K⁺` has inertia degree `2` over `K⁺` exactly when complex conjugation fixes it.
* `NumberField.IsCMField.inertiaDeg_eq_two_mul_iff_complexConj_smul_eq`: a prime `P` of a CM field
  unramified over `ℚ` satisfies `f(P | ℤ) = 2 f(w | ℤ)`, for `w` the prime of `K⁺` below it,
  exactly when complex conjugation fixes `P`.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4,
  Definition 2.7.
-/

public section

open NumberField

open scoped Pointwise

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [IsDomain R] [IsDomain S] [Module.Finite R S]
  [Module.Flat R S]

/-- **Inertia degree `|G|` means `G` fixes the prime.** In a Galois extension `S / R` with group
`G`, a prime `P` of `S` unramified over `R` has inertia degree `|G|` exactly when every element of
`G` fixes `P`: its decomposition group then has order its inertia degree. -/
theorem inertiaDeg_eq_natCard_iff_forall_smul_eq (P : Ideal S) [P.IsPrime]
    (he : P.ramificationIdx R = 1) : P.inertiaDeg R = Nat.card G ↔ ∀ g : G, g • P = P := by
  have := IsGaloisGroup.finite G R S
  have h := card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (R := R) (G := G) P
  rw [he, one_mul] at h
  rw [← h, Subgroup.card_eq_iff_eq_top, Subgroup.eq_top_iff']
  simp only [MulAction.mem_stabilizer_iff]

end Ideal

namespace NumberField.IsCMField

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

/-- **Inertness in `K / K⁺` through complex conjugation.** A prime `P` of a CM field `K`
unramified over the maximal real subfield `K⁺` has inertia degree `2` over `K⁺`, that is lies
over a place of `K⁺` inert in `K`, exactly when complex conjugation fixes `P`. -/
theorem inertiaDeg_eq_two_iff_complexConj_smul_eq (P : Ideal (𝓞 K)) [P.IsPrime]
    (he : P.ramificationIdx (𝓞 (maximalRealSubfield K)) = 1) :
    P.inertiaDeg (𝓞 (maximalRealSubfield K)) = 2 ↔ complexConj K • P = P := by
  have hcard : Nat.card (K ≃ₐ[maximalRealSubfield K] K) = 2 :=
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K) ▸
      IsGalois.card_aut_eq_finrank (maximalRealSubfield K) K
  rw [← hcard, Ideal.inertiaDeg_eq_natCard_iff_forall_smul_eq _ P he]
  refine ⟨fun h ↦ h _, fun h g ↦ ?_⟩
  -- `c` generates the Galois group, so it fixes `P` only if every element does
  have hg : g ∈ Subgroup.zpowers (complexConj K) := by
    rw [zpowers_complexConj_eq_top]
    trivial
  exact (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h) hg :
    g ∈ MulAction.stabilizer _ P)

/-- **Inertness over `ℤ` through complex conjugation.** Let `P` be a maximal ideal of the ring of
integers of a CM field `K`, unramified over `ℚ`, and `w` the prime of `K⁺` below it. Then
`f(P | ℤ) = 2 f(w | ℤ)`, which says that `w` is inert in `K`, exactly when complex conjugation
fixes `P`. -/
theorem inertiaDeg_eq_two_mul_iff_complexConj_smul_eq (P : Ideal (𝓞 K)) [P.IsMaximal]
    (he : P.ramificationIdx ℤ = 1) :
    P.inertiaDeg ℤ = 2 * (P.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ ↔
      complexConj K • P = P := by
  set w := P.under (𝓞 (maximalRealSubfield K))
  rw [Ideal.ramificationIdx_tower w P, mul_eq_one] at he
  rw [← inertiaDeg_eq_two_iff_complexConj_smul_eq P he.2, Ideal.inertiaDeg_tower w P, mul_comm,
    Nat.mul_left_inj (Ideal.inertiaDeg_pos w ℤ).ne']

end NumberField.IsCMField
