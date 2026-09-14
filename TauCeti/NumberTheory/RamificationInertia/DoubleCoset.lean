/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.GoingUp
public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.FixedField

/-!
# The double coset law for splitting in a non-Galois subfield

Let `M / K` be a finite Galois extension of number fields with group `G`, let `H` be a subgroup of
`G`, and let `E = M ^ H` be its fixed field, an intermediate field that need not be Galois over
`K`.  Fix a prime `p` of `𝓞 K` and a prime `Q` of `𝓞 M` above it, and let `D` be the
decomposition group of `Q`, that is, the stabilizer of `Q` in `G`.  This file proves that the
primes of `𝓞 E` above `p` are in bijection with the double cosets `H \ G / D`, the class of `σ`
corresponding to the contraction `σ Q ∩ 𝓞 E`.

The bijection separates into two ingredients.  Two primes of `𝓞 M` have the same contraction to
`𝓞 E` exactly when they lie in one `H`-orbit, because `H` is the Galois group of `M / E` and a
Galois group acts transitively on the primes above a fixed prime; this is
`Ideal.under_fixedField_eq_iff_mem_orbit`, and it is where all the arithmetic sits.  The rest is
the group-theoretic identity that the `H`-orbits inside a transitive `G`-set are indexed by the
`H`-`D` double cosets, which is `TauCeti.orbitRel_smul_iff_mem_doubleCoset_stabilizer`.

Contracting from `𝓞 M` rather than working inside `𝓞 E` directly is what makes all of this
possible: a prime of a non-Galois subfield has no Galois-theoretic description of its own, and the
bijection is the dictionary that supplies one.

## Main definitions

* `Ideal.doubleCosetQuotientEquivPrimesOver`: the bijection `H \ G / D ≃ p.primesOver (𝓞 E)`.

## Main results

* `Ideal.under_fixedField_eq_iff_mem_orbit`: two primes of `𝓞 M` contract to the same prime of
  `𝓞 E` exactly when one is an `H`-translate of the other.
* `Ideal.under_fixedField_smul_eq_iff_doubleCosetMk_eq`: the contractions of `σ Q` and `τ Q` to
  `𝓞 E` agree exactly when `σ` and `τ` lie in one `H`-`D` double coset.
* `Ideal.exists_smul_under_fixedField_eq`: every prime of `𝓞 E` above `p` is such a contraction.
* `Ideal.doubleCosetQuotientEquivPrimesOver_mk`: the bijection sends the class of `σ` to
  `σ Q ∩ 𝓞 E`.
* `Ideal.card_doubleCosetQuotient_eq_card_primesOver`: the resulting count.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, where the statement is
  recorded on page 55 and its proof is left to the reader.  G. J. Janusz, *Algebraic Number
  Fields*, Chapter I, gives a complete treatment.
-/

public section

open IntermediateField MulAction NumberField

open scoped NumberField Pointwise

namespace Ideal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-- **Same contraction to the fixed field means same `H`-orbit.**  For a subgroup `H` of
`Gal(M/K)` with fixed field `E = M ^ H`, two primes of `𝓞 M` contract to the same prime of `𝓞 E`
exactly when one is an `H`-translate of the other.

The forward direction is transitivity of `Gal(M/E)` on the primes above a fixed prime of `𝓞 E`,
read through the Galois correspondence `H ≃* Gal(M/E)`; the reverse direction is that an
automorphism fixing `E` pointwise does not move a contraction to `𝓞 E`.  Neither direction needs
`M / K` to be Galois: `M / E` is Galois on its own, being the fixed field of a finite group acting
on `M`. -/
theorem under_fixedField_eq_iff_mem_orbit (R R' : Ideal (𝓞 M)) [R.IsPrime] [R'.IsPrime]
    (H : Subgroup (M ≃ₐ[K] M)) :
    R.under (𝓞 ↥(fixedField H)) = R'.under (𝓞 ↥(fixedField H)) ↔ R ∈ MulAction.orbit H R' := by
  have : IsGalois ↥(fixedField H) M := IsGalois.of_fixed_field M H
  have : IsGaloisGroup (M ≃ₐ[↥(fixedField H)] M) ↥(fixedField H) M :=
    IsGaloisGroup.of_isGalois _ M
  rw [MulAction.mem_orbit_iff]
  constructor
  · intro h
    have : R.LiesOver (R'.under (𝓞 ↥(fixedField H))) := ⟨h.symm⟩
    have : R'.LiesOver (R'.under (𝓞 ↥(fixedField H))) := over_under _
    obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isGaloisGroup (R'.under (𝓞 ↥(fixedField H))) R' R
      (M ≃ₐ[↥(fixedField H)] M)
    exact ⟨(subgroupEquivAlgEquiv H).symm ρ, by
      rw [Subgroup.smul_def, ← H.subgroupEquivAlgEquiv_smul_ideal, MulEquiv.apply_symm_apply, hρ]⟩
  · rintro ⟨h, rfl⟩
    rw [Subgroup.smul_def, ← H.subgroupEquivAlgEquiv_smul_ideal h R']
    exact under_smul _ R' _

/-- **The fibres of `σ ↦ σ Q ∩ 𝓞 (M ^ H)` are the `H`-`D` double cosets.**  With `D` the
decomposition group of `Q` in `Gal(M/K)`, the contractions of `σ Q` and `τ Q` to the fixed field
of `H` agree exactly when `σ` and `τ` have the same class in `H \ Gal(M/K) / D`. -/
theorem under_fixedField_smul_eq_iff_doubleCosetMk_eq (Q : Ideal (𝓞 M)) [Q.IsPrime]
    (H : Subgroup (M ≃ₐ[K] M)) (σ τ : M ≃ₐ[K] M) :
    (σ • Q).under (𝓞 ↥(fixedField H)) = (τ • Q).under (𝓞 ↥(fixedField H)) ↔
      DoubleCoset.mk H (stabilizer (M ≃ₐ[K] M) Q) σ
        = DoubleCoset.mk H (stabilizer (M ≃ₐ[K] M) Q) τ := by
  rw [under_fixedField_eq_iff_mem_orbit, ← MulAction.orbitRel_apply,
    TauCeti.orbitRel_smul_iff_mem_doubleCoset_stabilizer H Q σ τ,
    ← TauCeti.doubleCosetMk_eq_mk_iff_mem]

/-- **Every prime of the fixed field above `p` is a contraction of a translate of `Q`.**  For
`M / K` Galois and `Q` a prime of `𝓞 M` above `p`, a prime `𝔮` of `𝓞 (M ^ H)` above `p` is
`σ Q ∩ 𝓞 (M ^ H)` for some `σ` in `Gal(M/K)`.

This is transitivity of `Gal(M/K)` on the primes of `𝓞 M` above `p`, transported downwards: `𝔮`
has some prime of `𝓞 M` above it, that prime lies above `p` as well, and so is a translate
of `Q`. -/
theorem exists_smul_under_fixedField_eq [IsGalois K M] (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M))
    [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M))
    (𝔮 : Ideal (𝓞 ↥(fixedField H))) [𝔮.IsPrime] [𝔮.LiesOver p] :
    ∃ σ : M ≃ₐ[K] M, (σ • Q).under (𝓞 ↥(fixedField H)) = 𝔮 := by
  obtain ⟨⟨R, hRp, hRo⟩⟩ := 𝔮.nonempty_primesOver (S := 𝓞 M)
  have : R.LiesOver p := LiesOver.trans R 𝔮 p
  have : IsGaloisGroup (M ≃ₐ[K] M) K M := IsGaloisGroup.of_isGalois _ M
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isGaloisGroup p Q R (M ≃ₐ[K] M)
  exact ⟨σ, by rw [hσ]; exact hRo.over.symm⟩

/-- The contraction of `σ Q` to the fixed field of `H`, as a prime of `𝓞 (M ^ H)` above `p`. -/
private def underFixedFieldPrimesOver (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M)) [Q.IsPrime]
    [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    p.primesOver (𝓞 ↥(fixedField H)) :=
  ⟨(σ • Q).under (𝓞 ↥(fixedField H)), inferInstance,
    ⟨by rw [under_under]; exact (inferInstance : (σ • Q).LiesOver p).over⟩⟩

/-- **The double coset law.**  For `M / K` a finite Galois extension of number fields with group
`G`, a subgroup `H ≤ G` with fixed field `E = M ^ H`, a prime `p` of `𝓞 K` and a prime `Q` of
`𝓞 M` above it with decomposition group `D`, the primes of `𝓞 E` above `p` are indexed by the
double cosets `H \ G / D`.

The class of `σ` corresponds to the contraction `σ Q ∩ 𝓞 E`, by
`Ideal.doubleCosetQuotientEquivPrimesOver_mk`. -/
noncomputable def doubleCosetQuotientEquivPrimesOver [IsGalois K M] (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M)) :
    DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M)) (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)) ≃
      p.primesOver (𝓞 ↥(fixedField H)) :=
  Equiv.ofBijective
    (fun q ↦ q.liftOn' (underFixedFieldPrimesOver p Q H) fun σ τ hστ ↦
      Subtype.ext ((under_fixedField_smul_eq_iff_doubleCosetMk_eq Q H σ τ).2 (Quotient.sound' hστ)))
    ⟨by
      refine fun q r hqr ↦ ?_
      induction q using Quotient.inductionOn' with | h σ =>
      induction r using Quotient.inductionOn' with | h τ =>
      exact (under_fixedField_smul_eq_iff_doubleCosetMk_eq Q H σ τ).1 (Subtype.ext_iff.1 hqr), by
      rintro ⟨𝔮, h𝔮p, h𝔮o⟩
      obtain ⟨σ, hσ⟩ := exists_smul_under_fixedField_eq p Q H 𝔮
      refine ⟨DoubleCoset.mk H _ σ, Subtype.ext ?_⟩
      -- `Quotient.liftOn'` at a representative reduces only definitionally, and the underlying
      -- function is `private`, so the goal has to be restated before `hσ` closes it.
      change (σ • Q).under (𝓞 ↥(fixedField H)) = 𝔮
      exact hσ⟩

/-- The double coset law sends the class of `σ` to the contraction `σ Q ∩ 𝓞 (M ^ H)`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOver_mk [IsGalois K M] (p : Ideal (𝓞 K)) (Q : Ideal (𝓞 M))
    [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    (doubleCosetQuotientEquivPrimesOver p Q H (DoubleCoset.mk H _ σ) :
        Ideal (𝓞 ↥(fixedField H)))
      = (σ • Q).under (𝓞 ↥(fixedField H)) :=
  (rfl)

/-- **The number of primes above `p` in a subfield is a number of double cosets.** -/
theorem card_doubleCosetQuotient_eq_card_primesOver [IsGalois K M] (p : Ideal (𝓞 K))
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver p] (H : Subgroup (M ≃ₐ[K] M)) :
    Nat.card (DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)))
      = Nat.card (p.primesOver (𝓞 ↥(fixedField H))) :=
  Nat.card_congr (doubleCosetQuotientEquivPrimesOver p Q H)

end Ideal
