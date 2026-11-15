/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Smooth.Flat
import TauCeti.RingTheory.Localization.LocalizationLocalization

/-!
# The closed-point factor `A × κ(A)` over a local ring

Let `A` be a local ring with residue field `κ(A)`, and let `B = A × κ(A)`, an `A`-algebra through
the diagonal map `a ↦ (a, a mod 𝔪)`. Its spectrum is `Spec A` together with one extra point, the
prime `A × 0`, which lies over the closed point of `Spec A`. Away from that extra point, `B`
agrees with `A`: localizing `B` at `(1, 0)` gives back `A`. So `B` is finite over `A`, étale at
every prime that does not lie over the maximal ideal, and normal when `A` is. When `A` is a domain
but not a field, `B` is nevertheless not torsion free, hence neither flat nor étale over `A`.

For `A` a normal local domain of dimension at least two, this shows that a finite normal
`A`-algebra which is étale over the punctured spectrum of `A` need not be étale, nor even flat.
Hence purity statements for finite normal algebras, such as Stacks, Lemma 58.20.3 (0BM9) and
Lemma 58.21.3 (0BMA), part (2), are false as written there: the algebra must also be torsion free
over `A`, which removes exactly the factors supported at the closed point. Normality is taken in
the sense of Stacks, Definition 10.37.11 (00GV): every localization at a prime is an integrally
closed domain.

## Main results

* `TauCeti.IsLocalRing.isEtaleAt_prod_residueField`: `A × κ(A)` is étale over `A` at every prime
  not lying over the maximal ideal of `A`.
* `TauCeti.IsLocalRing.isDomain_localization_prod_residueField` and
  `TauCeti.IsLocalRing.isIntegrallyClosed_localization_prod_residueField`: if `A` is a domain,
  respectively an integrally closed domain, then so is every localization of `A × κ(A)` at a
  prime.
* `TauCeti.IsLocalRing.not_isTorsionFree_prod_residueField`,
  `TauCeti.IsLocalRing.not_flat_prod_residueField` and
  `TauCeti.IsLocalRing.not_etale_prod_residueField`: if `A` is a domain but not a field, then
  `A × κ(A)` is not torsion free, not flat and not étale over `A`.

The `A`-module `A × κ(A)` is finite, since `κ(A)` is a finite `A`-module.

## References

* [Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9) and
  [Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA): the statements this example
  shows need a torsion-freeness hypothesis.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

variable (A : Type*) [CommRing A] [IsLocalRing A]

/-- A prime of `A × κ(A)` not lying over the maximal ideal of `A` does not contain `(1, 0)`:
if it did, it would contain the image `(a, 0)` of every `a ∈ 𝔪`. -/
private theorem fst_one_notMem (q : Ideal (A × ResidueField A)) [q.IsPrime]
    (hq : q.under A ≠ maximalIdeal A) : ((1, 0) : A × ResidueField A) ∉ q := by
  intro h
  refine hq ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
  intro a ha
  rw [Ideal.under, Ideal.mem_comap]
  have : algebraMap A (A × ResidueField A) a = (a, 0) * (1, 0) := by
    ext
    · simp
    · simp [(residue_eq_zero_iff a).mpr ha]
  rw [this]
  exact q.mul_mem_left _ h

/-- **`A × κ(A)` is étale over the punctured spectrum.** The algebra `A × κ(A)` is étale over `A`
at every prime not lying over the maximal ideal of `A`. -/
theorem isEtaleAt_prod_residueField (q : Ideal (A × ResidueField A)) [q.IsPrime]
    (hq : q.under A ≠ maximalIdeal A) : Algebra.IsEtaleAt A q := by
  -- Localizing at the idempotent `(1, 0)` recovers `A`, which is étale over itself.
  have hloc : Algebra.FormallyEtale A (Localization.Away ((1, 0) : A × ResidueField A)) := by
    let := (RingHom.fst A (ResidueField A)).toAlgebra
    have : IsScalarTower A (A × ResidueField A) A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact Algebra.FormallyEtale.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers ((1, 0) : A × ResidueField A)) A
        (Localization.Away ((1, 0) : A × ResidueField A))).restrictScalars A)
  exact Algebra.mem_etaleLocus_iff.mp (Algebra.basicOpen_subset_etaleLocus_iff.mpr hloc
    ((PrimeSpectrum.mem_basicOpen _ ⟨q, inferInstance⟩).mpr (fst_one_notMem A q hq)))

/-- Every localization of `A × κ(A)` at a prime is isomorphic to a localization of `A` or of
`κ(A)` at a prime, according to whether the prime omits `(1, 0)` or `(0, 1)`. -/
private theorem exists_ringEquiv_localization (q : Ideal (A × ResidueField A)) [q.IsPrime] :
    (∃ (P : Ideal A) (_ : P.IsPrime),
      Nonempty (Localization.AtPrime q ≃+* Localization.AtPrime P)) ∨
    ∃ (P : Ideal (ResidueField A)) (_ : P.IsPrime),
      Nonempty (Localization.AtPrime q ≃+* Localization.AtPrime P) := by
  by_cases h : ((1, 0) : A × ResidueField A) ∈ q
  · let := (RingHom.snd A (ResidueField A)).toAlgebra
    obtain ⟨P, _, -, f⟩ := IsLocalization.exists_ringEquiv_localization_atPrime
      (Submonoid.powers ((0, 1) : A × ResidueField A)) (ResidueField A) q
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr fun h' ↦ Ideal.IsPrime.ne_top
        inferInstance (q.eq_top_of_isUnit_mem (q.add_mem h h') (by simp [← Prod.one_eq_mk])))
    exact .inr ⟨P, inferInstance, f⟩
  · let := (RingHom.fst A (ResidueField A)).toAlgebra
    obtain ⟨P, _, -, f⟩ := IsLocalization.exists_ringEquiv_localization_atPrime
      (Submonoid.powers ((1, 0) : A × ResidueField A)) A q
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr h)
    exact .inl ⟨P, inferInstance, f⟩

variable [IsDomain A]

/-- If `A` is a local domain, every localization of `A × κ(A)` at a prime is a domain. -/
theorem isDomain_localization_prod_residueField (q : Ideal (A × ResidueField A)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) := by
  obtain ⟨P, _, ⟨f⟩⟩ | ⟨P, _, ⟨f⟩⟩ := exists_ringEquiv_localization A q <;>
    exact f.toMulEquiv.isDomain

/-- **`A × κ(A)` is normal when `A` is.** If `A` is an integrally closed local domain, every
localization of `A × κ(A)` at a prime is integrally closed. -/
theorem isIntegrallyClosed_localization_prod_residueField [IsIntegrallyClosed A]
    (q : Ideal (A × ResidueField A)) [q.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨P, _, ⟨f⟩⟩ | ⟨P, _, ⟨f⟩⟩ := exists_ringEquiv_localization A q <;>
    exact (isIntegrallyClosed_of_isLocalization _ P.primeCompl
      P.primeCompl_le_nonZeroDivisors).of_equiv f.symm

/-- If `A` is a local domain which is not a field, then `A × κ(A)` is not a torsion-free
`A`-module: a nonzero `x ∈ 𝔪` kills `(0, 1)`. -/
theorem not_isTorsionFree_prod_residueField (h : ¬ IsField A) :
    ¬ Module.IsTorsionFree A (A × ResidueField A) := by
  intro _
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt isField_iff_maximalIdeal_eq.mpr h)
  have hreg : IsSMulRegular (A × ResidueField A) x :=
    Module.IsTorsionFree.isSMulRegular (isRegular_iff_ne_zero.mpr hx0)
  have := @hreg (0, 1) 0 (by
    ext
    · simp
    · simp [Algebra.smul_def, (residue_eq_zero_iff x).mpr hx])
  simpa using congrArg Prod.snd this

/-- If `A` is a local domain which is not a field, then `A × κ(A)` is not flat over `A`. -/
theorem not_flat_prod_residueField (h : ¬ IsField A) : ¬ Module.Flat A (A × ResidueField A) :=
  fun _ ↦ not_isTorsionFree_prod_residueField A h inferInstance

/-- If `A` is a local domain which is not a field, then `A × κ(A)` is not étale over `A`,
although it is étale at every prime not lying over the maximal ideal
(`TauCeti.IsLocalRing.isEtaleAt_prod_residueField`). -/
theorem not_etale_prod_residueField (h : ¬ IsField A) : ¬ Algebra.Etale A (A × ResidueField A) :=
  fun _ ↦ not_flat_prod_residueField A h inferInstance

end TauCeti.IsLocalRing
