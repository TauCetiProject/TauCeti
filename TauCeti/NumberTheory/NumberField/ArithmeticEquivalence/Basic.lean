/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.NumberField.FixedField
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ResidueDegrees
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.SplittingType
import TauCeti.RepresentationTheory.OfMulAction.QuotientToInvariants

/-!
# Arithmetic equivalence and Gassmann's theorem

Two number fields are *arithmetically equivalent* when they have the same Dedekind zeta function,
equivalently the same number of integral ideals of every absolute norm. By multiplicativity of the
norm-counting function and its Euler product, the ideal counts at powers of a rational prime `p`
depend only on the multiset of residue degrees of the primes above `p`
(`TauCeti.normCoeff_one_apply_prime_pow_eq_prod_ofPowerSeries`,
`TauCeti.dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq`).

For a Galois extension `L / K` of number fields and two almost-conjugate subgroups `H, H' ≤
Gal(L / K)`, the permutation representations `ℚ[Gal(L / K) ⧸ H]` and `ℚ[Gal(L / K) ⧸ H']`
agree on fixed-point counts and therefore descend to equivalent permutation representations of
`D(Q) / I(Q)` on the inertia-orbit spaces `I(Q) \ (Gal(L / K) ⧸ H)` and `I(Q) \ (Gal(L / K) ⧸ H')`
at every prime `Q` of `𝓞 L` (`TauCeti.fullCycleType_toPerm_orbitRelQuotient_eq`). Comparing full
cycle types of an arithmetic Frobenius modulo `I(Q)` via
`Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg` shows that `L ^ H` and `L ^ H'`
have the same multiset of residue degrees above every maximal ideal of `𝓞 K`, ramified primes
included (`TauCeti.map_inertiaDeg_fixedField_eq_of_almostConjugate`).

Over `ℚ` this yields **Gassmann's theorem**: fixed fields of almost-conjugate subgroups have the
same number of ideals of every norm and the same Dedekind zeta function
(`Subgroup.dedekindZetaCoeff_fixedField_eq_of_almostConjugate`,
`Subgroup.dedekindZeta_fixedField_eq_of_almostConjugate`).

## Main results

* `TauCeti.map_inertiaDeg_fixedField_eq_of_almostConjugate`: almost-conjugate subgroups of
  `Gal(L / K)` have fixed fields with the same multiset of residue degrees above every maximal
  ideal of `𝓞 K` (ramified or unramified).
* `Subgroup.dedekindZetaCoeff_fixedField_eq_of_almostConjugate`: **Gassmann's theorem** for ideal
  counts.
* `Subgroup.dedekindZeta_fixedField_eq_of_almostConjugate`: **Gassmann's theorem** for Dedekind
  zeta functions.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open Ideal MulAction NumberField
open scoped NumberField Pointwise

namespace TauCeti

open scoped Classical in
/-- **Almost-conjugate subgroups have the same residue degrees at every prime.** For a Galois
extension `L / K` of number fields and almost-conjugate subgroups `H, H' ≤ Gal(L / K)`, the fixed
fields `L ^ H` and `L ^ H'` have the same multiset of residue degrees above every maximal ideal
`p` of `𝓞 K`, including primes that ramify in `L`. -/
theorem map_inertiaDeg_fixedField_eq_of_almostConjugate
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] {H H' : Subgroup (L ≃ₐ[K] L)}
    (hHH' : H.AlmostConjugate H') (p : Ideal (𝓞 K)) [p.IsMaximal] :
    (Finset.univ : Finset (p.primesOver (𝓞 ↥(IntermediateField.fixedField H)))).val.map
        (fun P ↦ P.val.inertiaDeg (𝓞 K)) =
      (Finset.univ : Finset (p.primesOver (𝓞 ↥(IntermediateField.fixedField H')))).val.map
        (fun P ↦ P.val.inertiaDeg (𝓞 K)) := by
  -- Choose a prime `Q` of `𝓞 L` above `p` and an arithmetic Frobenius `σ` at `Q`.
  obtain ⟨Q, hQmax, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) p
    fun x hx ↦ by
      have hx0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
        ((RingHom.mem_ker.mp hx).trans (map_zero _).symm)
      exact hx0 ▸ p.zero_mem
  have : Q.IsMaximal := hQmax
  have : Q.IsPrime := hQmax.isPrime
  have : Q.LiesOver p := ⟨hQp.symm⟩
  have hQne : Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hQmax (NumberField.RingOfIntegers.not_isField L)
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K Q hQne
  -- Read both residue-degree multisets as Frobenius cycle types on inertia-orbit spaces.
  rw [← Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg p Q H hσ,
    ← Ideal.fullCycleType_toPerm_inertiaOrbitQuotient_eq_map_inertiaDeg p Q H' hσ]
  -- Almost-conjugacy gives equal fixed-coset counts on `D(Q)`, hence equal cycle types on
  -- `I`-orbits.
  have hfix : ∀ d : stabilizer (L ≃ₐ[K] L) Q,
      Nat.card (fixedBy ((L ≃ₐ[K] L) ⧸ H) d) = Nat.card (fixedBy ((L ≃ₐ[K] L) ⧸ H') d) :=
    fun d ↦ Subgroup.almostConjugate_iff_forall_natCard_fixedBy_eq.mp hHH' d.val
  exact fullCycleType_toPerm_orbitRelQuotient_eq hfix (Q.inertia (stabilizer (L ≃ₐ[K] L) Q))
    (QuotientGroup.mk ⟨σ, hσ.mem_stabilizer⟩)

end TauCeti

namespace Subgroup

/-- **Gassmann's theorem.** If two subgroups `H` and `K` of the Galois group of a Galois number
field `E / ℚ` are almost conjugate, then their fixed fields have the same number of integral ideals
of every absolute norm. -/
theorem dedekindZetaCoeff_fixedField_eq_of_almostConjugate
    {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E] (H K : Subgroup (E ≃ₐ[ℚ] E))
    (hHK : H.AlmostConjugate K) (n : ℕ) :
    TauCeti.dedekindZetaCoeff (IntermediateField.fixedField H) n =
      TauCeti.dedekindZetaCoeff (IntermediateField.fixedField K) n :=
  TauCeti.dedekindZetaCoeff_eq_of_forall_map_inertiaDeg_eq _ _
    (fun v ↦ TauCeti.map_inertiaDeg_fixedField_eq_of_almostConjugate hHK v.asIdeal) n

/-- **Gassmann's theorem for Dedekind zeta functions.** Almost-conjugate subgroups of the Galois
group of a Galois number field `E / ℚ` have fixed fields with the same Dedekind zeta function. -/
theorem dedekindZeta_fixedField_eq_of_almostConjugate
    {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E] (H K : Subgroup (E ≃ₐ[ℚ] E))
    (hHK : H.AlmostConjugate K) (s : ℂ) :
    NumberField.dedekindZeta (IntermediateField.fixedField H) s =
      NumberField.dedekindZeta (IntermediateField.fixedField K) s := by
  rw [TauCeti.dedekindZeta_eq_LSeries_dedekindZetaCoeff,
    TauCeti.dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  congr 1
  ext n
  exact congrArg Nat.cast (H.dedekindZetaCoeff_fixedField_eq_of_almostConjugate K hHK n)

end Subgroup
