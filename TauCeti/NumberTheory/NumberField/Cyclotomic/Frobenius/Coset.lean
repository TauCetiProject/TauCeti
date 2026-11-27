/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.DirichletCharacter.FrobeniusCoset
import Mathlib.RingTheory.Invariant.Basic
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction

/-!
# Cyclotomic Frobenius cosets contain the decomposition group

To read a decomposition group in a cyclotomic subfield, lift its elements to the decomposition
group at the full level and reduce to the prime-to-`p` level. There the extension is unramified,
so all coordinates are powers of `p`. This gives a necessary condition on decomposition-group
 membership that also works at ramified primes.
-/

public section

open MulAction NumberField IsCyclotomicExtension.Rat
open scoped NumberField Pointwise

namespace Ideal

/-- Every element of the decomposition group in a normal cyclotomic subfield belongs to a
Frobenius coset of its Artin map, allowing exponent zero. -/
theorem exists_mem_frobeniusCoset_of_mem_stabilizer {N p : ℕ} [NeZero N]
    {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (hp : p.Prime) (E : IntermediateField ℚ L) [Normal ℚ E]
    {τ : E ≃ₐ[ℚ] E} (hτ : τ ∈ stabilizer (E ≃ₐ[ℚ] E) (Q.under (𝓞 E))) :
    ∃ i : ℕ, τ ∈ ((AlgEquiv.restrictNormalHom E).comp
      (galEquivZMod N L).symm.toMonoidHom).frobeniusCoset hp i := by
  let r := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := L) E
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois {N} ℚ L
  have : IsGaloisGroup E.fixingSubgroup E L := IsGaloisGroup.intermediateField (L ≃ₐ[ℚ] L) ℚ L E
  have : IsGaloisGroup E.fixingSubgroup (𝓞 E) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing E.fixingSubgroup (𝓞 E) (𝓞 L) E L
  have : Q.LiesOver (Q.under (𝓞 E)) := ⟨rfl⟩
  rw [← Ideal.map_stabilizer_of_surjective r E.fixingSubgroup (Q.under (𝓞 E)) Q
    (AlgEquiv.restrictNormalHom_surjective L) E.restrictNormalHom_ker.ge
    algebraMap_restrictNormal_smul] at hτ
  obtain ⟨σ, hσ, rfl⟩ := hτ
  let M := ordCompl[p] N
  have hMN : M ∣ N := Nat.ordCompl_dvd N p
  have : NeZero M := ⟨fun h ↦ NeZero.ne N (by simpa [h] using hMN)⟩
  let ζ := IsCyclotomicExtension.zeta N ℚ L ^ (N / M)
  have hζ : IsPrimitiveRoot ζ M := by
    have hdiv : N / M ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hMN)
      (NeZero.pos M))
    simpa only [ζ, Nat.div_div_self hMN (NeZero.ne N)] using
      (IsCyclotomicExtension.zeta_spec N ℚ L).pow_of_dvd hdiv (Nat.div_dvd_of_dvd hMN)
  let F := IntermediateField.adjoin ℚ ({ζ} : Set L)
  have : IsCyclotomicExtension {M} ℚ F := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {M} ℚ F
  have hstab := restrictNormal_mem_stabilizer_under (M := F) hσ
  have : Fact p.Prime := ⟨hp⟩
  have : (Q.under (𝓞 F)).LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨by rw [Ideal.under_under, Ideal.over_def Q (Ideal.span {(p : ℤ)})]⟩
  have : (Q.under (𝓞 F)).IsMaximal := isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ) _ <| by
    rw [← Ideal.over_def (Q.under (𝓞 F)) (Ideal.span {(p : ℤ)})]
    infer_instance
  have hpow := mem_zpowers_galEquivZMod_of_mem_stabilizer M F p (Q.under (𝓞 F))
    (Nat.coprime_ordCompl hp (NeZero.ne N)) hstab
  rw [galEquivZMod_restrictNormal_apply N L F hMN σ, ← mem_powers_iff_mem_zpowers] at hpow
  obtain ⟨i, hi⟩ := hpow
  refine ⟨i, (MonoidHom.mem_frobeniusCoset_iff _ hp).mpr ⟨galEquivZMod N L σ, hi.symm, ?_⟩⟩
  simp [r]

end Ideal
