/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.RingTheory.RingHom.Surjective
import TauCeti.RingTheory.Ideal.Quotient.Semilocal
import TauCeti.RingTheory.Length

/-!
# The length of a quotient as a sum of local lengths

Let `A` be a local ring, `B` an integral `A`-algebra and `J` an ideal of `B` with Artinian quotient
`B ⧸ J`. The `A`-length of `B ⧸ J` is a sum of local contributions, one for each maximal ideal `m`
of `B` containing `J`:

`length_A (B ⧸ J) = Σ_m length_{B_m} (B_m ⧸ J B_m) · length_A κ(B_m)`.

The factor `length_A κ(B_m)` is the residue degree `[κ(m) : κ(A)]` read as a length, and the
first factor is the local multiplicity of `J` at `m`; over a Dedekind domain it is the exponent of
`m` in the factorization of `J`. When `A = R_p` and `B = S_p` are the localizations of a finite
extension `R → S` at a prime `p` of `R`, this is the formula
`length_{R_p} (S_p ⧸ J_p) = Σ_{q ∣ p} [κ(q) : κ(p)] length_{S_q} (S_q ⧸ J_q)`
through which ideal norms and determinants of lattices are compared with the factorization of `J`.

The proof decomposes the Artinian ring `C = B ⧸ J` as the product of its localizations `C_q`
(`MaximalSpectrum.toPiLocalizationEquiv`), computes the `A`-length of each local factor by
`IsLocalRing.length_restrictScalars`, and identifies `C_q` with `B_m ⧸ J B_m` for the maximal
ideal `m` of `B` under `q`.

## Main results

* `Ideal.length_quotient_eq_finsum`: `length_A (B ⧸ J)` is the sum over the maximal ideals `q` of
  `C = B ⧸ J` of `length_{C_q} C_q · length_A κ(C_q)`.
* `Ideal.length_localization_quotient`: `(B ⧸ J)_q` has the same length over itself as
  `B_m ⧸ J B_m` over `B_m`, where `m` is the prime of `B` under `q`.
* `Ideal.length_quotient_eq_finsum_length_localization`: `length_A (B ⧸ J)` is the sum over the
  maximal ideals `m` of `B` of `length_{B_m} (B_m ⧸ J B_m) · length_A κ(B_m)`.

## References

* W. Fulton, *Intersection Theory*, Appendix A.3.
-/

public section

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- For an ideal `J` of `B` and a prime `q` of `B ⧸ J`, with preimage `m` in `B`, the localization
`(B ⧸ J)_q` has the same length over itself as `B_m ⧸ J B_m` over `B_m`. -/
theorem length_localization_quotient (J : Ideal B) (q : Ideal (B ⧸ J)) [q.IsPrime] :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime (q.comap (Quotient.mk J)))
        (Localization.AtPrime (q.comap (Quotient.mk J)) ⧸
          J.map (algebraMap B (Localization.AtPrime (q.comap (Quotient.mk J))))) := by
  -- The localization `ψ : B_m → (B ⧸ J)_q` of `B → B ⧸ J` is surjective with kernel `J B_m`.
  let ψ := Localization.localRingHom _ q (Quotient.mk J) rfl
  have hψ : Function.Surjective ψ :=
    RingHom.surjective_localRingHom_of_surjective _ Quotient.mk_surjective q
  have hker : RingHom.ker ψ = J.map (algebraMap B _) := by
    have hmap : ψ = IsLocalization.map (M := (q.comap (Quotient.mk J)).primeCompl)
        (T := q.primeCompl) (Localization.AtPrime q) (Quotient.mk J)
        (Localization.le_comap_primeCompl_iff.mpr le_rfl) := by
      apply Localization.localRingHom_unique
      exact IsLocalization.map_eq _
    rw [hmap, IsLocalization.ker_map (Localization.AtPrime q) (Quotient.mk J)
      (map_primeCompl_comap_of_surjective _ Quotient.mk_surjective q), mk_ker]
  let _ : Algebra (Localization.AtPrime (q.comap (Quotient.mk J))) (Localization.AtPrime q) :=
    ψ.toAlgebra
  let e : (Localization.AtPrime (q.comap (Quotient.mk J)) ⧸ RingHom.ker ψ)
      ≃ₐ[Localization.AtPrime (q.comap (Quotient.mk J))] Localization.AtPrime q :=
    AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hψ) (by
      simp [RingHom.algebraMap_toAlgebra])
  rw [← Module.length_eq_of_surjective (S := Localization.AtPrime (q.comap (Quotient.mk J))) hψ,
    ← e.toLinearEquiv.length_eq, (quotientEquivAlgOfEq _ hker).toLinearEquiv.length_eq]

variable [IsLocalRing A] [Algebra.IsIntegral A B]

/-- **The length of `B ⧸ J` is a sum of local lengths** (Fulton, *Intersection Theory*,
Appendix A.3). For an integral algebra `B` over a local ring `A` and an ideal `J` of `B` with
Artinian quotient `C = B ⧸ J`, `length_A C = Σ_q length_{C_q} C_q · length_A κ(C_q)`, summed over
the maximal ideals `q` of `C`. -/
theorem length_quotient_eq_finsum (J : Ideal B) [IsArtinianRing (B ⧸ J)] :
    Module.length A (B ⧸ J) =
      ∑ᶠ q : MaximalSpectrum (B ⧸ J),
        Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) *
          Module.length A (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) := by
  set C := B ⧸ J
  have := Fintype.ofFinite (MaximalSpectrum C)
  rw [((MaximalSpectrum.toPiLocalizationEquiv C).toLinearEquiv.restrictScalars A).length_eq,
    Module.length_pi_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- The maximal ideal of `C_q` lies over the maximal ideal of `A`, since `C` is integral over `A`.
  have : IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) := by
    refine ((IsLocalRing.local_hom_tfae _).out 1 5).2 ?_
    have hq : (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).comap
        (algebraMap C (Localization.AtPrime q.asIdeal)) = q.asIdeal :=
      Localization.AtPrime.under_maximalIdeal
    rw [IsScalarTower.algebraMap_eq A C (Localization.AtPrime q.asIdeal), ← comap_comap, hq]
    exact IsLocalRing.eq_maximalIdeal (IsMaximal.under A q.asIdeal)
  rw [IsLocalRing.length_restrictScalars A (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime q.asIdeal), Module.length_eq_of_surjective
      (M := IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.residue_surjective (R := A))]

/-- **The length of `B ⧸ J` as a sum of local multiplicities** (Fulton, *Intersection Theory*,
Appendix A.3). For an integral algebra `B` over a local ring `A` and an ideal `J` of `B` with
Artinian quotient,
`length_A (B ⧸ J) = Σ_m length_{B_m} (B_m ⧸ J B_m) · length_A κ(B_m)`, the sum over the maximal
ideals `m` of `B` (only those containing `J` contribute), with the residue degree `[κ(B_m) : κ(A)]`
read as the `A`-length of `κ(B_m)`. -/
theorem length_quotient_eq_finsum_length_localization (J : Ideal B) [IsArtinianRing (B ⧸ J)] :
    Module.length A (B ⧸ J) =
      ∑ᶠ m : MaximalSpectrum B,
        Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal ⧸
            J.map (algebraMap B (Localization.AtPrime m.asIdeal))) *
          Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) := by
  set G : MaximalSpectrum B → ℕ∞ := fun m ↦
    Module.length (Localization.AtPrime m.asIdeal) (Localization.AtPrime m.asIdeal ⧸
        J.map (algebraMap B (Localization.AtPrime m.asIdeal))) *
      Module.length A (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal))
  -- The maximal ideals of `B ⧸ J` are those of `B` containing `J`.
  let c : MaximalSpectrum (B ⧸ J) → MaximalSpectrum B := fun q ↦
    ⟨q.asIdeal.comap (Quotient.mk J), comap_isMaximal_of_surjective _ Quotient.mk_surjective⟩
  have hc : Function.Injective c := fun q q' h ↦ MaximalSpectrum.ext
    (comap_injective_of_surjective _ Quotient.mk_surjective (congrArg MaximalSpectrum.asIdeal h))
  -- Away from the maximal ideals containing `J`, the ideal `J B_m` is the unit ideal.
  have hsupp : Function.support G ⊆ Set.range c := by
    intro m hm
    by_cases hJm : J ≤ m.asIdeal
    · obtain ⟨q, hq⟩ := TauCeti.exists_maximalSpectrum_comap_mk_eq hJm
      exact ⟨q, MaximalSpectrum.ext hq⟩
    · refine absurd ?_ hm
      have : Subsingleton (Localization.AtPrime m.asIdeal ⧸
          J.map (algebraMap B (Localization.AtPrime m.asIdeal))) :=
        Submodule.Quotient.subsingleton_iff.2 (IsLocalization.AtPrime.map_eq_top_of_not_le _ hJm)
      simp [G, Module.length_eq_zero]
  have hG : ∑ᶠ m, G m = ∑ᶠ q, G (c q) := by
    rw [← finsum_mem_range hc, finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  rw [length_quotient_eq_finsum J, hG]
  refine finsum_congr fun q ↦ ?_
  rw [length_localization_quotient, length_residueField_localization_quotient]

end Ideal
