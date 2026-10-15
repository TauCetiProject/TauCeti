/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Permutation
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariants
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Valuation

/-!
# Relative discriminant coefficients from double cosets

Let `L/K` be a Galois extension of number fields, `H ≤ Gal(L/K)`, and `E = Lᴴ`.
Fix a prime `Q` of `L` over a prime `p` of `K`. The double cosets `H \ Gal(L/K) / D(Q)`
index the primes of `E` over `p`. This file computes the coefficient of `p` in the relative
discriminant of `E/K` entirely from the decomposition, inertia, and lower ramification groups
at `Q` and their conjugates.

For a representative `σ`, put `Dσ = σD(Q)σ⁻¹`, `Iσ = σI(Q)σ⁻¹`, and
`Gσ,i = σG_i(Q)σ⁻¹`. Its contribution is

`([Dσ : Dσ ∩ H] / [Iσ : Iσ ∩ H]) * (Σ_i (|G_i(Q)| - |Gσ,i ∩ H|) / |Iσ ∩ H|)`.

The first quotient is the residue degree of `σQ ∩ E`; the second is its different exponent.
Both divisions are exact and their denominators are positive. The infinite sum has only finitely
many nonzero terms, since the lower ramification groups are eventually trivial. No unramified
or tame hypothesis is imposed. Representatives may be chosen arbitrarily, and the formula also
shows that each contribution depends only on its double coset.

The local input is
`IsDedekindDomain.HeightOneSpectrum.ramificationIdx_mul_multiplicity_differentIdeal_fixedField`.
The global step combines `TauCeti.multiplicity_relDiscr` with
`Ideal.doubleCosetQuotientEquivPrimesOver` to sum these local contributions.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1–2.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 and Chapter III, §2.
-/

public section

open IsDedekindDomain IntermediateField NumberField
open scoped NumberField Pointwise

namespace TauCeti.NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

local notation "G" => L ≃ₐ[K] L

/-- The residue-degree-weighted different exponent below `Q` in `Lᴴ`, expressed using only
subgroup indices and ramification groups. The two natural-number divisions are exact: their
numerators are respectively `e * f` and `e(Q / Q∩Lᴴ) * v(𝔇)`. -/
theorem inertiaDeg_mul_multiplicity_differentIdeal_under_fixedField_eq
    (w : HeightOneSpectrum (𝓞 L)) (H : Subgroup G) :
    (w.asIdeal.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) *
        multiplicity (w.asIdeal.under (𝓞 ↥(fixedField H)))
          (differentIdeal (𝓞 K) (𝓞 ↥(fixedField H))) =
      (H.relIndex (MulAction.stabilizer G w.asIdeal) / H.relIndex (w.asIdeal.inertia G)) *
        ((∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup G i) -
          Nat.card (w.asIdeal.ramificationGroup G i ⊓ H : Subgroup G))) /
            Nat.card (w.asIdeal.inertia G ⊓ H : Subgroup G)) := by
  let E := fixedField H
  let : IsScalarTower K ↥E L := E.isScalarTower_mid'
  let : IsGalois ↥E L := IsGalois.of_fixed_field L H
  have hcard : Nat.card (w.asIdeal.inertia G ⊓ H : Subgroup G) =
      w.asIdeal.ramificationIdx (𝓞 ↥E) := by
    rw [← Ideal.card_inertia_fixedField_eq_card_inf,
      Ideal.card_inertia_eq_ramificationIdx (𝓞 ↥E) (L ≃ₐ[↥E] L)]
  rw [← Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex,
    ← Ideal.ramificationIdx_under_fixedField_eq_relIndex,
    Nat.mul_div_cancel_left _ (Ideal.ramificationIdx_pos (𝓞 K) _), hcard,
    ← w.ramificationIdx_mul_multiplicity_differentIdeal_fixedField H,
    Nat.mul_div_cancel_left _ (Ideal.ramificationIdx_pos (𝓞 ↥E) _)]
  rfl

/-- The discriminant contribution of a double coset representative is the residue-degree-weighted
different exponent of its associated prime. In particular it is unchanged when the representative
is replaced by another element of the same double coset. -/
theorem inertiaDeg_mul_multiplicity_differentIdeal_under_fixedField_smul_eq
    (w : HeightOneSpectrum (𝓞 L)) (H : Subgroup G) (σ : G) :
    ((σ • w.asIdeal).under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) *
        multiplicity ((σ • w.asIdeal).under (𝓞 ↥(fixedField H)))
          (differentIdeal (𝓞 K) (𝓞 ↥(fixedField H))) =
      (H.relIndex (MulAut.conj σ • MulAction.stabilizer G w.asIdeal) /
        H.relIndex (MulAut.conj σ • w.asIdeal.inertia G)) *
        ((∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup G i) -
          Nat.card (MulAut.conj σ • w.asIdeal.ramificationGroup G i ⊓ H : Subgroup G))) /
            Nat.card (MulAut.conj σ • w.asIdeal.inertia G ⊓ H : Subgroup G)) := by
  let wσ : HeightOneSpectrum (𝓞 L) :=
    ⟨σ • w.asIdeal, inferInstance, by
      intro h
      exact w.ne_bot ((smul_left_cancel_iff σ).mp (h.trans (Ideal.smul_bot σ).symm))⟩
  have h := inertiaDeg_mul_multiplicity_differentIdeal_under_fixedField_eq K L wσ H
  have hc (J : Subgroup G) : Nat.card (MulAut.conj σ • J : Subgroup G) = Nat.card J := by
    simpa only [MulEquiv.coe_mapSubgroup, MulEquiv.toMonoidHom_eq_coe,
      map_conj_eq_conj_smul] using
      Subgroup.card_mapSubgroup J (MulAut.conj σ)
  simpa only [wσ, MulAction.stabilizer_smul_eq_stabilizer_map_conj, Ideal.inertia_smul,
    Ideal.ramificationGroup_smul, MulEquiv.toMonoidHom_eq_coe, map_conj_eq_conj_smul, hc] using h

/-- **The relative discriminant coefficient of a fixed field from double cosets.** Sum the
group-theoretic contributions over `H \ Gal(L/K) / D(Q)`, using any choice of representatives.
The formula holds at ramified primes as well as unramified ones, including wild ramification. -/
theorem multiplicity_relDiscr_fixedField_eq_sum
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (H : Subgroup G)
    (r : DoubleCoset.Quotient (H : Set G) (MulAction.stabilizer G w.asIdeal : Set G) → G)
    (hr : ∀ q, DoubleCoset.mk H (MulAction.stabilizer G w.asIdeal) (r q) = q) :
    multiplicity v.asIdeal (relDiscr (𝓞 K) (𝓞 ↥(fixedField H))) =
      ∑ᶠ q, (H.relIndex (MulAut.conj (r q) • MulAction.stabilizer G w.asIdeal) /
        H.relIndex (MulAut.conj (r q) • w.asIdeal.inertia G)) *
        ((∑ᶠ i : ℕ, (Nat.card (w.asIdeal.ramificationGroup G i) -
          Nat.card (MulAut.conj (r q) • w.asIdeal.ramificationGroup G i ⊓ H : Subgroup G))) /
            Nat.card (MulAut.conj (r q) • w.asIdeal.inertia G ⊓ H : Subgroup G)) := by
  classical
  let _ := Fintype.ofFinite
    (DoubleCoset.Quotient (H : Set G) (MulAction.stabilizer G w.asIdeal : Set G))
  rw [multiplicity_relDiscr _ _ v.ne_bot (differentIdeal_ne_bot (A := 𝓞 K)),
    finsum_eq_sum_of_fintype]
  let e := Ideal.doubleCosetQuotientEquivPrimesOver v.asIdeal w.asIdeal H
  have hsum := e.sum_comp (fun P ↦ P.1.inertiaDeg (𝓞 K) *
    multiplicity P.1 (differentIdeal (𝓞 K) (𝓞 ↥(fixedField H))))
  rw [Finset.sum_subtype _ (fun _ ↦ Set.mem_toFinset) _]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro q _
  have he : (e q : Ideal (𝓞 ↥(fixedField H))) =
      (r q • w.asIdeal).under (𝓞 ↥(fixedField H)) := by
    simpa only [hr q] using
      Ideal.doubleCosetQuotientEquivPrimesOver_mk v.asIdeal w.asIdeal H (r q)
  rw [he]
  exact inertiaDeg_mul_multiplicity_differentIdeal_under_fixedField_smul_eq K L w H (r q)

end TauCeti.NumberField
