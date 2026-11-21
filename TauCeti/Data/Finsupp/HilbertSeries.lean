/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.PWO
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.PowerSeries.InvOneSubPow

/-!
# Hilbert series of upper and lower sets of exponents

Let `ι` be a finite type with `d` elements. For a set `U` of exponents `c : ι →₀ ℕ`, count the
exponents of `U` of each total degree `n`, and collect these counts into the power series
`∑ₙ #{c ∈ U | deg c = n} Tⁿ`. When `U` is an upper set for the componentwise order, this is the
Hilbert series of the monomial ideal spanned by the monomials `X^c`, `c ∈ U`. When `U` is a lower
set it is the Hilbert series of the quotient by the complementary monomial ideal, as for the
standard monomials of an ideal with respect to a monomial order. In both cases the series is
rational, of the form `p / (1 - T)ᵈ` for a polynomial `p`.

The proof is combinatorial. There are `d.multichoose n` exponents of degree `n`
(`Finsupp.ncard_setOf_degree_eq`), whose series is `(1 - T)⁻ᵈ`
(`PowerSeries.mk_multichoose_eq_invOneSubPow`), and the exponents above a fixed
`m` contribute `T^(deg m) (1 - T)⁻ᵈ`. By Dickson's lemma an upper set is the union of the sets of
exponents above each of its finitely many minimal elements, and inclusion–exclusion, through
`Ici m ∩ Ici m' = Ici (m ⊔ m')`, assembles its series.

The coefficients of the series may lie in any commutative ring, so taking them in `ℤ` or `ℚ`
retains the counts. With coefficients in a field of characteristic zero, Mathlib's
`Polynomial.hilbertPoly p d` then agrees with the counts in all degrees above the degree of `p`
(`Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`).

## Main results

* `Finsupp.mk_ncard_setOf_degree_eq_invOneSubPow`: the series counting all exponents by degree is
  `(1 - T)⁻ᵈ`.
* `Finsupp.mk_ncard_Ici_inter_setOf_degree_eq_X_pow_mul_invOneSubPow`: the series of the
  exponents above `m` is `T^(deg m) (1 - T)⁻ᵈ`.
* `IsUpperSet.exists_mk_ncard_inter_setOf_degree_eq_mul_invOneSubPow`: the series of an upper set
  of exponents is `p / (1 - T)ᵈ` for a polynomial `p`.
* `IsLowerSet.exists_mk_ncard_inter_setOf_degree_eq_mul_invOneSubPow`: the same for a lower set.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, 4th ed., Springer, 2015,
  Chapter 9, §2.
-/

public section

open PowerSeries Set
open scoped Polynomial

namespace Finsupp

variable {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]

/-- The series counting the exponents `c : ι →₀ ℕ` by total degree is `(1 - T)⁻ᵈ`, where
`d = card ι`. -/
theorem mk_ncard_setOf_degree_eq_invOneSubPow :
    PowerSeries.mk (fun n ↦ ({c : ι →₀ ℕ | c.degree = n}.ncard : R)) =
      invOneSubPow R (Fintype.card ι) := by
  simp_rw [ncard_setOf_degree_eq]
  exact mk_multichoose_eq_invOneSubPow R _

/-- The series counting the exponents `c ≥ m` by total degree is `T^(deg m) (1 - T)⁻ᵈ`, where
`d = card ι`. -/
theorem mk_ncard_Ici_inter_setOf_degree_eq_X_pow_mul_invOneSubPow (m : ι →₀ ℕ) :
    PowerSeries.mk (fun n ↦ ((Ici m ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R)) =
      (X : R⟦X⟧) ^ m.degree * invOneSubPow R (Fintype.card ι) := by
  rw [← mk_ncard_setOf_degree_eq_invOneSubPow]
  ext n
  rw [coeff_mk, coeff_X_pow_mul', coeff_mk]
  split_ifs with h
  · rw [← ncard_image_of_injective {c : ι →₀ ℕ | c.degree = n - m.degree}
      (add_left_injective m)]
    congr 2
    ext c
    refine ⟨fun ⟨(hmc : m ≤ c), hc⟩ ↦ ⟨c - m, ?_, tsub_add_cancel_of_le hmc⟩, ?_⟩
    · have := congrArg degree (tsub_add_cancel_of_le hmc)
      simp only [mem_ofPred_eq, map_add] at hc this ⊢
      omega
    · rintro ⟨c, hc, rfl⟩
      simp only [mem_ofPred_eq] at hc
      exact ⟨le_add_self (a := m), by simp [hc, Nat.sub_add_cancel h]⟩
  · have : Ici m ∩ {c : ι →₀ ℕ | c.degree = n} = ∅ :=
      eq_empty_of_forall_notMem fun c ⟨hmc, hc⟩ ↦ h (hc ▸ degree_mono hmc)
    simp [this]

omit [Fintype ι] in
/-- Inclusion–exclusion for the exponents of degree `n` in a union of two sets. -/
private theorem ncard_union_inter_setOf_degree_eq [Finite ι] (A B : Set (ι →₀ ℕ)) (n : ℕ) :
    (((A ∪ B) ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R) =
      (A ∩ {c : ι →₀ ℕ | c.degree = n}).ncard + (B ∩ {c : ι →₀ ℕ | c.degree = n}).ncard -
        (A ∩ B ∩ {c : ι →₀ ℕ | c.degree = n}).ncard := by
  have h := ncard_union_add_ncard_inter (A ∩ {c : ι →₀ ℕ | c.degree = n})
    (B ∩ {c : ι →₀ ℕ | c.degree = n}) ((finite_of_degree_eq n).subset inter_subset_right)
    ((finite_of_degree_eq n).subset inter_subset_right)
  rw [← union_inter_distrib_right, ← inter_inter_distrib_right] at h
  rw [eq_sub_iff_add_eq]
  simpa using congrArg (Nat.cast : ℕ → R) h

/-- The exponents lying above some element of a finite set `F` have series `p / (1 - T)ᵈ` for a
polynomial `p`, where `d = card ι`. -/
private theorem exists_mk_ncard_setOf_exists_le_inter_setOf_degree_eq (F : Finset (ι →₀ ℕ)) :
    ∃ p : R[X], PowerSeries.mk (fun n ↦
      (({c | ∃ f ∈ F, f ≤ c} ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R)) =
        p * invOneSubPow R (Fintype.card ι) := by
  classical
  induction hk : F.card using Nat.strong_induction_on generalizing F with
  | _ k ih =>
  obtain rfl | ⟨m, hm⟩ := F.eq_empty_or_nonempty
  · exact ⟨0, by ext n; simp⟩
  -- The exponents above `F` are those above `m` and those above `F.erase m`, and the exponents
  -- above both are those above `(F.erase m).image (m ⊔ ·)`, a set with fewer elements than `F`.
  have hlt : (F.erase m).card < k := hk ▸ Finset.card_erase_lt_of_mem hm
  obtain ⟨p, hp⟩ := ih _ hlt (F.erase m) rfl
  obtain ⟨q, hq⟩ := ih _ (Finset.card_image_le.trans_lt hlt) ((F.erase m).image (m ⊔ ·)) rfl
  have hF : {c | ∃ f ∈ F, f ≤ c} = Ici m ∪ {c | ∃ f ∈ F.erase m, f ≤ c} := by
    ext c
    simp only [mem_ofPred_eq, mem_union, mem_Ici, Finset.mem_erase]
    exact ⟨fun ⟨f, hf, hfc⟩ ↦
        (eq_or_ne f m).imp (fun h : f = m ↦ h ▸ hfc) fun h ↦ ⟨f, ⟨h, hf⟩, hfc⟩,
      fun h ↦ h.elim (fun h ↦ ⟨m, hm, h⟩) fun ⟨f, ⟨_, hf⟩, hfc⟩ ↦ ⟨f, hf, hfc⟩⟩
  have hinter : Ici m ∩ {c | ∃ f ∈ F.erase m, f ≤ c} =
      {c | ∃ g ∈ (F.erase m).image (m ⊔ ·), g ≤ c} := by
    ext c
    simp only [mem_inter_iff, mem_Ici, mem_ofPred_eq, Finset.exists_mem_image, sup_le_iff]
    exact ⟨fun ⟨hmc, f, hf, hfc⟩ ↦ ⟨f, hf, hmc, hfc⟩, fun ⟨f, hf, hmc, hfc⟩ ↦ ⟨hmc, f, hf, hfc⟩⟩
  refine ⟨Polynomial.X ^ m.degree + p - q, ?_⟩
  calc _ = PowerSeries.mk (fun n ↦ ((Ici m ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R)) +
        PowerSeries.mk (fun n ↦
          (({c | ∃ f ∈ F.erase m, f ≤ c} ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R)) -
        PowerSeries.mk (fun n ↦ (({c | ∃ g ∈ (F.erase m).image (m ⊔ ·), g ≤ c} ∩
          {c : ι →₀ ℕ | c.degree = n}).ncard : R)) := by
        ext n
        simp only [coeff_mk, map_add, map_sub]
        rw [hF, ncard_union_inter_setOf_degree_eq, hinter]
    _ = _ := by
        rw [mk_ncard_Ici_inter_setOf_degree_eq_X_pow_mul_invOneSubPow, hp, hq]
        push_cast
        ring

end Finsupp

open Finsupp

variable {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]

/-- **Rationality of the Hilbert series of a monomial ideal.** For an upper set `U` of exponents
`c : ι →₀ ℕ`, the series counting the elements of `U` by total degree is `p / (1 - T)ᵈ` for a
polynomial `p`, where `d = card ι`. -/
theorem IsUpperSet.exists_mk_ncard_inter_setOf_degree_eq_mul_invOneSubPow {U : Set (ι →₀ ℕ)}
    (hU : IsUpperSet U) :
    ∃ p : R[X], PowerSeries.mk (fun n ↦ ((U ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R)) =
      p * invOneSubPow R (Fintype.card ι) := by
  -- By Dickson's lemma `U` has finitely many minimal elements, and lies above them.
  have hfin : {f | Minimal (· ∈ U) f}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  have hU' : {c | ∃ f ∈ hfin.toFinset, f ≤ c} = U := by
    ext c
    simp only [mem_ofPred_eq, Finite.mem_toFinset]
    refine ⟨fun ⟨f, hf, hfc⟩ ↦ hU hfc hf.prop, fun hc ↦ ?_⟩
    obtain ⟨f, hfc, hf⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ U) c hc
    exact ⟨f, hf, hfc⟩
  rw [← hU']
  exact exists_mk_ncard_setOf_exists_le_inter_setOf_degree_eq R hfin.toFinset

/-- **Rationality of the Hilbert series of a monomial quotient.** For a lower set `L` of exponents
`c : ι →₀ ℕ`, such as the standard monomials of an ideal for a monomial order, the series
counting the elements of `L` by total degree is `p / (1 - T)ᵈ` for a polynomial `p`, where
`d = card ι`. -/
theorem IsLowerSet.exists_mk_ncard_inter_setOf_degree_eq_mul_invOneSubPow {L : Set (ι →₀ ℕ)}
    (hL : IsLowerSet L) :
    ∃ p : R[X], PowerSeries.mk (fun n ↦ ((L ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R)) =
      p * invOneSubPow R (Fintype.card ι) := by
  obtain ⟨p, hp⟩ := hL.compl.exists_mk_ncard_inter_setOf_degree_eq_mul_invOneSubPow R
  refine ⟨1 - p, ?_⟩
  -- The exponents of degree `n` split into those in `L` and those in its complement.
  have h (n : ℕ) : ((L ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R) =
      {c : ι →₀ ℕ | c.degree = n}.ncard - (Lᶜ ∩ {c : ι →₀ ℕ | c.degree = n}).ncard := by
    rw [eq_sub_iff_add_eq, inter_comm, inter_comm Lᶜ, ← sdiff_eq]
    simpa using congrArg (Nat.cast : ℕ → R)
      (ncard_inter_add_ncard_sdiff_eq_ncard _ L (finite_of_degree_eq n))
  calc _ = PowerSeries.mk (fun n ↦ ({c : ι →₀ ℕ | c.degree = n}.ncard : R)) -
        PowerSeries.mk (fun n ↦ ((Lᶜ ∩ {c : ι →₀ ℕ | c.degree = n}).ncard : R)) := by
        ext n
        simp [h]
    _ = _ := by
        rw [mk_ncard_setOf_degree_eq_invOneSubPow, hp]
        push_cast
        ring
