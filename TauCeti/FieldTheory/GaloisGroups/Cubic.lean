/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Label
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification
public import TauCeti.RingTheory.Polynomial.Monic.Irreducible
import TauCeti.RingTheory.Polynomial.Roots

/-!
# The Galois group of a cubic

An irreducible separable cubic has transitive Galois image in `Equiv.Perm (Fin 3)`, and the only
transitive subgroups of the symmetric group on three points are the alternating group `A₃`, the
reference subgroup of the label `3T1`, and the whole group `S₃`, that of `3T2`. So such a cubic
carries exactly one label, and which one is decided by parity: away from characteristic `2` the
Galois image lies in the alternating group exactly when the discriminant is a square. The
discriminant therefore determines the Galois group of an irreducible separable cubic on its
own: the label is `3T1` when `f.discr` is a square and `3T2` when it is not.

The two classical examples over `ℚ` are computed in full. The cubic `X³ - 3X - 1` has discriminant
`81 = 9²`, so its Galois group is cyclic of order three; the cubic `X³ - 2` has discriminant
`-108`, which is not a square in `ℚ` since it is negative, so its Galois group is `S₃`, of order
six. Irreducibility over `ℚ` is checked by the integral root theorem and a reduction modulo a small
prime.

## Main results

* `TauCeti.existsUnique_hasGaloisLabel_three`: an irreducible separable cubic carries exactly one
  label.
* `TauCeti.hasGaloisLabel_three_zero_iff`, `TauCeti.hasGaloisLabel_three_one_iff`: **the
  discriminant decides the label of a cubic**, `3T1` for a square discriminant and `3T2`
  otherwise.
* `TauCeti.hasGaloisLabel_X_pow_three_sub_three_mul_X_sub_one`: `X³ - 3X - 1` over `ℚ` has label
  `3T1`, and `TauCeti.natCard_gal_X_pow_three_sub_three_mul_X_sub_one`: its Galois group has
  order `3`.
* `TauCeti.hasGaloisLabel_X_pow_three_sub_two`: `X³ - 2` over `ℚ` has label `3T2`, and
  `TauCeti.natCard_gal_X_pow_three_sub_two`: its Galois group has order `6`.

## References

* K. Conrad, *Galois groups of cubics and quartics (not in characteristic 2)*, Theorem 2.3 and
  Examples 2.4–2.5.
* LMFDB, number fields `3.3.81.1` and `3.1.108.1`.
-/

public section

open Polynomial Equiv Equiv.Perm MulAction

namespace TauCeti

section General

variable {F : Type*} [Field F] {f : F[X]}

/-- A polynomial carries at most one label in degree three. -/
theorem HasGaloisLabel.eq_of_three {j k : TransitiveGroupIndex 3} (hj : HasGaloisLabel f j)
    (hk : HasGaloisLabel f k) : j = k := by
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f hj.separable
  exact (hj.transitiveGroupLabel (e.trans (finCongr hj.natDegree_eq))).eq_of_three
    (hk.transitiveGroupLabel _)

/-- **An irreducible separable cubic carries exactly one label**, `3T1` or `3T2`. -/
theorem existsUnique_hasGaloisLabel_three (hsep : f.Separable) (hirr : Irreducible f)
    (hdeg : f.natDegree = 3) : ∃! j : TransitiveGroupIndex 3, HasGaloisLabel f j :=
  (exists_hasGaloisLabel_of_irreducible hsep hirr hdeg fun G _ =>
    exists_transitiveGroupLabel_three G).elim fun j hj => ⟨j, hj, fun _ hk => hk.eq_of_three hj⟩

private theorem discr_C_mul_of_natDegree_eq_three (a : F) (ha : a ≠ 0)
    (hdeg : f.natDegree = 3) : (C a * f).discr = a ^ 4 * f.discr := by
  have hfdeg : f.degree = 3 :=
    (degree_eq_iff_natDegree_eq_of_pos (show 0 < (3 : ℕ) by omega)).mpr hdeg
  have hscaled : (C a * f).degree = 3 := by rw [degree_C_mul ha, hfdeg]
  rw [discr_of_degree_eq_three hscaled, discr_of_degree_eq_three hfdeg]
  simp only [coeff_C_mul]
  ring

private theorem isSquare_discr_iff_mem_range_three {E : Type*} [Field E] [Algebra F E]
    (hsep : f.Separable) (hdeg : f.natDegree = 3)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    IsSquare f.discr ↔ discrSqrt e ∈ Set.range (algebraMap F E) := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  let p : E[X] := ∏ i, (X - C (e i : E))
  have hfmapdeg : (f.map (algebraMap F E)).natDegree = 3 := by
    rw [natDegree_map_eq_of_injective (algebraMap F E).injective, hdeg]
  have hsplits : (f.map (algebraMap F E)).Splits := by
    rw [splits_iff_card_roots, hsep.roots_map_eq_map_numbering e]
    simpa [hfmapdeg] using hdeg
  have hfac : f.map (algebraMap F E) = C (algebraMap F E f.leadingCoeff) * p := by
    have hprod := hsplits.eq_prod_roots
    rw [hsep.roots_map_eq_map_numbering e] at hprod
    simpa [p, ← List.prod_ofFn, Function.comp_def] using hprod
  have hpdeg : p.natDegree = 3 := by
    rw [← hfmapdeg, hfac, natDegree_C_mul
      ((map_eq_zero_iff _ (algebraMap F E).injective).not.mpr hlc)]
  have hdiscr : algebraMap F E f.discr =
      (algebraMap F E f.leadingCoeff) ^ 4 * discrSqrt e ^ 2 := by
    rw [← discr_map_of_natDegree_eq (algebraMap F E)
      (natDegree_map_eq_of_injective (algebraMap F E).injective f), hfac,
      discr_C_mul_of_natDegree_eq_three _
        ((map_eq_zero_iff _ (algebraMap F E).injective).not.mpr hlc) hpdeg,
      discr_prod_X_sub_C_eq_sq]
    rw [discrSqrt_def]
  constructor
  · rintro ⟨c, hc⟩
    have hs : discrSqrt e * discrSqrt e =
        algebraMap F E (f.leadingCoeff⁻¹ ^ 2 * c) *
          algebraMap F E (f.leadingCoeff⁻¹ ^ 2 * c) := by
      have h := hdiscr
      rw [hc, map_mul] at h
      simp only [map_inv₀, map_pow, map_mul]
      have hlcE : algebraMap F E f.leadingCoeff ≠ 0 :=
        (map_eq_zero_iff _ (algebraMap F E).injective).not.mpr hlc
      field_simp [hlcE] at h ⊢
      ring_nf at h ⊢
      exact h.symm
    rcases mul_self_eq_mul_self_iff.mp hs with hs | hs
    · exact ⟨_, hs.symm⟩
    · exact ⟨-_, by rw [map_neg, ← hs]⟩
  · rintro ⟨c, hc⟩
    refine ⟨f.leadingCoeff ^ 2 * c, (algebraMap F E).injective ?_⟩
    simp only [map_mul, map_pow]
    rw [hc, hdiscr]
    ring

private theorem HasGaloisLabel.isSquare_discr_iff_three {j : TransitiveGroupIndex 3}
    (h : HasGaloisLabel f j) (hchar : ringChar F ≠ 2) :
    IsSquare f.discr ↔ referenceSubgroup 3 j ≤ alternatingGroup (Fin 3) := by
  have : IsGalois F f.SplittingField := IsGalois.of_separable_splitting_field h.separable
  let _ : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  obtain ⟨e⟩ := nonempty_rootSet_splittingField_equiv_fin f h.separable
  exact (isSquare_discr_iff_mem_range_three h.separable h.natDegree_eq e.symm).trans <|
    (discrSqrt_mem_range_iff hchar e.symm).trans h.range_le_alternatingGroup_iff

variable (hchar : ringChar F ≠ 2)
include hchar

/-- **A cubic with square discriminant has label `3T1`.** Away from characteristic `2`, a
polynomial has label `3T1`, that is Galois group cyclic of order three acting on its roots,
exactly when it is a separable irreducible cubic whose discriminant is a square. -/
theorem hasGaloisLabel_three_zero_iff :
    HasGaloisLabel f (⟨0, by simp⟩ : TransitiveGroupIndex 3) ↔
      f.Separable ∧ Irreducible f ∧ f.natDegree = 3 ∧ IsSquare f.discr := by
  refine ⟨fun h => ⟨h.separable, h.irreducible, h.natDegree_eq,
    (h.isSquare_discr_iff_three hchar).mpr referenceSubgroup_three_zero_le_alternatingGroup⟩,
    fun ⟨hsep, hirr, hdeg, hsq⟩ => ?_⟩
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_three hsep hirr hdeg
  obtain ⟨_ | _ | _, hlt⟩ := j
  · exact hj
  · exact (not_referenceSubgroup_three_one_le_alternatingGroup
      ((hj.isSquare_discr_iff_three hchar).mp hsq)).elim
  · simp at hlt

/-- **A cubic with non-square discriminant has label `3T2`.** Away from characteristic `2`, a
polynomial has label `3T2`, that is Galois group the full symmetric group on its three
roots, exactly when it is a separable irreducible cubic whose discriminant is not a square. -/
theorem hasGaloisLabel_three_one_iff :
    HasGaloisLabel f (⟨1, by simp⟩ : TransitiveGroupIndex 3) ↔
      f.Separable ∧ Irreducible f ∧ f.natDegree = 3 ∧ ¬ IsSquare f.discr := by
  refine ⟨fun h => ⟨h.separable, h.irreducible, h.natDegree_eq,
    fun hsq => not_referenceSubgroup_three_one_le_alternatingGroup
      ((h.isSquare_discr_iff_three hchar).mp hsq)⟩, fun ⟨hsep, hirr, hdeg, hsq⟩ => ?_⟩
  obtain ⟨j, hj, -⟩ := existsUnique_hasGaloisLabel_three hsep hirr hdeg
  obtain ⟨_ | _ | _, hlt⟩ := j
  · exact (hsq ((hj.isSquare_discr_iff_three hchar).mpr
      referenceSubgroup_three_zero_le_alternatingGroup)).elim
  · exact hj
  · simp at hlt

end General

/-! ### Two cubics over `ℚ` -/

/-- The discriminant of `X³ - 3X - 1` is `81`. -/
theorem discr_X_pow_three_sub_three_mul_X_sub_one :
    (X ^ 3 - 3 * X - 1 : ℚ[X]).discr = 81 := by
  rw [discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_sub, coeff_X_pow, coeff_X, coeff_one, coeff_ofNat_mul]
  norm_num

/-- The discriminant of `X³ - 2` is `-108`. -/
theorem discr_X_pow_three_sub_two : (X ^ 3 - 2 : ℚ[X]).discr = -108 := by
  rw [discr_of_degree_eq_three (by compute_degree!)]
  simp only [coeff_sub, coeff_X_pow, coeff_ofNat_zero, coeff_ofNat_succ]
  norm_num

/-- `X³ - 3X - 1` is irreducible over `ℚ`: it has no root modulo `2`, so no integral root. -/
theorem irreducible_X_pow_three_sub_three_mul_X_sub_one :
    Irreducible (X ^ 3 - 3 * X - 1 : ℚ[X]) := by
  have := irreducible_map_rat_of_natDegree_eq_three (g := X ^ 3 - 3 * X - 1)
    (by monicity!) (by compute_degree!) fun m hm => by
      have h2 := congrArg (Int.cast : ℤ → ZMod 2) hm
      push_cast [eval_sub, eval_pow, eval_X, eval_mul, eval_one, eval_ofNat] at h2
      generalize (m : ZMod 2) = y at h2
      revert y
      decide
  simpa using this

/-- `X³ - 2` is irreducible over `ℚ`: it has no root modulo `7`, so no integral root. -/
theorem irreducible_X_pow_three_sub_two : Irreducible (X ^ 3 - 2 : ℚ[X]) := by
  have := irreducible_map_rat_of_natDegree_eq_three (g := X ^ 3 - 2)
    (by monicity!) (by compute_degree!) fun m hm => by
      have h7 := congrArg (Int.cast : ℤ → ZMod 7) hm
      push_cast [eval_sub, eval_pow, eval_X, eval_ofNat] at h7
      generalize (m : ZMod 7) = y at h7
      revert y
      decide
  simpa using this

/-- **`X³ - 3X - 1` has label `3T1`**: its Galois group over `ℚ` is cyclic of order three. -/
theorem hasGaloisLabel_X_pow_three_sub_three_mul_X_sub_one :
    HasGaloisLabel (X ^ 3 - 3 * X - 1 : ℚ[X]) (⟨0, by simp⟩ : TransitiveGroupIndex 3) :=
  (hasGaloisLabel_three_zero_iff (by simp)).mpr
    ⟨irreducible_X_pow_three_sub_three_mul_X_sub_one.separable,
      irreducible_X_pow_three_sub_three_mul_X_sub_one, by compute_degree!,
      discr_X_pow_three_sub_three_mul_X_sub_one ▸ ⟨9, by norm_num⟩⟩

/-- **`X³ - 2` has label `3T2`**: its Galois group over `ℚ` is the symmetric group on its three
roots. The discriminant `-108` is negative, hence not a square. -/
theorem hasGaloisLabel_X_pow_three_sub_two :
    HasGaloisLabel (X ^ 3 - 2 : ℚ[X]) (⟨1, by simp⟩ : TransitiveGroupIndex 3) :=
  (hasGaloisLabel_three_one_iff (by simp)).mpr
    ⟨irreducible_X_pow_three_sub_two.separable, irreducible_X_pow_three_sub_two,
      by compute_degree!, by
        rw [discr_X_pow_three_sub_two]
        rintro ⟨r, hr⟩
        nlinarith [mul_self_nonneg r]⟩

/-- The Galois group of `X³ - 3X - 1` over `ℚ` has order `3`. -/
theorem natCard_gal_X_pow_three_sub_three_mul_X_sub_one :
    Nat.card (X ^ 3 - 3 * X - 1 : ℚ[X]).Gal = 3 := by
  rw [hasGaloisLabel_X_pow_three_sub_three_mul_X_sub_one.natCard_gal,
    natCard_referenceSubgroup_three_zero]

/-- The Galois group of `X³ - 2` over `ℚ` has order `6`. -/
theorem natCard_gal_X_pow_three_sub_two : Nat.card (X ^ 3 - 2 : ℚ[X]).Gal = 6 := by
  rw [hasGaloisLabel_X_pow_three_sub_two.natCard_gal, natCard_referenceSubgroup_three_one]

end TauCeti
