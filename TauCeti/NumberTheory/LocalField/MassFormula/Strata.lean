/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Main
import TauCeti.NumberTheory.LocalField.MassFormula.Total
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Wild-exponent strata of totally ramified extensions

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, and let `σ_K(n)`
(`TauCeti.totallyRamifiedOfDegree K n`) be the family of totally ramified degree-`n` subextensions
of `SeparableClosure K`. Derived directly from Serre's mass formula
(`TauCeti.tsum_one_div_natCard_residueField_pow_wildExponent`), this module establishes the
box-independent finiteness and stratum-mass identities for the wild-exponent fibers
`{E ∈ σ_K(n) | E.wildExponent = j}` uniformly in mixed and equal characteristic.

## Main results

* `TauCeti.finite_mem_totallyRamifiedOfDegree_wildExponent_le`,
  `TauCeti.finite_mem_totallyRamifiedOfDegree_discriminantExponent_le`,
  `TauCeti.finite_mem_totallyRamifiedOfDegree_wildExponent_eq`: finiteness of each bounded or
  fixed wild-exponent and bounded-discriminant stratum in any characteristic.
* `TauCeti.tsum_ncard_wildExponent_div_natCard_residueField_pow`: consistency of the stratum
  cardinalities with Serre's first mass formula.
* `TauCeti.IsRepresentativeSet.finite_wildExponent_eq`,
  `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: finiteness and
  isomorphism-class mass `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = #{c = j} / n` on a set of
  representatives `R`.
* `TauCeti.tsum_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq`,
  `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum`: total cardinal regrouping across strata, and
  finite total sum over `0 ≤ j ≤ n * v_K(n)` when `(n : K) ≠ 0`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, Colloques
  Internationaux du CNRS **143**, Paris, 1966, 143–169.
-/

public section
noncomputable section

open ValuativeRel
open scoped IntermediateField ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Bounded wild-exponent finiteness**: in any characteristic, only finitely many members of
`σ_K(n)` have wild exponent at most `D`. -/
theorem finite_mem_totallyRamifiedOfDegree_wildExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ D}.Finite :=
  finite_mem_totallyRamifiedOfDegree_wildExponent_le_of_tsum_ne_top
    (tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n) ▸
      ENNReal.natCast_ne_top n) D

/-- **Bounded discriminant finiteness**: in any characteristic, only finitely many members of
`σ_K(n)` have discriminant exponent at most `D`. -/
theorem finite_mem_totallyRamifiedOfDegree_discriminantExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ D}.Finite :=
  (finite_mem_totallyRamifiedOfDegree_wildExponent_le (K := K) n (D + 1)).subset fun _ ⟨hE, _⟩ ↦ by
    have := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hE
    exact ⟨hE, by omega⟩

/-- **Finiteness of each wild-exponent stratum**: for every `n` and `j`, the set of
`E ∈ σ_K(n)` with `E.wildExponent = j` is finite, including in equal characteristic `p` with
`p ∣ n`. -/
theorem finite_mem_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite :=
  (finite_mem_totallyRamifiedOfDegree_wildExponent_le (K := K) n j).subset
    fun _ ⟨hE, hEq⟩ ↦ ⟨hE, hEq.le⟩

/-- **Consistency with Serre's first mass formula**: summing the stratum counts weighted by
`q ^ (-j)` recovers `n`. -/
theorem tsum_ncard_wildExponent_div_natCard_residueField_pow (n : ℕ) :
    ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  have hcast : ∀ j : ℕ,
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j =
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard *
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j) := fun j ↦ by
    rw [div_eq_mul_one_div,
      ← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
      ENat.toENNReal_coe]
  simp_rw [hcast]
  rw [ENNReal.tsum_encard_sep_eq_mul _ IntermediateField.wildExponent
    fun j ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j]
  exact tsum_one_div_natCard_residueField_pow_wildExponent

/-- For a set of representatives `R` of `σ_K(n)`, each wild-exponent stratum `{M ∈ R | c(M) = j}`
is finite. -/
theorem IsRepresentativeSet.finite_wildExponent_eq {n : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R) (j : ℕ) :
    {M ∈ R | M.wildExponent = j}.Finite :=
  (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset
    fun _ ⟨hM, hj⟩ ↦ ⟨hR.subset hM, hj⟩

/-- **Isomorphism-class stratum mass**: for any set of representatives `R` of the `K`-isomorphism
classes in `σ_K(n)`, the Serre mass `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M)` equals
`#{E ∈ σ_K(n) | c(E) = j} / n`. -/
theorem IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq {n : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R) (j : ℕ) :
    ∑' M : {M ∈ R | M.wildExponent = j}, (1 / (Nat.card (M.val ≃ₐ[K] M.val) : ℝ≥0∞)) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) / n := by
  classical
  rcases n.eq_zero_or_pos with rfl | hn
  · obtain rfl : R = ∅ := Set.eq_empty_of_subset hR.subset totallyRamifiedOfDegree_zero
    simp [totallyRamifiedOfDegree_zero]
  let f : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun L ↦ if L.wildExponent = j then 1 else 0
  have hf := hR.tsum_eq_tsum_div_natCard_algEquiv_mul f fun e ↦ by
    simp only [f, IntermediateField.wildExponent_eq_of_algEquiv e]
  have hlhs : ∑' L : totallyRamifiedOfDegree K n, f L =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
    rw [ENNReal.tsum_subtype_ite (totallyRamifiedOfDegree K n) (fun E ↦ E.wildExponent = j)
        fun _ ↦ 1,
      ENNReal.tsum_set_one,
      ← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
      ENat.toENNReal_coe]
  let gR : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun M ↦ 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)
  have hrhs : ∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) * f M =
      (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j}, gR M.val := by
    rw [← ENNReal.tsum_subtype_ite R (fun M ↦ M.wildExponent = j) gR, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun M ↦ ?_
    by_cases h : M.val.wildExponent = j <;> simp [f, gR, h, div_eq_mul_inv]
  rw [hlhs, hrhs] at hf
  exact (ENNReal.eq_div_iff (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)).mpr hf.symm

/-- **Krasner's total count (cardinal form)**: in any characteristic, the extended cardinality of
`σ_K(n)` is the sum over all wild exponents `j` of the stratum counts. -/
theorem tsum_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (n : ℕ) :
    ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
      (totallyRamifiedOfDegree K n).encard := by
  have hcast : ∀ j : ℕ,
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard := fun j ↦ by
    rw [← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
      ENat.toENNReal_coe]
  simp_rw [hcast]
  have h := ENNReal.tsum_encard_sep_eq_mul (totallyRamifiedOfDegree K n)
    IntermediateField.wildExponent fun _ ↦ 1
  simpa using h.trans (ENNReal.tsum_set_one _)

/-- **Krasner's total count away from equal characteristic `p ∣ n`**: when `(n : K) ≠ 0`,
`(totallyRamifiedOfDegree K n).ncard` is the finite sum of the stratum counts for
`0 ≤ j ≤ n * v_K(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1),
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard := by
  have hfin : (totallyRamifiedOfDegree K n).Finite :=
    (tsum_one_div_natCard_residueField_pow_wildExponent_ne_top_iff_finite hnK).mp <| by
      rw [tsum_one_div_natCard_residueField_pow_wildExponent]
      exact ENNReal.natCast_ne_top n
  have htot := tsum_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n
  rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe,
    tsum_eq_sum (s := Finset.range (n * natCastValuation K n hnK + 1))] at htot
  · rw [← Nat.cast_sum] at htot
    exact_mod_cast htot.symm
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have hemp : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun E ⟨hE, hEj⟩ ↦
        (Nat.lt_of_le_of_lt
          (hEj ▸ IntermediateField.wildExponent_le_mul_natCastValuation hE hnK) hj).false
    rw [hemp, Set.ncard_empty, Nat.cast_zero]

end TauCeti
