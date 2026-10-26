/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Power residues and powers in an adic completion

For a height-one prime `v` of a Dedekind domain `R` with fraction field `K`, an element
`a ∈ R` outside `v` is an `n`-th power in `K_v` exactly when its residue is an `n`-th power,
provided `n` is outside `v`. No finiteness assumption on the residue field is needed.

This compares the power residue conditions in Kummer theory with local power conditions.
The residue-field identification is `residueFieldEquivAdicCompletionIntegers`, and lifting
uses `TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq`.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Lemma 6.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (Hensel's lemma).
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

open IsLocalRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- An element outside `v` is an `n`-th power in the adic completion exactly when its residue
is an `n`-th power, for `n` outside `v`. -/
theorem exists_pow_eq_adicCompletion_iff (v : HeightOneSpectrum R) {n : ℕ} {a : R}
    (hn : (n : R) ∉ v.asIdeal) (ha : a ∉ v.asIdeal) :
    (∃ x : v.adicCompletion K, x ^ n = algebraMap R (v.adicCompletion K) a) ↔
      ∃ b : R ⧸ v.asIdeal, b ^ n = Ideal.Quotient.mk v.asIdeal a := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hunit (r : R) (hr : r ∉ v.asIdeal) :
      IsUnit (algebraMap R (v.adicCompletionIntegers K) r) := by
    by_contra h
    apply hr
    rw [← under_maximalIdeal_adicCompletionIntegers (K := K) v, Ideal.mem_comap]
    simpa only [mem_maximalIdeal, mem_nonunits_iff] using h
  let e : (R ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers K) :=
    v.residueFieldEquivAdicCompletionIntegers (K := K)
  have hea : e (Ideal.Quotient.mk v.asIdeal a) =
      residue _ (algebraMap R (v.adicCompletionIntegers K) a) :=
    v.residueFieldEquivAdicCompletionIntegers_apply_mk a
  constructor
  · rintro ⟨x, hx⟩
    have hxint : Valued.v x ≤ 1 := by
      apply (pow_le_one_iff hn0).mp
      rw [← map_pow, hx]
      exact (mem_adicCompletionIntegers R K v).mp
        (algebraMap R (v.adicCompletionIntegers K) a).2
    let y : v.adicCompletionIntegers K := ⟨x, hxint⟩
    have hy : y ^ n = algebraMap R (v.adicCompletionIntegers K) a := by
      apply Subtype.ext
      simpa only [y, SubmonoidClass.coe_pow, algebraMap_adicCompletionIntegers_apply,
        algebraMap_adicCompletion, Function.comp_apply] using hx
    refine ⟨e.symm (residue _ y), e.injective ?_⟩
    rw [map_pow, e.apply_symm_apply, hea, ← map_pow, hy]
  · rintro ⟨b, hb⟩
    obtain ⟨y₀, hy₀⟩ := residue_surjective (e b)
    have hpow : residue _ y₀ ^ n =
        residue _ (algebraMap R (v.adicCompletionIntegers K) a) := by
      rw [hy₀, ← map_pow, hb, hea]
    have hy₀unit : IsUnit y₀ := by
      apply isUnit_of_map_unit (residue (v.adicCompletionIntegers K))
      exact (isUnit_pow_iff hn0).mp (hpow ▸ (hunit a ha).map (residue _))
    obtain ⟨y, hy, -⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq
      (by simpa using hunit n hn) hy₀unit hpow
    refine ⟨y, ?_⟩
    simpa only [SubmonoidClass.coe_pow, algebraMap_adicCompletionIntegers_apply,
      algebraMap_adicCompletion, Function.comp_apply] using
      congrArg (fun z : v.adicCompletionIntegers K ↦ (z : v.adicCompletion K)) hy

end IsDedekindDomain.HeightOneSpectrum
