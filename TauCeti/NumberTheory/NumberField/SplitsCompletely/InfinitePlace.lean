/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import TauCeti.NumberTheory.NumberField.SplitsCompletely.Galois
import TauCeti.NumberTheory.NumberField.ComplexConjugation.CMField

/-!
# Labelling split-prime conjugate pairs by infinite places

In a Galois CM field, the primes above a completely split prime form a Galois torsor.
After fixing a finite and an infinite base place, its quotient by complex conjugation
is identified with the infinite places. In particular, a choice of one prime from each
conjugate pair gives a finite-prime label at every infinite place.

This is the pairing used in `New.Parameters.nonempty_infinitePlace_equiv_finPlace`
in `New/Derivatives/Field/WeilData` of lsernau/grh-lean (`72fead1`); see Neukirch,
*Algebraic Number Theory*, Chapter I, §9, for decomposition groups.
-/

public section

namespace NumberField.InfinitePlace

open Ideal MulAction

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E] [IsCMField E] {P : Ideal ℤ}

private theorem chosenPrimeOrbit_bijective (w : InfinitePlace E)
    (Q : P.primesOver (𝓞 E)) (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    {S : Set (P.primesOver (𝓞 E))}
    (hS : ∀ R, (IsCMField.complexConj E).restrictScalars ℚ • R ∈ S ↔ R ∉ S) :
    Function.Bijective (fun R : S ↦ (P.galEquivPrimesOver Q hP).symm R.val • w) := by
  let e := P.galEquivPrimesOver Q hP
  let c := (IsCMField.complexConj E).restrictScalars ℚ
  have hconj : ComplexEmbedding.IsConj w.embedding c :=
    IsCMField.isConj_complexConj E w.embedding
  have hstab : (stabilizer Gal(E/ℚ) w : Set Gal(E/ℚ)) = {1, c} := by
    rw [← mk_embedding w, hconj.coe_stabilizer_mk]
  have hm (g : Gal(E/ℚ)) : e (c * g) = c • e g :=
    (P.galEquivPrimesOver_apply Q hP (c * g)).trans
      ((mul_smul c g Q).trans (congrArg (c • ·) (P.galEquivPrimesOver_apply Q hP g).symm))
  refine ⟨?_, ?_⟩
  · intro R R' h
    let g := e.symm R.val
    let g' := e.symm R'.val
    have hv : g • w = g' • w := h
    have hgg : g'⁻¹ * g ∈ stabilizer Gal(E/ℚ) w := by
      rw [mem_stabilizer_iff, mul_smul, hv, inv_smul_smul]
    rw [← SetLike.mem_coe, hstab, Set.mem_insert_iff, Set.mem_singleton_iff] at hgg
    rcases hgg with h₁ | h₂
    · exact Subtype.ext (e.symm.injective (inv_mul_eq_one.mp h₁).symm)
    · have hcomm : g' * c = c * g' := (g'.commute_complexConj).eq
      have hgc : g = c * g' := by rw [← hcomm, ← h₂, mul_inv_cancel_left]
      have hh : R.val = c • R'.val := by
        rw [← e.apply_symm_apply R.val, ← e.apply_symm_apply R'.val, ← hm]
        exact congrArg e hgc
      exact False.elim ((hS _).mp (hh ▸ R.prop) R'.prop)
  · intro v
    obtain ⟨g, hg⟩ := exists_smul_eq_of_comap_eq (k := ℚ) (w := w) (w' := v)
      (Subsingleton.elim _ _)
    by_cases h : e g ∈ S
    · exact ⟨⟨e g, h⟩, (congrArg (· • w) (e.symm_apply_apply g)).trans hg⟩
    · refine ⟨⟨e (c * g), hm g ▸ (hS _).mpr h⟩,
        (congrArg (· • w) (e.symm_apply_apply (c * g))).trans ?_⟩
      -- The central conjugation fixes the infinite base place, so both choices label `v`.
      have hc : c • w = w :=
        mem_stabilizer_iff.mp (SetLike.mem_coe.mp (hstab ▸ Set.mem_insert_of_mem _ rfl))
      have hcomm : g * c = c * g := g.commute_complexConj.eq
      rw [← hcomm, mul_smul, hc, hg]

/-- Given a finite prime `Q` above a completely split rational prime and a transversal `S`
of complex conjugation on that fiber, each infinite place has a unique prime label in `S`.
The two base places are used to compare the Galois actions. -/
noncomputable def equivPrimesOverTransversal (w : InfinitePlace E) (Q : P.primesOver (𝓞 E))
    (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    {S : Set (P.primesOver (𝓞 E))}
    (hS : ∀ R, (IsCMField.complexConj E).restrictScalars ℚ • R ∈ S ↔ R ∉ S) :
    InfinitePlace E ≃ S :=
  (Equiv.ofBijective _ (chosenPrimeOrbit_bijective w Q hP hS)).symm

/-- A translate of the finite base prime in the transversal corresponds to the same
translate of the infinite base place. -/
@[simp]
theorem equivPrimesOverTransversal_symm_apply (w : InfinitePlace E) (Q : P.primesOver (𝓞 E))
    (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    {S : Set (P.primesOver (𝓞 E))}
    (hS : ∀ R, (IsCMField.complexConj E).restrictScalars ℚ • R ∈ S ↔ R ∉ S)
    (g : Gal(E/ℚ)) (hg : g • Q ∈ S) :
    (w.equivPrimesOverTransversal Q hP (S := S) hS).symm ⟨g • Q, hg⟩ = g • w := by
  have he : (P.galEquivPrimesOver Q hP).symm (g • Q) = g := by
    rw [← P.galEquivPrimesOver_apply Q hP, Equiv.symm_apply_apply]
  simpa only [equivPrimesOverTransversal, Equiv.symm_symm, Equiv.ofBijective_apply] using
    congrArg (· • w) he

/-- If the translate of `Q` belongs to the transversal, it labels the corresponding translate
of the infinite base place. -/
theorem equivPrimesOverTransversal_apply_smul (w : InfinitePlace E) (Q : P.primesOver (𝓞 E))
    (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    {S : Set (P.primesOver (𝓞 E))}
    (hS : ∀ R, (IsCMField.complexConj E).restrictScalars ℚ • R ∈ S ↔ R ∉ S)
    (g : Gal(E/ℚ)) (hg : g • Q ∈ S) :
    w.equivPrimesOverTransversal Q hP (S := S) hS (g • w) = ⟨g • Q, hg⟩ := by
  apply (w.equivPrimesOverTransversal Q hP (S := S) hS).symm.injective
  rw [Equiv.symm_apply_apply, equivPrimesOverTransversal_symm_apply]

end NumberField.InfinitePlace
