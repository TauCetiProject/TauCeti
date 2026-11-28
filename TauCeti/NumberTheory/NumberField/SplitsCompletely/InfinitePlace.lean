/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import TauCeti.NumberTheory.RamificationInertia.Galois
import TauCeti.NumberTheory.NumberField.ComplexConjugation.CMField

/-!
# Labelling split-prime conjugate pairs by infinite places

In a Galois CM field, fix an infinite place `w` and a prime `Q` over a completely split
rational prime. A set `S` containing one prime of each conjugate pair above that rational
prime is in bijection with the infinite places. The bijection sends `g • w` to `g • Q`
whenever `g • Q` belongs to `S`.

This is the pairing used in `New.Parameters.nonempty_infinitePlace_equiv_finPlace`
in `New/Derivatives/Field/WeilData` of lsernau/grh-lean (`72fead1`); see Neukirch,
*Algebraic Number Theory*, Chapter I, §9, for decomposition groups.
-/

public section

namespace NumberField.InfinitePlace

open Ideal MulAction

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E] [IsCMField E] {P : Ideal ℤ}

private theorem chosenPrimeOrbit_bijective (w : InfinitePlace E)
    (Q : P.primesOver (𝓞 E)) (hP : (P.primesOver (𝓞 E)).ncard = Nat.card Gal(E/ℚ))
    {S : Set (P.primesOver (𝓞 E))}
    (hS : ∀ R, (IsCMField.complexConj E).restrictScalars ℚ • R ∈ S ↔ R ∉ S) :
    Function.Bijective (fun R : S ↦ (P.galEquivPrimesOver Q hP).symm R.val • w) := by
  let e := P.galEquivPrimesOver Q hP
  let c := (IsCMField.complexConj E).restrictScalars ℚ
  have hconj : ComplexEmbedding.IsConj w.embedding c :=
    IsCMField.isConj_complexConj E w.embedding
  have hstab : (stabilizer Gal(E/ℚ) w : Set Gal(E/ℚ)) = {1, c} := by
    rw [← mk_embedding w, hconj.coe_stabilizer_mk]
  have hm (g : Gal(E/ℚ)) : e (c * g) = c • e g := by
    simp only [e, galEquivPrimesOver_apply, TauCeti.smul_primesOver_galRestrict_eq, mul_smul]
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
      have hc : c • w = w := by
        apply mem_stabilizer_iff.mp
        rw [← SetLike.mem_coe, hstab]
        simp
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
  (Equiv.ofBijective _ (chosenPrimeOrbit_bijective w Q
    (hP.trans (IsGaloisGroup.card_eq_finrank Gal(E/ℚ) ℚ E).symm) hS)).symm

-- Evaluate before simp normalizes the action inside the subtype argument.
/-- A translate of the finite base prime in the transversal corresponds to the same
translate of the infinite base place. -/
@[simp↓]
theorem equivPrimesOverTransversal_symm_apply (w : InfinitePlace E) (Q : P.primesOver (𝓞 E))
    (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    {S : Set (P.primesOver (𝓞 E))}
    (hS : ∀ R, (IsCMField.complexConj E).restrictScalars ℚ • R ∈ S ↔ R ∉ S)
    (g : Gal(E/ℚ)) (hg : g • Q ∈ S) :
    (w.equivPrimesOverTransversal Q hP (S := S) hS).symm ⟨g • Q, hg⟩ = g • w := by
  simp only [equivPrimesOverTransversal, Equiv.symm_symm, Equiv.ofBijective_apply,
    TauCeti.smul_primesOver_galRestrict_eq, galEquivPrimesOver_symm_smul]

/-- If the translate of `Q` belongs to the transversal, it labels the corresponding translate
of the infinite base place. -/
@[simp]
theorem equivPrimesOverTransversal_apply_smul (w : InfinitePlace E) (Q : P.primesOver (𝓞 E))
    (hP : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E)
    {S : Set (P.primesOver (𝓞 E))}
    (hS : ∀ R, (IsCMField.complexConj E).restrictScalars ℚ • R ∈ S ↔ R ∉ S)
    (g : Gal(E/ℚ)) (hg : g • Q ∈ S) :
    w.equivPrimesOverTransversal Q hP (S := S) hS (g • w) = ⟨g • Q, hg⟩ := by
  apply (w.equivPrimesOverTransversal Q hP (S := S) hS).symm.injective
  rw [Equiv.symm_apply_apply, equivPrimesOverTransversal_symm_apply]

end NumberField.InfinitePlace
