/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Invariants

/-!
# Parity of finite Hasse discrepancies

Two systems of local invariants satisfying the Hasse product relation and having the same real
Hasse signs differ at an even number of finite places. This supplies the parity condition on the
finite correction set in the construction of a global form with prescribed local invariants.

The statement uses a finite set containing both supports, so it applies without making a choice
of support. The filtered set is exactly the set of finite places where the two signs differ.

## Reference

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section

open Finset IsDedekindDomain NumberField

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type*} [Field K] [NumberField K]

/-- If two systems have Hasse product one and equal real Hasse signs, the number of finite
places at which their finite Hasse signs differ is even. The finite set `S` may contain extra
places, since these are removed by the filter. -/
theorem even_card_finiteHasse_ne (I J : GlobalFormInvariants K)
    (hI : I.hasseProduct = 1) (hJ : J.hasseProduct = 1)
    (hreal : ∀ w, I.realHasse w = J.realHasse w)
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hSI : Function.mulSupport I.finiteHasse ⊆ S)
    (hSJ : Function.mulSupport J.finiteHasse ⊆ S) :
    Even (S.filter fun v ↦ I.finiteHasse v ≠ J.finiteHasse v).card := by
  classical
  have hsign (a b : ℤˣ) : a * b = if a = b then 1 else -1 := by
    rcases Int.units_eq_one_or a with (rfl | rfl) <;>
      rcases Int.units_eq_one_or b with (rfl | rfl) <;> norm_num
  have hp : (∏ v ∈ S, I.finiteHasse v) = ∏ v ∈ S, J.finiteHasse v := by
    rw [I.hasseProduct_eq_prod_of_mulSupport_subset hSI] at hI
    rw [J.hasseProduct_eq_prod_of_mulSupport_subset hSJ] at hJ
    simp_rw [← hreal] at hJ
    exact mul_right_cancel (hI.trans hJ.symm)
  have hprod : (∏ v ∈ S, I.finiteHasse v * J.finiteHasse v) = 1 := by
    simp_rw [Finset.prod_mul_distrib]
    rw [← hp, ← pow_two]
    simp
  have hfilter : (∏ v ∈ S, I.finiteHasse v * J.finiteHasse v) =
      (-1 : ℤˣ) ^ (S.filter fun v ↦ I.finiteHasse v ≠ J.finiteHasse v).card := by
    simp_rw [hsign]
    simp [Finset.prod_ite]
  rw [hfilter] at hprod
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hprod

/-- The finite places where two admissible systems with equal real Hasse signs disagree form an
even finite set. The returned set is characterized by membership, independently of the supports
used to calculate it. -/
theorem exists_even_finiteHasse_discrepancy (I J : GlobalFormInvariants K)
    (hI : I.IsAdmissible) (hJ : J.IsAdmissible)
    (hreal : ∀ w, I.realHasse w = J.realHasse w) :
    ∃ R : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v, v ∈ R ↔ I.finiteHasse v ≠ J.finiteHasse v) ∧ Even R.card := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 K)) :=
    (hI.hasFiniteMulSupport_finiteHasse.union hJ.hasFiniteMulSupport_finiteHasse).toFinset
  have hSI : Function.mulSupport I.finiteHasse ⊆ S := by
    intro v hv
    simpa [S] using (Or.inl hv : v ∈ Function.mulSupport I.finiteHasse ∪
      Function.mulSupport J.finiteHasse)
  have hSJ : Function.mulSupport J.finiteHasse ⊆ S := by
    intro v hv
    simpa [S] using (Or.inr hv : v ∈ Function.mulSupport I.finiteHasse ∪
      Function.mulSupport J.finiteHasse)
  refine ⟨S.filter fun v ↦ I.finiteHasse v ≠ J.finiteHasse v, ?_,
    even_card_finiteHasse_ne I J hI.hasseProduct_eq_one hJ.hasseProduct_eq_one
      hreal hSI hSJ⟩
  intro v
  simp only [mem_filter]
  constructor
  · exact And.right
  · intro hv
    have hs : I.finiteHasse v ≠ 1 ∨ J.finiteHasse v ≠ 1 := by
      by_contra h
      push Not at h
      exact hv (h.1.trans h.2.symm)
    exact ⟨by simpa [S, Function.mulSupport] using hs, hv⟩

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
