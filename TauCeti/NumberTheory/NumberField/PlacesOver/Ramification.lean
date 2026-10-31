/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.FinitePlace
import Mathlib.RingTheory.RamificationInertia.Basic
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Ramification vocabulary for finite places

A finite place of an extension lies over a finite place of the base when their prime ideals
lie over one another. Its local degree is the product of the ramification index and the residue
degree. The local degrees above any fixed place sum to the degree of the extension.

Unlike at infinite places, lying over in this sense does not mean equality of the restricted
absolute values: `w (algebraMap K F x) = v x ^ w.localDegree K`. The two meanings agree exactly
when the local degree is one. This distinction is essential when conjugating systems of linear
forms over an extension: the local degrees are the exponents in the product of local factors.

The equivalence `placesOverEquivPrimesOver` transports Mathlib's ideal-theoretic ramification
API to finite places. In particular, the sum formula reuses
`Ideal.sum_ramification_inertia_eq_finrank` rather than proving a new degree formula.

The statements and the normalization test follow Ralf Stephan's
`DiophantineApproximation/LocalExtension.lean` in `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0). The equivalence uses Mathlib's
`FinitePlace.equivHeightOneSpectrum` and `HeightOneSpectrum.equivPrimesOver`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §1.3, Corollary 1.3.2.
-/

public section

open IsDedekindDomain

namespace NumberField.FinitePlace

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- A finite place lies over another when the corresponding prime ideals lie over one another.
This differs from `AbsoluteValue.LiesOver`, which requires equality on the base field. -/
protected abbrev LiesOver (w : FinitePlace F) (v : FinitePlace K) : Prop :=
  w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal

@[simp]
theorem mk_liesOver_mk_iff (w : HeightOneSpectrum (𝓞 F)) (v : HeightOneSpectrum (𝓞 K)) :
    (mk w).LiesOver (mk v) ↔ w.asIdeal.LiesOver v.asIdeal := by
  simp only [FinitePlace.LiesOver, maximalIdeal_mk]

variable (K) in
/-- The local degree of a finite place over `K`: ramification index times residue degree. -/
noncomputable def localDegree (w : FinitePlace F) : ℕ :=
  w.maximalIdeal.asIdeal.ramificationIdx (𝓞 K) * w.maximalIdeal.asIdeal.inertiaDeg (𝓞 K)

omit [NumberField K] in
/-- The local degree is the product of the ideal-theoretic ramification index and inertia degree. -/
theorem localDegree_def (w : FinitePlace F) :
    w.localDegree K =
      w.maximalIdeal.asIdeal.ramificationIdx (𝓞 K) * w.maximalIdeal.asIdeal.inertiaDeg (𝓞 K) :=
  (rfl)

/-- Every local degree is positive. -/
theorem localDegree_pos (w : FinitePlace F) : 0 < w.localDegree K :=
  mul_pos (w.maximalIdeal.asIdeal.ramificationIdx_pos (𝓞 K))
    (w.maximalIdeal.asIdeal.inertiaDeg_pos (𝓞 K))

/-- Restricting a finite place to the base raises the base place to the local degree. -/
theorem apply_algebraMap (w : FinitePlace F) (v : FinitePlace K) [w.LiesOver v] (x : K) :
    w (algebraMap K F x) = v x ^ w.localDegree K := by
  simpa only [mk_maximalIdeal, localDegree_def] using
    mk_apply_algebraMap v.maximalIdeal w.maximalIdeal x

variable (F) in
/-- The finite places of `F` lying over a given finite place of `K`. -/
def placesOver (v : FinitePlace K) : Set (FinitePlace F) := {w | w.LiesOver v}

@[simp]
theorem mem_placesOver {w : FinitePlace F} {v : FinitePlace K} :
    w ∈ v.placesOver F ↔ w.LiesOver v := Iff.rfl

variable (F) in
/-- Finite places above `v` correspond to prime ideals above its maximal ideal. -/
noncomputable def placesOverEquivPrimesOver (v : FinitePlace K) :
    v.placesOver F ≃ v.maximalIdeal.asIdeal.primesOver (𝓞 F) :=
  (equivHeightOneSpectrum.subtypeEquiv fun w ↦
    (Ideal.liesOver_iff_dvd_map w.maximalIdeal.isPrime.ne_top)).trans
    (HeightOneSpectrum.equivPrimesOver (𝓞 F) v.maximalIdeal.ne_bot)

@[simp]
theorem placesOverEquivPrimesOver_apply (v : FinitePlace K) (w : v.placesOver F) :
    (placesOverEquivPrimesOver F v w).1 = w.1.maximalIdeal.asIdeal :=
  (rfl)

@[simp]
theorem placesOverEquivPrimesOver_symm_apply (v : FinitePlace K)
    (q : v.maximalIdeal.asIdeal.primesOver (𝓞 F)) :
    ((placesOverEquivPrimesOver F v).symm q).1.maximalIdeal.asIdeal = q.1 := by
  simpa only [placesOverEquivPrimesOver_apply] using
    congrArg Subtype.val ((placesOverEquivPrimesOver F v).apply_symm_apply q)

instance (v : FinitePlace K) : Finite (v.placesOver F) :=
  Finite.of_equiv _ (placesOverEquivPrimesOver F v).symm

/-- Only finitely many finite places lie over a fixed finite place. -/
theorem finite_placesOver (v : FinitePlace K) : (v.placesOver F).Finite := Set.toFinite _

/-- There is a finite place above every finite place of the base. -/
theorem nonempty_placesOver (v : FinitePlace K) : (v.placesOver F).Nonempty := by
  have : v.maximalIdeal.asIdeal.IsPrime := v.maximalIdeal.isPrime
  exact Set.nonempty_coe_sort.mp
    (placesOverEquivPrimesOver F v).nonempty

/-- A finite place above `v` restricts to its absolute value exactly when its local degree is one.
In particular, a ramified or nonsplit place need not satisfy `AbsoluteValue.LiesOver`. -/
theorem liesOver_val_iff_localDegree_eq_one (w : FinitePlace F) (v : FinitePlace K)
    [w.LiesOver v] : w.1.LiesOver v.1 ↔ w.localDegree K = 1 := by
  constructor
  · intro h
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    have hpos : 0 < v (z : K) := pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr hz0)
    have hlt : v (z : K) < 1 := by
      rw [← v.mk_maximalIdeal, mk_apply]
      exact (norm_lt_one_iff_mem K v.maximalIdeal z).mpr hz
    have hres : w (algebraMap K F (z : K)) = v (z : K) :=
      AbsoluteValue.LiesOver.apply_algebraMap v.1 (w := w.1) (z : K)
    apply pow_right_injective₀ hpos hlt.ne
    simpa only [pow_one] using (apply_algebraMap w v (z : K)).symm.trans hres
  · intro h
    refine ⟨AbsoluteValue.ext fun x ↦ ?_⟩
    rw [AbsoluteValue.under_def, AbsoluteValue.comp_apply, ← coe_apply, ← coe_apply,
      apply_algebraMap w v, h, pow_one]

open scoped Classical in
attribute [local instance] Fintype.ofFinite in
/-- The sum of the local degrees above a finite place is the degree of the extension. -/
theorem sum_localDegree (v : FinitePlace K) :
    ∑ w ∈ (v.placesOver F).toFinset, w.localDegree K = Module.finrank K F := by
  have : v.maximalIdeal.asIdeal.IsPrime := v.maximalIdeal.isPrime
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F,
    ← Ideal.sum_ramification_inertia_eq_finrank v.maximalIdeal.asIdeal (𝓞 F)]
  rw [← (placesOverEquivPrimesOver F v).sum_comp]
  simp only [placesOverEquivPrimesOver_apply, ← localDegree_def, Finset.sum_set_coe]

/-! The trivial extension and the distinction between prime-theoretic and absolute-value
restriction give normalization checks. -/

open scoped Classical in
attribute [local instance] Fintype.ofFinite in
example (v : FinitePlace K) :
    ∑ w ∈ (v.placesOver K).toFinset, w.localDegree K = 1 := by
  rw [sum_localDegree, Module.finrank_self]

example (w : FinitePlace F) (v : FinitePlace K) [w.LiesOver v]
    (h : 1 < w.localDegree K) : ¬ w.1.LiesOver v.1 := by
  rw [liesOver_val_iff_localDegree_eq_one w v]
  exact h.ne'

end NumberField.FinitePlace
