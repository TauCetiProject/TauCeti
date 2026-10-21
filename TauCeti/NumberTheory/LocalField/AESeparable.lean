/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Analysis.Polynomial.GCD
import TauCeti.MeasureTheory.Group.BoundedLineSections
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Almost every monic polynomial over a local field is separable

Let `K` be a nonarchimedean local field. A monic polynomial of degree `n` over `K` is its
coefficient vector `a : Fin n → K`, through `TauCeti.Polynomial.monicOfCoeff`. This file proves
that `monicOfCoeff a` is separable for almost every `a`, for every translation-invariant measure on
`Fin n → K` that is finite on compact sets, in particular for Haar measure.

In characteristic zero this is the statement that the discriminant locus is null. Its point is
equal characteristic `p`, where inseparable polynomials exist in every degree divisible by `p`
(for instance `X ^ p - π`): they still form a null set. In Serre's proof of his mass formula for
totally ramified extensions, polynomials are integrated over the Eisenstein region, and this is
what allows the inseparable Eisenstein polynomials, which have no root in a separable closure, to
be discarded.

The proof shows that the inseparable locus is contained in two null sets. The first is the
hyperplane on which the coefficient of `X` vanishes. The second is the zero locus of the resultant
of `f` and `f'` off that hyperplane. It meets each line in the direction of the constant term in
at most `n` points: moving the constant term does not change `f'`, which is nonzero there, and an
inseparable `f + C t` shares a root `β` with `f'` in an algebraic closure, which determines `t` as
`-f(β)`. Sets with boundedly many points on each line in a fixed direction are null by
`MeasureTheory.Measure.measure_eq_zero_of_encard_setOf_add_smul_mem_le`.

## Main results

* `MeasureTheory.Measure.ae_separable_monicOfCoeff`: almost every monic polynomial over `K` is
  separable.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §2, eq. (3).
-/

public section

open Polynomial MeasureTheory Set
open TauCeti.Polynomial (monicOfCoeff monic_monicOfCoeff natDegree_monicOfCoeff
  coeff_monicOfCoeff monicOfCoeff_add_single_zero)

namespace TauCeti

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- On a line in the direction of the constant coefficient through a coefficient vector whose
coefficient of `X` is nonzero, at most `n + 2` monic polynomials of degree `n + 2` are not
separable. -/
private theorem encard_setOf_not_separable_le (x : Fin (n + 2) → K) (hx : x 1 ≠ 0) :
    {t : K | ¬ (monicOfCoeff (x + t • Pi.single 0 1)).Separable}.encard ≤ n + 2 := by
  classical
  set f := monicOfCoeff x
  have hf' : derivative f ≠ 0 := fun h ↦ hx (by
    rw [← coeff_monicOfCoeff x 1]
    simpa [f, coeff_derivative] using congrArg (coeff · 0) h)
  let L := AlgebraicClosure K
  -- A non-separable `f + C t` shares a root `β` with `(f + C t)' = f'`, and `t = -f(β)`.
  have hsub : algebraMap K L '' {t : K | ¬ (monicOfCoeff (x + t • Pi.single 0 1)).Separable} ⊆
      (fun β ↦ -aeval β f) '' (derivative f).rootSet L := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [mem_ofPred_eq, ← Pi.single_smul', smul_eq_mul, mul_one,
      monicOfCoeff_add_single_zero] at ht
    rw [Separable, isCoprime_iff_aeval_ne_zero_of_isAlgClosed K L] at ht
    push Not at ht
    obtain ⟨β, h1, h2⟩ := ht
    refine ⟨β, (mem_rootSet_of_ne hf').mpr (by simpa using h2), ?_⟩
    simp only [map_add, aeval_C] at h1
    linear_combination -h1
  calc _ = (algebraMap K L '' _).encard :=
        ((algebraMap K L).injective.injOn).encard_image.symm
    _ ≤ ((derivative f).rootSet L).encard := (encard_le_encard hsub).trans (encard_image_le _ _)
    _ ≤ (derivative f).natDegree := by
        rw [rootSet, encard_coe_eq_coe_finsetCard]
        exact_mod_cast (Multiset.toFinset_card_le _).trans
          ((card_roots' _).trans natDegree_map_le)
    _ ≤ n + 2 := by
        exact_mod_cast (natDegree_derivative_le f).trans (by simp [f])

end Field

end TauCeti

open TauCeti.Polynomial (continuous_resultant_derivative_monicOfCoeff
  resultant_derivative_monicOfCoeff_eq_zero_iff)

namespace MeasureTheory.Measure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]

/-- **Almost every monic polynomial over a local field is separable.** For every
translation-invariant measure `μ` on the coefficient space `Fin n → K` that is finite on compact
sets, such as Haar measure, the monic polynomial `monicOfCoeff a` with coefficient vector `a` is
separable for `μ`-almost every `a`. This holds in every characteristic. -/
theorem ae_separable_monicOfCoeff (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] : ∀ᵐ a ∂μ, (monicOfCoeff a).Separable := by
  -- In degree at most one every monic polynomial is separable.
  obtain hn | ⟨m, rfl⟩ : n ≤ 1 ∨ ∃ m, n = m + 2 := by
    rcases n with _ | _ | m <;> simp
  · refine Filter.Eventually.of_forall fun a ↦ ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
    · rw [eq_one_of_monic_natDegree_zero (monic_monicOfCoeff a) (natDegree_monicOfCoeff a)]
      exact separable_one
    · rw [(monic_monicOfCoeff a).eq_X_add_C (natDegree_monicOfCoeff a)]
      exact separable_X_add_C _
  -- Otherwise the inseparable locus lies in the union of the hyperplane `a 1 = 0` and the zero
  -- locus of the resultant `r` of `f` and `f'` off that hyperplane. Each of the two meets every
  -- line in a fixed direction in boundedly many points.
  let r (a : Fin (m + 2) → K) : K :=
    resultant (monicOfCoeff a) (derivative (monicOfCoeff a)) (m + 2) (m + 2 - 1)
  have hr : Continuous r := continuous_resultant_derivative_monicOfCoeff
  have hr0 (a : Fin (m + 2) → K) : r a = 0 ↔ ¬ (monicOfCoeff a).Separable :=
    resultant_derivative_monicOfCoeff_eq_zero_iff a
  have h₁ : μ {a | a 1 = 0} = 0 := by
    refine μ.measure_eq_zero_of_encard_setOf_add_smul_mem_le
      (isClosed_eq (continuous_apply 1) continuous_const).measurableSet (Pi.single 1 1) (D := 1)
      fun x ↦ ?_
    have : {t : K | x 1 + t = 0} = {-x 1} := by
      ext t
      simp [eq_neg_iff_add_eq_zero, add_comm]
    simp [this]
  have h₂ : μ ({a | r a = 0} ∩ {a | a 1 ≠ 0}) = 0 := by
    refine μ.measure_eq_zero_of_encard_setOf_add_smul_mem_le
      ((isClosed_eq hr continuous_const).measurableSet.inter
        (isOpen_ne_fun (continuous_apply 1) continuous_const).measurableSet) (Pi.single 0 1)
      (D := m + 2) fun x ↦ ?_
    have h1 (t : K) : (x + t • Pi.single 0 1 : Fin (m + 2) → K) 1 = x 1 := by simp
    by_cases hx : x 1 = 0
    · simp [h1, hx]
    · refine le_trans (encard_le_encard fun t ht ↦ ?_) (TauCeti.encard_setOf_not_separable_le x hx)
      exact (hr0 _).mp ht.1
  rw [ae_iff]
  refine measure_mono_null (fun a ha ↦ ?_) (measure_union_null h₁ h₂)
  by_cases ha1 : a 1 = 0
  · exact Or.inl ha1
  · exact Or.inr ⟨(hr0 a).mpr ha, ha1⟩

end MeasureTheory.Measure
