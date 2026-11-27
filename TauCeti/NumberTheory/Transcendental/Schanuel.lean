/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import TauCeti.NumberTheory.Transcendental.AlgebraicLogs

import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import TauCeti.FieldTheory.IntermediateField.Adjoin.AlgebraicIndependent
import TauCeti.NumberTheory.Transcendental.Lindemann.Corollaries
import TauCeti.NumberTheory.Transcendental.Lindemann.Theorem

/-!
# Schanuel's conjecture

**Schanuel's conjecture** asserts that if the complex numbers `x₁, …, xₙ` are linearly
independent over `ℚ`, then the field `ℚ(x₁, …, xₙ, exp x₁, …, exp xₙ)` has transcendence degree
at least `n` over `ℚ`. It is open, and is recorded here as the proposition
`TauCeti.SchanuelConjecture`; its consequences take it as an explicit hypothesis.

Two special cases are theorems.

* For `n = 1` it says that `z` or `exp z` is transcendental for every `z ≠ 0`, which follows
  from the Hermite–Lindemann theorem.
* For algebraic `xᵢ` it says that the `exp xᵢ` are algebraically independent, which is the
  Lindemann–Weierstrass theorem in its algebraic independence form.

Assuming the conjecture, `e` and `π` are algebraically independent: apply it to the
`ℚ`-independent pair `(1, π i)`, for which `exp (π i) = -1`. More generally, logarithms of
algebraic numbers that are linearly independent over `ℚ` are algebraically independent, since
their exponentials are algebraic.

## Main definitions

* `TauCeti.SchanuelConjecture`: Schanuel's conjecture, as a proposition.

## Main results

* `TauCeti.SchanuelConjecture.natCard_le_trdeg`: the conjecture for families indexed by an
  arbitrary type.
* `TauCeti.one_le_trdeg_adjoin_exp`: the case `n = 1`, unconditionally.
* `TauCeti.natCard_le_trdeg_adjoin_exp_of_isAlgebraic`: the case of algebraic numbers,
  unconditionally.
* `TauCeti.SchanuelConjecture.algebraicIndependent_exp_one_pi`: the conjecture implies that `e`
  and `π` are algebraically independent over `ℚ`.
* `TauCeti.SchanuelConjecture.algebraicIndependent_of_mem_algebraicLogs`: the conjecture implies
  that `ℚ`-linearly independent logarithms of algebraic numbers are algebraically independent
  over `ℚ`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.3.
* S. Lang, *Introduction to Transcendental Numbers*, Addison-Wesley (1966), where the
  conjecture is attributed to Schanuel.
-/

public section

open Complex IntermediateField Set
open scoped IntermediateField

namespace TauCeti

/-- **Schanuel's conjecture**: if `x₁, …, xₙ ∈ ℂ` are linearly independent over `ℚ`, then the
field `ℚ(x₁, …, xₙ, exp x₁, …, exp xₙ)` has transcendence degree at least `n` over `ℚ`. This is
an open problem; it is recorded as a proposition to be used as an explicit hypothesis. -/
def SchanuelConjecture : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℂ), LinearIndependent ℚ x →
    (n : Cardinal) ≤ Algebra.trdeg ℚ (adjoin ℚ (range x ∪ range fun i ↦ exp (x i)))

/-- The quantified formulation of Schanuel's conjecture. -/
theorem schanuelConjecture_def :
    SchanuelConjecture ↔ ∀ (n : ℕ) (x : Fin n → ℂ), LinearIndependent ℚ x →
      (n : Cardinal) ≤ Algebra.trdeg ℚ (adjoin ℚ (range x ∪ range fun i ↦ exp (x i))) :=
  Iff.rfl

/-- Schanuel's conjecture for a family indexed by an arbitrary type: if `x : ι → ℂ` is linearly
independent over `ℚ`, then `ℚ(x, exp x)` has transcendence degree at least `Nat.card ι`. For
infinite `ι` the bound is `0`. -/
theorem SchanuelConjecture.natCard_le_trdeg (h : SchanuelConjecture) {ι : Type*} {x : ι → ℂ}
    (hx : LinearIndependent ℚ x) :
    (Nat.card ι : Cardinal) ≤ Algebra.trdeg ℚ (adjoin ℚ (range x ∪ range fun i ↦ exp (x i))) := by
  cases finite_or_infinite ι
  · -- Reindex by `Fin (Nat.card ι)`; the ranges do not change.
    let e := (Finite.equivFin ι).symm
    have h₁ : range (x ∘ e) = range x := e.surjective.range_comp x
    have h₂ : (range fun i ↦ exp ((x ∘ e) i)) = range fun i ↦ exp (x i) :=
      e.surjective.range_comp fun i ↦ exp (x i)
    -- `convert` also matches the field structures, which depend on the set of generators.
    convert h (Nat.card ι) (x ∘ e) (hx.comp e e.injective) using 5 <;> rw [h₁, h₂]
  · simp [Nat.card_eq_zero_of_infinite]

/-- The case `n = 1` of Schanuel's conjecture holds: for `z ≠ 0`, the field `ℚ(z, exp z)` has
transcendence degree at least `1`, since `z` or `exp z` is transcendental by the
Hermite–Lindemann theorem. -/
theorem one_le_trdeg_adjoin_exp {z : ℂ} (hz : z ≠ 0) : 1 ≤ Algebra.trdeg ℚ ℚ⟮z, exp z⟯ := by
  obtain ⟨w, hw, hwt⟩ : ∃ w ∈ ({z, exp z} : Set ℂ), Transcendental ℚ w := by
    by_cases hz' : IsAlgebraic ℚ z
    · exact ⟨exp z, by simp, transcendental_exp_of_isAlgebraic hz' hz⟩
    · exact ⟨z, by simp, hz'⟩
  have : Algebra.Transcendental ℚ ℚ⟮z, exp z⟯ :=
    ⟨⟨⟨w, subset_adjoin ℚ _ hw⟩, fun hw' ↦
      hwt ((isAlgebraic_algHom_iff (ℚ⟮z, exp z⟯).val Subtype.val_injective).2 hw')⟩⟩
  exact Cardinal.one_le_iff_pos.2 (trdeg_pos ℚ _)

/-- Schanuel's conjecture holds for algebraic numbers: if algebraic `x : ι → ℂ` is linearly
independent over `ℚ`, then `ℚ(x, exp x)` has transcendence degree at least `Nat.card ι`. Indeed
the `exp xᵢ` are algebraically independent, by the Lindemann–Weierstrass theorem. -/
theorem natCard_le_trdeg_adjoin_exp_of_isAlgebraic {ι : Type*} {x : ι → ℂ}
    (hx : LinearIndependent ℚ x) (halg : ∀ i, IsAlgebraic ℚ (x i)) :
    (Nat.card ι : Cardinal) ≤ Algebra.trdeg ℚ (adjoin ℚ (range x ∪ range fun i ↦ exp (x i))) := by
  cases finite_or_infinite ι
  swap
  · simp [Nat.card_eq_zero_of_infinite]
  let u : ι → integralClosure ℚ ℂ := fun i ↦ ⟨x i, (halg i).isIntegral⟩
  have hu : LinearIndependent ℕ u :=
    (LinearIndependent.of_comp (v := u) (integralClosure ℚ ℂ).val.toLinearMap hx).restrict_scalars'
      ℕ
  have hexp : AlgebraicIndependent ℚ fun i ↦ exp (x i) :=
    (algebraicIndependent_exp u hu).restrictScalars (algebraMap ℚ _).injective
  rw [union_comm]
  exact (natCard_le_trdeg_adjoin_union_iff (by rintro _ ⟨i, rfl⟩; exact halg i)).2 hexp

/-- Schanuel's conjecture implies that `e` and `π` are algebraically independent over `ℚ`. -/
theorem SchanuelConjecture.algebraicIndependent_exp_one_pi (h : SchanuelConjecture) :
    AlgebraicIndependent ℚ ![exp 1, (Real.pi : ℂ)] := by
  -- Apply the conjecture to the pair `(1, π i)`, which is linearly independent over `ℚ`.
  have hind : LinearIndependent ℚ ![(1 : ℂ), Real.pi * I] := by
    refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
    exact ⟨by simpa [Rat.smul_def] using congr_arg re hst,
      by simpa [Rat.smul_def, Real.pi_ne_zero] using congr_arg im hst⟩
  -- Since `exp (π i) = -1`, the field `ℚ(1, π i, e, -1)` lies in `ℚ(e, π, i)`, and `i` is
  -- algebraic.
  have hle : adjoin ℚ (range ![(1 : ℂ), Real.pi * I] ∪ range fun i ↦ exp (![1, Real.pi * I] i)) ≤
      adjoin ℚ (range ![exp 1, (Real.pi : ℂ)] ∪ {I}) := by
    have hπ : (Real.pi : ℂ) ∈ adjoin ℚ (range ![exp 1, (Real.pi : ℂ)] ∪ {I}) :=
      subset_adjoin ℚ _ (Or.inl ⟨1, rfl⟩)
    have hI : I ∈ adjoin ℚ (range ![exp 1, (Real.pi : ℂ)] ∪ {I}) :=
      subset_adjoin ℚ _ (Or.inr rfl)
    rw [adjoin_le_iff]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> fin_cases i
    · exact one_mem _
    · exact mul_mem hπ hI
    · exact subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)
    · simp [exp_pi_mul_I]
  refine (natCard_le_trdeg_adjoin_union_iff (T := {I}) ?_).1 <|
    (h.natCard_le_trdeg hind).trans (trdeg_le_of_injective (inclusion hle)
      (IntermediateField.inclusion_injective hle))
  rintro _ rfl
  exact (isIntegral_I ℚ).isAlgebraic

/-- Schanuel's conjecture implies that every family of logarithms of algebraic numbers, with any
choice of branches, that is linearly independent over `ℚ` is algebraically independent over
`ℚ`. -/
theorem SchanuelConjecture.algebraicIndependent_of_mem_algebraicLogs (h : SchanuelConjecture)
    {ι : Type*} {l : ι → ℂ} (hl : ∀ i, l i ∈ algebraicLogs) (hind : LinearIndependent ℚ l) :
    AlgebraicIndependent ℚ l := by
  -- Algebraic independence is a property of finite subfamilies.
  refine algebraicIndependent_of_finite_type fun t ht ↦ ?_
  have := ht.to_subtype
  -- The exponentials are algebraic, so the conjecture bounds the transcendence degree of the
  -- field generated by the `l i` alone.
  refine (natCard_le_trdeg_adjoin_union_iff ?_).1
    (h.natCard_le_trdeg (hind.comp _ Subtype.val_injective))
  rintro _ ⟨i, rfl⟩
  exact mem_algebraicLogs.1 (hl i)

end TauCeti
