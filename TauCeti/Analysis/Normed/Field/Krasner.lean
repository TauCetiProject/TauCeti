/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Krasner
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect

import Mathlib.Algebra.AlgebraicCard
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparableDegree
import TauCeti.Analysis.Normed.Field.Approximation
import TauCeti.FieldTheory.IntermediateField.Adjoin.PrimitiveElement

/-!
# Krasner approximation and countability of finite separable subextensions

Let `L` be an algebraically closed normed field over a normed field `K` satisfying Krasner's lemma
(`IsKrasner K L`), and let `k` be a field whose image in `K` is dense. Any separable element
`x : L` over `K` generates the same extension `K⟮x⟯` as some element `β : L` separable over `k`:
approximate `minpoly K x` by a monic polynomial `g ∈ k[X]` of the same degree whose root `β ∈ L`
lies closer to `x` than to any other conjugate of `x`, apply `IsKrasner.krasner` to get
`K⟮x⟯ ≤ K⟮β⟯`, and compare degrees over `K`. Then `g.map (algebraMap k K)` is `minpoly K β`, which
is separable since `β ∈ K⟮x⟯`, so `g` and hence `β` are separable over `k`.

By the primitive element theorem, every finite separable intermediate field `E` of `L / K` has the
form `K⟮β⟯` with `β` separable (and in particular algebraic) over `k`. When `k` is countable, the
elements of `L` algebraic over `k` are countable, so `L / K` has only countably many finite
separable subextensions (and hence countably many finite subextensions when `K` is perfect).

## Main results

* `IsSeparable.exists_isSeparable_adjoin_simple_eq`: every separable element of `L` over `K`
  generates the same simple extension over `K` as an element separable over the dense subfield `k`.
* `IntermediateField.exists_isSeparable_adjoin_simple_eq`: every finite separable intermediate
  field of `L / K` is generated over `K` by an element separable over `k`.
* `IntermediateField.countable_finiteDimensional_isSeparable`: when `k` is countable, `L / K` has
  only countably many finite separable intermediate fields.
* `IntermediateField.countable_finiteDimensional`: when `K` is perfect and `k` is countable,
  `L / K` has only countably many finite intermediate fields.

## References

* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3, §1.5 (Krasner's lemma and its consequences).
* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §6.
-/

public section

open Polynomial IntermediateField

section KrasnerApproximation

variable {k K L : Type*} [Field k] [NormedField K] [NormedField L] [NormedAlgebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [IsKrasner K L] [IsAlgClosed L]

/-- **Krasner approximation of simple separable extensions.** In an algebraically closed normed
extension `L / K` satisfying Krasner's lemma, every separable element `x : L` over `K` generates
the same intermediate field `K⟮x⟯` as some element `β : L` separable over a dense subfield `k`. -/
theorem IsSeparable.exists_isSeparable_adjoin_simple_eq {x : L} (hx : IsSeparable K x)
    (hk : DenseRange (algebraMap k K)) :
    ∃ β : L, IsSeparable k β ∧ K⟮β⟯ = K⟮x⟯ := by
  classical
  have hint : IsIntegral K x := hx.isIntegral
  -- Choose `δ > 0` at most the distance from `x` to every other conjugate of `x` in `L`.
  let S : Finset L := ((minpoly K x).aroots L).toFinset.erase x
  have hmemS : ∀ x' : L, IsConjRoot K x x' → x ≠ x' → x' ∈ S := fun x' hx' hne ↦
    Finset.mem_erase.mpr
      ⟨hne.symm, Multiset.mem_toFinset.mpr ((isConjRoot_iff_mem_minpoly_aroots hint).mp hx')⟩
  obtain ⟨δ, hδ, hδ_le⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x' : L, IsConjRoot K x x' → x ≠ x' → δ ≤ ‖x - x'‖ := by
    by_cases hS : S.Nonempty
    · refine ⟨(S.image fun x' ↦ ‖x - x'‖).min' (hS.image _), ?_, fun x' hx' hne ↦
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x', hmemS x' hx' hne, rfl⟩)⟩
      rw [Finset.lt_min'_iff]
      intro y hy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hy
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hx').symm)
    · exact ⟨1, zero_lt_one, fun x' hx' hne ↦ False.elim <| hS ⟨x', hmemS x' hx' hne⟩⟩
  -- Approximate `minpoly K x` by a monic polynomial `g ∈ k[X]` of the same degree whose root `β`
  -- satisfies `‖x - β‖ < δ`.
  obtain ⟨g, β, hgm, hdeg, hβ_eval, hxβ⟩ :=
    exists_monic_natDegree_eq_aeval_eq_zero_norm_sub_lt (minpoly.monic hint)
      (minpoly.aeval K x) hk hδ
  have hβ_evalK : aeval β (g.map (algebraMap k K)) = 0 := by rwa [aeval_map_algebraMap]
  have hβ_int : IsIntegral K β := ⟨g.map (algebraMap k K), hgm.map _, hβ_evalK⟩
  -- Krasner's lemma gives `K⟮x⟯ ≤ K⟮β⟯`, and degree comparison yields equality.
  have hx_mem : x ∈ K⟮β⟯ :=
    IsKrasner.krasner hx (IsAlgClosed.splits _) hβ_int fun x' hx' hne ↦
      hxβ.trans_le (hδ_le x' hx' hne)
  have hle : K⟮x⟯ ≤ K⟮β⟯ := adjoin_simple_le_iff.mpr hx_mem
  have hfin : FiniteDimensional K K⟮β⟯ := adjoin.finiteDimensional hβ_int
  have hdeg_le : Module.finrank K K⟮β⟯ ≤ Module.finrank K K⟮x⟯ := by
    rw [adjoin.finrank hβ_int, adjoin.finrank hint, ← hdeg, ← natDegree_map (algebraMap k K)]
    exact natDegree_le_of_dvd (minpoly.dvd K β hβ_evalK) (hgm.map _).ne_zero
  have hEq : K⟮β⟯ = K⟮x⟯ := (eq_of_le_of_finrank_le hle hdeg_le).symm
  -- `g.map (algebraMap k K)` is the minimal polynomial of `β` over `K`, separable as `β ∈ K⟮x⟯`.
  have hβK : IsSeparable K β := by
    have : Algebra.IsSeparable K K⟮β⟯ := by
      rw [hEq]
      exact (isSeparable_adjoin_simple_iff_isSeparable K L).mpr hx
    exact (isSeparable_adjoin_simple_iff_isSeparable K L).mp this
  have hmin : g.map (algebraMap k K) = minpoly K β := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ_int) (hgm.map _)
      (minpoly.dvd K β hβ_evalK) ?_
    rw [natDegree_map, hdeg, ← adjoin.finrank hint, ← hEq, adjoin.finrank hβ_int]
  rw [IsSeparable, ← hmin, separable_map] at hβK
  exact ⟨β, hβK.of_dvd (minpoly.dvd k β hβ_eval), hEq⟩

namespace IntermediateField

/-- **Every finite separable subextension is generated by an element separable over a dense
subfield.** In an algebraically closed normed extension `L / K` satisfying Krasner's lemma, every
finite separable intermediate field `E` has the form `K⟮β⟯` with `β : L` separable over a dense
subfield `k` of `K`. -/
theorem exists_isSeparable_adjoin_simple_eq (E : IntermediateField K L)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (hk : DenseRange (algebraMap k K)) :
    ∃ β : L, IsSeparable k β ∧ K⟮β⟯ = E := by
  obtain ⟨α, hα_sep, rfl⟩ := exists_isSeparable_primitive_element E
  exact hα_sep.exists_isSeparable_adjoin_simple_eq hk

/-- **Countably many finite separable subextensions.** If `k` is a countable dense subfield of `K`,
an algebraically closed Krasner extension `L / K` contains only countably many finite separable
intermediate fields. -/
theorem countable_finiteDimensional_isSeparable [Countable k] (hk : DenseRange (algebraMap k K)) :
    {E : IntermediateField K L | FiniteDimensional K E ∧ Algebra.IsSeparable K E}.Countable := by
  refine ((Algebraic.countable k L).image (fun β : L ↦ K⟮β⟯)).mono ?_
  rintro E ⟨hfin, hsep⟩
  obtain ⟨β, hβ, hE⟩ := exists_isSeparable_adjoin_simple_eq E hk
  exact ⟨β, hβ.isIntegral.isAlgebraic, hE⟩

/-- **Countably many finite subextensions over a perfect base.** If `K` is perfect and contains a
countable dense subfield `k`, an algebraically closed Krasner extension `L / K` contains only
countably many finite intermediate fields. -/
theorem countable_finiteDimensional [PerfectField K] [Countable k]
    (hk : DenseRange (algebraMap k K)) :
    {E : IntermediateField K L | FiniteDimensional K E}.Countable := by
  refine (countable_finiteDimensional_isSeparable (k := k) (K := K) (L := L) hk).mono ?_
  intro E hfin
  have : FiniteDimensional K E := hfin
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  exact ⟨hfin, inferInstance⟩

end IntermediateField

end KrasnerApproximation
