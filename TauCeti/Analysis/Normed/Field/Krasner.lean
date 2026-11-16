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
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Krasner approximation and countability of finite separable subextensions

Let `L` be an algebraically closed normed field over a normed field `K` satisfying Krasner's lemma
(`IsKrasner K L`), and let `k` be a field whose image in `K` is dense. Any separable element
`x : L` over `K` generates the same extension `K⟮x⟯` as some element `β : L` algebraic over `k`:
approximate `minpoly K x` by a monic polynomial `g ∈ k[X]` of the same degree whose root `β ∈ L`
lies closer to `x` than to any other conjugate of `x`, apply `IsKrasner.krasner` to get
`K⟮x⟯ ≤ K⟮β⟯`, and compare degrees over `K`.

By the primitive element theorem, every finite separable intermediate field `E` of `L / K` has the
form `K⟮β⟯` with `β` algebraic over `k`. When `k` is countable, the elements of `L` algebraic
over `k` are countable, so `L / K` has only countably many finite separable subextensions (and
hence countably many finite subextensions when `K` is perfect).

## Main results

* `IsSeparable.exists_isAlgebraic_adjoin_simple_eq`: every separable element of `L` over `K`
  generates the same simple extension over `K` as an element algebraic over the dense subfield `k`.
* `IntermediateField.exists_isAlgebraic_adjoin_simple_eq`: every finite separable intermediate
  field of `L / K` is generated over `K` by an element algebraic over `k`.
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
the same intermediate field `K⟮x⟯` as some element `β : L` algebraic over a dense subfield `k`. -/
theorem IsSeparable.exists_isAlgebraic_adjoin_simple_eq {x : L} (hx : IsSeparable K x)
    (hk : DenseRange (algebraMap k K)) :
    ∃ β : L, IsAlgebraic k β ∧ K⟮β⟯ = K⟮x⟯ := by
  classical
  have hint : IsIntegral K x := hx.isIntegral
  have hfm : (minpoly K x).Monic := minpoly.monic hint
  have hn : (minpoly K x).natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  -- Choose `δ > 0` at most the distance from `x` to every other conjugate of `x` in `L`.
  let S : Finset L := ((minpoly K x).map (algebraMap K L)).roots.toFinset.erase x
  have hmemS : ∀ x' : L, IsConjRoot K x x' → x ≠ x' → x' ∈ S := by
    intro x' hx' hne
    rw [Finset.mem_erase, Multiset.mem_toFinset, mem_roots (hfm.map _).ne_zero, IsRoot]
    refine ⟨hne.symm, ?_⟩
    have hroot := (isConjRoot_iff_mem_minpoly_rootSet hint).mp hx'
    rw [mem_rootSet_of_ne hfm.ne_zero, aeval_def, eval₂_eq_eval_map] at hroot
    exact hroot
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
  have hM : 0 < max ‖x‖ 1 := lt_max_of_lt_right one_pos
  have hε : 0 < (δ / max ‖x‖ 1) ^ (minpoly K x).natDegree / ((minpoly K x).natDegree + 1) := by
    positivity
  obtain ⟨g, hgm, hdeg, hcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hk hfm hε
  obtain ⟨β, hβ, hxβ⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε (minpoly.aeval K x) hfm
    (hgm.map _) (by rw [natDegree_map, hdeg]) hcoeff (IsAlgClosed.splits _)
  rw [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (div_pos hδ hM).le hn,
    div_mul_cancel₀ _ hM.ne'] at hxβ
  have hβ_evalK : aeval β (g.map (algebraMap k K)) = 0 := (mem_aroots.mp hβ).2
  have hβ_eval : aeval β g = 0 := by simpa [aeval_map_algebraMap] using hβ_evalK
  have hβ_int : IsIntegral K β := ⟨g.map (algebraMap k K), hgm.map _, hβ_evalK⟩
  -- Krasner's lemma gives `K⟮x⟯ ≤ K⟮β⟯`, and degree comparison yields equality.
  have hx_mem : x ∈ K⟮β⟯ :=
    IsKrasner.krasner hx (IsAlgClosed.splits _) hβ_int fun x' hx' hne ↦
      hxβ.trans_le (hδ_le x' hx' hne)
  have hle : K⟮x⟯ ≤ K⟮β⟯ := adjoin_simple_le_iff.mpr hx_mem
  have hfin : FiniteDimensional K K⟮β⟯ := adjoin.finiteDimensional hβ_int
  have hdeg_le : Module.finrank K K⟮β⟯ ≤ Module.finrank K K⟮x⟯ := by
    rw [adjoin.finrank hβ_int, adjoin.finrank hint, hdeg, ← natDegree_map (algebraMap k K)]
    exact natDegree_le_of_dvd (minpoly.dvd K β hβ_evalK) (hgm.map _).ne_zero
  exact ⟨β, ⟨g, hgm.ne_zero, hβ_eval⟩, (eq_of_le_of_finrank_le hle hdeg_le).symm⟩

namespace IntermediateField

/-- **Every finite separable subextension is generated by an element algebraic over a dense
subfield.** Combine the primitive element theorem with Krasner approximation. -/
theorem exists_isAlgebraic_adjoin_simple_eq (E : IntermediateField K L)
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (hk : DenseRange (algebraMap k K)) :
    ∃ β : L, IsAlgebraic k β ∧ K⟮β⟯ = E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  have hα_sep : IsSeparable K (α : L) := by
    rw [IsSeparable, ← IntermediateField.coe_val, minpoly.algHom_eq E.val E.val.injective α]
    exact Algebra.IsSeparable.isSeparable K α
  have hE : K⟮(α : L)⟯ = E := by
    refine le_antisymm (adjoin_simple_le_iff.mpr α.2) fun y hy ↦ ?_
    have hmem : y ∈ (K⟮α⟯).map E.val := ⟨⟨y, hy⟩, hα.symm ▸ mem_top, rfl⟩
    simpa [IntermediateField.adjoin_map] using hmem
  obtain ⟨β, hβ, hβEq⟩ := hα_sep.exists_isAlgebraic_adjoin_simple_eq hk
  exact ⟨β, hβ, hβEq.trans hE⟩

/-- **Countably many finite separable subextensions.** If `k` is a countable dense subfield of `K`,
an algebraically closed Krasner extension `L / K` contains only countably many finite separable
intermediate fields. -/
theorem countable_finiteDimensional_isSeparable [Countable k] (hk : DenseRange (algebraMap k K)) :
    {E : IntermediateField K L | FiniteDimensional K E ∧ Algebra.IsSeparable K E}.Countable := by
  refine ((Algebraic.countable k L).image (fun β : L ↦ K⟮β⟯)).mono ?_
  rintro E ⟨hfin, hsep⟩
  exact exists_isAlgebraic_adjoin_simple_eq E hk

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
