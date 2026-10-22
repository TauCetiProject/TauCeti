/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

/-!
# Orthogonal refinement of a finite family of idempotents

In a commutative ring, idempotents `e i` are the clopen subsets `D(e i)` of the spectrum.
Finitely many of them can be made disjoint without changing their union: order the index set and
replace `D(e i)` by the part of it not covered by the earlier ones. Algebraically, this gives
orthogonal idempotents `f i` with `f i * e i = f i` and `∑ i, f i = 1 - ∏ i, (1 - e i)`
(`TauCeti.exists_orthogonalIdempotents_sum_eq_one_sub_prod`). If the `D(e i)` cover the spectrum,
that is, if `∏ i, (1 - e i) = 0`, the refinement is a complete orthogonal family
(`TauCeti.exists_completeOrthogonalIdempotents_of_prod_one_sub_eq_zero`).
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The case of a family indexed by `Fin m`, by induction on `m`. -/
private theorem exists_orthogonalIdempotents_sum_eq_one_sub_prod_fin :
    ∀ {m : ℕ} (e : Fin m → R), (∀ i, IsIdempotentElem (e i)) →
      ∃ f : Fin m → R, OrthogonalIdempotents f ∧ (∀ i, f i * e i = f i) ∧
        ∑ i, f i = 1 - ∏ i, (1 - e i)
  | 0, _, _ => ⟨Fin.elim0, ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩, fun i ↦ i.elim0, by simp⟩
  | m + 1, e, he => by
    obtain ⟨f, hf, hfe, hsum⟩ :=
      exists_orthogonalIdempotents_sum_eq_one_sub_prod_fin (Fin.tail e) fun i ↦ he i.succ
    have he₀ := he 0
    -- Keep `e 0` and remove its component from each later `f i`.
    refine ⟨Fin.cons (e 0) fun i ↦ (1 - e 0) * f i, ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩,
      fun i ↦ ?_, ?_⟩
    · cases i using Fin.cases with
      | zero => exact he₀
      | succ i => exact he₀.one_sub.mul (hf.idem i)
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          linear_combination f j * he₀.mul_one_sub_self
      | succ i =>
        have hi : (1 - e 0) * f i * e 0 = 0 := by linear_combination f i * he₀.mul_one_sub_self
        cases j using Fin.cases with
        | zero => simpa only [Fin.cons_zero, Fin.cons_succ] using hi
        | succ j =>
          have hfij := hf.ortho fun h ↦ hij (congrArg Fin.succ h)
          simp only [Fin.cons_succ]
          linear_combination (1 - e 0) ^ 2 * hfij
    · cases i using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using he₀.eq
      | succ i =>
        have hfi : f i * e i.succ = f i := by simpa only [Fin.tail_def] using hfe i
        simp only [Fin.cons_succ]
        linear_combination (1 - e 0) * hfi
    · rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.mul_sum, hsum]
      simp only [Fin.tail_def]
      ring

/-- Finitely many idempotents `e i` of a commutative ring can be refined to orthogonal idempotents
`f i` with `f i * e i = f i` and the same union of components, `∑ i, f i = 1 - ∏ i, (1 - e i)`. -/
theorem exists_orthogonalIdempotents_sum_eq_one_sub_prod {ι : Type*} [Fintype ι] (e : ι → R)
    (he : ∀ i, IsIdempotentElem (e i)) :
    ∃ f : ι → R, OrthogonalIdempotents f ∧ (∀ i, f i * e i = f i) ∧
      ∑ i, f i = 1 - ∏ i, (1 - e i) := by
  let σ := Fintype.equivFin ι
  obtain ⟨f, hf, hfe, hsum⟩ :=
    exists_orthogonalIdempotents_sum_eq_one_sub_prod_fin (e ∘ σ.symm) fun i ↦ he _
  refine ⟨f ∘ σ, hf.embedding σ.toEmbedding, fun i ↦ by simpa using hfe (σ i), ?_⟩
  calc ∑ i, f (σ i) = ∑ i, f i := σ.sum_comp f
    _ = 1 - ∏ i, (1 - e i) := by
      rw [hsum, ← σ.symm.prod_comp fun i ↦ 1 - e i]
      simp only [Function.comp_apply]

/-- Idempotents `e i` whose components cover the spectrum, `∏ i, (1 - e i) = 0`, can be refined to
a complete orthogonal family `f i` with `f i * e i = f i`. -/
theorem exists_completeOrthogonalIdempotents_of_prod_one_sub_eq_zero {ι : Type*} [Fintype ι]
    (e : ι → R) (he : ∀ i, IsIdempotentElem (e i)) (hcover : ∏ i, (1 - e i) = 0) :
    ∃ f : ι → R, CompleteOrthogonalIdempotents f ∧ ∀ i, f i * e i = f i := by
  obtain ⟨f, hf, hfe, hsum⟩ := exists_orthogonalIdempotents_sum_eq_one_sub_prod e he
  exact ⟨f, ⟨hf, by rw [hsum, hcover, sub_zero]⟩, hfe⟩

end TauCeti
