/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Generating families and the least number of generators

For a finitely generated submodule, its least number of generators is at most `n` exactly
when it has a generating family indexed by `Fin n`. A minimum generating finset can be
embedded in `Fin n`, with zero at the unused indices. This includes the zero submodule
and the empty family.

If `p ≤ q` are submodules with `p` finitely generated, the `spanFinrank` of `q` is bounded by
those of `p` and the image of `q` in `M ⧸ p`. When `q` is finitely generated, this bounds its
least number of generators: generators of `p` together with lifts of generators of the image
generate `q`. For a non-finitely-generated submodule, `spanFinrank` is defined to be `0`.

## Main results

* `Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family`: `p.spanFinrank ≤ n` exactly
  when `p` is spanned by a family indexed by `Fin n`.
* `Submodule.spanFinrank_span_list_le_length`: the span of a list needs at most as many
  generators as the list's length.
* `Submodule.spanFinrank_restrictScalars_eq`: restricting scalars along a surjective
  `algebraMap` preserves `spanFinrank`.
* `Submodule.spanFinrank_le_spanFinrank_map_mkQ_add_spanFinrank`: for `p ≤ q` with `p`
  finitely generated, `q.spanFinrank ≤ (q.map p.mkQ).spanFinrank + p.spanFinrank`.

## References

* The bound through a quotient is the generator-lifting step in the proof of
  [Stacks Project, Lemma 10.106.7](https://stacks.math.columbia.edu/tag/00NU). It is ported from
  T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Bounding/PrincipalQuotientRegular.lean`, and generalizes its
  `Pcf.spanFinrank_maximalIdeal_le_add_one_of_principal_kernel` from a principal kernel and the
  maximal ideal of a local ring to any submodules `p ≤ q` with `p` finitely generated.
-/

public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finitely generated submodule has at most `n` generators exactly when it is spanned
by a family of length `n`. Zero entries may pad a shorter generating family. -/
theorem FG.spanFinrank_le_iff_exists_fin_generating_family {p : Submodule R M}
    (hp : p.FG) (n : ℕ) :
    p.spanFinrank ≤ n ↔ ∃ f : Fin n → M, span R (Set.range f) = p := by
  classical
  constructor
  · intro hn
    obtain ⟨s, hs, hspan⟩ := hp.exists_span_finset_card_eq_spanFinrank
    let e : s ↪ Fin n := s.equivFin.toEmbedding.trans
      ⟨Fin.castLE (hs.trans_le hn), Fin.castLE_injective _⟩
    let f : Fin n → M := Function.extend e Subtype.val (fun _ ↦ 0)
    refine ⟨f, le_antisymm ?_ ?_⟩
    · apply span_le.mpr
      rintro x ⟨i, rfl⟩
      dsimp [f]
      rw [Function.extend_def]
      split_ifs with hi
      · exact hspan ▸ subset_span (Classical.choose hi).property
      · exact p.zero_mem
    · rw [← hspan]
      apply span_mono
      intro x hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      exact e.injective.extend_apply Subtype.val (fun _ ↦ 0) ⟨x, hx⟩
  · rintro ⟨f, rfl⟩
    exact (spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans
      (by simpa using (Set.ncard_image_le (f := f) (s := Set.univ)))

/-- The span of the entries of a list needs at most as many generators as the list has entries. -/
theorem spanFinrank_span_list_le_length (l : List M) :
    (span R {x | x ∈ l}).spanFinrank ≤ l.length := by
  classical
  calc (span R {x | x ∈ l}).spanFinrank ≤ {x | x ∈ l}.ncard :=
        spanFinrank_span_le_ncard_of_finite l.finite_toSet
    _ = l.toFinset.card := by rw [← Set.ncard_coe_finset]; simp
    _ ≤ l.length := l.toFinset_card_le

section RestrictScalars

variable {R S : Type*} {M : Type u} [CommSemiring R] [Semiring S] [AddCommMonoid M]
  [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Along a surjective `algebraMap R S`, restricting scalars does not change the least number of
generators of an `S`-submodule. -/
theorem spanFinrank_restrictScalars_eq (H : Function.Surjective (algebraMap R S))
    (N : Submodule S M) : (N.restrictScalars R).spanFinrank = N.spanFinrank := by
  rw [spanFinrank, spanFinrank, spanRank_restrictScalars_eq H]

end RestrictScalars

end Submodule

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If `p ≤ q` are submodules with `p` finitely generated, then `q.spanFinrank` is at most the
sum of the `spanFinrank`s of `p` and of the image of `q` in `M ⧸ p`. When `q` is finitely
generated, this is a generator bound: generators of `p` and lifts of generators of the image
generate `q`. For non-finitely-generated `q`, `q.spanFinrank` is defined to be `0`. -/
theorem spanFinrank_le_spanFinrank_map_mkQ_add_spanFinrank {p q : Submodule R M} (hpq : p ≤ q)
    (hp : p.FG) : q.spanFinrank ≤ (q.map p.mkQ).spanFinrank + p.spanFinrank := by
  classical
  by_cases hq : q.FG
  swap
  · simp [spanFinrank_of_not_fg hq]
  obtain ⟨t, ht, htspan⟩ := (hq.map p.mkQ).exists_span_finset_card_eq_spanFinrank
  obtain ⟨s, hs, hsspan⟩ := hp.exists_span_finset_card_eq_spanFinrank
  let g : M ⧸ p → M := Function.surjInv p.mkQ_surjective
  have hg : ∀ y, p.mkQ (g y) = y := Function.surjInv_eq p.mkQ_surjective
  -- the lifts of the generators of the image of `q` generate `q` modulo `p`
  have hlift : (span R (t.image g : Set M)).map p.mkQ = q.map p.mkQ := by
    rw [map_span, Finset.coe_image, ← Set.image_comp, ← htspan]
    congr 1
    simp [hg]
  -- equal images modulo `p`, and `p ≤ q`
  have hspan : span R (s ∪ t.image g : Finset M) = q := by
    have hsup := congrArg (comap p.mkQ) hlift
    rw [comap_map_mkQ, comap_map_mkQ, sup_eq_right.mpr hpq] at hsup
    rw [Finset.coe_union, span_union, hsspan, hsup]
  have hcard : (s ∪ t.image g).card ≤ s.card + t.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  calc q.spanFinrank ≤ (s ∪ t.image g).card := by
        have hbound :=
          (spanFinrank_span_le_ncard_of_finite (R := R) (M := M)
            (s := ↑(s ∪ t.image g : Finset M)) (s ∪ t.image g).finite_toSet)
        simpa only [Set.ncard_coe_finset, hspan] using hbound
    _ ≤ _ := by omega

end Submodule
