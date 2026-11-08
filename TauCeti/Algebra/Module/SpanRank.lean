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
when it has a generating family indexed by `Fin n`; a shorter family can be padded with
zeros.

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
  refine ⟨fun hn ↦ ?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := hp.exists_span_finset_card_eq_spanFinrank
    let e : s ↪ Fin n := s.equivFin.toEmbedding.trans (Fin.castLEEmb (hs.trans_le hn))
    refine ⟨Function.extend e Subtype.val 0, le_antisymm (span_le.mpr ?_) (span_mono ?_)⟩
    · rintro _ ⟨i, rfl⟩
      by_cases hi : ∃ a, e a = i
      · obtain ⟨a, rfl⟩ := hi
        rw [e.injective.extend_apply]
        exact subset_span a.2
      · rw [Function.extend_apply' _ _ _ hi]
        exact zero_mem _
    · exact fun x hx ↦ ⟨e ⟨x, hx⟩, e.injective.extend_apply _ _ _⟩
  · rintro ⟨f, rfl⟩
    exact (spanFinrank_span_le_ncard_of_finite (Set.finite_range f)).trans
      (by simpa using Set.ncard_image_le (f := f) (s := Set.univ))

/-- The span of the entries of a list needs at most as many generators as the list has entries. -/
theorem spanFinrank_span_list_le_length (l : List M) :
    (span R {x | x ∈ l}).spanFinrank ≤ l.length := by
  classical
  rw [← List.coe_toFinset]
  exact (spanFinrank_span_le_ncard_of_finite l.toFinset.finite_toSet).trans
    ((Set.ncard_coe_finset _).trans_le l.toFinset_card_le)

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
  -- generators of `p` together with lifts of generators of the image of `q` generate `q`
  have hspan : span R (s ∪ t.image g : Finset M) = q := by
    have hlift : (span R (t.image g : Set M)).map p.mkQ = q.map p.mkQ := by
      rw [map_span, Finset.coe_image, ← Set.image_comp, Function.comp_surjInv, Set.image_id,
        htspan]
    have hsup := congrArg (comap p.mkQ) hlift
    rw [comap_map_mkQ, comap_map_mkQ, sup_eq_right.mpr hpq] at hsup
    rw [Finset.coe_union, span_union, hsspan, hsup]
  calc q.spanFinrank ≤ (s ∪ t.image g).card := hspan ▸
        (spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans_eq
          (Set.ncard_coe_finset _)
    _ ≤ s.card + t.card := (Finset.card_union_le _ _).trans (by grw [Finset.card_image_le])
    _ = _ := by omega

end Submodule
