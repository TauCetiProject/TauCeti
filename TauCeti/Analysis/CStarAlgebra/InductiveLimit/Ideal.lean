/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Basic
public import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Closed ideals of C⋆-inductive limits

Let `L = CStarInductiveLimit A f` be the C⋆-inductive limit of a directed system of C⋆-algebras
`A i` with possibly noninjective connecting maps. Every closed two-sided ideal `J` of `L` is the
closure of the union of the images of its preimages: writing `J_i` for the preimage of `J` under the
canonical map `of i : A i → L`,
`J = closure (⋃ i, of i (J_i))`.

The inclusion `⊇` holds because `J` is closed. For `⊆`, approximate `x ∈ J` by `of i a`. The
⋆-homomorphism `A i → L → L ⧸ J` has kernel `J_i`, so it dominates the quotient map
`A i → A i ⧸ J_i` in norm (`NonUnitalStarAlgHom.norm_apply_le_norm_apply_of_ker_le`); hence the
distance from `a` to `J_i` is at most `‖of i a - x‖`
(`NonUnitalStarAlgHom.exists_mem_comap_norm_sub_lt`), and a nearby `b ∈ J_i` gives `of i b ∈ J`
close to `x`.

As a consequence, an inductive limit of simple C⋆-algebras (only `⊥` and `⊤` are closed two-sided
ideals) is simple, also when the connecting maps are not injective: if a closed ideal `J` is not
`⊥`, some `J_i` is `⊤` with `of i ≠ 0`, and then every later `J_j` is `⊤`, so `J` contains the
dense union of the ranges.

## Main statements

* `TauCeti.CStarInductiveLimit.coe_eq_closure_iUnion_image_comap`: a closed two-sided ideal of
  the limit is the closure of the union of the images of its preimages in the stages.
* `TauCeti.CStarInductiveLimit.forall_isClosed_eq_bot_or_eq_top`: an inductive limit of simple
  C⋆-algebras is simple.

## References

* B. Blackadar, *Operator Algebras*, Encyclopaedia of Mathematical Sciences 122, Springer (2006),
  II.8.2.
-/

public section

noncomputable section

open scoped CStarAlgebra

namespace TauCeti

namespace CStarInductiveLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {A : ι → Type*}
  [∀ i, NonUnitalCStarAlgebra (A i)] {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
  [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
  [∀ i j (h : i ≤ j), NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
  [∀ i j (h : i ≤ j), StarHomClass (T h) (A i) (A j)] [DirectedSystem A (f · · ·)]

/-- **Closed ideals of an inductive limit.** A closed two-sided ideal `J` of the C⋆-inductive
limit is the closure of the union of the images of its preimages `J_i` in the stages. The
connecting maps need not be injective. -/
theorem coe_eq_closure_iUnion_image_comap (J : TwoSidedIdeal (CStarInductiveLimit A f))
    (hJ : IsClosed (J : Set (CStarInductiveLimit A f))) :
    (J : Set (CStarInductiveLimit A f)) =
      closure (⋃ i, of A f i '' (J.comap (of A f i) : Set (A i))) := by
  refine subset_antisymm (fun x hx => ?_) (hJ.closure_subset_iff.2 ?_)
  · refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1
      ((dense_iUnion_range_of A f).closure_eq.symm ▸ Set.mem_univ x) (ε / 3) (by positivity)
    obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨b, hb, hab⟩ := NonUnitalStarAlgHom.exists_mem_comap_norm_sub_lt (of A f i) J hx a
      (ε := ε / 3) (by positivity)
    refine ⟨of A f i b, Set.mem_iUnion.2 ⟨i, b, hb, rfl⟩, ?_⟩
    have h1 : ‖of A f i a - x‖ < ε / 3 := by rwa [← dist_eq_norm, dist_comm]
    have h2 : ‖of A f i (a - b)‖ ≤ ‖a - b‖ := NonUnitalStarAlgHom.norm_apply_le _ _
    rw [map_sub] at h2
    calc dist x (of A f i b) = ‖x - of A f i b‖ := dist_eq_norm _ _
      _ ≤ ‖x - of A f i a‖ + ‖of A f i a - of A f i b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖of A f i a - x‖ + ‖of A f i a - of A f i b‖ := by rw [norm_sub_rev x]
      _ < ε := by linarith
  · refine Set.iUnion_subset fun i => ?_
    rintro _ ⟨b, hb, rfl⟩
    exact (TwoSidedIdeal.mem_comap _).1 hb

/-- **An inductive limit of simple C⋆-algebras is simple.** If every stage has only `⊥` and `⊤`
as closed two-sided ideals, so does the C⋆-inductive limit. The connecting maps need not be
injective. -/
theorem forall_isClosed_eq_bot_or_eq_top
    (hA : ∀ i, ∀ I : TwoSidedIdeal (A i), IsClosed (I : Set (A i)) → I = ⊥ ∨ I = ⊤)
    (J : TwoSidedIdeal (CStarInductiveLimit A f))
    (hJ : IsClosed (J : Set (CStarInductiveLimit A f))) : J = ⊥ ∨ J = ⊤ := by
  by_cases h : ∃ i, J.comap (of A f i) = ⊤ ∧ of A f i ≠ 0
  · -- Every later preimage is `⊤`, so `J` contains the dense union of the ranges.
    obtain ⟨i, hi, hne⟩ := h
    right
    have hrange (k : ι) : Set.range (of A f k) ⊆ J := by
      obtain ⟨j, hij, hkj⟩ := exists_ge_ge i k
      have hj : J.comap (of A f j) = ⊤ := by
        refine (hA j _ (J.isClosed_comap (map_continuous (of A f j)) hJ)).resolve_left
          fun hbot => hne ?_
        ext a
        have ha : f i j hij a ∈ J.comap (of A f j) := by
          rw [TwoSidedIdeal.mem_comap, of_f]
          exact (TwoSidedIdeal.mem_comap _).1 (hi ▸ TwoSidedIdeal.mem_top _)
        rw [hbot, TwoSidedIdeal.mem_bot] at ha
        simp [← of_f hij a, ha]
      rintro _ ⟨c, rfl⟩
      rw [← of_f hkj c]
      exact (TwoSidedIdeal.mem_comap _).1 (hj ▸ TwoSidedIdeal.mem_top _)
    have hdense : (Set.univ : Set (CStarInductiveLimit A f)) ⊆ J := by
      rw [← (dense_iUnion_range_of A f).closure_eq]
      exact hJ.closure_subset_iff.2 (Set.iUnion_subset hrange)
    exact eq_top_iff.2 fun x _ => hdense (Set.mem_univ x)
  · -- Every image `of i (J_i)` is `0`, so `J` is the closure of `{0}`.
    simp only [not_exists, not_and, not_not] at h
    left
    have hzero (i : ι) : of A f i '' (J.comap (of A f i) : Set (A i)) ⊆ {0} := by
      rintro _ ⟨b, hb, rfl⟩
      rcases hA i _ (J.isClosed_comap (map_continuous (of A f i)) hJ) with hbot | htop
      · rw [hbot, TwoSidedIdeal.coe_bot] at hb
        simp [Set.mem_singleton_iff.1 hb]
      · simp [h i htop]
    have hsub : (J : Set (CStarInductiveLimit A f)) ⊆ {0} := by
      rw [coe_eq_closure_iUnion_image_comap J hJ, ← closure_singleton (x := (0 : _))]
      exact closure_mono (Set.iUnion_subset hzero)
    exact eq_bot_iff.2 fun x hx => (TwoSidedIdeal.mem_bot _).2 (hsub hx)

end CStarInductiveLimit

end TauCeti
