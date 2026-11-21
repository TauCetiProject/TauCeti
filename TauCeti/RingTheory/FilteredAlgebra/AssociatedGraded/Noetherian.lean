/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration
public import TauCeti.RingTheory.FilteredAlgebra.AssociatedGraded.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Complete filtrations with a noetherian associated graded ring

Let `F` be a decreasing ideal filtration of a possibly noncommutative ring `A` which is complete
and separated (`TauCeti.IsCompleteFiltration`): `⋂ₙ Fⁿ = 0`, and every sequence whose successive
differences lie in `F⁰, F¹, F², …` converges. If the associated graded ring `gr A` is left
noetherian, then so is `A`. No hypothesis such as `F¹ ⊆ Jac(A)` is needed; it follows from
completeness.

The proof lifts generators. For a left ideal `J` of `A`, the principal symbols of elements of `J`
span a left ideal of `gr A`, which is finitely generated, by symbols of finitely many `gᵢ ∈ J` of
orders `dᵢ`. The symbol of any `x ∈ J ∩ Fⁿ` is then a combination of the symbols of the `gᵢ`;
reading off its degree-`n` component gives `aᵢ ∈ Fⁿ⁻ᵈⁱ` with `x - ∑ aᵢ gᵢ ∈ J ∩ Fⁿ⁺¹`. Repeating
this on the error produces coefficient series which converge by completeness, and their limits
`cᵢ` satisfy `x - ∑ cᵢ gᵢ ∈ ⋂ₙ Fⁿ = 0`. Hence the `gᵢ` generate `J`.

This is the noetherian half of the transfer from graded to filtered rings used for Iwasawa
algebras of compact `p`-adic analytic groups, whose associated graded rings for suitable
filtrations are polynomial rings or their skew analogues. The right-sided statement, for the
opposite ring, is in `TauCeti.RingTheory.FilteredAlgebra.AssociatedGraded.Opposite`.

## Main results

* `TauCeti.AlgFiltration.isNoetherianRing_of_isNoetherianRing_associatedGraded`: a complete
  separated filtered ring with left noetherian associated graded ring is left noetherian.

## References

* P. Schneider and J. Teitelbaum, *Algebras of `p`-adic distributions and admissible
  representations*, Invent. Math. 153 (2003), Proposition 1.1 and Lemma 1.4.
* J.-E. Björk, *Filtered Noetherian rings*, in *Noetherian rings and their applications*, Math.
  Surveys Monogr. 24 (1987).
-/

public section

open Finset

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] {F : AlgFiltration A}

/-- The degree-`n` component of `c * σ(g)`, for the symbol `σ(g)` of some `g ∈ Fᵈ`, is the class
of `a * g` for some `a ∈ Fⁿ⁻ᵈ`. -/
private theorem exists_mul_of_apply (c : F.AssociatedGraded) {d : ℕ} (g : F.ideal d) (n : ℕ) :
    ∃ a ∈ F.ideal (n - d), ∃ h : a * g ∈ F.ideal n,
      (c * DirectSum.of F.GradedPiece d (g : F.GradedPiece d)) n =
        ((⟨a * g, h⟩ : F.ideal n) : F.GradedPiece n) := by
  have hzero : ∀ h : 0 * (g : A) ∈ F.ideal n,
      (0 : F.GradedPiece n) = ((⟨0 * g, h⟩ : F.ideal n) : F.GradedPiece n) :=
    fun _ => ((mk_eq_zero_iff _).2 (by simp)).symm
  induction c using DirectSum.induction_on with
  | zero => exact ⟨0, zero_mem _, by simp, by rw [zero_mul, DirectSum.zero_apply, hzero]⟩
  | of i y =>
    induction y using QuotientAddGroup.induction_on with | H y =>
    rw [of_mk_mul_of_mk]
    by_cases hin : i + d = n
    · subst hin
      exact ⟨y, by simp, F.mul_mem y.property g.property,
        DirectSum.of_eq_same _ _⟩
    · exact ⟨0, zero_mem _, by simp, by rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hin), hzero]⟩
  | add c c' hc hc' =>
    obtain ⟨a, ha, h, e⟩ := hc
    obtain ⟨a', ha', h', e'⟩ := hc'
    refine ⟨a + a', add_mem ha ha', by simpa [add_mul] using add_mem h h', ?_⟩
    rw [add_mul, DirectSum.add_apply, e, e', ← QuotientAddGroup.mk_add]
    exact congrArg _ (Subtype.ext (add_mul a a' g).symm)

/-- If the symbol of `x ∈ Fⁿ` lies in the left ideal of `gr A` spanned by the symbols of finitely
many `gᵢ ∈ Fᵈⁱ`, then `x ≡ ∑ aᵢ gᵢ` modulo `Fⁿ⁺¹` for some `aᵢ ∈ Fⁿ⁻ᵈⁱ`. -/
private theorem exists_sub_sum_mul_mem_succ {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (g : ∀ i, F.ideal (d i)) {n : ℕ} (x : F.ideal n)
    (hx : DirectSum.of F.GradedPiece n (x : F.GradedPiece n) ∈ Submodule.span F.AssociatedGraded
      (Set.range fun i => DirectSum.of F.GradedPiece (d i) (g i : F.GradedPiece (d i)))) :
    ∃ a : ι → A, (∀ i, a i ∈ F.ideal (n - d i)) ∧ (x : A) - ∑ i, a i * g i ∈ F.ideal (n + 1) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  choose a ha h e using fun i => exists_mul_of_apply (c i) (g i) n
  refine ⟨a, ha, ?_⟩
  have hsum : (x : F.GradedPiece n) =
      ((∑ i, ⟨a i * g i, h i⟩ : F.ideal n) : F.GradedPiece n) := by
    rw [← DirectSum.of_eq_same (β := F.GradedPiece) n (x : F.GradedPiece n), ← hc,
      DirectSum.sum_apply, QuotientAddGroup.mk_sum]
    exact sum_congr rfl fun i _ => e i
  simpa using (mk_eq_mk_iff _ _).1 hsum

/-- Under the conclusion of `exists_sub_sum_mul_mem_succ` at every order, every `x ∈ J` is
approximated to every order by combinations of the `gᵢ`, with coefficient series whose `n`-th
terms lie in `Fⁿ⁻ᵈⁱ`. -/
private theorem exists_coeff_sub_sum_mem {ι : Type*} [Fintype ι] {J : Submodule A A}
    {d : ι → ℕ} {g : ι → A} (hg : ∀ i, g i ∈ J)
    (hstep : ∀ n x, x ∈ J → x ∈ F.ideal n →
      ∃ a : ι → A, (∀ i, a i ∈ F.ideal (n - d i)) ∧ x - ∑ i, a i * g i ∈ F.ideal (n + 1))
    {x : A} (hx : x ∈ J) :
    ∃ c : ι → ℕ → A, (∀ i n, c i n ∈ F.ideal (n - d i)) ∧
      ∀ N, x - ∑ i, (∑ n ∈ range N, c i n) * g i ∈ F.ideal N := by
  classical
  have key : ∀ n y, ∃ a : ι → A, y ∈ J → y ∈ F.ideal n →
      (∀ i, a i ∈ F.ideal (n - d i)) ∧ y - ∑ i, a i * g i ∈ F.ideal (n + 1) := fun n y => by
    by_cases hy : y ∈ J ∧ y ∈ F.ideal n
    · obtain ⟨a, ha⟩ := hstep n y hy.1 hy.2
      exact ⟨a, fun _ _ => ha⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hy⟩
  choose a ha using key
  -- The successive errors `r N = x - ∑ᵢ (∑ n < N, aₙ(r n)ᵢ) gᵢ`.
  let r : ℕ → A := fun N => Nat.rec x (fun n rn => rn - ∑ i, a n rn i * g i) N
  have hr : ∀ N, r N ∈ J ∧ r N ∈ F.ideal N := fun N => by
    induction N with
    | zero => exact ⟨hx, by simp⟩
    | succ N ih =>
      exact ⟨sub_mem ih.1 (Submodule.sum_mem _ fun i _ => J.smul_mem _ (hg i)),
        (ha N (r N) ih.1 ih.2).2⟩
  refine ⟨fun i n => a n (r n) i, fun i n => (ha n (r n) (hr n).1 (hr n).2).1 i, fun N => ?_⟩
  suffices x - ∑ i, (∑ n ∈ range N, a n (r n) i) * g i = r N from this ▸ (hr N).2
  induction N with
  | zero => simp [r]
  | succ N ih =>
    simp only [sum_range_succ, add_mul, sum_add_distrib, ← sub_sub, ih]
    -- `r (N + 1)` unfolds to `r N - ∑ i, a N (r N) i * g i` by the recursion defining `r`.
    rfl

/-- In a complete separated filtered ring, if every `x ∈ J ∩ Fⁿ` is congruent modulo `Fⁿ⁺¹` to a
combination `∑ aᵢ gᵢ` of elements `gᵢ ∈ J` with `aᵢ ∈ Fⁿ⁻ᵈⁱ`, then the `gᵢ` generate `J`. -/
private theorem le_span_range (hF : IsCompleteFiltration F.ideal) {ι : Type*} [Fintype ι]
    {J : Submodule A A} {d : ι → ℕ} {g : ι → A} (hg : ∀ i, g i ∈ J)
    (hstep : ∀ n x, x ∈ J → x ∈ F.ideal n →
      ∃ a : ι → A, (∀ i, a i ∈ F.ideal (n - d i)) ∧ x - ∑ i, a i * g i ∈ F.ideal (n + 1)) :
    J ≤ Submodule.span A (Set.range g) := by
  intro x hx
  obtain ⟨c, hc, hcx⟩ := exists_coeff_sub_sum_mem hg hstep hx
  -- Shifted by `dᵢ`, the partial sums of the coefficient series are Cauchy, so they converge.
  choose C hC using fun i => hF.exists_limit (fun n => ∑ m ∈ range (n + d i), c i m) fun n => by
    simpa [Nat.add_right_comm n 1 (d i), sum_range_succ] using hc i (n + d i)
  suffices hxC : x = ∑ i, C i * g i by
    rw [hxC]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine (sub_eq_zero.1 (hF.eq_zero_of_forall_mem _ fun k => ?_))
  -- Compare with the approximation of order `N = k + ∑ᵢ dᵢ`.
  set N := k + ∑ i, d i
  have hdN : ∀ i, d i ≤ N - k := fun i => by
    simpa [N] using single_le_sum (fun j _ => Nat.zero_le (d j)) (mem_univ i)
  have hgi : ∀ i, (C i - ∑ n ∈ range N, c i n) * g i ∈ F.ideal k := fun i => by
    have h := hC i (N - d i)
    rw [Nat.sub_add_cancel (by have := hdN i; omega)] at h
    exact F.mul_mem (b := 0) (F.antitone (by have := hdN i; omega) h) (by simp)
  have : x - ∑ i, C i * g i =
      (x - ∑ i, (∑ n ∈ range N, c i n) * g i) - ∑ i, (C i - ∑ n ∈ range N, c i n) * g i := by
    simp only [sub_mul, sum_sub_distrib]
    abel
  rw [this]
  exact sub_mem (F.antitone (by omega) (hcx N)) (Submodule.sum_mem _ fun i _ => hgi i)

/-- A ring with a complete separated decreasing ideal filtration whose associated graded ring is
left noetherian is left noetherian. -/
theorem isNoetherianRing_of_isNoetherianRing_associatedGraded (hF : IsCompleteFiltration F.ideal)
    [IsNoetherianRing F.AssociatedGraded] :
    IsNoetherianRing A := by
  classical
  refine ⟨fun J => ?_⟩
  -- The symbols of the elements of `J` span a finitely generated left ideal of `gr A`.
  let S : Set F.AssociatedGraded := {z | ∃ n, ∃ x : F.ideal n, (x : A) ∈ J ∧
    z = DirectSum.of F.GradedPiece n (x : F.GradedPiece n)}
  obtain ⟨t, htS, hSt⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).1
    (IsNoetherian.noetherian (Submodule.span F.AssociatedGraded S))
  choose d g hgJ hg using fun z : t => htS z.property
  have ht : (t : Set F.AssociatedGraded) =
      Set.range fun z : t => DirectSum.of F.GradedPiece (d z) (g z : F.GradedPiece (d z)) := by
    ext z
    refine ⟨fun hz => ⟨⟨z, hz⟩, (hg ⟨z, hz⟩).symm⟩, ?_⟩
    rintro ⟨z, rfl⟩
    simpa only [← hg z] using Finset.mem_coe.2 z.property
  refine ⟨(univ : Finset t).image fun z => (g z : A), le_antisymm ?_ ?_⟩
  · rw [coe_image, coe_univ, Set.image_univ, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact hgJ z
  · rw [coe_image, coe_univ, Set.image_univ]
    refine le_span_range (d := d) hF hgJ fun n x hxJ hxn => ?_
    refine exists_sub_sum_mul_mem_succ g ⟨x, hxn⟩ ?_
    rw [← ht, ← hSt]
    exact Submodule.subset_span ⟨n, ⟨x, hxn⟩, hxJ, rfl⟩

end TauCeti.AlgFiltration
