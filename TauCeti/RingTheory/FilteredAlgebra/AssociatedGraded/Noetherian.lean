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
    fun _ => ((gradedPiece_mk_eq_zero_iff _).2 (by simp)).symm
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
  simpa using (gradedPiece_mk_eq_mk_iff _ _).1 hsum

/-- In a complete separated filtered ring, if every `x ∈ J ∩ Fⁿ` is congruent modulo `Fⁿ⁺¹` to a
combination `∑ aᵢ gᵢ` of elements `gᵢ ∈ J ∩ Fᵈⁱ` with `aᵢ ∈ Fⁿ⁻ᵈⁱ`, then the `gᵢ` generate `J`. -/
private theorem le_span_range (hF : IsCompleteFiltration F.ideal) {ι : Type*} [Fintype ι]
    {J : Submodule A A} {d : ι → ℕ} {g : ι → A} (hg : ∀ i, g i ∈ J)
    (hgd : ∀ i, g i ∈ F.ideal (d i))
    (hstep : ∀ n x, x ∈ J → x ∈ F.ideal n →
      ∃ a : ι → A, (∀ i, a i ∈ F.ideal (n - d i)) ∧ x - ∑ i, a i * g i ∈ F.ideal (n + 1)) :
    J ≤ Submodule.span A (Set.range g) := by
  have hJ : ∀ c, Fintype.linearCombination A g c ∈ J := fun c =>
    Submodule.sum_mem _ fun i _ => J.smul_mem _ (hg i)
  -- By successive approximation, combinations `∑ cᵢ gᵢ` with `cᵢ ∈ Fⁿ⁻ᵈⁱ`, which lie in
  -- `J ∩ Fⁿ`, exhaust `J`.
  intro x hx
  obtain ⟨c, -, rfl⟩ := (IsCompleteFiltration.pi fun i => hF.comp_sub_right (d i)).surjOn
    (G := fun n => J ⊓ F.ideal n) (fun y hy => hF.eq_zero_of_forall_mem y fun n => (hy n).2)
    (Fintype.linearCombination A g)
    (fun n => Submodule.map_le_iff_le_comap.2 fun c hc => ⟨hJ c,
      Submodule.sum_mem _ fun i _ => F.antitone (by omega)
        (F.mul_mem (Submodule.mem_pi.1 hc i trivial) (hgd i))⟩)
    (fun n z hz => by
      obtain ⟨a, ha, haz⟩ := hstep n z hz.1 hz.2
      exact ⟨a, Submodule.mem_pi.2 fun i _ => ha i, sub_mem hz.1 (hJ a), haz⟩)
    ⟨hx, by simp⟩
  rw [← Fintype.range_linearCombination]
  exact LinearMap.mem_range_self _ c

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
    refine le_span_range hF hgJ (fun z => (g z).property) fun n x hxJ hxn => ?_
    refine exists_sub_sum_mul_mem_succ g ⟨x, hxn⟩ ?_
    rw [← ht, ← hSt]
    exact Submodule.subset_span ⟨n, ⟨x, hxn⟩, hxJ, rfl⟩

end TauCeti.AlgFiltration
