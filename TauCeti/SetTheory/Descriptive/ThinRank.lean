/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Antichain
public import TauCeti.SetTheory.Ordinal.RankBounds
import TauCeti.SetTheory.Cardinal.AlephOne

/-!
# Rank analyses of thinness

A rank below `ω₁` can rule out Cantor antichains in two steps. First, if every fixed-rank
antichain is countable, then so is any antichain of bounded rank. Second, it suffices to find
a bounded-rank Cantor subcopy of any proposed Cantor antichain. The rank need not be measurable
or constant on equivalence classes.

The evidence for these steps is `Setoid.IsThinRankOn`. In a completely metrizable space it
implies `Setoid.IsThinOn`, since a nonempty perfect antichain would contain a Cantor antichain.

## References

* Adapted from Cameron Freer's `cameronfreer/infinitary-logic`,
  `InfinitaryLogic/Descriptive/RankedThinness.lean` (commit `518a366`, Apache-2.0).
-/

public section

open Cardinal Function Ordinal Set

namespace Setoid

variable {X : Type*} {E : Setoid X} {r : X → Ordinal.{o}} {A B : Set X}

/-- If every fixed-rank antichain in `A` is countable, then so is every antichain in `A` whose
ranks have a strict bound below `ω₁`. -/
theorem countable_antichain_of_boundedRankOn (E : Setoid X)
    (hfib : ∀ α < ω₁, ∀ ⦃S : Set X⦄, S ⊆ A ∩ r ⁻¹' {α} →
      S.Pairwise (fun x y => ¬ E x y) → S.Countable)
    (hBA : B ⊆ A) (hB : B.Pairwise (fun x y => ¬ E x y))
    (hbound : TauCeti.BoundedRankOn r B) : B.Countable := by
  obtain ⟨β, hβ, hr⟩ := TauCeti.boundedRankOn_iff.1 hbound
  have hcount : ((r ∘ Subtype.val : B → Ordinal.{o}) ⁻¹' Iio β).Countable := by
    refine TauCeti.countable_preimage_Iio_of_lt_omega_one hβ fun α hα => ?_
    have hsub : B ∩ r ⁻¹' {α} ⊆ A ∩ r ⁻¹' {α} := inter_subset_inter_left _ hBA
    have h := hfib α (hα.trans hβ) hsub (hB.mono inter_subset_left)
    apply (h.preimage (f := (Subtype.val : B → X)) Subtype.val_injective).mono
    intro x hx
    exact mem_inter x.property hx
  exact countable_coe_iff.1 (countable_univ_iff.1 (hcount.mono fun x _ => hr x x.property))

variable [TopologicalSpace X]

/-- Evidence for thinness of `A` with respect to `E`, using a prescribed rank `r`. It suffices
to bound the rank on a continuously embedded Cantor subcopy of each Cantor antichain. -/
structure IsThinRankOn (E : Setoid X) (r : X → Ordinal.{o}) (A : Set X) : Prop where
  /-- All points of `A` have rank below `ω₁`. -/
  lt_omega_one : ∀ x ∈ A, r x < ω₁
  /-- Every antichain contained in a single rank fibre of `A` is countable. -/
  countable_antichain : ∀ α < ω₁, ∀ ⦃B : Set X⦄, B ⊆ A ∩ r ⁻¹' {α} →
    B.Pairwise (fun x y => ¬ E x y) → B.Countable
  /-- Any Cantor antichain has a continuously embedded Cantor subcopy with bounded ranks. -/
  exists_boundedRankOn_comp : ∀ ⦃f : (ℕ → Bool) → X⦄, Continuous f → range f ⊆ A →
    (∀ x y, x ≠ y → ¬ E (f x) (f y)) →
    ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Injective e ∧
      TauCeti.BoundedRankOn r (range (f ∘ e))

/-- Restrict a thinness rank analysis to a subset. -/
theorem IsThinRankOn.mono (h : E.IsThinRankOn r A) (hBA : B ⊆ A) : E.IsThinRankOn r B where
  lt_omega_one x hx := h.lt_omega_one x (hBA hx)
  countable_antichain α hα _ hS :=
    h.countable_antichain α hα (hS.trans (inter_subset_inter_left _ hBA))
  exists_boundedRankOn_comp := fun {_} hf hB => h.exists_boundedRankOn_comp hf (hB.trans hBA)

/-- A rank analysis excludes Cantor antichains: a bounded-rank Cantor subcopy would be
countable, contradicting the continuum lower bound on its number of equivalence classes. -/
theorem IsThinRankOn.not_hasCantorAntichainOn (h : E.IsThinRankOn r A) :
    ¬ E.HasCantorAntichainOn A := by
  intro hCantor
  obtain ⟨f, hf, hfA, -, hanti⟩ := hCantor.exists_injective
  obtain ⟨e, he, heinj, hbound⟩ := h.exists_boundedRankOn_comp hf hfA hanti
  have hsub : range (f ∘ e) ⊆ A := (range_comp_subset_range e f).trans hfA
  have hne (x y : ℕ → Bool) (hxy : x ≠ y) : ¬ E ((f ∘ e) x) ((f ∘ e) y) :=
    hanti (e x) (e y) (heinj.ne hxy)
  have hcount : (range (f ∘ e)).Countable := by
    refine E.countable_antichain_of_boundedRankOn h.countable_antichain hsub ?_ hbound
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact hne x y (ne_of_apply_ne (f ∘ e) hxy)
  have : Countable (range (f ∘ e)) := hcount.to_subtype
  have hcopy : E.HasCantorAntichainOn (range (f ∘ e)) :=
    hasCantorAntichainOn_iff.2 ⟨f ∘ e, hf.comp he, mem_range_self, hne⟩
  exact (aleph0_lt_continuum.trans_le hcopy.continuum_le_mk_quotient_comap).not_ge
    (mk_le_aleph0_iff.2 inferInstance)

/-- In a completely metrizable space, a rank analysis rules out perfect antichains. -/
theorem IsThinRankOn.isThinOn [TopologicalSpace.IsCompletelyMetrizableSpace X]
    (h : E.IsThinRankOn r A) : E.IsThinOn A :=
  isThinOn_iff_not_hasCantorAntichainOn.2 h.not_hasCantorAntichainOn

end Setoid
