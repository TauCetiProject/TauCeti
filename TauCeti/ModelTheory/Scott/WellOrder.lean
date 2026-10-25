/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Order
public import TauCeti.ModelTheory.Scott.Isomorphism
public import Mathlib.ModelTheory.Order
public import Mathlib.ModelTheory.Skolem
public import Mathlib.ModelTheory.Ultraproducts
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Tactic.FinCases

/-!
# Well-orders of a fixed order type are `Lω₁ω`-definable but not first-order axiomatizable

By Scott's isomorphism theorem every countable order `M` has an `Lω₁ω` sentence, in the language
of orders, whose countable models are exactly the orders isomorphic to `M`. When `M` is a
well-order, for example `o.ToType` for a countable ordinal `o`, these are exactly the countable
well-orders of the order type of `M`.

For an infinite well-order this cannot be done in first-order logic, even by a theory with
infinitely many sentences. Every first-order theory of an infinite linear order has a countable
model that is not well-ordered. An infinite linear order contains a strictly monotone or strictly
antitone sequence, so in an ultraproduct over a nonprincipal ultrafilter on `ℕ` its shifted copies
form a strictly decreasing sequence, and by Łoś's theorem the ultraproduct is still a model.
A countable elementary substructure containing this sequence, given by the downward
Löwenheim–Skolem theorem, is the required model. Hence for an infinite countable well-order `M`
no first-order theory has, among countable structures, exactly the copies of `M` as its models.

## Main results

* `TauCeti.exists_sentenceω_realize_iff_nonempty_orderIso`: every countable order has an `Lω₁ω`
  sentence true in exactly the countable orders isomorphic to it.
* `TauCeti.exists_countable_model_not_wellFoundedLT`: every first-order theory of an infinite
  linear order has a countable model that is a linear order but not a well-order.
* `TauCeti.not_exists_theory_model_iff_nonempty_orderIso`: for an infinite countable well-order
  `M`, no first-order theory has as countable models exactly the orders isomorphic to `M`.

## References

* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, in
  *The Theory of Models*, 1965.
* H. Jerome Keisler, *Model Theory for Infinitary Logic*, North-Holland, 1971.
* David Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016.
-/

public section

universe w w'

namespace TauCeti

open FirstOrder FirstOrder.Language Structure Cardinal Filter

/-- Every countable order `M` has an `Lω₁ω` sentence in the language of orders that holds in a
countable order, in any universe, exactly when that order is isomorphic to `M`. For a countable
well-order `M`, such as `o.ToType` for an ordinal `o < ω₁`, its countable models are exactly the
well-orders of the order type of `M`. -/
theorem exists_sentenceω_realize_iff_nonempty_orderIso (M : Type w) [LE M] [Countable M] :
    ∃ σ : Language.order.Sentenceω, ∀ (N : Type w') [Language.order.Structure N] [LE N]
      [Language.order.OrderedStructure N] [Countable N],
      SentenceInf.Realize σ N ↔ Nonempty (M ≃o N) := by
  let := orderStructure M
  obtain ⟨σ, -, hσ⟩ := scott_isomorphism.{_, _, _, w'} (L := Language.order) M
  refine ⟨σ, fun N _ _ _ _ => (hσ N).trans ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ⟨StrongHomClass.toEquiv e⟩⟩⟩
  let := StrongHomClass.toOrderIsoClass Language.order M N (M ≃[Language.order] N)
  exact ⟨OrderIso.ofClass e⟩

/-- **Well-foundedness is not first-order.** Every first-order theory in the language of orders
that holds in an infinite linear order has a countable model that is a linear order, in the same
universe, but not a well-order. -/
theorem exists_countable_model_not_wellFoundedLT (T : Language.order.Theory) (M : Type w)
    [Language.order.Structure M] [LinearOrder M] [Language.order.OrderedStructure M] [Infinite M]
    [M ⊨ T] :
    ∃ (N : Type w) (_ : Language.order.Structure N) (_ : LinearOrder N)
      (_ : Language.order.OrderedStructure N), Countable N ∧ N ⊨ T ∧ ¬ WellFoundedLT N := by
  classical
  -- A family of sequences in `M` that is strictly decreasing in its first index at almost every
  -- coordinate: shifted copies of a strictly monotone sequence, or a strictly antitone one.
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℕ → M, ∀ i, ∀ᶠ n in (cofinite : Filter ℕ), x (i + 1) n < x i n := by
    obtain ⟨f, hf | hf⟩ := Infinite.exists_strictMono_or_strictAnti M
    · refine ⟨fun i n => f (n - i), fun i => ?_⟩
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_gt_atTop i] with n hn
      exact hf (by omega)
    · exact ⟨fun i _ => f i, fun i => .of_forall fun _ => hf (Nat.lt_succ_self i)⟩
  let u := hyperfilter ℕ
  let P := (u : Filter ℕ).Product fun _ => M
  have hP : ∀ φ : Language.order.Sentence, M ⊨ φ → P ⊨ φ := fun φ hφ =>
    (Ultraproduct.sentence_realize φ).mpr (.of_forall fun _ => hφ)
  have : P ⊨ T := (Theory.model_iff T).mpr fun φ hφ => hP φ (Theory.realize_sentence_of_mem T hφ)
  have : P ⊨ Language.order.linearOrderTheory := (Theory.model_iff _).mpr fun φ hφ =>
    hP φ (Theory.realize_sentence_of_mem _ hφ)
  let a : ℕ → P := fun i => (x i : P)
  -- In the ultraproduct, `≤` holds exactly when it holds at almost every coordinate.
  have hrel : ∀ i j, RelMap (leSymb : Language.order.Relations 2) ![a i, a j] ↔
      ∀ᶠ n in (u : Filter ℕ), x i n ≤ x j n := fun i j => by
    have h := Ultraproduct.realize_formula_cast (u := u) (M := fun _ => M)
      ((leSymb : Language.order.Relations 2).formula₂ (.var 0) (.var 1)) ![x i, x j]
    simp only [Formula.realize_rel₂, Term.realize_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      relMap_leSymb] at h
    exact h
  have hle : ∀ i, RelMap (leSymb : Language.order.Relations 2) ![a (i + 1), a i] ∧
      ¬ RelMap (leSymb : Language.order.Relations 2) ![a i, a (i + 1)] := fun i => by
    have hi : ∀ᶠ n in (u : Filter ℕ), x (i + 1) n < x i n := hyperfilter_le_cofinite (hx i)
    refine ⟨(hrel _ _).mpr (hi.mono fun _ h => h.le), fun h => ?_⟩
    obtain ⟨n, h₁, h₂⟩ := ((hrel _ _).mp h).and hi |>.exists
    exact h₂.not_ge h₁
  have ha : Function.Injective a := by
    let := Language.order.linearOrderOfModels P
    exact (strictAnti_nat_of_succ_lt fun i => lt_iff_le_not_ge.mpr (hle i)).injective
  have : Infinite P := .of_injective a ha
  -- A countable elementary substructure containing the decreasing sequence.
  obtain ⟨S, hS, hcard⟩ := exists_elementarySubstructure_card_eq Language.order (Set.range a)
    (ℵ₀ : Cardinal.{w}) le_rfl (by simpa using Cardinal.mk_range_le_lift (f := a))
    (by simp [order.card_eq_one]) (by simp)
  let : LinearOrder S := Language.order.linearOrderOfModels S
  -- `linearOrderOfModels` defines `≤` as the interpretation of `leSymb`.
  have : Language.order.OrderedStructure S := ⟨fun _ => Iff.rfl⟩
  refine ⟨S, inferInstance, inferInstance, this, ?_, inferInstance, fun hwf => ?_⟩
  · rw [← Cardinal.mk_le_aleph0_iff]
    simpa using hcard.le
  · let f : ℕ → S := fun i => ⟨a i, hS (Set.mem_range_self i)⟩
    exact not_strictAnti_of_wellFoundedLT f (strictAnti_nat_of_succ_lt fun i =>
      lt_iff_le_not_ge.mpr (hle i))

/-- **Infinite well-orders are not first-order axiomatizable among countable structures.** For
an infinite countable well-order `M`, no first-order theory in the language of orders has as its
countable models, in the universe of `M`, exactly the orders isomorphic to `M`. Contrast
`TauCeti.exists_sentenceω_realize_iff_nonempty_orderIso`, which gives a single `Lω₁ω` sentence
with this property. -/
theorem not_exists_theory_model_iff_nonempty_orderIso (M : Type w) [LinearOrder M]
    [WellFoundedLT M] [Infinite M] [Countable M] :
    ¬ ∃ T : Language.order.Theory, ∀ (N : Type w) [Language.order.Structure N] [LE N]
      [Language.order.OrderedStructure N] [Countable N], N ⊨ T ↔ Nonempty (M ≃o N) := by
  rintro ⟨T, hT⟩
  let := orderStructure M
  have : M ⊨ T := (hT M).mpr ⟨OrderIso.refl M⟩
  obtain ⟨N, _, _, _, _, hNT, hwf⟩ := exists_countable_model_not_wellFoundedLT T M
  obtain ⟨e⟩ := (hT N).mp hNT
  exact hwf e.symm.toOrderEmbedding.wellFoundedLT

end TauCeti
