/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.Polish.Analytic
public import TauCeti.SetTheory.Descriptive.CantorScheme
public import TauCeti.Topology.MetricSpace.Perfect

/-!
# The perfect set theorem for analytic sets

Souslin's perfect set theorem says that an uncountable analytic subset of a Hausdorff space
contains the range of a continuous injection of Cantor space. Consequently an analytic set is
countable or has exactly continuum many points.

An analytic set is the range of a continuous map `f` on a Polish space, so the theorem follows
from a statement about such maps: if `f` has uncountable range, then there is a continuous map
`g` of Cantor space into the domain with `f ∘ g` injective. In the vocabulary of antichains, the
kernel `Setoid.ker f` (the relation `f x = f y`) has a Cantor antichain.

The proof is a Cantor scheme of open sets with uncountable images. Call a point of the domain a
condensation point of `f` when every neighbourhood of it has uncountable image. By second
countability the non-condensation points have countable image, so an open set `U` with
uncountable image contains two condensation points with distinct values. The two values have
disjoint neighbourhoods in the Hausdorff target; shrinking around the two points gives two open
sets of small diameter, with closures inside `U`, with uncountable images, and whose images are
disjoint (`Continuous.exists_split_of_not_countable_image`). Iterating this split produces a
closure-antitone scheme of vanishing diameter in a complete metric on the domain, and
`CantorScheme.VanishingDiam.hasCantorAntichainOn` turns it into a Cantor antichain of
`Setoid.ker f`.

## Main results

* `Setoid.hasCantorAntichainOn_ker_univ_of_not_countable_range`: a continuous map from a Polish
  space to a Hausdorff space with uncountable range has a Cantor antichain for its kernel.
* `MeasureTheory.AnalyticSet.exists_nat_bool_injection_of_not_countable`: **the perfect set
  theorem for analytic sets**.
* `MeasureTheory.AnalyticSet.mk_eq_continuum_of_not_countable`: an uncountable analytic subset of
  a Hausdorff space has exactly `𝔠` points; the upper bound is
  `MeasureTheory.AnalyticSet.mk_le_continuum`.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 29.1 (the perfect set theorem for analytic sets, by a Cantor scheme on
  the condensation points of a parametrization).
* The scheme is assembled as in Mathlib's `Perfect.exists_nat_bool_injection`.
-/

public section

open Set Function Filter Topology Cardinal CantorScheme
open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X]

/-- **Cantor antichains for the kernel of a continuous map.** A continuous map from a Polish
space to a Hausdorff space with uncountable range has a Cantor antichain for its kernel: a
continuous map `g` of Cantor space into the domain with `f ∘ g` injective. -/
theorem Setoid.hasCantorAntichainOn_ker_univ_of_not_countable_range [TopologicalSpace Y]
    [PolishSpace Y] [T2Space X]
    {f : Y → X} (hf : Continuous f) (hrange : ¬(range f).Countable) :
    (Setoid.ker f).HasCantorAntichainOn univ := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  obtain ⟨u, -, hu, hu0⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  -- the open sets with uncountable image
  let P := {U : Set Y // IsOpen U ∧ ¬(f '' U).Countable}
  choose W hW hsep using fun (U : P) (n : ℕ) =>
    hf.exists_split_of_not_countable_image U.2.1 U.2.2 (hu n).1
  let D : List Bool → P := fun l => l.rec ⟨univ, isOpen_univ, by rwa [image_univ]⟩
    fun a l U => ⟨W U l.length a, (hW U l.length a).1, (hW U l.length a).2.1⟩
  let A : List Bool → Set Y := fun l => (D l).1
  have hA (a : Bool) (l : List Bool) : A (a :: l) = W (D l) l.length a := rfl
  have hanti : ClosureAntitone A := fun l a => by
    rw [hA]
    exact (hW (D l) l.length a).2.2.1
  have hdiam : VanishingDiam A := fun x => by
    refine (tendsto_add_atTop_iff_nat 1).1 <|
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu0 (fun _ => zero_le)
        fun n => ?_
    rw [PiNat.res_succ, hA, PiNat.res_length]
    exact (hW (D (PiNat.res x n)) n (x n)).2.2.2
  have hne (l : List Bool) : (A l).Nonempty :=
    nonempty_iff_ne_empty.2 fun h => (D l).2.2 (by simp [A, h])
  have hdom := hanti.map_of_vanishingDiam hdiam hne
  have hlim (x : ℕ → Bool) : (⋂ n, A (PiNat.res x n)).Nonempty :=
    ⟨_, mem_iInter.2 (map_mem ⟨x, hdom ▸ mem_univ x⟩)⟩
  exact hdiam.hasCantorAntichainOn (Setoid.ker f) hlim fun l x hx y hy => by
    rw [hA] at hx hy
    exact hsep (D l) l.length x hx y hy

namespace MeasureTheory

/-- **The perfect set theorem for analytic sets** (Souslin). An uncountable analytic subset of a
Hausdorff space contains the range of a continuous injection of Cantor space. -/
theorem AnalyticSet.exists_nat_bool_injection_of_not_countable [T2Space X] {s : Set X}
    (hs : AnalyticSet s) (hunc : ¬s.Countable) :
    ∃ f : (ℕ → Bool) → X, range f ⊆ s ∧ Continuous f ∧ Injective f := by
  obtain ⟨γ, _, _, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hs
  obtain ⟨h, hh, -, hker⟩ :=
    Setoid.hasCantorAntichainOn_iff.1 (Setoid.hasCantorAntichainOn_ker_univ_of_not_countable_range
      hg hunc)
  exact ⟨g ∘ h, range_comp_subset_range h g, hg.comp hh,
    fun a b hab => by_contra fun hne => hker a b hne hab⟩

/-- **Analytic sets satisfy the continuum hypothesis.** An uncountable analytic subset of a
Hausdorff space has exactly continuum many points. -/
theorem AnalyticSet.mk_eq_continuum_of_not_countable [T2Space X] {s : Set X} (hs : AnalyticSet s)
    (hunc : ¬s.Countable) : #s = 𝔠 := by
  refine hs.mk_le_continuum.antisymm ?_
  obtain ⟨f, hfs, -, hf⟩ := hs.exists_nat_bool_injection_of_not_countable hunc
  have hinj : Injective fun a => (⟨f a, hfs (mem_range_self a)⟩ : s) :=
    fun a b hab => hf (congrArg Subtype.val hab)
  simpa using lift_mk_le_lift_mk_of_injective hinj

end MeasureTheory
