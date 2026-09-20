/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the statements compare the `map_values` witness with another directing measure.
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
-- Public: the conclusions are consequences of almost-sure uniqueness of directing measures.
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Unique
-- Non-public: used to replace the mapped process by an a.e.-equal process.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Congr

/-!
# Compatibility of directing measures with measurable maps

A directing measure is functorial in the state space. If `X` is conditionally i.i.d. with
directing measure `ν`, then applying a measurable map `g` to every coordinate gives the
pushforward directing measure `ν.map g`. If the mapped process is also presented with another
directing measure `ξ`, uniqueness forces `ν.map g = ξ` almost surely.

The same conclusion holds when the mapped coordinates are first selected along an injection and
then changed almost surely. This form compares directing measures attached to two different
presentations of one conditionally i.i.d. family. The countable-family version puts all such
comparisons on one common almost-sure set; it is useful for projective families of finite
marginals, where all restriction maps must commute simultaneously.

## Main results

* `ConditionallyIIDWith.ae_map_directing_eq_of_comp_injective` compares directing measures after
  a measurable value map, an injective coordinate selection, and an a.e. change of the process.
* `ConditionallyIIDWith.ae_map_directing_eq_of_ae_eq` is the coordinate-preserving form.
* `ConditionallyIIDWith.ae_forall_map_directing_eq_of_comp_injective` makes a countable family of
  these compatibility equations hold simultaneously.
-/

public section

noncomputable section

open Filter MeasurableSpace MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure Ω} {ν : Ω → ProbabilityMeasure α} {ξ : Ω → ProbabilityMeasure β}

/-- **Directing measures commute almost surely with a measurable value map and an injective
coordinate selection.**

Suppose `ν` directs `X`, while `ξ` directs `Y`. If, after selecting the coordinates of `X` along
an injection `k`, applying `g` gives `Y` coordinatewise almost surely, then `ξ` is almost surely
the pushforward of `ν` by `g`.

The probability hypothesis is the one needed for almost-sure uniqueness of directing measures;
countable generation of the target measurable space promotes equality on a determining class to
equality of probability measures. -/
theorem ConditionallyIIDWith.ae_map_directing_eq_of_comp_injective
    [IsProbabilityMeasure μ] [CountablyGenerated β]
    {X : ι → Ω → α} {Y : ℕ → Ω → β}
    (hX : ConditionallyIIDWith μ X ν) (hY : ConditionallyIIDWith μ Y ξ)
    {g : α → β} (hg : Measurable g) {k : ℕ → ι} (hk : Function.Injective k)
    (hXY : ∀ i, (fun ω => g (X (k i) ω)) =ᵐ[μ] Y i) :
    (fun ω => (ν ω).map g) =ᵐ[μ] ξ := by
  have hmap : ConditionallyIIDWith μ (fun i ω => g (X (k i) ω))
      (fun ω => (ν ω).map g) :=
    (hX.comp_injective hk).map_values hg
  exact conditionallyIID_ae_unique (hmap.congr_process hXY) hY

/-- **Coordinate-preserving compatibility of directing measures with a measurable value map.**
If `Y i` is almost surely `g ∘ X i` for every coordinate, its directing measure is almost surely
the pushforward of the directing measure of `X`. -/
theorem ConditionallyIIDWith.ae_map_directing_eq_of_ae_eq
    [IsProbabilityMeasure μ] [CountablyGenerated β]
    {X : ℕ → Ω → α} {Y : ℕ → Ω → β}
    (hX : ConditionallyIIDWith μ X ν) (hY : ConditionallyIIDWith μ Y ξ)
    {g : α → β} (hg : Measurable g)
    (hXY : ∀ i, (fun ω => g (X i ω)) =ᵐ[μ] Y i) :
    (fun ω => (ν ω).map g) =ᵐ[μ] ξ :=
  hX.ae_map_directing_eq_of_comp_injective hY hg Function.injective_id hXY

/-- **Countably many directing-measure compatibility equations hold on one almost-sure set.**

For each `c`, the process `Y c` is obtained almost surely by mapping an injectively selected
subfamily of `X` through `g c`. If `ξ c` directs `Y c`, then simultaneously for every `c` it is
the corresponding pushforward of the directing measure of `X`.

The common null set is essential when the equations express compatibility of a countable
projective family: separate almost-sure statements cannot be substituted pointwise into all
levels at once without this promotion. -/
theorem ConditionallyIIDWith.ae_forall_map_directing_eq_of_comp_injective
    {γ : Type*} [Countable γ] {δ : γ → Type*}
    [∀ c, MeasurableSpace (δ c)] [∀ c, CountablyGenerated (δ c)]
    [IsProbabilityMeasure μ]
    {X : ι → Ω → α}
    (hX : ConditionallyIIDWith μ X ν)
    (Y : (c : γ) → ℕ → Ω → δ c) (ξ : (c : γ) → Ω → ProbabilityMeasure (δ c))
    (hY : ∀ c, ConditionallyIIDWith μ (Y c) (ξ c))
    (g : (c : γ) → α → δ c) (hg : ∀ c, Measurable (g c))
    (k : γ → ℕ → ι) (hk : ∀ c, Function.Injective (k c))
    (hXY : ∀ c i, (fun ω => g c (X (k c i) ω)) =ᵐ[μ] Y c i) :
    ∀ᵐ ω ∂μ, ∀ c, (ν ω).map (g c) = ξ c ω := by
  rw [ae_all_iff]
  exact fun c => hX.ae_map_directing_eq_of_comp_injective
    (hY c) (hg c) (hk c) (hXY c)

end Probability

end TauCeti

end

end
