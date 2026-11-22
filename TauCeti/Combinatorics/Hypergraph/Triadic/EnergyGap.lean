/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Gap
public import TauCeti.Combinatorics.Hypergraph.Triadic.Basic
import TauCeti.Combinatorics.Hypergraph.Polyad.Energy.Stability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Top regularity over a coarse skeleton from a small energy gap

Let the lower skeleton of `D` refine that of `C`. This file shows that a coloring `H` which is
top-regular over most fine polyads is also top-regular over most coarse polyads as soon as the
polyad energy gap between the two skeletons is small. Slicing
(`Colored3Graph.TopRegularOverMostPolyads.of_refinement`) passes top regularity in the other
direction, from coarse polyads to their large fine children.

Each irregular coarse polyad is charged, through the local criterion
`Colored3Graph.isTopRegularOverPolyad_of_sum_coarsen_le`, to its irregular fine children and to
the support-weighted deviations of the fine densities from the coarse ones. By
`Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_coarsen_le_of_color_eq`, if
`H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g`, the palette-summed deviation across
all `q = |κ|` top colors is at most `√(q g) |V| (|V| - 1) (|V| - 2)`. Summing the charges gives,
for polyad decompositions,

`H.exceptionalPolyadMass C δ r ≤ (H.exceptionalPolyadMass D η r + √(q g)) / (δ² - η)`

(`Colored3Graph.exceptionalPolyadMass_le_of_polyadEnergy_sub_le`).

More generally, when `π : Polyad3 D.skeleton → Polyad3 C.skeleton` is only an approximate
coarsening—for instance when pair regularization edits a small set of ordered pairs—combining
`Colored3Graph.isTopRegularOverPolyad_of_sum_polyadMap_le` with the palette-summed deviation bound
`Colored3Graph.sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le` bounds the coarse
exceptional mass by `(μ + √(q (g + 3 #M / N)) + 6 #M / N) / (δ² - η)`, where
`N = |V|.descFactorial 3` and `M` is the moved-triple set: `q` enters inside `√(q (g + 3 #M / N))`
while the additive `6 #M / N` term has no `q`-factor
(`Colored3Graph.exceptionalPolyadMass_le_of_polyadMap_polyadEnergy_sub_le`). Likewise, when a
recolored hypergraph has fine densities close in `L¹` to a coarse target `a`,
`Colored3Graph.exceptionalPolyadMass_le_of_sum_abs_relativeDensity_sub_le` transfers top regularity
to the coarse skeleton.

The coarse tolerance `δ` only has to satisfy `δ² > η` and to dominate the energy gap, so it can be
prescribed in terms of the complexity of the coarse skeleton alone. This is the mechanism behind
strong regularity: after iterating energy increments until the gap between two consecutive
skeletons is small compared with a schedule evaluated at the complexity of the coarser one, the
coarser skeleton is top-regular at that scheduled tolerance. A refinement
of the pair palette alone, as produced by `Colored3Graph.exists_topRegularOverMostPolyads`, is
one instance of the refinement hypothesis.

## Main definitions

* `TauCeti.topRegularFineTolerance`, `TauCeti.topRegularFineProportion`, and
  `TauCeti.topRegularEnergyGap`: calibrated fine tolerance, exceptional proportion, and energy-gap
  threshold for scheduled-rank regularity transfer.

## Main results

* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_polyadMap_polyadEnergy_sub_le` and
  `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_polyadMap_polyadEnergy_sub_le`: coarse
  exceptional mass and top regularity over most polyads along an arbitrary polyad map.
* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_vertexPart_le_of_polyadEnergy_sub_le` and
  `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_vertexPart_le_of_polyadEnergy_sub_le`:
  transfer under vertex-partition refinement with pair-color edits.
* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_polyadEnergy_sub_le`,
  `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_polyadEnergy_sub_le`, and
  `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_polyadEnergy_sub_le_topRegularEnergyGap`:
  exact-refinement specializations, including the scheduled-rank calibration.
* `TauCeti.Colored3Graph.exceptionalPolyadMass_le_of_sum_abs_relativeDensity_sub_le` and
  `TauCeti.Colored3Graph.TopRegularOverMostPolyads.of_sum_abs_relativeDensity_sub_le`: transfer when
  fine densities match an arbitrary coarse reference target in `L¹`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
-/

public section

open Finset

namespace TauCeti

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {η δ : ℝ} {r : ℕ}

open Classical in
/-- Generic charging bound: if each irregular coarse polyad `P` has `(δ² - η) |P|` bounded by its
irregular fine children under `π` plus a nonnegative charge `charge P`, and `∑ P, charge P ≤ β N`
whenever `N = |V|.descFactorial 3 > 0`, then the coarse exceptional mass is at most
`(H.exceptionalPolyadMass D η r + β) / (δ² - η)`. -/
private theorem exceptionalPolyadMass_le_of_sum_charge_le
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (π : Polyad3 D.skeleton → Polyad3 C.skeleton)
    (charge : Polyad3 C.skeleton → ℝ) (hcharge₀ : ∀ P, 0 ≤ charge P)
    {β : ℝ} (hβ₀ : 0 ≤ β)
    (hB : 0 < ((Fintype.card V).descFactorial 3 : ℝ) →
      ∑ P, charge P ≤ β * (Fintype.card V).descFactorial 3)
    (hηδ : η < δ ^ 2)
    (hloc : ∀ P, ¬H.IsTopRegularOverPolyad P δ r →
      (δ ^ 2 - η) * #P.support ≤
        (∑ Q : Polyad3 D.skeleton with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r,
          (#Q.support : ℝ)) + charge P) :
    H.exceptionalPolyadMass C δ r ≤ (H.exceptionalPolyadMass D η r + β) / (δ ^ 2 - η) := by
  set θ := δ ^ 2 - η
  have hθ : 0 < θ := sub_pos.2 hηδ
  let irr (P : Polyad3 C.skeleton) : ℝ :=
    ∑ Q : Polyad3 D.skeleton with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ)
  have hP_le (P : Polyad3 C.skeleton) :
      (if ¬H.IsTopRegularOverPolyad P δ r then θ * #P.support else 0) ≤ irr P + charge P := by
    by_cases hP : H.IsTopRegularOverPolyad P δ r
    · simp only [hP, not_true_eq_false, ↓reduceIte]
      exact add_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (hcharge₀ P)
    · simp only [hP, not_false_eq_true, ↓reduceIte]
      exact hloc P hP
  have hirr : ∑ P, irr P =
      ∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ) := by
    rw [sum_filter, ← sum_fiberwise univ π]
    refine sum_congr rfl fun P _ ↦ ?_
    rw [← sum_filter, filter_filter]
  rw [exceptionalPolyadMass_eq_sum_div hC, exceptionalPolyadMass_eq_sum_div hD]
  obtain hN | hN := (Nat.cast_nonneg (α := ℝ) ((Fintype.card V).descFactorial 3)).eq_or_lt
  · rw [← hN, div_zero, div_zero, zero_add]
    exact div_nonneg hβ₀ hθ.le
  · have htotal : θ * ∑ P : Polyad3 C.skeleton with ¬H.IsTopRegularOverPolyad P δ r,
        (#P.support : ℝ) ≤
        (∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η r, (#Q.support : ℝ)) +
          β * (Fintype.card V).descFactorial 3 := by
      rw [mul_sum, sum_filter]
      calc _ ≤ ∑ P, (irr P + charge P) := sum_le_sum fun P _ ↦ by
              simpa only [apply_ite (θ * ·), mul_zero] using hP_le P
        _ = ∑ P, irr P + ∑ P, charge P := sum_add_distrib
        _ ≤ _ := add_le_add hirr.le (hB hN)
    rw [div_le_div_iff₀ hN hθ, add_mul, div_mul_cancel₀ _ hN.ne']
    linarith

open Classical in
/-- Re-index the fiberwise support-weighted density deviations across `π` into a single sum over
fine polyads. -/
private theorem sum_sum_fiber_abs_relativeDensity_sub [Fintype κ]
    (π : Polyad3 D.skeleton → Polyad3 C.skeleton)
    (a : Polyad3 C.skeleton → κ → ℝ) :
    ∑ P : Polyad3 C.skeleton, ∑ c : κ,
        ∑ Q : Polyad3 D.skeleton with π Q = P,
          (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) - a P c| =
      ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) *
        ∑ c : κ, |(H.relativeDensity c Q : ℝ) - a (π Q) c| := by
  rw [← sum_fiberwise univ π]
  refine sum_congr rfl fun P _ ↦ ?_
  rw [sum_comm]
  exact sum_congr rfl fun Q hQ ↦ by rw [mul_sum, (mem_filter.1 hQ).2]

open Classical in
/-- Across all coarse polyads `P`, the moved triples in fine children `π Q = P` together with those
in `P.support` sum to `2 #M`. -/
private theorem sum_moved_polyadMap (π : Polyad3 D.skeleton → Polyad3 C.skeleton) :
    ∑ P : Polyad3 C.skeleton,
        ((∑ Q : Polyad3 D.skeleton with π Q = P,
            (#(({x | Polyad3.ofTriple C.skeleton x ≠
                π (Polyad3.ofTriple D.skeleton x)} : Finset _) ∩ Q.support) : ℝ)) +
          #(({x | Polyad3.ofTriple C.skeleton x ≠
              π (Polyad3.ofTriple D.skeleton x)} : Finset _) ∩ P.support)) =
      2 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)}
  rw [sum_add_distrib, sum_fiberwise univ π]
  have h₁ : ∑ Q : Polyad3 D.skeleton, (#(M ∩ Q.support) : ℝ) = #M :=
    mod_cast Polyad3.sum_card_inter_support (S := D.skeleton) M
  have h₂ : ∑ P : Polyad3 C.skeleton, (#(M ∩ P.support) : ℝ) = #M :=
    mod_cast Polyad3.sum_card_inter_support (S := C.skeleton) M
  linarith

open Classical in
/-- Parameterized charging lemma along `π : Polyad3 D.skeleton → Polyad3 C.skeleton` for a coarse
target `a` and multiplier `k ≥ 0`. -/
private theorem exceptionalPolyadMass_le_of_polyadMap_target_le [Fintype κ]
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (π : Polyad3 D.skeleton → Polyad3 C.skeleton)
    (a : Polyad3 C.skeleton → κ → ℝ) {k β cM : ℝ}
    (hk : 0 ≤ k) (hβ : 0 ≤ β) (hcM : 0 ≤ cM)
    (hdev : ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) *
        ∑ c, |(H.relativeDensity c Q : ℝ) - a (π Q) c| ≤
      β * (Fintype.card V).descFactorial 3 +
        cM * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)})
    (hηδ : η < δ ^ 2)
    (hreg : ∀ P : Polyad3 C.skeleton,
      (∀ c, (∑ Q : Polyad3 D.skeleton with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r,
          (#Q.support : ℝ)) +
        k * (∑ Q : Polyad3 D.skeleton with π Q = P,
          (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) - a P c|) +
        k * ((∑ Q : Polyad3 D.skeleton with π Q = P,
          (#(({x | Polyad3.ofTriple C.skeleton x ≠
            π (Polyad3.ofTriple D.skeleton x)} : Finset _) ∩ Q.support) : ℝ)) +
          #(({x | Polyad3.ofTriple C.skeleton x ≠
            π (Polyad3.ofTriple D.skeleton x)} : Finset _) ∩ P.support)) ≤
        (δ ^ 2 - η) * #P.support) →
      H.IsTopRegularOverPolyad P δ r) :
    H.exceptionalPolyadMass C δ r ≤
      (H.exceptionalPolyadMass D η r + k * β +
        k * (cM + 2) *
          #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
          (Fintype.card V).descFactorial 3) / (δ ^ 2 - η) := by
  set M : Finset {x : Fin 3 → V // Function.Injective x} :=
    {x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)}
  let dev (c : κ) (P : Polyad3 C.skeleton) : ℝ :=
    ∑ Q : Polyad3 D.skeleton with π Q = P,
      (#Q.support : ℝ) * |(H.relativeDensity c Q : ℝ) - a P c|
  let mov (P : Polyad3 C.skeleton) : ℝ :=
    (∑ Q : Polyad3 D.skeleton with π Q = P, (#(M ∩ Q.support) : ℝ)) + #(M ∩ P.support)
  have hdev₀ (c : κ) (P : Polyad3 C.skeleton) : 0 ≤ dev c P :=
    sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  rw [add_assoc (H.exceptionalPolyadMass D η r)]
  refine exceptionalPolyadMass_le_of_sum_charge_le hC hD π
    (fun P ↦ k * (∑ c, dev c P) + k * mov P)
    (fun P ↦ add_nonneg (mul_nonneg hk (sum_nonneg fun c _ ↦ hdev₀ c P))
      (mul_nonneg hk (add_nonneg (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    (by positivity)
    (fun hN ↦ ?_) hηδ fun P hP ↦ ?_
  · have hdev_sum : ∑ P, ∑ c, dev c P ≤ β * (Fintype.card V).descFactorial 3 + cM * #M :=
      (sum_sum_fiber_abs_relativeDensity_sub (H := H) π a).le.trans hdev
    have hmov_sum : ∑ P, mov P = 2 * #M := sum_moved_polyadMap π
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hmov_sum, add_mul, div_mul_cancel₀ _ hN.ne']
    nlinarith [mul_le_mul_of_nonneg_left hdev_sum hk]
  · have : ¬∀ c, (∑ Q : Polyad3 D.skeleton with π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r,
        (#Q.support : ℝ)) + k * dev c P + k * mov P ≤ (δ ^ 2 - η) * #P.support :=
      fun h ↦ hP (hreg P h)
    obtain ⟨c, hc⟩ := not_forall.1 this
    have hle := mul_le_mul_of_nonneg_left (single_le_sum (fun c _ ↦ hdev₀ c P) (mem_univ c)) hk
    linarith [not_le.1 hc]

/-! ### Approximate coarsenings and exact refinements -/

open Classical in
/-- **Exceptional mass from an energy gap along an approximate polyad map.** For polyad
decompositions `C` and `D`, any parent map `π : Polyad3 D.skeleton → Polyad3 C.skeleton` with moved
triples `M = {x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)}`, and an
energy gap `H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g`, if `0 ≤ η < δ²` and
`0 < δ` then
`H.exceptionalPolyadMass C δ r ≤ (μ + √(|κ| (g + 3 #M / N)) + 6 #M / N) / (δ² - η)`, where
`N = |V|.descFactorial 3` and `μ = H.exceptionalPolyadMass D η r`. -/
theorem exceptionalPolyadMass_le_of_polyadMap_polyadEnergy_sub_le [Fintype κ]
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (π : Polyad3 D.skeleton → Polyad3 C.skeleton) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.exceptionalPolyadMass C δ r ≤
      (H.exceptionalPolyadMass D η r +
        √(Fintype.card κ *
          (g + 3 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
            (Fintype.card V).descFactorial 3)) +
        6 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
          (Fintype.card V).descFactorial 3) / (δ ^ 2 - η) := by
  refine (exceptionalPolyadMass_le_of_polyadMap_target_le hC hD π
    (fun P c ↦ H.relativeDensity c P) (k := 1)
    (β := √(Fintype.card κ *
      (g + 3 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
        (Fintype.card V).descFactorial 3)))
    (cM := 4) zero_le_one (Real.sqrt_nonneg _) (by positivity)
    (by
      have h := sum_card_support_mul_sum_abs_relativeDensity_polyadMap_le π hgap
      rw [filter_congr_decidable univ
        (fun x ↦ Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x))] at h
      exact h) hηδ
    fun P hP ↦ isTopRegularOverPolyad_of_sum_polyadMap_le (θ := δ ^ 2 - η) π hη hδ
      (add_sub_cancel η (δ ^ 2)).le fun c ↦ by
        rw [filter_congr_decidable univ (fun Q ↦ π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r),
          filter_congr_decidable univ (fun Q ↦ π Q = P),
          filter_congr_decidable univ
            (fun x ↦ Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x))]
        simpa only [one_mul, ← add_assoc] using hP c).trans_eq (by ring)

open Classical in
/-- **Top regularity over most coarse polyads along an approximate polyad map.**
`TopRegularOverMostPolyads` form of
`Colored3Graph.exceptionalPolyadMass_le_of_polyadMap_polyadEnergy_sub_le`. -/
theorem TopRegularOverMostPolyads.of_polyadMap_polyadEnergy_sub_le [Fintype κ] {μ : ℝ}
    (h : H.TopRegularOverMostPolyads D η μ r)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (π : Polyad3 D.skeleton → Polyad3 C.skeleton) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.TopRegularOverMostPolyads C δ
      ((μ +
        √(Fintype.card κ *
          (g + 3 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
            (Fintype.card V).descFactorial 3)) +
        6 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
          (Fintype.card V).descFactorial 3) / (δ ^ 2 - η)) r := by
  refine topRegularOverMostPolyads_iff.2
    ((exceptionalPolyadMass_le_of_polyadMap_polyadEnergy_sub_le hC hD π hgap hη hδ hηδ).trans ?_)
  exact div_le_div_of_nonneg_right (by linarith [topRegularOverMostPolyads_iff.1 h])
    (sub_pos.2 hηδ).le

/-- **Exceptional mass from an energy gap under an approximate coarsening.** Specializes
`Colored3Graph.exceptionalPolyadMass_le_of_polyadMap_polyadEnergy_sub_le` to `Polyad3.coarsen hV f`,
bounding the moved triples by `3 #E |V|` where
`E = {p | C.skeleton.pairColors.color p ≠ f (D.skeleton.pairColors.color p)}`. -/
theorem exceptionalPolyadMass_le_of_vertexPart_le_of_polyadEnergy_sub_le [Fintype κ]
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.exceptionalPolyadMass C δ r ≤
      (H.exceptionalPolyadMass D η r +
        √(Fintype.card κ *
          (g + 9 * #{p | C.skeleton.pairColors.color p ≠ f (D.skeleton.pairColors.color p)} *
            Fintype.card V / (Fintype.card V).descFactorial 3)) +
        18 * #{p | C.skeleton.pairColors.color p ≠ f (D.skeleton.pairColors.color p)} *
          Fintype.card V / (Fintype.card V).descFactorial 3) / (δ ^ 2 - η) := by
  refine (exceptionalPolyadMass_le_of_polyadMap_polyadEnergy_sub_le hC hD
    (fun Q : Polyad3 D.skeleton ↦ Q.coarsen hV f) hgap hη hδ hηδ).trans ?_
  have hm : (#{x | Polyad3.ofTriple C.skeleton x ≠
      (Polyad3.ofTriple D.skeleton x).coarsen hV f} : ℝ) ≤
      3 * #{p | C.skeleton.pairColors.color p ≠ f (D.skeleton.pairColors.color p)} *
        Fintype.card V :=
    mod_cast Polyad3.card_filter_ofTriple_ne_coarsen_ofTriple_le hV f
  refine div_le_div_of_nonneg_right (add_le_add (add_le_add le_rfl ?_) ?_) (sub_pos.2 hηδ).le
  · refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (Nat.cast_nonneg _))
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- **Top regularity over most coarse polyads under an approximate coarsening.**
`TopRegularOverMostPolyads` form of
`Colored3Graph.exceptionalPolyadMass_le_of_vertexPart_le_of_polyadEnergy_sub_le`. -/
theorem TopRegularOverMostPolyads.of_vertexPart_le_of_polyadEnergy_sub_le [Fintype κ] {μ : ℝ}
    (h : H.TopRegularOverMostPolyads D η μ r)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.TopRegularOverMostPolyads C δ
      ((μ +
        √(Fintype.card κ *
          (g + 9 * #{p | C.skeleton.pairColors.color p ≠ f (D.skeleton.pairColors.color p)} *
            Fintype.card V / (Fintype.card V).descFactorial 3)) +
        18 * #{p | C.skeleton.pairColors.color p ≠ f (D.skeleton.pairColors.color p)} *
          Fintype.card V / (Fintype.card V).descFactorial 3) / (δ ^ 2 - η)) r := by
  refine topRegularOverMostPolyads_iff.2
    ((exceptionalPolyadMass_le_of_vertexPart_le_of_polyadEnergy_sub_le
      hC hD hV f hgap hη hδ hηδ).trans ?_)
  exact div_le_div_of_nonneg_right (by linarith [topRegularOverMostPolyads_iff.1 h])
    (sub_pos.2 hηδ).le

/-- **Exceptional mass from an energy gap.** Let the skeleton of `D` refine that of `C` along the
color map `f`, both selecting polyad decompositions, and let the polyad energy gap of `H` between
them be at most `g`. If `0 ≤ η < δ²` and `0 < δ`, the proportion of the support carried by the
coarse polyads over which `H` is not `(δ, r)`-top-regular is at most
`(μ + √(q g)) / (δ² - η)`, where `μ` is the corresponding fine proportion at `(η, r)` and `q` is
the number of top colors. -/
theorem exceptionalPolyadMass_le_of_polyadEnergy_sub_le [Fintype κ]
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p)) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.exceptionalPolyadMass C δ r ≤
      (H.exceptionalPolyadMass D η r + √(Fintype.card κ * g)) / (δ ^ 2 - η) := by
  have hE : ({p | C.skeleton.pairColors.color p ≠ f (D.skeleton.pairColors.color p)} :
      Finset _) = ∅ := by
    ext p
    simp [hf p]
  refine (exceptionalPolyadMass_le_of_vertexPart_le_of_polyadEnergy_sub_le
    hC hD hV f hgap hη hδ hηδ).trans_eq ?_
  simp [hE]

/-- **Top regularity over most coarse polyads.** If `H` is `(η, r)`-top-regular over all fine
polyads of `D` outside a `μ`-proportion of the support, and the polyad energy gap between the
skeletons of `D` and of the coarser `C` is at most `g`, then for `0 ≤ η < δ²` and `0 < δ`, `H` is
`(δ, r)`-top-regular over all coarse polyads outside a `(μ + √(q g)) / (δ² - η)`-proportion, where
`q` is the number of top colors. -/
theorem TopRegularOverMostPolyads.of_polyadEnergy_sub_le [Fintype κ] {μ : ℝ}
    (h : H.TopRegularOverMostPolyads D η μ r)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p)) {g : ℝ}
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.TopRegularOverMostPolyads C δ ((μ + √(Fintype.card κ * g)) / (δ ^ 2 - η)) r := by
  refine topRegularOverMostPolyads_iff.2
    ((exceptionalPolyadMass_le_of_polyadEnergy_sub_le hC hD hV f hf hgap hη hδ hηδ).trans ?_)
  exact div_le_div_of_nonneg_right (by linarith [topRegularOverMostPolyads_iff.1 h])
    (sub_pos.2 hηδ).le

end Colored3Graph

/-! ### Scheduled-rank calibration -/

/-- Fine top-regularity tolerance for scheduled-rank energy-gap transfer at coarse tolerance `δ`. -/
noncomputable def topRegularFineTolerance (δ : ℝ) : ℝ :=
  δ ^ 2 / 2

/-- Unfolding lemma for `TauCeti.topRegularFineTolerance`. -/
theorem topRegularFineTolerance_def (δ : ℝ) :
    topRegularFineTolerance δ = δ ^ 2 / 2 :=
  (rfl)

/-- For positive `δ`, `topRegularFineTolerance δ` is positive. -/
theorem topRegularFineTolerance_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < topRegularFineTolerance δ := by
  rw [topRegularFineTolerance_def]
  positivity

/-- Fine exceptional-mass bound for scheduled-rank energy-gap transfer at coarse tolerance `δ` and
exceptional proportion `ε`. -/
noncomputable def topRegularFineProportion (δ ε : ℝ) : ℝ :=
  ε * topRegularFineTolerance δ / 2

/-- Unfolding lemma for `TauCeti.topRegularFineProportion`. -/
theorem topRegularFineProportion_def (δ ε : ℝ) :
    topRegularFineProportion δ ε = ε * topRegularFineTolerance δ / 2 :=
  (rfl)

/-- For positive `δ` and `ε`, `topRegularFineProportion δ ε` is positive. -/
theorem topRegularFineProportion_pos {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    0 < topRegularFineProportion δ ε := by
  rw [topRegularFineProportion_def]
  have := topRegularFineTolerance_pos hδ
  positivity

/-- Calibrated polyad energy-gap threshold for scheduled-rank regularity transfer with `q` top
colors, coarse tolerance `δ`, and exceptional proportion `ε`. -/
noncomputable def topRegularEnergyGap (q : ℕ) (δ ε : ℝ) : ℝ :=
  (topRegularFineProportion δ ε / (q + 1)) ^ 2

/-- Unfolding lemma for `TauCeti.topRegularEnergyGap`. -/
theorem topRegularEnergyGap_def (q : ℕ) (δ ε : ℝ) :
    topRegularEnergyGap q δ ε = (topRegularFineProportion δ ε / (q + 1)) ^ 2 :=
  (rfl)

/-- For positive `δ` and `ε`, `topRegularEnergyGap q δ ε` is positive. -/
theorem topRegularEnergyGap_pos (q : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    0 < topRegularEnergyGap q δ ε := by
  rw [topRegularEnergyGap_def]
  have := topRegularFineProportion_pos hδ hε
  positivity

namespace Colored3Graph

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]
  {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {δ : ℝ} {r : ℕ}

/-- **Scheduled-rank energy-gap regularity transfer.** Specializes
`TopRegularOverMostPolyads.of_polyadEnergy_sub_le` to fine parameters
`topRegularFineTolerance δ` and `topRegularFineProportion δ ε` across an energy gap at most
`topRegularEnergyGap (Nat.card κ) δ ε`, yielding `(δ, r)`-top regularity outside an `ε`-proportion
of the injective triples. -/
theorem TopRegularOverMostPolyads.of_polyadEnergy_sub_le_topRegularEnergyGap [Fintype κ] {δ ε : ℝ}
    (h : H.TopRegularOverMostPolyads D (topRegularFineTolerance δ)
      (topRegularFineProportion δ ε) r)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤
      topRegularEnergyGap (Nat.card κ) δ ε)
    (hδ : 0 < δ) :
    H.TopRegularOverMostPolyads C δ ε r := by
  rw [topRegularEnergyGap_def] at hgap
  set q : ℝ := (Nat.card κ : ℝ)
  set γ := topRegularFineProportion δ ε / (q + 1)
  have hγ : 0 ≤ γ := div_nonneg h.nonneg (by positivity)
  have hη : topRegularFineTolerance δ < δ ^ 2 := by
    rw [topRegularFineTolerance_def]
    linarith [pow_pos hδ 2]
  have hreg := h.of_polyadEnergy_sub_le hC hD hV f hf hgap
    (topRegularFineTolerance_pos hδ).le hδ hη
  refine hreg.mono le_rfl ?_ le_rfl
  -- The exceptional proportion is at most `(ε δ² / 4 + √(q γ²)) / (δ² / 2) ≤ ε`.
  rw [← Nat.card_eq_fintype_card, div_le_iff₀ (sub_pos.2 hη)]
  have hsqrt : √(q * γ ^ 2) ≤ q * γ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hγ]
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_self_iff.2
        ((em (Nat.card κ = 0)).imp Nat.cast_eq_zero.2 Nat.one_le_cast_iff_ne_zero.2))
      hγ
  have hqγ : q * γ ≤ topRegularFineProportion δ ε := by
    dsimp only [γ]
    rw [mul_div_left_comm]
    exact mul_le_of_le_one_right h.nonneg
      ((div_le_one₀ (by positivity)).2 (le_add_of_nonneg_right zero_le_one))
  rw [topRegularFineProportion_def, topRegularFineTolerance_def] at hqγ ⊢
  linarith

/-! ### Reference density targets -/

variable {η : ℝ}

open Classical in
/-- **Exceptional mass from matching a coarse reference density target.** Let `C` and `D` be polyad
decompositions, let `π : Polyad3 D.skeleton → Polyad3 C.skeleton` assign coarse parents, and let
`a : Polyad3 C.skeleton → κ → ℝ` be a reference target. If the support-weighted `L¹` deviation of
`H.relativeDensity · Q` from `a (π Q)` summed over all fine polyads and colors is at most `β N`
(where `N = |V|.descFactorial 3` and `0 ≤ β`), then for `0 ≤ η < δ²` and `0 < δ`,
`H.exceptionalPolyadMass C δ r ≤ (H.exceptionalPolyadMass D η r + 2 β + 4 #M / N) / (δ² - η)`. -/
theorem exceptionalPolyadMass_le_of_sum_abs_relativeDensity_sub_le [Fintype κ]
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (π : Polyad3 D.skeleton → Polyad3 C.skeleton)
    {a : Polyad3 C.skeleton → κ → ℝ}
    {β : ℝ} (hβ : 0 ≤ β)
    (hdev : ∑ Q : Polyad3 D.skeleton, #Q.support * ∑ c,
        |(H.relativeDensity c Q : ℝ) - a (π Q) c| ≤ β * (Fintype.card V).descFactorial 3)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.exceptionalPolyadMass C δ r ≤
      (H.exceptionalPolyadMass D η r + 2 * β +
        4 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
          (Fintype.card V).descFactorial 3) / (δ ^ 2 - η) := by
  refine (exceptionalPolyadMass_le_of_polyadMap_target_le hC hD π a (k := 2)
    (β := β) (cM := 0) zero_le_two hβ le_rfl (by simpa using hdev) hηδ
    fun P hP ↦ isTopRegularOverPolyad_of_sum_abs_relativeDensity_sub_le (a := a P)
      (θ := δ ^ 2 - η) π hη hδ (add_sub_cancel η (δ ^ 2)).le fun c ↦ by
        rw [filter_congr_decidable univ (fun Q ↦ π Q = P ∧ ¬H.IsTopRegularOverPolyad Q η r),
          filter_congr_decidable univ (fun Q ↦ π Q = P),
          filter_congr_decidable univ
            (fun x ↦ Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x))]
        simpa only [mul_add, ← add_assoc] using hP c).trans_eq (by ring)

open Classical in
/-- **Top regularity over most coarse polyads from a reference density target.**
`TopRegularOverMostPolyads` form of
`Colored3Graph.exceptionalPolyadMass_le_of_sum_abs_relativeDensity_sub_le`. -/
theorem TopRegularOverMostPolyads.of_sum_abs_relativeDensity_sub_le [Fintype κ] {μ : ℝ}
    (h : H.TopRegularOverMostPolyads D η μ r)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (π : Polyad3 D.skeleton → Polyad3 C.skeleton)
    {a : Polyad3 C.skeleton → κ → ℝ}
    {β : ℝ} (hβ : 0 ≤ β)
    (hdev : ∑ Q : Polyad3 D.skeleton, #Q.support * ∑ c,
        |(H.relativeDensity c Q : ℝ) - a (π Q) c| ≤ β * (Fintype.card V).descFactorial 3)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hηδ : η < δ ^ 2) :
    H.TopRegularOverMostPolyads C δ
      ((μ + 2 * β +
        4 * #{x | Polyad3.ofTriple C.skeleton x ≠ π (Polyad3.ofTriple D.skeleton x)} /
          (Fintype.card V).descFactorial 3) / (δ ^ 2 - η)) r := by
  refine topRegularOverMostPolyads_iff.2
    ((exceptionalPolyadMass_le_of_sum_abs_relativeDensity_sub_le hC hD π hβ hdev
      hη hδ hηδ).trans ?_)
  exact div_le_div_of_nonneg_right (by linarith [topRegularOverMostPolyads_iff.1 h])
    (sub_pos.2 hηδ).le

end Colored3Graph

end TauCeti
