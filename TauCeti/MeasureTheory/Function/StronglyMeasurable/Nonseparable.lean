/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Weakly zero yet non-strongly-measurable maps into nonseparable `ℓᵖ` spaces

On any space `α` equipped with a measure `μ` assigning zero mass to singletons
(`NullSingletonClass μ`), the family of single-coordinate vectors `x ↦ lp.single p x (a x)`
witnesses the necessity of the separability hypothesis in Pettis's measurability theorem:

1. For `p = 2` and a family of Hilbert spaces `G : α → Type*` over `𝕜 = ℝ` or `ℂ`, every
   continuous linear functional `ℓ : StrongDual 𝕜 (lp G 2)` is represented by a vector `g : lp G 2`
   whose support is countable and hence `μ`-null. Consequently `x ↦ ℓ (lp.single 2 x (a x))`
   vanishes `μ`-almost everywhere (`StrongDual.comp_lp_single_ae_eq_zero`).
2. For every `1 ≤ p ≤ ∞` and any family of normed groups `G : α → Type*`, if `a x ≠ 0` on a set
   `s` with `μ s ≠ 0`, then distinct values `lp.single p x (a x)` and `lp.single p y (a y)` are
   separated by `‖a x‖` (`lp.norm_le_dist_single`), so no separable subset of `lp G p` can cover
   `μ.restrict s`-almost all values of `x ↦ lp.single p x (a x)`. Hence the map is not Bochner
   `AEStronglyMeasurable` on `s` (`TauCeti.not_aestronglyMeasurable_lp_single`).

## Main declarations

* `StrongDual.comp_lp_single_ae_eq_zero`: every continuous linear functional on `lp G 2` vanishes
  almost everywhere along `x ↦ lp.single 2 x (a x)` under any atomless measure.
* `TauCeti.not_aestronglyMeasurable_lp_single`: `x ↦ lp.single p x (a x)` is not
  `AEStronglyMeasurable` on any set of positive atomless measure where `a` is nowhere zero.

## References

* B. J. Pettis, *On integration in vector spaces*, Trans. Amer. Math. Soc. **44** (1938), 277–304.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Theorem 1.1.20 (Pettis measurability theorem).
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StrongDual

/-- Under any measure `μ` on `α` assigning zero mass to singletons, every continuous linear
functional `ℓ` on the Hilbert direct sum `lp G 2` vanishes `μ`-almost everywhere along
`x ↦ lp.single 2 x (a x)`: by Riesz representation `ℓ` pairs with an `ℓ²` family whose support is
countable, hence `μ`-null. -/
theorem comp_lp_single_ae_eq_zero {α 𝕜 : Type*} [DecidableEq α] [MeasurableSpace α]
    {μ : Measure α} [NullSingletonClass μ] [RCLike 𝕜] {G : α → Type*}
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)] [∀ i, CompleteSpace (G i)]
    (ℓ : StrongDual 𝕜 (lp G 2)) (a : ∀ i, G i) :
    (fun x : α => ℓ (lp.single 2 x (a x))) =ᵐ[μ] 0 := by
  let g : lp G 2 := (InnerProductSpace.toDual 𝕜 (lp G 2)).symm ℓ
  have hval : ∀ x : α, ℓ (lp.single 2 x (a x)) = ⟪g x, a x⟫_𝕜 := fun x => by
    rw [← InnerProductSpace.toDual_symm_apply, lp.inner_single_right]
  have hsupp : {x : α | g x ≠ 0}.Countable := by
    refine ((g.prop.summable (by norm_num)).countable_support).mono fun x hx => ?_
    simp only [Function.mem_support, ne_eq]
    exact (Real.rpow_ne_zero (norm_nonneg _) (by norm_num)).2 (norm_ne_zero_iff.2 hx)
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) (hsupp.measure_zero μ)
  intro hgx
  apply hx
  simp [hval x, hgx]

end StrongDual

namespace TauCeti

/-- Under any measure `μ` assigning zero mass to singletons, if `a x ≠ 0` for all `x ∈ s` and
`μ s ≠ 0`, then the single-coordinate map `x ↦ lp.single p x (a x)` into `lp G p` (`1 ≤ p ≤ ∞`)
is not Bochner `AEStronglyMeasurable` on `s`: decomposing `s` by `1 / (n + 1) ≤ ‖a x‖`, any
separable set in the codomain contains at most countably many pairwise separated points from each
piece, whose preimage has `μ`-measure zero. -/
theorem not_aestronglyMeasurable_lp_single {α : Type*} [DecidableEq α] [MeasurableSpace α]
    {μ : Measure α} [NullSingletonClass μ] {G : α → Type*} [∀ i, NormedAddCommGroup (G i)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {a : ∀ i, G i} {s : Set α} (ha : ∀ x ∈ s, a x ≠ 0)
    (hs : μ s ≠ 0) :
    ¬ AEStronglyMeasurable (fun x : α => lp.single (E := G) p x (a x)) (μ.restrict s) := by
  intro hu
  obtain ⟨t, ⟨c, hc_count, htc⟩, hae⟩ := hu.isSeparable_ae_range
  let S : Set α := s ∩ {x : α | lp.single (E := G) p x (a x) ∈ t}
  let piece : ℕ → Set α := fun n => {x ∈ S | (1 / ((n : ℝ) + 1)) ≤ ‖a x‖}
  have hcover : S ⊆ ⋃ n : ℕ, piece n := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 (ha x hx.1))
    exact mem_iUnion.2 ⟨n, hx, hn.le⟩
  have hpiece_count : ∀ n : ℕ, (piece n).Countable := fun n => by
    let δ : ℝ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := Nat.one_div_pos_of_nat
    have hnear : ∀ x : piece n, ∃ z : c,
        dist (lp.single (E := G) p x.val (a x.val)) z.val < δ / 2 := fun x => by
      obtain ⟨z, hzc, hxz⟩ := Metric.mem_closure_iff.1 (htc x.property.1.2) (δ / 2) (half_pos hδ)
      exact ⟨⟨z, hzc⟩, hxz⟩
    choose f hf using hnear
    have hfinj : Function.Injective f := by
      intro x y hxy
      by_contra hne
      have hsep : δ ≤ dist (lp.single (E := G) p x.val (a x.val))
          (lp.single (E := G) p y.val (a y.val)) :=
        x.property.2.trans (lp.norm_le_dist_single (Subtype.coe_ne_coe.2 hne) (a x.val) (a y.val))
      have hlt : dist (lp.single (E := G) p x.val (a x.val))
          (lp.single (E := G) p y.val (a y.val)) < δ := by
        calc dist (lp.single (E := G) p x.val (a x.val)) (lp.single (E := G) p y.val (a y.val))
            ≤ dist (lp.single (E := G) p x.val (a x.val)) (f x).val +
                dist (lp.single (E := G) p y.val (a y.val)) (f x).val := dist_triangle_right _ _ _
          _ = dist (lp.single (E := G) p x.val (a x.val)) (f x).val +
                dist (lp.single (E := G) p y.val (a y.val)) (f y).val := by rw [hxy]
          _ < δ / 2 + δ / 2 := add_lt_add (hf x) (hf y)
          _ = δ := add_halves δ
      exact hsep.not_gt hlt
    have : Countable c := hc_count.to_subtype
    exact Set.countable_coe_iff.1 (Function.Injective.countable hfinj)
  have hS_count : S.Countable := (countable_iUnion hpiece_count).mono hcover
  have hS_zero : (μ.restrict s) S = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le s S).trans (hS_count.measure_zero μ).le)
  have hTc_zero : (μ.restrict s) {x : α | lp.single (E := G) p x (a x) ∈ t}ᶜ = 0 := ae_iff.1 hae
  have h_univ : (μ.restrict s) univ = 0 := nonpos_iff_eq_zero.1 <| by
    calc (μ.restrict s) univ
        = (μ.restrict s) s := by rw [Measure.restrict_apply_univ, Measure.restrict_apply_self]
      _ ≤ (μ.restrict s) (S ∪ {x : α | lp.single (E := G) p x (a x) ∈ t}ᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases ht : lp.single (E := G) p x (a x) ∈ t
          · exact Or.inl ⟨hx, ht⟩
          · exact Or.inr ht
      _ ≤ (μ.restrict s) S + (μ.restrict s) {x : α | lp.single (E := G) p x (a x) ∈ t}ᶜ :=
          measure_union_le _ _
      _ = 0 := by simp [hS_zero, hTc_zero]
  rw [Measure.restrict_apply_univ] at h_univ
  exact hs h_univ

end TauCeti
