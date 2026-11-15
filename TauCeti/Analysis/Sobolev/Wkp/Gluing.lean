/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Sobolev.W1p.Gluing
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Gluing
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.Sets.Opens

/-!
# Gluing arbitrary-order Sobolev functions along finite open covers

Let `V i` be a finite family of open sets covering an open set `Ω`. Sobolev functions
`w i ∈ W^{k,p}(V i)` whose values agree almost everywhere with one function `u` come from a
single `v ∈ W^{k,p}(Ω)` with value `u`, which restricts to `w i` on each `V i` and satisfies
`‖v‖ ≤ ∑ᵢ ‖w i‖` (`TauCeti.Wkp.exists_glue`). Equivalently, a family whose restrictions agree on
the pairwise intersections glues (`TauCeti.Wkp.exists_glue_of_restrictL_eq`). The glued function
is unique, since a Sobolev function on `Ω` is determined by its restrictions to the members of any
open cover (`TauCeti.Wkp.ext_of_restrictL_eq`).

These are the statements used to pass between a Sobolev function on a domain and its restrictions
to the charts of a finite atlas, for every order `k` and every `1 ≤ p ≤ ∞`. No boundary
regularity of the sets is used.

The weak derivatives are glued at each order with `TauCeti.exists_hasWeakFDerivOn_iSup`, and the
norm bound comes from gluing `Lᵖ` classes along a finite cover
(`MeasureTheory.Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion`), which rests on subadditivity of
`eLpNorm` over a finite union (`MeasureTheory.eLpNorm_restrict_biUnion_finset_le`). Order one
is `TauCeti.W1p.exists_glue`. Above order one the norm is the Euclidean product of the
lower-order norm and the highest-derivative norm, and the bound uses the triangle inequality in
the plane (`Real.sqrt_sum_sq_add_sum_sq_le_sum_sqrt`).

## Main results

* `TauCeti.Wkp.exists_glue`: gluing along a finite open cover with prescribed value.
* `TauCeti.Wkp.exists_glue_of_restrictL_eq`: gluing compatible families along a finite open cover.
* `TauCeti.Wkp.ext_of_restrictL_eq`: restrictions to an open cover determine a Sobolev function.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1 (localization of Sobolev
  functions with a finite cover).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, §9.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*}

/-- The gluing theorem with norm bound, by induction on the order. -/
private theorem exists_glue_aux [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) : ∀ (k : ℕ) (w : ∀ i, Wkp mu (V i) p k) {u : E → ℝ},
      (∀ i, value k (w i) =ᵐ[mu.restrict (V i : Set E)] u) →
      ∃ v : Wkp mu Omega p k,
        value k v =ᵐ[mu.restrict (Omega : Set E)] u ∧ ‖v‖ ≤ ∑ i, ‖w i‖
  | 0, w, _, hw => by
      simpa only [value_zero] using
        Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion (Opens.le_iSup_iff_subset_iUnion.1 hcov) w
          fun i => by simpa only [value_zero] using hw i
  | 1, w, _, hw => by
      -- The recursively indexed order-one space and its norm are those of `W1p`, so the `W1p`
      -- glue and its norm bound are used at type `Wkp … 1` directly.
      obtain ⟨v, hv, -, hvn⟩ := W1p.exists_glue hle hcov (fun i => (w i : W1p mu (V i) p))
        fun i => by simpa only [value_one (w i)] using hw i
      exact ⟨v, by simpa only [value_one v] using hv, hvn⟩
  | k + 2, w, u, hw => by
      have hw' : ∀ i, value (k + 1) (lowerOrder (k + 1) (w i)) =ᵐ[mu.restrict (V i : Set E)] u :=
        fun i => by simpa only [value_succ] using hw i
      obtain ⟨v', hv', hv'n⟩ :=
        exists_glue_aux hle hcov (k + 1) (fun i => lowerOrder (k + 1) (w i)) hw'
      have hgi : ∀ i, iteratedGradient k v' =ᵐ[mu.restrict (V i : Set E)]
          iteratedGradient k (lowerOrder (k + 1) (w i)) := fun i => by
        rw [← restrictL_eq_of_value_ae_eq_restrict (hle i) (k + 1) hv' (hw' i)]
        exact (iteratedGradient_restrictL_ae (hle i) k v').symm
      have hloc : ∀ i, HasWeakFDerivOn mu (V i) (iteratedGradient k v')
          (iteratedGradient (k + 1) (w i)) :=
        fun i => (hasWeakFDerivOn_iteratedGradient k (w i)).congr_ae (hgi i).symm
      obtain ⟨U, hU, hUi⟩ := exists_hasWeakFDerivOn_iSup V _ hloc
      obtain ⟨D, hD, hDn⟩ := Lp.exists_ae_eq_norm_le_sum_of_subset_iUnion
        (g := fun x => (U x : IteratedGradient E (k + 1)))
        (Opens.le_iSup_iff_subset_iUnion.1 hcov) (fun i => iteratedGradient (k + 1) (w i))
        fun i => (hUi i).symm
      have hmk : HasWeakFDerivOn mu Omega (iteratedGradient k v') D :=
        (hU.mono hcov).congr_ae_deriv hD.symm
      refine ⟨mk k v' D hmk, by rw [value_mk]; exact hv', ?_⟩
      have heq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k
        (mk k v' D hmk)
      rw [lowerOrder_mk, iteratedGradient_mk] at heq
      rw [← Real.sqrt_sq (norm_nonneg (mk k v' D hmk)), heq]
      refine (Real.sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hv'n 2)
        (pow_le_pow_left₀ (norm_nonneg _) hDn 2))).trans
          ((Real.sqrt_sum_sq_add_sum_sq_le_sum_sqrt _ _ _).trans_eq
            (Finset.sum_congr rfl fun i _ => ?_))
      rw [← norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k (w i),
        Real.sqrt_sq (norm_nonneg _)]

/-- **Gluing Sobolev functions along a finite open cover.** Let the open sets `V i`, finitely
many, cover `Ω` and lie in `Ω`. If `w i ∈ W^{k,p}(V i)` has value `u` almost everywhere on `V i`
for every `i`, then some `v ∈ W^{k,p}(Ω)` has value `u` almost everywhere on `Ω`, restricts to
`w i` on each `V i`, and satisfies `‖v‖ ≤ ∑ᵢ ‖w i‖`. It is unique by
`TauCeti.Wkp.ext_of_restrictL_eq`. -/
theorem exists_glue [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (w : ∀ i, Wkp mu (V i) p k) {u : E → ℝ}
    (hw : ∀ i, value k (w i) =ᵐ[mu.restrict (V i : Set E)] u) :
    ∃ v : Wkp mu Omega p k, value k v =ᵐ[mu.restrict (Omega : Set E)] u ∧
      (∀ i, restrictL (hle i) k v = w i) ∧ ‖v‖ ≤ ∑ i, ‖w i‖ := by
  obtain ⟨v, hv, hvn⟩ := exists_glue_aux hle hcov k w hw
  exact ⟨v, hv, fun i => restrictL_eq_of_value_ae_eq_restrict (hle i) k hv (hw i), hvn⟩

/-- **Restrictions to a cover determine a Sobolev function.** Two elements of `W^{k,p}(Ω)` with
the same restrictions to the members of an open cover of `Ω` are equal. The cover may be
uncountable. -/
theorem ext_of_restrictL_eq {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) {v v' : Wkp mu Omega p k}
    (h : ∀ i, restrictL (hle i) k v = restrictL (hle i) k v') : v = v' := by
  apply ext k
  apply Lp.ext
  refine ae_restrict_of_subset_iUnion_isOpen (fun i => (V i).isOpen)
    (Opens.le_iSup_iff_subset_iUnion.1 hcov) fun i => ?_
  filter_upwards [value_restrictL_ae (hle i) k v, value_restrictL_ae (hle i) k v']
    with x h₁ h₂
  rw [← h₁, ← h₂, h i]

/-- **Gluing compatible Sobolev functions along a finite open cover.** Let the open sets `V i`,
finitely many, cover `Ω` and lie in `Ω`. If `w i ∈ W^{k,p}(V i)` and `w j` have the same
restriction to `V i ⊓ V j` for all `i` and `j`, then some `v ∈ W^{k,p}(Ω)` restricts to `w i` on
each `V i`, and `‖v‖ ≤ ∑ᵢ ‖w i‖`. -/
theorem exists_glue_of_restrictL_eq [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (w : ∀ i, Wkp mu (V i) p k)
    (hw : ∀ i j, restrictL (inf_le_left : V i ⊓ V j ≤ V i) k (w i) =
      restrictL (inf_le_right : V i ⊓ V j ≤ V j) k (w j)) :
    ∃ v : Wkp mu Omega p k, (∀ i, restrictL (hle i) k v = w i) ∧ ‖v‖ ≤ ∑ i, ‖w i‖ := by
  obtain ⟨u, hu⟩ : ∃ u : E → ℝ, ∀ i, value k (w i) =ᵐ[mu.restrict (V i : Set E)] u := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨0, fun i => isEmptyElim i⟩
    · obtain ⟨f, hf⟩ := exists_surjective_nat ι
      obtain ⟨u, hu⟩ := TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter
        (μ := mu) (L := fun n => (V (f n) : Set E)) (fun n => (V (f n)).isOpen.measurableSet)
        (a := fun n => (value k (w (f n)) : E → ℝ)) fun n m => by
          have hnm := congrArg (value k) (hw (f n) (f m))
          rw [← Opens.coe_inf]
          filter_upwards [value_restrictL_ae (inf_le_left : V (f n) ⊓ V (f m) ≤ V (f n)) k
              (w (f n)),
            value_restrictL_ae (inf_le_right : V (f n) ⊓ V (f m) ≤ V (f m)) k (w (f m))]
            with x h₁ h₂
          rw [← h₁, ← h₂, hnm]
      refine ⟨u, fun i => ?_⟩
      obtain ⟨n, rfl⟩ := hf i
      exact (hu n).symm
  obtain ⟨v, -, hv, hvn⟩ := exists_glue hle hcov k w hu
  exact ⟨v, hv, hvn⟩

end TauCeti.Wkp
