/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# Componentwise Poincaré–Wirtinger inequalities

On a disconnected domain the gradient does not control deviation from one global mean: a
function can take different constant values on different components. Instead one subtracts the
mean on each component.

For a disjoint open cover, a common Poincaré–Wirtinger constant on the pieces gives
exactly the same constant on their union after this componentwise normalization. This holds for
all `1 ≤ p ≤ ∞`. At finite exponents the `p`-th power integrals add; at infinity the essential
suprema combine by a supremum. No separation of the closures of the pieces is required.
For an infinite union the common bound on the component constants is an explicit
hypothesis, not a consequence of boundedness of the union.

The normalizing function is specified by its values on each piece. Its values outside the
union are immaterial and left unconstrained by the statement. When the pieces are nonempty and
preconnected they are precisely the connected components of the union.

## Main declarations

* `TauCeti.W1p.exists_eqOn_setAverage_and_eLpNorm_value_sub_le_of_pairwise_disjoint`:
  glue a uniform family of Poincaré–Wirtinger inequalities with no loss in the constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1: the connected-domain
  Poincaré–Wirtinger inequality.
-/

public section

noncomputable section

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Function

namespace TauCeti

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Ω : Opens E} {ι : Type*} {U : ι → Opens E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Componentwise Poincaré–Wirtinger with uniform constants.** Suppose a disjoint
open cover of `Ω` has a Poincaré–Wirtinger inequality with the same constant `C` on every piece.
For every `u ∈ W^{1,p}(Ω)`, subtracting its mean separately on each piece gives an `Lᵖ` bound
by `C` times the norm of its weak gradient on `Ω`, including at `p = ∞`.

The conclusion characterizes the normalizing function on the cover, without imposing any
condition on its irrelevant values outside `Ω`. -/
theorem W1p.exists_eqOn_setAverage_and_eLpNorm_value_sub_le_of_pairwise_disjoint
    (hd : Pairwise (Disjoint on fun i ↦ (U i : Set E)))
    (hcover : ⋃ i, (U i : Set E) = Ω) (C : ℝ≥0)
    (hP : ∀ i, ∀ v : W1p mu (U i) p,
      eLpNorm (fun x ↦ W1p.value v x - ⨍ y in U i, W1p.value v y ∂mu)
        p (mu.restrict (U i)) ≤ C * ‖W1p.gradient v‖ₑ)
    (u : W1p mu Ω p) :
    ∃ m : E → ℝ,
      (∀ i, EqOn m (fun _ ↦ ⨍ y in U i, W1p.value u y ∂mu) (U i)) ∧
      eLpNorm (fun x ↦ W1p.value u x - m x) p (mu.restrict Ω) ≤ C * ‖W1p.gradient u‖ₑ := by
  classical
  let m : E → ℝ := fun x ↦ if hx : ∃ i, x ∈ U i then
    ⨍ y in U hx.choose, W1p.value u y ∂mu else 0
  have hm (i : ι) : EqOn m (fun _ ↦ ⨍ y in U i, W1p.value u y ∂mu) (U i) := by
    intro x hx
    have hex : ∃ j, x ∈ U j := ⟨i, hx⟩
    have hi : hex.choose = i := by
      by_contra hne
      exact Set.disjoint_left.1 (hd hne) hex.choose_spec hx
    simp only [m, dite_eq_left hex, hi]
  refine ⟨m, hm, ?_⟩
  have hU (i : ι) : U i ≤ Ω := fun x hx ↦
    (Set.ext_iff.1 hcover x).1 (mem_iUnion.2 ⟨i, hx⟩)
  have hlocal (i : ι) :
      eLpNorm (fun x ↦ W1p.value u x - m x) p (mu.restrict (U i)) ≤
        C * eLpNorm (W1p.gradient u : E → E) p (mu.restrict (U i)) := by
    have hval := W1p.value_restrictL_ae (hU i) u
    have havg := average_congr hval
    have hmean : ∀ᵐ x ∂mu.restrict (U i), m x = ⨍ y in U i, W1p.value u y ∂mu :=
      (ae_restrict_mem (U i).isOpen.measurableSet).mono fun x hx ↦ hm i hx
    have heq : (fun x ↦ W1p.value u x - m x) =ᵐ[mu.restrict (U i)]
        (fun x ↦ W1p.value (W1p.restrictL (hU i) u) x -
          ⨍ y in U i, W1p.value (W1p.restrictL (hU i) u) y ∂mu) := by
      filter_upwards [hval, hmean] with x hx hmx
      rw [hx, hmx, havg]
    rw [eLpNorm_congr_ae heq]
    have hgrad := eLpNorm_congr_ae (p := p) (W1p.gradient_restrictL_ae (hU i) u)
    rw [← hgrad, ← Lp.eNorm_def]
    exact hP i _
  let ι' := {i : ι // (U i : Set E).Nonempty}
  have hd' : Pairwise (Disjoint on fun i : ι' ↦ (U i : Set E)) :=
    fun i j hij ↦ hd (Subtype.coe_ne_coe.2 hij)
  have : Countable ι' := hd'.countable_of_isOpen_disjoint
    (fun i ↦ (U i).isOpen) (fun i ↦ i.property)
  have hcover' : ⋃ i : ι', (U i : Set E) = Ω := by
    rw [← hcover]
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, hi⟩, fun ⟨i, hi⟩ ↦ ⟨⟨i, x, hi⟩, hi⟩⟩
  have hsum : mu.restrict (Ω : Set E) = Measure.sum (fun i : ι' ↦ mu.restrict (U i : Set E)) := by
    rw [← hcover']
    exact Measure.restrict_iUnion hd' fun i ↦ (U i).isOpen.measurableSet
  have h := eLpNorm_sum_measure_le_mul_of_forall_le
    (fun i : ι' ↦ mu.restrict (U i : Set E)) (fun i ↦ hlocal i)
  rw [← hsum, ← Lp.eNorm_def] at h
  exact h

end Uniform

end TauCeti
