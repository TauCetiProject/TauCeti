/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Componentwise Poincaré–Wirtinger inequalities

On a disconnected domain the gradient does not control deviation from one global mean: a
function can take different constant values on different components. Instead one subtracts the
mean on each component.

For a countable disjoint open cover, a common Poincaré–Wirtinger constant on the pieces gives
exactly the same constant on their union after this componentwise normalization. This holds for
all `1 ≤ p ≤ ∞`. At finite exponents the `p`-th power integrals add; at infinity the essential
suprema combine by a supremum. In particular, on a finite disjoint union of bounded connected
Lipschitz domains, the maximum of their constants works. No separation of their closures is
required. For an infinite union the common bound on the component constants is an explicit
hypothesis, not a consequence of boundedness of the union.

The normalizing function is specified by its values on each piece. Its values outside the
union are immaterial; the construction chooses zero there. When the pieces are nonempty and
preconnected they are precisely the connected components of the union.

## Main declarations

* `TauCeti.W1p.exists_eLpNorm_sub_le_of_componentwise_poincare`: glue a uniform family of
  Poincaré–Wirtinger inequalities with no loss in the constant.
* `TauCeti.W1p.exists_componentwise_poincare_of_finite_isLipschitzDomainWith`: the inequality
  on a finite disjoint union of bounded connected Lipschitz domains.

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
  {Ω : Opens E} {ι : Type*} [Countable ι] {U : ι → Opens E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Componentwise Poincaré–Wirtinger with uniform constants.** Suppose a countable disjoint
open cover of `Ω` has a Poincaré–Wirtinger inequality with the same constant `C` on every piece.
For every `u ∈ W^{1,p}(Ω)`, subtracting its mean separately on each piece gives an `Lᵖ` bound
by `C` times the norm of its weak gradient on `Ω`, including at `p = ∞`.

The conclusion characterizes the normalizing function on the cover, without imposing any
condition on its irrelevant values outside `Ω`. -/
theorem W1p.exists_eLpNorm_sub_le_of_componentwise_poincare
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
        eLpNorm ((C : ℝ) • (W1p.gradient u : E → E)) p (mu.restrict (U i)) := by
    have hval := W1p.value_restrictL_ae (hU i) u
    have havg := average_congr hval
    have hmean : ∀ᵐ x ∂mu.restrict (U i), m x = ⨍ y in U i, W1p.value u y ∂mu :=
      (ae_restrict_mem (U i).isOpen.measurableSet).mono fun x hx ↦ hm i hx
    have heq : (fun x ↦ W1p.value u x - m x) =ᵐ[mu.restrict (U i)]
        (fun x ↦ W1p.value (W1p.restrictL (hU i) u) x -
          ⨍ y in U i, W1p.value (W1p.restrictL (hU i) u) y ∂mu) := by
      filter_upwards [hval, hmean] with x hx hmx
      rw [hx, hmx, havg]
    rw [eLpNorm_congr_ae heq, eLpNorm_const_smul, Real.eNorm_eq_ofReal C.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    have hgrad := eLpNorm_congr_ae (p := p) (W1p.gradient_restrictL_ae (hU i) u)
    rw [← hgrad, ← Lp.eNorm_def]
    exact hP i _
  have hsum : mu.restrict (Ω : Set E) = Measure.sum (fun i ↦ mu.restrict (U i : Set E)) := by
    rw [← hcover]
    exact Measure.restrict_iUnion hd fun i ↦ (U i).isOpen.measurableSet
  have h := eLpNorm_sum_measure_le_of_forall_le
    (fun i ↦ mu.restrict (U i : Set E)) hlocal
  rw [← hsum, eLpNorm_const_smul, Real.eNorm_eq_ofReal C.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ← Lp.eNorm_def] at h
  exact h

end Uniform

section Finite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Finite ι] {U : ι → Opens (WithLp 2 (ℝ × E))}
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ι → ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Poincaré–Wirtinger on finitely many components.** On a finite disjoint union of bounded
preconnected Lipschitz open sets, the gradient controls the deviation from the mean on each
piece, for every `1 ≤ p ≤ ∞`. The constant is uniform in the Sobolev function and can be chosen
as the maximum of the component constants. -/
theorem W1p.exists_componentwise_poincare_of_finite_isLipschitzDomainWith
    (hd : Pairwise (Disjoint on fun i ↦ (U i : Set (WithLp 2 (ℝ × E)))))
    (hcover : ⋃ i, (U i : Set (WithLp 2 (ℝ × E))) = Ω)
    (hL : ∀ i, (U i : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith (L i))
    (hb : ∀ i, IsBounded (U i : Set (WithLp 2 (ℝ × E))))
    (hc : ∀ i, IsPreconnected (U i : Set (WithLp 2 (ℝ × E))))
    (hne : ∀ i, Set.Nonempty (U i : Set (WithLp 2 (ℝ × E)))) :
    ∃ C : ℝ≥0, ∀ u : W1p volume Ω p, ∃ m : WithLp 2 (ℝ × E) → ℝ,
      (∀ i, EqOn m (fun _ ↦ ⨍ y in U i, W1p.value u y) (U i)) ∧
      eLpNorm (fun x ↦ W1p.value u x - m x) p (volume.restrict Ω) ≤ C * ‖W1p.gradient u‖ₑ := by
  classical
  let := Fintype.ofFinite ι
  have hP (i : ι) : ∃ C : ℝ≥0, ∀ v : W1p volume (U i) p,
      eLpNorm (fun x ↦ W1p.value v x - ⨍ y in U i, W1p.value v y)
        p (volume.restrict (U i)) ≤ C * ‖W1p.gradient v‖ₑ := by
    obtain ⟨C, hC, hP⟩ := W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith
      (p := p) (hL i) (hb i) (hc i) subset_rfl
      ((U i).isOpen.measure_pos volume (hne i)).ne'
    rw [ENNReal.ofReal_eq_coe_nnreal hC] at hP
    exact ⟨⟨C, hC⟩, hP⟩
  choose C hC using hP
  refine ⟨Finset.univ.sup C, fun u ↦
    W1p.exists_eLpNorm_sub_le_of_componentwise_poincare hd hcover _ (fun i v ↦ ?_) u⟩
  exact (hC i v).trans <| mul_le_mul_left (by
    exact_mod_cast (Finset.le_sup (f := C) (Finset.mem_univ i))) _

end Finite

end TauCeti
