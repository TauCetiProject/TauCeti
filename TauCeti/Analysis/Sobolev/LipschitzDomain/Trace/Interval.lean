/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Slab
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
import TauCeti.LinearAlgebra.Dimension.Prod
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.OuterMeasure.AE

/-!
# The trace of a Lipschitz domain on an interval is the endpoint map

A bounded Lipschitz domain `Ω ⊆ ℝ × E` has a trace operator
`TauCeti.W1p.frontierTrace : W^{1,p}(Ω) → Lᵖ(frontier Ω, σ)`, `1 ≤ p < ∞`, for normalized
`dim E`-dimensional Euclidean Hausdorff measure `σ` on the frontier. On the real line, a
`W^{1,p}` function on an interval `(a, b)` has a continuous representative on `[a, b]`
(`TauCeti.W1p.intervalRepresentativeL`), and its endpoint values are the interval trace
`TauCeti.W1p.intervalTraceL`. This file shows that the two traces agree in dimension one.

The model space `ℝ × E` is a copy of the line exactly when `E` is the zero space, and then the
slab `{x | a < x.fst < b}` is a bounded Lipschitz domain
(`TauCeti.isLipschitzDomainWith_setOf_fst_mem_Ioo`, `TauCeti.isBounded_setOf_fst_mem_Ioo`), the
interval `(a, b)` itself. More generally, let an affine isometry `g : ℝ → ℝ × E` carry `(a, b)`
onto a bounded Lipschitz domain `Ω`. Then `frontier Ω = {g a, g b}`, surface measure is counting
measure, and for `u ∈ W^{1,p}(Ω)`, whose transfer `u ∘ g` lies in `W^{1,p}(a, b)`:

* the trace of `u` is the continuous representative of `u ∘ g` read along `g⁻¹`, almost everywhere
  on the frontier (`TauCeti.W1p.frontierTrace_ae_eq_intervalRepresentativeL`);
* its values at the two frontier points are the endpoint values of `u ∘ g`:
  `(T u (g a), T u (g b)) = ((u ∘ g)(a), (u ∘ g)(b))`, which is the interval trace
  (`TauCeti.W1p.frontierTrace_apply_eq_intervalTraceL`).

For the slab over the zero space, with `g t = (t, 0)`, this reads: the trace of `u` at `(a, 0)` and
`(b, 0)` is the interval trace of `t ↦ u (t, 0)`
(`TauCeti.W1p.frontierTrace_apply_toLp_eq_intervalTraceL`).

The argument is that `u` itself has a representative continuous on all of `ℝ × E`, the
continuous representative of `u ∘ g` composed with `g⁻¹` and with the projection onto `[a, b]`.
The trace of a function continuous up to the boundary is its boundary restriction
(`TauCeti.W1p.frontierTrace_ae_eq_of_continuousOn`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5, Theorem 1 (the trace operator).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 8.2 (continuous representatives on an interval).
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {a b : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A Sobolev function on a rigid copy `g '' (a, b)` of an interval agrees almost everywhere with
the continuous representative of `u ∘ g`, read along `g⁻¹` and extended past the endpoints by
the projection onto `[a, b]`. -/
private theorem W1p.value_ae_eq_intervalRepresentativeL_comp (hab : a < b)
    (g : ℝ ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (hg : Ioo a b = g ⁻¹' Ω) (u : W1p volume Ω p) :
    W1p.value u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
      fun x => W1p.intervalRepresentativeL hab
        (W1p.compAffineIsometryEquivL (U := ⟨Ioo a b, isOpen_Ioo⟩) g hg u)
        (projIcc a b hab.le (g.symm x)) := by
  have hΩ : (Ω : Set (WithLp 2 (ℝ × E))) = g.symm ⁻¹' Ioo a b := by
    ext x
    rw [mem_preimage, hg, mem_preimage, g.apply_symm_apply]
  have hmp : MeasurePreserving g.symm (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))
      (volume.restrict (Ioo a b)) := by
    rw [hΩ]
    exact g.symm.measurePreserving.restrict_preimage measurableSet_Ioo
  -- Undo the change of variables: `u = (u ∘ g) ∘ g⁻¹`.
  conv_lhs => rw [← W1p.compAffineIsometryEquivL_symm_compAffineIsometryEquivL
    (U := ⟨Ioo a b, isOpen_Ioo⟩) g hg hΩ u]
  exact (W1p.value_compAffineIsometryEquivL_ae (V := ⟨Ioo a b, isOpen_Ioo⟩) g.symm hΩ _).trans
    (hmp.quasiMeasurePreserving.ae_eq_comp (W1p.value_ae_eq_intervalRepresentativeL hab _))

/-- **The trace on a rigid copy of an interval is read off the continuous representative.** Let
an affine isometry `g : ℝ → ℝ × E` carry the interval `(a, b)` onto a bounded Lipschitz domain
`Ω`, and let `1 ≤ p < ∞`. For `u ∈ W^{1,p}(Ω)`, the trace of `u` is, almost everywhere on the
frontier, the continuous representative of `u ∘ g ∈ W^{1,p}(a, b)` at `g⁻¹ x ∈ {a, b}`. -/
theorem W1p.frontierTrace_ae_eq_intervalRepresentativeL (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (hab : a < b)
    (g : ℝ ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (hg : Ioo a b = g ⁻¹' Ω) (u : W1p volume Ω p) :
    W1p.frontierTrace hp hΩ hb u =ᵐ[(μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E))))]
      fun x => W1p.intervalRepresentativeL hab
        (W1p.compAffineIsometryEquivL (U := ⟨Ioo a b, isOpen_Ioo⟩) g hg u)
        (projIcc a b hab.le (g.symm x)) :=
  W1p.frontierTrace_ae_eq_of_continuousOn hp hΩ hb
    ((W1p.continuous_intervalRepresentativeL_projIcc hab _).comp g.symm.continuous).continuousOn
    (W1p.value_ae_eq_intervalRepresentativeL_comp hab g hg u)

/-- **The trace on a rigid copy of an interval is the endpoint map.** Let an affine isometry
`g : ℝ → ℝ × E` carry the interval `(a, b)` onto a bounded Lipschitz domain `Ω`, and let
`1 ≤ p < ∞`. Then `E` is the zero space, the frontier of `Ω` is the pair of points `{g a, g b}`,
each of surface measure `1`, and for `u ∈ W^{1,p}(Ω)` the values of the trace of `u` there are the
endpoint values of `u ∘ g ∈ W^{1,p}(a, b)`: the pair `(T u (g a), T u (g b))` is the interval
trace of `u ∘ g`. These values do not depend on the representative of the trace. -/
theorem W1p.frontierTrace_apply_eq_intervalTraceL (hp : p ≠ (∞ : ℝ≥0∞))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : Bornology.IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (hab : a < b)
    (g : ℝ ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (hg : Ioo a b = g ⁻¹' Ω) (u : W1p volume Ω p) :
    (W1p.frontierTrace hp hΩ hb u (g a), W1p.frontierTrace hp hΩ hb u (g b)) =
      W1p.intervalTraceL hab
        (W1p.compAffineIsometryEquivL (U := ⟨Ioo a b, isOpen_Ioo⟩) g hg u) := by
  have hfrontier : frontier (Ω : Set (WithLp 2 (ℝ × E))) = {g a, g b} := by
    rw [← image_preimage_eq (Ω : Set (WithLp 2 (ℝ × E))) g.surjective, ← hg,
      ← g.coe_toHomeomorph, ← Homeomorph.image_frontier, frontier_Ioo hab, image_pair]
  -- Surface measure is counting measure, so the two frontier points are atoms of mass `1`.
  have hatom (t : ℝ) (ht : t = a ∨ t = b) :
      W1p.frontierTrace hp hΩ hb u (g t) = W1p.intervalRepresentativeL hab
        (W1p.compAffineIsometryEquivL (U := ⟨Ioo a b, isOpen_Ioo⟩) g hg u)
        (projIcc a b hab.le t) := by
    have hmem : g t ∈ frontier (Ω : Set (WithLp 2 (ℝ × E))) := by
      rw [hfrontier]
      rcases ht with rfl | rfl <;> simp
    have hpos : (μHE[finrank ℝ E] : Measure (WithLp 2 (ℝ × E))).restrict
        (frontier (Ω : Set (WithLp 2 (ℝ × E)))) {g t} ≠ 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton _),
        singleton_inter_of_mem hmem,
        -- `ℝ × E` is a copy of the line `ℝ` only when `E` is the zero space.
        (g.linearIsometryEquiv.toLinearEquiv.trans
          (WithLp.linearEquiv 2 ℝ (ℝ × E))).finrank_eq_zero_of_self_prod,
        Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
      exact one_ne_zero
    simpa only [g.symm_apply_apply] using (W1p.frontierTrace_ae_eq_intervalRepresentativeL hp hΩ
      hb hab g hg u).self_of_ae_of_measure_singleton_ne_zero hpos
  rw [hatom a (.inl rfl), hatom b (.inr rfl), W1p.intervalTraceL_apply,
    projIcc_left, projIcc_right]

/-- **The trace of the interval `(a, b)` is its endpoint map.** Over the zero space `E`, the slab
`{x | a < x.fst < b}` of `ℝ × E` is the interval `(a, b)`, a bounded Lipschitz domain. For
`1 ≤ p < ∞` and `u` in `W^{1,p}` of the slab, the values of the trace of `u` at the two frontier
points `(a, 0)` and `(b, 0)` are the endpoint values of `t ↦ u (t, 0)`, its interval trace. -/
theorem W1p.frontierTrace_apply_toLp_eq_intervalTraceL [Unique E] (hp : p ≠ (∞ : ℝ≥0∞))
    (hab : a < b) (u : W1p volume ⟨{x : WithLp 2 (ℝ × E) | x.fst ∈ Ioo a b},
      isOpen_setOf_fst_mem_Ioo⟩ p) :
    (W1p.frontierTrace hp (isLipschitzDomainWith_setOf_fst_mem_Ioo hab)
        isBounded_setOf_fst_mem_Ioo u (WithLp.toLp 2 (a, 0)),
      W1p.frontierTrace hp (isLipschitzDomainWith_setOf_fst_mem_Ioo hab)
        isBounded_setOf_fst_mem_Ioo u (WithLp.toLp 2 (b, 0))) =
      W1p.intervalTraceL hab (W1p.compAffineIsometryEquivL (U := ⟨Ioo a b, isOpen_Ioo⟩)
        (LinearIsometryEquiv.withLpProdUnique 2 ℝ ℝ E).symm.toAffineIsometryEquiv
        withLpProdUnique_symm_preimage_setOf_fst_mem_Ioo.symm u) := by
  have h := W1p.frontierTrace_apply_eq_intervalTraceL hp
    (isLipschitzDomainWith_setOf_fst_mem_Ioo hab) isBounded_setOf_fst_mem_Ioo hab
    (LinearIsometryEquiv.withLpProdUnique 2 ℝ ℝ E).symm.toAffineIsometryEquiv
    withLpProdUnique_symm_preimage_setOf_fst_mem_Ioo.symm u
  rwa [LinearIsometryEquiv.coe_toAffineIsometryEquiv,
    LinearIsometryEquiv.withLpProdUnique_symm_apply,
    LinearIsometryEquiv.withLpProdUnique_symm_apply, ← Unique.eq_default 0] at h

end TauCeti
