/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Homomorphism densities of the smallest graphs

The edge and triangle densities have the familiar integral formulas:

```text
t(K₂, W) = ∫∫ W(x, y)                              the edge density
t(K₃, W) = ∫∫∫ W(x, y) W(x, z) W(y, z)             the triangle density
```

Each is given as both a product-measure integral and an iterated integral. The four-cycle density
is an integral over `(Ω × Ω) × (Ω × Ω)`, with opposite vertices paired. This pairing makes its
integrand a product of two paths between the vertices of the first pair.

The graph-independent transports `homDensity_fin_two`, `homDensity_fin_three`, and
`homDensity_fin_four` express densities as integrals over these product spaces. The corresponding
integrability lemmas allow Fubini's theorem to turn them into iterated integrals.

The coordinate equivalences are Mathlib's `MeasurableEquiv.finTwoArrow`, together with
`TauCeti.finThreeArrow` and `TauCeti.finFourArrowPairPair` from
`TauCeti.MeasureTheory.Constructions.Pi`. The paired four-coordinate equivalence reads a vertex
assignment as `((x 0, x 2), (x 1, x 3))`.

## Main results

* `homDensity_fin_two`, `homDensity_fin_three`, `homDensity_fin_four` — the graph-independent
  transports;
* `homDensity_top_fin_two` and `homDensity_top_fin_two_eq_integral_integral` — the edge density;
* `homDensity_top_fin_three` and `homDensity_top_fin_three_eq_integral_integral_integral` — the
  triangle density;
* `homDensity_cycleGraph_four`, `integrable_cycleGraph_four` — the 4-cycle density and its
  integrability;
* `integrable_prod_edgeFactor_fin_two`, `integrable_prod_edgeFactor_fin_three`,
  `integrable_prod_edgeFactor_fin_four` — integrability of
  the transported integrand, again for an arbitrary graph;
* `integrable_edge_integrand`, `integrable_triangle_integrand` — the same for the two expanded
  integrands, so a consumer of either iterated form has the hypothesis `integral_prod` needs.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The two-vertex transport.**  For any graph on `Fin 2`, the homomorphism density is an integral
over `Ω × Ω`.  This is independent of the graph; the concrete values below only substitute an edge
set into it. -/
theorem homDensity_fin_two (F : SimpleGraph (Fin 2)) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    homDensity F W
      = ∫ p : Ω × Ω, ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2] e ∂(μ.prod μ) := by
  rw [homDensity_def]
  simpa only [MeasurableEquiv.finTwoArrow_symm_apply, Matrix.empty_eq finZeroElim,
    Matrix.Fin.cons_vecEmpty, Matrix.Fin.cons_vecCons] using
    ((measurePreserving_finTwoArrow μ).symm.integral_comp'
      (fun x : Fin 2 → Ω => ∏ e ∈ F.edgeFinset, edgeFactor W x e)).symm

/-- **The three-vertex transport.**  For any graph on `Fin 3`, the homomorphism density is an
integral over `Ω × Ω × Ω`. -/
theorem homDensity_fin_three (F : SimpleGraph (Fin 3)) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    homDensity F W
      = ∫ p : Ω × Ω × Ω, ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2.1, p.2.2] e
          ∂(μ.prod (μ.prod μ)) := by
  rw [homDensity_def]
  simpa only [finThreeArrow_symm_apply] using
    ((measurePreserving_finThreeArrow μ).symm.integral_comp'
      (fun x : Fin 3 → Ω => ∏ e ∈ F.edgeFinset, edgeFactor W x e)).symm

/-- For any graph on `Fin 2`, its edge-factor product is integrable on `Ω × Ω`. -/
theorem integrable_prod_edgeFactor_fin_two (F : SimpleGraph (Fin 2)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω => ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2] e) (μ.prod μ) := by
  simpa only [Function.comp_def, MeasurableEquiv.finTwoArrow_symm_apply,
    Matrix.empty_eq finZeroElim, Matrix.Fin.cons_vecEmpty, Matrix.Fin.cons_vecCons] using
    (measurePreserving_finTwoArrow μ).symm.integrable_comp_of_integrable
      (integrable_homDensity_integrand F W)

/-- For any graph on `Fin 3`, its edge-factor product is integrable on `Ω × Ω × Ω`. -/
theorem integrable_prod_edgeFactor_fin_three (F : SimpleGraph (Fin 3)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω => ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1, p.2.1, p.2.2] e)
      (μ.prod (μ.prod μ)) := by
  simpa only [Function.comp_def, finThreeArrow_symm_apply] using
    (measurePreserving_finThreeArrow μ).symm.integrable_comp_of_integrable
      (integrable_homDensity_integrand F W)

/-- **The four-vertex transport.**  For any graph on `Fin 4`, the homomorphism density is an
integral over two copies of `Ω × Ω`, with the coordinates paired for the four-cycle formulas. -/
theorem homDensity_fin_four (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    homDensity F W =
      ∫ p : (Ω × Ω) × (Ω × Ω),
        ∏ e ∈ F.edgeFinset,
          edgeFactor W ![p.1.1, p.2.1, p.1.2, p.2.2] e
          ∂((μ.prod μ).prod (μ.prod μ)) := by
  rw [homDensity_def]
  simpa only [finFourArrowPairPair_symm_apply] using
    ((measurePreserving_finFourArrowPairPair μ).symm.integral_comp'
      (fun x : Fin 4 → Ω => ∏ e ∈ F.edgeFinset, edgeFactor W x e)).symm

/-- **Transported integrability, four vertices.**  For any graph on `Fin 4`, the transported
integrand is integrable on the paired product space. -/
theorem integrable_prod_edgeFactor_fin_four (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    Integrable (fun p : (Ω × Ω) × (Ω × Ω) =>
      ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1.1, p.2.1, p.1.2, p.2.2] e)
      ((μ.prod μ).prod (μ.prod μ)) := by
  simpa only [Function.comp_def, finFourArrowPairPair_symm_apply] using
    (measurePreserving_finFourArrowPairPair μ).symm.integrable_comp_of_integrable
      (integrable_homDensity_integrand F W)

private theorem prod_edgeFactor_cycleGraph_four (W : Graphon Ω μ)
    (p : (Ω × Ω) × (Ω × Ω)) :
    ∏ e ∈ (SimpleGraph.cycleGraph 4).edgeFinset,
        edgeFactor W ![p.1.1, p.2.1, p.1.2, p.2.2] e =
      W p.1.1 p.2.1 * W p.2.1 p.1.2 * W p.1.2 p.2.2 * W p.2.2 p.1.1 := by
  have hedge : (SimpleGraph.cycleGraph 4).edgeFinset =
      {s(0, 1), s(0, 3), s(1, 2), s(2, 3)} := by decide
  rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [edgeFactor_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [Graphon.symm (W := W) (p.1.1) (p.2.2)]
  ring

/-- The four-cycle integrand is integrable on the paired product space. -/
theorem integrable_cycleGraph_four (W : Graphon Ω μ) :
    Integrable (fun p : (Ω × Ω) × (Ω × Ω) =>
      W p.1.1 p.2.1 * W p.2.1 p.1.2 * W p.1.2 p.2.2 * W p.2.2 p.1.1)
      ((μ.prod μ).prod (μ.prod μ)) :=
  (integrable_prod_edgeFactor_fin_four (SimpleGraph.cycleGraph 4) W).congr
    (ae_of_all _ fun p => prod_edgeFactor_cycleGraph_four W p)

/-- **The four-cycle density.**  The homomorphism density of `C₄` is the integral of its four edge
product over the paired product space. -/
theorem homDensity_cycleGraph_four (W : Graphon Ω μ) :
    homDensity (SimpleGraph.cycleGraph 4) W =
      ∫ p : (Ω × Ω) × (Ω × Ω),
        W p.1.1 p.2.1 * W p.2.1 p.1.2 * W p.1.2 p.2.2 * W p.2.2 p.1.1
          ∂((μ.prod μ).prod (μ.prod μ)) := by
  rw [homDensity_fin_four]
  exact integral_congr_ae (ae_of_all _ fun p => prod_edgeFactor_cycleGraph_four W p)

/-- The edge factor product of `K₂`, expanded.  Shared by the density value and its
integrability. -/
private theorem prod_edgeFactor_top_fin_two (W : Graphon Ω μ) (p : Ω × Ω) :
    ∏ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset, edgeFactor W ![p.1, p.2] e = W p.1 p.2 := by
  have hedge : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by decide
  rw [hedge, Finset.prod_singleton, edgeFactor_mk]
  simp

/-- The edge factor product of `K₃`, expanded.  Shared by the density value and its
integrability. -/
private theorem prod_edgeFactor_top_fin_three (W : Graphon Ω μ) (p : Ω × Ω × Ω) :
    ∏ e ∈ (⊤ : SimpleGraph (Fin 3)).edgeFinset, edgeFactor W ![p.1, p.2.1, p.2.2] e
      = W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2 := by
  have hedge : (⊤ : SimpleGraph (Fin 3)).edgeFinset = {s(0, 1), s(0, 2), s(1, 2)} := by decide
  rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [edgeFactor_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The edge integrand is integrable on `Ω × Ω`. -/
theorem integrable_edge_integrand (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω => W p.1 p.2) (μ.prod μ) :=
  (integrable_prod_edgeFactor_fin_two ⊤ W).congr
    (ae_of_all _ fun p => prod_edgeFactor_top_fin_two W p)

/-- The triangle integrand is integrable on `Ω × Ω × Ω`. -/
theorem integrable_triangle_integrand (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω => W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2)
      (μ.prod (μ.prod μ)) :=
  (integrable_prod_edgeFactor_fin_three ⊤ W).congr
    (ae_of_all _ fun p => prod_edgeFactor_top_fin_three W p)

/-- **The edge density.**  The homomorphism density of the one-edge graph `K₂` is the integral of
the graphon over the whole square. -/
theorem homDensity_top_fin_two (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W = ∫ p : Ω × Ω, W p.1 p.2 ∂(μ.prod μ) := by
  rw [homDensity_fin_two]
  exact integral_congr_ae (ae_of_all _ fun p => prod_edgeFactor_top_fin_two W p)

/-- The edge density as an iterated integral. -/
theorem homDensity_top_fin_two_eq_integral_integral (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W = ∫ x, ∫ y, W x y ∂μ ∂μ := by
  rw [homDensity_top_fin_two, integral_prod _ (integrable_edge_integrand W)]

/-- **The triangle density.**  The homomorphism density of `K₃` is the integral of the product of
the graphon over the three edges of a triple of points. -/
theorem homDensity_top_fin_three (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W
      = ∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2 ∂(μ.prod (μ.prod μ)) := by
  rw [homDensity_fin_three]
  exact integral_congr_ae (ae_of_all _ fun p => prod_edgeFactor_top_fin_three W p)

/-- The triangle density as an iterated integral. -/
theorem homDensity_top_fin_three_eq_integral_integral_integral (W : Graphon Ω μ) :
    homDensity (⊤ : SimpleGraph (Fin 3)) W = ∫ x, ∫ y, ∫ z, W x y * W x z * W y z ∂μ ∂μ ∂μ := by
  rw [homDensity_top_fin_three, integral_prod _ (integrable_triangle_integrand W)]
  refine integral_congr_ae ?_
  filter_upwards [(integrable_triangle_integrand W).prod_right_ae] with x hx
  exact integral_prod _ hx

end DenseGraphLimits

end TauCeti
