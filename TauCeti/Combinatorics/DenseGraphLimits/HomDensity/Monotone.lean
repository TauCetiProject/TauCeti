/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Structural
public import Mathlib.Combinatorics.SimpleGraph.Clique
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Monotonicity of homomorphism densities

The homomorphism density `t(F, W)` is monotone in the graphon and antitone in the graph.

* **In the graphon.** If `U ≤ W` almost everywhere on `Ω × Ω`, then `t(F, U) ≤ t(F, W)`: the
  integrand is a product of nonnegative edge factors, and every edge joins two distinct vertices, so
  a `μ ⊗ μ`-null set of exceptional pairs is null for each edge factor.
* **In the graph.** Adding edges multiplies the integrand by further factors in `[0, 1]`, so
  `t(F', W) ≤ t(F, W)` whenever `F ≤ F'`. Combined with invariance under embeddings of the vertex
  type, this gives `t(F', W) ≤ t(F, W)` whenever `F` is contained in `F'` (Mathlib's `F ⊑ F'`: an
  injective homomorphism `F → F'`), on possibly different vertex types.

The containment form specializes to complete graphs: a graph containing an `n`-clique has density
at most `t(Kₙ, W)`, and a graph with at least one edge has density at most the edge density
`t(K₂, W)`.

## Main results

* `TauCeti.DenseGraphLimits.homDensity_mono_ae` — `t(F, ·)` is monotone under almost-everywhere
  comparison of graphons, and `TauCeti.DenseGraphLimits.homDensity_mono` its pointwise form;
* `TauCeti.DenseGraphLimits.homDensity_anti` — `t(·, W)` is antitone on graphs on a fixed vertex
  type;
* `TauCeti.DenseGraphLimits.homDensity_le_of_isContained` — `t(F', W) ≤ t(F, W)` when `F ⊑ F'`;
* `TauCeti.DenseGraphLimits.homDensity_le_homDensity_top_of_not_cliqueFree` and
  `TauCeti.DenseGraphLimits.homDensity_le_homDensity_top_fin_two` — the clique and edge bounds.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §7.2.
-/

public section

noncomputable section

open MeasureTheory SimpleGraph

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {V V' : Type*} [Fintype V] [Fintype V']

/-- **Monotonicity in the graphon.** If `U ≤ W` almost everywhere on `Ω × Ω`, then
`t(F, U) ≤ t(F, W)` for every finite graph `F`. -/
theorem homDensity_mono_ae {F : SimpleGraph V} [DecidableRel F.Adj] {U W : Graphon Ω μ}
    (h : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 ≤ W p.1 p.2) :
    homDensity F U ≤ homDensity F W := by
  -- Each edge joins two distinct vertices, so its two coordinates have joint law `μ ⊗ μ`.
  have hedge : ∀ e ∈ F.edgeFinset, ∀ᵐ x ∂(Measure.pi fun _ : V => μ),
      edgeFactor U x e ≤ edgeFactor W x e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      have hab : a ≠ b := F.ne_of_adj (by simpa using he)
      simpa using
        (TauCeti.measurePreserving_eval_pair (fun _ : V => μ) hab).quasiMeasurePreserving.ae h
  rw [homDensity_def, homDensity_def]
  refine integral_mono_ae (integrable_homDensity_integrand F U)
    (integrable_homDensity_integrand F W)
    (((Filter.eventually_all_finset _).2 hedge).mono fun x hx => ?_)
  exact Finset.prod_le_prod₀ (fun e _ => edgeFactor_nonneg U x e) hx

/-- **Monotonicity in the graphon, pointwise form.** If `U ≤ W` everywhere, then
`t(F, U) ≤ t(F, W)` for every finite graph `F`. -/
theorem homDensity_mono {F : SimpleGraph V} [DecidableRel F.Adj] {U W : Graphon Ω μ}
    (h : ∀ x y, U x y ≤ W x y) : homDensity F U ≤ homDensity F W :=
  homDensity_mono_ae (Filter.Eventually.of_forall fun p => h p.1 p.2)

/-- **Antitonicity in the graph.** Adding edges can only lower a homomorphism density: if `F ≤ F'`
on the same vertex type, then `t(F', W) ≤ t(F, W)`. -/
theorem homDensity_anti (W : Graphon Ω μ) {F F' : SimpleGraph V} [DecidableRel F.Adj]
    [DecidableRel F'.Adj] (h : F ≤ F') : homDensity F' W ≤ homDensity F W := by
  rw [homDensity_def, homDensity_def]
  refine integral_mono (integrable_homDensity_integrand F' W)
    (integrable_homDensity_integrand F W) fun x => ?_
  exact Finset.prod_le_prod_of_subset_of_le_one₀ (edgeFinset_subset_edgeFinset.2 h)
    (fun e _ => edgeFactor_nonneg W x e) fun e _ _ => edgeFactor_le_one W x e

/-- **Antitonicity under containment.** If `F` is contained in `F'`, meaning that there is an
injective graph homomorphism `F → F'`, then `t(F', W) ≤ t(F, W)`. The two graphs may live on
different vertex types. -/
theorem homDensity_le_of_isContained (W : Graphon Ω μ) {F : SimpleGraph V} [DecidableRel F.Adj]
    {F' : SimpleGraph V'} [DecidableRel F'.Adj] (h : F ⊑ F') :
    homDensity F' W ≤ homDensity F W := by
  classical
  obtain ⟨f, hf⟩ := isContained_iff_exists_le_comap.1 h
  calc homDensity F' W ≤ homDensity (F.map f) W := homDensity_anti W (map_le_iff_le_comap.2 hf)
    _ = homDensity F W := homDensity_map_embedding W F f

/-- **The clique bound.** A finite graph containing an `n`-clique has homomorphism density at most
that of the complete graph `Kₙ`. -/
theorem homDensity_le_homDensity_top_of_not_cliqueFree (W : Graphon Ω μ) {F : SimpleGraph V}
    [DecidableRel F.Adj] {n : ℕ} (h : ¬F.CliqueFree n) :
    homDensity F W ≤ homDensity (⊤ : SimpleGraph (Fin n)) W :=
  homDensity_le_of_isContained W ((not_cliqueFree_iff_top_isContained n).1 h)

/-- **The edge bound.** A finite graph with at least one edge has homomorphism density at most the
edge density `t(K₂, W)`. -/
theorem homDensity_le_homDensity_top_fin_two (W : Graphon Ω μ) {F : SimpleGraph V}
    [DecidableRel F.Adj] (hF : F ≠ ⊥) :
    homDensity F W ≤ homDensity (⊤ : SimpleGraph (Fin 2)) W :=
  homDensity_le_homDensity_top_of_not_cliqueFree W (cliqueFree_two.not.2 hF)

end DenseGraphLimits

end TauCeti
