/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.LipschitzRepresentative
public import TauCeti.Analysis.Sobolev.Wkp.HolderRepresentative

/-!
# Lipschitz representatives of `W^{k,∞}` functions

Let `Ω` be a convex open subset of a finite-dimensional real inner product space. Applying the
Lipschitz representative `W^{1,∞}(Ω) → C^{0,1}(closure Ω)` (`TauCeti.W1p.lipschitzRepresentativeL`)
to the derivatives of every order gives the endpoint `p = ∞` of the Sobolev embedding into Hölder
spaces, `W^{k,∞} ⊆ C^{k-1,1}` for `k ≥ 1`: every `u ∈ W^{j+1,∞}(Ω)` has a representative that is
`Cʲ` on `Ω` and whose derivatives of every order `i ≤ j` are bounded by `K ‖u‖` and Lipschitz with
constant `K ‖u‖` on `Ω` (`TauCeti.Wkp.exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex`).
This is the domain-independent induction
`TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL` at Hölder
exponent `1`. On the whole space the representative lies in the Banach space
`C_b^{j,1}(E)` of `TauCeti.CkHolderSpace`, and depends linearly and boundedly on `u`
(`TauCeti.Wkp.toCkHolderSpaceOne`, the case `α = 1`, `p = ∞` of `TauCeti.Wkp.toCkHolderSpaceL`).

Unlike the embeddings for `p < ∞`, there is no gain of a fractional exponent here: the exponent
`1` is that of the Lipschitz bound itself, and it is sharp, since `x ↦ |x|` lies in
`W^{1,∞}(-1, 1)` and is not `C¹`.

## Main declarations

* `TauCeti.Wkp.exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex`:
  `W^{j+1,∞}(Ω) ⊆ C^{j,1}(Ω)` on convex `Ω`, with bounds linear in `‖u‖`.
* `TauCeti.Wkp.toCkHolderSpaceOne`: the embedding `W^{j+1,∞}(E) → C_b^{j,1}(E)` as a continuous
  linear map, characterised by `TauCeti.Wkp.toCkHolderSpaceOne_eq_iff`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Wkp

/-- On a convex domain, the Lipschitz representatives of the first-order parts give Lipschitz
representatives of every order, as required by
`exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL`. -/
private theorem forall_holderSpaceL_one {Ω : Opens E} (hΩ : Convex ℝ (Ω : Set E)) (k : ℕ) :
    ∃ T : Wkp volume Ω ∞ (k + 1) →L[ℝ] HolderSpace 1 (closure (Ω : Set E)) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = value (k + 1) u x :=
  ⟨(W1p.lipschitzRepresentativeL hΩ).comp (firstOrderL k), fun u ↦ by
    have h := W1p.ae_lipschitzRepresentativeL_eq (μ := volume) hΩ (firstOrder k u)
    rw [value_firstOrder] at h
    rwa [ContinuousLinearMap.comp_apply, firstOrderL_apply]⟩

/-- **The Sobolev embedding `W^{j+1,∞} ⊆ C^{j,1}` on convex domains.** Let `Ω` be a convex open
set. There is a constant `K` such that every `u ∈ W^{j+1,∞}(Ω)` agrees almost everywhere on `Ω`
with a function `g` that is `Cʲ` on `Ω`, whose derivatives of order `i ≤ j` are bounded by `K ‖u‖`
and Lipschitz with constant `K ‖u‖` on `Ω`. -/
theorem exists_contDiffOn_lipschitzOnWith_iteratedFDeriv_of_convex {Ω : Opens E}
    (hΩ : Convex ℝ (Ω : Set E)) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ u : Wkp volume Ω ∞ (j + 1), ∃ g : E → ℝ, ContDiffOn ℝ j g Ω ∧
      (value (j + 1) u : E → ℝ) =ᵐ[volume.restrict Ω] g ∧ ∀ i ≤ j,
        (∀ x ∈ Ω, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
          LipschitzOnWith (K * ‖u‖₊) (iteratedFDeriv ℝ i g) Ω := by
  obtain ⟨K, hK⟩ := exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL
    one_pos (forall_holderSpaceL_one hΩ) j
  refine ⟨K, fun u ↦ ?_⟩
  obtain ⟨g, hg, hug, hbd⟩ := hK u
  exact ⟨g, hg, hug, fun i hi ↦ ⟨(hbd i hi).1, holderOnWith_one.1 (hbd i hi).2⟩⟩

/-- **The Sobolev embedding `W^{j+1,∞}(E) → C_b^{j,1}(E)`.** On the whole space, every
`u ∈ W^{j+1,∞}(E)` has a representative that is `Cʲ` with bounded derivatives through order `j`
and a Lipschitz `j`-th derivative. It depends linearly and boundedly on `u`, and is the only
element of `C_b^{j,1}(E)` agreeing almost everywhere with `u`
(`TauCeti.Wkp.toCkHolderSpaceOne_eq_iff`). -/
def toCkHolderSpaceOne (j : ℕ) : Wkp volume (⊤ : Opens E) ∞ (j + 1) →L[ℝ] CkHolderSpace j 1 E ℝ :=
  toCkHolderSpaceL one_pos (forall_holderSpaceL_one convex_univ) j

/-- The embedding `W^{j+1,∞}(E) → C_b^{j,1}(E)` gives a representative of `u`. -/
theorem value_ae_eq_toCkHolderSpaceOne (j : ℕ) (u : Wkp volume (⊤ : Opens E) ∞ (j + 1)) :
    (value (j + 1) u : E → ℝ) =ᵐ[volume] toCkHolderSpaceOne j u :=
  value_ae_eq_toCkHolderSpaceL _ _ j u

/-- `toCkHolderSpaceOne j u` is the only element of `C_b^{j,1}(E)` representing `u`. -/
theorem toCkHolderSpaceOne_eq_iff (j : ℕ) {u : Wkp volume (⊤ : Opens E) ∞ (j + 1)}
    {f : CkHolderSpace j 1 E ℝ} :
    toCkHolderSpaceOne j u = f ↔ (value (j + 1) u : E → ℝ) =ᵐ[volume] f :=
  toCkHolderSpaceL_eq_iff _ _ j

end Wkp

end TauCeti
