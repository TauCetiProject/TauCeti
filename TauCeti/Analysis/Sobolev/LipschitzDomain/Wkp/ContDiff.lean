/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.LinearIsometry
import TauCeti.Analysis.Sobolev.Wkp.HolderRepresentative

/-!
# Hölder derivatives up to the boundary

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space of dimension
`n`, whose image under a linear isometry onto the model space `WithLp 2 (ℝ × E)` is a Lipschitz
domain, and let `n < p < ∞`. Every `u ∈ W^{j+1,p}(Ω)` agrees almost everywhere on `Ω` with a
function `g` that is `Cʲ` on `Ω` and whose derivatives of every order `i ≤ j` are bounded and
Hölder of exponent `1 - n/p` on `Ω`, with bounds linear in the norm of `u`. Since they are
uniformly continuous, all these derivatives extend continuously to `closure Ω`. In the plane this
is the `C^{j,1-2/p}` regularity up to the boundary of members of `W^{j+1,p}` with `p > 2`, on
discs and half-discs (`TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Planar`).

## Method

Each derivative is controlled by Morrey's embedding at exponent `q = p`, which applies to
`W^{k+1,p}(Ω)` for every `k`. This gives the exponent `1 - n/p` at every order, which the Hölder
embedding `W^{k,p} → C^{0,1-n/(k p)}` would not. The induction on `j` uses only the existence of
these embeddings, and is the domain-independent
`TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL`
(`TauCeti.Analysis.Sobolev.Wkp.HolderRepresentative`).

## Main declarations

* `TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_isLipschitzDomainWith_image`:
  `W^{j+1,p}(Ω) ⊆ C^{j,1-n/p}` for `n < p`, on isometric copies of bounded Lipschitz domains.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part II.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Theorem B.1.11.
-/

public section

noncomputable section

namespace TauCeti

open Bornology MeasureTheory Module TopologicalSpace
open scoped ENNReal NNReal ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

namespace Wkp

/-- **Hölder derivatives up to the boundary of a Lipschitz domain.** Let
`e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E)` be a linear isometry and `Ω ⊆ F` a bounded open set of dimension
`n` whose image `e '' Ω` is a Lipschitz domain, and let `n < p < ∞`. There is a constant `K` such
that every `u ∈ W^{j+1,p}(Ω)` agrees almost everywhere on `Ω` with a function `g` that is `Cʲ` on
`Ω`, and whose derivatives of order `i ≤ j` are bounded by `K ‖u‖` and Hölder of exponent
`1 - n/p` with constant `K ‖u‖` on `Ω`. In particular they extend continuously to `closure Ω`. -/
theorem exists_contDiffOn_holderOnWith_iteratedFDeriv_of_isLipschitzDomainWith_image
    {L : ℝ≥0} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × E))
    {Ω : Opens F} (hΩ : (e '' (Ω : Set F)).IsLipschitzDomainWith L) (hb : IsBounded (Ω : Set F))
    (hp : (finrank ℝ F : ℝ≥0) < p) (j : ℕ) :
    ∃ K : ℝ≥0, ∀ u : Wkp volume Ω p (j + 1), ∃ g : F → ℝ, ContDiffOn ℝ j g Ω ∧
      (value (j + 1) u : F → ℝ) =ᵐ[volume.restrict Ω] g ∧ ∀ i ≤ j,
        (∀ x ∈ Ω, ‖iteratedFDeriv ℝ i g x‖ ≤ K * ‖u‖) ∧
          HolderOnWith (K * ‖u‖₊) (1 - finrank ℝ F / p) (iteratedFDeriv ℝ i g) Ω :=
  exists_contDiffOn_holderOnWith_iteratedFDeriv_of_forall_holderSpaceL
    (tsub_pos_of_lt ((div_lt_one (pos_of_gt hp)).2 hp))
    (fun k => exists_morreyEmbeddingL_of_isLipschitzDomainWith_image e hΩ hb k hp le_self_add
      le_rfl) j

end Wkp

end TauCeti
