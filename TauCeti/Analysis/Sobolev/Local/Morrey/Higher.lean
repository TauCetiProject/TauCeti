/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Sobolev.WeakDeriv.ContinuousRepresentative

/-!
# Higher-order Morrey embedding for local Sobolev maps on planar domains

Let `Ω ⊆ ℂ` be open, let `F` be a finite-dimensional real normed space, let `2 < p ≤ ∞` and let
`k ≥ 0`. This file proves that a map `u ∈ W^{k+1,p}_loc(Ω, F)`, in the sense of
`TauCeti.MemWkpLoc p Ω (k + 1)`, agrees almost everywhere on `Ω` with a map `g` of class `Cᵏ` on
`Ω`, whose first derivative is a weak derivative of `u` (for `k ≥ 1`) and whose `k`-th derivative
lies in `W^{1,p}_loc` and is Hölder continuous with exponent `α = 1 - 2 / p` on compact subsets of
`Ω`, with the local bound

`‖Dᵏg(x) - Dᵏg(y)‖ ≤ C ‖D(Dᵏg)‖_{Lᵖ(B(x, 2|x - y|))} |x - y|^α`
whenever `closedBall x (2|x - y|) ⊆ Ω`.

Here `Dᵏg = iteratedFDeriv ℝ k g` and `D(Dᵏg)` is any weak derivative of it on `Ω`. The constant
`C` depends only on `p`, `k` and `F`. Equivalently, `W^{k,p}_loc` maps have `C^{k-1, 1-2/p}`
representatives for `k ≥ 1`.

## Proof

The order-one case is `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative` together with the
local Morrey inequality `TauCeti.MemWkpLoc.exists_dist_preciseRepresentative_le`. Higher orders
follow by induction on `k`: a weak derivative of `u ∈ W^{k+2,p}_loc` lies in `W^{k+1,p}_loc`, so
it has a `Cᵏ` representative by induction, and a function whose weak derivative is `Cᵏ` has a
`Cᵏ⁺¹` representative (`TauCeti.HasWeakFDerivOn.exists_contDiffOn_succ_ae_eq`).

For the Hölder bound, the classical derivative of a `C¹` representative `g` of `u` is a weak
derivative of `u` lying in the preceding local Sobolev class
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`), so by induction `iteratedFDeriv ℝ k g`
lies in `W^{1,p}_loc` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`). The order-one
estimates then apply to it. These two derivative results hold for every `p` and live in
`TauCeti.Analysis.Sobolev.Local.Basic`. The finite-dimensionality of the space of `k`-multilinear
maps needed by the order-one estimates is `ContinuousMultilinearMap.instModuleFinite`.

## Main declarations

* `TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq`: `W^{k+1,p}_loc ⊆ Cᵏ` for `p > 2`.
* `TauCeti.MemWkpLoc.exists_dist_iteratedFDeriv_le`: the local Morrey inequality for the top
  derivative.
* `TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact`: Hölder continuity of the
  top derivative on compact subsets of `Ω`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Morrey's embedding for local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 5 and §5.6.3.
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {k : ℕ} {u g : ℂ → F}

/-! ### Morrey's embedding at higher order -/

variable [FiniteDimensional ℝ F]

/-- **Morrey's embedding `W^{k+1,p}_loc ⊆ Cᵏ` for `p > 2`.** A map `u ∈ MemWkpLoc p Ω (k + 1)`
agrees almost everywhere on `Ω` with a map `g` that is `Cᵏ` on `Ω`. For `k ≥ 1` the classical
derivative of `g` is a weak derivative of `u`
(`TauCeti.MemWkpLoc.hasWeakFDerivOn_fderiv_of_contDiffOn`), and the `k`-th derivative of `g` is
Hölder continuous with exponent `1 - 2 / p` on compact subsets of `Ω`
(`TauCeti.MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact`). -/
theorem MemWkpLoc.exists_contDiffOn_ae_eq (hp : 2 < p) (hu : MemWkpLoc p Ω (k + 1) u) :
    ∃ g : ℂ → F, ContDiffOn ℝ k g Ω ∧ u =ᵐ[volume.restrict Ω] g := by
  induction k generalizing F with
  | zero =>
    refine ⟨preciseRepresentative volume u, ?_, ?_⟩
    · simpa using hu.continuousOn_preciseRepresentative hp
    · exact hu.memLpLoc.ae_eq_preciseRepresentative (one_le_two.trans hp.le)
  | succ k ih =>
    obtain ⟨D, hD, hDk⟩ := hu.exists_weakFDeriv_of_isOpen
    obtain ⟨h, hh, hDh⟩ := ih hDk
    obtain ⟨g, hg, hug, -⟩ := (hD.congr_ae_deriv hDh).exists_contDiffOn_succ_ae_eq (n := k) hh
    exact ⟨g, by exact_mod_cast hg, hug⟩

/-- The `k`-th derivative of a `Cᵏ` representative of `u ∈ MemWkpLoc p Ω (k + 1)` lies in
`MemWkpLoc p Ω 1`, is continuous on `Ω`, and therefore equals its precise representative there. -/
private theorem iteratedFDeriv_memWkpLoc_one_and_eqOn (hu : MemWkpLoc p Ω (k + 1) u)
    (hg : ContDiffOn ℝ k g Ω) (hug : u =ᵐ[volume.restrict Ω] g) :
    MemWkpLoc p Ω 1 (iteratedFDeriv ℝ k g) ∧
      EqOn (preciseRepresentative volume (iteratedFDeriv ℝ k g)) (iteratedFDeriv ℝ k g) Ω := by
  have h1 := hu.iteratedFDeriv_of_contDiffOn hg hug
  have hcont : ContinuousOn (iteratedFDeriv ℝ k g) Ω :=
    ContinuousOn.continuousOn_iteratedFDeriv hg Ω.isOpen le_rfl
  exact ⟨h1, eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hcont.locallyIntegrableOn Ω.isOpen.measurableSet) (Filter.EventuallyEq.refl _ _) hcont⟩

/-- **The local Morrey inequality at higher order.** Let `2 < p ≤ ∞`, `α = 1 - 2 / p` and
`k ≥ 0`. There is a constant `C > 0`, depending only on `p`, `k` and `F`, such that the following
holds. Let `u ∈ MemWkpLoc p Ω (k + 1)`, let `g` be `Cᵏ` on `Ω` and equal to `u` almost everywhere
on `Ω`, and let `E` be a weak derivative of `Dᵏg = iteratedFDeriv ℝ k g` on `Ω`, which exists
since `Dᵏg ∈ MemWkpLoc p Ω 1` (`TauCeti.MemWkpLoc.iteratedFDeriv_of_contDiffOn`).
If `closedBall x (2 |x - y|) ⊆ Ω`, then

`‖Dᵏg(x) - Dᵏg(y)‖ ≤ C ‖E‖_{Lᵖ(B(x, 2 |x - y|))} |x - y|^α`. -/
theorem MemWkpLoc.exists_dist_iteratedFDeriv_le (hp : 2 < p) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ} {u g : ℂ → F}
      {E : ℂ → ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) F},
      MemWkpLoc p Ω (k + 1) u → ContDiffOn ℝ k g Ω → u =ᵐ[volume.restrict Ω] g →
      HasWeakFDerivOn volume Ω (iteratedFDeriv ℝ k g) E →
      ∀ {x y : ℂ}, closedBall x (2 * dist x y) ⊆ Ω →
        dist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y) ≤
          C * (eLpNorm E p (volume.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  obtain ⟨C, hC, hdist⟩ := MemWkpLoc.exists_dist_preciseRepresentative_le
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ) F) hp
  refine ⟨C, hC, fun {Ω u g E} hu hg hug hE x y hxy => ?_⟩
  obtain ⟨h1, heq⟩ := iteratedFDeriv_memWkpLoc_one_and_eqOn hu hg hug
  have hx : x ∈ (Ω : Set ℂ) := hxy (mem_closedBall_self (by positivity))
  have hy : y ∈ (Ω : Set ℂ) := hxy (by
    rw [mem_closedBall, dist_comm]
    linarith [dist_nonneg (x := x) (y := y)])
  rw [← heq hx, ← heq hy]
  exact hdist h1 hE hxy

/-- **Morrey's embedding at higher order on compact sets.** If `2 < p ≤ ∞`, `g` is `Cᵏ` on `Ω`
and agrees almost everywhere on `Ω` with `u ∈ MemWkpLoc p Ω (k + 1)`, then
`iteratedFDeriv ℝ k g` is Hölder continuous with exponent `1 - 2 / p` on every compact subset of
`Ω`: `g` is a `C^{k, 1 - 2/p}` representative of `u`. -/
theorem MemWkpLoc.exists_holderOnWith_iteratedFDeriv_of_isCompact (hp : 2 < p)
    (hu : MemWkpLoc p Ω (k + 1) u) (hg : ContDiffOn ℝ k g Ω) (hug : u =ᵐ[volume.restrict Ω] g)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal (iteratedFDeriv ℝ k g) K := by
  obtain ⟨h1, heq⟩ := iteratedFDeriv_memWkpLoc_one_and_eqOn hu hg hug
  obtain ⟨C, hC⟩ := h1.exists_holderOnWith_preciseRepresentative_of_isCompact hp hK hKΩ
  refine ⟨C, fun x hx y hy => ?_⟩
  rw [← heq (hKΩ hx), ← heq (hKΩ hy)]
  exact hC x hx y hy

end TauCeti
