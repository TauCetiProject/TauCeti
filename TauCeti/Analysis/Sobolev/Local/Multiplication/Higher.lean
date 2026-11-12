/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Multiplication
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Mixed-exponent products of local Sobolev maps at every order

Let `p > 2`, `1 < q ≤ p` and let `B : F × G → H` be continuous bilinear with `F` and `G`
finite-dimensional. For every `i ≥ 1`, if `f ∈ W^{i,p}_loc(Ω)` and `g ∈ W^{i,q}_loc(Ω)` on an open
planar domain `Ω`, then `B(f, g) ∈ W^{i,q}_loc(Ω)`. At `q = p` this is the algebra property of
`W^{i,p}_loc` under continuous bilinear maps.

These products describe how variable coefficients act on local Sobolev maps: a coefficient
field `A ∈ W^{i,p}_loc(Ω; F →L[ℝ] G)` with `p > 2` multiplies `W^{i,q}_loc(Ω; F)` into
`W^{i,q}_loc(Ω; G)`, and such fields compose with one another. The composition form is what the
higher-order composition theorem `TauCeti.MemWkpLoc.contDiffOn_comp_succ` uses to control the
weak derivative `z ↦ Dg(u z) ∘L Du z` of `g ∘ u`.

## Main declarations

* `TauCeti.MemWkpLoc.bilin_succ`: mixed-exponent products at every positive order.
* `TauCeti.MemWkpLoc.clm_apply_succ`: the field form `z ↦ A z (u z)` for a matrix-valued
  coefficient `A`.
* `TauCeti.MemWkpLoc.compL_succ`: the composition form `z ↦ A z ∘L C z`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- **Mixed-exponent products at every positive order.** For `p > 2` and `1 < q ≤ p`, the
product of a `W^{k+1,p}_loc` map with a `W^{k+1,q}_loc` map, both with finite-dimensional values,
is in `W^{k+1,q}_loc`. At `q = p` this is the algebra property of `W^{k+1,p}_loc` under continuous
bilinear maps. -/
theorem MemWkpLoc.bilin_succ [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {k : ℕ} {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p Ω (k + 1) f) (hg : MemWkpLoc q Ω (k + 1) g) :
    MemWkpLoc q Ω (k + 1) (fun z => B (f z) (g z)) := by
  -- Induction on the order from the order-one statement `TauCeti.MemWkpLoc.bilin`. By the weak
  -- Leibniz rule, the weak derivative of `B(f, g)` is `B(Df, g) + B(f, Dg)`, a sum of two mixed
  -- products of one order lower for the bilinear maps `B.precompL ℂ` and `B.precompR ℂ`, whose
  -- factors `Df` and `Dg` again have finite-dimensional values.
  induction k generalizing F G H with
  | zero => exact hf.bilin B hp hq hqp hg
  | succ k ih =>
    let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
    -- The order-one statement supplies local `L^q` membership of the product.
    have h1 : MemWkpLoc q Ω 1 (fun z => B (f z) (g z)) :=
      (hf.of_le (by omega)).bilin B hp hq hqp (hg.of_le (by omega))
    obtain ⟨Df, hDf, hDfk⟩ := hf.exists_weakFDeriv_of_isOpen
    obtain ⟨Dg, hDg, hDgk⟩ := hg.exists_weakFDeriv_of_isOpen
    -- `f` is locally bounded, by the local gain of integrability at `q = p`.
    have hfi : MemLpLoc ∞ Ω f := (hf.of_le (by omega)).memLpLoc_of_holderTriple hp le_rfl
    have hD := hDf.bilin_of_memLpLoc B hp hq hqp (hfi.mono_exponent le_top) hDfk.memLpLoc hDg
      hg.memLpLoc hDgk.memLpLoc
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨h1.memLpLoc, _, hD, ?_⟩
    exact (ih (B.precompL ℂ) hDfk hg.of_succ).add (ih (B.precompR ℂ) hf.of_succ hDgk)

/-- **Coefficient fields acting on local Sobolev maps.** For `p > 2` and `1 < q ≤ p`, a
coefficient field `A ∈ W^{k+1,p}_loc(Ω; F →L[ℝ] G)` applied to a map `u ∈ W^{k+1,q}_loc(Ω; F)`
gives `z ↦ A z (u z) ∈ W^{k+1,q}_loc(Ω; G)`. -/
theorem MemWkpLoc.clm_apply_succ (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {k : ℕ}
    {A : ℂ → F →L[ℝ] G} {u : ℂ → F} (hA : MemWkpLoc p Ω (k + 1) A)
    (hu : MemWkpLoc q Ω (k + 1) u) : MemWkpLoc q Ω (k + 1) (fun z => A z (u z)) :=
  hA.bilin_succ (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) hp hq hqp hu

/-- **Composition of local Sobolev fields of linear maps.** For `p > 2` and `1 < q ≤ p`, if
`A ∈ W^{k+1,p}_loc(Ω; G →L[ℝ] H)` and `C ∈ W^{k+1,q}_loc(Ω; F →L[ℝ] G)`, then
`z ↦ A z ∘L C z ∈ W^{k+1,q}_loc(Ω; F →L[ℝ] H)`. -/
theorem MemWkpLoc.compL_succ [FiniteDimensional ℝ H] (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    {k : ℕ} {A : ℂ → G →L[ℝ] H} {C : ℂ → F →L[ℝ] G} (hA : MemWkpLoc p Ω (k + 1) A)
    (hC : MemWkpLoc q Ω (k + 1) C) : MemWkpLoc q Ω (k + 1) (fun z => (A z).comp (C z)) :=
  hA.bilin_succ (ContinuousLinearMap.compL ℝ F G H) hp hq hqp hC

end TauCeti
