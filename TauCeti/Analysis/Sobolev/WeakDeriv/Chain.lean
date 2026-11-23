/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Iterated weak gradient chains

A chain of iterated weak gradients of `u : E → ℝ` on an open set `Ω` is a family of fields
`G i : E → TauCeti.IteratedGradient E i` such that `u` has weak derivative `innerSL ℝ ∘ G 0` and
each `G (i + 1)` is the weak derivative of `G i`. Since weak derivatives are unique almost
everywhere, two such chains of the same function agree almost everywhere, level by level. By this
uniqueness, chains defined near every point of `Ω` glue to a chain on all of `Ω`.

## Main declarations

* `TauCeti.ae_eq_of_iteratedGradient_chain`: uniqueness of weak derivative chains.
* `TauCeti.ae_eq_iteratedGradientChain_of_contDiffOn`: for a `C^{n+1}` representative, the chain is
  the classical one.
* `TauCeti.exists_hasWeakFDerivOn_chain_of_locally`: weak derivative chains defined near every
  point glue to one on the whole domain.
-/

public section

open MeasureTheory TopologicalSpace

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} {Omega : Opens E}

/-- **Uniqueness of weak derivative chains.** Two chains of iterated weak gradients of the same
function on `Ω` agree almost everywhere on `Ω`, level by level. -/
theorem ae_eq_of_iteratedGradient_chain (n : ℕ) {u : E → ℝ}
    {G G' : (i : ℕ) → E → IteratedGradient E i}
    (h0 : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G 0 x)))
    (hG : ∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1)))
    (h0' : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G' 0 x)))
    (hG' : ∀ i < n, HasWeakFDerivOn mu Omega (G' i) (G' (i + 1))) :
    ∀ i ≤ n, G i =ᵐ[mu.restrict Omega] G' i := by
  intro i hi
  induction i with
  | zero =>
    filter_upwards [h0.ae_eq h0'] with x hx
    exact innerSL_inj.1 hx
  | succ i ih =>
    exact (hG i (by omega)).ae_eq ((hG' i (by omega)).congr_ae (ih (by omega)).symm)

/-- **Weak derivative chains of `C^{n+1}` functions are classical.** If `u` agrees almost
everywhere on `Ω` with a function `f` that is `C^{n+1}` on `Ω`, then every chain of iterated weak
gradients of `u` agrees almost everywhere on `Ω`, through order `n`, with the classical iterated
gradients `TauCeti.iteratedGradientChain f`. -/
theorem ae_eq_iteratedGradientChain_of_contDiffOn [mu.IsAddHaarMeasure] (n : ℕ) {u f : E → ℝ}
    (hf : ContDiffOn ℝ (n + 1) f Omega) (huf : u =ᵐ[mu.restrict Omega] f)
    {G : (i : ℕ) → E → IteratedGradient E i}
    (h0 : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G 0 x)))
    (hG : ∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1))) :
    ∀ i ≤ n, G i =ᵐ[mu.restrict Omega] iteratedGradientChain f i :=
  ae_eq_of_iteratedGradient_chain n (h0.congr_ae huf) hG
    (by simpa only [iteratedGradientChain_zero] using
      hasWeakFDerivOn_gradient_of_contDiffOn (hf.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1))))
    fun i hi => by
      rw [iteratedGradientChain_succ]
      exact ContDiffOn.hasWeakFDerivOn_fderiv fun x hx =>
        (contDiffAt_iteratedGradientChain (hf.contDiffAt (Omega.isOpen.mem_nhds hx)) i
          (by exact_mod_cast (by omega : 1 + i + 1 ≤ n + 1))).contDiffWithinAt

/-- **Weak derivative chains glue.** If every point of `Ω` has an open neighbourhood on which `f`
has a chain `H 0, …, H n` of iterated weak gradients, then `f` has such a chain on all of `Ω`.
The local chains are not required to agree pointwise on overlaps. -/
theorem exists_hasWeakFDerivOn_chain_of_locally (n : ℕ) {f : E → ℝ}
    (h : ∀ x ∈ Omega, ∃ W : Opens E, x ∈ W ∧ ∃ H : (i : ℕ) → E → IteratedGradient E i,
      HasWeakFDerivOn mu W f (fun y => innerSL ℝ (H 0 y)) ∧
        ∀ i < n, HasWeakFDerivOn mu W (H i) (H (i + 1))) :
    ∃ G : (i : ℕ) → E → IteratedGradient E i,
      HasWeakFDerivOn mu Omega f (fun x => innerSL ℝ (G 0 x)) ∧
        ∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1)) := by
  -- By uniqueness the local chains agree almost everywhere on overlaps, so each field glues
  -- with `exists_hasWeakFDerivOn_iff_locally`.
  induction n with
  | zero =>
    obtain ⟨D, hD⟩ := exists_hasWeakFDerivOn_iff_locally.2 fun x hx => by
      obtain ⟨W, hxW, H, hH0, -⟩ := h x hx
      exact ⟨W, hxW, _, hH0⟩
    refine ⟨Function.update (fun _ _ => 0) 0 fun x => (InnerProductSpace.toDual ℝ E).symm (D x),
      ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    refine hD.congr_ae_deriv (Filter.Eventually.of_forall fun x => ?_)
    ext v
    simp only [Function.update_self, innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
  | succ n ih =>
    obtain ⟨G, hG0, hG⟩ := ih fun x hx => by
      obtain ⟨W, hxW, H, hH0, hH⟩ := h x hx
      exact ⟨W, hxW, H, hH0, fun i hi => hH i (by omega)⟩
    -- Near each point the top field `G n` agrees with that of a local chain, which has a weak
    -- derivative there.
    obtain ⟨D, hD⟩ := exists_hasWeakFDerivOn_iff_locally.2 fun x hx => by
      obtain ⟨W, hxW, H, hH0, hH⟩ := h x hx
      have hle : W ⊓ Omega ≤ W := inf_le_left
      have hle' : W ⊓ Omega ≤ Omega := inf_le_right
      have hGH := ae_eq_of_iteratedGradient_chain n (hG0.mono hle')
        (fun i hi => (hG i hi).mono hle') (hH0.mono hle) (fun i hi => (hH i (by omega)).mono hle)
        n le_rfl
      exact ⟨W ⊓ Omega, ⟨hxW, hx⟩, _, ((hH n (by omega)).mono hle).congr_ae hGH.symm⟩
    refine ⟨Function.update G (n + 1) D, ?_, fun i hi => ?_⟩
    · rw [Function.update_of_ne (Nat.succ_ne_zero n).symm]
      exact hG0
    · rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hG i hi
      · rw [Function.update_self]
        exact hD

end TauCeti
