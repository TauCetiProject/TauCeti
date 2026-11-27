/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Crossing
import TauCeti.Analysis.Fredholm.SelfAdjoint
import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Order.Interval.Basic
import TauCeti.Topology.Order.Interval.Jumps

/-!
# The regular-crossing formula for the spectral flow

Let `A` be a continuous path of self-adjoint Fredholm operators on a real Hilbert space `H` over
`[a, b]`, whose endpoints `A a` and `A b` are injective, hence invertible. A *crossing* of `A` is a
time `t` at which `A t` is not injective. It is *regular* when `A` has a derivative `A' t` at `t`
and the crossing form `Γₜ v = ⟪A' t v, v⟫` on the kernel of `A t`
(`ContinuousLinearMap.crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))`) is
nondegenerate. This file proves **Robbin and Salamon's regular-crossing formula**: if every
crossing is regular, then there are finitely many crossings
(`TauCeti.finite_setOf_ker_ne_bot`), and the spectral flow `TauCeti.spectralFlow A a b` is the sum
of the signatures of their crossing forms,

`spectralFlow A a b = ∑ᶠ t ∈ (a, b), (sigPos Γₜ - sigNeg Γₜ)`

(`TauCeti.spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm`). Positive crossings count
positively. Times at which `A t` is injective contribute `0` to the sum, since the crossing form
then lives on the zero space.

The local ingredients are in `TauCeti.Analysis.Fredholm.Spectral.Crossing`. Regular crossings are
isolated (`TauCeti.eventually_ker_eq_bot_of_crossingForm_nondegenerate`), and the injective times
form an open subset of `[a, b]`, because an injective self-adjoint Fredholm operator is invertible
(`ContinuousLinearMap.IsFredholm.isInvertible_of_injective_of_isSelfAdjoint`) and invertible
operators form an open set. So the crossings form a closed discrete subset of `[a, b]`, which is
finite. The spectral flow is then the sum of its jumps at the crossings
(`TauCeti.eq_finsum_of_eventually_eq_of_add`). Over an interval without crossings the path is
invertible and has no spectral flow
(`TauCeti.spectralFlow_eq_zero_of_forall_ker_eq_bot`). Across a crossing, the spectral
flow over a short enough interval is the signature of its crossing form
(`TauCeti.eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm`), and concatenation
(`TauCeti.spectralFlow_add_adjacent_intervals`) adds the pieces.

In finite dimensions every operator is Fredholm
(`ContinuousLinearMap.isFredholm_of_finiteDimensional`), so the formula holds for every
continuous path of symmetric operators with invertible endpoints and regular crossings. There the
spectral flow is also the drop of the negative index of `A t`
(`TauCeti.spectralFlow_eq_finrank_pointSpectralSubspace_sub_finrank`), and the formula becomes
the drop of the negative index of `⟪A t ·, ·⟫` along a path of symmetric forms with regular
crossings, `ContinuousLinearMap.sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm`.

## Main results

* `TauCeti.spectralFlow_eq_zero_of_forall_ker_eq_bot`: a path without crossings has no spectral
  flow.
* `TauCeti.finite_setOf_ker_ne_bot`: a path with regular crossings has finitely many crossings.
* `TauCeti.spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm`: the regular-crossing formula.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Theorem 4.21 (the spectral flow as a sum of crossing signatures).
* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
-/

public section

open Filter Set Topology ContinuousLinearMap
open scoped InnerProductSpace

namespace TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {A A' : ℝ → H →L[ℝ] H} {a b : ℝ}

/-- A continuous path of self-adjoint Fredholm operators on a real Hilbert space that is injective,
hence invertible, at every time of `[a, b]` has no spectral flow over `[a, b]`. -/
theorem spectralFlow_eq_zero_of_forall_ker_eq_bot (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    (hker : ∀ t ∈ Icc a b, (A t).ker = ⊥) : spectralFlow A a b = 0 :=
  spectralFlow_eq_zero_of_forall_zero_notMem_spectrum hab hA hsa fun t ht ↦
    (hF t ht).zero_notMem_spectrum_of_injective_of_isSelfAdjoint (hsa t ht)
      (LinearMap.ker_eq_bot.1 (hker t ht))

/-- **A path with regular crossings has finitely many crossings.** Let `A` be a continuous path of
self-adjoint Fredholm operators on a real Hilbert space over `[a, b]`, injective at both endpoints.
If at every crossing `t ∈ (a, b)`, where `A t` is not injective, the path has a derivative `A' t`
and a nondegenerate crossing form, then the crossings in `[a, b]` form a finite set. -/
theorem finite_setOf_ker_ne_bot (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    (ha : (A a).ker = ⊥) (hb : (A b).ker = ⊥)
    (hderiv : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ → HasDerivAt A (A' t) t)
    (hreg : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ →
      (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))).Nondegenerate) :
    {t ∈ Icc a b | (A t).ker ≠ ⊥}.Finite := by
  refine finite_setOf_not_of_eventually (p := fun t ↦ (A t).ker = ⊥) ha hb (fun z hz hnz ↦ ?_)
    fun z hz' hnz ↦ ?_
  · -- `A z` is invertible, and so is `A t` for every `t ∈ [a, b]` near `z`.
    have hunit : IsUnit (A z) :=
      (hF z hz).isUnit_of_injective_of_isSelfAdjoint (hsa z hz) (LinearMap.ker_eq_bot.1 hnz)
    exact ((hA z hz).eventually (Units.isOpen.mem_nhds hunit)).mono fun t ht ↦
      LinearMap.ker_eq_bot.2 (isInvertible_iff_isUnit.2 ht).injective
  · -- Regular crossings are isolated.
    have hz := Ioo_subset_Icc_self hz'
    obtain ⟨hcont, hsa'⟩ := hA.eventually_continuousAt_and_eventually_of_mem_Ioo hsa hz'
    exact eventually_ker_eq_bot_of_crossingForm_nondegenerate hcont hsa' (hF z hz)
      (hderiv z hz' hnz) (hreg z hz' hnz)

/-- **The regular-crossing formula for the spectral flow** (Robbin–Salamon). Let `A` be a continuous
path of self-adjoint Fredholm operators on a real Hilbert space over `[a, b]`, injective (hence
invertible) at both endpoints. Suppose that every crossing `t ∈ (a, b)`, a time at which `A t` is
not injective, is regular: `A` has a derivative `A' t` at `t`, and the crossing form
`Γₜ : v ↦ ⟪A' t v, v⟫` on the kernel of `A t` is nondegenerate. Then the spectral flow of `A` is the
sum over the crossings of the signatures `sigPos Γₜ - sigNeg Γₜ`. Times at which `A t` is
injective contribute zero to the sum, and there are only finitely many crossings
(`TauCeti.finite_setOf_ker_ne_bot`). -/
theorem spectralFlow_eq_finsum_sigPos_sub_sigNeg_crossingForm (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t))
    (hF : ∀ t ∈ Icc a b, (A t).IsFredholm) (ha : (A a).ker = ⊥) (hb : (A b).ker = ⊥)
    (hderiv : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ → HasDerivAt A (A' t) t)
    (hreg : ∀ t ∈ Ioo a b, (A t).ker ≠ ⊥ →
      (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))).Nondegenerate) :
    spectralFlow A a b = ∑ᶠ t ∈ Ioo a b,
      ((sigPos (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))) : ℤ) -
        sigNeg (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t)))) := by
  refine eq_finsum_of_eventually_eq_of_add (p := fun t ↦ (A t).ker = ⊥) hab
    (finite_setOf_ker_ne_bot hA hsa hF ha hb hderiv hreg) ha hb
    (fun s m t has hsm hmt htb ↦ ?_) (fun s t has hst htb hker ↦ ?_) (fun s hs hns ↦ ?_)
    fun t _ ht ↦ sigPos_sub_sigNeg_crossingForm_eq_zero_of_ker_eq_bot (by rwa [ker_innerSL_comp]) _
  · -- The spectral flow is additive.
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    exact spectralFlow_add_adjacent_intervals hsm hmt (hA.mono hsub)
      (fun u hu ↦ hsa u (hsub hu)) fun u hu ↦ hF u (hsub hu)
  · -- Over an interval without crossings there is no spectral flow.
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    exact spectralFlow_eq_zero_of_forall_ker_eq_bot hst (hA.mono hsub)
      (fun u hu ↦ hsa u (hsub hu)) (fun u hu ↦ hF u (hsub hu)) hker
  · -- Across a crossing the spectral flow jumps by the signature of its crossing form.
    obtain ⟨hcont, hsa'⟩ := hA.eventually_continuousAt_and_eventually_of_mem_Ioo hsa hs
    exact eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm hcont hsa'
      (hF s (Ioo_subset_Icc_self hs)) (hderiv s hs hns) (hreg s hs hns)

end TauCeti
