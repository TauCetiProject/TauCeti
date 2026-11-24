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
finite. The sum is assembled by induction on the crossings from the last one. Over an interval
without crossings the path is invertible and has no spectral flow
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

/-- At an interior time of `[a, b]`, a path continuous and self-adjoint on `[a, b]` is continuous
and self-adjoint at all nearby times. -/
private theorem eventually_continuousAt_and_isSelfAdjoint (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    (∀ᶠ t in 𝓝 t₀, ContinuousAt A t) ∧ ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t) :=
  ⟨eventually_of_mem (Ioo_mem_nhds ht₀.1 ht₀.2) fun _ ht ↦
      hA.continuousAt (Icc_mem_nhds ht.1 ht.2),
    eventually_of_mem (Icc_mem_nhds ht₀.1 ht₀.2) hsa⟩

omit [CompleteSpace H] in
/-- A crossing in `[a, b]` of a path injective at both endpoints lies in `(a, b)`. -/
private theorem mem_Ioo_of_ker_ne_bot (ha : (A a).ker = ⊥) (hb : (A b).ker = ⊥) {t : ℝ}
    (ht : t ∈ Icc a b) (hnt : (A t).ker ≠ ⊥) : t ∈ Ioo a b :=
  ⟨lt_of_le_of_ne ht.1 fun h ↦ hnt (h ▸ ha), lt_of_le_of_ne ht.2 fun h ↦ hnt (h ▸ hb)⟩

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
  rw [← inter_ofPred_eq_sep, ← compl_ofPred, ← sdiff_eq]
  -- The injective times are codiscrete in the compact interval `[a, b]`.
  refine isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin <|
    mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun z hz ↦ ?_
  suffices h : ∀ᶠ t in 𝓝[≠] z, t ∈ Icc a b → (A t).ker = ⊥ from
    mem_of_superset h fun t ht ↦ (em (t ∈ Icc a b)).imp ht id
  by_cases hnz : (A z).ker = ⊥
  · -- `A z` is invertible, and so is `A t` for every `t ∈ [a, b]` near `z`.
    have hunit : IsUnit (A z) :=
      (hF z hz).isUnit_of_injective_of_isSelfAdjoint (hsa z hz) (LinearMap.ker_eq_bot.1 hnz)
    have hopen := eventually_nhdsWithin_iff.1 <| (hA z hz).eventually (Units.isOpen.mem_nhds hunit)
    filter_upwards [nhdsWithin_le_nhds hopen] with t ht htI
    exact LinearMap.ker_eq_bot.2 (isInvertible_iff_isUnit.2 (ht htI)).injective
  · -- A crossing lies in `(a, b)`, and regular crossings are isolated.
    have hz' : z ∈ Ioo a b := mem_Ioo_of_ker_ne_bot ha hb hz hnz
    obtain ⟨hcont, hsa'⟩ := eventually_continuousAt_and_isSelfAdjoint hA hsa hz'
    filter_upwards [eventually_ker_eq_bot_of_crossingForm_nondegenerate hcont hsa' (hF z hz)
      (hderiv z hz' hnz) (hreg z hz' hnz)] with t ht _ using ht

/-- The regular-crossing formula for a finite set `S` of regular crossings in `(a, b)` outside which
the path is injective, by induction on `S` from its largest element. -/
private theorem spectralFlow_eq_sum_crossingForm_of_finset (S : Finset ℝ) :
    ∀ b, a ≤ b → ContinuousOn A (Icc a b) → (∀ t ∈ Icc a b, IsSelfAdjoint (A t)) →
      (∀ t ∈ Icc a b, (A t).IsFredholm) → (∀ t ∈ Icc a b, t ∉ S → (A t).ker = ⊥) →
      (∀ t ∈ S, t ∈ Ioo a b ∧ HasDerivAt A (A' t) t ∧
        (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))).Nondegenerate) →
      spectralFlow A a b = ∑ t ∈ S,
        ((sigPos (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t))) : ℤ) -
          sigNeg (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (A' t)))) := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro b hab hA hsa hF hker _
    rw [Finset.sum_empty]
    exact spectralFlow_eq_zero_of_forall_ker_eq_bot hab hA hsa hF fun t ht ↦
      hker t ht (Finset.notMem_empty t)
  | insert s S hlt ih =>
    intro b _ hA hsa hF hker hS
    obtain ⟨⟨has, hsb⟩, hd, hΓ⟩ := hS s (Finset.mem_insert_self s S)
    obtain ⟨hcont, hsa'⟩ := eventually_continuousAt_and_isSelfAdjoint hA hsa ⟨has, hsb⟩
    -- Choose `t₁ < s < t₂`, with `t₁` above every other crossing, such that the spectral flow from
    -- `t₁` to `t₂` is the signature of the crossing form at `s`.
    have hleft : ∀ᶠ t in 𝓝[<] s, t ∈ Ioo a s ∧ ∀ x ∈ S, x < t :=
      (eventually_mem_set.2 (Ioo_mem_nhdsLT has)).and <| (eventually_all_finset S).2 fun x hx ↦
        (eventually_mem_set.2 (Ioo_mem_nhdsLT (hlt x hx))).mono fun t ht ↦ ht.1
    obtain ⟨t₁, ⟨⟨hat₁, ht₁s⟩, hSt₁⟩, hjump⟩ := (hleft.and
      (eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm hcont hsa'
        (hF s ⟨has.le, hsb.le⟩) hd hΓ)).exists
    obtain ⟨t₂, ⟨hst₂, ht₂b⟩, hjump⟩ :=
      ((eventually_mem_set.2 (Ioo_mem_nhdsGT hsb)).and hjump).exists
    -- On `[t₂, b]` there is no crossing, so there is no spectral flow there.
    have hright : spectralFlow A t₂ b = 0 := by
      have hsub : Icc t₂ b ⊆ Icc a b := Icc_subset_Icc (has.trans hst₂).le le_rfl
      refine spectralFlow_eq_zero_of_forall_ker_eq_bot ht₂b.le (hA.mono hsub)
        (fun t ht ↦ hsa t (hsub ht)) (fun t ht ↦ hF t (hsub ht)) fun t ht ↦ hker t (hsub ht) ?_
      rw [Finset.mem_insert, not_or]
      exact ⟨(hst₂.trans_le ht.1).ne', fun htS ↦ (hlt t htS).not_gt (hst₂.trans_le ht.1)⟩
    -- On `[a, t₁]` the crossings are those of `S`, and the induction hypothesis applies.
    have hsub : Icc a t₁ ⊆ Icc a b := Icc_subset_Icc le_rfl (ht₁s.trans hsb).le
    have hinit := ih t₁ hat₁.le (hA.mono hsub) (fun t ht ↦ hsa t (hsub ht))
      (fun t ht ↦ hF t (hsub ht))
      (fun t ht htS ↦ hker t (hsub ht) (by
        rw [Finset.mem_insert, not_or]
        exact ⟨(ht.2.trans_lt ht₁s).ne, htS⟩))
      (fun t htS ↦ ⟨⟨(hS t (Finset.mem_insert_of_mem htS)).1.1, hSt₁ t htS⟩,
        (hS t (Finset.mem_insert_of_mem htS)).2⟩)
    -- Concatenate the spectral flows over `[a, t₁]`, `[t₁, t₂]` and `[t₂, b]`.
    have ht₁t₂ : t₁ ≤ t₂ := (ht₁s.trans hst₂).le
    have hsub₂ : Icc a t₂ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₂b.le
    rw [spectralFlow_add_adjacent_intervals (hat₁.le.trans ht₁t₂) ht₂b.le hA hsa hF,
      spectralFlow_add_adjacent_intervals hat₁.le ht₁t₂ (hA.mono hsub₂)
        (fun t ht ↦ hsa t (hsub₂ ht)) (fun t ht ↦ hF t (hsub₂ ht)),
      hinit, hjump, hright, Finset.sum_insert fun h ↦ (hlt s h).false]
    ring

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
  have hfin := finite_setOf_ker_ne_bot hA hsa hF ha hb hderiv hreg
  have hS : ∀ t, t ∈ hfin.toFinset ↔ t ∈ Icc a b ∧ (A t).ker ≠ ⊥ := by simp
  rw [spectralFlow_eq_sum_crossingForm_of_finset hfin.toFinset b hab hA hsa hF
    (fun t ht htS ↦ not_not.1 fun hnt ↦ htS ((hS t).2 ⟨ht, hnt⟩))
    (fun t htS ↦ by
      obtain ⟨ht, hnt⟩ := (hS t).1 htS
      have hIoo := mem_Ioo_of_ker_ne_bot ha hb ht hnt
      exact ⟨hIoo, hderiv t hIoo hnt, hreg t hIoo hnt⟩)]
  refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
  ext t
  simp only [mem_inter_iff, Finset.mem_coe, hS, Function.mem_support]
  refine and_congr_left fun hft ↦ ?_
  -- Only crossings contribute: at an injective time the crossing form lives on the zero space.
  have hnt : (A t).ker ≠ ⊥ := fun hnt ↦ hft <|
    sigPos_sub_sigNeg_crossingForm_eq_zero_of_ker_eq_bot (by rwa [ker_innerSL_comp]) _
  exact ⟨fun ht ↦ ⟨Ioo_subset_Icc_self ht, hnt⟩, fun ⟨ht, _⟩ ↦ mem_Ioo_of_ker_ne_bot ha hb ht hnt⟩

end TauCeti
