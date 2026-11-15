/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Pointwise
public import Mathlib.Order.Filter.CountableInter

/-!
# Countable group actions: almost invariant events versus invariant events

Mathlib's `ErgodicSMul` is phrased with **almost** invariant events: an action is ergodic when
every measurable `s` with `(g • ·) ⁻¹' s =ᵐ[μ] s` for all `g` is null or conull.  Concrete
σ-algebras of invariant events — the invariant σ-algebra of a map, or the exchangeable σ-algebra
of path space — instead collect the **exactly** invariant events, those with
`(g • ·) ⁻¹' s = s`.

For a **countable** group the two formulations agree up to null sets: the saturation
`⋃ g, g • s` is exactly invariant and, being a countable union of sets each almost equal to `s`,
almost equal to `s`.  This file records that saturation
(`exists_smul_invariant_ae_eq`) and the resulting characterization
(`ergodicSMul_iff_forall_smul_invariant`): to prove a countable action ergodic it suffices to
handle exactly invariant events.

Countability is essential and is not a technical convenience: the saturation of an almost
invariant set by an uncountable group need not be measurable, let alone almost equal to the
original set.

No measure invariance is needed for the saturation itself; `SMulInvariantMeasure` enters only
because `ErgodicSMul` extends it.

The same idea works for functions: a function that is almost everywhere invariant under each
element of a countable group acting by measure-preserving maps has an everywhere-invariant
strongly measurable representative
(`AEStronglyMeasurable.exists_stronglyMeasurable_forall_smul_eq`).
-/

public section

open Filter MeasureTheory Set

open scoped Pointwise

namespace TauCeti

namespace MeasureTheory

variable {G X : Type*} [Group G] [Countable G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] {μ : Measure X}

/-- **An almost invariant event of a countable group action is almost equal to an exactly
invariant one.**  The witness is the saturation `⋃ g, g • s`.

No invariance hypothesis on `μ` is needed. -/
theorem exists_smul_invariant_ae_eq {s : Set X} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (fun x => g • x) ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ g : G, (fun x => g • x) ⁻¹' t = t) ∧ t =ᵐ[μ] s := by
  refine ⟨⋃ g : G, g • s, .iUnion fun g => hs.const_smul g, fun g => ?_, ?_⟩
  · simp only [preimage_smul, smul_set_iUnion, smul_smul]
    exact (Equiv.mulLeft g⁻¹).surjective.iUnion_comp (· • s)
  · refine (EventuallyEqSet.countable_iUnion fun g : G => ?_).trans (iUnion_const s).eventuallyEqSet
    simpa only [preimage_smul, inv_inv] using hinv g⁻¹

/-- **Ergodicity of a countable group action can be tested on exactly invariant events**: for an
invariant measure, the action is ergodic if and only if every measurable, exactly invariant event
is null or conull.

The reverse direction is the useful one: it reduces ergodicity of a countable action to a
zero-one law for the σ-algebra of exactly invariant events. -/
theorem ergodicSMul_iff_forall_smul_invariant [SMulInvariantMeasure G X μ] :
    ErgodicSMul G X μ ↔ ∀ t : Set X, MeasurableSet t →
      (∀ g : G, (fun x => g • x) ⁻¹' t = t) → EventuallyEmptyOrUniv t (ae μ) := by
  refine ⟨fun _ t ht ht_inv => aeconst_of_forall_preimage_smul_ae_eq G ht.nullMeasurableSet
    fun g => .of_eq (ht_inv g), fun h => ⟨fun hs hinv => ?_⟩⟩
  obtain ⟨t, ht, ht_inv, hts⟩ := exists_smul_invariant_ae_eq hs hinv
  exact (h t ht ht_inv).congr hts

end MeasureTheory

end TauCeti

namespace MeasureTheory

section InvariantRepresentative

variable {G X E : Type*} [Group G] [Countable G] [MulAction G X] [MeasurableSpace X]
  [MeasurableConstSMul G X] {μ : Measure X} [SMulInvariantMeasure G X μ] [TopologicalSpace E]
  [TopologicalSpace.MetrizableSpace E] [Zero E]

/-- **Invariant representatives.** If `f` is almost everywhere strongly measurable and, for each
element `g` of a countable group of measure-preserving maps, `f (g • x) = f x` for almost every
`x`, then `f` agrees almost everywhere with a strongly measurable function `f'` satisfying
`f' (g • x) = f' x` for every `g` and every `x`. -/
theorem AEStronglyMeasurable.exists_stronglyMeasurable_forall_smul_eq {f : X → E}
    (hf : AEStronglyMeasurable f μ) (hinv : ∀ g : G, (fun x ↦ f (g • x)) =ᵐ[μ] f) :
    ∃ f' : X → E, StronglyMeasurable f' ∧ (∀ (g : G) (x : X), f' (g • x) = f' x) ∧
      f' =ᵐ[μ] f := by
  have hf₀ := hf.stronglyMeasurable_mk
  -- The points along whose orbit the representative `hf.mk f` is constant form a measurable,
  -- invariant set of full measure; `f'` is `hf.mk f` there and `0` elsewhere.
  set B : Set X := ⋂ g : G, {x | hf.mk f (g • x) = hf.mk f x} with hB_def
  have hmem (x : X) : x ∈ B ↔ ∀ g : G, hf.mk f (g • x) = hf.mk f x := by simp [hB_def]
  have hB : MeasurableSet B := .iInter fun g ↦
    (hf₀.comp_measurable (measurable_const_smul g)).measurableSet_eq_fun hf₀
  have hBsmul (g : G) {x : X} (hx : x ∈ B) : g • x ∈ B :=
    (hmem _).2 fun h ↦ by rw [smul_smul, (hmem x).1 hx, (hmem x).1 hx]
  have hBae : ∀ᵐ x ∂μ, x ∈ B := by
    simp only [hmem, ae_all_iff]
    intro g
    filter_upwards [(measurePreserving_smul g μ).quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk,
      hinv g, hf.ae_eq_mk] with x h₁ h₂ h₃
    exact h₁.symm.trans (h₂.trans h₃)
  refine ⟨B.indicator (hf.mk f), hf₀.indicator hB, fun g x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ B
    · rw [indicator_of_mem (hBsmul g hx), indicator_of_mem hx, (hmem x).1 hx g]
    · have hgx : g • x ∉ B := fun h ↦ hx (by simpa using hBsmul g⁻¹ h)
      rw [indicator_of_notMem hgx, indicator_of_notMem hx]
  · filter_upwards [hBae, hf.ae_eq_mk] with x hx h
    rw [indicator_of_mem hx, h]

end InvariantRepresentative

end MeasureTheory
