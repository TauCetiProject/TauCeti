/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Radical

import Mathlib.RingTheory.Nakayama
import TauCeti.RingTheory.Ideal.Extended

/-!
# Nakayama's lemma for an idempotent

An idempotent endomorphism `e` of a finitely generated module `M` over a not necessarily
commutative ring `A` whose image lies in `I • M`, for an ideal `I` in the Jacobson radical, is
zero: applying `e` to `range e ≤ I • M` gives `range e ≤ I • range e`, and Nakayama's lemma, in the
form of Mathlib's `Submodule.FG.eq_bot_of_le_jacobson_smul`, concludes.

Let `T` be a not necessarily commutative algebra over a commutative ring `S`, `J` an ideal of `S`
in the Jacobson radical, and `e` an idempotent of `T` whose summand `e T` is a finitely generated
`S`-module. If `e T ⊆ S e + JT`, then `e T = S e`: applying left multiplication by `e` to
`e T ⊆ S e + JT` gives `e T ⊆ S e + J • e T`, and Nakayama's lemma, in the form of Mathlib's
`Submodule.le_of_le_smul_of_le_jacobson`, concludes.

The extended ideal `JT` is read as `J • T` through `Ideal.mem_map_algebraMap_iff`, which does not
need `T` to be commutative.

## Main results

* `IsIdempotentElem.eq_zero_of_range_le_smul_top`: an idempotent endomorphism of a finitely
  generated module with image in `I • ⊤`, for `I` in the Jacobson radical, is zero.
* `IsIdempotentElem.exists_smul_eq_mul_of_mul_sub_smul_mem`: in a not necessarily commutative
  `S`-algebra `T`, an idempotent `e` with `e T` finitely generated over `S` and
  `e T ⊆ S e + JT`, for `J` in the Jacobson radical of `S`, has `e T = S e`.
-/

public section

/-- **Nakayama's lemma for an idempotent endomorphism.** An idempotent endomorphism of a finitely
generated module over a not necessarily commutative ring `A` whose image lies in `I • ⊤`, for an
ideal `I` in the Jacobson radical of `A`, is zero. -/
theorem IsIdempotentElem.eq_zero_of_range_le_smul_top {A M : Type*} [Ring A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] {I : Ideal A} (hI : I ≤ Ring.jacobson A)
    {e : Module.End A M} (he : IsIdempotentElem e) (h : LinearMap.range e ≤ I • ⊤) : e = 0 := by
  -- Applying `e` to `range e ≤ I • ⊤` gives `range e ≤ I • range e`.
  have hN : LinearMap.range e ≤ Ring.jacobson A • LinearMap.range e := by
    rintro _ ⟨x, rfl⟩
    have hmem : e (e x) ∈ (I • (⊤ : Submodule A M)).map e := ⟨e x, h ⟨x, rfl⟩, rfl⟩
    rw [← mul_apply_eq_comp, he.eq, Submodule.map_smul'', ← LinearMap.range_eq_map] at hmem
    exact Submodule.smul_mono_left hI hmem
  have hfg : (LinearMap.range e).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map e
  exact LinearMap.range_eq_bot.mp (Submodule.FG.eq_bot_of_le_jacobson_smul hfg hN)

/-- **Nakayama's lemma for an idempotent.** Let `T` be a not necessarily commutative `S`-algebra,
`J` an ideal of `S` in the Jacobson radical, and `e` an idempotent of `T` such that `e T` is a
finitely generated `S`-module. If `e T ⊆ S e + JT`, then `e T = S e`. -/
theorem IsIdempotentElem.exists_smul_eq_mul_of_mul_sub_smul_mem {S T : Type*} [CommRing S]
    [Ring T] [Algebra S T] {J : Ideal S} (hJ : J ≤ Ring.jacobson S) {e : T}
    (he : IsIdempotentElem e) (hfg : (LinearMap.mulLeft S e).range.FG)
    (h : ∀ x : T, ∃ s : S, e * x - s • e ∈ J.map (algebraMap S T)) (x : T) :
    ∃ s : S, s • e = e * x := by
  let f := LinearMap.mulLeft S e
  have hle : LinearMap.range f ≤ S ∙ e := by
    refine Submodule.le_of_le_smul_of_le_jacobson hfg hJ fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz
    obtain ⟨s, hs⟩ := h y
    have hmem : f (e * y - s • e) ∈ J • LinearMap.range f := by
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem ((Ideal.mem_map_algebraMap_iff J).mp hs)
    have hy : f y = s • e + f (e * y - s • e) := by
      simp only [f, LinearMap.mulLeft_apply, mul_sub, ← mul_assoc, mul_smul_comm, he.eq]
      abel
    rw [hy]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self e)) hmem
  simpa only [f, LinearMap.mulLeft_apply] using
    Submodule.mem_span_singleton.mp (hle (LinearMap.mem_range_self f x))
