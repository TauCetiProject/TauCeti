/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness
-- Proof-only: identify its ideal-linear quotient map with Mathlib's `reduceModIdeal`.
import all TauCeti.RingTheory.QuotSMulTop

/-!
# Exactness of principal-adic completion with a regular last term

If `0 → M → N → P → 0` is short exact and multiplication by `r` is injective on `P`, then
completion for `(r)` preserves short exactness. There are no Noetherian or finite-generation
assumptions. In particular, this applies to p-adic completion of a short exact sequence with
p-torsion-free last term.
Surjectivity on the right is already supplied by `AdicCompletion.map_surjective`.

More generally, completion preserves a right exact sequence when the first map is injective
modulo every power of the defining ideal. The unique preimages of a compatible family in the
kernel are automatically compatible. For a principal ideal, regularity on the last term gives
this injectivity for the range inclusion by `Ideal.mapQSMulTop_span_singleton_injective`.
Surjectivity of completion onto the completed range then gives middle exactness without an
injectivity assumption on the original first map.

The maps and compatible-residue model are Mathlib's `AdicCompletion`, due to Judith Ludwig
and Christian Merten. The finite-level exactness results are those of
`TauCeti.RingTheory.QuotSMulTop`; no new completion carrier is introduced.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- If a linear map is injective modulo every power of an ideal, its completion is injective. -/
theorem map_injective_of_reduceModIdeal_injective
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Injective (map I f) := by
  intro x y h
  exact AdicCompletion.ext fun n ↦ hf n (by
    simpa only [map_val_apply] using congrArg (fun z ↦ z.val n) h)

/-- Completion preserves a right exact sequence if its first map is injective modulo every
power of the defining ideal. No finiteness hypothesis is needed. -/
theorem map_exact_of_reduceModIdeal_injective
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Exact (map I f) (map I g) := by
  classical
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ fun y hy ↦ ?_
  · rw [map_comp, hfg.linearMap_comp_eq_zero, map_zero]
  have hpre (n : ℕ) : ∃ x, f.reduceModIdeal (I ^ n) x = y.val n := by
    -- The ideal-linear reduction and `reduceModIdeal` are the same quotient map.
    apply (Ideal.mapQSMulTop_exact (I ^ n) hfg hg (y.val n)).mp
    have hz : g.reduceModIdeal (I ^ n) (y.val n) = 0 :=
      congrArg (fun z ↦ z.val n) hy
    exact hz
  choose x hx using hpre
  have hcompat {m n : ℕ} (hmn : m ≤ n) : transitionMap I M hmn (x n) = x m := by
    apply hf m
    have hnat := LinearMap.congr_fun (transitionMap_comp_reduceModIdeal I f hmn) (x n)
    simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hx, y.property hmn]
      using hnat.symm
  exact ⟨⟨x, hcompat⟩, AdicCompletion.ext fun n ↦ hx n⟩

/-- A short exact sequence whose last term is `r`-torsion-free remains injective on the left
after `(r)`-adic completion. The modules need not be finite. -/
theorem map_span_singleton_injective_of_isSMulRegular {r : R}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hr : IsSMulRegular P r) :
    Function.Injective (map (Ideal.span {r}) f) := by
  apply map_injective_of_reduceModIdeal_injective
  intro n
  rw [Ideal.span_singleton_pow]
  -- Both reductions are induced by `f` on the quotient by `rⁿ`.
  exact Ideal.mapQSMulTop_span_singleton_injective hfg hf (hr.pow n)

/-- Principal-adic completion preserves a right exact sequence when the parameter acts
injectively on the last term, without any Noetherian or finite-generation assumption. Together
with `map_span_singleton_injective_of_isSMulRegular` and `map_surjective`, this also gives all
three parts of short exactness when the first map is injective. -/
theorem map_span_singleton_exact_of_isSMulRegular {r : R}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (hr : IsSMulRegular P r) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) := by
  have hfg' : Function.Exact f.range.subtype g := by
    apply f.surjective_rangeRestrict.comp_exact_iff_exact.mp
    simpa only [LinearMap.subtype_comp_rangeRestrict] using hfg
  rw [← f.subtype_comp_rangeRestrict, ← map_comp]
  apply (map_surjective _ f.surjective_rangeRestrict).comp_exact_iff_exact.mpr
  apply map_exact_of_reduceModIdeal_injective hfg' hg
  intro n
  rw [Ideal.span_singleton_pow]
  -- Regularity of `rⁿ` gives injectivity of the finite-level range inclusion.
  exact Ideal.mapQSMulTop_span_singleton_injective hfg' f.range.injective_subtype (hr.pow n)

end AdicCompletion
