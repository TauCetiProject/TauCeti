/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.QuotSMulTop

import TauCeti.RingTheory.AdicCompletion.Basic
import TauCeti.RingTheory.AdicCompletion.Exactness
import TauCeti.RingTheory.AdicCompletion.Regular.Basic
import TauCeti.RingTheory.QuotSMulTop

/-!
# Isomorphisms modulo a regular element and principal-adic completion

Let `r` be an element of a commutative ring `R` and `M` an `R`-module on which `r` is regular.
A linear map `f : N → M` which is bijective modulo `r` is then bijective modulo every power `rⁿ`
(`IsSMulRegular.bijective_quotSMulTop_map_pow`, in `TauCeti.RingTheory.QuotSMulTop`), so it
induces an isomorphism of
`(r)`-adic completions (`IsSMulRegular.bijective_adicCompletion_map`). The typical `f` is the map
`Rᵗ → M` given by lifts of a basis of `M ⧸ r M` over `R ⧸ r`: then each `M ⧸ rⁿ M` is isomorphic
to `(R ⧸ rⁿ)ᵗ`, and the completion of `M` to the `t`-th power of the completion of `R`.

The completion of `M` only sees `M` modulo `D = ⋂ₙ rⁿ M`, the kernel of `M → M̂`
(`AdicCompletion.ker_of`). Regularity of `r` makes `D` divisible by `r`
(`IsSMulRegular.smul_iInf_pow_smul_top`). If `N` is `(r)`-adically Hausdorff, then `f` is
injective and its range `P` meets `D` trivially; multiplication by `r` is bijective on
`M ⧸ (P + D)` (`IsSMulRegular.bijective_smul_quotient_range_sup_iInf`, in
`TauCeti.RingTheory.QuotSMulTop`) and on the cokernel of `M → M̂`
(`IsSMulRegular.bijective_smul_quotient_range_adicCompletionOf`). These two quotients record what
a lattice of lifts and the completion fail to see; neither inclusion `P → M` nor `M → M̂` need
split.

When `R` is a `ℤ_(p)`-algebra and `r = p`, the intersection `D` is the maximal divisible subgroup
of `M` and every quotient on which `p` acts bijectively is uniquely divisible
(`TauCeti.GroupTheory.Divisible.LocalizationAtPrime`). For a torsion-free `ℤ_(p)`-module `T` with
`T ⧸ p T` of finite dimension `t`, these results give `T ⧸ pⁿ T ≃ (ℤ_(p) ⧸ pⁿ)ᵗ`, a completion
free of rank `t`, completion kernel `Div(T)`, a lattice `P ≃ ℤ_(p)ᵗ` of lifts with
`P ∩ Div(T) = 0`, and uniquely divisible quotients `T ⧸ (P + Div(T))` and `T̂ ⧸ T`.

## Main results

* `IsSMulRegular.bijective_adicCompletion_map`: a map bijective modulo `r` is bijective on
  completions.
* `IsSMulRegular.injective_of_injective_quotSMulTop_map`,
  `IsSMulRegular.range_inf_iInf_pow_smul_top_eq_bot`: with a Hausdorff source, the lattice of
  lifts is a copy of the source meeting `⋂ₙ rⁿ M` trivially.
* `IsSMulRegular.bijective_smul_quotient_range_adicCompletionOf`: `r` is bijective on `M̂ ⧸ M`.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, proof of Proposition VI.7.3 and
  Warning VI.7.5.
* C. Weibel, *Algebraic K-theory of rings of integers in local and global fields*, Handbook of
  K-theory, Corollary 63.
-/

public section

open Function Submodule Pointwise

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace IsSMulRegular

variable {r : R} (hM : IsSMulRegular M r) {f : N →ₗ[R] M}
include hM

/-- **Completion of a map bijective modulo a regular element.** If `r` is regular on `M` and `f`
is bijective modulo `r`, then `f` induces an isomorphism of `(r)`-adic completions. -/
theorem bijective_adicCompletion_map (hf : Bijective (QuotSMulTop.map r f)) :
    Bijective (AdicCompletion.map (Ideal.span {r}) f) := by
  refine ⟨AdicCompletion.map_injective_of_comap_pow_smul_top_le (k := 0) fun n ↦ ?_,
    AdicCompletion.map_surjective_of_mkQ_comp_surjective ?_⟩
  · simpa only [Nat.add_zero, Ideal.span_singleton_pow, ideal_span_singleton_smul] using
      hM.comap_pow_smul_top_le (QuotSMulTop.map_injective_iff_comap_smul_top_le.mp hf.1) n
  · rw [← LinearMap.range_eq_top, LinearMap.range_comp, map_mkQ_eq_top, sup_comm,
      ideal_span_singleton_smul]
    exact QuotSMulTop.map_surjective_iff_range_sup_smul_top_eq_top.mp hf.2

/-- **The lattice of lifts.** If `r` is regular on `M`, `f` is injective modulo `r`, and `N` is
`(r)`-adically Hausdorff, then `f` is injective. -/
theorem injective_of_injective_quotSMulTop_map [IsHausdorff (Ideal.span {r}) N]
    (hf : Injective (QuotSMulTop.map r f)) : Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx ↦ ?_
  have hx' : x ∈ ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R N) :=
    hM.comap_iInf_pow_smul_top_le hf (by simp [hx])
  simpa [IsHausdorff.iInf_pow_smul_top_eq_bot_of_span_singleton ‹_›] using hx'

/-- **The lattice of lifts meets `⋂ₙ rⁿ M` trivially.** If `r` is regular on `M`, `f` is
injective modulo `r`, and `N` is `(r)`-adically Hausdorff, then the range of `f` meets
`⋂ₙ rⁿ M` only in `0`. -/
theorem range_inf_iInf_pow_smul_top_eq_bot [IsHausdorff (Ideal.span {r}) N]
    (hf : Injective (QuotSMulTop.map r f)) :
    LinearMap.range f ⊓ ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨⟨x, rfl⟩, hx⟩
  have hx' : x ∈ ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R N) := hM.comap_iInf_pow_smul_top_le hf hx
  rw [IsHausdorff.iInf_pow_smul_top_eq_bot_of_span_singleton ‹_›, mem_bot] at hx'
  simp [hx']

/-- **What the completion misses.** If `r` is regular on `M`, then multiplication by `r` is
bijective on the cokernel `M̂ ⧸ M` of the map to the `(r)`-adic completion. -/
theorem bijective_smul_quotient_range_adicCompletionOf :
    Bijective fun x : AdicCompletion (Ideal.span {r}) M ⧸
        LinearMap.range (AdicCompletion.of (Ideal.span {r}) M) ↦ r • x := by
  set I := Ideal.span {r}
  have hsup :=
    AdicCompletion.range_of_sup_smul_top_eq_top (I := I) (Submodule.fg_span_singleton r) M
  rw [ideal_span_singleton_smul] at hsup
  refine ⟨TauCeti.isSMulRegular_quotient_range_of_injective_quotSMulTop_map hM.adicCompletion ?_,
    surjective_smul_quotient_of_sup_smul_top_eq_top hsup le_rfl⟩
  · -- `of m ∈ r M̂` forces `m ∈ r M`.
    refine QuotSMulTop.map_injective_iff_comap_smul_top_le.mpr ?_
    simpa only [I, ideal_span_singleton_smul] using
      AdicCompletion.comap_of_smul_top_le (Submodule.fg_span_singleton r) M

end IsSMulRegular
