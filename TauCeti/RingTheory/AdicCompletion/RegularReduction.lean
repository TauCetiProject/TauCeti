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
import TauCeti.RingTheory.AdicCompletion.Regular
import TauCeti.RingTheory.QuotSMulTop

/-!
# Isomorphisms modulo a regular element and principal-adic completion

Let `r` be an element of a commutative ring `R` and `M` an `R`-module on which `r` is regular.
A linear map `f : N → M` which is bijective modulo `r` is then bijective modulo every power `rⁿ`
(`IsSMulRegular.bijective_quotSMulTop_map_pow`), so it induces an isomorphism of
`(r)`-adic completions (`IsSMulRegular.bijective_adicCompletion_map`). The typical `f` is the map
`Rᵗ → M` given by lifts of a basis of `M ⧸ r M` over `R ⧸ r`: then each `M ⧸ rⁿ M` is isomorphic
to `(R ⧸ rⁿ)ᵗ`, and the completion of `M` to the `t`-th power of the completion of `R`.

The completion of `M` only sees `M` modulo `D = ⋂ₙ rⁿ M`, the kernel of `M → M̂`
(`AdicCompletion.ker_of`). Regularity of `r` makes `D` divisible by `r`
(`IsSMulRegular.smul_iInf_pow_smul_top`). If `N` is `(r)`-adically Hausdorff, then `f` is
injective and its range `P` meets `D` trivially; multiplication by `r` is bijective on
`M ⧸ (P + D)` (`IsSMulRegular.bijective_smul_quotient_range_sup_iInf`) and on the cokernel of
`M → M̂` (`IsSMulRegular.bijective_smul_quotient_range_of`). These two quotients record what a
lattice of lifts and the completion fail to see; neither inclusion `P → M` nor `M → M̂` need split.

When `R` is a `ℤ_(p)`-algebra and `r = p`, the intersection `D` is the maximal divisible subgroup
of `M` and every quotient on which `p` acts bijectively is uniquely divisible
(`TauCeti.GroupTheory.Divisible.LocalizationAtPrime`). For a torsion-free `ℤ_(p)`-module `T` with
`T ⧸ p T` of finite dimension `t`, these results give `T ⧸ pⁿ T ≃ (ℤ_(p) ⧸ pⁿ)ᵗ`, a completion
free of rank `t`, completion kernel `Div(T)`, a lattice `P ≃ ℤ_(p)ᵗ` of lifts with
`P ∩ Div(T) = 0`, and uniquely divisible quotients `T ⧸ (P + Div(T))` and `T̂ ⧸ T`.

## Main results

* `IsSMulRegular.comap_pow_smul_top_le`: injectivity modulo `r` propagates to every `rⁿ`.
* `IsSMulRegular.bijective_quotSMulTop_map_pow`, `IsSMulRegular.bijective_adicCompletion_map`:
  a map bijective modulo `r` is bijective modulo every `rⁿ` and on completions.
* `IsSMulRegular.injective_of_injective_quotSMulTop_map`,
  `IsSMulRegular.range_inf_iInf_pow_smul_top_eq_bot`: with a Hausdorff source, the lattice of
  lifts is a copy of the source meeting `⋂ₙ rⁿ M` trivially.
* `IsSMulRegular.bijective_smul_quotient_range_sup_iInf`,
  `IsSMulRegular.bijective_smul_quotient_range_of`: `r` is bijective on `M ⧸ (P + ⋂ₙ rⁿ M)` and
  on `M̂ ⧸ M`.

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

/-- **Injectivity modulo `rⁿ`.** If `r` is regular on `M` and `f x ∈ r M` forces `x ∈ r N`, then
`f x ∈ rⁿ M` forces `x ∈ rⁿ N`, for every `n`. -/
theorem comap_pow_smul_top_le (hf : (r • ⊤ : Submodule R M).comap f ≤ r • ⊤) (n : ℕ) :
    (r ^ n • ⊤ : Submodule R M).comap f ≤ r ^ n • ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro x hx
    simp only [mem_comap, mem_smul_pointwise_iff_exists, mem_top, true_and] at hx ⊢
    obtain ⟨y, hy⟩ := hx
    -- `f x = r • (rⁿ • y)`, so `x = r • x'`; cancelling `r` puts `f x'` in `rⁿ M`.
    have hfx : f x ∈ (r • ⊤ : Submodule R M) := (mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨r ^ n • y, trivial, by rw [← hy, pow_succ', mul_smul]⟩
    obtain ⟨x', -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp (hf hfx)
    have hx' : f x' = r ^ n • y := hM <| by
      beta_reduce
      rw [← map_smul, ← hy, pow_succ', mul_smul]
    obtain ⟨z, -, hz⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp <| ih <|
      mem_comap.mpr <| (mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, trivial, hx'.symm⟩
    exact ⟨z, by rw [← hz, pow_succ', mul_smul]⟩

/-- **Bijectivity modulo `rⁿ`.** If `r` is regular on `M` and `f` is bijective modulo `r`, then
`f` is bijective modulo every power `rⁿ`. -/
theorem bijective_quotSMulTop_map_pow (hf : Bijective (QuotSMulTop.map r f)) (n : ℕ) :
    Bijective (QuotSMulTop.map (r ^ n) f) := by
  refine ⟨QuotSMulTop.map_injective_iff_comap_smul_top_le.mpr <|
    hM.comap_pow_smul_top_le (QuotSMulTop.map_injective_iff_comap_smul_top_le.mp hf.1) n,
    QuotSMulTop.map_surjective_iff_range_sup_smul_top_eq_top.mpr ?_⟩
  have h := sup_pow_smul_top_eq_top (I := Ideal.span {r}) (P := LinearMap.range f) (by
    rw [ideal_span_singleton_smul]
    exact QuotSMulTop.map_surjective_iff_range_sup_smul_top_eq_top.mp hf.2) n
  rwa [Ideal.span_singleton_pow, ideal_span_singleton_smul] at h

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

/-- If `r` is regular on `M` and `f` is injective modulo `r`, then `f x ∈ ⋂ₙ rⁿ M` forces
`x ∈ ⋂ₙ rⁿ N`. -/
theorem comap_iInf_pow_smul_top_le (hf : Injective (QuotSMulTop.map r f)) :
    (⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M)).comap f ≤ ⨅ n : ℕ, r ^ n • ⊤ := by
  rw [comap_iInf]
  exact iInf_mono <|
    hM.comap_pow_smul_top_le (QuotSMulTop.map_injective_iff_comap_smul_top_le.mp hf)

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

/-- **What the lattice of lifts misses.** If `r` is regular on `M` and `f` is bijective modulo
`r`, then multiplication by `r` is bijective on `M ⧸ (range f + ⋂ₙ rⁿ M)`. -/
theorem bijective_smul_quotient_range_sup_iInf (hf : Bijective (QuotSMulTop.map r f)) :
    Bijective fun x : M ⧸ (LinearMap.range f ⊔ ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M)) ↦ r • x := by
  refine ⟨(isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr fun x hx ↦ ?_, ?_⟩
  · -- Write `r • x = f a + d`; then `f a ∈ r M`, so `a = r • a'`, and `d = r • d'` with `d' ∈ D`.
    obtain ⟨_, ⟨a, rfl⟩, d, hd, had⟩ := mem_sup.mp hx
    have hfa : f a ∈ (r • ⊤ : Submodule R M) := by
      have hd1 : d ∈ (r • ⊤ : Submodule R M) := by
        simpa using (Submodule.mem_iInf _).mp hd 1
      rw [show f a = r • x - d by rw [← had, add_sub_cancel_right]]
      exact sub_mem (smul_mem_pointwise_smul _ _ _ trivial) hd1
    obtain ⟨a', -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp <|
      (QuotSMulTop.map_injective_iff_comap_smul_top_le.mp hf.1) hfa
    obtain ⟨d', hd', rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp
      (hM.smul_iInf_pow_smul_top.ge hd)
    have hx' : x = f a' + d' := hM (by beta_reduce; rw [smul_add, ← map_smul, had])
    exact hx' ▸ add_mem_sup (LinearMap.mem_range_self f a') hd'
  · -- Every class is `r` times a class, since `range f + r M = M`.
    exact surjective_smul_quotient_of_sup_smul_top_eq_top
      (QuotSMulTop.map_surjective_iff_range_sup_smul_top_eq_top.mp hf.2) le_sup_left

/-- **What the completion misses.** If `r` is regular on `M`, then multiplication by `r` is
bijective on the cokernel `M̂ ⧸ M` of the map to the `(r)`-adic completion. -/
theorem bijective_smul_quotient_range_of :
    Bijective fun x : AdicCompletion (Ideal.span {r}) M ⧸
        LinearMap.range (AdicCompletion.of (Ideal.span {r}) M) ↦ r • x := by
  set I := Ideal.span {r}
  have hsup :=
    AdicCompletion.range_of_sup_smul_top_eq_top (I := I) (Submodule.fg_span_singleton r) M
  rw [ideal_span_singleton_smul] at hsup
  refine ⟨TauCeti.isSMulRegular_quotient_range_of_injective_quotSMulTop_map hM.adicCompletion ?_,
    surjective_smul_quotient_of_sup_smul_top_eq_top hsup le_rfl⟩
  · -- `of m ∈ r M̂` forces `m ∈ r M`, by evaluating at level one.
    refine QuotSMulTop.map_injective_iff_comap_smul_top_le.mpr fun m hm ↦ ?_
    obtain ⟨y, -, hy⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hm
    have h1 := congrArg (AdicCompletion.eval I M 1) hy
    rw [map_smul, AdicCompletion.eval_of] at h1
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M 1 y)
    rw [← hy₁, ← Submodule.Quotient.mk_smul, mkQ_apply, Submodule.Quotient.eq, pow_one,
      ideal_span_singleton_smul] at h1
    simpa using sub_mem (smul_mem_pointwise_smul y₁ r ⊤ trivial) h1

end IsSMulRegular
