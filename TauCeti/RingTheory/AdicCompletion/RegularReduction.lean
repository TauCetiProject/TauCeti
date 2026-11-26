/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.GroupTheory.Divisible.MaxDivisible

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

When `R` is a `ℤ_(p)`-algebra, that is when the integers prime to `p` are units of `R`, and
`r = p`, the intersection `D` is the maximal divisible subgroup of `M`
(`TauCeti.AddCommGroup.maxDivisible_eq_toAddSubgroup_iInf_pow_smul_top`), and every quotient on
which `p` acts bijectively is uniquely divisible, i.e. a `ℚ`-vector space
(`TauCeti.bijective_nsmul_of_bijective_smul_prime`). For a torsion-free `ℤ_(p)`-module `T` with
`T ⧸ p T` of finite dimension `t`, these results give `T ⧸ pⁿ T ≃ (ℤ_(p) ⧸ pⁿ)ᵗ`, a completion
free of rank `t`, completion kernel `Div(T)`, a lattice `P ≃ ℤ_(p)ᵗ` of lifts with
`P ∩ Div(T) = 0`, and uniquely divisible quotients `T ⧸ (P + Div(T))` and `T̂ ⧸ T`.

## Main results

* `Submodule.sup_pow_smul_top_eq_top`: `P + I M = M` implies `P + Iⁿ M = M`.
* `IsSMulRegular.comap_pow_smul_top_le`: injectivity modulo `r` propagates to every `rⁿ`.
* `IsSMulRegular.bijective_quotSMulTop_map_pow`, `IsSMulRegular.bijective_adicCompletion_map`:
  a map bijective modulo `r` is bijective modulo every `rⁿ` and on completions.
* `IsSMulRegular.injective_of_injective_quotSMulTop_map`,
  `IsSMulRegular.range_inf_iInf_pow_smul_top_eq_bot`: with a Hausdorff source, the lattice of
  lifts is a copy of the source meeting `⋂ₙ rⁿ M` trivially.
* `AdicCompletion.ker_of`, `AdicCompletion.ker_of_span_singleton`: the kernel of `M → M̂` is
  `⋂ₙ Iⁿ M`.
* `IsSMulRegular.bijective_smul_quotient_range_sup_iInf`,
  `IsSMulRegular.bijective_smul_quotient_range_of`: `r` is bijective on `M ⧸ (P + ⋂ₙ rⁿ M)` and
  on `M̂ ⧸ M`.
* `TauCeti.AddCommGroup.maxDivisible_eq_toAddSubgroup_iInf_pow_smul_top`: over a `ℤ_(p)`-algebra,
  `Div(M) = ⋂ₙ pⁿ M` for `p`-torsion-free `M`.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, proof of Proposition VI.7.3 and
  Warning VI.7.5.
* C. Weibel, *Algebraic K-theory of rings of integers in local and global fields*, Handbook of
  K-theory, Corollary 63.
-/

public section

open Function Submodule Pointwise

namespace Submodule

/-- If `P` and `I M` together span `M`, then so do `P` and `Iⁿ M`, for every `n`. -/
theorem sup_pow_smul_top_eq_top {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {I : Ideal R} {P : Submodule R M} (h : P ⊔ I • ⊤ = ⊤)
    (n : ℕ) : P ⊔ I ^ n • ⊤ = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine eq_top_iff.mpr ?_
    calc (⊤ : Submodule R M) = P ⊔ I ^ n • (P ⊔ I • ⊤) := by rw [h, ih]
      _ ≤ P ⊔ I ^ (n + 1) • ⊤ := by
        rw [smul_sup, ← sup_assoc, pow_succ, Submodule.mul_smul]
        exact sup_le_sup_right (sup_le le_rfl smul_le_right) _

end Submodule

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace QuotSMulTop

variable {r : R} {f : N →ₗ[R] M}

/-- The reduction of `f` modulo `r` is injective exactly when `f x ∈ r M` forces `x ∈ r N`. -/
theorem map_injective_iff_comap_smul_top_le :
    Injective (QuotSMulTop.map r f) ↔ (r • ⊤ : Submodule R M).comap f ≤ r • ⊤ := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_⟩
  · refine (Submodule.Quotient.mk_eq_zero _).mp (h ?_)
    rwa [map_apply_mk, map_zero, Submodule.Quotient.mk_eq_zero]
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [map_apply_mk, Submodule.Quotient.mk_eq_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h hx)

/-- The reduction of `f` modulo `r` is surjective exactly when the range of `f` and `r M` span
`M`. -/
theorem map_surjective_iff_range_sup_smul_top_eq_top :
    Surjective (QuotSMulTop.map r f) ↔ LinearMap.range f ⊔ r • ⊤ = ⊤ := by
  rw [← LinearMap.range_eq_top, sup_comm, ← map_mkQ_eq_top, ← LinearMap.range_comp,
    ← map_comp_mkQ, LinearMap.range_comp, LinearMap.range_eq_top.mpr (mkQ_surjective _),
    Submodule.map_top]

end QuotSMulTop

namespace AdicCompletion

/-- The kernel of the map from a module to its `I`-adic completion is `⋂ₙ Iⁿ M`. -/
@[simp]
theorem ker_of (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    LinearMap.ker (of I M) = ⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) := by
  ext x
  simp only [LinearMap.mem_ker, mem_iInf]
  refine ⟨fun hx n ↦ ?_, fun hx ↦ AdicCompletion.ext fun n ↦ ?_⟩
  · have := congrArg (fun y ↦ y.val n) hx
    simpa [of_apply, Submodule.Quotient.mk_eq_zero] using this
  · simpa [of_apply, Submodule.Quotient.mk_eq_zero] using hx n

/-- For a finitely generated ideal `I`, the image of `M` and `I M̂` span the `I`-adic
completion `M̂`. -/
theorem range_of_sup_smul_top_eq_top {I : Ideal R} (hI : I.FG) (M : Type*) [AddCommGroup M]
    [Module R M] : LinearMap.range (of I M) ⊔ I • ⊤ = ⊤ := by
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (eval I M 1 y)
  have hy : y - of I M m ∈ I • (⊤ : Submodule R (AdicCompletion I M)) := by
    have h : (I • ⊤ : Submodule R (AdicCompletion I M)) = LinearMap.ker (eval I M 1) := by
      simpa using pow_smul_top_eq_ker_eval (M := M) (n := 1) hI
    rw [h, LinearMap.mem_ker, map_sub, eval_of, ← hm, mkQ_apply, sub_self]
  simpa using add_mem_sup (LinearMap.mem_range_self (of I M) m) hy

/-- The kernel of the map from a module to its `(r)`-adic completion is `⋂ₙ rⁿ M`. -/
theorem ker_of_span_singleton (r : R) (M : Type*) [AddCommGroup M] [Module R M] :
    LinearMap.ker (of (Ideal.span {r}) M) = ⨅ n : ℕ, r ^ n • (⊤ : Submodule R M) := by
  simp [Ideal.span_singleton_pow, ideal_span_singleton_smul]

end AdicCompletion

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
  have h0 := IsHausdorff.iInf_pow_smul ‹IsHausdorff (Ideal.span {r}) N›
  simp only [Ideal.span_singleton_pow, ideal_span_singleton_smul] at h0
  simpa [h0] using hx'

/-- **The lattice of lifts meets `⋂ₙ rⁿ M` trivially.** If `r` is regular on `M`, `f` is
injective modulo `r`, and `N` is `(r)`-adically Hausdorff, then the range of `f` meets
`⋂ₙ rⁿ M` only in `0`. -/
theorem range_inf_iInf_pow_smul_top_eq_bot [IsHausdorff (Ideal.span {r}) N]
    (hf : Injective (QuotSMulTop.map r f)) :
    LinearMap.range f ⊓ ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨⟨x, rfl⟩, hx⟩
  have hx' : x ∈ ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R N) := hM.comap_iInf_pow_smul_top_le hf hx
  have h0 := IsHausdorff.iInf_pow_smul ‹IsHausdorff (Ideal.span {r}) N›
  simp only [Ideal.span_singleton_pow, ideal_span_singleton_smul] at h0
  rw [h0, mem_bot] at hx'
  simp [hx']

/-- **`⋂ₙ rⁿ M` is divisible by `r`.** If `r` is regular on `M`, every element of `⋂ₙ rⁿ M` is
`r` times an element of `⋂ₙ rⁿ M`. -/
theorem smul_iInf_pow_smul_top :
    r • ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M) = ⨅ n : ℕ, r ^ n • ⊤ := by
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨y, hy, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
    obtain ⟨z, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp ((Submodule.mem_iInf _).mp hy n)
    exact (mem_smul_pointwise_iff_exists _ _ _).mpr ⟨r • z, trivial, smul_comm _ _ _⟩
  · simp only [Submodule.mem_iInf, mem_smul_pointwise_iff_exists, mem_top, true_and] at hx
    obtain ⟨y, hy⟩ := hx 1
    rw [pow_one] at hy
    refine ⟨y, (Submodule.mem_iInf _).mpr fun n ↦ ?_, hy⟩
    -- `x = rⁿ⁺¹ • z`, and cancelling `r` from `r • y = r • (rⁿ • z)` gives `y = rⁿ • z`.
    obtain ⟨z, hz⟩ := hx (n + 1)
    refine (mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z, trivial, hM ?_⟩
    beta_reduce
    rw [hy, ← hz, pow_succ', mul_smul]

/-- **What the lattice of lifts misses.** If `r` is regular on `M` and `f` is bijective modulo
`r`, then multiplication by `r` is bijective on `M ⧸ (range f + ⋂ₙ rⁿ M)`. -/
theorem bijective_smul_quotient_range_sup_iInf (hf : Bijective (QuotSMulTop.map r f)) :
    Bijective fun x : M ⧸ (LinearMap.range f ⊔ ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M)) ↦ r • x := by
  refine ⟨(isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr fun x hx ↦ ?_, fun x ↦ ?_⟩
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
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx : x ∈ LinearMap.range f ⊔ (r • ⊤ : Submodule R M) := by
      rw [QuotSMulTop.map_surjective_iff_range_sup_smul_top_eq_top.mp hf.2]
      trivial
    obtain ⟨_, ⟨a, rfl⟩, z, hz, rfl⟩ := mem_sup.mp hx
    obtain ⟨y, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hz
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    beta_reduce
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, add_sub_cancel_right]
    exact mem_sup_left (LinearMap.mem_range_self f a)

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
    fun x ↦ ?_⟩
  · -- `of m ∈ r M̂` forces `m ∈ r M`, by evaluating at level one.
    refine QuotSMulTop.map_injective_iff_comap_smul_top_le.mpr fun m hm ↦ ?_
    obtain ⟨y, -, hy⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hm
    have h1 := congrArg (AdicCompletion.eval I M 1) hy
    rw [map_smul, AdicCompletion.eval_of] at h1
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I M 1 y)
    rw [← hy₁, ← Submodule.Quotient.mk_smul, mkQ_apply, Submodule.Quotient.eq, pow_one,
      ideal_span_singleton_smul] at h1
    simpa using sub_mem (smul_mem_pointwise_smul y₁ r ⊤ trivial) h1
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ LinearMap.range (AdicCompletion.of I M) ⊔ (r • ⊤ : Submodule R _) := by
      rw [hsup]
      exact mem_top
    obtain ⟨_, ⟨a, rfl⟩, w, hw, rfl⟩ := mem_sup.mp hy
    obtain ⟨z, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hw
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    beta_reduce
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, add_sub_cancel_right]
    exact LinearMap.mem_range_self _ a

end IsSMulRegular

namespace TauCeti

variable {p : ℕ}

/-- **Unique divisibility over `ℤ_(p)`.** Let `R` be a ring in which the integers prime to the
prime `p` are units, and `Q` an `R`-module on which multiplication by `p` is bijective. Then
multiplication by every nonzero integer is bijective on `Q`: `Q` is uniquely divisible, i.e. a
`ℚ`-vector space. -/
theorem bijective_nsmul_of_bijective_smul_prime (hp : p.Prime)
    (hR : ∀ n : ℕ, n.Coprime p → IsUnit (n : R)) {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hQ : Bijective fun x : Q ↦ (p : R) • x) {n : ℕ} (hn : n ≠ 0) :
    Bijective fun x : Q ↦ n • x := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hu : IsUnit ((m : R)) := hR m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  have hpa (k : ℕ) : Bijective fun x : Q ↦ (p : R) ^ k • x := by
    induction k with
    | zero =>
      simp only [pow_zero, one_smul]
      exact bijective_id
    | succ k ih =>
      simp only [pow_succ', mul_smul]
      exact hQ.comp ih
  have hmu : Bijective fun x : Q ↦ (m : R) • x :=
    (Module.End.isUnit_iff _).mp ((hu.map (algebraMap R (Module.End R Q))))
  convert (hpa a).comp hmu using 1
  ext x
  simp [← Nat.cast_smul_eq_nsmul R, mul_smul]

end TauCeti

namespace TauCeti.AddCommGroup

variable {p : ℕ}

/-- **The maximal divisible subgroup over `ℤ_(p)`.** Let `R` be a ring in which the integers
prime to the prime `p` are units, and `M` an `R`-module on which `p` is regular. Then the maximal
divisible subgroup of `M` is `⋂ₙ pⁿ M`, the kernel of the map to the `(p)`-adic completion. -/
theorem maxDivisible_eq_toAddSubgroup_iInf_pow_smul_top (hp : p.Prime)
    (hR : ∀ n : ℕ, n.Coprime p → IsUnit (n : R)) (hM : IsSMulRegular M (p : R)) :
    maxDivisible M = (⨅ n : ℕ, ((p : R) ^ n • ⊤ : Submodule R M)).toAddSubgroup := by
  set D := ⨅ n : ℕ, ((p : R) ^ n • ⊤ : Submodule R M)
  refine le_antisymm (fun x hx ↦ ?_)
    (AddSubgroup.IsDivisible.le_maxDivisible <| AddSubgroup.isDivisible_def.mpr fun n hn x hx ↦ ?_)
  · -- `x ∈ Div(M)` is a `pⁿ`-fold multiple for every `n`.
    refine (mem_iInf _).mpr fun n ↦ ?_
    obtain ⟨y, -, hy⟩ := exists_mem_maxDivisible_nsmul_eq hx (pow_ne_zero n hp.ne_zero)
    exact (mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨y, trivial, by rw [← hy, ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow]⟩
  · -- Write `n = pᵃ m` with `p ∤ m`: `D` is divisible by `pᵃ`, and `m` acts invertibly on `M`,
    -- preserving `D`.
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
    have hu : IsUnit ((m : R)) := hR m ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
    have hDp : ∀ k : ℕ, ∀ y ∈ D, ∃ z ∈ D, (p : R) ^ k • z = y := by
      intro k
      induction k with
      | zero => exact fun y hy ↦ ⟨y, hy, by simp⟩
      | succ k ih =>
        intro y hy
        obtain ⟨z, hz, rfl⟩ := ih y hy
        obtain ⟨w, hw, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp
          (hM.smul_iInf_pow_smul_top.ge hz)
        exact ⟨w, hw, by rw [pow_succ, mul_smul]⟩
    obtain ⟨z, hz, rfl⟩ := hDp a x hx
    have hmz : (m : R) • (hu.unit⁻¹ • z) = z := by
      rw [Units.smul_def, smul_smul, IsUnit.mul_val_inv, one_smul]
    refine ⟨hu.unit⁻¹ • z, D.smul_of_tower_mem _ hz, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul R, Nat.cast_mul, Nat.cast_pow, mul_smul, hmz]

end TauCeti.AddCommGroup
