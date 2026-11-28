/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module

/-!
# Classical completeness of cokernels at a regular scalar

* `TauCeti.IsDerivedComplete.isHausdorff_span_singleton_of_isSMulRegular`: a derived
  `(f)`-complete module is `(f)`-adically separated if `f` acts injectively. In this case the
  intersection of the powers is divisible by `f`, so it vanishes by
  `TauCeti.IsDerivedComplete.eq_bot_of_le_pointwise_smul`.
* `TauCeti.IsDerivedComplete.isAdicComplete_quotient_range_of_isSMulRegular`: the cokernel
  of a map of derived `(f)`-complete modules is classically `(f)`-adically complete if `f`
  acts injectively on it. The derived completeness input is
  `TauCeti.IsDerivedComplete.quotient_range`.

In particular a quotient by multiplication by one scalar stays complete if the adic generator
is regular on the quotient. See Bhatt, Ma, Patakfalvi, Schwede, Tucker, Waldron and Witaszek,
*Globally +-regular varieties and the minimal model program for threefolds in mixed
characteristic*, Lemma 2.8.
-/

public section

open AdicCompletion Pointwise

namespace TauCeti.IsDerivedComplete

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {f : R}

/-- A derived `(f)`-complete module on which `f` acts injectively is `(f)`-adically Hausdorff. -/
theorem isHausdorff_span_singleton_of_isSMulRegular
    (hM : IsDerivedComplete (Ideal.span {f}) M) (hf : IsSMulRegular M f) :
    IsHausdorff (Ideal.span {f}) M := by
  let K : Submodule R M := ⨅ n : ℕ, f ^ n • ⊤
  have hK : K ≤ f • K := by
    intro x hx
    have hxpow := (Submodule.mem_iInf _).1 hx
    have hx₁ : x ∈ f • (⊤ : Submodule R M) := by
      simpa only [pow_one] using hxpow 1
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx₁
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, ?_, hy⟩
    refine (Submodule.mem_iInf _).2 fun n ↦ ?_
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hxpow (n + 1))
    rw [pow_succ', mul_smul, ← hy] at hz
    exact (hf hz) ▸ Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hzero : K = ⊥ := hM.eq_bot_of_le_pointwise_smul (Ideal.mem_span_singleton_self f) hK
  refine ⟨fun x hx ↦ ?_⟩
  have hxK : x ∈ K := by
    refine (Submodule.mem_iInf _).2 fun n ↦ ?_
    simpa only [SModEq.zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      using hx n
  rwa [hzero, Submodule.mem_bot] at hxK

/-- The cokernel of a map between derived `(f)`-complete modules is classically
`(f)`-adically complete if `f` acts injectively on it. This applies to `N / gN`
by taking the map to be multiplication by `g` on `N`. -/
theorem isAdicComplete_quotient_range_of_isSMulRegular
    (hM : IsDerivedComplete (Ideal.span {f}) M) (hN : IsDerivedComplete (Ideal.span {f}) N)
    (g : M →ₗ[R] N) (hf : IsSMulRegular (N ⧸ LinearMap.range g) f) :
    IsAdicComplete (Ideal.span {f}) (N ⧸ LinearMap.range g) := by
  have hQ : IsDerivedComplete (Ideal.span {f}) (N ⧸ LinearMap.range g) :=
    hM.quotient_range hN g
  exact (isAdicComplete_iff_isDerivedComplete_and_isHausdorff (Submodule.fg_span_singleton f)).2
    ⟨hQ, hQ.isHausdorff_span_singleton_of_isSMulRegular hf⟩

end TauCeti.IsDerivedComplete
