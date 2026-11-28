/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.RingTheory.AdicCompletion.DerivedComplete.Module
import TauCeti.RingTheory.Regular.IsSMulRegular

/-!
# Classical completeness of cokernels at a regular scalar

* `TauCeti.IsDerivedComplete.isHausdorff_span_singleton_of_isSMulRegular`: a derived
  `(f)`-complete module is `(f)`-adically separated if `f` acts injectively. In this case the
  intersection of the powers is divisible by `f` by `IsSMulRegular.smul_iInf_pow_smul_top`,
  so it vanishes by
  `TauCeti.IsDerivedComplete.eq_bot_of_le_pointwise_smul`.
* `TauCeti.IsDerivedComplete.isAdicComplete_quotient_range_of_isSMulRegular`: the cokernel
  of a map of derived `(f)`-complete modules is classically `(f)`-adically complete if `f`
  acts injectively on it. The derived completeness input is
  `TauCeti.IsDerivedComplete.quotient_range`.
* `TauCeti.IsDerivedComplete.quotSMulTop` and
  `TauCeti.IsDerivedComplete.isAdicComplete_quotSMulTop_of_isSMulRegular` give the
  derived and classical completeness results for `N / gN` in Mathlib's `QuotSMulTop` API.
  The derived result identifies the scalar multiple of the whole module with the range of
  scalar multiplication using `Submodule.pointwise_smul_def` and `LinearMap.range_eq_map`.

See Bhatt, Ma, Patakfalvi, Schwede, Tucker, Waldron and Witaszek,
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
  have hK : K ≤ f • K := hf.smul_iInf_pow_smul_top.ge
  have hzero : K = ⊥ := hM.eq_bot_of_le_pointwise_smul (Ideal.mem_span_singleton_self f) hK
  refine ⟨fun x hx ↦ ?_⟩
  have hxK : x ∈ K := by
    refine (Submodule.mem_iInf _).2 fun n ↦ ?_
    simpa only [SModEq.zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
      using hx n
  rwa [hzero, Submodule.mem_bot] at hxK

/-- The cokernel of a map between derived `(f)`-complete modules is classically
`(f)`-adically complete if `f` acts injectively on it. For `N / gN`, see
`isAdicComplete_quotSMulTop_of_isSMulRegular`. -/
theorem isAdicComplete_quotient_range_of_isSMulRegular
    (hM : IsDerivedComplete (Ideal.span {f}) M) (hN : IsDerivedComplete (Ideal.span {f}) N)
    (g : M →ₗ[R] N) (hf : IsSMulRegular (N ⧸ LinearMap.range g) f) :
    IsAdicComplete (Ideal.span {f}) (N ⧸ LinearMap.range g) := by
  have hQ : IsDerivedComplete (Ideal.span {f}) (N ⧸ LinearMap.range g) :=
    hM.quotient_range hN g
  exact (isAdicComplete_iff_isDerivedComplete_and_isHausdorff (Submodule.fg_span_singleton f)).2
    ⟨hQ, hQ.isHausdorff_span_singleton_of_isSMulRegular hf⟩

/-- If `N` is derived `I`-complete, so is the scalar quotient `N / gN`.
See [Stacks Project, Lemma 15.93.6 (Tag 091U)](https://stacks.math.columbia.edu/tag/091U)
for closure under cokernels. -/
theorem quotSMulTop {I : Ideal R} (hN : IsDerivedComplete I N) (g : R) :
    IsDerivedComplete I (QuotSMulTop g N) := by
  suffices h : IsDerivedComplete I (N ⧸ g • (⊤ : Submodule R N)) from h
  rw [Submodule.pointwise_smul_def, ← LinearMap.range_eq_map]
  exact hN.quotient_range hN (DistribSMul.toLinearMap R N g)

/-- The scalar quotient `N / gN` of a derived `(f)`-complete module is classically
`(f)`-adically complete if `f` acts injectively on the quotient. See
Bhatt–Ma–Patakfalvi–Schwede–Tucker–Waldron–Witaszek, Lemma 2.8. -/
theorem isAdicComplete_quotSMulTop_of_isSMulRegular
    (hN : IsDerivedComplete (Ideal.span {f}) N) {g : R} (hf : IsSMulRegular (QuotSMulTop g N) f) :
    IsAdicComplete (Ideal.span {f}) (QuotSMulTop g N) := by
  have hQ := hN.quotSMulTop g
  exact (isAdicComplete_iff_isDerivedComplete_and_isHausdorff (Submodule.fg_span_singleton f)).2
    ⟨hQ, hQ.isHausdorff_span_singleton_of_isSMulRegular hf⟩

end TauCeti.IsDerivedComplete
