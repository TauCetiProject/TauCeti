/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regular elements on localization cokernels

Let `f : M →ₗ[R] N` be localization at a submonoid `S`. If `r` is regular on `M`,
and every denominator is regular on `M / rM`, then `r` is regular on `N / range f`.
In particular, when `(r, s)` is a regular pair, the cokernel of `M → M[1/s]`
has no `r`-torsion. This supplies the regular-cokernel hypothesis for exactness
of principal-adic completion of localization sequences.

Neither finiteness nor Noetherianity is required. The localization map need not
be injective: the quotient is by its image, not by an assumed embedded copy of `M`.

## References

* Douglas–Francis–Henriques–Hill, *Topological Modular Forms*, Chapter 12, §8,
  for the regular localization/completion comparison.
-/

public section

open scoped Pointwise

namespace IsLocalizedModule

section Semiring

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  (f : M →ₗ[R] N) [IsLocalizedModule S f] {r : R}

include S f in
/-- A regular scalar remains regular after localization of a module. -/
theorem isSMulRegular (hr : IsSMulRegular M r) : IsSMulRegular N r := by
  -- Scalar multiplication by `r` is the endomorphism `r • id`.
  have hinj : Function.Injective (r • (LinearMap.id : M →ₗ[R] M)) := hr
  have h := map_injective S f f (r • (LinearMap.id : M →ₗ[R] M)) hinj
  intro x y hxy
  apply h
  simpa only [map_smul, map_id, LinearMap.smul_apply, LinearMap.id_apply] using hxy

end Semiring

variable {R : Type*} [CommRing R] (S : Submonoid R)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) [IsLocalizedModule S f] {r : R}

/-- Divisibility by `r` descends through localization if all denominators act
regularly modulo `r`. The scalar `r` itself need not be regular. -/
theorem mem_smul_top_of_map_eq_smul
    (hS : ∀ s : S, IsSMulRegular (QuotSMulTop r M) (s : R))
    {m : M} {x : N} (hm : f m = r • x) : m ∈ r • (⊤ : Submodule R M) := by
  obtain ⟨⟨n, s⟩, hn⟩ := IsLocalizedModule.surj S f x
  simp only [Submonoid.smul_def] at hn
  have heq : f (r • n) = f ((s : R) • m) := by
    rw [map_smul, ← hn, smul_comm, ← hm, map_smul]
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) heq
  simp only [Submonoid.smul_def] at ht
  apply mem_of_isSMulRegular_quotient_of_smul_mem (hS (t * s))
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨(t : R) • n, trivial, ?_⟩
  rw [Submonoid.coe_mul, mul_smul, smul_comm r]
  exact ht

/-- Reduction modulo `r` of a localization map is injective when its denominators
are regular on `M / rM`, even if the original localization map is not injective. -/
theorem quotSMulTop_map_injective
    (hS : ∀ s : S, IsSMulRegular (QuotSMulTop r M) (s : R)) :
    Function.Injective (QuotSMulTop.map r f) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro q hq
  induction q using Submodule.Quotient.induction_on with | H m => ?_
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have hfm : f m ∈ r • (⊤ : Submodule R N) := by
    simpa only [LinearMap.mem_ker, QuotSMulTop.map_apply_mk,
      Submodule.Quotient.mk_eq_zero] using hq
  obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hfm
  exact mem_smul_top_of_map_eq_smul S f hS hx.symm

/-- If `r` is regular on `M` and every denominator is regular modulo `r`, then
`r` is regular on the cokernel of the localization map. -/
theorem isSMulRegular_quotient_range (hr : IsSMulRegular M r)
    (hS : ∀ s : S, IsSMulRegular (QuotSMulTop r M) (s : R)) :
    IsSMulRegular (N ⧸ LinearMap.range f) r := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro x hx
  obtain ⟨m, hm⟩ := hx
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
    (mem_smul_top_of_map_eq_smul S f hS hm)
  exact ⟨y, (isSMulRegular S f hr) ((f.map_smul r y).symm.trans
    ((congrArg f hy).trans hm))⟩

/-- For a regular pair `(r, s)` on a module, the cokernel of localization away
from `s` has no `r`-torsion. Regularity here does not require the quotient to be nonzero. -/
theorem isSMulRegular_quotient_range_away {s : R}
    [IsLocalizedModule.Away s f] (hr : IsSMulRegular M r)
    (hs : IsSMulRegular (QuotSMulTop r M) s) :
    IsSMulRegular (N ⧸ LinearMap.range f) r := by
  apply isSMulRegular_quotient_range (Submonoid.powers s) f hr
  rintro ⟨a, ⟨n, rfl⟩⟩
  exact hs.pow n

end IsLocalizedModule
