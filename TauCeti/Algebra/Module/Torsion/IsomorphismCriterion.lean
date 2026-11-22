/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import TauCeti.Algebra.Module.Torsion.Essential

/-!
# Detecting isomorphisms modulo a regular element

Let `r` be an element of a commutative ring `R` and `f : M →ₗ[R] N` a linear map, with `r`
regular on `N`. Write `f mod r : M ⧸ rM → N ⧸ rN` for the reduction `QuotSMulTop.map r f`.

* `f mod r` is injective exactly when `r` is regular on the cokernel `N ⧸ range f`, provided `f`
  is injective; only regularity of `r` on `N` is needed for the implication from left to right.
  In other words, the range of `f` is then saturated: `r • y ∈ range f` forces `y ∈ range f`.
* If moreover every element of `N` is carried into the range of `f` by a power of `r` (the
  cokernel is `r`-power torsion), then `f` is surjective exactly when `f mod r` is injective.
* If `M ⧸ rM` is `I`-power torsion for an ideal `I`, injectivity of `f mod r` may be tested on
  the `I`-torsion `(M ⧸ rM)[I]`, which is essential in `M ⧸ rM`.

Combining these, for `M` and `N` without `r`-torsion and `f` becoming bijective once `r` is
inverted, `f` is bijective exactly when `f mod r` is injective on `(M ⧸ rM)[I]`. Neither
completeness, separatedness nor finiteness is required.

This is the integral isomorphism criterion of Emerton for `ϖ`-adically admissible
representations of `GL₂(ℚ_p)` over a complete local noetherian `O`-algebra `A` with maximal ideal
`𝔪`: there `r = ϖ`, `I = 𝔪`, the reduction `Π₁ ⧸ ϖΠ₁` is `𝔪`-power torsion, and an `A[G]`-linear
map between `ϖ`-torsion-free such representations inducing an isomorphism after inverting `ϖ` is
an isomorphism exactly when it is injective on the `𝔪`-socles of the reductions. The group action
plays no role. Rational surjectivity cannot be dropped: `x ↦ (x, 0)` from `O` to `O²` is injective
after inverting `ϖ` and on residual socles, but has cokernel `O`.

## Main results

* `TauCeti.isSMulRegular_quotient_range_iff_injective_quotSMulTop_map`: for injective `f` and `r`
  regular on `N`, `f mod r` is injective exactly when `r` is regular on the cokernel of `f`.
* `TauCeti.surjective_iff_injective_quotSMulTop_map`: with `r`-power-torsion cokernel, `f` is
  surjective exactly when `f mod r` is injective.
* `TauCeti.surjective_iff_disjoint_torsionBySet_ker_quotSMulTop_map`: the same, with injectivity
  tested on the `I`-torsion of `M ⧸ rM`.
* `TauCeti.bijective_iff_disjoint_torsionBySet_ker_quotSMulTop_map`: the criterion for a map
  which becomes bijective after inverting `r`.

## References

* M. Emerton, *Local-global compatibility in the p-adic Langlands programme for `GL₂/ℚ`*,
  unpublished manuscript, draft of 23 March 2011, §3.1, Lemma 3.1.6.
-/

public section

open Function LinearMap Submodule
open scoped Pointwise

namespace TauCeti

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {r : R} {f : M →ₗ[R] N}

/-- **Saturation of the range.** If `r` is regular on `N` and `f mod r` is injective, then `r` is
regular on the cokernel of `f`: `r • y ∈ range f` forces `y ∈ range f`. -/
theorem isSMulRegular_quotient_range_of_injective_quotSMulTop_map (hN : IsSMulRegular N r)
    (h : Injective (QuotSMulTop.map r f)) : IsSMulRegular (N ⧸ range f) r := by
  refine (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr fun y ⟨z, hz⟩ ↦ ?_
  -- The class of `z` maps to the class of `r • y = 0` in `N ⧸ rN`, so `z = r • w`.
  have hz0 : Submodule.Quotient.mk (p := r • (⊤ : Submodule R M)) z = 0 := h <| by
    rw [QuotSMulTop.map_apply_mk, map_zero, hz, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul y r ⊤ trivial
  obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
    ((Submodule.Quotient.mk_eq_zero _).mp hz0)
  exact ⟨w, hN (by simpa using hz)⟩

/-- **Regularity on the cokernel.** For injective `f` with `r` regular on `N`, the reduction
`f mod r : M ⧸ rM → N ⧸ rN` is injective exactly when `r` is regular on `N ⧸ range f`. -/
theorem isSMulRegular_quotient_range_iff_injective_quotSMulTop_map (hf : Injective f)
    (hN : IsSMulRegular N r) :
    IsSMulRegular (N ⧸ range f) r ↔ Injective (QuotSMulTop.map r f) := by
  refine ⟨fun hC ↦ ?_, isSMulRegular_quotient_range_of_injective_quotSMulTop_map hN⟩
  refine (injective_iff_map_eq_zero _).mpr fun q hq ↦ ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero] at hq
  -- `f z = r • y`; regularity on the cokernel puts `y = f w`, and injectivity gives `z = r • w`.
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hq
  obtain ⟨w, rfl⟩ := (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp hC y ⟨z, hy.symm⟩
  rw [Submodule.Quotient.mk_eq_zero, ← hf (by rw [← hy, map_smul] : f (r • w) = f z)]
  exact Submodule.smul_mem_pointwise_smul w r ⊤ trivial

/-- **Surjectivity from the reduction modulo `r`.** If `r` is regular on `N`, a power of `r`
carries every element of `N` into the range of `f`, and `f mod r` is injective, then `f` is
surjective. -/
theorem surjective_of_injective_quotSMulTop_map (hN : IsSMulRegular N r)
    (hC : ∀ y : N, ∃ n : ℕ, r ^ n • y ∈ range f) (h : Injective (QuotSMulTop.map r f)) :
    Surjective f := by
  have hsat := (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mp
    (isSMulRegular_quotient_range_of_injective_quotSMulTop_map hN h)
  refine fun y ↦ mem_range.mp ?_
  obtain ⟨n, hn⟩ := hC y
  induction n generalizing y with
  | zero => simpa using hn
  | succ n ih => exact hsat y (ih (r • y) (by rwa [smul_smul, ← pow_succ]))

/-- **The isomorphism criterion modulo `r`.** Let `f` be injective, `r` regular on `N`, and
suppose a power of `r` carries every element of `N` into the range of `f`. Then `f` is surjective
exactly when its reduction `f mod r : M ⧸ rM → N ⧸ rN` is injective. -/
theorem surjective_iff_injective_quotSMulTop_map (hf : Injective f) (hN : IsSMulRegular N r)
    (hC : ∀ y : N, ∃ n : ℕ, r ^ n • y ∈ range f) :
    Surjective f ↔ Injective (QuotSMulTop.map r f) :=
  ⟨fun hs ↦ (QuotSMulTop.congr r (LinearEquiv.ofBijective f ⟨hf, hs⟩)).injective,
    surjective_of_injective_quotSMulTop_map hN hC⟩

/-- **The isomorphism criterion on the `I`-torsion.** Let `f` be injective, `r` regular on `N`,
and suppose a power of `r` carries every element of `N` into the range of `f`. If `M ⧸ rM` is
`I`-power torsion, then `f` is surjective exactly when `f mod r` is injective on the `I`-torsion
`(M ⧸ rM)[I]`. -/
theorem surjective_iff_disjoint_torsionBySet_ker_quotSMulTop_map {I : Ideal R}
    (hf : Injective f) (hN : IsSMulRegular N r) (hC : ∀ y : N, ∃ n : ℕ, r ^ n • y ∈ range f)
    (hM : I.primaryComponent (QuotSMulTop r M) = ⊤) :
    Surjective f ↔
      Disjoint (torsionBySet R (QuotSMulTop r M) I) (ker (QuotSMulTop.map r f)) :=
  (surjective_iff_injective_quotSMulTop_map hf hN hC).trans
    (injective_iff_disjoint_torsionBySet_ker hM)

/-- **The integral isomorphism criterion.** Let `r` be regular on `M` and on `N`, and suppose
`f` becomes bijective after inverting `r`: its localization `M' → N'` at the powers of `r` is
bijective. If `M ⧸ rM` is `I`-power torsion, then `f` is bijective exactly when `f mod r` is
injective on the `I`-torsion `(M ⧸ rM)[I]`. -/
theorem bijective_iff_disjoint_torsionBySet_ker_quotSMulTop_map {I : Ideal R}
    {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (i : M →ₗ[R] M') (j : N →ₗ[R] N') [IsLocalizedModule (.powers r) i]
    [IsLocalizedModule (.powers r) j] (hM : IsSMulRegular M r) (hN : IsSMulRegular N r)
    (hloc : Bijective (IsLocalizedModule.map (.powers r) i j f))
    (hMI : I.primaryComponent (QuotSMulTop r M) = ⊤) :
    Bijective f ↔
      Disjoint (torsionBySet R (QuotSMulTop r M) I) (ker (QuotSMulTop.map r f)) := by
  -- `j ∘ f = (f localized) ∘ i` with `i` injective, as `r` is regular on `M`.
  have hi : Injective i := (IsLocalizedModule.injective_iff_isRegular (.powers r) i).mpr
    fun ⟨_, n, hn⟩ ↦ hn ▸ hM.pow n
  have hf : Injective f := by
    refine Injective.of_comp (f := j) ?_
    rw [← coe_comp, ← IsLocalizedModule.map_comp (.powers r) i j f, coe_comp]
    exact hloc.1.comp hi
  -- A power of `r` carries each `y : N` into the range of `f`, by rational surjectivity.
  have hC (y : N) : ∃ n : ℕ, r ^ n • y ∈ range f := by
    obtain ⟨p, hxs⟩ := hloc.2 (j y)
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (.powers r) i p
    simp only [uncurry_apply_pair, IsLocalizedModule.map_mk'] at hxs
    rw [IsLocalizedModule.mk'_eq_iff, ← map_smul_of_tower, eq_comm] at hxs
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) hxs
    obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩⟩ := c, s
    refine ⟨a + b, (r ^ a) • x, ?_⟩
    simp only [Submonoid.smul_def, map_smul] at hc ⊢
    rw [← hc, smul_smul, ← pow_add]
  rw [Bijective, and_iff_right hf]
  exact surjective_iff_disjoint_torsionBySet_ker_quotSMulTop_map hf hN hC hMI

end TauCeti
