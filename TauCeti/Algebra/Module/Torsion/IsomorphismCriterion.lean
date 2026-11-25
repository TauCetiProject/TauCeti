/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.Algebra.Module.LocalizedModule.Map
public import TauCeti.Algebra.Module.Torsion.Essential
import TauCeti.RingTheory.QuotSMulTop

/-!
# Detecting isomorphisms modulo a regular element

Let `r` be an element of a commutative ring `R` and `f : M →ₗ[R] N` a linear map, with `r`
regular on `N`. Write `f mod r : M ⧸ rM → N ⧸ rN` for the reduction `QuotSMulTop.map r f`.

* `f mod r` is injective exactly when `r` is regular on the cokernel `N ⧸ range f`, provided `f`
  is injective; only regularity of `r` on `N` is needed for the implication from left to right.
  In other words, the range of `f` is then saturated: `r • y ∈ range f` forces `y ∈ range f`.
* If moreover every element of `N` is carried into the range of `f` by a power of `r` (the
  cokernel is `r`-power torsion), then `f` is surjective exactly when `f mod r` is injective.
  These two facts are `TauCeti.isSMulRegular_quotient_range_iff_injective_quotSMulTop_map` and
  `TauCeti.surjective_iff_injective_quotSMulTop_map` in `TauCeti.RingTheory.QuotSMulTop`.
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

* `TauCeti.surjective_iff_disjoint_torsionBySet_ker_quotSMulTop_map`: with `r`-power-torsion
  cokernel, `f` is surjective exactly when `f mod r` is injective on the `I`-torsion of `M ⧸ rM`.
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
  have hf : Injective f := IsLocalizedModule.injective_of_map_injective (.powers r) i j
    (fun ⟨_, n, hn⟩ ↦ hn ▸ hM.pow n) hloc.1
  -- Rational surjectivity makes the cokernel of `f` `r`-power torsion.
  have hC (y : N) : ∃ n : ℕ, r ^ n • y ∈ range f := by
    obtain ⟨⟨_, n, rfl⟩, hy⟩ :=
      IsLocalizedModule.exists_smul_mem_range_of_map_surjective (.powers r) i j hloc.2 y
    exact ⟨n, hy⟩
  rw [Bijective, and_iff_right hf]
  exact surjective_iff_disjoint_torsionBySet_ker_quotSMulTop_map hf hN hC hMI

end TauCeti
