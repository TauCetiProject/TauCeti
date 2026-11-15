/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Toeplitz
public import TauCeti.Analysis.Fredholm.Adjoint
import TauCeti.Analysis.Fourier.Hardy.BoundaryUniqueness
import TauCeti.Analysis.Fourier.Uniqueness

/-!
# Coburn's alternative for Toeplitz operators

For a nonzero essentially bounded symbol `a` on the unit circle, either the Toeplitz operator
`T_a` or its adjoint `T_a† = T_ā` is injective. Consequently a Fredholm Toeplitz operator of
index zero is invertible; this is how invertibility of `T_a` for a continuous symbol `a` reduces
to the computation of its Fredholm index.

The proof is the Hardy product argument. A Hardy function `f` lies in the kernel of `T_a` exactly
when `a f` has only negative Fourier modes (`TauCeti.toeplitz_apply_eq_zero_iff`). Suppose that
`T_a f = 0` and `T_ā g = 0`. The conjugate `conj g` of a Hardy function has only nonpositive
modes, so the integrable product `a f conj g` has only negative modes. Its complex conjugate
`ā g conj f` has only negative modes for the same reason, so `a f conj g` also has only positive
modes. Hence all Fourier coefficients of `a f conj g` vanish and `a f conj g = 0` almost
everywhere. If `f` and `g` are nonzero, then by boundary uniqueness they are nonzero almost
everywhere, which forces `a = 0`.

## Main results

* `TauCeti.eq_zero_of_toeplitz_apply_eq_zero_of_toeplitz_star_apply_eq_zero`: if `T_a` and
  `T_ā` both have nonzero kernel vectors, then `a = 0`.
* `TauCeti.ker_toeplitz_eq_bot_or_ker_adjoint_toeplitz_eq_bot`: **Coburn's alternative**: for
  `a ≠ 0`, `ker T_a = 0` or `ker T_a† = 0`.
* `TauCeti.isInvertible_toeplitz_of_isFredholm_of_index_eq_zero`: a Fredholm Toeplitz operator
  of index zero is invertible.

## References

* L. A. Coburn, *Weyl's theorem for nonnormal operators*, Michigan Math. J. **13** (1966),
  285–288.
* E. Park, *Toeplitz operators*, for the Hardy product argument.
* A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, Springer
  (2006), Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- If `T_a f = 0`, then for every Hardy function `g` the product `a f conj g` has no Fourier modes
`n ≥ 0`: the factor `a f` has only negative modes and `conj g` only nonpositive ones. -/
private theorem fourierCoeff_mul_star_eq_zero {a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))}
    {f : HardySpace} (hf : toeplitz a f = 0) (g : HardySpace) {n : ℤ} (hn : 0 ≤ n) :
    fourierCoeff (⇑(a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) *
      ⇑(star (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))))) n = 0 := by
  have hmem := (mem_hardySubmodule_orthogonal_iff _).mp ((toeplitz_apply_eq_zero_iff a f).mp hf)
  refine (Lp.memLp _).fourierCoeff_mul_eq_zero_of_add_lt (a := -1) (b := 0) (Lp.memLp _)
    (fun m hm ↦ ?_) (fun m hm ↦ ?_) (by omega)
  · lift m to ℕ using (by omega)
    exact hmem m
  · rw [fourierCoeff_star, HardySpace.fourierCoeff_eq_zero g (by omega), map_zero]

/-- **The Hardy product argument.** If the Toeplitz operators `T_a` and `T_ā = T_a†` have nonzero
kernel vectors `f` and `g`, then the symbol `a` is zero. -/
theorem eq_zero_of_toeplitz_apply_eq_zero_of_toeplitz_star_apply_eq_zero
    {a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))} {f g : HardySpace} (hf₀ : f ≠ 0)
    (hg₀ : g ≠ 0) (hf : toeplitz a f = 0) (hg : toeplitz (star a) g = 0) : a = 0 := by
  set F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := ↑f
  set G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := ↑g
  -- The product `w = a f conj g` is integrable; we show that all its Fourier coefficients vanish.
  have hint : Integrable (⇑(a • F) * ⇑(star G)) AddCircle.haarAddCircle :=
    (Lp.memLp _).integrable_mul (Lp.memLp _)
  set w : Lp ℂ 1 (AddCircle.haarAddCircle (T := 1)) := hint.toL1 _
  have hw : ⇑w =ᵐ[AddCircle.haarAddCircle] ⇑(a • F) * ⇑(star G) := hint.coeFn_toL1
  -- The conjugate of `w` is the product `ā g conj f` built from the kernel vector `g` of `T_ā`.
  have hw' : ⇑(star w) =ᵐ[AddCircle.haarAddCircle] ⇑(star a • G) * ⇑(star F) := by
    filter_upwards [Lp.coeFn_star w, hw, Lp.coeFn_lpSMul (r := 2) a F,
      Lp.coeFn_lpSMul (r := 2) (star a) G, Lp.coeFn_star a, Lp.coeFn_star G, Lp.coeFn_star F]
      with t h₁ h₂ h₃ h₄ h₅ h₆ h₇
    simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, Pi.star_apply, Pi.mul_apply, Pi.smul_apply',
      smul_eq_mul, star_mul', star_star]
    ring
  have hcoeff (n : ℤ) : fourierCoeff w n = 0 := by
    rcases le_or_gt 0 n with hn | hn
    · rw [fourierCoeff_congr_ae hw]
      exact fourierCoeff_mul_star_eq_zero hf g hn
    · have h := fourierCoeff_mul_star_eq_zero hg f (n := -n) (by omega)
      rwa [← fourierCoeff_congr_ae hw', fourierCoeff_star, neg_neg, map_eq_zero] at h
  have hw₀ := (L1.integrable_coeFn w).ae_eq_zero_of_forall_fourierCoeff_eq_zero hcoeff
  -- Since `f` and `g` are nonzero almost everywhere, `a f conj g = 0` forces `a = 0`.
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hw₀, hw, HardySpace.ae_ne_zero hf₀, HardySpace.ae_ne_zero hg₀,
    Lp.coeFn_lpSMul (r := 2) a F, Lp.coeFn_star G] with t h₀ h₁ hft hgt h₂ h₃
  simp only [h₁, h₂, h₃, Pi.mul_apply, Pi.smul_apply', smul_eq_mul, Pi.star_apply, Pi.zero_apply,
    mul_eq_zero, star_eq_zero] at h₀
  rcases h₀ with (h₀ | h₀) | h₀
  exacts [h₀, absurd h₀ hft, absurd h₀ hgt]

/-- **Coburn's alternative.** For a nonzero essentially bounded symbol `a`, either the Toeplitz
operator `T_a` or its adjoint has trivial kernel. -/
theorem ker_toeplitz_eq_bot_or_ker_adjoint_toeplitz_eq_bot
    {a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))} (ha : a ≠ 0) :
    LinearMap.ker (toeplitz a : HardySpace →ₗ[ℂ] HardySpace) = ⊥ ∨
      LinearMap.ker
        (ContinuousLinearMap.adjoint (toeplitz a) : HardySpace →ₗ[ℂ] HardySpace) = ⊥ := by
  rw [adjoint_toeplitz]
  by_contra! h
  obtain ⟨f, hf, hf₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.1
  obtain ⟨g, hg, hg₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.2
  exact ha (eq_zero_of_toeplitz_apply_eq_zero_of_toeplitz_star_apply_eq_zero hf₀ hg₀ hf hg)

/-- A Fredholm Toeplitz operator of index zero is invertible. -/
theorem isInvertible_toeplitz_of_isFredholm_of_index_eq_zero
    {a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))} (hT : (toeplitz a).IsFredholm)
    (h₀ : (toeplitz a).index = 0) : (toeplitz a).IsInvertible := by
  refine hT.isInvertible_of_index_eq_zero h₀
    (ker_toeplitz_eq_bot_or_ker_adjoint_toeplitz_eq_bot ?_)
  -- The zero operator is not Fredholm, since its kernel, Hardy space, is infinite dimensional.
  rintro rfl
  rw [map_zero] at hT
  have hfin := hT.finite_ker
  rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero] at hfin
  have : FiniteDimensional ℂ HardySpace := Submodule.topEquiv.finiteDimensional
  exact Module.Finite.not_linearIndependent_of_infinite _ hardyBasis.orthonormal.linearIndependent

end TauCeti
