/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal.Spectral

/-!
# The inclusion `Spv (A, I) → Spv A` is not spectral

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Remark 7.6.** The space `Spv (A, I)` is spectral
(`TauCeti.ValuationSpectrum.spectralSpace_spvOfIdeal`, Lemma 7.5(1)) and is a subspace of the
spectral space `Spv A`, but the inclusion is not a spectral map in general. So spectrality of
subspaces of `Spv (A, I)`, such as `Cont A` and `Spa (A, A⁺)`, cannot be deduced from `Spv A`
through the inclusion; it has to be proved inside `Spv (A, I)`, as is done for
`TauCeti.ValuationSpectrum.isProConstructible_val_preimage_setOfPred_forall_vle_one`.

This file proves the remark for the unit ideal and `A = k[X₀, X₁]` over any field `k`. The open
`{v : v(X₀) ≠ 0}` of `Spv A` is quasi-compact, but its trace on `Spv (A, A)` is not.

* A point `v` of `Spv (A, A)` has full characteristic group, so if `v(x) ≠ 0` then
  `v(d x) ≥ 1` for some `d ∈ A` (`exists_vle_one_mul_of_characteristicSubgroup_eq_top`). Hence
  the opens `{v : 1 ≤ v(d x)}`, for `d ∈ A`, cover the trace of `{v : v(x) ≠ 0}`.
* For `A = k[X₀, X₁]`, pull back the `t`-adic valuation of `k⸨t⸩` along `X₀ ↦ tᴺ`, `X₁ ↦ t⁻¹`.
  This valuation lies in `Spv (A, A)`, because it has rank one and `v(X₁) > 1`. For every finite
  set of `d`, taking `N` larger than the `X₁`-degrees of the `d` gives `v(d X₀) < 1` for all of
  them. So no finite subfamily of that cover suffices.

## Main results

* `TauCeti.ValuationSpectrum.not_isCompact_preimage_basicOpen_spvOfIdeal_top`: if `x ∈ A` is
  such that for every finite `F ⊆ A` some point of `Spv (A, A)` has `v(x) ≠ 0` and `v(d x) < 1`
  for all `d ∈ F`, then the trace of `{v : v(x) ≠ 0}` on `Spv (A, A)` is not quasi-compact.
* `TauCeti.ValuationSpectrum.not_isSpectralMap_subtypeVal_spvOfIdeal_top_mvPolynomial`:
  **Remark 7.6**, the inclusion `Spv (k[X₀, X₁], k[X₀, X₁]) → Spv k[X₀, X₁]` is not spectral.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Lemma 7.5 and Remark 7.6.
-/

public section

namespace TauCeti.ValuationSpectrum

open Valuation WithZero

variable {A : Type*} [CommRing A]

/-- **The trace of `{v : v(x) ≠ 0}` on `Spv (A, A)` is not quasi-compact** as soon as, for every
finite `F ⊆ A`, some point of `Spv (A, A)` satisfies `v(x) ≠ 0` and `v(d x) < 1` for all
`d ∈ F`. The opens `{v : 1 ≤ v(d x)}`, for `d ∈ A`, cover this trace, and the hypothesis says
that no finite subfamily does. -/
theorem not_isCompact_preimage_basicOpen_spvOfIdeal_top
    {hfg : ∃ J : Ideal A, J.FG ∧ (⊤ : Ideal A).radical = J.radical} {x : A}
    (h : ∀ F : Finset A, ∃ v ∈ spvOfIdeal ⊤ hfg,
      ¬ v.toValuativeRel.vle x 0 ∧ ∀ d ∈ F, ¬ v.toValuativeRel.vle 1 (d * x)) :
    ¬ IsCompact (((↑) : spvOfIdeal ⊤ hfg → Spv A) ⁻¹' basicOpen x x) := by
  intro hc
  obtain ⟨F, hF⟩ := hc.elim_finite_subcover
    (fun d ↦ ((↑) : spvOfIdeal ⊤ hfg → Spv A) ⁻¹' basicOpen 1 (d * x))
    (fun d ↦ (isOpen_basicOpen 1 (d * x)).preimage continuous_subtype_val)
    (fun v hv ↦ by
      obtain ⟨d, hd⟩ := exists_vle_one_mul_of_characteristicSubgroup_eq_top
        (mem_spvOfIdeal_top_iff.mp v.2) ((mem_basicOpen_iff _ _ _).mp hv).2
      exact Set.mem_iUnion.mpr ⟨d, (mem_basicOpen_iff _ _ _).mpr hd⟩)
  obtain ⟨v, hv, hx, hF'⟩ := h F
  obtain ⟨d, hd, hvd⟩ := Set.mem_iUnion₂.mp (hF (show ⟨v, hv⟩ ∈ _ from
    (mem_basicOpen_iff _ _ _).mpr ⟨v.toValuativeRel.vle_refl x, hx⟩))
  exact hF' d hd ((mem_basicOpen_iff _ _ _).mp hvd).1

/-! ### The example `k[X₀, X₁]` -/

section MvPolynomial

variable (k : Type*) [Field k]

/-- The valuation on `k[X₀, X₁]` pulled back from the `t`-adic valuation of `k⸨t⸩` along
`X₀ ↦ tᴺ`, `X₁ ↦ t⁻¹`. -/
private noncomputable def laurentValuation (N : ℕ) : Valuation (MvPolynomial (Fin 2) k) ℤᵐ⁰ :=
  (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).comap
    (MvPolynomial.aeval ![HahnSeries.single (N : ℤ) 1, HahnSeries.single (-1) 1] :
      MvPolynomial (Fin 2) k →ₐ[k] LaurentSeries k).toRingHom

private theorem laurentValuation_X_zero (N : ℕ) :
    laurentValuation k N (MvPolynomial.X 0) = exp (-(N : ℤ)) := by
  simp [laurentValuation, LaurentSeries.valuation_single_zpow]

private theorem laurentValuation_X_one (N : ℕ) :
    laurentValuation k N (MvPolynomial.X 1) = exp 1 := by
  simp [laurentValuation, LaurentSeries.valuation_single_zpow]

/-- If every monomial of `d` has `X₁`-degree less than `N`, then `v_N(d X₀) < 1`. -/
private theorem laurentValuation_mul_X_zero_lt_one {N : ℕ} {d : MvPolynomial (Fin 2) k}
    (hd : ∀ m ∈ d.support, m 1 < N) : laurentValuation k N (d * MvPolynomial.X 0) < 1 := by
  rw [d.as_sum, Finset.sum_mul]
  refine Valuation.map_sum_lt _ one_ne_zero fun m hm ↦ ?_
  have hC : laurentValuation k N (MvPolynomial.C (d.coeff m)) ≤ 1 := by
    simpa [laurentValuation, LaurentSeries.algebraMap_apply] using
      (LaurentSeries.val_le_one_iff_eq_coe k _).mpr
        ⟨PowerSeries.C (d.coeff m), PowerSeries.coe_C _⟩
  rw [MvPolynomial.monomial_eq, mul_assoc, map_mul, Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_two, map_mul, map_mul, map_pow, map_pow, laurentValuation_X_zero,
    laurentValuation_X_one]
  calc laurentValuation k N (MvPolynomial.C (d.coeff m)) *
        (exp (-(N : ℤ)) ^ m 0 * exp 1 ^ m 1 * exp (-(N : ℤ)))
      ≤ 1 * (1 * exp 1 ^ m 1 * exp (-(N : ℤ))) := by
        -- `gcongr` closes the constant factor with `hC`
        gcongr
        exact pow_le_one₀ zero_le (exp_le_one_iff.mpr (by omega))
    _ < 1 := by
        rw [one_mul, one_mul, ← exp_nsmul, ← exp_add, exp_lt_one_iff]
        have := hd m hm
        simp only [nsmul_eq_mul, mul_one]
        omega

/-- `v_N` lies in `Spv (A, A)`: it has rank one and `v_N(X₁) > 1`. -/
private theorem ofValuation_laurentValuation_mem_spvOfIdeal_top
    (hfg : ∃ J : Ideal (MvPolynomial (Fin 2) k), J.FG ∧ (⊤ : Ideal _).radical = J.radical)
    (N : ℕ) : ofValuation (laurentValuation k N) ∈ spvOfIdeal ⊤ hfg := by
  rw [mem_spvOfIdeal_top_iff, ← hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top,
    (isEquiv_valuation_ofValuation _).hasFullCharacteristicGroup_iff]
  exact hasFullCharacteristicGroup_of_one_lt (y := MvPolynomial.X 1)
    (by rw [laurentValuation_X_one]; exact one_lt_exp_iff.mpr one_pos)

/-- **Wedhorn, Remark 7.6: the inclusion `Spv (A, I) → Spv A` is not spectral in general.** For
`A = k[X₀, X₁]` over a field `k` and `I = A`, the quasi-compact open `{v : v(X₀) ≠ 0}` of
`Spv A` has a trace on `Spv (A, A)` that is not quasi-compact. -/
theorem not_isSpectralMap_subtypeVal_spvOfIdeal_top_mvPolynomial
    (hfg : ∃ J : Ideal (MvPolynomial (Fin 2) k), J.FG ∧ (⊤ : Ideal _).radical = J.radical) :
    ¬ IsSpectralMap ((↑) : spvOfIdeal ⊤ hfg → Spv (MvPolynomial (Fin 2) k)) := by
  intro hspec
  refine not_isCompact_preimage_basicOpen_spvOfIdeal_top (x := MvPolynomial.X 0) (fun F ↦ ?_)
    (hspec.isCompact_preimage_of_isOpen (isOpen_basicOpen _ _) (isCompact_basicOpen _ _))
  obtain ⟨N, hN⟩ := (F.biUnion fun d ↦ d.support.image fun m ↦ m 1).exists_nat_subset_range
  refine ⟨_, ofValuation_laurentValuation_mem_spvOfIdeal_top k hfg (N + 1), ?_, fun d hd ↦ ?_⟩
  · simp [laurentValuation_X_zero]
  · have hlt := laurentValuation_mul_X_zero_lt_one k (N := N + 1) (d := d) fun m hm ↦ by
      have := hN (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image_of_mem _ hm⟩)
      simp only [Finset.mem_range] at this
      omega
    simpa using hlt

end MvPolynomial

end TauCeti.ValuationSpectrum
