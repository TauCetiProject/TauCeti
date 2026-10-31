/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.ChainRule

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.Deriv.AddCircle

/-!
# Smooth circle diffeomorphisms act on `H^k`

A boundary circle of a cut Riemann surface carries no preferred coordinate, so the Sobolev spaces
of boundary maps must not depend on the parametrization: a fixed diffeomorphism `φ` of the circle
should induce a bounded isomorphism `u ↦ u ∘ φ` of `H^s`.
`TauCeti/Analysis/Sobolev/Circle/Precomp.lean` and `TauCeti/Analysis/Sobolev/Circle/ChainRule.lean`
treat the orders `s = 0` and `s = 1`. This file treats every integer order `s = k ≥ 0`, for smooth
diffeomorphisms.

Let `φ` have the lift `F : ℝ → ℝ`, `F (x + T) = F x + T`, with smooth derivative
`0 < c ≤ F' ≤ M`. The proof is an induction on `k`. For `u ∈ H^(k+1)`, the chain rule on `H¹`
says that `u ∘ φ` has the weak derivative `F' · (u' ∘ φ)`. By induction `u ∘ φ` and `u' ∘ φ` lie
in `H^k`, and multiplication by the smooth function `F'` preserves `H^k`
(`TauCeti.CircleSobolev.mulFourierSeries`), so `u ∘ φ ∈ H^(k+1)`. Precomposition is therefore a
linear map of `H^k`. Its graph is closed: it is the inverse image, under the continuous inclusions
`H^k × H^k → H⁰ × H⁰`, of the closed graph of the bounded precomposition operator on `H⁰`. So it
is continuous by the closed graph theorem. The inverse map of the circle has the smooth lift
`F⁻¹` (`Homeomorph.contDiff_symm_deriv`), so the inverse precomposition preserves `H^k` as well,
and the two restrict to inverse automorphisms of `H^k` (`TauCeti.CircleSobolev.restrictEquiv`).

## Main definitions

* `TauCeti.CircleSobolev.precompNatEquivOfLift k`: for `φ` with lift `F` and smooth derivative
  `0 < c ≤ F' ≤ M`, the continuous linear automorphism `u ↦ u ∘ φ` of `H^k`.

## Main statements

* `TauCeti.CircleSobolev.inclusion_precompNatEquivOfLift`: in `H⁰` it is the precomposition
  `TauCeti.CircleSobolev.precompEquivOfLift`; similarly for its inverse
  (`TauCeti.CircleSobolev.inclusion_precompNatEquivOfLift_symm`).
* `TauCeti.CircleSobolev.inclusion_precompNatEquivOfLift_of_le`: the operators on the different
  orders are compatible with the inclusions `H^k → H^j`, `j ≤ k`.
* `TauCeti.CircleSobolev.derivative_precompNatEquivOfLift`: the chain rule
  `(u ∘ φ)' = F' · (u' ∘ φ)` in `H^k`, for `u ∈ H^(k+1)`.
* `TauCeti.CircleSobolev.precompNatEquivOfLift_symm_eq`: the inverse is precomposition with the
  inverse map of the circle, presented by any of its smooth lifts.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the Sobolev spaces of boundary maps on which
  the Hardy decompositions of cut Riemann surfaces are carried out.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6 (change of variables in Sobolev spaces under diffeomorphisms).
-/

public section

noncomputable section

open MeasureTheory AddCircle Complex Real
open scoped ContDiff

namespace TauCeti

namespace CircleSobolev

variable {T : ℝ} [hT : Fact (0 < T)] {φ : AddCircle T → AddCircle T}

section Lift

variable {F F' : ℝ → ℝ} {c M : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
  (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) (hc : 0 < c)
  (hcF : ∀ x, c ≤ F' x) (hMF : ∀ x, F' x ≤ M) (hF' : ContDiff ℝ ∞ F')

/-- The weak chain rule on `H¹`: the derivative of `u ∘ φ` is `F' · (u' ∘ φ)`, with the
multiplication by the smooth function `F'` acting through its Fourier coefficients. -/
private theorem derivative_precompOneEquivOfLift_eq {f' : AddCircle T → ℂ}
    (hf' : ∀ x : ℝ, f' x = F' x) (a : CircleSobolev 1 ℂ) :
    derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num)
        (precompOneEquivOfLift hF hper hφ hc hcF hMF hF'.continuous a) =
      mulFourierSeries (fourierCoeff f')
        (precompEquivOfLift hF hper hφ hc hcF hMF
          (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a)) := by
  have hf'c : (fun x : ℝ ↦ f' x) = fun x ↦ (F' x : ℂ) := funext hf'
  let g : C(AddCircle T, ℂ) := ⟨f', (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
    (by rw [Function.comp_def, hf'c]; exact continuous_ofReal.comp hF'.continuous)⟩
  have hg : ContDiff ℝ ∞ fun x : ℝ ↦ g x := by
    simp only [g, ContinuousMap.coe_mk, hf'c]
    exact ofRealCLM.contDiff.comp hF'
  have hfg : ⇑g = f' := rfl
  rw [← hfg, mulFourierSeries_fourierCoeff_eq_multiplicationOperator hg]
  refine (toLpₗᵢ T).injective (Lp.ext ?_)
  filter_upwards [toLpₗᵢ_derivative_precompOneEquivOfLift hF hper hφ hc hcF hMF hF'.continuous
      (f' := (periodic_deriv_of_lift hF hper).lift) (fun _ ↦ rfl) a,
    toLpₗᵢ_multiplicationOperator_ae (ContinuousMap.toLp ⊤ haarAddCircle ℂ g)
      (precompEquivOfLift hF hper hφ hc hcF hMF
        (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a)),
    ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ) haarAddCircle g,
    toLpₗᵢ_precompEquivOfLift hF hper hφ hc hcF hMF
      (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp [g, hf', Function.Periodic.lift_coe]

include hF' in
/-- **Precomposition preserves `H^k`.** For `u ∈ H^k`, the function `u ∘ φ ∈ H⁰` comes from an
element of `H^k`. -/
private theorem exists_inclusion_eq_precompEquivOfLift (k : ℕ) (a : CircleSobolev k ℂ) :
    ∃ b : CircleSobolev k ℂ, inclusion (Nat.cast_nonneg k) b =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (Nat.cast_nonneg k) a) := by
  induction k with
  | zero =>
    exact ⟨inclusion Nat.cast_zero.le (precompEquivOfLift hF hper hφ hc hcF hMF
      (inclusion (Nat.cast_nonneg 0) a)), CircleSobolev.ext (by simp)⟩
  | succ k ih =>
    have h₁ : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
    have hk : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
    -- `f'` is the derivative `F'`, regarded as a smooth function on the circle.
    set f' : AddCircle T → ℂ := fun z ↦ ((periodic_deriv_of_lift hF hper).lift z : ℂ)
    have hf' (x : ℝ) : f' x = F' x := rfl
    have hsum := summable_weight_mul_norm_fourierCoeff_of_contDiff (f := f')
      (ofRealCLM.contDiff.comp hF')
    obtain ⟨v, hv⟩ := ih (inclusion hk a)
    obtain ⟨w, hw⟩ := ih (derivative T (Nat.cast_succ k).ge a)
    -- The weak derivative `F' · (u' ∘ φ)` of `u ∘ φ` lies in `H^k`.
    have hderiv : inclusion (Nat.cast_nonneg k) (mulFourierSeries (fourierCoeff f') w) =
        derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num)
          (precompOneEquivOfLift hF hper hφ hc hcF hMF hF'.continuous (inclusion h₁ a)) := by
      rw [inclusion_mulFourierSeries _ (hsum _) (hsum _), hw,
        derivative_precompOneEquivOfLift_eq hF hper hφ hc hcF hMF hF' hf', inclusion_derivative,
        derivative_inclusion]
    obtain ⟨b, rfl, -⟩ := exists_inclusion_eq_and_derivative_eq T v
      (mulFourierSeries (fourierCoeff f') w) fun n ↦ by
        have e₁ := congr_arg (coeff · n) hderiv
        have e₂ := congr_arg (coeff · n) hv
        have e₃ := congr_arg (coeff · n) (inclusion_precompOneEquivOfLift hF hper hφ hc hcF hMF
          hF'.continuous (inclusion h₁ a))
        simp only [coeff_inclusion, coeff_derivative, inclusion_inclusion] at e₁ e₂ e₃
        rw [e₁, e₃, e₂]
    refine ⟨inclusion (Nat.cast_succ k).le b, ?_⟩
    simp only [inclusion_inclusion] at hv ⊢
    exact hv

include hF' in
/-- **The inverse precomposition preserves `H^k`.** The inverse map of the circle has a smooth
lift, so for `u ∈ H^k` the function `u ∘ φ⁻¹ ∈ H⁰` comes from an element of `H^k`. -/
private theorem exists_inclusion_eq_precompEquivOfLift_symm (k : ℕ) (b : CircleSobolev k ℂ) :
    ∃ a : CircleSobolev k ℂ, inclusion (Nat.cast_nonneg k) a =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion (Nat.cast_nonneg k) b) := by
  have hpos (x : ℝ) : 0 < F' x := hc.trans_le (hcF x)
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  obtain ⟨G, hGF, hFG, hperG, hG⟩ := exists_lift_inverse hF hper hpos
  -- The inverse map `ψ` of the circle, with lift `G`.
  set e := homeomorphOfLift φ (strictMono_of_hasDerivAt_pos hF hpos) hFc hper hφ
  have hψφ : Function.LeftInverse e.symm φ :=
    homeomorphOfLift_symm_apply_apply (strictMono_of_hasDerivAt_pos hF hpos) hFc hper hφ
  have hψ (y : ℝ) : e.symm y = G y := by
    rw [show ((y : ℝ) : AddCircle T) = φ (G y) by rw [hφ, hFG y], hψφ]
  -- `G` is smooth since `F` is smooth with nonvanishing derivative, so `(F' ∘ G)⁻¹` is smooth.
  have hFs : ContDiff ℝ ∞ F :=
    contDiff_infty_iff_deriv.2 ⟨fun x ↦ (hF x).differentiableAt,
      (funext fun x ↦ (hF x).deriv : deriv F = F') ▸ hF'⟩
  let E : ℝ ≃ₜ ℝ :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      continuous_toFun := hFc
      continuous_invFun := continuous_iff_continuousAt.2 fun y ↦ (hG y).continuousAt }
  have hGs : ContDiff ℝ ∞ G := E.contDiff_symm_deriv (fun x ↦ (hpos x).ne') hF hFs
  have hM : 0 < M⁻¹ := inv_pos.2 ((hpos 0).trans_le (hMF 0))
  rw [precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hM
    (fun y ↦ inv_anti₀ (hpos _) (hMF _)) (fun y ↦ inv_anti₀ hc (hcF _)) hψφ]
  exact exists_inclusion_eq_precompEquivOfLift hG hperG hψ hM
    (fun y ↦ inv_anti₀ (hpos _) (hMF _)) (fun y ↦ inv_anti₀ hc (hcF _))
    ((hF'.comp hGs).inv fun _ ↦ (hpos _).ne') k b

/-- **Smooth circle diffeomorphisms act on `H^k`.** Let `φ` be the map of the circle with lift
`F`, so that `F (x + T) = F x + T` and `φ x = F x`, and suppose that `F` has a smooth derivative
with `0 < c ≤ F' ≤ M`. Then for every natural number `k`, `u ↦ u ∘ φ` is a continuous linear
automorphism of `H^k`. Its inverse is precomposition with the inverse map of the circle
(`TauCeti.CircleSobolev.precompNatEquivOfLift_symm_eq`). -/
def precompNatEquivOfLift (k : ℕ) : CircleSobolev k ℂ ≃L[ℂ] CircleSobolev k ℂ :=
  restrictEquiv (Nat.cast_nonneg k) (Nat.cast_nonneg k) (precompEquivOfLift hF hper hφ hc hcF hMF)
    (exists_inclusion_eq_precompEquivOfLift hF hper hφ hc hcF hMF hF' k)
    (exists_inclusion_eq_precompEquivOfLift_symm hF hper hφ hc hcF hMF hF' k)

/-- In `H⁰`, precomposition on `H^k` is the precomposition `precompEquivOfLift`: the inclusion of
`u ∘ φ` into `H⁰` is the precomposition of the inclusion of `u`. -/
@[simp]
theorem inclusion_precompNatEquivOfLift (k : ℕ) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_nonneg k) (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (Nat.cast_nonneg k) a) :=
  inclusion_restrictEquiv _ _ _ _ _ a

/-- In `H⁰`, the inverse of precomposition on `H^k` is the inverse of `precompEquivOfLift`. -/
@[simp]
theorem inclusion_precompNatEquivOfLift_symm (k : ℕ) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_nonneg k) ((precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k).symm a) =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion (Nat.cast_nonneg k) a) :=
  inclusion_restrictEquiv_symm _ _ _ _ _ a

/-- Precomposition on the different orders is compatible with the inclusions `H^k → H^j`. -/
theorem inclusion_precompNatEquivOfLift_of_le {j k : ℕ} (h : j ≤ k) (a : CircleSobolev k ℂ) :
    inclusion (Nat.cast_le.2 h) (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k a) =
      precompNatEquivOfLift hF hper hφ hc hcF hMF hF' j (inclusion (Nat.cast_le.2 h) a) :=
  inclusion_injective (Nat.cast_nonneg j) (by
    simp only [inclusion_inclusion, inclusion_precompNatEquivOfLift])

/-- **The chain rule on `H^k`.** For `u ∈ H^(k+1)`, the derivative of `u ∘ φ` is `F' · (u' ∘ φ)`
in `H^k`, where `f'` is the function `F'` regarded on the circle, acting on `H^k` by
multiplication. -/
theorem derivative_precompNatEquivOfLift {f' : AddCircle T → ℂ} (hf' : ∀ x : ℝ, f' x = F' x)
    (k : ℕ) (a : CircleSobolev (k + 1 : ℕ) ℂ) :
    derivative T (Nat.cast_succ k).ge (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' (k + 1) a) =
      mulFourierSeries (fourierCoeff f')
        (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k
          (derivative T (Nat.cast_succ k).ge a)) := by
  have h₁ : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hsum := summable_weight_mul_norm_fourierCoeff_of_contDiff (f := f')
    (by simp only [hf']; exact ofRealCLM.contDiff.comp hF')
  -- The precomposition on `H^(k+1)` agrees with the one on `H¹`.
  have hone : inclusion h₁ (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' (k + 1) a) =
      precompOneEquivOfLift hF hper hφ hc hcF hMF hF'.continuous (inclusion h₁ a) :=
    inclusion_injective zero_le_one (by
      simp only [inclusion_inclusion, inclusion_precompNatEquivOfLift,
        inclusion_precompOneEquivOfLift])
  refine inclusion_injective (Nat.cast_nonneg k) ?_
  rw [inclusion_mulFourierSeries _ (hsum _) (hsum _), inclusion_precompNatEquivOfLift,
    inclusion_derivative, ← derivative_inclusion T (show (0 : ℝ) + 1 ≤ 1 by norm_num) h₁, hone,
    derivative_precompOneEquivOfLift_eq hF hper hφ hc hcF hMF hF' hf', inclusion_derivative,
    derivative_inclusion]

/-- The inverse of `precompNatEquivOfLift` is `precompNatEquivOfLift` for the inverse map `ψ` of
the circle, presented by any lift `G` of `ψ` with smooth derivative between two positive
constants. -/
theorem precompNatEquivOfLift_symm_eq {ψ : AddCircle T → AddCircle T} {G G' : ℝ → ℝ}
    {c' M' : ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hperG : ∀ x, G (x + T) = G x + T)
    (hψ : ∀ x : ℝ, ψ x = G x) (hc' : 0 < c') (hcG : ∀ x, c' ≤ G' x) (hMG : ∀ x, G' x ≤ M')
    (hG' : ContDiff ℝ ∞ G') (hψφ : Function.LeftInverse ψ φ) (k : ℕ) :
    (precompNatEquivOfLift hF hper hφ hc hcF hMF hF' k).symm =
      precompNatEquivOfLift hG hperG hψ hc' hcG hMG hG' k :=
  ContinuousLinearEquiv.ext <| funext fun a ↦ inclusion_injective (Nat.cast_nonneg k) (by
    rw [inclusion_precompNatEquivOfLift_symm, inclusion_precompNatEquivOfLift,
      precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hc' hcG hMG hψφ])

end Lift

end CircleSobolev

end TauCeti
