/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.ChainRule
public import TauCeti.Analysis.Sobolev.Circle.FractionalPrecomp

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.Deriv.AddCircle

/-!
# Smooth circle diffeomorphisms act on `H^s`

A boundary circle of a cut Riemann surface carries no preferred coordinate, so the Sobolev spaces
of boundary maps must not depend on the parametrization: a fixed diffeomorphism `φ` of the circle
should induce a bounded isomorphism `u ↦ u ∘ φ` of `H^s`.
`TauCeti/Analysis/Sobolev/Circle/Precomp.lean`, `TauCeti/Analysis/Sobolev/Circle/ChainRule.lean`
and `TauCeti/Analysis/Sobolev/Circle/FractionalPrecomp.lean` treat the orders `s = 0`, `s = 1` and
`0 < s < 1`. This file treats every real order `s ≥ 0`, for smooth diffeomorphisms. This includes
the half-integer orders `s = k - 1/2` of the boundary traces of `H^k` functions.

Let `φ` have the lift `F : ℝ → ℝ`, `F (x + T) = F x + T`, with smooth derivative
`0 < c ≤ F' ≤ M`. The proof passes from the order `s` to the order `s + 1`, starting from the
orders `0 ≤ s < 1`. For `u ∈ H^(s+1)`, the chain rule on `H¹` says that `u ∘ φ` has the weak
derivative `F' · (u' ∘ φ)`. By induction `u ∘ φ` and `u' ∘ φ` lie in `H^s`, and multiplication by
the smooth function `F'` preserves `H^s` (`TauCeti.CircleSobolev.mulFourierSeries`), so
`u ∘ φ ∈ H^(s+1)`. Precomposition is therefore a linear map of `H^s`. Its graph is closed: it is
the inverse image, under the continuous inclusions `H^s × H^s → H⁰ × H⁰`, of the closed graph of
the bounded precomposition operator on `H⁰`. So it is continuous by the closed graph theorem. The
inverse map of the circle has the smooth lift `F⁻¹` (`Homeomorph.contDiff_symm_deriv`), so the
inverse precomposition preserves `H^s` as well, and the two restrict to inverse automorphisms of
`H^s` (`TauCeti.CircleSobolev.restrictEquiv`).

## Main definitions

* `TauCeti.CircleSobolev.precompSmoothEquivOfLift`: for `s ≥ 0` and `φ` with lift `F` and smooth
  derivative `0 < c ≤ F' ≤ M`, the continuous linear automorphism `u ↦ u ∘ φ` of `H^s`.

## Main statements

* `TauCeti.CircleSobolev.inclusion_precompSmoothEquivOfLift`: in `H⁰` it is the precomposition
  `TauCeti.CircleSobolev.precompEquivOfLift`; similarly for its inverse
  (`TauCeti.CircleSobolev.inclusion_precompSmoothEquivOfLift_symm`).
* `TauCeti.CircleSobolev.toContinuousMap_precompSmoothEquivOfLift`: for `s > 1/2` it is the
  composition `u ↦ u ∘ φ` of continuous representatives.
* `TauCeti.CircleSobolev.inclusion_precompSmoothEquivOfLift_of_le`: the operators on the different
  orders are compatible with the inclusions `H^s → H^t`, `0 ≤ t ≤ s`.
* `TauCeti.CircleSobolev.derivative_precompSmoothEquivOfLift`: the chain rule
  `(u ∘ φ)' = F' · (u' ∘ φ)` in `H^s`, for `u ∈ H^(s+1)`.
* `TauCeti.CircleSobolev.precompSmoothEquivOfLift_symm_eq`: the inverse is precomposition with the
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

omit hT in
include hF' in
/-- The derivative of a lift with smooth derivative is a smooth function on the circle. -/
theorem contDiff_derivOfLift (hF'c : Continuous F') :
    ContDiff ℝ ∞ fun x : ℝ ↦ derivOfLift hF hper hF'c x := by
  simp only [derivOfLift_coe]
  exact ofRealCLM.contDiff.comp hF'

/-- The weak chain rule on `H¹`: the derivative of `u ∘ φ` is `F' · (u' ∘ φ)`, with the
multiplication by the smooth function `F'` acting through its Fourier coefficients. -/
private theorem derivative_precompOneEquivOfLift_eq {f' : AddCircle T → ℂ}
    (hf' : ∀ x : ℝ, f' x = F' x) (a : CircleSobolev 1 ℂ) :
    derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num)
        (precompOneEquivOfLift hF hper hφ hc hcF hMF hF'.continuous a) =
      mulFourierSeries (fourierCoeff f')
        (precompEquivOfLift hF hper hφ hc hcF hMF
          (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a)) := by
  set g := derivOfLift hF hper hF'.continuous
  have hfg : ⇑g = f' := funext fun y ↦ by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [derivOfLift_coe, hf']
  rw [← hfg, mulFourierSeries_fourierCoeff_eq_multiplicationOperator
    (contDiff_derivOfLift hF hper hF' _)]
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
  simp [g, Function.Periodic.lift_coe]

include hF' in
/-- **Precomposition passes from `H^s` to `H^(s + 1)`.** If precomposition with `φ` preserves
`H^s`, `s ≥ 0`, then it preserves `H^t` for `t = s + 1`: the weak derivative `F' · (u' ∘ φ)` of
`u ∘ φ` lies in `H^s`. The order `t` is a separate variable so that the induction below can
apply this at `t = (s - 1) + 1`. -/
private theorem exists_inclusion_eq_precompEquivOfLift_of_eq_add_one {s t : ℝ} (hs : 0 ≤ s)
    (ht : t = s + 1)
    (ih : ∀ a : CircleSobolev s ℂ, ∃ b : CircleSobolev s ℂ,
      inclusion hs b = precompEquivOfLift hF hper hφ hc hcF hMF (inclusion hs a))
    (a : CircleSobolev t ℂ) :
    ∃ b : CircleSobolev t ℂ, inclusion (by linarith) b =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion (by linarith) a) := by
  subst ht
  have h₁ : (1 : ℝ) ≤ s + 1 := by linarith
  -- `f'` is the derivative `F'`, regarded as a smooth function on the circle.
  set f' := derivOfLift hF hper hF'.continuous
  have hf' (x : ℝ) : f' x = F' x := derivOfLift_coe hF hper _ x
  have hsum := summable_weight_mul_norm_fourierCoeff_of_contDiff (f := f')
    (contDiff_derivOfLift hF hper hF' _)
  obtain ⟨v, hv⟩ := ih (inclusion (by linarith) a)
  obtain ⟨w, hw⟩ := ih (derivative T le_rfl a)
  -- The weak derivative `F' · (u' ∘ φ)` of `u ∘ φ` lies in `H^s`.
  have hderiv : inclusion hs (mulFourierSeries (fourierCoeff f') w) =
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
  exact ⟨b, by simpa only [inclusion_inclusion] using hv⟩

include hF' in
/-- **Precomposition preserves `H^s`, `s ≥ 0`.** For `u ∈ H^s` the function `u ∘ φ ∈ H⁰` comes from
an element of `H^s`. -/
private theorem exists_inclusion_eq_precompEquivOfLift {s : ℝ} (hs : 0 ≤ s)
    (a : CircleSobolev s ℂ) :
    ∃ b : CircleSobolev s ℂ, inclusion hs b =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion hs a) := by
  -- Induction on an integer `n` with `s < n + 1`, starting from the orders `0 ≤ s < 1`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s < n + 1 := ⟨⌊s⌋₊, Nat.lt_floor_add_one s⟩
  induction n generalizing s with
  | zero =>
    rcases hs.eq_or_lt with rfl | hs0
    · exact ⟨precompEquivOfLift hF hper hφ hc hcF hMF (inclusion hs a),
        CircleSobolev.ext (by simp)⟩
    · exact ⟨precompFractionalEquivOfLift hs0 (by simpa using hn) hF hper hφ hc hcF hMF a,
        inclusion_precompFractionalEquivOfLift hs0 _ hF hper hφ hc hcF hMF a⟩
  | succ n ih =>
    rcases lt_or_ge s (n + 1) with hsn | hsn
    · exact ih hs a hsn
    · exact exists_inclusion_eq_precompEquivOfLift_of_eq_add_one hF hper hφ hc hcF hMF hF'
        (by linarith : 0 ≤ s - 1) (by ring)
        (fun b ↦ ih (by linarith) b (by push_cast at hn; linarith)) a

include hF' in
/-- **The inverse precomposition preserves `H^s`, `s ≥ 0`.** The inverse map of the circle has a
smooth lift, so for `u ∈ H^s` the function `u ∘ φ⁻¹ ∈ H⁰` comes from an element of `H^s`. -/
private theorem exists_inclusion_eq_precompEquivOfLift_symm {s : ℝ} (hs : 0 ≤ s)
    (b : CircleSobolev s ℂ) :
    ∃ a : CircleSobolev s ℂ, inclusion hs a =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion hs b) := by
  have hpos (x : ℝ) : 0 < F' x := hc.trans_le (hcF x)
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  -- The inverse map `ψ` of the circle, with lift `G`.
  obtain ⟨ψ, G, hψφ, hGF, hFG, hperG, hψ, hG, hMG, hcG⟩ :=
    exists_inverse_of_lift hF hper hφ hc hcF hMF
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
  rw [precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hM hMG hcG hψφ]
  exact exists_inclusion_eq_precompEquivOfLift hG hperG hψ hM hMG hcG
    ((hF'.comp hGs).inv fun _ ↦ (hpos _).ne') hs b

/-- **Smooth circle diffeomorphisms act on `H^s`.** Let `φ` be the map of the circle with lift
`F`, so that `F (x + T) = F x + T` and `φ x = F x`, and suppose that `F` has a smooth derivative
with `0 < c ≤ F' ≤ M`. Then for every real `s ≥ 0`, `u ↦ u ∘ φ` is a continuous linear
automorphism of `H^s`. Its inverse is precomposition with the inverse map of the circle
(`TauCeti.CircleSobolev.precompSmoothEquivOfLift_symm_eq`). -/
def precompSmoothEquivOfLift {s : ℝ} (hs : 0 ≤ s) : CircleSobolev s ℂ ≃L[ℂ] CircleSobolev s ℂ :=
  restrictEquiv hs hs (precompEquivOfLift hF hper hφ hc hcF hMF)
    (exists_inclusion_eq_precompEquivOfLift hF hper hφ hc hcF hMF hF' hs)
    (exists_inclusion_eq_precompEquivOfLift_symm hF hper hφ hc hcF hMF hF' hs)

/-- In `H⁰`, precomposition on `H^s` is the precomposition `precompEquivOfLift`: the inclusion of
`u ∘ φ` into `H⁰` is the precomposition of the inclusion of `u`. -/
@[simp]
theorem inclusion_precompSmoothEquivOfLift {s : ℝ} (hs : 0 ≤ s) (a : CircleSobolev s ℂ) :
    inclusion hs (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' hs a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion hs a) :=
  inclusion_restrictEquiv _ _ _ _ _ a

/-- In `H⁰`, the inverse of precomposition on `H^s` is the inverse of `precompEquivOfLift`. -/
@[simp]
theorem inclusion_precompSmoothEquivOfLift_symm {s : ℝ} (hs : 0 ≤ s) (a : CircleSobolev s ℂ) :
    inclusion hs ((precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' hs).symm a) =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion hs a) :=
  inclusion_restrictEquiv_symm _ _ _ _ _ a

/-- **Precomposition of continuous representatives.** For `s > 1/2`, the continuous
representative of `u ∘ φ` is the continuous representative of `u` composed with `φ`. -/
theorem toContinuousMap_precompSmoothEquivOfLift {s : ℝ} (hs : 1 / 2 < s) (a : CircleSobolev s ℂ)
    (x : AddCircle T) :
    toContinuousMap T hs (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' (by linarith) a) x =
      toContinuousMap T hs a (φ x) := by
  have hφc : Continuous φ :=
    continuous_of_lift (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt) hφ
  refine DFunLike.congr_fun (?_ : _ = (toContinuousMap T hs a).comp ⟨φ, hφc⟩) x
  refine ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) haarAddCircle ?_
  rw [← toLpₗᵢ_inclusion_eq_toLp_toContinuousMap T hs, ← toLpₗᵢ_precomp_inclusion hs hφc,
    inclusion_precompSmoothEquivOfLift, precompEquivOfLift_apply]

/-- Precomposition on the different orders is compatible with the inclusions `H^s → H^t`. -/
theorem inclusion_precompSmoothEquivOfLift_of_le {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (a : CircleSobolev s ℂ) :
    inclusion hts (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' (ht.trans hts) a) =
      precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' ht (inclusion hts a) :=
  inclusion_injective ht (by
    simp only [inclusion_inclusion, inclusion_precompSmoothEquivOfLift])

/-- **The chain rule on `H^s`.** For `u ∈ H^(s+1)`, `s ≥ 0`, the derivative of `u ∘ φ` is
`F' · (u' ∘ φ)` in `H^s`, where `f'` is the function `F'` regarded on the circle, acting on `H^s`
by multiplication. -/
theorem derivative_precompSmoothEquivOfLift {f' : AddCircle T → ℂ} (hf' : ∀ x : ℝ, f' x = F' x)
    {s : ℝ} (hs : 0 ≤ s) (a : CircleSobolev (s + 1) ℂ) :
    derivative T le_rfl (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' (by linarith) a) =
      mulFourierSeries (fourierCoeff f')
        (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' hs (derivative T le_rfl a)) := by
  have h₁ : (1 : ℝ) ≤ s + 1 := by linarith
  have hsum := summable_weight_mul_norm_fourierCoeff_of_contDiff (f := f')
    (by simp only [hf']; exact ofRealCLM.contDiff.comp hF')
  -- The precomposition on `H^(s+1)` agrees with the one on `H¹`.
  have hone : inclusion h₁ (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' (by linarith) a) =
      precompOneEquivOfLift hF hper hφ hc hcF hMF hF'.continuous (inclusion h₁ a) :=
    inclusion_injective zero_le_one (by
      simp only [inclusion_inclusion, inclusion_precompSmoothEquivOfLift,
        inclusion_precompOneEquivOfLift])
  refine inclusion_injective hs ?_
  rw [inclusion_mulFourierSeries _ (hsum _) (hsum _), inclusion_precompSmoothEquivOfLift,
    inclusion_derivative, ← derivative_inclusion T (show (0 : ℝ) + 1 ≤ 1 by norm_num) h₁, hone,
    derivative_precompOneEquivOfLift_eq hF hper hφ hc hcF hMF hF' hf', inclusion_derivative,
    derivative_inclusion]

/-- The inverse of `precompSmoothEquivOfLift` is `precompSmoothEquivOfLift` for the inverse map `ψ`
of the circle, presented by any lift `G` of `ψ` with smooth derivative between two positive
constants. -/
theorem precompSmoothEquivOfLift_symm_eq {ψ : AddCircle T → AddCircle T} {G G' : ℝ → ℝ}
    {c' M' : ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hperG : ∀ x, G (x + T) = G x + T)
    (hψ : ∀ x : ℝ, ψ x = G x) (hc' : 0 < c') (hcG : ∀ x, c' ≤ G' x) (hMG : ∀ x, G' x ≤ M')
    (hG' : ContDiff ℝ ∞ G') (hψφ : Function.LeftInverse ψ φ) {s : ℝ} (hs : 0 ≤ s) :
    (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' hs).symm =
      precompSmoothEquivOfLift hG hperG hψ hc' hcG hMG hG' hs :=
  ContinuousLinearEquiv.ext <| funext fun a ↦ inclusion_injective hs (by
    rw [inclusion_precompSmoothEquivOfLift_symm, inclusion_precompSmoothEquivOfLift,
      precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hc' hcG hMG hψφ])

end Lift

end CircleSobolev

end TauCeti
