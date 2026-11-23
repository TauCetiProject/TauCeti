/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import TauCeti.Analysis.Analytic.TaylorSeries

/-!
# Analytic uniformization of formal power series

Let `K` be a commutative semiring with an algebra map to a nontrivially normed field `𝕜` (typically
`K = ℚ` and `𝕜 = ℂ`). A formal power series `f ∈ K⟦X⟧` is **uniformized along `φ : 𝕜 → 𝕜` by
`g : 𝕜 → 𝕜`**, written `TauCeti.Uniformizes φ f g`, when there is a function `F` analytic at `0`
whose Taylor series at `0` is the image of `f` and such that `g` and `F ∘ φ` have the same germ at
`0`. This is an identity of germs at `0`: the realization `F` of `f` only needs to exist near `0`,
whereas `φ` and `g` are typically holomorphic on a whole closed disc, so `g` is the analytic
continuation of `f ∘ φ` along `φ`. When `φ` is continuous at `0` with `φ 0 = 0`, `f` and `φ`
determine `g` near `0`; if moreover `φ` does not vanish identically near `0`, `g` and `φ` determine
the image of `f` in `𝕜⟦X⟧`, hence `f` itself when `K → 𝕜` is injective.

Uniformizations by functions holomorphic on a closed disc are the analytic hypotheses of the
arithmetic algebraicity criterion of Calegari, Dimitrov and Tang, which bounds the rank of families
of series with integral coefficients uniformized along a common map `φ` with `|φ'(0)| > 1`.

## Main declarations

* `TauCeti.Uniformizes`: the germ relation `g = F ∘ φ` near `0`, with `F` realizing `f`
  (`TauCeti.uniformizes_iff`).
* `TauCeti.uniformizes_iff_iteratedDeriv`: the same relation with Taylor coefficients written as
  `F⁽ⁿ⁾(0) / n!`.
* `TauCeti.Uniformizes.apply_zero`: `g 0` is the constant coefficient of `f` when `φ 0 = 0`.
* `TauCeti.Uniformizes.eventuallyEq`, `TauCeti.Uniformizes.eqOn`: uniqueness of the uniformizing
  germ, and of an analytic uniformizing function on a preconnected set containing `0`.
* `TauCeti.Uniformizes.map_eq_map`, `TauCeti.Uniformizes.eq_powerSeries`: the germs of `g` and of
  a map `φ` with `φ z → 0` as `z → 0` that does not vanish identically near `0` determine the image
  of `f` in `𝕜⟦X⟧`, and `f` itself when `K → 𝕜` is injective.
* `TauCeti.Uniformizes.add`, `TauCeti.Uniformizes.mul`, `TauCeti.Uniformizes.neg`,
  `TauCeti.uniformizes_C`,
  `TauCeti.uniformizes_X`, `TauCeti.uniformizes_coe_polynomial`: uniformizations along a fixed `φ`
  respect the ring operations.
* `TauCeti.Uniformizes.comp`, `TauCeti.Uniformizes.comp_mul_left`: reparametrization of the
  source, for instance replacing `φ z` and `g z` by `φ (r * z)` and `g (r * z)`.
* `TauCeti.Uniformizes.taylorSeries_eq`: the Taylor series of `g` at `0` is the formal
  substitution of the Taylor series of `φ` into `f`.

## References

* Frank Calegari, Vesselin Dimitrov and Yunqing Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), §1.1.1 and §2.1.
-/

public section

open Filter Function Topology

namespace TauCeti

variable {𝕜 K : Type*} [NontriviallyNormedField 𝕜] {φ φ' g g' g₁ g₂ : 𝕜 → 𝕜}

section CommSemiring

variable [CommSemiring K] [Algebra K 𝕜] {f f₁ f₂ : PowerSeries K}

/-- A formal power series `f` over `K` is **uniformized along `φ` by `g`** if some function `F`
analytic at `0`, with Taylor series at `0` equal to the image of `f` in `𝕜⟦X⟧`, satisfies
`g = F ∘ φ` on a neighbourhood of `0`. The relation is a germ identity at `0`; its applications
assume `φ 0 = 0`. -/
def Uniformizes (φ : 𝕜 → 𝕜) (f : PowerSeries K) (g : 𝕜 → 𝕜) : Prop :=
  ∃ F : 𝕜 → 𝕜, AnalyticAt 𝕜 F 0 ∧ taylorSeries F 0 = f.map (algebraMap K 𝕜) ∧
    g =ᶠ[𝓝 0] F ∘ φ

/-- The defining property of a uniformization: a realization `F` of `f` analytic at `0` with
`g = F ∘ φ` near `0`. -/
theorem uniformizes_iff : Uniformizes φ f g ↔ ∃ F : 𝕜 → 𝕜, AnalyticAt 𝕜 F 0 ∧
    taylorSeries F 0 = f.map (algebraMap K 𝕜) ∧ g =ᶠ[𝓝 0] F ∘ φ :=
  Iff.rfl

/-- **Uniformization with Taylor coefficients `F⁽ⁿ⁾(0) / n!`.** In characteristic zero, the
Taylor coefficients of the realization `F` are its iterated derivatives at `0` divided by `n!`. -/
theorem uniformizes_iff_iteratedDeriv [CharZero 𝕜] [CompleteSpace 𝕜] :
    Uniformizes φ f g ↔ ∃ F : 𝕜 → 𝕜, AnalyticAt 𝕜 F 0 ∧
      (∀ n, algebraMap K 𝕜 (PowerSeries.coeff n f) = iteratedDeriv n F 0 / n.factorial) ∧
      g =ᶠ[𝓝 0] F ∘ φ := by
  refine exists_congr fun F ↦ and_congr_right fun hF ↦ and_congr_left fun _ ↦ ?_
  have hcoeff (n : ℕ) : PowerSeries.coeff n (taylorSeries F 0) =
      iteratedDeriv n F 0 / n.factorial := by
    rw [← hF.factorial_smul_coeff_taylorSeries, nsmul_eq_mul,
      mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 n.factorial_ne_zero)]
  simp only [PowerSeries.ext_iff, PowerSeries.coeff_map, hcoeff, eq_comm]

/-- A function `F` analytic at `0` uniformizes its own Taylor series at `0` along any `φ`, by
`F ∘ φ`. -/
theorem uniformizes_taylorSeries {F : 𝕜 → 𝕜} (hF : AnalyticAt 𝕜 F 0) (φ : 𝕜 → 𝕜) :
    Uniformizes φ (taylorSeries F 0) (F ∘ φ) :=
  ⟨F, hF, by rw [Algebra.algebraMap_self, PowerSeries.map_id, id], EventuallyEq.rfl⟩

/-- Uniformization depends only on the germs of `φ` and `g` at `0`. -/
theorem Uniformizes.congr (h : Uniformizes φ f g) (hφ : φ =ᶠ[𝓝 0] φ') (hg : g =ᶠ[𝓝 0] g') :
    Uniformizes φ' f g' := by
  obtain ⟨F, hF, hFf, hgF⟩ := h
  exact ⟨F, hF, hFf, hg.symm.trans (hgF.trans (hφ.fun_comp F))⟩

/-- If `φ 0 = 0`, the value of a uniformizing function at `0` is the constant coefficient. -/
theorem Uniformizes.apply_zero (h : Uniformizes φ f g) (hφ : φ 0 = 0) :
    g 0 = algebraMap K 𝕜 (PowerSeries.constantCoeff f) := by
  obtain ⟨F, -, hFf, hgF⟩ := h
  rw [hgF.eq_of_nhds, comp_apply, hφ, ← constantCoeff_taylorSeries (f := F), hFf]
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, -PowerSeries.coeff_zero_eq_constantCoeff]

/-- A uniformization along a map `φ` analytic at `0` with `φ 0 = 0` is analytic at `0`. -/
theorem Uniformizes.analyticAt (h : Uniformizes φ f g) (hφ : AnalyticAt 𝕜 φ 0) (hφ0 : φ 0 = 0) :
    AnalyticAt 𝕜 g 0 := by
  obtain ⟨F, hF, -, hgF⟩ := h
  exact ((hφ0 ▸ hF).comp hφ).congr hgF.symm

/-- **Uniqueness of the uniformizing germ.** Along a map `φ` with `φ z → 0` as `z → 0`, two
uniformizations of the same series agree near `0`. -/
theorem Uniformizes.eventuallyEq (h₁ : Uniformizes φ f g₁) (h₂ : Uniformizes φ f g₂)
    (hφ : Tendsto φ (𝓝 0) (𝓝 0)) : g₁ =ᶠ[𝓝 0] g₂ := by
  obtain ⟨F₁, hF₁, hF₁f, hg₁⟩ := h₁
  obtain ⟨F₂, hF₂, hF₂f, hg₂⟩ := h₂
  have hF : F₁ =ᶠ[𝓝 0] F₂ := (taylorSeries_inj hF₁ hF₂).1 (hF₁f.trans hF₂f.symm)
  exact hg₁.trans ((hF.comp_tendsto hφ).trans hg₂.symm)

/-- **Identity theorem for uniformizations.** Along a map `φ` with `φ z → 0` as `z → 0`, two
uniformizations of the same series that are analytic on a neighbourhood of a preconnected set `U`
containing `0` agree on `U`. -/
theorem Uniformizes.eqOn (h₁ : Uniformizes φ f g₁) (h₂ : Uniformizes φ f g₂)
    (hφ : Tendsto φ (𝓝 0) (𝓝 0)) {U : Set 𝕜} (hg₁ : AnalyticOnNhd 𝕜 g₁ U)
    (hg₂ : AnalyticOnNhd 𝕜 g₂ U) (hU : IsPreconnected U) (h₀ : 0 ∈ U) : Set.EqOn g₁ g₂ U :=
  hg₁.eqOn_of_preconnected_of_eventuallyEq hg₂ hU h₀ (h₁.eventuallyEq h₂ hφ)

/-- **A uniformization determines the series over `𝕜`.** Along a map `φ` with `φ z → 0` as
`z → 0` that does not vanish identically near `0`, two series uniformized by the same `g` have the
same image in `𝕜⟦X⟧`. -/
theorem Uniformizes.map_eq_map (h₁ : Uniformizes φ f₁ g) (h₂ : Uniformizes φ f₂ g)
    (hφ : Tendsto φ (𝓝 0) (𝓝 0)) (hφ0 : ¬φ =ᶠ[𝓝 0] 0) :
    f₁.map (algebraMap K 𝕜) = f₂.map (algebraMap K 𝕜) := by
  obtain ⟨F₁, hF₁, hF₁f, hg₁⟩ := h₁
  obtain ⟨F₂, hF₂, hF₂f, hg₂⟩ := h₂
  rw [← hF₁f, ← hF₂f, taylorSeries_inj hF₁ hF₂, eventuallyEq_iff_sub]
  -- `F₁ - F₂` vanishes along `φ`, which takes nonzero values arbitrarily close to `0`, so the zero
  -- of `F₁ - F₂` at `0` is not isolated.
  refine (hF₁.sub hF₂).eventually_eq_zero_or_eventually_ne_zero.resolve_right fun hne ↦ hφ0 ?_
  have hne' : ∀ᶠ z in 𝓝 0, φ z ≠ 0 → (F₁ - F₂) (φ z) ≠ 0 :=
    hφ.eventually (eventually_nhdsWithin_iff.1 hne)
  filter_upwards [hne', hg₁.symm.trans hg₂] with z hz hg
  exact not_not.1 fun h ↦ hz h (sub_eq_zero.2 hg)

/-- **A uniformization determines the series.** If `K → 𝕜` is injective, then along a map `φ` with
`φ z → 0` as `z → 0` that does not vanish identically near `0`, two series uniformized by the same
`g` are equal. -/
theorem Uniformizes.eq_powerSeries [FaithfulSMul K 𝕜] (h₁ : Uniformizes φ f₁ g)
    (h₂ : Uniformizes φ f₂ g) (hφ : Tendsto φ (𝓝 0) (𝓝 0)) (hφ0 : ¬φ =ᶠ[𝓝 0] 0) : f₁ = f₂ :=
  PowerSeries.map_injective _ (FaithfulSMul.algebraMap_injective K 𝕜) (h₁.map_eq_map h₂ hφ hφ0)

/-- A constant series is uniformized by the constant function. -/
@[simp]
theorem uniformizes_C (φ : 𝕜 → 𝕜) (c : K) :
    Uniformizes φ (PowerSeries.C c) (fun _ ↦ algebraMap K 𝕜 c) :=
  ⟨fun _ ↦ algebraMap K 𝕜 c, analyticAt_const, by simp, EventuallyEq.rfl⟩

/-- The zero series is uniformized by the zero function. -/
@[simp]
theorem uniformizes_zero (φ : 𝕜 → 𝕜) : Uniformizes φ (0 : PowerSeries K) 0 := by
  simpa [Pi.zero_def] using uniformizes_C φ (0 : K)

/-- The unit series is uniformized by the constant function `1`. -/
@[simp]
theorem uniformizes_one (φ : 𝕜 → 𝕜) : Uniformizes φ (1 : PowerSeries K) 1 := by
  simpa [Pi.one_def] using uniformizes_C φ (1 : K)

/-- The variable `X` is uniformized along `φ` by `φ` itself. -/
@[simp]
theorem uniformizes_X (φ : 𝕜 → 𝕜) : Uniformizes φ (PowerSeries.X : PowerSeries K) φ := by
  refine ⟨fun z ↦ z, analyticAt_id, ?_, EventuallyEq.rfl⟩
  simpa using taylorSeries_sub_const (𝕜 := 𝕜) (a := 0)

/-- Uniformizations along a fixed `φ` add. -/
theorem Uniformizes.add (h₁ : Uniformizes φ f₁ g₁) (h₂ : Uniformizes φ f₂ g₂) :
    Uniformizes φ (f₁ + f₂) (g₁ + g₂) := by
  obtain ⟨F₁, hF₁, hF₁f, hg₁⟩ := h₁
  obtain ⟨F₂, hF₂, hF₂f, hg₂⟩ := h₂
  exact ⟨F₁ + F₂, hF₁.add hF₂, by rw [taylorSeries_add hF₁ hF₂, hF₁f, hF₂f, map_add],
    hg₁.add hg₂⟩

/-- Uniformizations along a fixed `φ` multiply. -/
theorem Uniformizes.mul (h₁ : Uniformizes φ f₁ g₁) (h₂ : Uniformizes φ f₂ g₂) :
    Uniformizes φ (f₁ * f₂) (g₁ * g₂) := by
  obtain ⟨F₁, hF₁, hF₁f, hg₁⟩ := h₁
  obtain ⟨F₂, hF₂, hF₂f, hg₂⟩ := h₂
  exact ⟨F₁ * F₂, hF₁.mul hF₂, by rw [taylorSeries_mul hF₁ hF₂, hF₁f, hF₂f, map_mul],
    hg₁.mul hg₂⟩

/-- Uniformizations along a fixed `φ` are compatible with powers. -/
theorem Uniformizes.pow (h : Uniformizes φ f g) (n : ℕ) : Uniformizes φ (f ^ n) (g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ] using ih.mul h

/-- A polynomial is uniformized along `φ` by its evaluation at `φ`. -/
theorem uniformizes_coe_polynomial (φ : 𝕜 → 𝕜) (P : Polynomial K) :
    Uniformizes φ (P : PowerSeries K) (fun z ↦ Polynomial.aeval (φ z) P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa [Polynomial.coe_add, Pi.add_def] using hP.add hQ
  | monomial n c =>
    simpa [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_C, Polynomial.coe_X,
      Algebra.smul_def, Pi.mul_def, Pi.pow_def] using
      (uniformizes_C φ c).mul ((uniformizes_X (K := K) φ).pow n)

/-- **Reparametrization.** Precomposing `φ` and `g` with a map `ψ` such that `ψ z → 0` as `z → 0`
preserves uniformization. -/
theorem Uniformizes.comp (h : Uniformizes φ f g) {ψ : 𝕜 → 𝕜} (hψ : Tendsto ψ (𝓝 0) (𝓝 0)) :
    Uniformizes (φ ∘ ψ) f (g ∘ ψ) := by
  obtain ⟨F, hF, hFf, hg⟩ := h
  exact ⟨F, hF, hFf, hg.comp_tendsto hψ⟩

/-- **Rescaling the source.** Replacing `φ z` and `g z` by `φ (r * z)` and `g (r * z)` preserves
uniformization. -/
theorem Uniformizes.comp_mul_left (h : Uniformizes φ f g) (r : 𝕜) :
    Uniformizes (fun z ↦ φ (r * z)) f (fun z ↦ g (r * z)) :=
  h.comp (ψ := (r * ·)) ((continuous_const.mul continuous_id).tendsto' 0 0 (mul_zero r))

end CommSemiring

section CommRing

variable [CommRing K] [Algebra K 𝕜] {f f₁ f₂ : PowerSeries K}

/-- Uniformizations along a fixed `φ` are compatible with negation. -/
theorem Uniformizes.neg (h : Uniformizes φ f g) : Uniformizes φ (-f) (-g) := by
  obtain ⟨F, hF, hFf, hg⟩ := h
  exact ⟨-F, hF.neg, by rw [taylorSeries_neg, hFf, map_neg], hg.neg⟩

/-- Uniformizations along a fixed `φ` subtract. -/
theorem Uniformizes.sub (h₁ : Uniformizes φ f₁ g₁) (h₂ : Uniformizes φ f₂ g₂) :
    Uniformizes φ (f₁ - f₂) (g₁ - g₂) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- **Taylor expansion of a uniformization.** If `φ` is analytic at `0` with `φ 0 = 0`, the
Taylor series at `0` of a uniformization of `f` along `φ` is the formal substitution of the Taylor
series of `φ` into `f`. -/
theorem Uniformizes.taylorSeries_eq (h : Uniformizes φ f g) (hφ : AnalyticAt 𝕜 φ 0)
    (hφ0 : φ 0 = 0) : taylorSeries g 0 = f.subst (taylorSeries φ 0) := by
  obtain ⟨F, hF, hFf, hg⟩ := h
  have hψ : PowerSeries.HasSubst (taylorSeries φ 0) :=
    .of_constantCoeff_zero' (by rw [constantCoeff_taylorSeries, hφ0])
  rw [taylorSeries_congr hg, taylorSeries_comp (by rwa [hφ0]) hφ, hφ0, map_zero, sub_zero, hFf]
  ext n
  rw [PowerSeries.coeff_subst' hψ, PowerSeries.coeff_subst' hψ]
  simp [Algebra.smul_def]

end CommRing

end TauCeti
