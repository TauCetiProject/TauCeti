/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.TrivSqZeroExt
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.Analysis.Normed.Ring.DualNumber
public import TauCeti.Analysis.Normed.Ring.BerkovichSpectrum.SpectralFormula
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import TauCeti.Algebra.TrivSqZeroExt.Basic

/-!
# Concrete Berkovich spectra and checks for Berkovich's spectral formula

We instantiate `TauCeti.Spectrum` and Berkovich's spectral formula on concrete normed rings:

* **`p`-adic numbers `ℚ_[p]`:** the Berkovich spectrum is a singleton whose unique point evaluates
  every `x : ℚ_[p]` to its `p`-adic norm `‖x‖`, and `smoothingFun (normRingSeminorm ℚ_[p]) x = ‖x‖`.
* **Multivariate Tate algebras `K⟨X_σ⟩` at unit polyradius:** over any ultrametric normed
  commutative ring `K` with multiplicative normalized norm (in particular any nonarchimedean normed
  field), the Gauss norm defines the greatest point `Spectrum.normPoint` of the Berkovich
  spectrum, attaining `sSup {x f | x} = smoothingFun (normRingSeminorm _) f = ‖f‖` for every
  restricted series `f`.
* **Trivial square-zero extensions and dual numbers `K[ε]/(ε²)`:** for both Mathlib's `ℓ¹` norm on
  `DualNumber K` and the ultrametric maximum norm on `TauCeti.MaxDualNumber K`, projection to `K`
  induces a homeomorphism of Berkovich spectra. Over a normed field `K`, the generator `ε` has
  `‖ε‖ = 1` while `smoothingFun (normRingSeminorm _) ε = sSup {x ε | x} = 0`, `‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖`,
  and the ambient norm does not belong to `Spectrum`.
* **Boundary cases, negative control, and functoriality:** emptiness on the zero ring `PUnit`,
  vanishing on square-zero elements, failure of the constant-`1` map (which preserves `1` and `*`
  and satisfies subadditivity) to define a `MulRingSeminorm` because `map_zero` fails, and
  contravariant pullback identities.
-/

public section

namespace TauCeti.Spectrum.Examples

/-! ### `p`-adic numbers `ℚ_[p]` -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Every point of the Berkovich spectrum of `ℚ_[p]` is the `p`-adic norm, `Spectrum ℚ_[p]`
has a unique point, and the spectral seminorm of `ℚ_[p]` equals the `p`-adic norm. -/
theorem padic_spectrum (a : ℚ_[p]) :
    (∀ x : Spectrum ℚ_[p], x a = ‖a‖) ∧
      Nonempty (Unique (Spectrum ℚ_[p])) ∧
      smoothingFun (normRingSeminorm ℚ_[p]) a = ‖a‖ :=
  ⟨fun x ↦ by rw [x.eq_normPoint, normPoint_apply], ⟨inferInstance⟩,
    (smoothingFun_eq_sSup a).trans (sSup_range_eval_of_normMulClass a)⟩

end Padic

/-! ### Gauss norm point on the unit-radius Tate algebra -/

section TateAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*} [NormedCommRing K] [IsUltrametricDist K] [NormMulClass K] [NormOneClass K]

/-- On the unit-radius restricted power series ring `K⟨X_σ⟩`, the Gauss norm defines the top point
of the Berkovich spectrum, and both the spectral seminorm and the supremum over the Berkovich
spectrum equal the Gauss norm on every series `f`. -/
theorem gaussNorm_point_tateAlgebra
    (f : IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) :
    let T := IsRestricted.subring (R := K) (fun _ : σ ↦ 1)
    (normPoint : Spectrum T) f = gaussNorm norm (fun _ : σ ↦ 1) (f : MvPowerSeries σ K) ∧
      (∀ x : Spectrum T, x ≤ normPoint) ∧
      sSup (Set.range fun x : Spectrum T ↦ x f) = ‖f‖ ∧
      smoothingFun (normRingSeminorm T) f = ‖f‖ :=
  ⟨(normPoint_apply f).trans (norm_eq_gaussNorm f), fun _ ↦ le_top,
    sSup_range_eval_of_normMulClass f,
    (smoothingFun_eq_sSup f).trans (sSup_range_eval_of_normMulClass f)⟩

end TateAlgebra

/-! ### Trivial square-zero extensions and dual numbers -/

private theorem eps_checks_of_sq_zero_of_norm_one {A : Type*} [SeminormedCommRing A] {a : A}
    (ha_sq : a * a = 0) (ha_norm : ‖a‖ = 1) :
    ‖a‖ = 1 ∧
      smoothingFun (normRingSeminorm A) a = 0 ∧
      sSup (Set.range fun x : Spectrum A ↦ x a) = 0 ∧
      ‖a * a‖ ≠ ‖a‖ * ‖a‖ ∧
      ¬∃ x : Spectrum A, ∀ b, x b = ‖b‖ := by
  have hnil : IsNilpotent a := ⟨2, by rw [sq, ha_sq]⟩
  have hmul : ‖a * a‖ ≠ ‖a‖ * ‖a‖ := by
    rw [ha_sq, norm_zero, ha_norm, mul_one]
    exact zero_ne_one
  exact ⟨ha_norm, smoothingFun_eq_zero_of_isNilpotent hnil,
    sSup_range_eval_eq_zero_of_isNilpotent hnil, hmul,
    not_exists_apply_eq_norm_of_isNilpotent hnil (by rw [ha_norm]; exact one_ne_zero)⟩

section TrivSqZeroExt

private noncomputable def trivSqZeroExtHomeomorph (R M : Type*) [SeminormedRing R]
    [SeminormedAddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul R M]
    [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    Spectrum (TrivSqZeroExt R M) ≃ₜ Spectrum R :=
  retractHomeomorph
    (TrivSqZeroExt.inlHom R M)
    (TrivSqZeroExt.isBounded_inlHom R M)
    (TrivSqZeroExt.fstHom ℕ R M).toRingHom
    (TrivSqZeroExt.isBounded_fstHom ℕ R M)
    (fun r ↦ by simp)
    (fun y ↦ by simpa using TrivSqZeroExt.isNilpotent_sub_inl_fst y)

/-- Over a normed division ring `K`, the Berkovich spectrum of `DualNumber K` has a unique
point. -/
theorem unique_dualNumber (K : Type*) [NormedDivisionRing K] :
    Nonempty (Unique (Spectrum (DualNumber K))) :=
  ⟨(trivSqZeroExtHomeomorph K K).toEquiv.unique⟩

/-- Over any normed field `K`, the square-zero generator `ε` of `DualNumber K` has norm `1` while
both its spectral seminorm and its supremum over `Spectrum (DualNumber K)` vanish, the norm
is not multiplicative at `ε`, and no point of `Spectrum (DualNumber K)` equals the norm. -/
theorem dualNumber_eps_checks (K : Type*) [NormedField K] :
    let ε : DualNumber K := DualNumber.eps
    ‖ε‖ = 1 ∧
      smoothingFun (normRingSeminorm (DualNumber K)) ε = 0 ∧
      sSup (Set.range fun x : Spectrum (DualNumber K) ↦ x ε) = 0 ∧
      ‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖ ∧
      ¬∃ x : Spectrum (DualNumber K), ∀ y, x y = ‖y‖ :=
  eps_checks_of_sq_zero_of_norm_one DualNumber.eps_mul_eps (by
    rw [TrivSqZeroExt.norm_def, DualNumber.fst_eps, DualNumber.snd_eps, norm_zero, norm_one,
      zero_add])

end TrivSqZeroExt

section MaxDualNumber

private noncomputable def maxDualNumberHomeomorph (K : Type*) [NormedCommRing K]
    [IsUltrametricDist K] :
    Spectrum (MaxDualNumber K) ≃ₜ Spectrum K :=
  retractHomeomorph
    (MaxDualNumber.inlHom K)
    (MaxDualNumber.isBounded_inlHom K)
    (MaxDualNumber.fstHom K)
    (MaxDualNumber.isBounded_fstHom K)
    MaxDualNumber.fstHom_inlHom
    MaxDualNumber.isNilpotent_sub_inlHom_fstHom

/-- Over an ultrametric normed field `K`, the ultrametric dual numbers `MaxDualNumber K` have a
singleton Berkovich spectrum, while `MaxDualNumber.eps` has norm `1`, spectral seminorm `0`, and
shows that the ambient ultrametric norm does not lie in `Spectrum (MaxDualNumber K)`. -/
theorem maxDualNumber_eps_checks (K : Type*) [NormedField K] [IsUltrametricDist K] :
    let ε : MaxDualNumber K := MaxDualNumber.eps
    Nonempty (Unique (Spectrum (MaxDualNumber K))) ∧
      ‖ε‖ = 1 ∧
      smoothingFun (normRingSeminorm (MaxDualNumber K)) ε = 0 ∧
      sSup (Set.range fun x : Spectrum (MaxDualNumber K) ↦ x ε) = 0 ∧
      ‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖ ∧
      ¬∃ x : Spectrum (MaxDualNumber K), ∀ y, x y = ‖y‖ :=
  ⟨⟨(maxDualNumberHomeomorph K).toEquiv.unique⟩,
    eps_checks_of_sq_zero_of_norm_one MaxDualNumber.eps_mul_eps MaxDualNumber.norm_eps⟩

end MaxDualNumber

/-! ### Boundary cases, negative control, and functoriality checks -/

/-- On the zero ring `PUnit`, `Spectrum PUnit` is empty and both sides of Berkovich's spectral
formula evaluate to `0`. -/
theorem punit_spectrum_empty (a : PUnit) :
    IsEmpty (Spectrum PUnit) ∧
      smoothingFun (normRingSeminorm PUnit) a = 0 ∧
      sSup (Set.range fun x : Spectrum PUnit ↦ x a) = 0 := by
  have hsup : sSup (Set.range fun x : Spectrum PUnit ↦ x a) = 0 := by
    rw [Set.range_eq_empty, Real.sSup_empty]
  exact ⟨inferInstance, (smoothingFun_eq_sSup a).trans hsup, hsup⟩

/-- Every square-zero element vanishes under every point of the Berkovich spectrum, and over a
commutative seminormed ring its supremum over the spectrum is `0`. -/
theorem sq_zero_apply_and_sSup_eq_zero {A : Type*} [SeminormedCommRing A] {a : A}
    (ha : a * a = 0) :
    (∀ x : Spectrum A, x a = 0) ∧
      sSup (Set.range fun x : Spectrum A ↦ x a) = 0 := by
  have hnil : IsNilpotent a := ⟨2, by rwa [sq]⟩
  exact ⟨fun x ↦ x.eq_zero_of_isNilpotent hnil, sSup_range_eval_eq_zero_of_isNilpotent hnil⟩

/-- **Negative control (dropping `map_zero`).** On any ring `R`, the constant-`1` function
`fun _ : R ↦ (1 : ℝ)` is nonnegative, even, subadditive, normalized (`f 1 = 1`), and
multiplicative, yet is never a `MulRingSeminorm R` because `α 0 = 0 ≠ 1`. -/
theorem const_one_not_mulRingSeminorm (R : Type*) [NonAssocRing R] :
    let f : R → ℝ := fun _ ↦ 1
    f 1 = 1 ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f (-x) = f x) ∧
      (∀ x y, f (x + y) ≤ f x + f y) ∧ (∀ x y, f (x * y) = f x * f y) ∧
      ¬∃ α : MulRingSeminorm R, ⇑α = f := by
  refine ⟨rfl, fun _ ↦ zero_le_one, fun _ ↦ rfl, fun _ _ ↦ by norm_num, fun _ _ ↦ by norm_num, ?_⟩
  rintro ⟨α, hα⟩
  have h0 : α 0 = 1 := congrFun hα 0
  linarith [map_zero α]

/-- Pullback along bounded ring homomorphisms preserves `0` and `1`, acts as the identity on
`RingHom.id`, and composes contravariantly. -/
theorem comap_checks {A B C : Type*} [SeminormedRing A] [SeminormedRing B] [SeminormedRing C]
    (φ : A →+* B) (hφ : φ.IsBounded) (ψ : B →+* C) (hψ : ψ.IsBounded)
    (x : Spectrum A) (y : Spectrum B) (z : Spectrum C) :
    comap φ hφ y 0 = 0 ∧
      comap φ hφ y 1 = 1 ∧
      comap (RingHom.id A) RingHom.isBounded_id x = x ∧
      comap φ hφ (comap ψ hψ z) = comap (ψ.comp φ) (hψ.comp hφ) z :=
  ⟨map_zero _, map_one _, by simp, by rw [comap_comp]; rfl⟩

end TauCeti.Spectrum.Examples
