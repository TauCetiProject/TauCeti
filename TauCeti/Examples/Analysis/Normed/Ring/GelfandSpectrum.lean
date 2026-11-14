/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.Analysis.Normed.Ring.DualNumber
public import TauCeti.Analysis.Normed.Ring.GelfandSpectrum
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Concrete Gel'fand spectra and checks for Berkovich's spectral formula

We instantiate `TauCeti.GelfandSpectrum` and Berkovich's spectral formula on concrete normed rings:

* **`p`-adic numbers `ℚ_[p]`:** the Gel'fand spectrum is a singleton whose unique point evaluates
  every `x : ℚ_[p]` to its `p`-adic norm `‖x‖`, and `smoothingFun (normRingSeminorm ℚ_[p]) x = ‖x‖`.
* **Multivariate Tate algebras `K⟨X_σ⟩` at unit polyradius:** over any ultrametric normed
  commutative ring `K` with multiplicative normalized norm (in particular any nonarchimedean normed
  field), the Gauss norm defines the greatest point `GelfandSpectrum.normPoint` of the Gel'fand
  spectrum, attaining `sSup {α f | α} = smoothingFun (normRingSeminorm _) f = ‖f‖` for every
  restricted series `f`.
* **Trivial square-zero extensions and dual numbers `K[ε]/(ε²)`:** for both Mathlib's `ℓ¹` norm on
  `DualNumber K` and the ultrametric maximum norm on `TauCeti.MaxDualNumber K`, projection to `K`
  induces a homeomorphism of Gel'fand spectra. Over a normed field `K`, the generator `ε` has
  `‖ε‖ = 1` while `smoothingFun (normRingSeminorm _) ε = sSup {α ε | α} = 0`, `‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖`,
  and the ambient norm does not belong to `GelfandSpectrum`.
* **Boundary cases, negative control, and functoriality:** emptiness on the zero ring `PUnit`,
  vanishing on square-zero elements, failure of the constant-`1` map (which preserves `1` and `*`
  and satisfies subadditivity) to define a `MulRingSeminorm` because `map_zero` fails, and
  contravariant pullback identities.
-/

public section

namespace TauCeti.GelfandSpectrum.Examples

/-! ### `p`-adic numbers `ℚ_[p]` -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Every point of the Gel'fand spectrum of `ℚ_[p]` is the `p`-adic norm, `GelfandSpectrum ℚ_[p]`
has a unique point, and the spectral seminorm of `ℚ_[p]` equals the `p`-adic norm. -/
theorem padic_spectrum (x : ℚ_[p]) :
    (∀ α : GelfandSpectrum ℚ_[p], α x = ‖x‖) ∧
      Nonempty (Unique (GelfandSpectrum ℚ_[p])) ∧
      smoothingFun (normRingSeminorm ℚ_[p]) x = ‖x‖ :=
  ⟨fun α ↦ α.apply_eq_norm x, ⟨inferInstance⟩,
    (smoothingFun_eq_sSup x).trans (sSup_range_eval_of_normMulClass x)⟩

end Padic

/-! ### Gauss norm point on the unit-radius Tate algebra -/

section TateAlgebra

open _root_.MvPowerSeries

variable {σ K : Type*} [NormedCommRing K] [IsUltrametricDist K] [NormMulClass K] [NormOneClass K]

/-- On the unit-radius restricted power series ring `K⟨X_σ⟩`, the Gauss norm defines the top point
of the Gel'fand spectrum, and both the spectral seminorm and the supremum over the Gel'fand
spectrum equal the Gauss norm on every series `f`. -/
theorem gaussNorm_point_tateAlgebra
    (f : IsRestricted.subring (R := K) (fun _ : σ ↦ 1)) :
    let T := IsRestricted.subring (R := K) (fun _ : σ ↦ 1)
    normPoint T f = gaussNorm norm (fun _ : σ ↦ 1) (f : MvPowerSeries σ K) ∧
      (∀ α : GelfandSpectrum T, α ≤ normPoint T) ∧
      sSup (Set.range fun α : GelfandSpectrum T ↦ α f) = ‖f‖ ∧
      smoothingFun (normRingSeminorm T) f = ‖f‖ :=
  ⟨(normPoint_apply f).trans (norm_eq_gaussNorm f), le_normPoint,
    sSup_range_eval_of_normMulClass f,
    (smoothingFun_eq_sSup f).trans (sSup_range_eval_of_normMulClass f)⟩

end TateAlgebra

/-! ### Trivial square-zero extensions and dual numbers -/

section TrivSqZeroExt

/-- Projection to the first component gives a homeomorphism between the Gel'fand spectrum of a
trivial square-zero extension `TrivSqZeroExt R M` (with the `ℓ¹` norm) and `GelfandSpectrum R`. -/
noncomputable def trivSqZeroExtHomeomorph (R M : Type*) [SeminormedRing R]
    [SeminormedAddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul R M]
    [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    GelfandSpectrum (TrivSqZeroExt R M) ≃ₜ GelfandSpectrum R :=
  retractHomeomorph
    (TrivSqZeroExt.inlHom R M)
    ⟨1, zero_lt_one, fun x ↦ by simp⟩
    (TrivSqZeroExt.fstHom ℕ R M).toRingHom
    ⟨1, zero_lt_one, fun y ↦ by
      rw [one_mul, TrivSqZeroExt.norm_def]
      exact le_add_of_nonneg_right (norm_nonneg _)⟩
    (fun x ↦ TrivSqZeroExt.fst_inl M x)
    (fun y ↦ ⟨2, by
      have hy : y - TrivSqZeroExt.inl y.fst = TrivSqZeroExt.inr y.snd := by
        ext <;> simp
      change (y - TrivSqZeroExt.inl y.fst) ^ 2 = 0
      rw [hy, sq, TrivSqZeroExt.inr_mul_inr]⟩)

/-- `trivSqZeroExtHomeomorph` evaluates a spectrum point on `TrivSqZeroExt R M` along `inl`. -/
@[simp]
theorem trivSqZeroExtHomeomorph_apply {R M : Type*} [SeminormedRing R]
    [SeminormedAddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul R M]
    [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
    (β : GelfandSpectrum (TrivSqZeroExt R M)) (r : R) :
    trivSqZeroExtHomeomorph R M β r = β (TrivSqZeroExt.inl r) :=
  retractHomeomorph_apply _ _ _ _ _ _ β r

/-- `(trivSqZeroExtHomeomorph R M).symm` pulls a spectrum point on `R` back along `fst`. -/
@[simp]
theorem trivSqZeroExtHomeomorph_symm_apply {R M : Type*} [SeminormedRing R]
    [SeminormedAddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsBoundedSMul R M]
    [IsBoundedSMul Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
    (α : GelfandSpectrum R) (y : TrivSqZeroExt R M) :
    (trivSqZeroExtHomeomorph R M).symm α y = α y.fst :=
  retractHomeomorph_symm_apply _ _ _ _ _ _ α y

/-- Over a normed division ring `K`, the Gel'fand spectrum of `DualNumber K` has a unique point,
given by `x ↦ ‖x.fst‖`. -/
theorem unique_dualNumber (K : Type*) [NormedDivisionRing K] :
    Nonempty (Unique (GelfandSpectrum (DualNumber K))) :=
  ⟨(trivSqZeroExtHomeomorph K K).toEquiv.unique⟩

/-- Over any normed field `K`, the square-zero generator `ε` of `DualNumber K` has norm `1` while
both its spectral seminorm and its supremum over `GelfandSpectrum (DualNumber K)` vanish, the norm
is not multiplicative at `ε`, and no point of `GelfandSpectrum (DualNumber K)` equals the norm. -/
theorem dualNumber_eps_checks (K : Type*) [NormedField K] :
    let ε : DualNumber K := DualNumber.eps
    ‖ε‖ = 1 ∧
      smoothingFun (normRingSeminorm (DualNumber K)) ε = 0 ∧
      sSup (Set.range fun α : GelfandSpectrum (DualNumber K) ↦ α ε) = 0 ∧
      ‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖ ∧
      ¬∃ α : GelfandSpectrum (DualNumber K), ∀ x, α x = ‖x‖ := by
  intro ε
  have hε_norm : ‖ε‖ = 1 := by
    rw [TrivSqZeroExt.norm_def, DualNumber.fst_eps, DualNumber.snd_eps, norm_zero, norm_one,
      zero_add]
  have hε_nil : IsNilpotent ε := ⟨2, by rw [sq, DualNumber.eps_mul_eps]⟩
  have hε_sm : smoothingFun (normRingSeminorm (DualNumber K)) ε = 0 := by
    rw [← (normRingSeminorm (DualNumber K)).smoothing_apply]
    exact (normRingSeminorm (DualNumber K)).smoothing_eq_zero_of_isNilpotent hε_nil
  have hε_sup : sSup (Set.range fun α : GelfandSpectrum (DualNumber K) ↦ α ε) = 0 := by
    rw [← smoothingFun_eq_sSup, hε_sm]
  have hε_mul : ‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖ := by
    rw [DualNumber.eps_mul_eps, norm_zero, hε_norm, mul_one]
    exact zero_ne_one
  refine ⟨hε_norm, hε_sm, hε_sup, hε_mul, ?_⟩
  rintro ⟨α, hα⟩
  have h0 : α ε = 0 := α.eq_zero_of_isNilpotent hε_nil
  linarith [hα ε, hε_norm]

end TrivSqZeroExt

section MaxDualNumber

/-- Projection to the first component gives a homeomorphism between the Gel'fand spectrum of
`MaxDualNumber K` (with the ultrametric maximum norm) and `GelfandSpectrum K`. -/
noncomputable def maxDualNumberHomeomorph (K : Type*) [NormedCommRing K] [IsUltrametricDist K] :
    GelfandSpectrum (MaxDualNumber K) ≃ₜ GelfandSpectrum K :=
  retractHomeomorph
    (MaxDualNumber.ofDualNumber.toRingHom.comp (TrivSqZeroExt.inlHom K K))
    ⟨1, zero_lt_one, fun x ↦ by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        TrivSqZeroExt.inlHom_apply, MaxDualNumber.norm_ofDualNumber, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, norm_zero, one_mul]
      exact max_eq_left (norm_nonneg x) |>.le⟩
    ((TrivSqZeroExt.fstHom ℕ K K).toRingHom.comp MaxDualNumber.ofDualNumber.symm.toRingHom)
    ⟨1, zero_lt_one, fun y ↦ by
      rw [one_mul]
      have hy : y = MaxDualNumber.ofDualNumber (MaxDualNumber.ofDualNumber.symm y) := by simp
      conv_rhs => rw [hy, MaxDualNumber.norm_ofDualNumber]
      exact le_max_left _ _⟩
    (fun x ↦ by simp)
    (fun y ↦ ⟨2, by
      apply MaxDualNumber.ofDualNumber.symm.injective
      rw [map_zero, map_pow]
      set z : DualNumber K := MaxDualNumber.ofDualNumber.symm y
      have hz : MaxDualNumber.ofDualNumber.symm
          (y - (MaxDualNumber.ofDualNumber.toRingHom.comp (TrivSqZeroExt.inlHom K K))
            (((TrivSqZeroExt.fstHom ℕ K K).toRingHom.comp
              MaxDualNumber.ofDualNumber.symm.toRingHom) y)) =
          TrivSqZeroExt.inr z.snd := by
        ext <;> simp [z]
      rw [hz, sq, TrivSqZeroExt.inr_mul_inr]⟩)

/-- `maxDualNumberHomeomorph K` evaluates a spectrum point on `MaxDualNumber K` along the scalar
inclusion. -/
@[simp]
theorem maxDualNumberHomeomorph_apply {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    (β : GelfandSpectrum (MaxDualNumber K)) (r : K) :
    maxDualNumberHomeomorph K β r = β (MaxDualNumber.ofDualNumber (TrivSqZeroExt.inl r)) :=
  retractHomeomorph_apply _ _ _ _ _ _ β r

/-- `(maxDualNumberHomeomorph K).symm` pulls a spectrum point on `K` back along the first
coefficient projection. -/
@[simp]
theorem maxDualNumberHomeomorph_symm_apply {K : Type*} [NormedCommRing K] [IsUltrametricDist K]
    (α : GelfandSpectrum K) (y : MaxDualNumber K) :
    (maxDualNumberHomeomorph K).symm α y = α (MaxDualNumber.ofDualNumber.symm y).fst :=
  retractHomeomorph_symm_apply _ _ _ _ _ _ α y

/-- Over an ultrametric normed field `K`, the ultrametric dual numbers `MaxDualNumber K` have a
singleton Gel'fand spectrum, while `MaxDualNumber.eps` has norm `1`, spectral seminorm `0`, and
shows that the ambient ultrametric norm does not lie in `GelfandSpectrum (MaxDualNumber K)`. -/
theorem maxDualNumber_eps_checks (K : Type*) [NormedField K] [IsUltrametricDist K] :
    let ε : MaxDualNumber K := MaxDualNumber.eps
    Nonempty (Unique (GelfandSpectrum (MaxDualNumber K))) ∧
      ‖ε‖ = 1 ∧
      smoothingFun (normRingSeminorm (MaxDualNumber K)) ε = 0 ∧
      sSup (Set.range fun α : GelfandSpectrum (MaxDualNumber K) ↦ α ε) = 0 ∧
      ‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖ ∧
      ¬∃ α : GelfandSpectrum (MaxDualNumber K), ∀ x, α x = ‖x‖ := by
  intro ε
  have hε_nil : IsNilpotent ε := ⟨2, by rw [sq, MaxDualNumber.eps_mul_eps]⟩
  have hε_sm : smoothingFun (normRingSeminorm (MaxDualNumber K)) ε = 0 := by
    rw [← (normRingSeminorm (MaxDualNumber K)).smoothing_apply]
    exact (normRingSeminorm (MaxDualNumber K)).smoothing_eq_zero_of_isNilpotent hε_nil
  have hε_sup : sSup (Set.range fun α : GelfandSpectrum (MaxDualNumber K) ↦ α ε) = 0 := by
    rw [← smoothingFun_eq_sSup, hε_sm]
  have hε_mul : ‖ε * ε‖ ≠ ‖ε‖ * ‖ε‖ := by
    rw [MaxDualNumber.eps_mul_eps, norm_zero, MaxDualNumber.norm_eps, mul_one]
    exact zero_ne_one
  refine ⟨⟨(maxDualNumberHomeomorph K).toEquiv.unique⟩,
    MaxDualNumber.norm_eps, hε_sm, hε_sup, hε_mul, ?_⟩
  rintro ⟨α, hα⟩
  have h0 : α ε = 0 := α.eq_zero_of_isNilpotent hε_nil
  linarith [hα ε, MaxDualNumber.norm_eps (K := K)]

end MaxDualNumber

/-! ### Boundary cases, negative control, and functoriality checks -/

/-- On the zero ring `PUnit`, `GelfandSpectrum PUnit` is empty and both sides of Berkovich's
spectral formula evaluate to `0`. -/
theorem punit_spectrum_empty (x : PUnit) :
    IsEmpty (GelfandSpectrum PUnit) ∧
      smoothingFun (normRingSeminorm PUnit) x = 0 ∧
      sSup (Set.range fun α : GelfandSpectrum PUnit ↦ α x) = 0 := by
  have hsup : sSup (Set.range fun α : GelfandSpectrum PUnit ↦ α x) = 0 := by
    rw [Set.range_eq_empty, Real.sSup_empty]
  exact ⟨inferInstance, (smoothingFun_eq_sSup x).trans hsup, hsup⟩

/-- Every square-zero element vanishes under every point of the Gel'fand spectrum, and over a
commutative seminormed ring its supremum over the spectrum is `0`. -/
theorem sq_zero_apply_and_sSup_eq_zero {A : Type*} [SeminormedCommRing A] {x : A}
    (hx : x * x = 0) :
    (∀ α : GelfandSpectrum A, α x = 0) ∧
      sSup (Set.range fun α : GelfandSpectrum A ↦ α x) = 0 := by
  have hnil : IsNilpotent x := ⟨2, by rwa [sq]⟩
  refine ⟨fun α ↦ α.eq_zero_of_isNilpotent hnil, ?_⟩
  rw [← smoothingFun_eq_sSup, ← (normRingSeminorm A).smoothing_apply]
  exact (normRingSeminorm A).smoothing_eq_zero_of_isNilpotent hnil

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
    (φ : A →+* B) (hφ : ∃ C₁ > 0, ∀ x, ‖φ x‖ ≤ C₁ * ‖x‖)
    (ψ : B →+* C) (hψ : ∃ C₂ > 0, ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (hψφ : ∃ C₃ > 0, ∀ x, ‖(ψ.comp φ) x‖ ≤ C₃ * ‖x‖)
    (hid : ∃ C₀ > 0, ∀ x : A, ‖x‖ ≤ C₀ * ‖x‖)
    (α : GelfandSpectrum A) (β : GelfandSpectrum B) (γ : GelfandSpectrum C) :
    comap φ hφ β 0 = 0 ∧
      comap φ hφ β 1 = 1 ∧
      comap (RingHom.id A) hid α = α ∧
      comap φ hφ (comap ψ hψ γ) = comap (ψ.comp φ) hψφ γ :=
  ⟨map_zero _, map_one _, comap_id hid α, comap_comp ψ hψ φ hφ hψφ γ⟩

end TauCeti.GelfandSpectrum.Examples
