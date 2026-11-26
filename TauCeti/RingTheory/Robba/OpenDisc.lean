/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Basic
public import TauCeti.RingTheory.Robba.Basic

/-!
# Power series on the open unit disc in the Robba ring

A power series `f = ∑_{n ≥ 0} aₙ Xⁿ` over a normed ring lies on the open unit disc
(`PowerSeries.OnOpenDisc f 1`) when `‖aₙ‖ ρⁿ → 0` for every radius `0 < ρ < 1`. Its coefficient
family, extended by zero to negative degrees, is the coefficient family of `f` as a formal Laurent
series, and it converges at a radius `ρ` exactly when `f` is restricted at `ρ`
(`TauCeti.laurentConvergesAt_coeff_coe_iff_isRestricted`). So `f` converges on the whole punctured
open unit disc and lies in every annular subalgebra of the Robba ring.

Products of power series are Cauchy products, which are the convolutions of coefficient families
supported in nonnegative degrees. This gives an injective algebra map
`TauCeti.RobbaRing.ofOnOpenDisc` from the power series on the open unit disc, often written `R⁺` or
`B⁺_rig`, to the Robba ring. Its image consists exactly of the elements with no terms of negative
degree (`TauCeti.RobbaRing.mem_range_ofOnOpenDisc`): a Laurent series without negative terms that
converges on an annulus `r < |t| < 1` converges on the whole disc `|t| < 1`.

## Main definitions

* `TauCeti.RobbaRing.ofOnOpenDisc`: the inclusion of the power series on the open unit disc into
  the Robba ring.

## Main results

* `TauCeti.laurentConvergesAt_coeff_coe_iff_isRestricted`: a power series converges on the circle
  of radius `ρ` as a Laurent series exactly when it is restricted at `ρ`.
* `TauCeti.laurentGaussNorm_coeff_coe`, `TauCeti.RobbaRing.laurentGaussNorm_ofOnOpenDisc`: the
  Gauss norm of a power series as a Laurent series is its Gauss norm as a power series.
* `TauCeti.RobbaRing.ofOnOpenDisc_injective`, `TauCeti.RobbaRing.ofOnOpenDisc_mem_annulus`: the
  inclusion is injective and lands in every annular subalgebra.
* `TauCeti.RobbaRing.mem_range_ofOnOpenDisc`: its image is the set of elements with no terms of
  negative degree.
* `TauCeti.RobbaRing.ofOnOpenDisc_polynomialHom`: a polynomial `P` maps to `P(t)`.
* `TauCeti.RobbaRing.coe_one_add_monomial_pow_natCast`: the binomial theorem, the coefficient of
  `tⁿ` in `(1 + t) ^ N` is `C(N, n)`.
-/

public section

open Filter Topology
open scoped PowerSeries LaurentSeries DiscreteConvolution

namespace TauCeti

/-- **A power series converges on a circle as a Laurent series exactly when it is restricted
there**: the coefficient family of `f` as a formal Laurent series, which vanishes in negative
degrees, satisfies `‖aₙ‖ ρⁿ → 0` along the cofinite filter of `ℤ` exactly when
`‖coeff n f‖ ρⁿ → 0`. -/
theorem laurentConvergesAt_coeff_coe_iff_isRestricted {R : Type*} [NormedRing R] {ρ : ℝ}
    {f : R⟦X⟧} : LaurentConvergesAt ρ (f : R⸨X⸩).coeff ↔ f.IsRestricted ρ := by
  rw [laurentConvergesAt_iff, PowerSeries.isRestricted_iff]
  refine ⟨fun h ↦ (h.comp Nat.cast_injective.tendsto_cofinite).congr fun n ↦ by simp,
    fun h ↦ ?_⟩
  rw [Int.cofinite_eq, Nat.cofinite_eq_atTop] at *
  have htoNat : Tendsto Int.toNat atTop atTop :=
    tendsto_atTop_atTop.2 fun m ↦ ⟨m, fun n hn ↦ by omega⟩
  refine Tendsto.sup (tendsto_const_nhds.congr' ?_) ((h.comp htoNat).congr' ?_)
  · filter_upwards [eventually_lt_atBot 0] with n hn
    simp [PowerSeries.coeff_coe, hn]
  · filter_upwards [eventually_ge_atTop 0] with n hn
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp

/-- **The Gauss norm of a power series as a Laurent series**: at every radius `ρ`, the Gauss norm
`sup_n ‖aₙ‖ ρⁿ` of the coefficient family of `f` as a formal Laurent series, which vanishes in
negative degrees, is the Gauss norm `PowerSeries.gaussNorm` of `f`. -/
theorem laurentGaussNorm_coeff_coe {R : Type*} [NormedRing R] (ρ : ℝ) (f : R⟦X⟧) :
    laurentGaussNorm ρ (f : R⸨X⸩).coeff = f.gaussNorm norm ρ := by
  have hnat (k : ℕ) : ‖(f : R⸨X⸩).coeff k‖ * ρ ^ (k : ℤ) = ‖PowerSeries.coeff k f‖ * ρ ^ k := by
    simp
  have hneg {n : ℤ} (hn : n < 0) : ‖(f : R⸨X⸩).coeff n‖ * ρ ^ n = 0 := by
    simp [PowerSeries.coeff_coe, hn]
  rw [laurentGaussNorm_def, PowerSeries.gaussNorm_eq]
  have h0 : 0 ≤ ⨆ k : ℕ, ‖PowerSeries.coeff k f‖ * ρ ^ k := by
    simpa [PowerSeries.gaussNorm_eq] using
      PowerSeries.gaussNorm_nonneg norm ρ f fun _ ↦ norm_nonneg _
  by_cases hf : f.HasGaussNorm norm ρ
  · have hf' : BddAbove (Set.range fun n : ℤ ↦ ‖(f : R⸨X⸩).coeff n‖ * ρ ^ n) := by
      obtain ⟨B, hB⟩ := hf
      refine ⟨max B 0, Set.forall_mem_range.2 fun n ↦ ?_⟩
      rcases lt_or_ge n 0 with hn | hn
      · exact (hneg hn).le.trans (le_max_right _ _)
      · lift n to ℕ using hn
        exact (hnat n).trans_le (hB ⟨n, rfl⟩) |>.trans (le_max_left _ _)
    refine le_antisymm (ciSup_le fun n ↦ ?_) (ciSup_le fun k ↦ (hnat k).ge.trans (le_ciSup hf' k))
    rcases lt_or_ge n 0 with hn | hn
    · exact (hneg hn).trans_le h0
    · lift n to ℕ using hn
      exact (hnat n).trans_le (le_ciSup hf n)
  · have hf' : ¬BddAbove (Set.range fun n : ℤ ↦ ‖(f : R⸨X⸩).coeff n‖ * ρ ^ n) := by
      refine fun h ↦ hf (h.mono ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨k, hnat k⟩
    rw [Real.iSup_of_not_bddAbove hf, Real.iSup_of_not_bddAbove hf']

namespace RobbaRing

open IsConvolutionRing

variable (R : Type*) [NormedCommRing R]

/-- The coefficient family of a power series on the open unit disc converges on the whole
punctured open unit disc. -/
private theorem coeff_coe_mem_annularCoeff (f : PowerSeries.OnOpenDisc.subring R 1) (r : ℝ) :
    ((f : R⟦X⟧) : R⸨X⸩).coeff ∈ annularCoeff R r :=
  mem_annularCoeff.2 fun _ hρ₀ _ hρ₁ ↦ laurentConvergesAt_coeff_coe_iff_isRestricted.2 <|
    (PowerSeries.OnOpenDisc.mem_subring.1 f.property).isRestricted (by rwa [abs_of_pos hρ₀])

variable [IsUltrametricDist R] [CompleteSpace R]

/-- **The inclusion of the power series on the open unit disc into the Robba ring**: a power series
`∑_{n ≥ 0} aₙ Xⁿ` converging on `|t| < 1` is the Laurent series `∑_{n ≥ 0} aₙ tⁿ`. -/
noncomputable def ofOnOpenDisc : PowerSeries.OnOpenDisc.subring R 1 →ₐ[R] RobbaRing R where
  toFun f := ⟨((f : R⟦X⟧) : R⸨X⸩).coeff,
    annularCoeff_le_robbaCoeff zero_lt_one (coeff_coe_mem_annularCoeff R f 0)⟩
  map_one' := by
    ext n
    simp [HahnSeries.coeff_one, Pi.single_apply]
  map_mul' f g := by
    have h (f : PowerSeries.OnOpenDisc.subring R 1) :
        ∀ i < 0, ((f : R⟦X⟧) : R⸨X⸩).coeff i = 0 :=
      fun i hi ↦ by simp [PowerSeries.coeff_coe, hi]
    ext n
    -- The convolution of two families supported in nonnegative degrees is the Cauchy product.
    simp only [Subring.coe_mul]
    rw [coe_mul, DiscreteConvolution.addRingConvolution_eq_tsum_sub]
    simp only [mul_comm (((f : R⟦X⟧) : R⸨X⸩).coeff (n - _))]
    rcases lt_or_ge n 0 with hn | hn
    · rw [DiscreteConvolution.tsum_mul_sub_eq_zero_of_neg (h g) (h f) hn, PowerSeries.coeff_coe,
        ite_eq_left hn]
    · lift n to ℕ using hn
      rw [DiscreteConvolution.tsum_mul_sub_eq_sum_antidiagonal (h g) (h f) n,
        LaurentSeries.coeff_coe_powerSeries, mul_comm (f : R⟦X⟧), PowerSeries.coeff_mul]
      simp
  map_zero' := by
    ext n
    simp
  map_add' f g := by
    ext n
    simp
  commutes' c := by
    ext n
    by_cases hn : n = 0 <;> simp [hn]

/-- The coefficient family of the image of a power series `f` is that of `f` as a formal Laurent
series. -/
theorem coe_ofOnOpenDisc (f : PowerSeries.OnOpenDisc.subring R 1) :
    (ofOnOpenDisc R f : ℤ → R) = ((f : R⟦X⟧) : R⸨X⸩).coeff :=
  (rfl)

/-- The coefficient of `tⁿ` in the image of a power series `f` is the coefficient of `Xⁿ` in
`f`. -/
@[simp]
theorem coe_ofOnOpenDisc_natCast (f : PowerSeries.OnOpenDisc.subring R 1) (n : ℕ) :
    (ofOnOpenDisc R f : ℤ → R) n = PowerSeries.coeff n (f : R⟦X⟧) := by
  simp [coe_ofOnOpenDisc]

/-- The image of a power series has no terms of negative degree. -/
@[simp]
theorem coe_ofOnOpenDisc_of_neg (f : PowerSeries.OnOpenDisc.subring R 1) {n : ℤ} (hn : n < 0) :
    (ofOnOpenDisc R f : ℤ → R) n = 0 := by
  simp [coe_ofOnOpenDisc, PowerSeries.coeff_coe, hn]

/-- The variable `X` maps to the variable `t` of the Robba ring. -/
theorem ofOnOpenDisc_polynomialHom_X :
    ofOnOpenDisc R (PowerSeries.OnOpenDisc.polynomialHom Polynomial.X) = monomial 1 1 := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [coe_ofOnOpenDisc_of_neg R _ hn, coe_monomial, Pi.single_eq_of_ne (by omega)]
  · lift n to ℕ using hn
    rw [coe_ofOnOpenDisc_natCast, PowerSeries.OnOpenDisc.coe_polynomialHom, Polynomial.coeff_coe,
      Polynomial.coeff_X, coe_monomial, Pi.single_apply]
    grind

/-- **The inclusion on polynomials**: a polynomial `P` maps to its evaluation `P(t)` at the
variable `t` of the Robba ring. -/
@[simp]
theorem ofOnOpenDisc_polynomialHom (P : Polynomial R) :
    ofOnOpenDisc R (PowerSeries.OnOpenDisc.polynomialHom P) =
      Polynomial.aeval (monomial 1 1) P := by
  rw [← PowerSeries.OnOpenDisc.polynomialAlgHom_apply, ← AlgHom.comp_apply]
  congr 1
  exact Polynomial.algHom_ext (by simpa using ofOnOpenDisc_polynomialHom_X R)

/-- `(1 + t) ^ N` is the image of the polynomial `(1 + X) ^ N`, whose coefficients are binomial
coefficients. -/
private theorem one_add_monomial_pow (N : ℕ) : (1 + monomial 1 1 : RobbaRing R) ^ N =
    ofOnOpenDisc R (PowerSeries.OnOpenDisc.polynomialHom ((1 + Polynomial.X) ^ N)) := by
  simp

/-- **The binomial theorem in the Robba ring**: the coefficient of `tⁿ` in `(1 + t) ^ N` is
`C(N, n)`. -/
@[simp]
theorem coe_one_add_monomial_pow_natCast (N n : ℕ) :
    (((1 + monomial 1 1 : RobbaRing R) ^ N : RobbaRing R) : ℤ → R) n = N.choose n := by
  rw [one_add_monomial_pow, coe_ofOnOpenDisc_natCast, PowerSeries.OnOpenDisc.coe_polynomialHom,
    Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- `(1 + t) ^ N` has no terms of negative degree. -/
@[simp]
theorem coe_one_add_monomial_pow_of_neg (N : ℕ) {n : ℤ} (hn : n < 0) :
    (((1 + monomial 1 1 : RobbaRing R) ^ N : RobbaRing R) : ℤ → R) n = 0 := by
  rw [one_add_monomial_pow, coe_ofOnOpenDisc_of_neg R _ hn]

/-- **The inclusion preserves Gauss norms**: at every radius `ρ`, the Gauss norm of the image of a
power series `f` is the Gauss norm `PowerSeries.gaussNorm` of `f`. -/
theorem laurentGaussNorm_ofOnOpenDisc (ρ : ℝ) (f : PowerSeries.OnOpenDisc.subring R 1) :
    laurentGaussNorm ρ (ofOnOpenDisc R f : ℤ → R) = (f : R⟦X⟧).gaussNorm norm ρ :=
  laurentGaussNorm_coeff_coe ρ _

/-- Distinct power series have distinct images in the Robba ring. -/
theorem ofOnOpenDisc_injective : Function.Injective (ofOnOpenDisc R) := fun f g h ↦
  Subtype.ext <| PowerSeries.ext fun n ↦ by
    simpa using congrArg (fun F : RobbaRing R ↦ (F : ℤ → R) n) h

/-- **A power series on the open unit disc converges on every annulus** `r < |t| < 1`. -/
theorem ofOnOpenDisc_mem_annulus (f : PowerSeries.OnOpenDisc.subring R 1) (r : ℝ) :
    ofOnOpenDisc R f ∈ annulus R r :=
  mem_annulus.2 (coeff_coe_mem_annularCoeff R f r)

/-- **The power series on the open unit disc are the elements of the Robba ring with no terms of
negative degree.** A Laurent series without negative terms converging on some annulus
`r < |t| < 1` converges on the whole open unit disc. -/
theorem mem_range_ofOnOpenDisc {g : RobbaRing R} :
    g ∈ (ofOnOpenDisc R).range ↔ ∀ n < 0, (g : ℤ → R) n = 0 := by
  refine ⟨fun ⟨f, hf⟩ n hn ↦ hf ▸ coe_ofOnOpenDisc_of_neg R f hn, fun h ↦ ?_⟩
  set f : R⟦X⟧ := PowerSeries.mk fun k ↦ (g : ℤ → R) k
  have hfg : (f : R⸨X⸩).coeff = g := by
    funext n
    rcases lt_or_ge n 0 with hn | hn
    · simp [PowerSeries.coeff_coe, hn, h n hn]
    · lift n to ℕ using hn
      simp [f]
  have hf : f.OnOpenDisc 1 := by
    refine PowerSeries.onOpenDisc_iff.2 fun r hr₀ hr₁ ↦ ?_
    obtain ⟨s, hs, hg⟩ := mem_robbaCoeff.1 g.property
    -- Convergence at a radius `ρ` between `max s r` and `1` gives convergence at `r < ρ`.
    obtain ⟨ρ, hρ, hρ₁⟩ := exists_between (max_lt hs hr₁)
    rw [max_lt_iff] at hρ
    have hfρ : f.IsRestricted ρ := laurentConvergesAt_coeff_coe_iff_isRestricted.1 <| hfg ▸
      mem_annularCoeff.1 hg ρ (hr₀.trans hρ.2) hρ.1 hρ₁
    exact hfρ.onOpenDisc.isRestricted (by rw [abs_of_pos hr₀]; exact hρ.2)
  exact ⟨⟨f, PowerSeries.OnOpenDisc.mem_subring.2 hf⟩,
    IsConvolutionRing.ext fun n ↦ congrFun hfg n⟩

end RobbaRing

end TauCeti
