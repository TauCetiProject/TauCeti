/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.ModularForms.DedekindEta.LimitFormula
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
public import TauCeti.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Units.Dirichlet
import TauCeti.RingTheory.FractionalIdeal.Norm

/-!
# The Chowla–Selberg formula in class-mean form

Let `K` be an imaginary quadratic field of discriminant `-D`, `χ` its quadratic character and `σ`
a complex embedding. For each ideal class `C` choose `τ_C` in the upper half-plane with `σ(𝔞_C)`
homothetic to `ℤ + ℤ τ_C` for a fractional ideal `𝔞_C` of class `C`. The class-mean form of the
formula of Chowla and Selberg is

`(1 / h_K) ∑_C log (4 π Im τ_C |η(τ_C)|⁴) = γ + log (2π / √D) - L'(1, χ) / L(1, χ)`,

where `log (4 π Im τ |η(τ)|⁴)` is the logarithmic period `UpperHalfPlane.logPeriod τ`.

The proof compares the expansions at `s = 1` of the two sides of
`∑_C (2 / √D)ˢ E(τ_C, s) = w ζ_K(s) = w ζ(s) L(s, χ)`, `w` the number of roots of unity of `K`
and `E(τ, s)` the real Epstein zeta function of `ℤ τ + ℤ`. On the left, Kronecker's first limit
formula (`UpperHalfPlane.tendsto_epsteinZeta_sub`) gives the constant terms; on the right the
pole of `ζ` and the derivative of `L(s, χ)` at `1`. Comparing the residues recovers the class
number formula `w L(1, χ) = 2π h_K / √D`, and comparing the constant terms gives the formula. The
number `w` cancels, so no assumption `D > 4` is needed.

The identity of Dirichlet series uses, for each class, Tau Ceti's description of the partial zeta
function of an ideal class as a sum over the points of an ideal lattice in the fundamental cone
(`TauCeti.LFunctions.hasSum_norm_cpow_idealLattice_fundamentalCone`); in an imaginary quadratic
field the unit rank is `0` and the cone is the set of points of nonzero norm. The normalisation
`2 / √D` is the covolume identity `N(𝔞) √D = 2 |c|² Im τ` for `σ(𝔞) = c (ℤ + ℤ τ)`
(`TauCeti.NumberField.absNorm_mul_sqrt_abs_discr_of_image_eq`), proved by computing the
discriminant of a `ℤ`-basis of `𝔞` through the trace form, which is `Tr x = 2 Re (σ x)`
(`TauCeti.NumberField.trace_eq_two_mul_re_of_finrank_eq_two`).

## Main results

* `TauCeti.NumberField.absNorm_mul_sqrt_abs_discr_of_image_eq`: the covolume of an ideal lattice.
* `TauCeti.NumberField.chowlaSelberg_classMean`: the Chowla–Selberg formula in class-mean form.
* `TauCeti.NumberField.chowlaSelberg_classMean_fundamentalDiscriminantChar`: the same formula for
  the quadratic character of the discriminant of `K`, with no hypothesis on `ζ_K`.

## References

The argument is adapted from the file `src/Lib/CM/ChowlaSelberg.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC), declarations
`New.hasSum_ideal_classes`, `New.CMLattice.riemannZeta₁_mul_entireL_eq_sum` and
`New.CMLattice.sum_kronecker_terms`, which prove the case of a prime `D ≡ 7 (mod 8)` for the
lattices of CM curves in a different normalisation.

* S. Chowla, A. Selberg, *On Epstein's zeta-function*, J. reine angew. Math. 227 (1967), 86–110:
  §12, p. 109, with Kronecker's limit formula in the form of §6, (39), p. 97.
-/

public section

noncomputable section

open Complex Filter Module NumberField NumberField.InfinitePlace Set Topology UpperHalfPlane
open scoped Matrix nonZeroDivisors Real

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### A fractional ideal whose image is homothetic to `ℤ τ + ℤ` -/

section Lattice

variable (σ : K →+* ℂ) {I : FractionalIdeal (𝓞 K)⁰ K} {c : ℂ} {τ : ℍ}

/-- The `ℤ`-linear map `y ↦ σ y / c` on a fractional ideal. -/
private def divEmbedding (I : FractionalIdeal (𝓞 K)⁰ K) (c : ℂ) :
    (I : Submodule (𝓞 K) K) →ₗ[ℤ] ℂ :=
  LinearMap.mulLeft ℤ c⁻¹ ∘ₗ σ.toAddMonoidHom.toIntLinearMap ∘ₗ
    (I : Submodule (𝓞 K) K).subtype.restrictScalars ℤ

omit [NumberField K] in
private theorem divEmbedding_apply (y : (I : Submodule (𝓞 K) K)) :
    divEmbedding σ I c y = c⁻¹ * σ y := (rfl)

omit [NumberField K] in
private theorem divEmbedding_injective (hc : c ≠ 0) : Function.Injective (divEmbedding σ I c) :=
  fun _ _ h ↦ Subtype.ext <| σ.injective <| mul_left_cancel₀ (inv_ne_zero hc) h

omit [NumberField K] in
private theorem range_divEmbedding (hc : c ≠ 0)
    (hI : σ '' (I : Set K) = (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) :
    LinearMap.range (divEmbedding σ I c) = τ.periodPair.lattice := by
  ext z
  rw [LinearMap.mem_range, PeriodPair.lattice, periodPair_ω₁, periodPair_ω₂, Set.pair_comm]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨l, hl, hly⟩ : σ y ∈ (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ) :=
      hI ▸ Set.mem_image_of_mem σ y.property
    rwa [divEmbedding_apply, ← hly, inv_mul_cancel_left₀ hc]
  · intro hz
    obtain ⟨y, hy, hyz⟩ : c * z ∈ σ '' (I : Set K) := hI ▸ Set.mem_image_of_mem _ hz
    exact ⟨⟨y, hy⟩, by rw [divEmbedding_apply, hyz, inv_mul_cancel_left₀ hc]⟩

/-- If `σ(I) = c (ℤ + ℤ τ)`, the map `y ↦ σ y / c` identifies `I` with the lattice `ℤ τ + ℤ`. -/
private def idealEquivLattice (hc : c ≠ 0)
    (hI : σ '' (I : Set K) = (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) :
    (I : Submodule (𝓞 K) K) ≃ₗ[ℤ] τ.periodPair.lattice :=
  (LinearEquiv.ofInjective (divEmbedding σ I c) (divEmbedding_injective σ hc)).trans
    (LinearEquiv.ofEq _ _ (range_divEmbedding σ hc hI))

omit [NumberField K] in
private theorem apply_idealEquivLattice_symm (hc : c ≠ 0)
    (hI : σ '' (I : Set K) = (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ))
    (l : τ.periodPair.lattice) :
    σ ((idealEquivLattice σ hc hI).symm l) = c * l := by
  set y := (idealEquivLattice σ hc hI).symm l
  have h : (idealEquivLattice σ hc hI y : ℂ) = c⁻¹ * σ y := by
    simp only [idealEquivLattice, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.ofInjective_apply, divEmbedding_apply]
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, mul_inv_cancel_left₀ hc]

/-- A quadratic field with a fractional ideal whose image under `σ` is homothetic to `ℤ + ℤ τ` is
imaginary: `σ` is not real, since `τ` is not. -/
private theorem isTotallyComplex_of_image_eq (hK : finrank ℚ K = 2) (hc : c ≠ 0)
    (hI : σ '' (I : Set K) = (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) :
    IsTotallyComplex K := by
  classical
  obtain ⟨y₀, -, hy₀⟩ : c * τ ∈ σ '' (I : Set K) :=
    hI ▸ ⟨τ, Submodule.subset_span (by simp), rfl⟩
  obtain ⟨y₁, -, hy₁⟩ : c * 1 ∈ σ '' (I : Set K) :=
    hI ▸ ⟨1, Submodule.subset_span (by simp), rfl⟩
  have hσ : ¬ ComplexEmbedding.IsReal σ := fun h ↦ by
    have h' := congr($(ComplexEmbedding.isReal_iff.mp h) (y₀ / y₁))
    rw [ComplexEmbedding.conjugate_coe_eq, map_div₀, hy₀, hy₁, mul_one,
      mul_div_cancel_left₀ _ hc, conj_eq_iff_im] at h'
    exact τ.im_pos.ne' h'
  have h1 : 0 < nrComplexPlaces K :=
    Fintype.card_pos_iff.mpr ⟨⟨mk σ, isComplex_mk_iff.mpr hσ⟩⟩
  exact .of_finrank_le_two_mul_nrComplexPlaces (by omega)

/-- **The covolume of an ideal lattice of an imaginary quadratic field.** If the image of a
fractional ideal `I` under a complex embedding `σ` is `c (ℤ + ℤ τ)`, then
`N(I) √|d_K| = 2 |c|² Im τ`: both sides are twice the area of `ℂ / σ(I)`. -/
theorem absNorm_mul_sqrt_abs_discr_of_image_eq (hK : finrank ℚ K = 2) (hc : c ≠ 0)
    (hI : σ '' (I : Set K) = (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) :
    (FractionalIdeal.absNorm I : ℝ) * √|(discr K : ℝ)| = 2 * ‖c‖ ^ 2 * τ.im := by
  classical
  have := isTotallyComplex_of_image_eq σ hK hc hI
  -- A `ℤ`-basis `v` of `I` with `σ v₀ = c τ`, `σ v₁ = c`, and a `ℚ`-basis `B` of `K` coming from a
  -- `ℤ`-basis of `𝓞 K`.
  let bI : Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K) :=
    τ.periodPair.latticeBasis.map (idealEquivLattice σ hc hI).symm
  let v : Fin 2 → K := (↑) ∘ bI
  have hv (i : Fin 2) : σ (v i) = c * τ.periodPair.latticeBasis i :=
    apply_idealEquivLattice_symm σ hc hI _
  have h2 : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hK]
  let b := (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq h2)
  let B : Basis (Fin 2) ℚ K := b.localizationLocalization ℚ ℤ⁰ K
  have hN : |B.det v| = FractionalIdeal.absNorm I := FractionalIdeal.abs_det_basis_change b I bI
  -- `disc(v) = det_B(v)² disc(B) = N(I)² d_K`.
  have hvB : v = B ᵥ* (B.toMatrix v).map (algebraMap ℚ K) := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Basis.toMatrix_apply, mul_comm (B _),
      ← Algebra.smul_def, B.sum_repr]
  have hdisc : Algebra.discr ℚ v = B.det v ^ 2 * discr K := by
    rw [hvB, Algebra.discr_of_matrix_vecMul, ← Basis.det_apply, ← hvB,
      Algebra.discr_localizationLocalization, ← NumberField.discr_eq_discr K b, eq_intCast]
  -- `disc(v) = det (Tr(vᵢ vⱼ)) = -4 |c|⁴ (Im τ)²`, from `Tr x = 2 Re (σ x)`.
  have htr (i j : Fin 2) : (Algebra.trace ℚ K (v i * v j) : ℝ) =
      2 * (c ^ 2 * τ.periodPair.latticeBasis i * τ.periodPair.latticeBasis j).re := by
    rw [trace_eq_two_mul_re_of_finrank_eq_two hK σ, map_mul, hv, hv]
    ring_nf
  have hcomp : (Algebra.discr ℚ v : ℝ) = -(4 * ‖c‖ ^ 4 * τ.im ^ 2) := by
    rw [Algebra.discr_def, Matrix.det_fin_two, show ‖c‖ ^ 4 = (‖c‖ ^ 2) ^ 2 by ring,
      Complex.sq_norm, normSq_apply]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Rat.cast_sub, Rat.cast_mul, htr,
      PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one, periodPair_ω₁, periodPair_ω₂,
      mul_one, sq, mul_re, mul_im, coe_re, coe_im]
    ring
  -- Hence `N(I)² |d_K| = 4 |c|⁴ (Im τ)²`, and both sides of the claim are nonnegative.
  have hsq : ((FractionalIdeal.absNorm I : ℝ) * √|(discr K : ℝ)|) ^ 2 =
      (2 * ‖c‖ ^ 2 * τ.im) ^ 2 := by
    have h := congrArg (fun q : ℚ ↦ |(q : ℝ)|) hdisc
    simp only [hcomp, abs_neg, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, abs_mul, abs_pow,
      ← Rat.cast_abs, hN] at h
    rw [abs_norm, abs_of_pos τ.im_pos] at h
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    linear_combination -h
  have := τ.im_pos
  exact (sq_eq_sq₀ (mul_nonneg (by exact_mod_cast FractionalIdeal.absNorm_nonneg _)
    (Real.sqrt_nonneg _)) (by positivity)).mp hsq

/-- If `σ(I) = c (ℤ + ℤ τ)`, the identification of `ℤ²` with the lattice of `I` in the mixed space
sending `(m, n)` to the image of the point `y ∈ I` with `σ y = c (m τ + n)`. -/
private def intPairEquivIdealLattice {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hc : c ≠ 0)
    (hI : σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) :
    (ℤ × ℤ) ≃ mixedEmbedding.idealLattice K I :=
  (τ.periodPair.latticeEquivProd.symm.trans (idealEquivLattice σ hc hI).symm).toEquiv.trans
    (mixedEmbedding.idealLatticeEquiv I)

private theorem intPairEquivIdealLattice_zero {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hc : c ≠ 0)
    (hI : σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) :
    intPairEquivIdealLattice σ hc hI 0 = 0 :=
  Subtype.ext (by simp [intPairEquivIdealLattice])

private theorem norm_intPairEquivIdealLattice [IsTotallyComplex K] (hK : finrank ℚ K = 2)
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hc : c ≠ 0)
    (hI : σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) (p : ℤ × ℤ) :
    mixedEmbedding.norm (intPairEquivIdealLattice σ hc hI p : mixedEmbedding.mixedSpace K) =
      ‖c‖ ^ 2 * ‖(p.1 : ℂ) * τ + p.2‖ ^ 2 := by
  simp only [intPairEquivIdealLattice, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
    mixedEmbedding.coe_idealLatticeEquiv, mixedEmbedding.norm_eq_norm]
  rw [Rat.cast_abs, abs_norm_eq_norm_sq_of_finrank_eq_two hK σ, LinearEquiv.trans_apply,
    apply_idealEquivLattice_symm, PeriodPair.latticeEquiv_symm_apply, norm_mul, mul_pow]
  simp

/-- If `σ(I) = c (ℤ + ℤ τ)`, then for `s > 1` the lattice sum
`∑_{(m, n)} (k Im τ / |m τ + n|²) ^ s`, `k = 2 / √|d_K|`, is `w` times the partial zeta function
`∑_{𝔟 ∈ [I]⁻¹} N(𝔟)^(-s)`, `w` the number of roots of unity. -/
private theorem hasSum_mul_im_div_norm_sq_rpow [IsTotallyComplex K] (hK : finrank ℚ K = 2)
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hc : c ≠ 0)
    (hI : σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : ℤ × ℤ ↦
        ((((2 / √|(discr K : ℝ)|) * (τ.im / ‖(p.1 : ℂ) * τ + p.2‖ ^ 2)) ^ s : ℝ) : ℂ))
      (Units.torsionOrder K * ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-(s : ℂ))) := by
  set N : ℝ := (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
  have hN : 0 < N := Rat.cast_pos.mpr (FractionalIdeal.absNorm_pos I.ne_zero)
  have hcov := absNorm_mul_sqrt_abs_discr_of_image_eq σ hK hc hI
  have hd := sqrt_abs_cast_discr_pos K
  -- Transport Tau Ceti's sum over the points of the lattice of `I` in the fundamental cone to
  -- `ℤ² ∖ {0}`.
  let Φ := intPairEquivIdealLattice σ hc hI
  have hΦ := norm_intPairEquivIdealLattice σ hK hc hI
  have hcone (p : ℤ × ℤ) :
      p ∈ ({0}ᶜ : Set (ℤ × ℤ)) ↔ (Φ p : mixedEmbedding.mixedSpace K) ∈
        mixedEmbedding.fundamentalCone K := by
    rw [mixedEmbedding.fundamentalCone.mem_iff_norm_ne_zero_of_rank_eq_zero
      (Units.rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K hK), Ne,
      mixedEmbedding.norm_coe_idealLattice_eq_zero_iff, Set.mem_compl_singleton_iff]
    rw [← intPairEquivIdealLattice_zero σ hc hI, Φ.injective.eq_iff]
  have h0 := (Equiv.subtypeEquiv Φ hcone).hasSum_iff.mpr
    ((TauCeti.LFunctions.hasSum_norm_cpow_idealLattice_fundamentalCone I
      (s := s) (by simpa using hs)).mul_left ((N : ℂ) ^ (s : ℂ)))
  have hval : (N : ℂ) ^ (s : ℂ) * ((Units.torsionOrder K : ℂ) *
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-(s : ℂ)) *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-(s : ℂ))) =
      Units.torsionOrder K * ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-(s : ℂ)) := by
    have hNs : (N : ℂ) ^ (s : ℂ) ≠ 0 := by
      simp [cpow_eq_zero_iff, hN.ne']
    rw [show ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) = (N : ℂ) by
      simp [N], cpow_neg]
    field_simp
  rw [hval] at h0
  refine (hasSum_subtype_iff_of_support_subset fun p hp ↦ ?_).mp (h0.congr_fun fun p ↦ ?_)
  · rintro rfl
    simp [(zero_lt_one.trans hs).ne'] at hp
  · -- `N^s (|c|² |w|²)^(-s) = (k Im τ / |w|²)^s`, since `k Im τ = N / |c|²`.
    have hcov' : N * √|(discr K : ℝ)| = 2 * ‖c‖ ^ 2 * τ.im := hcov
    have hk : 2 / √|(discr K : ℝ)| * τ.im = N / ‖c‖ ^ 2 := by
      field_simp
      linear_combination -hcov'
    simp only [Function.comp_apply, Equiv.subtypeEquiv_apply]
    rw [hΦ]
    rw [← mul_div_assoc, hk, div_div, Real.div_rpow hN.le (by positivity), ofReal_div,
      div_eq_mul_inv, cpow_neg, ofReal_cpow hN.le, ofReal_cpow (by positivity)]

end Lattice

/-! ### Comparing the expansions at `s = 1` -/

/-- If `Eᵢ(s) = π / (s - 1) + Lᵢ + o(1)` as `s → 1⁺`, then
`∑ᵢ kˢ (s - 1) Eᵢ(s) = n k π + (s - 1) B(s)` for `s > 1`, `n` the number of terms, where the
bracket `B(s)` tends to `∑ᵢ (π k log k + k Lᵢ)`. -/
private theorem sum_rpow_mul_sub_one_mul_eq {ι : Type*} [Fintype ι] {k : ℝ} (hk : 0 < k)
    {E : ι → ℝ → ℝ} {L : ι → ℝ}
    (hE : ∀ i, Tendsto (fun s ↦ E i s - π / (s - 1)) (𝓝[>] 1) (𝓝 (L i))) :
    (∀ᶠ s : ℝ in 𝓝[>] 1, ∑ i, k ^ s * ((s - 1) * E i s) =
      Fintype.card ι * (k * π) + (s - 1) * ∑ i, (π * ((k ^ s - k) / (s - 1)) +
        k ^ s * (E i s - π / (s - 1)))) ∧
    Tendsto (fun s : ℝ ↦ ∑ i, (π * ((k ^ s - k) / (s - 1)) +
      k ^ s * (E i s - π / (s - 1)))) (𝓝[>] 1)
      (𝓝 (∑ i, (π * (k * Real.log k) + k * L i))) := by
  have hk1 : HasDerivAt (fun s : ℝ ↦ k ^ s) (k * Real.log k) 1 := by
    simpa using (Real.hasStrictDerivAt_const_rpow hk 1).hasDerivAt
  have hpow : Tendsto (fun s : ℝ ↦ k ^ s) (𝓝[>] 1) (𝓝 k) := by
    simpa using hk1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun s : ℝ ↦ (k ^ s - k) / (s - 1)) (𝓝[>] 1) (𝓝 (k * Real.log k)) := by
    refine (hk1.tendsto_slope.mono_left (nhdsWithin_mono _ fun s hs ↦ ne_of_gt hs)).congr
      fun s ↦ ?_
    simp [slope_def_field]
  refine ⟨?_, tendsto_finsetSum _ fun i _ ↦ (hslope.const_mul π).add (hpow.mul (hE i))⟩
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs.ne'
  rw [show (Fintype.card ι : ℝ) * (k * π) = ∑ _i : ι, k * π by simp, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  field_simp
  ring

/-- Let `W` be complex differentiable at `1`, and let `W(s) = ∑ᵢ kˢ (s - 1) Eᵢ(s)` for real
`s > 1` near `1`, where `Eᵢ(s) = π / (s - 1) + Lᵢ + o(1)`. Then `W(1) = n k π`, `n` the number of
terms, and `W'(1) = ∑ᵢ (π k log k + k Lᵢ)`. -/
private theorem value_and_deriv_eq_of_tendsto {ι : Type*} [Fintype ι] {k : ℝ} (hk : 0 < k)
    {E : ι → ℝ → ℝ} {L : ι → ℝ}
    (hE : ∀ i, Tendsto (fun s ↦ E i s - π / (s - 1)) (𝓝[>] 1) (𝓝 (L i)))
    {W : ℂ → ℂ} {W' : ℂ} (hW : HasDerivAt W W' 1)
    (hWE : ∀ᶠ s : ℝ in 𝓝[>] 1, W s = ((∑ i, k ^ s * ((s - 1) * E i s) : ℝ) : ℂ)) :
    W 1 = (Fintype.card ι * (k * π) : ℝ) ∧
      W' = (∑ i, (π * (k * Real.log k) + k * L i) : ℝ) := by
  obtain ⟨hEq, hR⟩ := sum_rpow_mul_sub_one_mul_eq hk hE
  have hsub : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_sub_right (1 : ℝ)).tendsto 1)
  have hval : Tendsto (fun s : ℝ ↦ ∑ i, k ^ s * ((s - 1) * E i s)) (𝓝[>] 1)
      (𝓝 (Fintype.card ι * (k * π))) := by
    have h := (hsub.mul hR).const_add (Fintype.card ι * (k * π))
    rw [zero_mul, add_zero] at h
    exact h.congr' (hEq.mono fun s hs ↦ hs.symm)
  have hW1 : Tendsto (fun s : ℝ ↦ W s) (𝓝[>] 1) (𝓝 (W 1)) :=
    (hW.continuousAt.tendsto.comp (continuous_ofReal.tendsto 1)).mono_left nhdsWithin_le_nhds
  have h1 : W 1 = (Fintype.card ι * (k * π) : ℝ) :=
    tendsto_nhds_unique hW1 ((continuous_ofReal.tendsto _).comp hval |>.congr' <|
      hWE.mono fun s hs ↦ hs.symm)
  refine ⟨h1, ?_⟩
  -- The slopes of `W` at `1` are the brackets.
  have hWs : Tendsto (fun s : ℝ ↦ (s - 1 : ℂ)⁻¹ * (W s - W 1)) (𝓝[>] 1) (𝓝 W') := by
    refine ((HasDerivAt.comp_ofReal (z := 1) (by simpa using hW)).tendsto_slope.mono_left
      (nhdsWithin_mono _ fun s hs ↦ ne_of_gt hs)).congr fun s ↦ ?_
    simp [slope, Complex.real_smul]
  refine tendsto_nhds_unique hWs (((continuous_ofReal.tendsto _).comp hR).congr' ?_)
  filter_upwards [hWE, hEq, self_mem_nhdsWithin] with s hs hs' (hs1 : 1 < s)
  have hne : (s - 1 : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hs1.ne'
  simp only [Function.comp_apply, hs, hs', h1]
  push_cast
  field_simp
  ring

/-! ### The class mean -/

/-- A Dirichlet character `χ` modulo `D` with `ζ_K = ζ · L(·, χ)` on `Re s > 1`, for `K` quadratic
of discriminant `-D`, is the character of `K`, so it is not trivial. -/
private theorem ne_one_of_dedekindZeta_eq (hK : finrank ℚ K = 2) {D : ℕ} [NeZero D]
    (hD : discr K = -(D : ℤ)) {χ : DirichletCharacter ℂ D}
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s) : χ ≠ 1 := by
  have hDK : (discr K).natAbs = D := by omega
  subst hDK
  have hχK : χ = (Multiquadratic.fundamentalDiscriminantChar (discr K)
      (Multiquadratic.isFundamentalDiscr_discr hK)).ringHomComp (Int.castRingHom ℂ) := by
    refine DirichletCharacter.eq_of_LFunction_eq _ fun s hs ↦
      mul_left_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs) ?_
    rw [← hχ s hs, dedekindZeta_eq_riemannZeta_mul_LFunction hK hs]
  exact hχK ▸ Multiquadratic.ringHomComp_fundamentalDiscriminantChar_discr_ne_one hK

/-- Summing `hasSum_mul_im_div_norm_sq_rpow` over a system of representatives: for `s > 1`,
`∑_C kˢ E(τ_C, s) = w ζ_K(s)`, with `k = 2 / √|d_K|` and `w` the number of roots of unity. -/
private theorem sum_rpow_mul_epsteinZeta_eq [IsTotallyComplex K] (hK : finrank ℚ K = 2)
    (σ : K →+* ℂ) {τ : ClassGroup (𝓞 K) → ℍ} {I : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hIC : ∀ C, ClassGroup.mk K (I C) = C) {c : ClassGroup (𝓞 K) → ℂ} (hc : ∀ C, c C ≠ 0)
    (hI : ∀ C, σ '' ((I C : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (c C * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ C : ℂ)} : Set ℂ)) {s : ℝ} (hs : 1 < s) :
    ((∑ C, (2 / √|(discr K : ℝ)|) ^ s * (τ C).epsteinZeta s : ℝ) : ℂ) =
      Units.torsionOrder K * dedekindZeta K s := by
  have hk : 0 < 2 / √|(discr K : ℝ)| := div_pos two_pos (sqrt_abs_cast_discr_pos K)
  have hclass (C : ClassGroup (𝓞 K)) :
      (((2 / √|(discr K : ℝ)|) ^ s * (τ C).epsteinZeta s : ℝ) : ℂ) =
        Units.torsionOrder K * ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
          ClassGroup.mk0 𝔟 = (ClassGroup.mk K (I C))⁻¹},
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-(s : ℂ)) := by
    refine HasSum.unique ?_ (hasSum_mul_im_div_norm_sq_rpow σ hK (hc C) (hI C) hs)
    refine (hasSum_ofReal.mpr ((hasSum_epsteinZeta (τ C) hs).mul_left _)).congr_fun fun p ↦ ?_
    rw [Real.mul_rpow hk.le (by positivity)]
  rw [← LFunctions.sum_tsum_mk0_eq_dedekindZeta (by simpa using hs), Finset.mul_sum, ofReal_sum]
  simp only [hclass]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ fun C ↦ by rw [hIC C]; rfl

/-- The algebra at the end of the proof: if `w L = n k π` and
`w (γ L + L') = ∑ᵢ (π k log k + k π (2γ + log π - Pᵢ))`, then the mean of the `Pᵢ` is
`γ + log (k π) - L' / L`. -/
private theorem classMean_eq_of_value_deriv {ι : Type*} [Fintype ι] [Nonempty ι] {k r : ℝ}
    (hk : 0 < k) {w L L' : ℂ} (hw : w ≠ 0) {P : ι → ℝ}
    (h1 : w * L = ((Fintype.card ι * (k * π) : ℝ) : ℂ))
    (h2 : w * (Real.eulerMascheroniConstant * L + L') = ((∑ i, (π * (k * Real.log k) +
      k * (π * (2 * Real.eulerMascheroniConstant + Real.log π - P i))) : ℝ) : ℂ))
    (hkπ : k * π = r) :
    (((∑ i, P i) / Fintype.card ι : ℝ) : ℂ) =
      ((Real.eulerMascheroniConstant + Real.log r : ℝ) : ℂ) - L' / L := by
  have hπ := Real.pi_pos
  have hsum : ∑ i, (π * (k * Real.log k) + k * (π * (2 * Real.eulerMascheroniConstant +
      Real.log π - P i))) = Fintype.card ι * (π * (k * Real.log k) +
        k * (π * (2 * Real.eulerMascheroniConstant + Real.log π))) - k * π * ∑ i, P i := by
    rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum] at h2
  have hL : L = ((Fintype.card ι * (k * π) : ℝ) : ℂ) / w := by
    rw [← h1, mul_div_cancel_left₀ _ hw]
  have hL' : L' = ((Fintype.card ι * (π * (k * Real.log k) +
      k * (π * (2 * Real.eulerMascheroniConstant + Real.log π))) - k * π * (∑ i, P i) : ℝ) : ℂ) /
        w - Real.eulerMascheroniConstant * L := by
    rw [← h2]
    field_simp
    ring
  have hnC : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hkC : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne'
  have hπC : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ.ne'
  rw [hL', hL, ← hkπ, Real.log_mul hk.ne' hπ.ne']
  push_cast
  field_simp
  ring

/-- **The Chowla–Selberg formula in class-mean form.** Let `K` be an imaginary quadratic field of
discriminant `-D`, `σ` a complex embedding of `K`, and `χ` the Dirichlet character modulo `D` with
`ζ_K(s) = ζ(s) L(s, χ)` for `Re s > 1`. Let `τ_C` be points of the upper half-plane such that the
image under `σ` of some fractional ideal of the class `C` is homothetic to `ℤ + ℤ τ_C`. Then the
mean over the ideal classes of the logarithmic periods `log (4 π Im τ_C |η(τ_C)|⁴)` is
`γ + log (2π / √D) - L'(1, χ) / L(1, χ)`, `γ` Euler's constant.

There is no restriction `D > 4`: the number of roots of unity of `K` cancels. -/
theorem chowlaSelberg_classMean (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (D : ℕ) [NeZero D]
    (hD : discr K = -(D : ℤ)) (χ : DirichletCharacter ℂ D)
    (hχ : ∀ s : ℂ, 1 < s.re → dedekindZeta K s = riemannZeta s * χ.LFunction s)
    (τ : ClassGroup (𝓞 K) → ℍ)
    (hτ : ∀ C, ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = C ∧
      ∃ c : ℂ, c ≠ 0 ∧ σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
        (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ C : ℂ)} : Set ℂ)) :
    (((∑ C, (τ C).logPeriod) / classNumber K : ℝ) : ℂ) =
      ((Real.eulerMascheroniConstant + Real.log (2 * π / √D) : ℝ) : ℂ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  have : IsTotallyComplex K :=
    IsTotallyComplex.of_discr_lt_zero (by have := NeZero.ne D; omega) hK
  choose I hIC c hc hI using hτ
  set k : ℝ := 2 / √|(discr K : ℝ)| with hk_def
  have hk : 0 < k := div_pos two_pos (sqrt_abs_cast_discr_pos K)
  set w : ℂ := (Units.torsionOrder K : ℂ)
  have hw : w ≠ 0 := Nat.cast_ne_zero.mpr (Units.torsionOrder_ne_zero K)
  -- Both `W(s) = w (s - 1) ζ(s) L(s, χ)` and `∑_C kˢ (s - 1) E(τ_C, s)` are `w (s - 1) ζ_K(s)`.
  let W : ℂ → ℂ := fun z ↦ w * (riemannZeta₁ z * χ.LFunction z)
  have hW : HasDerivAt W (w * (deriv riemannZeta₁ 1 * χ.LFunction 1 +
      riemannZeta₁ 1 * deriv χ.LFunction 1)) 1 :=
    (((differentiable_riemannZeta₁ 1).hasDerivAt.mul (DirichletCharacter.differentiableAt_LFunction
      χ 1 (.inr (ne_one_of_dedekindZeta_eq hK hD hχ))).hasDerivAt).const_mul w)
  have hWE : ∀ᶠ s : ℝ in 𝓝[>] 1,
      W s = ((∑ C, k ^ s * ((s - 1) * (τ C).epsteinZeta s) : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have hs1 : (s : ℂ) - 1 ≠ 0 := by exact_mod_cast sub_ne_zero.2 hs.ne'
    have hz : riemannZeta₁ s = (s - 1) * riemannZeta s := by
      rw [riemannZeta_eq_inv_sub_mul (by exact_mod_cast hs.ne'), mul_inv_cancel_left₀ hs1]
    have h := sum_rpow_mul_epsteinZeta_eq hK σ hIC hc hI hs
    rw [hχ s (by simpa using hs)] at h
    simp only [W, hz]
    rw [show ∑ C, k ^ s * ((s - 1) * (τ C).epsteinZeta s) =
      (s - 1) * ∑ C, k ^ s * (τ C).epsteinZeta s by rw [Finset.mul_sum]; ring_nf]
    push_cast at h ⊢
    rw [h]
    ring
  -- Compare values and derivatives at `1`, and solve for `L'(1, χ) / L(1, χ)`.
  obtain ⟨h1, h2⟩ := value_and_deriv_eq_of_tendsto hk (fun C ↦ tendsto_epsteinZeta_sub (τ C)) hW
    hWE
  simp only [W, riemannZeta₁_one, deriv_riemannZeta₁_one, one_mul] at h1 h2
  have hkπ : k * π = 2 * π / √D := by
    rw [hk_def, hD, Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast]
    ring
  exact classMean_eq_of_value_deriv hk hw h1 h2 hkπ

/-- **The Chowla–Selberg formula in class-mean form, for the character of the field.** Let `K` be
a quadratic field, `σ` a complex embedding of `K`, and `χ_K` the quadratic character `(d_K / ·)`
of the discriminant `d_K` of `K`, at level `|d_K|`. Let `τ_C` be points of the upper half-plane
such that the image under `σ` of some fractional ideal of the class `C` is homothetic to
`ℤ + ℤ τ_C` (this forces `K` to be imaginary). Then the mean over the ideal classes of the
logarithmic periods `log (4 π Im τ_C |η(τ_C)|⁴)` is
`γ + log (2π / √|d_K|) - L'(1, χ_K) / L(1, χ_K)`. This is `chowlaSelberg_classMean` with the
factorisation `ζ_K = ζ · L(·, χ_K)` supplied by `dedekindZeta_eq_riemannZeta_mul_LFunction`. -/
theorem chowlaSelberg_classMean_fundamentalDiscriminantChar (hK : finrank ℚ K = 2)
    (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ)
    (hτ : ∀ C, ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = C ∧
      ∃ c : ℂ, c ≠ 0 ∧ σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
        (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ C : ℂ)} : Set ℂ)) :
    (((∑ C, (τ C).logPeriod) / classNumber K : ℝ) : ℂ) =
      ((Real.eulerMascheroniConstant + Real.log (2 * π / √(discr K).natAbs) : ℝ) : ℂ) -
        deriv (DirichletCharacter.LFunction ((Multiquadratic.fundamentalDiscriminantChar
          (discr K) (Multiquadratic.isFundamentalDiscr_discr hK)).ringHomComp
            (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((Multiquadratic.fundamentalDiscriminantChar (discr K)
          (Multiquadratic.isFundamentalDiscr_discr hK)).ringHomComp (Int.castRingHom ℂ)) 1 := by
  obtain ⟨I, -, c, hc, hI⟩ := hτ 1
  have := isTotallyComplex_of_image_eq σ hK hc hI
  have hdK := IsTotallyComplex.discr_lt_zero hK
  exact chowlaSelberg_classMean hK σ (discr K).natAbs (by omega) _
    (fun _ hs ↦ dedekindZeta_eq_riemannZeta_mul_LFunction hK hs) τ hτ

end TauCeti.NumberField
