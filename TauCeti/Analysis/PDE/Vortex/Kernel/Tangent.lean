/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension
public import Mathlib.RingTheory.Polynomial.Basic
import TauCeti.Analysis.Meromorphic.PrincipalPart
import TauCeti.Analysis.PDE.Vortex.AmplitudeForm
public import TauCeti.Analysis.PDE.Vortex.Gauge.ComplexStructure
import TauCeti.Analysis.PDE.Vortex.Kernel.Existence
import TauCeti.Data.Multiset.Fintype
import TauCeti.RingTheory.Polynomial.DegreeLT
import TauCeti.RingTheory.Polynomial.PartialFractions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Polynomial

/-!
# The kernel of the vortex operator as the tangent space of the divisor space

A field `x = (b₁, b₂, p, q)` represents `a = i (b₁ ds + b₂ dt)` and `α = 2 (p + i q)`. An
effective divisor `D ∈ Sym^m ℂ` is determined by its monic polynomial
`P_D = ∏_{a ∈ D} (X - a)` (`Sym.toMonic`), so in these symmetric coordinates `Sym^m ℂ` is the
affine space of monic polynomials of degree `m`, modelled on the space `ℂ[X]_{<m}` of polynomials
of degree less than `m` (`Polynomial.degreeLT ℂ m`) by `P ↦ P - X^m` (`Sym.coeffEquiv`, through
`Polynomial.monicEquivDegreeLT`). Its tangent space at every point, collisions included, is
therefore `ℂ[X]_{<m}`. A curve of divisors `D(t)` moves `P_{D(t)}` with velocity `δP`, and
`δP / P` has, at each point of `D`, the principal part recording how the zeros there move.

Let `x` have section with zero divisor `D`. A variation `y` with section variation `δα` has
**divisor variation** `R` (`TauCeti.Vortex.IsDivisorVariation x y D R`) if

`P_D δα = α (P_D G + R)`  for a continuous `G`,

that is, off the zeros, `δα / α - R / P_D` is continuous. If `R` has degree less than `|D|`, it
is unique (`TauCeti.Vortex.IsDivisorVariation.unique`): a polynomial `Q` that is `P_D` times a
continuous function is divisible by `P_D`
(`TauCeti.multiset_prod_X_sub_C_dvd_of_forall_eval_eq_mul`).

This file proves that at a smooth field with vanishing holomorphicity rows `∂bar_a α = 0`,
`|α| → 1` at infinity and zero divisor `D ∈ Sym^m ℂ`, in particular at a smooth framed degree-`m`
vortex, every element of the `C²` square-integrable kernel of the gauge-fixed operator
`L_x = d₀* ⊕ d₁` (`TauCeti.Vortex.gaugeFixedKernel x`) has a unique divisor variation of degree
less than `m`, and that this is a real-linear isomorphism

`ker L_x ≃ ℂ[X]_{<m}`

(`TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT`). This identifies the kernel of `L_x` with the
real tangent space of `Sym^m ℂ` at `D`, in every degree and including repeated zeros. The proof
compares dimensions. Both spaces have real dimension `2m`
(`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`). The kernel elements having a
divisor variation of degree less than `m` form a real subspace, on which the divisor variation is
real-linear by uniqueness, and it maps this subspace onto `ℂ[X]_{<m}`, so the subspace is the
whole kernel. Ontoness holds because the kernel element with
`δα / α = c / (w - a)^(j+1) + ξ` (`TauCeti.Vortex.exists_mem_gaugeFixedKernel_sectionValue_eq`)
has divisor variation `c P_D / (X - a)^(j+1)`
(`TauCeti.Vortex.isDivisorVariation_of_sectionValue_eq`), and these polynomials span
`ℂ[X]_{<m}` by partial fractions
(`Polynomial.span_range_multiset_prod_X_sub_C_sub_replicate_eq_degreeLT`).

The isomorphism is the expected one on translations. The covariant translation
`y_v = (ι_v F_a, ∇_v α)` (`TauCeti.Vortex.covariantTranslation`) is the velocity of the curve of
vortices `x(· + t v)`, whose zeros move by `-t v`, corrected by an infinitesimal gauge
transformation into the gauge-fixing slice, and its divisor variation is
`v P_D' = d/dt ∏_{a ∈ D} (X - a + t v)`
(`TauCeti.Vortex.isDivisorVariation_covariantTranslation`,
`TauCeti.Vortex.coe_gaugeFixedKernelEquivDegreeLT_covariantTranslation`). Writing `α = h P_D` with
`h` smooth and nowhere zero, `∇_v α = α (∂_v h / h + i b(v)) + h v P_D'`, which is the defining
identity with `G = ∂_v h / h + i b(v)`.

The isomorphism is complex linear for the complex structure `J` of the kernel
(`TauCeti.Vortex.gaugeFixedKernelAlmostComplexStructure`): the section variation of `J y` is
`i δα`, so its divisor variation is `i R`
(`TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT_gaugeFixedKernelAlmostComplexStructure`). Followed by
the coefficients of polynomials of degree less than `m`, it gives divisor coordinates
`TauCeti.Vortex.gaugeFixedKernelEquivCoeff : ker L_x ≃ ℂ^m`, in which `J` is multiplication by `i`
(`TauCeti.Vortex.gaugeFixedKernelEquivCoeff_symm_I_smul`).

## Main definitions

* `TauCeti.Vortex.IsDivisorVariation x y D R`: `R` is a divisor variation of the variation `y`.
* `TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT`: the real-linear isomorphism from the kernel of
  `L_x` to `ℂ[X]_{<m}`.
* `TauCeti.Vortex.gaugeFixedKernelEquivCoeff`: the same isomorphism followed by the coefficients,
  onto `ℂ^m`.

## Main results

* `TauCeti.Vortex.IsDivisorVariation.unique`: uniqueness of the divisor variation of degree `< |D|`.
* `TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT_eq_iff`: the isomorphism sends a kernel element to
  its divisor variation.
* `TauCeti.Vortex.coe_gaugeFixedKernelEquivDegreeLT_covariantTranslation`: it sends the covariant
  translation `y_v` to `v P_D'`.
* `TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT_gaugeFixedKernelAlmostComplexStructure`: it is
  complex linear for the complex structure `J` of the kernel.
* `TauCeti.Vortex.gaugeFixedKernelEquivCoeff_symm_I_smul`: in divisor coordinates `J` is
  multiplication by `i`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public noncomputable section

namespace TauCeti.Vortex

open Complex Filter Module Polynomial
open scoped Topology ContDiff

/-! ### Divisor variations -/

section DivisorVariation

variable {x y y' : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ} {R R' : ℂ[X]}

/-- **The divisor variation of a field variation.** For the polynomial `P = ∏_{a ∈ D} (X - a)` of
the divisor `D` of the section `α` of `x`, a polynomial `R` is a divisor variation of the variation
`y`, with section variation `δα`, if `P δα = α (P G + R)` for a continuous function `G`: off the
zeros, `δα / α` and `R / P` differ by a continuous function. When `R` has degree less than `|D|`,
it is the tangent vector to the space of monic polynomials of degree `|D|` recording how the zeros
of `α` move. -/
def IsDivisorVariation (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ) (R : ℂ[X]) : Prop :=
  ∃ G : ℂ → ℂ, Continuous G ∧ ∀ w, (D.map fun a ↦ X - C a).prod.eval w * sectionValue y w =
    sectionValue x w * ((D.map fun a ↦ X - C a).prod.eval w * G w + R.eval w)

theorem isDivisorVariation_iff : IsDivisorVariation x y D R ↔
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ w, (D.map fun a ↦ X - C a).prod.eval w * sectionValue y w =
      sectionValue x w * ((D.map fun a ↦ X - C a).prod.eval w * G w + R.eval w) :=
  Iff.rfl

/-- The zero variation has divisor variation zero. -/
theorem isDivisorVariation_zero : IsDivisorVariation x 0 D 0 :=
  ⟨0, continuous_const, fun w ↦ by simp [sectionValue_zero]⟩

/-- Divisor variations add. -/
theorem IsDivisorVariation.add (hy : IsDivisorVariation x y D R)
    (hy' : IsDivisorVariation x y' D R') : IsDivisorVariation x (y + y') D (R + R') := by
  obtain ⟨G, hG, h⟩ := hy
  obtain ⟨G', hG', h'⟩ := hy'
  refine ⟨G + G', hG.add hG', fun w ↦ ?_⟩
  rw [sectionValue_add, mul_add, h w, h' w, Pi.add_apply, eval_add]
  ring

/-- Divisor variations scale with real multiples of the variation. -/
theorem IsDivisorVariation.smul (hy : IsDivisorVariation x y D R) (t : ℝ) :
    IsDivisorVariation x (t • y) D (t • R) := by
  obtain ⟨G, hG, h⟩ := hy
  refine ⟨fun w ↦ t * G w, continuous_const.mul hG, fun w ↦ ?_⟩
  rw [sectionValue_smul, eval_smul, Complex.real_smul, mul_left_comm, h w]
  ring

/-- **Divisor variations are complex linear.** The divisor variation of `J y`, for the complex
structure `J = TauCeti.Vortex.variationComplexStructure` of variations, is `i` times that of `y`,
since the section variation of `J y` is `i δα`. -/
theorem IsDivisorVariation.variationComplexStructure (hy : IsDivisorVariation x y D R) :
    IsDivisorVariation x (fun w ↦ Vortex.variationComplexStructure (y w)) D (I • R) := by
  obtain ⟨G, hG, h⟩ := hy
  refine ⟨fun w ↦ I * G w, continuous_const.mul hG, fun w ↦ ?_⟩
  rw [sectionValue_variationComplexStructure, eval_smul, smul_eq_mul]
  linear_combination I * h w

/-- **Uniqueness of the divisor variation.** If the section of `x` has zero divisor `D`, a
variation has at most one divisor variation of degree less than `|D|`. -/
theorem IsDivisorVariation.unique (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hR : IsDivisorVariation x y D R) (hR' : IsDivisorVariation x y D R')
    (hdeg : R.degree < Multiset.card D) (hdeg' : R'.degree < Multiset.card D) : R = R' := by
  obtain ⟨G, hG, h⟩ := hR
  obtain ⟨G', hG', h'⟩ := hR'
  set P : ℂ[X] := (D.map fun a ↦ X - C a).prod
  -- Where `α ≠ 0`, `R' - R = P (G - G')`; the zeros of `α` are finite and both sides continuous.
  have hsub : (D.toFinset : Set ℂ)ᶜ ⊆ {w | sectionValue x w ≠ 0} := fun w hw h0 ↦
    hw (by simpa using Multiset.count_pos.1 (hD.pos_iff.2 h0))
  have hdense : Dense {w | sectionValue x w ≠ 0} :=
    (D.toFinset.finite_toSet.countable.dense_compl ℝ).mono hsub
  have heq : ∀ w, (R' - R).eval w = P.eval w * (G - G') w := congrFun <|
    Continuous.ext_on hdense (Polynomial.continuous _) ((Polynomial.continuous P).mul
      (hG.sub hG')) fun w hw ↦ by
        have hw' := mul_left_cancel₀ hw ((h w).symm.trans (h' w))
        simp only [eval_sub, Pi.sub_apply]
        linear_combination hw'.symm
  have hdvd := multiset_prod_X_sub_C_dvd_of_forall_eval_eq_mul
    (fun _ _ ↦ (hG.sub hG').continuousAt) heq
  have hlt : (R' - R).degree < P.degree := by
    rw [degree_eq_natDegree (monic_multisetProd_X_sub_C D).ne_zero,
      natDegree_multiset_prod_X_sub_C_eq_card]
    exact (degree_sub_le _ _).trans_lt (max_lt hdeg' hdeg)
  exact (sub_eq_zero.1 (eq_zero_of_dvd_of_degree_lt hdvd hlt)).symm

/-- **The divisor variation of a pole.** Let `⟨a, j⟩` be a point of the multiset `D`, and let the
section `α` of `x` vanish at `a`. A variation with section variation
`δα = α (c / (w - a)^(j+1) + ξ)` off `a`, for a continuous `ξ`, has divisor variation
`c P / (X - a)^(j+1)`, where `P = ∏_{b ∈ D} (X - b)`. -/
theorem isDivisorVariation_of_sectionValue_eq (i : D.ToType) (hα : sectionValue x i.1 = 0)
    {c : ℂ} {ξ : ℂ → ℂ} (hξ : Continuous ξ)
    (hy : ∀ w, w ≠ i.1 →
      sectionValue y w = sectionValue x w * (c / (w - i.1) ^ ((i.2 : ℕ) + 1) + ξ w)) :
    IsDivisorVariation x y D
      (c • ((D - Multiset.replicate ((i.2 : ℕ) + 1) i.1).map fun b ↦ X - C b).prod) := by
  refine ⟨ξ, hξ, fun w ↦ ?_⟩
  rcases eq_or_ne w i.1 with rfl | hw
  · -- At `a`, both `P` and `α` vanish.
    have hP : (D.map fun b ↦ X - C b).prod.eval i.1 = 0 := by
      simp [Multiset.prod_eq_zero_iff, sub_eq_zero]
    rw [hP, hα, zero_mul, zero_mul]
  · rw [hy w hw, multiset_prod_X_sub_C_eq_pow_mul i.add_one_le_count]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_smul, smul_eq_mul]
    field_simp [pow_ne_zero _ (sub_ne_zero.2 hw)]
    ring

/-- **The divisor variation of a covariant translation.** Let `x` have `C¹` connection
coefficients, differentiable section, vanishing holomorphicity rows and zero divisor `D`. The
covariant translation `y_v = (ι_v F_a, ∇_v α)` has divisor variation `v P'`, the velocity at
`t = 0` of the polynomial `∏_{a ∈ D} (X - a + t v)` of the divisor translated by `-t v`. -/
theorem isDivisorVariation_covariantTranslation (hb₁ : ContDiff ℝ 1 (fun w ↦ x w 0))
    (hb₂ : ContDiff ℝ 1 (fun w ↦ x w 1)) (hp : Differentiable ℝ (fun w ↦ x w 2))
    (hq : Differentiable ℝ (fun w ↦ x w 3)) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (v : ℂ) :
    IsDivisorVariation x (covariantTranslation x v) D (v • derivative (D.map fun a ↦ X - C a).prod)
    := by
  set P : ℂ[X] := (D.map fun a ↦ X - C a).prod
  -- The section is `h P` with `h` of class `C¹` and nowhere zero.
  obtain ⟨h, hh, hh₀, hα⟩ := exists_contDiff_sectionValue_eq_mul_prod_sub le_rfl hb₁ hb₂ hp hq
    hhol hD
  simp only [← eval_multiset_prod_X_sub_C] at hα
  have hαfun : sectionValue x = fun w ↦ h w * P.eval w := funext hα
  refine ⟨fun w ↦ fderiv ℝ h w v / h w + I * ((x w 0 * v.re + x w 1 * v.im : ℝ) : ℂ),
    ((hh.continuous_fderiv one_ne_zero).clm_apply continuous_const).div hh.continuous hh₀ |>.add
      (continuous_const.mul (continuous_ofReal.comp ((hb₁.continuous.mul continuous_const).add
        (hb₂.continuous.mul continuous_const)))), fun w ↦ ?_⟩
  have hPd : HasFDerivAt (fun w ↦ P.eval w)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (P.derivative.eval w)).restrictScalars ℝ)
      w :=
    (P.hasDerivAt w).hasFDerivAt.restrictScalars ℝ
  have hfd : fderiv ℝ (sectionValue x) w v =
      fderiv ℝ h w v * P.eval w + h w * (v * P.derivative.eval w) := by
    rw [hαfun, fderiv_fun_mul (hh.differentiable one_ne_zero w) hPd.differentiableAt, hPd.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul]
    ring
  rw [sectionValue_covariantTranslation (hp w) (hq w), covariantDerivative_apply, hfd, hα w,
    eval_smul, smul_eq_mul]
  field_simp [hh₀ w]
  ring

end DivisorVariation

/-! ### The kernel of `L_x` and the tangent space of `Sym^m ℂ` -/

section Kernel

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ} {D : Sym ℂ m}

/-- A polynomial of degree less than `m` has degree less than the degree of `D ∈ Sym^m ℂ`. -/
private theorem degree_lt_card_of_mem {R : ℂ[X]} (hR : R ∈ degreeLT ℂ m) :
    R.degree < Multiset.card (D : Multiset ℂ) := by
  simpa [Sym.card_coe] using mem_degreeLT.1 hR

/-- On a space of variations each of which has a divisor variation of degree less than `m`, the
divisor variation, a real-linear map to `ℂ[X]_{<m}`. -/
private def divisorVariationMap (hD : IsZeroMultiplicity (sectionValue x) fun z ↦
      (D : Multiset ℂ).count z) (V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)))
    (hV : ∀ y ∈ V, ∃ R ∈ degreeLT ℂ m, IsDivisorVariation x y D R) : V →ₗ[ℝ] degreeLT ℂ m where
  toFun y := ⟨(hV y y.property).choose, (hV y y.property).choose_spec.1⟩
  map_add' y y' := by
    obtain ⟨h₁, h₂⟩ := (hV y y.property).choose_spec
    obtain ⟨h₁', h₂'⟩ := (hV y' y'.property).choose_spec
    obtain ⟨h₁'', h₂''⟩ := (hV _ (y + y').property).choose_spec
    exact Subtype.ext (h₂''.unique hD (h₂.add h₂') (degree_lt_card_of_mem h₁'')
      (degree_lt_card_of_mem (add_mem h₁ h₁')))
  map_smul' t y := by
    obtain ⟨h₁, h₂⟩ := (hV y y.property).choose_spec
    obtain ⟨h₁'', h₂''⟩ := (hV _ (t • y).property).choose_spec
    exact Subtype.ext (h₂''.unique hD (h₂.smul t) (degree_lt_card_of_mem h₁'')
      (degree_lt_card_of_mem (Submodule.smul_of_tower_mem _ t h₁)))

private theorem isDivisorVariation_divisorVariationMap
    {hD : IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z}
    {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    {hV : ∀ y ∈ V, ∃ R ∈ degreeLT ℂ m, IsDivisorVariation x y D R} (y : V) :
    IsDivisorVariation x y D (divisorVariationMap hD V hV y) :=
  (hV y y.property).choose_spec.2

/-- The divisor variation map is onto when every polynomial of degree less than `m` is the
divisor variation of an element of the space. -/
private theorem surjective_divisorVariationMap
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z)
    {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ∃ R ∈ degreeLT ℂ m, IsDivisorVariation x y D R)
    (h : ∀ R : degreeLT ℂ m, ∃ y ∈ V, IsDivisorVariation x y D R) :
    Function.Surjective (divisorVariationMap hD V hV) := fun R ↦ by
  obtain ⟨y, hy, hyR⟩ := h R
  exact ⟨⟨y, hy⟩, Subtype.ext ((isDivisorVariation_divisorVariationMap _).unique hD hyR
    (degree_lt_card_of_mem (Subtype.prop _)) (degree_lt_card_of_mem R.property))⟩

variable (hx : ContDiff ℝ ∞ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
  (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z)

include hx hhol hlim hD in
/-- The kernel of `L_x` and `ℂ[X]_{<m}` both have real dimension `2m`. -/
private theorem finrank_gaugeFixedKernel_eq_finrank_degreeLT :
    finrank ℝ (gaugeFixedKernel x) = finrank ℝ (degreeLT ℂ m) := by
  rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD, Sym.card_coe,
    ← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_degreeLT]

include hx hhol hlim hD in
/-- Every polynomial of degree less than `m` is the divisor variation of a kernel element of
`L_x`: the kernel elements with a prescribed pole realize the partial-fraction polynomials
`c P / (X - a)^(j+1)`, which span `ℂ[X]_{<m}`. -/
private theorem exists_mem_gaugeFixedKernel_isDivisorVariation (R : degreeLT ℂ m) :
    ∃ y ∈ gaugeFixedKernel x, IsDivisorVariation x y D R := by
  classical
  set Q : (D : Multiset ℂ).ToType → ℂ[X] := fun i ↦
    (((D : Multiset ℂ) - Multiset.replicate ((i.2 : ℕ) + 1) i.1).map fun b ↦ X - C b).prod
  have hR : (R : ℂ[X]) ∈ Submodule.span ℂ (Set.range Q) := by
    rw [span_range_multiset_prod_X_sub_C_sub_replicate_eq_degreeLT, Sym.card_coe]
    exact R.property
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hR
  -- A kernel element with divisor variation `c i • Q i` for each point `i` of `D`.
  have hy (i : (D : Multiset ℂ).ToType) : ∃ y ∈ gaugeFixedKernel x,
      IsDivisorVariation x y D (c i • Q i) := by
    obtain ⟨y, hy, -, ξ, hξ, hyξ⟩ := exists_mem_gaugeFixedKernel_sectionValue_eq hx hhol hlim hD i
      (c i)
    exact ⟨y, hy, isDivisorVariation_of_sectionValue_eq i
      (hD.pos_iff.1 (Multiset.count_pos.2 Multiset.coe_mem)) hξ hyξ⟩
  choose y hyK hyR using hy
  refine ⟨∑ i, y i, Submodule.sum_mem _ fun i _ ↦ hyK i, hc ▸ ?_⟩
  induction (Finset.univ : Finset (D : Multiset ℂ).ToType) using Finset.induction_on with
  | empty => simpa using isDivisorVariation_zero
  | insert i s hi ih => simpa [Finset.sum_insert hi] using (hyR i).add ih

include hx hhol hlim hD in
/-- Every kernel element of `L_x` has a divisor variation of degree less than `m`. The kernel
elements having one form a subspace, which maps onto `ℂ[X]_{<m}` of real dimension `2m`, the
dimension of the kernel. -/
private theorem exists_isDivisorVariation :
    ∀ y ∈ gaugeFixedKernel x, ∃ R ∈ degreeLT ℂ m, IsDivisorVariation x y D R := by
  let S : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) :=
    { carrier := {y | y ∈ gaugeFixedKernel x ∧ ∃ R ∈ degreeLT ℂ m, IsDivisorVariation x y D R}
      add_mem' := fun ⟨hy, R, hR, h⟩ ⟨hy', R', hR', h'⟩ ↦
        ⟨add_mem hy hy', R + R', add_mem hR hR', h.add h'⟩
      zero_mem' := ⟨zero_mem _, 0, zero_mem _, isDivisorVariation_zero⟩
      smul_mem' := fun t _ ⟨hy, R, hR, h⟩ ↦
        ⟨Submodule.smul_mem _ t hy, t • R, Submodule.smul_of_tower_mem _ t hR, h.smul t⟩ }
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := MeasureTheory.volume)
    (hx.of_le (by simp)) hhol hlim fun _ ↦ mem_gaugeFixedKernel.1
  have : FiniteDimensional ℝ S := Submodule.finiteDimensional_of_le fun _ hy ↦ hy.1
  have hsurj := surjective_divisorVariationMap hD (V := S) (fun _ hy ↦ hy.2) fun R ↦ by
    obtain ⟨y, hy, hyR⟩ := exists_mem_gaugeFixedKernel_isDivisorVariation hx hhol hlim hD R
    exact ⟨y, ⟨hy, R, R.property, hyR⟩, hyR⟩
  have hSK : S = gaugeFixedKernel x := by
    refine Submodule.eq_of_le_of_finrank_le (fun _ hy ↦ hy.1) ?_
    rw [finrank_gaugeFixedKernel_eq_finrank_degreeLT hx hhol hlim hD]
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  intro y hy
  rw [← hSK] at hy
  exact hy.2

/-- **The kernel of `L_x` is the tangent space of the divisor space.** Let `x` be a smooth field
with vanishing holomorphicity rows `∂bar_a α = 0`, `|α|² → 1` at infinity and zero divisor
`D ∈ Sym^m ℂ`, for instance a smooth framed degree-`m` vortex. The divisor variation is a
real-linear isomorphism from the `C²` square-integrable kernel of the gauge-fixed operator `L_x`
onto the space `ℂ[X]_{<m}` of polynomials of degree less than `m`, the tangent space of `Sym^m ℂ`
in the coordinates given by the coefficients of the monic polynomial `∏_{a ∈ D} (X - a)`. It is
characterized by `TauCeti.Vortex.gaugeFixedKernelEquivDegreeLT_eq_iff`. -/
def gaugeFixedKernelEquivDegreeLT : gaugeFixedKernel x ≃ₗ[ℝ] degreeLT ℂ m :=
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := MeasureTheory.volume)
    (hx.of_le (by simp)) hhol hlim fun _ ↦ mem_gaugeFixedKernel.1
  have : FiniteDimensional ℝ (degreeLT ℂ m) := .trans ℝ ℂ _
  have hsurj := surjective_divisorVariationMap hD (exists_isDivisorVariation hx hhol hlim hD)
    (exists_mem_gaugeFixedKernel_isDivisorVariation hx hhol hlim hD)
  LinearEquiv.ofBijective _ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_gaugeFixedKernel_eq_finrank_degreeLT hx hhol hlim hD)).2 hsurj, hsurj⟩

/-- The image of a kernel element of `L_x` under `gaugeFixedKernelEquivDegreeLT` is a divisor
variation of it. -/
theorem isDivisorVariation_gaugeFixedKernelEquivDegreeLT (y : gaugeFixedKernel x) :
    IsDivisorVariation x y D (gaugeFixedKernelEquivDegreeLT hx hhol hlim hD y) :=
  isDivisorVariation_divisorVariationMap (hD := hD)
    (hV := exists_isDivisorVariation hx hhol hlim hD) y

/-- **Characterization of `gaugeFixedKernelEquivDegreeLT`.** It sends a kernel element `y` of
`L_x` to the unique divisor variation of `y` of degree less than `m`. -/
theorem gaugeFixedKernelEquivDegreeLT_eq_iff {y : gaugeFixedKernel x} {R : degreeLT ℂ m} :
    gaugeFixedKernelEquivDegreeLT hx hhol hlim hD y = R ↔ IsDivisorVariation x y D R := by
  refine ⟨fun h ↦ h ▸ isDivisorVariation_gaugeFixedKernelEquivDegreeLT hx hhol hlim hD y,
    fun h ↦ Subtype.ext ((isDivisorVariation_gaugeFixedKernelEquivDegreeLT hx hhol hlim hD y).unique
      hD h (degree_lt_card_of_mem (Subtype.prop _)) (degree_lt_card_of_mem R.property))⟩

/-- **The divisor variation is complex linear on the kernel.** The isomorphism
`gaugeFixedKernelEquivDegreeLT` sends `J y`, for the complex structure
`TauCeti.Vortex.gaugeFixedKernelAlmostComplexStructure` of the kernel of `L_x`, to `i` times the
divisor variation of `y`. So it identifies the kernel of `L_x`, with this complex structure, with
the complex tangent space `ℂ[X]_{<m}` of `Sym^m ℂ`. -/
@[simp]
theorem gaugeFixedKernelEquivDegreeLT_gaugeFixedKernelAlmostComplexStructure
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelEquivDegreeLT hx hhol hlim hD (gaugeFixedKernelAlmostComplexStructure x y) =
      I • gaugeFixedKernelEquivDegreeLT hx hhol hlim hD y := by
  rw [gaugeFixedKernelEquivDegreeLT_eq_iff, Submodule.coe_smul_of_tower]
  convert (isDivisorVariation_gaugeFixedKernelEquivDegreeLT hx hhol hlim hD
    y).variationComplexStructure using 1
  exact funext (coe_gaugeFixedKernelAlmostComplexStructure_apply x y)

/-- **Divisor coordinates on the kernel of `L_x`.** The real-linear isomorphism from the kernel
of `L_x` onto `ℂ^m` sending a kernel element to the coefficients of its divisor variation, a
polynomial of degree less than `m` (`Polynomial.degreeLTEquiv`). -/
def gaugeFixedKernelEquivCoeff : gaugeFixedKernel x ≃ₗ[ℝ] (Fin m → ℂ) :=
  (gaugeFixedKernelEquivDegreeLT hx hhol hlim hD).trans ((degreeLTEquiv ℂ m).restrictScalars ℝ)

theorem gaugeFixedKernelEquivCoeff_apply (y : gaugeFixedKernel x) :
    gaugeFixedKernelEquivCoeff hx hhol hlim hD y =
      degreeLTEquiv ℂ m (gaugeFixedKernelEquivDegreeLT hx hhol hlim hD y) :=
  (rfl)

/-- The kernel element with divisor coordinates `v` is the kernel element whose divisor variation
is the polynomial with coefficients `v`. -/
theorem gaugeFixedKernelEquivCoeff_symm_apply (v : Fin m → ℂ) :
    (gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm v =
      (gaugeFixedKernelEquivDegreeLT hx hhol hlim hD).symm ((degreeLTEquiv ℂ m).symm v) :=
  (rfl)

/-- The divisor coordinates are complex linear for the complex structure `J` of the kernel. -/
@[simp]
theorem gaugeFixedKernelEquivCoeff_gaugeFixedKernelAlmostComplexStructure
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelEquivCoeff hx hhol hlim hD (gaugeFixedKernelAlmostComplexStructure x y) =
      I • gaugeFixedKernelEquivCoeff hx hhol hlim hD y := by
  rw [gaugeFixedKernelEquivCoeff_apply,
    gaugeFixedKernelEquivDegreeLT_gaugeFixedKernelAlmostComplexStructure, map_smul,
    gaugeFixedKernelEquivCoeff_apply]

/-- The inverse of `gaugeFixedKernelEquivDegreeLT` is complex linear: the kernel element with
divisor variation `i • R` is `J` applied to the kernel element with divisor variation `R`. -/
@[simp]
theorem gaugeFixedKernelEquivDegreeLT_symm_I_smul (R : degreeLT ℂ m) :
    (gaugeFixedKernelEquivDegreeLT hx hhol hlim hD).symm (I • R) =
      gaugeFixedKernelAlmostComplexStructure x
        ((gaugeFixedKernelEquivDegreeLT hx hhol hlim hD).symm R) := by
  rw [LinearEquiv.symm_apply_eq,
    gaugeFixedKernelEquivDegreeLT_gaugeFixedKernelAlmostComplexStructure,
    LinearEquiv.apply_symm_apply]

/-- In divisor coordinates `J` is multiplication by `i`: the kernel element with coordinates
`i • v` is `J` applied to the kernel element with coordinates `v`. -/
@[simp]
theorem gaugeFixedKernelEquivCoeff_symm_I_smul (v : Fin m → ℂ) :
    (gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm (I • v) =
      gaugeFixedKernelAlmostComplexStructure x
        ((gaugeFixedKernelEquivCoeff hx hhol hlim hD).symm v) := by
  rw [LinearEquiv.symm_apply_eq,
    gaugeFixedKernelEquivCoeff_gaugeFixedKernelAlmostComplexStructure,
    LinearEquiv.apply_symm_apply]

/-- **Covariant translations move the divisor rigidly.** At a smooth vortex with `|α|² → 1` at
infinity and zero divisor `D ∈ Sym^m ℂ`, the isomorphism `gaugeFixedKernelEquivDegreeLT` sends the
covariant translation `y_v = (ι_v F_a, ∇_v α)` to `v P'`, where `P = ∏_{a ∈ D} (X - a)`: the
velocity of the divisor translated by `-t v`. -/
theorem coe_gaugeFixedKernelEquivDegreeLT_covariantTranslation (hsol : ∀ w, equation x w = 0)
    (v : ℂ) :
    (gaugeFixedKernelEquivDegreeLT hx hhol hlim hD
      ⟨covariantTranslation x v, covariantTranslation_mem_gaugeFixedKernel (hx.of_le (by simp))
        hsol hlim v⟩ : ℂ[X]) = v • derivative ((D : Multiset ℂ).map fun a ↦ X - C a).prod := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hmem : v • derivative ((D : Multiset ℂ).map fun a ↦ X - C a).prod ∈ degreeLT ℂ m := by
    refine Submodule.smul_mem _ _ (mem_degreeLT.2 ?_)
    have hP := monic_multisetProd_X_sub_C (D : Multiset ℂ)
    refine (degree_derivative_lt hP.ne_zero).trans_le ?_
    rw [degree_eq_natDegree hP.ne_zero, natDegree_multiset_prod_X_sub_C_eq_card, Sym.card_coe]
  exact congrArg Subtype.val ((gaugeFixedKernelEquivDegreeLT_eq_iff hx hhol hlim hD
    (R := ⟨_, hmem⟩)).2 (isDivisorVariation_covariantTranslation ((hxi 0).of_le (by simp))
      ((hxi 1).of_le (by simp)) ((hxi 2).differentiable (by simp))
      ((hxi 3).differentiable (by simp)) hhol hD v))

end Kernel

end TauCeti.Vortex
