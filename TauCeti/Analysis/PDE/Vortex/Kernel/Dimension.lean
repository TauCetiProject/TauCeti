/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Analytic.ExtractZeros
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.PDE.Vortex.Kernel.Existence

/-!
# The kernel of the gauge-fixed operator at a plane vortex has dimension `2m`

Let `x` be a field whose holomorphicity rows `∂bar_a α = 0` vanish, with `|α| → 1` at infinity,
and let the zeros of its section `α`, counted with multiplicity, form the effective divisor `D`.
This file determines the kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) through the principal-part map of
`TauCeti.Analysis.PDE.Vortex.PrincipalPart`, following Samols and Taubes:

1. **Upper bound at `C²` regularity.** Every real vector space of `C²` square-integrable solutions
   `y` of `L_x y = 0` has dimension at most `2 |D|`
   (`TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`), and at most `2m`
   under the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`
   (`TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`). The last two rows of
   `L_x y = 0` are the linearized holomorphicity rows, giving `δα = α G + e^ν H` with `H` entire,
   and `TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`
   makes `TauCeti.Vortex.principalPartMap` injective.
2. **Surjectivity and equivalence at smooth fields.** When `x` is smooth, the single-pole kernel
   elements of `TauCeti.Analysis.PDE.Vortex.Kernel.Existence` have triangular principal parts with
   respect to the divided differences of the entire factor `f = e⁻ᵛ α`: a pole of order `j + 1` at
   a zero `z` of multiplicity `n` has `H` proportional to `(swap dslope z)^[j + 1] f`, which
   vanishes to order `n - 1 - j` at `z` and to order `D.count z'` at every `z' ≠ z`. Back
   substitution in `j` and summation over `z ∈ D` realize every principal-part vector by a smooth
   `L²` kernel element
   (`TauCeti.Vortex.exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq`,
   `TauCeti.Vortex.principalPartMap_surjective`). Thus the principal-part map is a real-linear
   equivalence `gaugeFixedKernel x ≃ₗ[ℝ] (D → ℂ)` (`TauCeti.Vortex.gaugeFixedKernelEquiv`), every
   element of `gaugeFixedKernel x` is smooth (`TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`),
   and `gaugeFixedKernel x` has real dimension `2 |D|` (`2m` in framing degree `m`:
   `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`,
   `TauCeti.Vortex.finrank_gaugeFixedKernel`). Only the holomorphicity rows of the vortex equation
   are used.

The comparison of `gaugeFixedKernel x` with the Sobolev and weak `L²` kernels is in
`TauCeti.Analysis.PDE.Vortex.Kernel.Sobolev`.

## Main results

* `TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero` and
  `TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`: a space of `C²`
  square-integrable kernel elements is finite dimensional, of dimension at most `2 |D|`.
* `TauCeti.Vortex.finiteDimensional_of_tendsto_sectionValue_mul_inv_pow` and
  `TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`: the same for a field
  framed in degree `m`, with bound `2m`.
* `TauCeti.Vortex.exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq` and
  `TauCeti.Vortex.principalPartMap_surjective`: every principal-part vector in `D → ℂ` is realized
  by a smooth `L²` solution of `L_x y = 0`.
* `TauCeti.Vortex.gaugeFixedKernelEquiv`: the real-linear equivalence
  `gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)` given by the principal-part map.
* `TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`: at a smooth field with `∂bar_a α = 0` and
  `|α|² → 1`, every element of `gaugeFixedKernel x` is smooth.
* `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel`: `gaugeFixedKernel x` has real dimension `2 |D|`, hence
  `2m` under the degree-`m` end framing.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory
open scoped ContDiff Topology

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {D : Multiset ℂ} {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}

/-! ### The upper bound at `C²` regularity -/

omit [μ.IsAddHaarMeasure] in
/-- A `C²` kernel element of `L_x` has `C²` components and satisfies the holomorphicity rows of
the linearized equation, which are the last two rows of `L_x y = 0`. -/
private theorem forall_mem_linearizedEquation_eq_zero
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∀ y ∈ V, ContDiff ℝ 2 (fun w ↦ y w 0) ∧ ContDiff ℝ 2 (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
  intro y hy
  obtain ⟨hy, -, hker⟩ := hV y hy
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hy
  refine ⟨hi 0, hi 1, (hi 2).differentiable (by norm_num), (hi 3).differentiable (by norm_num),
    fun w ↦ ⟨?_, ?_⟩⟩
  · rw [← gaugeFixedOperator_apply_two, hker w, PiLp.zero_apply]
  · rw [← gaugeFixedOperator_apply_three, hker w, PiLp.zero_apply]

/-- **The principal-part map on the kernel.** For a space `V` of `C²` square-integrable kernel
elements, the principal-part map `TauCeti.Vortex.principalPartMap` gives an injective real-linear
map from `V` to `ℂ^|D|`. -/
private theorem exists_injective_linearMap (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    ∃ Φ : V →ₗ[ℝ] Multiset.ToType D → ℂ, Function.Injective Φ := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  have hp := (hi 2).differentiable (by norm_num)
  have hq := (hi 3).differentiable (by norm_num)
  have hlin := forall_mem_linearizedEquation_eq_zero hV
  -- An integrating factor `ν` with `∂bar ν = (b₂ - i b₁) / 2`.
  obtain ⟨ν, hν, hνeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num) (contDiff_connectionCoeff
      (hi 0) (hi 1))
  have hdec (y) (hy : y ∈ V) : ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hlin y hy
    obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
      hp hq hhol (hν.differentiable (by norm_num)) hνeq h₁ h₂ h₃ h₄ h₅
    exact ⟨G, hG.continuous, H, hH, hGH⟩
  exact ⟨principalPartMap hD hν.continuous hdec,
    principalPartMap_injective (k := 2) (by norm_num) (hi 0) (hi 1) hp hq hhol hD hν hνeq hlin hdec
      fun y hy η hη hyη ↦ eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol hlim (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη
        hyη⟩

/-- **Kernel elements of the gauge-fixed operator form a finite-dimensional space.** Let `x` be a
`C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has zero
divisor `D`. Then every real vector space of `C²` square-integrable solutions of `L_x y = 0` is
finite dimensional. -/
theorem finiteDimensional_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V :=
  let ⟨Φ, hΦ⟩ := exists_injective_linearMap hx hhol hlim hD hV
  FiniteDimensional.of_injective Φ hΦ

/-- **The kernel of the gauge-fixed operator at a vortex has dimension at most `2 |D|`.** Let `x`
be a `C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has
zero divisor `D`. Then every real vector space of `C²` square-integrable solutions of `L_x y = 0`
has dimension at most twice the degree of `D`. -/
theorem finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Module.finrank ℝ V ≤ 2 * Multiset.card D := by
  obtain ⟨Φ, hΦ⟩ := exists_injective_linearMap hx hhol hlim hD hV
  refine (LinearMap.finrank_le_finrank_of_injective hΦ).trans_eq ?_
  rw [Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
    Finset.card_univ, Multiset.card_coe, mul_comm]

/-- **Kernel elements at a framed vortex form a finite-dimensional space.** At a `C²` field with
vanishing holomorphicity rows and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`, every real
vector space of `C²` square-integrable solutions of `L_x y = 0` is finite dimensional. -/
theorem finiteDimensional_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    FiniteDimensional ℝ V := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  exact finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hi 0)
    (hi 1) ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
    (forall_mem_linearizedEquation_eq_zero hV) fun y hy η hη hyη ↦
      eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
        (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη hyη

/-- **The kernel of the gauge-fixed operator at a framed vortex has dimension at most `2m`.** At a
`C²` field with vanishing holomorphicity rows and the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`, every real vector space of `C²` square-integrable solutions of
`L_x y = 0` has dimension at most `2m`, the real dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow {m : ℕ} (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hV : ∀ y ∈ V, ContDiff ℝ 2 y ∧ MemLp y 2 μ ∧ ∀ w, gaugeFixedOperator x y w = 0) :
    Module.finrank ℝ V ≤ 2 * m := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  exact finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hi 0)
    (hi 1) ((hi 2).differentiable (by norm_num)) ((hi 3).differentiable (by norm_num)) hhol hframe
    (forall_mem_linearizedEquation_eq_zero hV) fun y hy η hη hyη ↦
      eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by norm_num)) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
        (hV y hy).1.continuous (hV y hy).2.1 (hV y hy).2.2 hη hyη

/-! ### Surjectivity of the principal-part map and exact dimension `2m` -/

/-- The subspace of smooth square-integrable kernel elements of `L_x`. -/
private def smoothGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧ ∀ z, gaugeFixedOperator x y z = 0}
  add_mem' := by
    rintro y v ⟨hy, hy₂, hyk⟩ ⟨hv, hv₂, hvk⟩
    refine ⟨hy.add hv, hy₂.add hv₂, fun z ↦ ?_⟩
    rw [gaugeFixedOperator_add x (hy.differentiable (by simp) z) (hv.differentiable (by simp) z),
      hyk, hvk, add_zero]
  zero_mem' := ⟨contDiff_zero_fun, MemLp.zero, fun z ↦ by simp⟩
  smul_mem' := by
    rintro t y ⟨hy, hy₂, hyk⟩
    exact ⟨hy.const_smul t, hy₂.const_smul t, fun z ↦ by
      rw [gaugeFixedOperator_smul, hyk, smul_zero]⟩

private theorem smoothGaugeFixedKernel_le_gaugeFixedKernel :
    smoothGaugeFixedKernel x ≤ gaugeFixedKernel x :=
  fun _ ⟨hy, hy₂, hyk⟩ ↦ mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), hy₂, hyk⟩

/-- Every element of `gaugeFixedKernel x` admits a decomposition `δα = α G + e^ν H` with `G`
continuous and `H` entire. -/
private theorem gaugeFixedKernel_decomposition (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {ν : ℂ → ℂ} (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
  have hlin := forall_mem_linearizedEquation_eq_zero (V := gaugeFixedKernel x)
    fun _ hy ↦ mem_gaugeFixedKernel.1 hy
  intro y hy
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hlin y hy
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
    ((contDiff_euclidean.1 hx 2).differentiable (by norm_num))
    ((contDiff_euclidean.1 hx 3).differentiable (by norm_num)) hhol hν hνeq h₁ h₂ h₃ h₄ h₅
  exact ⟨G, hG.continuous, H, hH, hGH⟩

/-- Dividing the entire factor `f = e⁻ᵛ α` by `(w - z)^(j + 1)` at a zero `z` of multiplicity
`D.count z > j` produces an entire function `F` vanishing to order `D.count z - 1 - j` at `z` and
to order `D.count z'` at every `z' ≠ z`. -/
private theorem exists_differentiable_eq_pow_mul_exp_neg_mul_sectionValue
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) {z : ℂ} {j : ℕ}
    (hj : j < D.count z) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ w, exp (-ν w) * sectionValue x w = (w - z) ^ (j + 1) * F w) ∧
      analyticOrderAt F z = (D.count z - 1 - j : ℕ) ∧
      ∀ z' ≠ z, analyticOrderAt F z' = D.count z' := by
  set f : ℂ → ℂ := fun w ↦ exp (-ν w) * sectionValue x w
  have hf : Differentiable ℂ f := differentiable_exp_neg_mul_sectionValue hp hq hhol hν hνeq
  have hfD : IsZeroMultiplicity f fun z' ↦ D.count z' :=
    hD.mul_left_of_continuous hν.continuous.neg.cexp fun _ ↦ exp_ne_zero _
  have hford (z' : ℂ) : analyticOrderAt f z' = D.count z' :=
    hfD.analyticOrderAt_eq (hf.analyticAt z')
  set F : ℂ → ℂ := (Function.swap dslope z)^[j + 1] f
  have hF : Differentiable ℂ F := fun w ↦
    ((hf.analyticAt w).iterate_dslope (j + 1)).differentiableAt
  have hfF (w : ℂ) : f w = (w - z) ^ (j + 1) * F w := by
    rw [← smul_eq_mul]
    exact (pow_sub_smul_iterate_dslope_of_zero (j + 1)
      (fun k hk ↦ iterate_dslope_apply_eq_zero_of_lt
        (by rw [hford z]; exact_mod_cast Nat.succ_le_of_lt hj) hk) w).symm
  have hmon (w : ℂ) : AnalyticAt ℂ (fun u ↦ (u - z) ^ (j + 1)) w :=
    (analyticAt_id.sub analyticAt_const).pow (j + 1)
  refine ⟨F, hF, hfF, ?_, fun z' hz' ↦ ?_⟩
  · have hpowz : analyticOrderAt (fun u ↦ (u - z) ^ (j + 1)) z = (j + 1 : ℕ) := by
      simpa only [Pi.pow_def] using analyticOrderAt_centeredMonomial (z₀ := z) (n := j + 1)
    have hmul : ((D.count z : ℕ) : ℕ∞) = (j + 1 : ℕ) + analyticOrderAt F z := by
      rw [← hford z, funext hfF,
        analyticOrderAt_fun_mul (hmon z) (hF.analyticAt z), hpowz]
    have hsplit : ((D.count z : ℕ) : ℕ∞) = (j + 1 : ℕ) + (D.count z - 1 - j : ℕ) := by
      exact_mod_cast (by omega : D.count z = (j + 1) + (D.count z - 1 - j))
    have hEq := hmul.symm.trans hsplit
    exact le_antisymm
      ((ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).1 hEq.le)
      ((ENat.add_le_add_iff_left (ENat.natCast_ne_top _)).1 hEq.ge)
  · have hpow0 : analyticOrderAt (fun w ↦ (w - z) ^ (j + 1)) z' = 0 :=
      analyticOrderAt_eq_zero.2 (.inr (pow_ne_zero _ (sub_ne_zero.2 hz')))
    rw [← hford z', funext hfF,
      analyticOrderAt_fun_mul (hmon z') (hF.analyticAt z'), hpow0, zero_add]

private theorem exists_contDiffAt_sectionValue_eq_pow_count_mul (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (z : ℂ) :
    ∃ v : ℂ → ℂ, ContDiffAt ℝ ∞ v z ∧ v z ≠ 0 ∧
      sectionValue x =ᶠ[𝓝 z] fun w ↦ (w - z) ^ D.count z * v w := by
  choose N v hv hv₀ hvf using fun z' ↦
    exists_contDiffAt_sectionValue_eq_pow_mul (k := ⊤) (by simp) (contDiff_euclidean.1 hx 0)
      (contDiff_euclidean.1 hx 1) ((contDiff_euclidean.1 hx 2).differentiable (by simp))
      ((contDiff_euclidean.1 hx 3).differentiable (by simp)) hhol hD.exists_ne_zero z'
  have hNz : N z = D.count z := congrFun ((isZeroMultiplicity_iff.2 fun z' ↦
    ⟨v z', (hv z').continuousAt, hv₀ z', hvf z'⟩).unique hD) z
  exact ⟨v z, hv z, hv₀ z, hNz ▸ hvf z⟩

/-- A single-pole kernel element of order `D.count z - m` at `z` realizes any prescribed `m`-th
derivative `d` at `z`, while all lower derivatives at `z` and all principal parts at `z' ≠ z`
vanish. -/
private theorem exists_mem_smoothGaugeFixedKernel_triangular (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) {z : ℂ} {m : ℕ}
    (hm : m < D.count z) (d : ℂ) :
    ∃ y ∈ smoothGaugeFixedKernel x,
      principalPart x ν y z m = d ∧
      (∀ k < m, principalPart x ν y z k = 0) ∧
      ∀ z' ≠ z, ∀ k < D.count z', principalPart x ν y z' k = 0 := by
  set j := D.count z - 1 - m
  have hj : j < D.count z := by omega
  have hmj : D.count z - 1 - j = m := by omega
  obtain ⟨F, hF, hfF, hFz, hFne⟩ := exists_differentiable_eq_pow_mul_exp_neg_mul_sectionValue
    ((contDiff_euclidean.1 hx 2).differentiable (by simp))
    ((contDiff_euclidean.1 hx 3).differentiable (by simp)) hhol hD hν hνeq hj
  rw [hmj] at hFz
  obtain ⟨hFz_lt, hFz_ne⟩ :=
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hF.analyticAt z)).1 hFz
  obtain ⟨v, hv, -, hvf⟩ := exists_contDiffAt_sectionValue_eq_pow_count_mul hx hhol hD z
  set c : ℂ := d / iteratedDeriv m F z
  obtain ⟨y, hy, hy₂, hyk, ξ, hξ, hyξ⟩ :=
    exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add hx hhol hlim hv hvf hj c
  -- Globally `δα = α ξ + e^ν (c F)`, since both sides are continuous and agree away from `z`.
  have hyH (w : ℂ) : sectionValue y w = sectionValue x w * ξ w + exp (ν w) * (c * F w) := by
    have hcont₁ : Continuous (sectionValue y) :=
      (contDiff_sectionValue (contDiff_euclidean.1 hy 2) (contDiff_euclidean.1 hy 3)).continuous
    have hcont₂ : Continuous fun w ↦ sectionValue x w * ξ w + exp (ν w) * (c * F w) :=
      ((contDiff_sectionValue (contDiff_euclidean.1 hx 2)
        (contDiff_euclidean.1 hx 3)).continuous.mul hξ.continuous).add
        (hν.continuous.cexp.mul (continuous_const.mul hF.continuous))
    refine congrFun (Continuous.ext_on (dense_compl_singleton z) hcont₁ hcont₂ fun w hw ↦ ?_) w
    have hαw : sectionValue x w = exp (ν w) * ((w - z) ^ (j + 1) * F w) := by
      rw [← hfF w, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
    have hne : (w - z) ^ (j + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hw)
    rw [hyξ w hw, mul_add, hαw]
    field_simp
    ring
  have hH : Differentiable ℂ fun w ↦ c * F w := (differentiable_const c).mul hF
  refine ⟨y, ⟨hy, hy₂, hyk⟩, ?_, fun k hk ↦ ?_, fun z' hz' k hk ↦ ?_⟩
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyH hm,
      iteratedDeriv_const_mul_field, div_mul_cancel₀ d hFz_ne]
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyH (hk.trans hm),
      iteratedDeriv_const_mul_field, hFz_lt k hk, mul_zero]
  · have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hF.analyticAt z')).1
      (hFne z' hz').ge k hk
    rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyH hk,
      iteratedDeriv_const_mul_field, hzero, mul_zero]

/-- Back substitution over the orders `k < r` at a single zero `z` realizes any jet up to order `r`
at `z` while keeping all principal parts at `z' ≠ z` equal to zero. -/
private theorem exists_mem_smoothGaugeFixedKernel_at_point (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) (z : ℂ)
    (g : ℕ → ℂ) {r : ℕ} (hr : r ≤ D.count z) :
    ∃ y ∈ smoothGaugeFixedKernel x,
      (∀ k < r, principalPart x ν y z k = g k) ∧
      ∀ z' ≠ z, ∀ k < D.count z', principalPart x ν y z' k = 0 := by
  have hdec : ∀ y ∈ smoothGaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w :=
    fun y hy ↦ gaugeFixedKernel_decomposition (hx.of_le (by simp)) hhol hν hνeq y
      (smoothGaugeFixedKernel_le_gaugeFixedKernel hy)
  induction r with
  | zero =>
    refine ⟨0, zero_mem _, fun _ hk ↦ absurd hk (Nat.not_lt_zero _), fun z' _ k hk ↦ ?_⟩
    let idx : Multiset.ToType D := ⟨z', ⟨k, hk⟩⟩
    have h0 : principalPart x ν ((0 : smoothGaugeFixedKernel x) :
        ℂ → EuclideanSpace ℝ (Fin 4)) idx.1 idx.2 = 0 := by
      rw [← principalPartMap_apply hD hν.continuous hdec 0 idx, map_zero, Pi.zero_apply]
    simpa [idx] using h0
  | succ r ih =>
    obtain ⟨y₀, hy₀, hy₀z, hy₀ne⟩ := ih (Nat.le_of_succ_le hr)
    obtain ⟨y₁, hy₁, hy₁r, hy₁lt, hy₁ne⟩ := exists_mem_smoothGaugeFixedKernel_triangular hx hhol
      hlim hD hν hνeq hr (g r - principalPart x ν y₀ z r)
    have hadd {z' : ℂ} {k : ℕ} (hk : k < D.count z') :
        principalPart x ν (y₀ + y₁) z' k =
          principalPart x ν y₀ z' k + principalPart x ν y₁ z' k := by
      let idx : Multiset.ToType D := ⟨z', ⟨k, hk⟩⟩
      have h : principalPart x ν ((⟨y₀, hy₀⟩ + ⟨y₁, hy₁⟩ : smoothGaugeFixedKernel x) :
          ℂ → EuclideanSpace ℝ (Fin 4)) idx.1 idx.2 =
          principalPart x ν y₀ idx.1 idx.2 + principalPart x ν y₁ idx.1 idx.2 := by
        rw [← principalPartMap_apply hD hν.continuous hdec (⟨y₀, hy₀⟩ + ⟨y₁, hy₁⟩) idx,
          map_add, Pi.add_apply, principalPartMap_apply, principalPartMap_apply]
      simpa [idx] using h
    refine ⟨y₀ + y₁, add_mem hy₀ hy₁, fun k hk ↦ ?_, fun z' hz' k hk ↦ ?_⟩
    · rw [hadd (lt_of_lt_of_le hk hr)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | rfl
      · rw [hy₀z k hlt, hy₁lt k hlt, add_zero]
      · rw [hy₁r, add_sub_cancel]
    · rw [hadd hk, hy₀ne z' hz' k hk, hy₁ne z' hz' k hk, add_zero]

/-- **Kernel elements with prescribed principal parts.** Let `x` be a smooth field with vanishing
holomorphicity rows and `|α|² → 1` at infinity, whose section has zero divisor `D`, and let `ν` be
a differentiable integrating factor with `∂bar ν = (b₂ - i b₁) / 2`. For every principal-part
vector `p : D → ℂ` there is a smooth square-integrable solution `y` of `L_x y = 0` whose
principal-part data equal `p`. -/
theorem exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (p : Multiset.ToType D → ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧
      (∀ w, gaugeFixedOperator x y w = 0) ∧
      ∀ i : Multiset.ToType D, principalPart x ν y i.1 i.2 = p i := by
  classical
  have hdec : ∀ y ∈ smoothGaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w :=
    fun y hy ↦ gaugeFixedKernel_decomposition (hx.of_le (by simp)) hhol hν hνeq y
      (smoothGaugeFixedKernel_le_gaugeFixedKernel hy)
  choose yz hyz hyzeq hyzne using fun z : ℂ ↦
    exists_mem_smoothGaugeFixedKernel_at_point hx hhol hlim hD hν hνeq z
      (fun k ↦ if hk : k < D.count z then p ⟨z, ⟨k, hk⟩⟩ else 0) le_rfl
  let S : smoothGaugeFixedKernel x := ∑ z ∈ D.toFinset, ⟨yz z, hyz z⟩
  refine ⟨S.1, S.2.1, S.2.2.1, S.2.2.2, ?_⟩
  rintro ⟨z₀, ⟨k₀, hk₀⟩⟩
  have hi_mem : z₀ ∈ D.toFinset :=
    Multiset.mem_toFinset.2 (Multiset.count_pos.1 (Nat.zero_lt_of_lt hk₀))
  let idx : Multiset.ToType D := ⟨z₀, ⟨k₀, hk₀⟩⟩
  have hsum : principalPart x ν S.1 idx.1 idx.2 =
      ∑ z ∈ D.toFinset, principalPart x ν (yz z) idx.1 idx.2 := by
    rw [← principalPartMap_apply hD hν.continuous hdec S idx, _root_.map_sum, Finset.sum_apply]
    simp only [principalPartMap_apply]
  have hsum' : principalPart x ν S.1 z₀ k₀ =
      ∑ z ∈ D.toFinset, principalPart x ν (yz z) z₀ k₀ := by
    simpa [idx] using hsum
  rw [hsum', Finset.sum_eq_single z₀
    (fun z _ hz ↦ hyzne z z₀ hz.symm k₀ hk₀)
    (fun hnot ↦ absurd hi_mem hnot)]
  simpa [hk₀] using hyzeq z₀ k₀ hk₀

/-- **Surjectivity of the principal-part map.** Let `x` be a smooth field with vanishing
holomorphicity rows and `|α|² → 1` at infinity, whose section has zero divisor `D`, and let `ν` be
a differentiable integrating factor. On every real vector space `V` of variations admitting
holomorphic decompositions `δα = α G + e^ν H` and containing all smooth `L²` kernel elements of
`L_x`, the principal-part map `V →ₗ[ℝ] (D → ℂ)` is surjective. -/
theorem principalPartMap_surjective (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (hker : ∀ y, ContDiff ℝ ∞ y → MemLp y 2 volume →
      (∀ w, gaugeFixedOperator x y w = 0) → y ∈ V) :
    Function.Surjective (principalPartMap hD hν.continuous hdec) := by
  intro p
  obtain ⟨y, hy, hy₂, hyk, hyp⟩ :=
    exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq hx hhol hlim hD hν hνeq p
  refine ⟨⟨y, hker y hy hy₂ hyk⟩, funext fun i ↦ ?_⟩
  simpa only [principalPartMap_apply] using hyp i

private theorem principalPartMap_bijective_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    Function.Bijective (principalPartMap hD hν.continuous hdec) := by
  have hx₂ : ContDiff ℝ 2 x := hx.of_le (by simp)
  exact ⟨principalPartMap_injective (k := 2) (by norm_num)
      (contDiff_euclidean.1 hx₂ 0) (contDiff_euclidean.1 hx₂ 1)
      ((contDiff_euclidean.1 hx₂ 2).differentiable (by norm_num))
      ((contDiff_euclidean.1 hx₂ 3).differentiable (by norm_num)) hhol hD hν hνeq
      (forall_mem_linearizedEquation_eq_zero (V := gaugeFixedKernel x)
        fun _ hy ↦ mem_gaugeFixedKernel.1 hy) hdec
      (fun y hy η hη hyη ↦ by
        obtain ⟨hyc, hy₂, hyk⟩ := mem_gaugeFixedKernel.1 hy
        exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
          (hx.of_le (by simp)) hhol hlim hyc.continuous hy₂ hyk hη hyη),
    principalPartMap_surjective hx hhol hlim hD (hν.differentiable (by norm_num)) hνeq hdec
      fun _ hy hy₂ hyk ↦ mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), hy₂, hyk⟩⟩

/-- **The principal-part equivalence on `gaugeFixedKernel x`.** At a smooth field `x` with
`∂bar_a α = 0`, `|α|² → 1` at infinity, zero divisor `D`, and `C²` integrating factor `ν`, the
principal-part map is a real-linear equivalence from `gaugeFixedKernel x` onto
`Multiset.ToType D → ℂ`. -/
def gaugeFixedKernelEquiv (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ) :=
  LinearEquiv.ofBijective
    (principalPartMap hD hν.continuous
      (gaugeFixedKernel_decomposition (hx.of_le (by simp)) hhol
        (hν.differentiable (by norm_num)) hνeq))
    (principalPartMap_bijective_gaugeFixedKernel hx hhol hlim hD hν hνeq _)

@[simp]
theorem gaugeFixedKernelEquiv_apply (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : gaugeFixedKernel x) (i : Multiset.ToType D) :
    gaugeFixedKernelEquiv hx hhol hlim hD hν hνeq y i = principalPart x ν y i.1 i.2 := by
  rw [gaugeFixedKernelEquiv, LinearEquiv.ofBijective_apply, principalPartMap_apply]

/-- Every `C²` field with vanishing holomorphicity rows and `|α|² → 1` at infinity has a finite
zero divisor `D`. -/
private theorem exists_isZeroMultiplicity_sectionValue_of_tendsto_normSq (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Multiset ℂ, IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z := by
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hlim.eventually (lt_mem_nhds zero_lt_one)] with w hw h0
    rw [sectionValue_eq_zero_iff] at h0
    simp [h0] at hw
  choose n v hvc hv₀ hvf using
    exists_contDiffAt_sectionValue_eq_pow_mul (k := 2) (by norm_num) (contDiff_euclidean.1 hx 0)
      (contDiff_euclidean.1 hx 1) ((contDiff_euclidean.1 hx 2).differentiable (by norm_num))
      ((contDiff_euclidean.1 hx 3).differentiable (by norm_num)) hhol htail.exists
  have hmult : IsZeroMultiplicity (sectionValue x) n :=
    isZeroMultiplicity_iff.2 fun z ↦ ⟨v z, (hvc z).continuousAt, hv₀ z, hvf z⟩
  obtain ⟨D, rfl⟩ := hmult.exists_eq_count htail
  exact ⟨D, hmult⟩

/-- **The kernel `gaugeFixedKernel x` is finite dimensional.** At any `C²` field `x` with vanishing
holomorphicity rows and `|α|² → 1` at infinity, `gaugeFixedKernel x` is finite dimensional. -/
theorem finiteDimensional_gaugeFixedKernel_of_tendsto_normSq (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (gaugeFixedKernel x) :=
  let ⟨_, hD⟩ := exists_isZeroMultiplicity_sectionValue_of_tendsto_normSq hx hhol hlim
  finiteDimensional_of_gaugeFixedOperator_eq_zero hx hhol hlim hD fun _ hy ↦
    mem_gaugeFixedKernel.1 hy

/-- **Smoothness of kernel elements.** At a smooth field `x` with vanishing holomorphicity rows and
`|α|² → 1` at infinity, every `C²` square-integrable solution of `L_x y = 0` is smooth: it has the
same principal parts as a smooth kernel element, and the principal-part map is injective on
`gaugeFixedKernel x`. -/
theorem contDiff_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y := by
  have hx₂ : ContDiff ℝ 2 x := hx.of_le (by simp)
  obtain ⟨D, hD⟩ := exists_isZeroMultiplicity_sectionValue_of_tendsto_normSq hx₂ hhol hlim
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := 2) (by norm_num)
    (contDiff_connectionCoeff (contDiff_euclidean.1 hx₂ 0) (contDiff_euclidean.1 hx₂ 1))
  let e := gaugeFixedKernelEquiv hx hhol hlim hD hν hνeq
  obtain ⟨y', hy', hy'₂, hy'k, hy'p⟩ := exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq
    hx hhol hlim hD (hν.differentiable (by norm_num)) hνeq (e ⟨y, hy⟩)
  have heq : y' = y := congrArg Subtype.val
    (e.injective (a₁ := ⟨y', mem_gaugeFixedKernel.2 ⟨hy'.of_le (by simp), hy'₂, hy'k⟩⟩)
      (a₂ := ⟨y, hy⟩) (funext fun i ↦ by simpa only [e, gaugeFixedKernelEquiv_apply] using hy'p i))
  exact heq ▸ hy'

/-- **The kernel of `L_x` has real dimension `2 |D|`.** At a smooth field `x` with vanishing
holomorphicity rows, `|α|² → 1` at infinity, and zero divisor `D`, the kernel `gaugeFixedKernel x`
has real dimension `2 |D|`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * Multiset.card D := by
  have hx₂ : ContDiff ℝ 2 x := hx.of_le (by simp)
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (n := 2) (by norm_num)
    (contDiff_connectionCoeff (contDiff_euclidean.1 hx₂ 0) (contDiff_euclidean.1 hx₂ 1))
  rw [(gaugeFixedKernelEquiv hx hhol hlim hD hν hνeq).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul, Finset.card_univ,
    Multiset.card_coe, mul_comm]

/-- **The kernel of `L_x` at a framed degree-`m` vortex has real dimension `2m`.** Let `x` be a
smooth field satisfying the holomorphicity rows `∂bar_a α = 0` and the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`. Then `gaugeFixedKernel x` has real dimension `2m`, the real dimension of
the divisor space `Sym^m ℂ`. -/
theorem finrank_gaugeFixedKernel {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hx₂ : ContDiff ℝ 2 x := hx.of_le (by simp)
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity_sectionValue (k := 2) (by norm_num)
    (contDiff_euclidean.1 hx₂ 0) (contDiff_euclidean.1 hx₂ 1)
    ((contDiff_euclidean.1 hx₂ 2).differentiable (by norm_num))
    ((contDiff_euclidean.1 hx₂ 3).differentiable (by norm_num)) hhol hframe
  rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD, Sym.card_coe]

end TauCeti.Vortex
