/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.LogVariation
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.PDE.Vortex.Bootstrap
import TauCeti.Analysis.PDE.Vortex.KernelExistence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The dimension of the kernel of the gauge-fixed vortex operator

Let `x` be a field whose holomorphicity rows `∂bar_a α = 0` vanish, with `|α| → 1` at infinity,
and let the zeros of its section `α`, counted with multiplicity, form the effective divisor `D`.
This file proves that the kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) is real-linearly isomorphic through its principal parts to
`D → ℂ` (`TauCeti.Vortex.principalPartEquiv`) when `x` is smooth, and hence has exact real
dimension `2 |D|` (`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`), and `2m` at a smooth
field with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`
(`TauCeti.Vortex.finrank_gaugeFixedKernel`). Only the holomorphicity rows of the vortex equation
are used.

The upper bound holds already for `C²` fields: every real vector space of `C²` square-integrable
solutions `y` of `L_x y = 0` has dimension at most `2 |D|`
(`TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`), and at most `2m` for the
degree-`m` end framing (`TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`).
The last two rows of `L_x y = 0` are the holomorphicity rows of the linearized equation, so the
section variation decomposes as `δα = α G + e^ν H` with `H` entire, and the derivatives of `H` at
the zeros of `α` record the principal parts of `δα / α` (`TauCeti.Vortex.principalPartMap`). This
real-linear map to `ℂ^|D|` is injective (`TauCeti.Vortex.principalPartMap_injective`) by the
vanishing theorem
`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`.

When `x` is smooth,
`TauCeti.Vortex.exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add` realizes every
pole `c / (w - z)^(r+1)` (`r < count z D`) by a smooth square-integrable kernel element. Writing
`α = e^ν f` with `f` entire and factoring `f` through its divisor of zeros
(`TauCeti.IsZeroMultiplicity.exists_differentiable_eq_mul_prod_pow`), these single-pole elements
form an upper-triangular spanning set for the Taylor jets `H⁽ʲ⁾(z)` (`j < count z D`) and vanish to
full multiplicity at every other zero of `α`. Hence every principal-part datum is realized by a
smooth kernel element
(`TauCeti.Vortex.exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq`), every `C²` kernel
element is smooth (`TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`), and `principalPartMap` is a
real-linear isomorphism onto `D → ℂ`.

When `x` also has bounded derivatives of all orders — in particular when `x` lies in every affine
Sobolev space `A_m^j`, as holds for any `C¹` Coulomb-slice vortex in `A_m^k` (`k ≥ 2`) by
`TauCeti.Vortex.mem_framedFieldSpace_of_equation_eq_zero` — elliptic regularity identifies the
classical kernel with the distributional `L²` kernel `TauCeti.Vortex.weakGaugeFixedKernel`
(`TauCeti.Vortex.gaugeFixedKernelEquivWeak`), giving real dimension `2m` for the weak kernel as
well (`TauCeti.Vortex.finrank_weakGaugeFixedKernel`,
`TauCeti.Vortex.finrank_weakGaugeFixedKernel_of_equation_eq_zero`).

## Main results

* `TauCeti.Vortex.finiteDimensional_of_gaugeFixedOperator_eq_zero` and
  `TauCeti.Vortex.finrank_le_two_mul_card_of_gaugeFixedOperator_eq_zero`: a space of `C²`
  square-integrable kernel elements is finite dimensional, of dimension at most `2 |D|`.
* `TauCeti.Vortex.finiteDimensional_of_tendsto_sectionValue_mul_inv_pow` and
  `TauCeti.Vortex.finrank_le_two_mul_of_tendsto_sectionValue_mul_inv_pow`: the same for a `C²`
  field framed in degree `m`, with bound `2m`.
* `TauCeti.Vortex.exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq` and
  `TauCeti.Vortex.principalPartEquiv`: at a smooth field, the principal-part map is a real-linear
  equivalence `gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)` realized by smooth variations.
* `TauCeti.Vortex.contDiff_of_mem_gaugeFixedKernel`: every `y ∈ gaugeFixedKernel x` is smooth.
* `TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_card`,
  `TauCeti.Vortex.finrank_gaugeFixedKernel` and
  `TauCeti.Vortex.finrank_gaugeFixedKernel_of_mem_framedVortexSubMulAction`: exact dimension `2 |D|`
  and `2m` for `gaugeFixedKernel x`.
* `TauCeti.Vortex.finiteDimensional_weakGaugeFixedKernel`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel` and
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_of_equation_eq_zero`: finite dimensionality and
  exact dimension `2m` for the distributional `L²` kernel `weakGaugeFixedKernel`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open Complex Filter MeasureTheory
open scoped ContDiff Topology

namespace TauCeti.Vortex

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}
  {D : Multiset ℂ} {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}

/-! ### The `C²` dimension upper bound -/

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

section ExactDimension

/-- A finite product of powers `(w - a) ^ k a` is entire. -/
private theorem differentiable_finset_prod_sub_pow (s : Finset ℂ) (k : ℂ → ℕ) :
    Differentiable ℂ fun w ↦ ∏ a ∈ s, (w - a) ^ k a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact ((differentiable_id.sub_const a).pow (k a)).mul ih

/-- If an entire function `H` factors globally as `(w - z) ^ n * u w` with `u` continuous, its
derivatives at `z` of order below `n` vanish. -/
private theorem iteratedDeriv_eq_zero_of_eq_pow_mul {H u : ℂ → ℂ} {z : ℂ} {n j : ℕ}
    (hH : Differentiable ℂ H) (hu : Continuous u)
    (heq : ∀ w, H w = (w - z) ^ n * u w) (hj : j < n) :
    iteratedDeriv j H z = 0 :=
  ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt z)).1
    ((hH.analyticAt z).natCast_le_analyticOrderAt_of_eventually_eq_pow_smul hu.continuousAt
      (Eventually.of_forall fun w ↦ by rw [heq w, smul_eq_mul]))) j hj

/-- A `C²` field with `∂bar_a α = 0` and `|α|² → 1` at infinity has a finite multiset of zeros
counted with multiplicity. -/
private theorem exists_multiset_isZeroMultiplicity_of_tendsto (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ D : Multiset ℂ, IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  have htail : ∀ᶠ w in cocompact ℂ, sectionValue x w ≠ 0 := by
    filter_upwards [hlim.eventually (lt_mem_nhds zero_lt_one)] with w hw hz
    rw [sectionValue_eq_zero_iff] at hz
    simp [hz] at hw
  choose n v hvc hv₀ hvf using exists_contDiffAt_sectionValue_eq_pow_mul (k := 2) one_le_two
    (hi 0) (hi 1) ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp))
    hhol htail.exists
  have hmult : IsZeroMultiplicity (sectionValue x) n :=
    isZeroMultiplicity_iff.2 fun z ↦ ⟨v z, (hvc z).continuousAt, hv₀ z, hvf z⟩
  obtain ⟨D, rfl⟩ := hmult.exists_eq_count htail
  exact ⟨D, hmult⟩

/-- Decomposition `δα = α G + e^ν H` for every `y ∈ gaugeFixedKernel x`. -/
private theorem exists_decomposition_of_mem_gaugeFixedKernel (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hlin := forall_mem_linearizedEquation_eq_zero (μ := volume) (V := gaugeFixedKernel x)
    fun _ hy ↦ mem_gaugeFixedKernel.1 hy
  intro y hy
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hlin y hy
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
    ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp)) hhol hν hνeq h₁ h₂ h₃ h₄ h₅
  exact ⟨G, hG.continuous, H, hH, hGH⟩

/-- The real subspace of smooth square-integrable solutions of `L_x y = 0`. -/
private def smoothGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | ContDiff ℝ ∞ y ∧ MemLp y 2 volume ∧ ∀ z, gaugeFixedOperator x y z = 0}
  add_mem' {y v} hy hv := ⟨hy.1.add hv.1, hy.2.1.add hv.2.1, fun z ↦ by
    rw [gaugeFixedOperator_add x (hy.1.differentiable (by simp) z)
      (hv.1.differentiable (by simp) z), hy.2.2, hv.2.2, add_zero]⟩
  zero_mem' := ⟨contDiff_zero_fun, MemLp.zero, fun z ↦ by simp⟩
  smul_mem' t y hy := ⟨hy.1.const_smul t, hy.2.1.const_smul t, fun z ↦ by
    rw [gaugeFixedOperator_smul, hy.2.2, smul_zero]⟩

private theorem smoothGaugeFixedKernel_le :
    smoothGaugeFixedKernel x ≤ gaugeFixedKernel x :=
  fun _ hy ↦ mem_gaugeFixedKernel.2 ⟨hy.1.of_le (by simp), hy.2.1, hy.2.2⟩

/-- Factor `α(w) = e^{ν(w)} (w - z)^{count z D} Q(w)` with `Q` entire, `Q(z) ≠ 0`, and `Q`
divisible in the ring of entire functions by `(w - z')^{count z' D}` at every other point
`z' ≠ z` of `D`. -/
private theorem exists_differentiable_sectionValue_eq_exp_mul_pow_mul (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {z : ℂ} (hz : 0 < D.count z) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ Q z ≠ 0 ∧
      (∀ w, sectionValue x w = exp (ν w) * ((w - z) ^ D.count z * Q w)) ∧
      ∀ z', z' ≠ z → 0 < D.count z' →
        ∃ U : ℂ → ℂ, Differentiable ℂ U ∧ ∀ w, Q w = (w - z') ^ D.count z' * U w := by
  classical
  have hi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hf : Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w :=
    differentiable_exp_neg_mul_sectionValue ((hi 2).differentiable (by simp))
      ((hi 3).differentiable (by simp)) hhol hν hνeq
  obtain ⟨g, hg, hg₀, hfg⟩ :=
    (hD.mul_left_of_continuous hν.continuous.neg.cexp (fun _ ↦ exp_ne_zero _))
      |>.exists_differentiable_eq_mul_prod_pow hf
  simp only [Pi.neg_apply] at hfg
  have hzD : z ∈ D.toFinset := Multiset.mem_toFinset.2 (Multiset.count_pos.1 hz)
  refine ⟨fun w ↦ g w * ∏ a ∈ D.toFinset.erase z, (w - a) ^ D.count a,
    hg.mul (differentiable_finset_prod_sub_pow _ _),
    mul_ne_zero (hg₀ z) <| Finset.prod_ne_zero_iff.2 fun a ha ↦
      pow_ne_zero _ (sub_ne_zero.2 fun hza ↦ (Finset.ne_of_mem_erase ha) hza.symm),
    fun w ↦ ?_, fun z' hz' hz'pos ↦ ?_⟩
  · have hmul := Finset.mul_prod_erase D.toFinset (fun a ↦ (w - a) ^ D.count a) hzD
    calc sectionValue x w = exp (ν w) * (exp (-ν w) * sectionValue x w) := by
          rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ = exp (ν w) * ((w - z) ^ D.count z * _) := by dsimp only; rw [hfg w, ← hmul]; ring
  · have hz'mem : z' ∈ D.toFinset.erase z :=
      Finset.mem_erase.2 ⟨hz', Multiset.mem_toFinset.2 (Multiset.count_pos.1 hz'pos)⟩
    refine ⟨fun w ↦ g w * ∏ a ∈ (D.toFinset.erase z).erase z', (w - a) ^ D.count a,
      hg.mul (differentiable_finset_prod_sub_pow _ _), fun w ↦ ?_⟩
    have hmul := Finset.mul_prod_erase (D.toFinset.erase z) (fun a ↦ (w - a) ^ D.count a) hz'mem
    linear_combination -g w * hmul

/-- **Upper-triangular realization of a single Taylor coefficient.** For `j < count z D` and
`d ∈ ℂ`, a pole of order `count z D - j` at `z` yields a smooth kernel element whose principal part
at `(z, j)` is `d`, whose lower principal parts `j' < j` at `z` vanish, and whose principal parts
at every other point `z' ≠ z` of `D` vanish. -/
private theorem exists_triangular_principalPart (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {z : ℂ} {j : ℕ} (hj : j < D.count z) (d : ℂ) :
    ∃ y ∈ smoothGaugeFixedKernel x,
      principalPart x ν y z j = d ∧
      (∀ j' < j, principalPart x ν y z j' = 0) ∧
      ∀ z', z' ≠ z → ∀ j' < D.count z', principalPart x ν y z' j' = 0 := by
  have hi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨Q, hQ, hQz, hαQ, hQdiv⟩ := exists_differentiable_sectionValue_eq_exp_mul_pow_mul hx hhol
    hD hν hνeq (Nat.zero_lt_of_lt hj)
  -- Local smooth factorization at `z` for single-pole kernel existence.
  obtain ⟨n, v, hv, hv₀, hvf⟩ := exists_contDiffAt_sectionValue_eq_pow_mul (k := ⊤) le_top
    (hi 0) (hi 1) ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp))
    hhol hD.exists_ne_zero z
  obtain ⟨v', hv', hv'₀, hvf'⟩ := isZeroMultiplicity_iff.1 hD z
  obtain rfl : n = D.count z := eq_of_eventually_sub_pow_mul_eq hv.continuousAt hv₀ hv' hv'₀
    (by filter_upwards [hvf, hvf'] with w hw hw'; rw [← hw, ← hw'])
  set r := D.count z - 1 - j
  set c : ℂ := d / ((j.factorial : ℂ) * Q z)
  obtain ⟨y, hy, hyL, hker, ξ, hξ, hyξ⟩ :=
    exists_gaugeFixedOperator_eq_zero_sectionValue_eq_mul_div_pow_add hx hhol hlim hv hvf
      (j := r) (by omega) c
  -- Globally `δα = α ξ + e^ν H` with `H w = (w - z) ^ j * (c * Q w)`.
  set H : ℂ → ℂ := fun w ↦ (w - z) ^ j * (c * Q w)
  have hH : Differentiable ℂ H :=
    ((differentiable_id.sub_const z).pow j).mul ((differentiable_const c).mul hQ)
  have hyGH : ∀ w, sectionValue y w = sectionValue x w * ξ w + exp (ν w) * H w := by
    have hαc : Continuous (sectionValue x) := hD.continuous
    have hyc : Continuous (sectionValue y) :=
      contDiff_sectionValue (contDiff_euclidean.1 hy 2) (contDiff_euclidean.1 hy 3) |>.continuous
    have hrhs : Continuous fun w ↦ sectionValue x w * ξ w + exp (ν w) * H w :=
      (hαc.mul hξ.continuous).add (hν.continuous.cexp.mul hH.continuous)
    exact fun w ↦ congrFun (Continuous.ext_on (dense_compl_singleton z) hyc hrhs fun w' hw' ↦ by
      have hpow : (w' - z) ^ D.count z = (w' - z) ^ j * (w' - z) ^ (r + 1) := by
        rw [← pow_add, show j + (r + 1) = D.count z by omega]
      have hne : (w' - z) ^ (r + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hw')
      rw [hyξ w' hw', mul_add, add_comm (sectionValue x w' * _), add_right_inj, hαQ w', hpow]
      simp only [H]
      field_simp) w
  refine ⟨y, ⟨hy, hyL, hker⟩, ?_, fun j' hj' ↦ ?_, fun z' hz' j' hj' ↦ ?_⟩
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyGH hj]
    have hcd : ContDiffAt ℂ j (fun w ↦ c * Q w) z :=
      ((differentiable_const c).mul hQ).contDiff.contDiffAt
    have hderiv := iteratedDeriv_pow_sub_smul_self (a := z) (n := j) hcd
    simp only [smul_eq_mul, nsmul_eq_mul] at hderiv
    rw [show H = fun w ↦ (w - z) ^ j * (c * Q w) from rfl, hderiv]
    have hfac : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 j.factorial_ne_zero
    simp only [c]
    field_simp
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyGH (hj'.trans hj)]
    exact iteratedDeriv_eq_zero_of_eq_pow_mul hH (u := fun w ↦ c * Q w)
      (continuous_const.mul hQ.continuous) (fun _ ↦ rfl) hj'
  · rw [principalPart_eq_iteratedDeriv hD hν.continuous hξ.continuous hH hyGH hj']
    obtain ⟨U, hU, hQU⟩ := hQdiv z' hz' (Nat.zero_lt_of_lt hj')
    have hu : Continuous fun w ↦ (w - z) ^ j * (c * U w) :=
      (((differentiable_id.sub_const z).pow j).mul ((differentiable_const c).mul hU)).continuous
    exact iteratedDeriv_eq_zero_of_eq_pow_mul hH hu (fun w ↦ by simp only [H, hQU w]; ring) hj'

/-- Forward induction on `m ≤ count z D`: realize any jet `p 0, …, p (m - 1)` at `z` while keeping
all principal parts at every `z' ≠ z` equal to zero. -/
private theorem exists_jet_at_point (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (z : ℂ) (p : ℕ → ℂ) {m : ℕ} (hm : m ≤ D.count z) :
    ∃ y : smoothGaugeFixedKernel x,
      (∀ j < m, principalPart x ν y z j = p j) ∧
      ∀ z', z' ≠ z → ∀ j' < D.count z', principalPart x ν y z' j' = 0 := by
  let hdec := exists_decomposition_of_mem_gaugeFixedKernel (hx.of_le (by simp)) hhol hν hνeq
  set Φ := principalPartMap hD hν.continuous hdec ∘ₗ
    Submodule.inclusion (smoothGaugeFixedKernel_le (x := x))
  have hΦ (y : smoothGaugeFixedKernel x) (w : ℂ) (j : ℕ) (hj : j < D.count w) :
      principalPart x ν y w j = Φ y ⟨w, ⟨j, hj⟩⟩ :=
    (principalPartMap_apply hD hν.continuous hdec
      (Submodule.inclusion (smoothGaugeFixedKernel_le (x := x)) y) ⟨w, ⟨j, hj⟩⟩).symm
  have hadd (a b : smoothGaugeFixedKernel x) (w : ℂ) (j : ℕ) (hj : j < D.count w) :
      principalPart x ν (a + b : smoothGaugeFixedKernel x) w j =
        principalPart x ν a w j + principalPart x ν b w j := by
    rw [hΦ (a + b) w j hj, hΦ a w j hj, hΦ b w j hj]
    exact congrFun (map_add Φ a b) _
  induction m with
  | zero =>
    refine ⟨0, fun _ hj ↦ absurd hj (Nat.not_lt_zero _), fun z' _ j' hj' ↦ ?_⟩
    rw [hΦ 0 z' j' hj']
    exact congrFun (map_zero Φ) _
  | succ m ih =>
    obtain ⟨y₁, hy₁z, hy₁o⟩ := ih (Nat.le_of_succ_le hm)
    obtain ⟨y₂, hy₂s, hy₂m, hy₂lt, hy₂o⟩ :=
      exists_triangular_principalPart hx hhol hlim hD hν hνeq hm (p m - principalPart x ν y₁ z m)
    refine ⟨y₁ + ⟨y₂, hy₂s⟩, fun j hj ↦ ?_, fun z' hz' j' hj' ↦ ?_⟩
    · rw [hadd _ _ z j (lt_of_lt_of_le hj hm)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
      · simp [hy₁z j hlt, hy₂lt j hlt]
      · simp [hy₂m]
    · rw [hadd _ _ z' j' hj', hy₁o z' hz' j' hj', hy₂o z' hz' j' hj', add_zero]

/-- **Every principal-part datum is realized by a smooth kernel element.** Let `x` be a smooth
field satisfying the holomorphicity rows `∂bar_a α = 0` with `|α|² → 1` at infinity and zero
divisor `D`, and let `∂bar ν = (b₂ - i b₁) / 2`. For every `p : D → ℂ` there is a smooth
square-integrable solution `y` of `L_x y = 0` whose principal-part data are `p`. -/
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
  set Φ := principalPartMap hD hν.continuous
    (exists_decomposition_of_mem_gaugeFixedKernel (hx.of_le (by simp)) hhol hν hνeq) ∘ₗ
    Submodule.inclusion (smoothGaugeFixedKernel_le (x := x))
  have hΦ (y : smoothGaugeFixedKernel x) (i : Multiset.ToType D) :
      principalPart x ν y i.1 i.2 = Φ y i := by
    rw [LinearMap.comp_apply, principalPartMap_apply]; rfl
  choose yz hyz hyzo using fun z : ℂ ↦ exists_jet_at_point hx hhol hlim hD hν hνeq z
    (fun j ↦ if hj : j < D.count z then p ⟨z, ⟨j, hj⟩⟩ else 0) le_rfl
  set Y : smoothGaugeFixedKernel x := ∑ z ∈ D.toFinset, yz z
  refine ⟨Y.1, Y.2.1, Y.2.2.1, Y.2.2.2, fun i ↦ ?_⟩
  have hiD : i.1 ∈ D.toFinset :=
    Multiset.mem_toFinset.2 (Multiset.count_pos.1 (Nat.zero_lt_of_lt i.2.2))
  rw [hΦ Y i, show Y = ∑ a ∈ D.toFinset, yz a from rfl, map_sum, Finset.sum_apply,
    Finset.sum_eq_single i.1
      (fun a _ hai ↦ by rw [← hΦ, hyzo a i.1 hai.symm i.2 i.2.2])
      (fun hi ↦ absurd hiD hi),
    ← hΦ, hyz i.1 i.2 i.2.2]
  simp only [i.2.2, ↓reduceDIte]
  rfl

/-- **The principal-part isomorphism** (Taubes, Samols). At a smooth field `x` satisfying the
holomorphicity rows `∂bar_a α = 0` with `|α|² → 1` at infinity and zero divisor `D`, the
principal-part map identifies `gaugeFixedKernel x` real-linearly with `D → ℂ`. -/
def principalPartEquiv (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ) :=
  let hx2 : ContDiff ℝ 2 x := hx.of_le (by simp)
  let hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx2 i
  let hνd : Differentiable ℝ ν := hν.differentiable (by norm_num)
  let hdec := exists_decomposition_of_mem_gaugeFixedKernel hx2 hhol hνd hνeq
  LinearEquiv.ofBijective (principalPartMap hD hν.continuous hdec)
    ⟨principalPartMap_injective (k := 2) (by norm_num) (hi 0) (hi 1)
        ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp)) hhol hD hν hνeq
        (forall_mem_linearizedEquation_eq_zero (μ := volume) fun _ hy ↦ mem_gaugeFixedKernel.1 hy)
        hdec fun y hy η hη hyη ↦
          eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
            (hx2.of_le one_le_two) hhol hlim (mem_gaugeFixedKernel.1 hy).1.continuous
            (mem_gaugeFixedKernel.1 hy).2.1 (mem_gaugeFixedKernel.1 hy).2.2 hη hyη,
      fun p ↦ by
        obtain ⟨y, hy, hyL, hker, hyp⟩ :=
          exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq hx hhol hlim hD hνd hνeq p
        exact ⟨⟨y, mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), hyL, hker⟩⟩,
          funext fun i ↦ (principalPartMap_apply _ _ _ _ i).trans (hyp i)⟩⟩

/-- Evaluating `principalPartEquiv` at the point `⟨a, j⟩` of `D` gives `principalPart x ν y a j`. -/
@[simp]
theorem principalPartEquiv_apply (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : gaugeFixedKernel x) (i : Multiset.ToType D) :
    principalPartEquiv hx hhol hlim hD hν hνeq y i = principalPart x ν y i.1 i.2 :=
  principalPartMap_apply _ _ _ y i

/-- **Every classical kernel element at a smooth vortex is smooth.** If `x` is smooth with
`∂bar_a α = 0` and `|α|² → 1` at infinity, then every `y ∈ gaugeFixedKernel x` (assumed only `C²`)
is smooth (`C^∞`). -/
theorem contDiff_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y := by
  obtain ⟨D, hD⟩ := exists_multiset_isZeroMultiplicity_of_tendsto (hx.of_le (by simp)) hhol hlim
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 (hx.of_le (by simp)) i
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num)
    (contDiff_connectionCoeff (hi 0) (hi 1))
  set e := principalPartEquiv hx hhol hlim hD hν hνeq
  obtain ⟨y₀, hy₀, hy₀L, hker, hyp⟩ := exists_contDiff_gaugeFixedOperator_eq_zero_principalPart_eq
    hx hhol hlim hD (hν.differentiable (by norm_num)) hνeq (e ⟨y, hy⟩)
  have heq : (⟨y₀, mem_gaugeFixedKernel.2 ⟨hy₀.of_le (by simp), hy₀L, hker⟩⟩ :
      gaugeFixedKernel x) = ⟨y, hy⟩ :=
    e.injective <| funext fun i ↦
      (principalPartEquiv_apply hx hhol hlim hD hν hνeq _ i).trans (hyp i)
  have hy₀y : y₀ = y := congrArg Subtype.val heq
  exact hy₀y ▸ hy₀

/-- **The kernel of `L_x` has exact real dimension `2 |D|`.** Let `x` be a smooth field with
vanishing holomorphicity rows and `|α|² → 1` at infinity, whose section has zero divisor `D`. Then
`gaugeFixedKernel x` has real dimension `2 |D|`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * Multiset.card D := by
  have hi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 (hx.of_le (by simp)) i
  obtain ⟨ν, hν, hνeq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num)
    (contDiff_connectionCoeff (hi 0) (hi 1))
  rw [(principalPartEquiv hx hhol hlim hD hν hνeq).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul, Finset.card_univ,
    Multiset.card_coe, mul_comm]

/-- **The kernel of `L_x` at a smooth degree-`m` framed field has exact real dimension `2m`.** Let
`x` be a smooth field satisfying the holomorphicity rows `∂bar_a α = 0`, whose section has the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then `gaugeFixedKernel x` has real dimension `2m`,
the real dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_gaugeFixedKernel {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  have hi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨D, hD⟩ := exists_sym_isZeroMultiplicity_sectionValue (k := ⊤) le_top (hi 0) (hi 1)
    ((hi 2).differentiable (by simp)) ((hi 3).differentiable (by simp)) hhol hframe
  rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD, Sym.card_coe]

/-- At any smooth framed degree-`m` vortex (`framedVortexSubMulAction m`), the kernel of `L_x` has
real dimension `2m`. -/
theorem finrank_gaugeFixedKernel_of_mem_framedVortexSubMulAction {m : ℕ}
    (hx : x ∈ framedVortexSubMulAction m) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m := by
  obtain ⟨hxc, hsol, hframe⟩ := mem_framedVortexSubMulAction.1 hx
  exact finrank_gaugeFixedKernel hxc (fun w ↦ by simp [hsol w]) hframe

end ExactDimension

/-! ### The distributional `L²` kernel and Sobolev framed fields -/

section WeakKernel

/-- **The distributional `L²` kernel of `L_x` is finite dimensional.** When `x` is smooth with
bounded derivatives of all orders, `∂bar_a α = 0`, and `|α|² → 1` at infinity,
`weakGaugeFixedKernel hx.continuous` is finite dimensional over `ℝ`. -/
theorem finiteDimensional_weakGaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ (i : Fin 4) (n : ℕ), ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (weakGaugeFixedKernel hx.continuous) := by
  obtain ⟨D, hD⟩ := exists_multiset_isZeroMultiplicity_of_tendsto (hx.of_le (by simp)) hhol hlim
  have : FiniteDimensional ℝ (gaugeFixedKernel x) :=
    finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) (hx.of_le (by simp)) hhol hlim hD
      fun _ hy ↦ mem_gaugeFixedKernel.1 hy
  exact (gaugeFixedKernelEquivWeak hx hbound).finiteDimensional

/-- **The distributional `L²` kernel of `L_x` has exact real dimension `2 |D|`.** -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ (i : Fin 4) (n : ℕ), ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (weakGaugeFixedKernel hx.continuous) = 2 * Multiset.card D :=
  (gaugeFixedKernelEquivWeak hx hbound).symm.finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD)

/-- **The distributional `L²` kernel of `L_x` at a framed field has exact real dimension `2m`.** -/
theorem finrank_weakGaugeFixedKernel {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ (i : Fin 4) (n : ℕ), ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (weakGaugeFixedKernel hx.continuous) = 2 * m :=
  (gaugeFixedKernelEquivWeak hx hbound).symm.finrank_eq.trans
    (finrank_gaugeFixedKernel hx hhol hframe)

/-- For a continuous field lying in every affine Sobolev space `A_m^j` and satisfying the
holomorphicity rows, `gaugeFixedKernel x` has real dimension `2m`. -/
theorem finrank_gaugeFixedKernel_of_forall_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j) (hcont : Continuous x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel
    (contDiff_infty.2 fun k ↦ contDiff_of_mem_framedFieldSpace (s := ((k + 2 : ℕ) : ℝ))
      (by push_cast; linarith) (hx (k + 2)) hcont)
    hhol (tendsto_sectionValue_mul_inv_pow (s := 2) one_lt_two (hx 2) hcont)

/-- For a continuous field lying in every affine Sobolev space `A_m^j` and satisfying the
holomorphicity rows, the distributional `L²` kernel `weakGaugeFixedKernel hcont` is finite
dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel_of_forall_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j)
    (hcont : Continuous x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    FiniteDimensional ℝ (weakGaugeFixedKernel hcont) :=
  finiteDimensional_weakGaugeFixedKernel
    (contDiff_infty.2 fun k ↦ contDiff_of_mem_framedFieldSpace (s := ((k + 2 : ℕ) : ℝ))
      (by push_cast; linarith) (hx (k + 2)) hcont)
    (fun i n ↦ exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace (k := n)
      (s := ((n + 2 : ℕ) : ℝ)) (by push_cast; linarith) (hx (n + 2)) hcont i le_rfl)
    hhol (tendsto_normSq_of_mem_framedFieldSpace (s := 2) one_lt_two (hx 2) hcont)

/-- For a continuous field lying in every affine Sobolev space `A_m^j` and satisfying the
holomorphicity rows, the distributional `L²` kernel `weakGaugeFixedKernel hcont` has real dimension
`2m`. -/
theorem finrank_weakGaugeFixedKernel_of_forall_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j) (hcont : Continuous x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (weakGaugeFixedKernel hcont) = 2 * m :=
  (gaugeFixedKernelEquivWeakOfForallMemFramedFieldSpace hx hcont).symm.finrank_eq.trans
    (finrank_gaugeFixedKernel_of_forall_mem_framedFieldSpace hx hcont hhol)

/-- **Kernel dimension at a Coulomb-slice Sobolev vortex.** Let `x ∈ A_m^k` (`k ≥ 2`) be a `C¹`
solution of the plane vortex equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` through a `C¹`
base field `x₀` lying in every `A_m^j` (such as `referenceField f m`). Then `gaugeFixedKernel x` has
real dimension `2m`. -/
theorem finrank_gaugeFixedKernel_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ z, equation x z = 0) (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_of_forall_mem_framedFieldSpace
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) hxc.continuous
    fun w ↦ by simp [heq w]

/-- **Distributional `L²` kernel dimension at a Coulomb-slice Sobolev vortex.** Under the hypotheses
of `TauCeti.Vortex.finrank_gaugeFixedKernel_of_equation_eq_zero`, the distributional `L²` kernel
`weakGaugeFixedKernel hxc.continuous` has real dimension `2m` (and is finite dimensional by
`TauCeti.Vortex.finiteDimensional_weakGaugeFixedKernel_of_equation_eq_zero`). -/
theorem finrank_weakGaugeFixedKernel_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ z, equation x z = 0) (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (weakGaugeFixedKernel hxc.continuous) = 2 * m :=
  finrank_weakGaugeFixedKernel_of_forall_mem_framedFieldSpace
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) hxc.continuous
    fun w ↦ by simp [heq w]

/-- Under the hypotheses of `TauCeti.Vortex.finrank_weakGaugeFixedKernel_of_equation_eq_zero`, the
distributional `L²` kernel `weakGaugeFixedKernel hxc.continuous` is finite dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)}
    {m k : ℕ} (hk : 1 < k) {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ z, equation x z = 0) (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    FiniteDimensional ℝ (weakGaugeFixedKernel hxc.continuous) :=
  finiteDimensional_weakGaugeFixedKernel_of_forall_mem_framedFieldSpace
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) hxc.continuous
    fun w ↦ by simp [heq w]

end WeakKernel

end TauCeti.Vortex
end
