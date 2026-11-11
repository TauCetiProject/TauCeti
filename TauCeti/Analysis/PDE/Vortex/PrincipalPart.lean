/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import TauCeti.Analysis.Complex.Wirtinger.PrincipalPart
public import TauCeti.Analysis.Complex.ZeroMultiplicity
import TauCeti.Analysis.PDE.Vortex.Divisor
import TauCeti.Analysis.PDE.Vortex.LogVariation
import TauCeti.Analysis.PDE.Vortex.Zeros
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# The principal parts of the kernel of the gauge-fixed vortex operator

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)` and a variation `y` has section variation `δα`. At a field `x` satisfying the
holomorphicity rows `∂bar_a α = 0` of the vortex equation, consider the kernel of the
gauge-fixed operator `L_x = d₀* ⊕ d₁` on `C²` square-integrable variations
(`TauCeti.Vortex.gaugeFixedKernel x`). Off the zeros of `α`, a kernel element `y` is the
logarithmic variation of `η = δα / α`, whose connection part is `δb₁ + i δb₂ = 2 i ∂bar η`
(`TauCeti.Vortex.apply_eq_logVariation_div_apply`). So `∂bar η` extends to the `C²` function
`(δb₁ + i δb₂) / (2 i)` on the whole plane, and at a zero `z` of `α` of multiplicity `n` the
product `(w - z)ⁿ η` is bounded. By the removable singularity theorem for `∂bar`
(`TauCeti.exists_contDiffAt_eventuallyEq_add_principalPartSum`), near `z`

`δα / α = g + ∑_{j < n} c_j / (w - z)^(j + 1)`

with `g` of class `C²` at `z`
(`TauCeti.Vortex.exists_contDiffAt_eventuallyEq_add_principalPartSum_div_sectionValue`). The
coefficients `c` are the principal part of `δα / α` at `z`.

A kernel element whose quotient `δα / α` is bounded near every zero of `α` vanishes, when
`|α| → 1` at infinity (`TauCeti.Vortex.eq_zero_of_isBigO_div_sectionValue`): the quotient then
extends to a global `C²` function, and the vanishing theorem
`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto` applies.
Hence, if the zeros of `α` form the divisor `D`, the **principal-part map**
(`TauCeti.Vortex.kernelPrincipalPart`), sending a kernel element to the principal parts of
`δα / α` of order `D(z)` at the points `z` of `D`, is a real-linear injection of the kernel into
`∏_{z ∈ D} ℂ^(D(z))`, a real vector space of dimension `2 |D|`
(`TauCeti.Vortex.kernelPrincipalPart_injective`). For a field with the degree-`m` end framing,
whose divisor has `m` points, the kernel is therefore finite-dimensional, of real dimension at
most `2 m` (`TauCeti.Vortex.finrank_gaugeFixedKernel_le`).

At an actual vortex this is the injectivity half of the identification of the kernel of `L_x`
with the tangent space `ℂᵐ` of the divisor space `Sym^m ℂ`. Surjectivity of the principal-part
map, which needs the existence theory of vortices, and the comparison of this classical kernel
with the kernel of the Sobolev realization of `L_x`, which needs elliptic regularity, are not
treated here.

## Main definitions

* `TauCeti.Vortex.kernelPrincipalPart`: the principal parts of `δα / α` at the zeros of `α`.

## Main results

* `TauCeti.Vortex.exists_contDiffAt_eventuallyEq_add_principalPartSum_div_sectionValue`: the
  local form of `δα / α` at a zero of `α`.
* `TauCeti.Vortex.eq_zero_of_isBigO_div_sectionValue`: a kernel element with `δα / α` bounded
  at the zeros of `α` vanishes.
* `TauCeti.Vortex.kernelPrincipalPart_injective`: the principal-part map is injective.
* `TauCeti.Vortex.finrank_gaugeFixedKernel_le`: the kernel of `L_x` at a framed degree-`m` field
  has real dimension at most `2 m`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Complex Filter MeasureTheory Module Set Topology

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The local form of `δα / α` at a zero -/

/-- **The singularity of `δα / α` at a zero of the section.** Let `x` be a differentiable field
satisfying the holomorphicity rows of the vortex equation, and `y` a `C²` variation satisfying
the two `∂bar` rows of `L_x y = 0`. If the section factors near `z` as `α(w) = (w - z)ⁿ V(w)` with
`V` continuous and nonzero at `z`, then near `z`, off `z`,
`δα / α = g + ∑_{j < n} c_j / (w - z)^(j + 1)` for some coefficients `c` and a function `g` of
class `C²` at `z`. -/
theorem exists_contDiffAt_eventuallyEq_add_principalPartSum_div_sectionValue
    (hx : Differentiable ℝ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hy : ContDiff ℝ 2 y)
    (hker : ∀ w, gaugeFixedOperator x y w 2 = 0 ∧ gaugeFixedOperator x y w 3 = 0) {z : ℂ} {n : ℕ}
    {V : ℂ → ℂ} (hV : ContinuousAt V z) (hV₀ : V z ≠ 0)
    (hfac : ∀ᶠ w in 𝓝 z, sectionValue x w = (w - z) ^ n * V w) :
    ∃ (c : Fin n → ℂ) (g : ℂ → ℂ), ContDiffAt ℝ 2 g z ∧
      ∀ᶠ w in 𝓝[≠] z, sectionValue y w / sectionValue x w = g w + principalPartSum c z w := by
  have hyd : Differentiable ℝ y := hy.differentiable (by simp)
  have hne : ∀ᶠ w in 𝓝[≠] z, (w - z) ^ n ≠ 0 ∧ V w ≠ 0 ∧
      sectionValue x w = (w - z) ^ n * V w := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hV.eventually_ne hV₀),
      nhdsWithin_le_nhds hfac] with w hwz hVw hw
    exact ⟨pow_ne_zero _ (sub_ne_zero.mpr hwz), hVw, hw⟩
  -- Off the zeros of `α`, `η = δα / α` has `∂bar η = (δb₁ + i δb₂) / (2 i)`.
  have hη : ∀ᶠ w in 𝓝[≠] z,
      DifferentiableAt ℝ (fun w ↦ sectionValue y w / sectionValue x w) w ∧
        conjWirtingerDeriv (fun w ↦ sectionValue y w / sectionValue x w) w 1 =
          ((y w 0 : ℂ) + y w 1 * I) / (2 * I) := by
    filter_upwards [hne] with w ⟨hwz, hVw, hw⟩
    have hα : sectionValue x w ≠ 0 := by
      rw [hw]
      exact mul_ne_zero hwz hVw
    have hd : DifferentiableAt ℝ (fun w ↦ sectionValue y w / sectionValue x w) w :=
      (differentiableAt_sectionValue_of_differentiableAt (hyd w)).mul
        ((differentiableAt_sectionValue_of_differentiableAt (hx w)).inv hα)
    refine ⟨hd, ?_⟩
    have hrep := apply_eq_logVariation_div_apply (hx w) (hyd w) hα (hhol w).1 (hhol w).2
      (hker w).1 (hker w).2
    have h := logVariation_zero_add_one_mul_I x hd
    rw [← hrep] at h
    rw [h]
    field_simp
  -- The product `(w - z)ⁿ η = δα / V` is bounded near `z`.
  have hb : (fun w ↦ (w - z) ^ n * (sectionValue y w / sectionValue x w)) =O[𝓝[≠] z]
      (fun _ ↦ (1 : ℝ)) := by
    have hc : ContinuousAt (fun w ↦ sectionValue y w / V w) z :=
      (differentiableAt_sectionValue_of_differentiableAt (hyd z)).continuousAt.div hV hV₀
    refine (hc.tendsto.isBigO_one ℝ |>.mono nhdsWithin_le_nhds).congr' ?_ EventuallyEq.rfl
    filter_upwards [hne] with w ⟨hwz, hVw, hw⟩
    rw [hw]
    field_simp
  have hβ : ContDiff ℝ 2 fun w ↦ ((y w 0 : ℂ) + y w 1 * I) / (2 * I) :=
    ((ofRealCLM.contDiff.comp (contDiff_euclidean.1 hy 0)).add
      ((ofRealCLM.contDiff.comp (contDiff_euclidean.1 hy 1)).mul contDiff_const)).div_const _
  exact exists_contDiffAt_eventuallyEq_add_principalPartSum (k := 2) (by norm_num) univ_mem
    hβ.contDiffOn hη hb

/-- At every point `z`, the quotient `δα / α` of a kernel element has a principal part of order
`n z`, for `n` the zero multiplicity function of the section. -/
theorem exists_hasPrincipalPart_div_sectionValue (hx : Differentiable ℝ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hy : y ∈ gaugeFixedKernel x)
    {n : ℂ → ℕ} (hn : IsZeroMultiplicity (sectionValue x) n) (z : ℂ) :
    ∃ c : Fin (n z) → ℂ, HasPrincipalPart (fun w ↦ sectionValue y w / sectionValue x w) z c := by
  obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
  obtain ⟨V, hV, hV₀, hfac⟩ := isZeroMultiplicity_iff.1 hn z
  obtain ⟨c, g, hg, hηg⟩ := exists_contDiffAt_eventuallyEq_add_principalPartSum_div_sectionValue
    hx hhol hyc (fun w ↦ by simp [hker w]) hV hV₀ hfac
  exact ⟨c, hasPrincipalPart_of_eventuallyEq_add hg.continuousAt hηg⟩

/-! ### Kernel elements with regular `δα / α` -/

/-- **A kernel element with `δα / α` bounded at the zeros vanishes.** Let `x` be a `C²` field
satisfying the holomorphicity rows of the vortex equation, with `|α|² → 1` at infinity. If a
kernel element `y` of `L_x` has `δα / α` bounded near every zero of `α`, then `y = 0`. -/
theorem eq_zero_of_isBigO_div_sectionValue (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy : y ∈ gaugeFixedKernel x)
    (hbdd : ∀ z, sectionValue x z = 0 →
      (fun w ↦ sectionValue y w / sectionValue x w) =O[𝓝[≠] z] (fun _ ↦ (1 : ℝ))) :
    y = 0 := by
  obtain ⟨hyc, hy₂, hker⟩ := mem_gaugeFixedKernel.1 hy
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  have hαc : Continuous (sectionValue x) := (contDiff_sectionValue (hxi 2) (hxi 3)).continuous
  have hδc : Continuous (sectionValue y) :=
    (contDiff_sectionValue (contDiff_euclidean.1 hyc 2) (contDiff_euclidean.1 hyc 3)).continuous
  have hne : ∃ w, sectionValue x w ≠ 0 := by
    obtain ⟨w, hw⟩ := (hlim.eventually (lt_mem_nhds zero_lt_one)).exists
    refine ⟨w, fun h ↦ ?_⟩
    rw [sectionValue_eq_zero_iff] at h
    rw [h, mul_zero] at hw
    exact lt_irrefl _ hw
  have hfac := exists_contDiffAt_sectionValue_eq_pow_mul (k := 2) (by norm_num) (hxi 0) (hxi 1)
    ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hne
  -- At every point, `η` agrees on a punctured neighbourhood with a function `C²` at the point.
  have hloc (z : ℂ) : ∃ g : ℂ → ℂ, ContDiffAt ℝ 2 g z ∧
      (fun w ↦ sectionValue y w / sectionValue x w) =ᶠ[𝓝[≠] z] g := by
    obtain ⟨n, V, hV, hV₀, hf⟩ := hfac z
    obtain ⟨c, g, hg, hηg⟩ := exists_contDiffAt_eventuallyEq_add_principalPartSum_div_sectionValue
      (hx.differentiable (by simp)) hhol hyc (fun w ↦ by simp [hker w]) hV.continuousAt hV₀ hf
    have hηb : (fun w ↦ sectionValue y w / sectionValue x w) =O[𝓝[≠] z]
        (fun _ ↦ (1 : ℝ)) := by
      by_cases hz : sectionValue x z = 0
      · exact hbdd z hz
      · exact ((hδc.continuousAt.div hαc.continuousAt hz).tendsto.isBigO_one ℝ).mono
          nhdsWithin_le_nhds
    -- A bounded principal part vanishes.
    have hc : c = 0 :=
      (hasPrincipalPart_of_eventuallyEq_add hg.continuousAt hηg).unique
        (hasPrincipalPart_zero_iff.mpr hηb)
    refine ⟨g, hg, hηg.mono fun w hw ↦ ?_⟩
    simp only [hw, hc, principalPartSum_zero, Pi.zero_apply, add_zero]
  choose g hg hηg using hloc
  -- The zeros of `α` are isolated.
  have hiso (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, sectionValue x w ≠ 0 := by
    obtain ⟨n, V, hV, hV₀, hf⟩ := hfac z
    filter_upwards [nhdsWithin_le_nhds hf, nhdsWithin_le_nhds (hV.continuousAt.eventually_ne hV₀),
      self_mem_nhdsWithin] with w hw hVw hwz
    rw [hw]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hwz)) hVw
  -- The regularized quotient `η' z = g z z` is a global `C²` function with `δα = α η'`.
  set η' : ℂ → ℂ := fun w ↦ g w w with hη'_def
  have hη'off (w : ℂ) (hw : sectionValue x w ≠ 0) :
      η' w = sectionValue y w / sectionValue x w :=
    tendsto_nhds_unique ((hg w).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (((hδc.continuousAt.div hαc.continuousAt hw).tendsto.mono_left nhdsWithin_le_nhds).congr'
        (hηg w))
  have hη'loc (z : ℂ) : η' =ᶠ[𝓝 z] g z := by
    have h : ∀ᶠ w in 𝓝[≠] z, η' w = g z w := by
      filter_upwards [hiso z, hηg z] with w hw hgw
      rw [hη'off w hw]
      exact hgw
    filter_upwards [eventually_nhdsWithin_iff.mp h] with w hw
    by_cases hwz : w = z
    · rw [hwz]
    · exact hw hwz
  have hη'c : ContDiff ℝ 2 η' :=
    contDiff_iff_contDiffAt.mpr fun z ↦ (hg z).congr_of_eventuallyEq (hη'loc z)
  have hfin := finite_setOfPred_sectionValue_eq_zero (k := 2) (by norm_num) (hxi 0) (hxi 1)
    ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hlim
  have hdense : Dense {w | sectionValue x w ≠ 0} := by
    simpa only [compl_ofPred] using Set.Countable.dense_compl ℝ hfin.countable
  have hyη' (w : ℂ) : sectionValue y w = sectionValue x w * η' w := by
    refine congrFun (Continuous.ext_on hdense hδc (hαc.mul hη'c.continuous) fun w hw ↦ ?_) w
    have hw' : sectionValue x w ≠ 0 := hw
    rw [Pi.mul_apply, hη'off w hw']
    field_simp
  exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto (μ := volume)
    (hx.of_le one_le_two) hhol hlim hyc.continuous hy₂ hker hη'c hyη'

/-! ### The principal-part map -/

section PrincipalPartMap

variable (hx : Differentiable ℝ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
  {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)

/-- **The principal-part map** of the kernel of `L_x`, at a field whose section has zero divisor
`D`: a kernel element `y` goes to the principal parts of order `D(z)` of `δα / α` at the points
`z` of `D`. -/
def kernelPrincipalPart :
    gaugeFixedKernel x →ₗ[ℝ] ((z : D.toFinset) → Fin (D.count (z : ℂ)) → ℂ) where
  toFun y z := principalPart (fun w ↦ sectionValue y w / sectionValue x w) z (D.count (z : ℂ))
  map_add' y v := by
    funext z
    obtain ⟨c, hc⟩ := exists_hasPrincipalPart_div_sectionValue hx hhol y.2 hD z
    obtain ⟨d, hd⟩ := exists_hasPrincipalPart_div_sectionValue hx hhol v.2 hD z
    have hcd : HasPrincipalPart
        (fun w ↦ sectionValue ((y + v : gaugeFixedKernel x) : ℂ → EuclideanSpace ℝ (Fin 4)) w /
          sectionValue x w) z (c + d) :=
      (hc.add hd).congr (Eventually.of_forall fun w ↦ by
        simp only [Submodule.coe_add, sectionValue_add, add_div])
    rw [Pi.add_apply, hcd.principalPart_eq, hc.principalPart_eq, hd.principalPart_eq]
  map_smul' t y := by
    funext z
    obtain ⟨c, hc⟩ := exists_hasPrincipalPart_div_sectionValue hx hhol y.2 hD z
    have htc : HasPrincipalPart
        (fun w ↦ sectionValue ((t • y : gaugeFixedKernel x) : ℂ → EuclideanSpace ℝ (Fin 4)) w /
          sectionValue x w) z ((t : ℂ) • c) :=
      (hc.const_mul (t : ℂ)).congr (Eventually.of_forall fun w ↦ by
        simp only [Submodule.coe_smul, sectionValue_smul, mul_div_assoc])
    rw [Pi.smul_apply, htc.principalPart_eq, hc.principalPart_eq, RingHom.id_apply]
    ext j
    simp [Complex.real_smul]

@[simp]
theorem kernelPrincipalPart_apply (y : gaugeFixedKernel x) (z : D.toFinset) :
    kernelPrincipalPart hx hhol hD y z =
      principalPart (fun w ↦ sectionValue y w / sectionValue x w) z (D.count (z : ℂ)) :=
  (rfl)

/-- The principal parts selected by `kernelPrincipalPart` are the principal parts of
`δα / α`. -/
theorem hasPrincipalPart_kernelPrincipalPart (y : gaugeFixedKernel x) (z : D.toFinset) :
    HasPrincipalPart (fun w ↦ sectionValue y w / sectionValue x w) z
      (kernelPrincipalPart hx hhol hD y z) :=
  hasPrincipalPart_principalPart (exists_hasPrincipalPart_div_sectionValue hx hhol y.2 hD z)

end PrincipalPartMap

/-- **Injectivity of the principal-part map.** At a `C²` field satisfying the holomorphicity
rows of the vortex equation, with zero divisor `D` and `|α|² → 1` at infinity, a kernel element
of `L_x` is determined by the principal parts of `δα / α` at the points of `D`. -/
theorem kernelPrincipalPart_injective (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Function.Injective (kernelPrincipalPart (hx.differentiable (by simp)) hhol hD) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  refine Subtype.ext (eq_zero_of_isBigO_div_sectionValue hx hhol hlim y.2 fun z hz ↦ ?_)
  have hzD : z ∈ D.toFinset := Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (hD.pos_iff.mpr hz))
  have h := hasPrincipalPart_kernelPrincipalPart (hx.differentiable (by simp)) hhol hD y ⟨z, hzD⟩
  rw [hy, Pi.zero_apply] at h
  exact hasPrincipalPart_zero_iff.mp h

/-- **The kernel of `L_x` at a framed field is finite-dimensional.** -/
theorem finiteDimensional_gaugeFixedKernel (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (gaugeFixedKernel x) := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨D, -, hD⟩ := exists_isZeroMultiplicity_of_tendsto (k := 2) (by norm_num) (hxi 0) (hxi 1)
    ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hframe
  exact FiniteDimensional.of_injective _ (kernelPrincipalPart_injective hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD)

/-- **The kernel of `L_x` at a framed degree-`m` field has real dimension at most `2 m`.** Let
`x` be a `C²` field satisfying the holomorphicity rows `∂bar_a α = 0` of the vortex equation,
whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then the `C²`
square-integrable kernel of the gauge-fixed operator `L_x` has real dimension at most `2 m`. -/
theorem finrank_gaugeFixedKernel_le (hx : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    finrank ℝ (gaugeFixedKernel x) ≤ 2 * m := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨D, rfl, hD⟩ := exists_isZeroMultiplicity_of_tendsto (k := 2) (by norm_num) (hxi 0)
    (hxi 1) ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hframe
  refine (LinearMap.finrank_le_finrank_of_injective (kernelPrincipalPart_injective hx hhol
    (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hD)).trans_eq ?_
  -- The principal parts at the points of `D` form a real vector space of dimension `2 |D|`.
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.sum_coe_sort D.toFinset (fun z ↦ D.count z * 2), ← Finset.sum_mul,
    Multiset.toFinset_sum_count_eq, mul_comm]

end TauCeti.Vortex
