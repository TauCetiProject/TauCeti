/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Fredholm
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The gauge-fixed vortex operator on `H¹` has index `2m`

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` is realized as a bounded operator

`TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`,

with `a` the `L∞` class of `x`. At a `C¹` vortex with `|α| → 1` at infinity it is onto
(`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`), and if also `d_a α → 0` at infinity it is
Fredholm (`TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator`), so its index is the real
dimension of its kernel. This file computes that dimension, completing Taubes's computation of the
index of the linearized vortex operator.

* **The kernel is the weak and classical kernel.** At every continuous field, taking the `L²` class
  of the values identifies the kernel of the realization with the weak `L²` kernel
  `weakGaugeFixedKernel x`, the square-integrable weak solutions of `L_x y = 0`
  (`TauCeti.Vortex.sobolevGaugeFixedKernelEquiv`). The map is injective because an element of
  `H¹(ℂ)` is determined by its values, it lands in the weak kernel by integration by parts
  (`TauCeti.Vortex.mem_ker_sobolevGaugeFixedOperator_iff`), and it is onto because every weak
  `L²` solution is the value of a strong `H¹` solution
  (`TauCeti.Vortex.exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`).
  At a smooth field whose coordinates have bounded derivatives through order `3`, composing with
  `TauCeti.Vortex.gaugeFixedKernelEquivWeak` identifies `(sobolevGaugeFixedOperator a).ker`
  with the classical `C²` kernel `gaugeFixedKernel x`
  (`TauCeti.Vortex.kerSobolevGaugeFixedOperatorEquiv`), yielding exact kernel dimensions and real
  Fredholm indices `2 |D|` (`TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul_card`) and
  `2 m`
  (`TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow`),
  as well as bijectivity when the section has no zeros or in degree `0`
  (`TauCeti.Vortex.bijective_sobolevGaugeFixedOperator_of_forall_sectionValue_ne_zero`,
  `TauCeti.Vortex.bijective_sobolevGaugeFixedOperator`).
* **Index `2m`.** At a continuous plane vortex lying in the affine field space `A_m^k` for every
  `k`, the weak kernel has real dimension `2m`
  (`TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`), the dimension of the divisor space
  `Sym^m ℂ`. Such a vortex is smooth, `|α| → 1` and `d_a α → 0` at infinity
  (`TauCeti.Vortex.tendsto_covariantDerivative_cocompact`), so the realization is onto
  (`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace`) and
  Fredholm (`TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace`),
  its kernel has dimension `2m`
  (`TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_eq_two_mul`) and its index is `2m`
  (`TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul`).

Every smooth framed degree-`m` vortex has a framed gauge representative lying in every `A_m^k`
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`), and every effective divisor
of degree `m` is the divisor of such a vortex, so these results apply over all of `Sym^m ℂ`.

## Main results

* `TauCeti.Vortex.sobolevGaugeFixedKernelEquiv`: the kernel of the realization is linearly
  isomorphic to the weak `L²` kernel, at every continuous field, by taking the `L²` class of the
  values (`TauCeti.Vortex.coeFn_sobolevGaugeFixedKernelEquiv`).
* `TauCeti.Vortex.kerSobolevGaugeFixedOperatorEquiv`: canonical real-linear equivalence between
  `(sobolevGaugeFixedOperator a).ker` and the classical `C²` kernel `gaugeFixedKernel x`.
* `TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card`,
  `finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow`,
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul_card`, and
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow`:
  exact kernel dimension and real Fredholm index `2 |D|` and `2 m`.
* `TauCeti.Vortex.bijective_sobolevGaugeFixedOperator_of_forall_sectionValue_ne_zero` and
  `TauCeti.Vortex.bijective_sobolevGaugeFixedOperator`: bijectivity when the section has no zeros
  and in degree zero.
* `TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_eq_two_mul`: at a plane vortex in every
  `A_m^k`, the kernel of the realization has real dimension `2m`.
* `TauCeti.Vortex.sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace`: at such a
  vortex, the realization is onto.
* `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace`: at such a
  vortex, the realization is Fredholm.
* `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul`: at such a vortex, the realization
  has index `2m`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter TopologicalSpace Module
open scoped ENNReal Topology RealInnerProductSpace ContDiff

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- The values of `y ∈ H¹(ℂ)⁴` form a square-integrable field `ℂ → ℝ⁴`. -/
private theorem memLp_values (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4))) 2
      volume :=
  memLp_piLp_iff.2 fun j ↦ by simpa using W1p.memLp_value (y j)

/-- The `L²` class of the values of `y ∈ H¹(ℂ)⁴`. -/
private def valuesLp : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →ₗ[ℝ]
    Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) where
  toFun y := (memLp_values y).toLp _
  map_add' y y' := by
    rw [← MemLp.toLp_add]
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [(ae_all_iff.2 fun j ↦ W1p.value_add_ae (y j) (y' j)).filter_mono
      (ae_mono (Measure.restrict_coe_opens_top _).ge)]
      with z hz
    ext j
    simp [hz j]
  map_smul' c y := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [(ae_all_iff.2 fun j ↦ W1p.value_smul_ae c (y j)).filter_mono
      (ae_mono (Measure.restrict_coe_opens_top _).ge)]
      with z hz
    ext j
    simp [hz j]

private theorem coeFn_valuesLp (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    valuesLp y =ᵐ[volume]
      fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)) :=
  (memLp_values y).coeFn_toLp

/-- An element of `H¹(ℂ)⁴` is determined by its values. -/
private theorem valuesLp_injective : Function.Injective valuesLp := by
  refine (injective_iff_map_eq_zero valuesLp).2 fun y hy ↦ funext fun j ↦ W1p.ext_value ?_
  rw [Pi.zero_apply, W1p.value_zero, Lp.eq_zero_iff_ae_eq_zero]
  refine ae_restrict_of_ae ?_
  filter_upwards [coeFn_valuesLp y, hy ▸ Lp.coeFn_zero _ 2 (volume : Measure ℂ)] with z h₁ h₂
  simpa using congr($(h₁.symm.trans h₂) j)

/-- The values of an element of the kernel of the realization solve `L_x y = 0` weakly, so their
`L²` class lies in the weak kernel. -/
private theorem valuesLp_mem_weakGaugeFixedKernel (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2} (hy : y ∈ (sobolevGaugeFixedOperator a).ker) :
    valuesLp y ∈ weakGaugeFixedKernel x := by
  refine (mem_weakGaugeFixedKernel_iff hx).2 fun η hη hηc ↦ ?_
  rw [← (mem_ker_sobolevGaugeFixedOperator_iff hx hax).1 hy η hη hηc]
  exact integral_congr_ae ((coeFn_valuesLp y).mono fun z hz ↦ by simp only [hz])

/-- Every element of the weak kernel is the `L²` class of the values of an element of the kernel
of the realization. -/
private theorem exists_valuesLp_eq (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} (hu : u ∈ weakGaugeFixedKernel x) :
    ∃ w ∈ (sobolevGaugeFixedOperator a).ker, valuesLp w = u := by
  have h0 (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
      ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z, η z⟫ = 0 := by
    rw [integral_congr_ae (((Lp.coeFn_zero _ 2 μ⊤).filter_mono
      (ae_mono (Measure.restrict_coe_opens_top _).ge)).mono
      fun z hz ↦ by rw [hz, Pi.zero_apply, inner_zero_left])]
    exact integral_zero _ _
  -- A weak solution of `L_x u = 0` is the value of a strong solution.
  obtain ⟨w, hw, hw0⟩ := exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    hx hax (Lp.memLp u) (f := (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)) fun η hη hηc ↦ by
      rw [h0]
      exact (mem_weakGaugeFixedKernel_iff hx).1 hu η hη hηc
  refine ⟨w, LinearMap.mem_ker.2 hw0, Lp.ext ?_⟩
  filter_upwards [coeFn_valuesLp w, ae_all_iff.2 hw] with z h₁ h₂
  rw [h₁]
  ext j
  simp [h₂ j]

/-- **The kernel of the `H¹` realization is the weak `L²` kernel.** At a continuous field `x`
with `L∞` class `a`, taking the `L²` class of the values is a linear isomorphism from the kernel of
the realization `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` onto the weak `L²` kernel of `L_x`, the
square-integrable weak solutions of `L_x y = 0`. -/
def sobolevGaugeFixedKernelEquiv (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  LinearEquiv.ofBijective ((valuesLp.domRestrict _).codRestrict (weakGaugeFixedKernel x)
      fun y ↦ valuesLp_mem_weakGaugeFixedKernel hx hax y.property)
    ⟨fun _ _ h ↦ Subtype.ext (valuesLp_injective (congrArg Subtype.val h)), fun u ↦
      let ⟨w, hw, hwu⟩ := exists_valuesLp_eq hx hax u.property
      ⟨⟨w, hw⟩, Subtype.ext hwu⟩⟩

/-- The isomorphism `sobolevGaugeFixedKernelEquiv` sends `y` to the `L²` class of its values
`z ↦ (y₀(z), y₁(z), y₂(z), y₃(z))`. -/
theorem coeFn_sobolevGaugeFixedKernelEquiv (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : (sobolevGaugeFixedOperator a).ker) :
    (sobolevGaugeFixedKernelEquiv hx hax y : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume) =ᵐ[volume]
      fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value (y.val j) z : EuclideanSpace ℝ (Fin 4)) :=
  coeFn_valuesLp y.val

/-- At a continuous field with `L∞` class `a`, the kernel of the realization of `L_x` on `H¹` has
the dimension of the weak `L²` kernel. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_finrank_weakGaugeFixedKernel (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = finrank ℝ (weakGaugeFixedKernel x) :=
  (sobolevGaugeFixedKernelEquiv hx hax).finrank_eq

/-! ### Identification with the classical kernel, index `2|D|`, and degree-zero bijectivity -/

/-- **Canonical equivalence between `H¹` and `C²` kernels.** At a smooth field `x` with bounded
derivatives through order `3` and `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a` is
canonically linearly isomorphic to `gaugeFixedKernel x`. -/
def kerSobolevGaugeFixedOperatorEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] gaugeFixedKernel x :=
  (sobolevGaugeFixedKernelEquiv hx.continuous hax).trans
    (gaugeFixedKernelEquivWeak hx hbound).symm

/-- The image of an `H¹` kernel element under `kerSobolevGaugeFixedOperatorEquiv` agrees almost
everywhere with its value coordinates. -/
theorem kerSobolevGaugeFixedOperatorEquiv_apply_ae (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) (j : Fin 4) :
    W1p.value (y.val j) =ᵐ[μ⊤]
      fun z ↦ (kerSobolevGaugeFixedOperatorEquiv hx hbound hax y).val z j := by
  set Y := kerSobolevGaugeFixedOperatorEquiv hx hbound hax y
  have hY :
      gaugeFixedKernelEquivWeak hx hbound Y = sobolevGaugeFixedKernelEquiv hx.continuous hax y :=
    (gaugeFixedKernelEquivWeak hx hbound).apply_symm_apply _
  have h1 := coe_gaugeFixedKernelEquivWeak_ae_eq hx hbound Y
  have h2 := coeFn_sobolevGaugeFixedKernelEquiv hx.continuous hax y
  rw [hY] at h1
  refine ae_restrict_of_ae ?_
  filter_upwards [h1, h2] with z hz1 hz2
  simpa using congr($(hz2.symm.trans hz1) j)

/-- The preimage of a classical kernel element under `kerSobolevGaugeFixedOperatorEquiv` has value
coordinates agreeing almost everywhere with that classical element. -/
theorem kerSobolevGaugeFixedOperatorEquiv_symm_value_ae (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (Y : gaugeFixedKernel x) (j : Fin 4) :
    W1p.value (((kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm Y).val j) =ᵐ[μ⊤]
      fun z ↦ Y.val z j := by
  simpa [LinearEquiv.apply_symm_apply] using
    kerSobolevGaugeFixedOperatorEquiv_apply_ae hx hbound hax
      ((kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm Y) j

/-- Characteristic property of `kerSobolevGaugeFixedOperatorEquiv`: an `H¹` kernel element `y` maps
to `Y ∈ gaugeFixedKernel x` if and only if each coordinate value of `y` agrees almost everywhere
with the corresponding coordinate of `Y`. -/
theorem kerSobolevGaugeFixedOperatorEquiv_eq_iff (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) (Y : gaugeFixedKernel x) :
    kerSobolevGaugeFixedOperatorEquiv hx hbound hax y = Y ↔
      ∀ j : Fin 4, W1p.value (y.val j) =ᵐ[μ⊤] fun z ↦ Y.val z j := by
  refine ⟨fun h j ↦ h ▸ kerSobolevGaugeFixedOperatorEquiv_apply_ae hx hbound hax y j, fun h ↦ ?_⟩
  set Y' := kerSobolevGaugeFixedOperatorEquiv hx hbound hax y
  have hae : (Y' : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] Y := by
    have hae_j (j : Fin 4) :
        (fun z ↦ Y'.val z j) =ᵐ[volume] fun z ↦ Y.val z j := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (kerSobolevGaugeFixedOperatorEquiv_apply_ae hx hbound hax y j).symm.trans (h j)
    filter_upwards [ae_all_iff.2 hae_j] with z hz
    ext j
    exact hz j
  exact Subtype.ext (((continuous_of_mem_gaugeFixedKernel Y'.property).ae_eq_iff_eq volume
    (continuous_of_mem_gaugeFixedKernel Y.property)).1 hae)

/-- **Exact real dimension `2 |D|` of the `H¹` kernel of `L_x`.** At a smooth field `x` with
bounded derivatives through order `3`, vanishing holomorphicity rows `∂bar_a α = 0`, `|α|² → 1`
at infinity, zero divisor `D`, and `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a`
has real dimension `2 |D|`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * Multiset.card D := by
  rw [(kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD]

/-- **Exact real dimension `2 m` of the `H¹` kernel of `L_x` at a framed field.** At a smooth field
`x` with bounded derivatives through order `3`, vanishing holomorphicity rows, the degree-`m` end
framing `α(z) (z / |z|)⁻ᵐ → 1`, and `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a`
has real dimension `2 m`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow
    {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m := by
  rw [(kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe]

/-- **Real Fredholm index `2 |D|` of `L_x : H¹ → L²`.** At a smooth plane vortex `x` with bounded
derivatives through order `3`, `|α|² → 1` at infinity, zero divisor `D`, and `L∞` class `a`,
the Sobolev realization `sobolevGaugeFixedOperator a` has real Fredholm index `2 |D|`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * Multiset.card D := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
      (sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol hlim hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card hx hbound
      (fun w ↦ by simp [hsol w]) hlim hD hax]
  push_cast
  rfl

/-- **Real Fredholm index `2 m` of `L_x : H¹ → L²` at a framed vortex.** At a smooth plane vortex
`x` with bounded derivatives through order `3`, the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`, and `L∞` class `a`, the Sobolev realization `sobolevGaugeFixedOperator a`
has real Fredholm index `2 m`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow
    {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * m := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
      (sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol
        (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow hx hbound
      (fun w ↦ by simp [hsol w]) hframe hax]
  push_cast
  rfl

/-- Transport triviality of `gaugeFixedKernel x` back to `(sobolevGaugeFixedOperator a).ker` via
`kerSobolevGaugeFixedOperatorEquiv`. -/
private theorem ker_sobolevGaugeFixedOperator_eq_bot_of_gaugeFixedKernel_eq_bot
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (hbot : gaugeFixedKernel x = ⊥) :
    (sobolevGaugeFixedOperator a).ker = ⊥ :=
  Submodule.subsingleton_iff_eq_bot.1 <|
    have : Subsingleton (gaugeFixedKernel x) := Submodule.subsingleton_iff_eq_bot.2 hbot
    (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).injective.subsingleton

/-- **Trivial `H¹` kernel when the section has no zeros.** At a smooth field `x` with bounded
derivatives through order `3`, vanishing holomorphicity rows, `|α|² → 1` at infinity, no zeros of
`α`, and `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a` is trivial. -/
theorem ker_sobolevGaugeFixedOperator_eq_bot_of_forall_sectionValue_ne_zero (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker = ⊥ :=
  ker_sobolevGaugeFixedOperator_eq_bot_of_gaugeFixedKernel_eq_bot hx hbound hax
    (gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero (hx.of_le (by simp)) hhol hlim hne)

/-- **Trivial `H¹` kernel in degree zero.** At a smooth field `x` with bounded derivatives through
order `3`, vanishing holomorphicity rows, `α(z) → 1` at infinity, and `L∞` class `a`, the kernel
of `sobolevGaugeFixedOperator a` is trivial. -/
theorem ker_sobolevGaugeFixedOperator_eq_bot (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1)) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker = ⊥ :=
  ker_sobolevGaugeFixedOperator_eq_bot_of_gaugeFixedKernel_eq_bot hx hbound hax
    (gaugeFixedKernel_eq_bot (hx.of_le (by simp)) hhol hframe)

/-- **Bijectivity of `L_x : H¹ → L²` when the section has no zeros.** At a smooth plane vortex `x`
with bounded derivatives through order `3`, `|α|² → 1` at infinity, no zeros of `α`, and `L∞`
class `a`, `sobolevGaugeFixedOperator a` is bijective (hence a continuous linear equivalence by
`ContinuousLinearEquiv.ofBijective`). -/
theorem bijective_sobolevGaugeFixedOperator_of_forall_sectionValue_ne_zero (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) (hax : a =ᵐ[μ⊤] x) :
    Function.Bijective (sobolevGaugeFixedOperator a) :=
  ⟨LinearMap.ker_eq_bot.1 (ker_sobolevGaugeFixedOperator_eq_bot_of_forall_sectionValue_ne_zero
      hx hbound (fun w ↦ by simp [hsol w]) hlim hne hax),
    sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol hlim hax⟩

/-- **Bijectivity of `L_x : H¹ → L²` in degree zero.** At a smooth plane vortex `x` with bounded
derivatives through order `3`, `α(z) → 1` at infinity, and `L∞` class `a`,
`sobolevGaugeFixedOperator a` is bijective. -/
theorem bijective_sobolevGaugeFixedOperator (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1)) (hax : a =ᵐ[μ⊤] x) :
    Function.Bijective (sobolevGaugeFixedOperator a) := by
  have hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1) :=
    tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow (m := 0) (by simpa using hframe)
  exact ⟨LinearMap.ker_eq_bot.1 (ker_sobolevGaugeFixedOperator_eq_bot hx hbound
      (fun w ↦ by simp [hsol w]) hframe hax),
    sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol hlim hax⟩

/-! ### Plane vortices in every `A_m^k` -/

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **The kernel of the realization at a plane vortex is finite-dimensional.** Let `x` be a
continuous field lying in `A_m^k` for every `k` whose section satisfies the holomorphicity rows
`∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`, and let `a` be its
`L∞` class. Then the kernel of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is finite-dimensional. -/
theorem finiteDimensional_ker_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x) :
    FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker :=
  have := finiteDimensional_weakGaugeFixedKernel hx hmem hhol
  (sobolevGaugeFixedKernelEquiv hx hax).symm.finiteDimensional

/-- **The kernel of the realization at a plane vortex has dimension `2m`.** Let `x` be a
continuous field lying in the affine field space `A_m^k` for every `k` whose section satisfies the
holomorphicity rows `∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`,
and let `a` be its `L∞` class. Then the kernel of the realization `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` has
real dimension `2m`, the dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m := by
  rw [finrank_ker_sobolevGaugeFixedOperator_eq_finrank_weakGaugeFixedKernel hx hax,
    finrank_weakGaugeFixedKernel_eq_two_mul hx hmem hhol]

/-- **The realization at a plane vortex is onto.** Let `x` be a continuous plane vortex lying in
the affine field space `A_m^k` for every `k`, with `L∞` class `a`. Then the cokernel of the
realization `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` vanishes. -/
theorem sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hsol : ∀ z, equation x z = 0) (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (sobolevGaugeFixedOperator a) :=
  sobolevGaugeFixedOperator_surjective
    ((contDiff_of_forall_mem_framedFieldSpace hx hmem).of_le (by simp)) hsol
    (tendsto_normSq_of_forall_mem_framedFieldSpace hx hmem) hax

/-- **The realization at a plane vortex is Fredholm.** Let `x` be a continuous plane vortex lying
in the affine field space `A_m^k` for every `k`, with `L∞` class `a`. Then the realization
`L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is a Fredholm operator. -/
theorem isFredholm_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace hx hmem
  have hlim := tendsto_normSq_of_forall_mem_framedFieldSpace hx hmem
  exact isFredholm_sobolevGaugeFixedOperator (hxs.of_le (by simp)) hsol hlim
    (tendsto_covariantDerivative_cocompact (contDiff_euclidean.1 hxs 0).continuous
      ((contDiff_euclidean.1 hxs 2).of_le (by simp)) ((contDiff_euclidean.1 hxs 3).of_le (by simp))
      hsol hlim 1) hax

/-- **The realization at a plane vortex has index `2m`** (Taubes). Let `x` be a continuous plane
vortex lying in the affine field space `A_m^k` for every `k`, with `L∞` class `a`. Then the
realization `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the gauge-fixed vortex operator, which is onto, has real
index `2m`, the dimension of the divisor space `Sym^m ℂ`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * m := by
  rw [ContinuousLinearMap.index_of_surjective _
      (sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace hx hmem hsol hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul hx hmem (fun w ↦ by simp [hsol w]) hax]
  omega

end TauCeti.Vortex
