/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.KernelDimension
public import TauCeti.Analysis.PDE.Vortex.SobolevScale
import TauCeti.Analysis.PDE.Vortex.Bootstrap
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The weak `L²` kernel of the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) has
formal adjoint `L_x*` (`gaugeFixedAdjoint`). Its **weak `L²` kernel**
(`TauCeti.Vortex.weakGaugeFixedKernel`) is the orthogonal complement in `L²(ℂ; ℝ⁴)` of the fields
`L_x* η`, `η` smooth and compactly supported. At a continuous field it consists of the weak
solutions of `L_x u = 0`, the square-integrable `u` with `∫ ⟪u, L_x* η⟫ = 0` for every such `η`
(`TauCeti.Vortex.mem_weakGaugeFixedKernel_iff`). At an essentially bounded field these weak
solutions lie in `H¹`
(`TauCeti.Vortex.mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`), so this is also
the kernel of `L_x` acting weakly on `H¹(ℂ)⁴`, the kernel in the Fredholm theory of
`L_x : H¹ → L²`.

The classical kernel `gaugeFixedKernel x` consists of the `C²` square-integrable solutions of
`L_x y = 0`, and at a framed plane vortex of degree `m` it has real dimension `2m`, the dimension
of the divisor space `Sym^m ℂ` (`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul`). This file
shows that the two kernels agree.

* A classical kernel element is a weak solution, by integration by parts
  (`TauCeti.Vortex.forall_integral_inner_gaugeFixedAdjoint_eq_iff`), so taking `L²` classes maps
  `gaugeFixedKernel x` injectively into `weakGaugeFixedKernel x` at every continuous field
  (`TauCeti.Vortex.gaugeFixedKernelToLp_mem_weakGaugeFixedKernel`).
* At a smooth field whose coordinates have bounded derivatives of every order, the elliptic
  bootstrap makes every weak solution of `L_x u = 0` almost everywhere equal to a smooth classical
  one (`TauCeti.Vortex.exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq`), so the map
  is onto (`TauCeti.Vortex.range_gaugeFixedKernelToLp`) and gives a linear isomorphism
  `TauCeti.Vortex.gaugeFixedKernelEquivWeak : gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x`.
  Consequently, testing against `C^k` compactly supported fields for any `1 ≤ k ≤ ∞` cuts out the
  same weak kernel (`TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_forall_contDiff`).

A continuous field lying in the affine field space `A_m^k` for every `k` is such a field, with the
degree-`m` end framing. If its section also satisfies the holomorphicity rows `∂bar_a α = 0`, as
at a plane vortex, its weak `L²` kernel is finite-dimensional of real dimension `2m`
(`TauCeti.Vortex.finiteDimensional_weakGaugeFixedKernel`,
`TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`), and the same holds for every `C¹`
Coulomb-gauge vortex in `A_m^k` (`k ≥ 2`) via the elliptic bootstrap
(`TauCeti.Vortex.finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero`,
`TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero`). This is the kernel
in Taubes's computation of the real index `2m` of the linearized vortex operator. At a plane
vortex, a field satisfying the full vortex equation, the cokernel of that operator also vanishes
(`TauCeti.Vortex.exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq`).

## Main definitions

* `TauCeti.Vortex.weakGaugeFixedKernel x`: the weak `L²` kernel of `L_x`.
* `TauCeti.Vortex.gaugeFixedKernelEquivWeak`: linear isomorphism between `gaugeFixedKernel x` and
  `weakGaugeFixedKernel x` at a smooth field with bounded derivatives.

## Main results

* `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff` and
  `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff_forall_contDiff`: at a continuous field (and, for
  `C^k` tests with `1 ≤ k ≤ ∞`, at a smooth field with bounded derivatives), the weak kernel
  consists of the weak solutions of `L_x u = 0`.
* `TauCeti.Vortex.range_gaugeFixedKernelToLp`: at a smooth field with bounded derivatives, the
  weak kernel is the space of `L²` classes of the classical kernel.
* `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_card`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_of_tendsto`,
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`, and
  `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero`: real dimension
  `2 |D|` and `2m` of the weak `L²` kernel at smooth fields with bounded derivatives and at
  Coulomb-gauge vortices in `A_m^k` (`k ≥ 2`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Filter MeasureTheory Module
open scoped RealInnerProductSpace ContDiff Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The weak `L²` kernel of the gauge-fixed operator** `L_x = d₀* ⊕ d₁`: the orthogonal
complement in `L²(ℂ; ℝ⁴)` of the `L²` classes of the fields `L_x* η`, for smooth compactly
supported test fields `η`. At a continuous field it consists of the weak solutions of `L_x u = 0`
(`mem_weakGaugeFixedKernel_iff`). -/
def weakGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) :=
  (Submodule.span ℝ {g | ∃ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η ∧
    HasCompactSupport η ∧ (g : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] gaugeFixedAdjoint x η})ᗮ

/-- **The weak kernel consists of the weak solutions of `L_x u = 0`.** At a continuous field `x`,
a square-integrable field `u` lies in the weak kernel of `L_x` exactly when
`∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly supported test field `η`. -/
theorem mem_weakGaugeFixedKernel_iff (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  rw [weakGaugeFixedKernel, Submodule.mem_orthogonal]
  refine ⟨fun h η hη hηc ↦ ?_, fun h g hg ↦ ?_⟩
  · -- The field `L_x* η` is continuous with compact support, so it has an `L²` class.
    have hm : MemLp (gaugeFixedAdjoint x η) 2 volume :=
      (continuous_gaugeFixedAdjoint hx (hη.of_le (by simp))).memLp_of_hasCompactSupport
        (hasCompactSupport_gaugeFixedAdjoint hηc)
    rw [← L2.inner_toLp u hm, real_inner_comm]
    exact h _ (Submodule.subset_span ⟨η, hη, hηc, hm.coeFn_toLp⟩)
  · induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨η, hη, hηc, hgη⟩ := hg
      rw [L2.inner_def, ← h η hη hηc]
      exact integral_congr_ae (hgη.mono fun z hz ↦ by dsimp only; rw [hz, real_inner_comm])
    | zero => exact inner_zero_left u
    | add g g' _ _ hg hg' => rw [inner_add_left, hg, hg', add_zero]
    | smul c g _ hg => rw [real_inner_smul_left, hg, mul_zero]

private theorem integral_inner_gaugeFixedKernelToLp_gaugeFixedAdjoint_eq_zero
    (hx : Continuous x) (y : gaugeFixedKernel x) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪gaugeFixedKernelToLp x y z, gaugeFixedAdjoint x η z⟫ = 0 := by
  obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 y.2
  have hae : (fun z ↦ ⟪gaugeFixedKernelToLp x y z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
      fun z ↦ ⟪(y : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ :=
    (coeFn_gaugeFixedKernelToLp y).mono fun _ hz ↦ by dsimp only; rw [hz]
  rw [integral_congr_ae hae,
    ← integral_inner_gaugeFixedOperator hx (hyc.of_le one_le_two) hη (.inr hηc)]
  simp [hker]

/-- **Classical kernel elements are weak solutions.** At a continuous field, the `L²` class of a
`C²` square-integrable solution of `L_x y = 0` lies in the weak kernel of `L_x`. -/
theorem gaugeFixedKernelToLp_mem_weakGaugeFixedKernel (hx : Continuous x)
    (y : gaugeFixedKernel x) : gaugeFixedKernelToLp x y ∈ weakGaugeFixedKernel x :=
  (mem_weakGaugeFixedKernel_iff hx).2 fun _ hη hηc ↦
    integral_inner_gaugeFixedKernelToLp_gaugeFixedAdjoint_eq_zero hx y (hη.of_le (by simp)) hηc

/-- **Weak and classical `L²` kernels coincide.** Let `x` be a smooth field whose coordinates have
bounded derivatives of every order. Then every weak `L²` solution of `L_x u = 0` is the `L²`
class of a `C²` square-integrable classical solution: the weak kernel of `L_x` is the image of
its classical kernel `gaugeFixedKernel x`. -/
theorem range_gaugeFixedKernelToLp (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    LinearMap.range (gaugeFixedKernelToLp x) = weakGaugeFixedKernel x := by
  refine le_antisymm ?_ fun u hu ↦ ?_
  · rintro _ ⟨y, rfl⟩
    exact gaugeFixedKernelToLp_mem_weakGaugeFixedKernel hx.continuous y
  -- A weak solution of `L_x u = 0` agrees almost everywhere with a smooth classical solution.
  obtain ⟨y, hy, huy, hyk, hker⟩ := exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq
    hx hbound (Lp.memLp u) (fun k ↦ zero_mem (sobolevFields k)) continuous_const
    fun η hη hηc ↦ by simpa using (mem_weakGaugeFixedKernel_iff hx.continuous).1 hu η hη hηc
  have hyK : y ∈ gaugeFixedKernel x :=
    mem_gaugeFixedKernel.2 ⟨hy.of_le (by simp), by simpa using hyk 0, hker⟩
  exact ⟨⟨y, hyK⟩, Lp.ext ((coeFn_gaugeFixedKernelToLp ⟨y, hyK⟩).trans huy.symm)⟩

/-- **Equivalence of the classical and weak `L²` kernels of `L_x`.** At any smooth field `x` whose
coordinates have bounded derivatives of every order, passing to `L²` classes identifies
`gaugeFixedKernel x` linearly with `weakGaugeFixedKernel x`. -/
def gaugeFixedKernelEquivWeak (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  (LinearEquiv.ofInjective (gaugeFixedKernelToLp x) (gaugeFixedKernelToLp_injective x)).trans
    (LinearEquiv.ofEq _ _ (range_gaugeFixedKernelToLp hx hbound))

/-- Passing from `gaugeFixedKernel x` to `weakGaugeFixedKernel x` via `gaugeFixedKernelEquivWeak`
acts as `gaugeFixedKernelToLp x`. -/
@[simp]
theorem coe_gaugeFixedKernelEquivWeak (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    (gaugeFixedKernelEquivWeak hx hbound y : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) =
      gaugeFixedKernelToLp x y := (rfl)

/-- The `L²` class of `(gaugeFixedKernelEquivWeak hx hbound).symm u` is `u`. -/
@[simp]
theorem gaugeFixedKernelToLp_gaugeFixedKernelEquivWeak_symm (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (u : weakGaugeFixedKernel x) :
    gaugeFixedKernelToLp x ((gaugeFixedKernelEquivWeak hx hbound).symm u) =
      (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) := by
  rw [← coe_gaugeFixedKernelEquivWeak hx hbound, LinearEquiv.apply_symm_apply]

/-- At a smooth field `x` with bounded derivatives of every order, testing against `C^k` compactly
supported fields for any `1 ≤ k ≤ ∞` (in particular `k = 1`, `k = 2`, or `k = ∞`) cuts out the
same weak `L²` kernel. -/
theorem mem_weakGaugeFixedKernel_iff_forall_contDiff {k : ℕ∞ω} (hk : 1 ≤ k) (hk' : k ≤ ∞)
    (hx : ContDiff ℝ ∞ x) (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ k η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  refine ⟨fun hu η hη hηc ↦ ?_, fun hu ↦ (mem_weakGaugeFixedKernel_iff hx.continuous).2
    fun η hη hηc ↦ hu η (hη.of_le hk') hηc⟩
  simpa only [gaugeFixedKernelToLp_gaugeFixedKernelEquivWeak_symm hx hbound ⟨u, hu⟩] using
    integral_inner_gaugeFixedKernelToLp_gaugeFixedAdjoint_eq_zero hx.continuous
      ((gaugeFixedKernelEquivWeak hx hbound).symm ⟨u, hu⟩) (hη.of_le hk) hηc

/-- At a smooth field with bounded derivatives, the weak kernel of `L_x` has the dimension of its
classical kernel. -/
theorem finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    finrank ℝ (weakGaugeFixedKernel x) = finrank ℝ (gaugeFixedKernel x) :=
  (gaugeFixedKernelEquivWeak hx hbound).symm.finrank_eq

/-- **Finite-dimensionality of the weak `L²` kernel.** At a smooth field `x` with bounded
derivatives of every order, `∂bar_a α = 0`, `|α|² → 1` at infinity, and zero divisor `D`, the weak
`L²` kernel `weakGaugeFixedKernel x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel_of_isZeroMultiplicity {D : Multiset ℂ}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) := by
  have : FiniteDimensional ℝ (gaugeFixedKernel x) :=
    finiteDimensional_of_gaugeFixedOperator_eq_zero (hx.of_le (by simp)) hhol hlim hD
      fun _ hy ↦ mem_gaugeFixedKernel.1 hy
  exact (gaugeFixedKernelEquivWeak hx hbound).finiteDimensional

/-- **The weak `L²` kernel of `L_x` has real dimension `2 |D|`.** Let `x` be a smooth field whose
coordinates have bounded derivatives of every order, satisfying the holomorphicity rows
`∂bar_a α = 0` with `|α|² → 1` at infinity and zero divisor `D`. Then `weakGaugeFixedKernel x` has
real dimension `2 |D|`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_card {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * Multiset.card D := by
  rw [finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel hx hbound,
    finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD]

/-- **The weak `L²` kernel of `L_x` at a framed degree-`m` field has real dimension `2m`.** Let
`x` be a smooth field whose coordinates have bounded derivatives of every order, satisfying the
holomorphicity rows `∂bar_a α = 0` and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then
`weakGaugeFixedKernel x` has real dimension `2m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_tendsto {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  rw [finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel hx hbound,
    finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe]

/-! ### The weak kernel at a plane vortex -/

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **The weak kernel at a plane vortex is finite-dimensional.** Let `x` be a continuous field
lying in the affine field space `A_m^k` for every `k` whose section satisfies the holomorphicity
rows `∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`. Then the weak
`L²` kernel of `L_x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace hx hmem
  have := finiteDimensional_gaugeFixedKernel (hxs.of_le (by simp)) hhol
    (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx)
  rw [← range_gaugeFixedKernelToLp hxs
    fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2))]
  infer_instance

/-- **The weak kernel at a plane vortex has dimension `2m`** (Taubes). Let `x` be a continuous
field lying in the affine field space `A_m^k` for every `k` whose section satisfies the
holomorphicity rows `∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`.
Then the weak `L²` kernel of `L_x` has real dimension `2m`, the dimension of the divisor space
`Sym^m ℂ`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace hx hmem
  rw [finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel hxs
      fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)),
    finrank_gaugeFixedKernel_eq_two_mul hxs hhol
      (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx)]

/-- **The kernel of `L_x` at a smooth field in `A_m^s` (`s > 1`) has real dimension `2m`.** Let
`x` be a smooth field in `framedFieldSpace f m s` (`s > 1`) satisfying the holomorphicity rows
`∂bar_a α = 0`. Then `gaugeFixedKernel x` has real dimension `2m`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace {s : ℝ} (hs : 1 < s)
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul hxs hhol
    (tendsto_sectionValue_mul_inv_pow hs hx hxs.continuous)

/-- **Real dimension `2m` of the classical kernel at a Coulomb-gauge vortex.** Let `x ∈ A_m^k`
(`k ≥ 2`) be a `C¹` solution of the vortex equation in Coulomb gauge `d₀*_{x₀}(x - x₀) = 0`
relative to a `C¹` field `x₀` lying in every `A_m^j`. Then `gaugeFixedKernel x` has real dimension
`2m`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero {k : ℕ} (hk : 1 < k)
    {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)} (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j)
    (hx₀c : ContDiff ℝ 1 x₀) (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ z, equation x z = 0) (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace (by exact_mod_cast hk) hx
    (contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge)
    fun w ↦ ⟨by simp [heq w], by simp [heq w]⟩

/-- **Real dimension `2m` of the weak `L²` kernel at a Coulomb-gauge vortex.** Let `x ∈ A_m^k`
(`k ≥ 2`) be a `C¹` solution of the vortex equation in Coulomb gauge `d₀*_{x₀}(x - x₀) = 0`
relative to a `C¹` field `x₀` lying in every `A_m^j`. Then `weakGaugeFixedKernel x` has real
dimension `2m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero {k : ℕ} (hk : 1 < k)
    {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)} (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j)
    (hx₀c : ContDiff ℝ 1 x₀) (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ z, equation x z = 0) (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    finrank ℝ (weakGaugeFixedKernel x) = 2 * m :=
  finrank_weakGaugeFixedKernel_eq_two_mul hxc.continuous
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge)
    fun w ↦ ⟨by simp [heq w], by simp [heq w]⟩

end TauCeti.Vortex
