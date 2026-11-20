/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.KernelDimension
public import TauCeti.Analysis.PDE.Vortex.SobolevScale
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
  is onto (`TauCeti.Vortex.range_gaugeFixedKernelToLp`).

A continuous field lying in the affine field space `A_m^k` for every `k` is such a field, with the
degree-`m` end framing. If its section also satisfies the holomorphicity rows `∂bar_a α = 0`, as
at a plane vortex, its weak `L²` kernel is finite-dimensional of real dimension `2m`
(`TauCeti.Vortex.finiteDimensional_weakGaugeFixedKernel`,
`TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`). This is the kernel in Taubes's
computation of the real index `2m` of the linearized vortex operator. At a plane vortex, a field
satisfying the full vortex equation, the cokernel of that operator also vanishes
(`TauCeti.Vortex.exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq`).

## Main definitions

* `TauCeti.Vortex.weakGaugeFixedKernel x`: the weak `L²` kernel of `L_x`.

## Main results

* `TauCeti.Vortex.mem_weakGaugeFixedKernel_iff`: at a continuous field, the weak kernel consists
  of the weak solutions of `L_x u = 0`.
* `TauCeti.Vortex.range_gaugeFixedKernelToLp`: at a smooth field with bounded derivatives, the
  weak kernel is the space of `L²` classes of the classical kernel.
* `TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`: at a continuous field lying in every
  `A_m^k` and satisfying the holomorphicity rows, for instance a plane vortex, the weak kernel has
  real dimension `2m`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Module
open scoped RealInnerProductSpace ContDiff

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

/-- **Classical kernel elements are weak solutions.** At a continuous field, the `L²` class of a
`C²` square-integrable solution of `L_x y = 0` lies in the weak kernel of `L_x`. -/
theorem gaugeFixedKernelToLp_mem_weakGaugeFixedKernel (hx : Continuous x)
    (y : gaugeFixedKernel x) : gaugeFixedKernelToLp x y ∈ weakGaugeFixedKernel x := by
  obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 y.property
  refine (mem_weakGaugeFixedKernel_iff hx).2 fun η hη hηc ↦ ?_
  have hweak := (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx
    (hyc.of_le one_le_two) continuous_const).2 hker η hη hηc
  rw [← integral_congr_ae ((coeFn_gaugeFixedKernelToLp y).mono fun z hz ↦ by rw [hz]), hweak]
  simp

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

/-- At a smooth field with bounded derivatives, the weak kernel of `L_x` has the dimension of its
classical kernel. -/
theorem finrank_weakGaugeFixedKernel_eq_finrank_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    finrank ℝ (weakGaugeFixedKernel x) = finrank ℝ (gaugeFixedKernel x) := by
  rw [← range_gaugeFixedKernelToLp hx hbound,
    LinearMap.finrank_range_of_inj (gaugeFixedKernelToLp_injective x)]

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

end TauCeti.Vortex
