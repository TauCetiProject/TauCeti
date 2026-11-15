/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import TauCeti.Analysis.PDE.Vortex.Bootstrap
import TauCeti.Analysis.PDE.Vortex.KernelDimension

/-!
# The gauge-fixed vortex operator on the Sobolev scale

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴` with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a weak solution of `L_x y = f` if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for
every smooth compactly supported test field `η`; for `C¹` fields this is the same as a classical
solution (`forall_integral_inner_gaugeFixedAdjoint_eq_iff`). This file compares weak and classical
`L²` solutions, identifies the weak `L²` kernel `weakGaugeFixedKernel x` linearly with the
classical kernel `gaugeFixedKernel x`, and shows that at a plane vortex on the framed Sobolev scale
`A_m^k` the operator `L_x` maps `H^(k+1)` onto `H^k` weakly for every `k` while both its classical
and weak `L²` kernels have real dimension `2 m`.

* `exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq`: at a smooth field `x` whose
  coordinates have bounded derivatives of every order, a weak `L²` solution of `L_x y = f`, with
  `f` continuous and in every `H^k`, agrees almost everywhere with a smooth classical solution
  lying in every `H^k`. Conversely a `C¹`, `L²` classical solution is a weak solution, so it is
  smooth (`contDiff_of_gaugeFixedOperator_eq`), and every element of `gaugeFixedKernel x` lies in
  `sobolevFields s` for every `s : ℝ` (`mem_sobolevFields_of_mem_gaugeFixedKernel`).
* `weakGaugeFixedKernel x` and `gaugeFixedKernelEquivWeak`: the weak `L²` kernel of `L_x` and its
  linear isomorphism with `gaugeFixedKernel x` at any smooth field with bounded derivatives, giving
  exact real dimension `2 |D|` (`finrank_weakGaugeFixedKernel_eq_two_mul_card`) and `2 m`
  (`finrank_weakGaugeFixedKernel_eq_two_mul`).
* `exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields_add_one`:
  at a continuous vortex lying in `A_m^k` for every `k`, the weak right inverse `Q` of `L_x` maps
  `H^k` into `H^(k+1)` for every `k`. This is the vanishing of the cokernel of `L_x` on the
  Sobolev scale.
* `exists_contDiff_gaugeFixedOperator_eq_of_forall_mem_framedFieldSpace`: at such a vortex, every
  continuous field lying in every `H^k` is `L_x y` for a smooth `y` lying in every `H^k`.
* `finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace`,
  `finrank_weakGaugeFixedKernel_eq_two_mul_of_forall_mem_framedFieldSpace`,
  `finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero`, and
  `finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero`: real dimension `2 m` of the
  classical and weak `L²` kernels on the framed Sobolev spaces `A_m^s` and at Coulomb-gauge
  solutions of the vortex equation.

The vortex hypotheses enter through the spectral gap of `L_x*` (`|α| → 1` at infinity), the
elliptic bootstrap (bounded derivatives of `x`), and the principal-part kernel identification
(`∂bar_a α = 0` and degree-`m` framing). A continuous field in every `A_m^k` is smooth with
bounded derivatives (`contDiff_of_forall_mem_framedFieldSpace`,
`exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace`), and `|α| → 1` by the end framing.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff Topology

variable {x y f : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Regularity of weak and classical solutions -/

/-- A square-integrable weak solution of `L_x y = f`, with `f` in every `H^k`, lies in every
`H^k` when `x` is smooth with bounded derivatives: the elliptic bootstrap at every order. -/
private theorem forall_mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq
    (hx : ContDiff ℝ ∞ x) (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) (k : ℕ) :
    y ∈ sobolevFields k := by
  cases k with
  | zero => simpa using hy
  | succ k =>
    exact_mod_cast mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
      (fun i n _ ↦ hbound i n) hy (hf k) hweak

/-- **Weak `L²` solutions are smooth.** Let `x` be a smooth field whose coordinates have bounded
derivatives of every order, and let `y` be a square-integrable weak solution of `L_x y = f`, with
`f` continuous and in every `H^k`. Then `y` agrees almost everywhere with a smooth field lying in
every `H^k` and solving `L_x y = f` everywhere. For `f = 0` this identifies the weak `L²` kernel
of `L_x` with smooth classical solutions of `L_x y = 0`. -/
theorem exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k) (hfc : Continuous f)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∃ y' : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y' ∧ y =ᵐ[volume] y' ∧
      (∀ k : ℕ, y' ∈ sobolevFields k) ∧ ∀ z, gaugeFixedOperator x y' z = f z := by
  have hk := forall_mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq hx hbound hy hf hweak
  obtain ⟨y', hy', hyy'⟩ := exists_contDiff_ae_eq_of_forall_mem_sobolevFields hk
  refine ⟨y', hy', hyy', fun k ↦ mem_sobolevFields_of_ae_eq (hk k) hyy', ?_⟩
  refine (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx.continuous
    (hy'.of_le (by exact_mod_cast le_top)) hfc).1 fun η hη hηc ↦ ?_
  rw [← hweak η hη hηc]
  exact integral_congr_ae (hyy'.mono fun z hz ↦ by simp only [hz])

/-- **Classical `L²` solutions are smooth.** Let `x` be a smooth field whose coordinates have
bounded derivatives of every order. A square-integrable `C¹` solution of `L_x y = f`, with `f` in
every `H^k`, is smooth. In particular every `C¹` element of the `L²` kernel of `L_x` is
smooth. -/
theorem contDiff_of_gaugeFixedOperator_eq (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : ContDiff ℝ 1 y) (hyL : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k)
    (heq : ∀ z, gaugeFixedOperator x y z = f z) : ContDiff ℝ ∞ y := by
  have hfc : Continuous f := funext heq ▸ continuous_gaugeFixedOperator hx.continuous hy
  obtain ⟨y', hy', hyy', -⟩ := exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq hx
    hbound hyL hf hfc ((forall_integral_inner_gaugeFixedAdjoint_eq_iff hx.continuous hy hfc).2 heq)
  rwa [(hy.continuous.ae_eq_iff_eq volume hy'.continuous).1 hyy']

/-- At a smooth field `x` whose coordinates have bounded derivatives of every order, every element
of `gaugeFixedKernel x` lies in `sobolevFields s` for every `s : ℝ`. -/
theorem mem_sobolevFields_of_mem_gaugeFixedKernel (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : y ∈ gaugeFixedKernel x) (s : ℝ) :
    y ∈ sobolevFields s := by
  obtain ⟨hyc, hyL, hker⟩ := mem_gaugeFixedKernel.1 hy
  refine sobolevFields_mono (Nat.le_ceil s)
    (forall_mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq hx hbound hyL
      (f := 0) (fun _ ↦ zero_mem _) ?_ ⌈s⌉₊)
  simpa using (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx.continuous
    (hyc.of_le one_le_two) continuous_const).2 hker

/-! ### The weak `L²` kernel and its dimension -/

/-- The weak `L²` kernel of the gauge-fixed operator `L_x`: those `u ∈ L²(ℂ; ℝ⁴)` whose pairing
with `L_x* η` is integrable and has zero integral for every smooth compactly supported test field
`η`. When `x` is continuous, `L_x* η` is continuous with compact support so the integrability
condition is automatic (`mem_weakGaugeFixedKernel_iff`). -/
def weakGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) where
  carrier := {u | ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
    Integrable (fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫) volume ∧
      ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0}
  add_mem' {u v} hu hv η hη hηc := by
    have hae : (fun z ↦ ⟪(u + v : Lp _ 2 _) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
        fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫ + ⟪v z, gaugeFixedAdjoint x η z⟫ :=
      (Lp.coeFn_add u v).mono fun z hz ↦ by dsimp only; rw [hz, Pi.add_apply, inner_add_left]
    refine ⟨((hu η hη hηc).1.add (hv η hη hηc).1).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_add (hu η hη hηc).1 (hv η hη hηc).1,
      (hu η hη hηc).2, (hv η hη hηc).2, add_zero]
  zero_mem' η _ _ := by
    have hae : (fun z ↦ ⟪(0 : Lp _ 2 _) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume] fun _ ↦ 0 :=
      (Lp.coeFn_zero _ 2 _).mono fun z hz ↦ by dsimp only; rw [hz, Pi.zero_apply, inner_zero_left]
    exact ⟨(integrable_zero _ _ _).congr hae.symm,
      (integral_congr_ae hae).trans (integral_zero _ _)⟩
  smul_mem' c {u} hu η hη hηc := by
    have hae : (fun z ↦ ⟪(c • u : Lp _ 2 _) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
        fun z ↦ c * ⟪u z, gaugeFixedAdjoint x η z⟫ :=
      (Lp.coeFn_smul c u).mono fun z hz ↦ by simp [hz, inner_smul_left]
    refine ⟨((hu η hη hηc).1.const_mul c).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_const_mul, (hu η hη hηc).2, mul_zero]

/-- Membership in `weakGaugeFixedKernel x` unfolds to integrability and vanishing integral against
`L_x* η` for every smooth compactly supported test field `η`. -/
@[simp]
theorem mem_weakGaugeFixedKernel {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        Integrable (fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫) volume ∧
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 :=
  Iff.rfl

/-- For a continuous field `x`, `u ∈ L²` lies in `weakGaugeFixedKernel x` if and only if
`∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly supported test field `η`. -/
theorem mem_weakGaugeFixedKernel_iff (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  refine ⟨fun hu η hη hηc ↦ (hu η hη hηc).2, fun hu η hη hηc ↦ ⟨?_, hu η hη hηc⟩⟩
  have hL : MemLp (gaugeFixedAdjoint x η) 2 volume :=
    (continuous_gaugeFixedAdjoint hx (hη.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  exact (Lp.memLp u).integrable_inner hL

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

/-- For a continuous field `x`, the `L²` class of every classical kernel element lies in the weak
`L²` kernel. -/
theorem gaugeFixedKernelToLp_mem_weakGaugeFixedKernel (hx : Continuous x)
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelToLp x y ∈ weakGaugeFixedKernel x :=
  (mem_weakGaugeFixedKernel_iff hx).2 fun _ hη hηc ↦
    integral_inner_gaugeFixedKernelToLp_gaugeFixedAdjoint_eq_zero hx y (hη.of_le (by simp)) hηc

/-- **Equivalence of the classical and weak `L²` kernels of `L_x`.** At any smooth field `x` whose
coordinates have bounded derivatives of all orders, passing to `L²` classes identifies
`gaugeFixedKernel x` linearly with `weakGaugeFixedKernel x`. -/
noncomputable def gaugeFixedKernelEquivWeak (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  LinearEquiv.ofBijective
    ((gaugeFixedKernelToLp x).codRestrict (weakGaugeFixedKernel x)
      (gaugeFixedKernelToLp_mem_weakGaugeFixedKernel hx.continuous))
    ⟨fun y₁ y₂ h ↦ gaugeFixedKernelToLp_injective x (congrArg Subtype.val h), fun ⟨u, hu⟩ ↦ by
      obtain ⟨y', hy', huy', hy'k, hker⟩ :=
        exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq hx hbound (Lp.memLp u)
          (f := 0) (fun _ ↦ zero_mem _) continuous_const fun η hη hηc ↦ by
            simpa using (hu η hη hηc).2
      have hy'K : y' ∈ gaugeFixedKernel x :=
        mem_gaugeFixedKernel.2 ⟨hy'.of_le (by simp), memLp_of_mem_sobolevFields (hy'k 0), hker⟩
      refine ⟨⟨y', hy'K⟩, Subtype.ext (Lp.ext_iff.2 ?_)⟩
      exact (coeFn_gaugeFixedKernelToLp ⟨y', hy'K⟩).trans huy'.symm⟩

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

/-- At a smooth field `x` with bounded derivatives of all orders, testing against `C^k` compactly
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

/-- **Finite-dimensionality of the weak `L²` kernel.** At a smooth field `x` with bounded
derivatives of all orders, `∂bar_a α = 0`, `|α|² → 1` at infinity, and zero divisor `D`, the weak
`L²` kernel `weakGaugeFixedKernel x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
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
coordinates have bounded derivatives of all orders, satisfying the holomorphicity rows
`∂bar_a α = 0` with `|α|² → 1` at infinity and zero divisor `D`. Then `weakGaugeFixedKernel x` has
real dimension `2 |D|`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_card {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * Multiset.card D :=
  (gaugeFixedKernelEquivWeak hx hbound).symm.finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD)

/-- **The weak `L²` kernel of `L_x` at a framed degree-`m` field has real dimension `2 m`.** Let `x`
be a smooth field whose coordinates have bounded derivatives of all orders, satisfying the
holomorphicity rows `∂bar_a α = 0` and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then
`weakGaugeFixedKernel x` has real dimension `2 m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m :=
  (gaugeFixedKernelEquivWeak hx hbound).symm.finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe)

/-! ### Surjectivity and kernel dimension at a vortex -/

variable {ρ : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **The right inverse on the Sobolev scale.** Let `x` be a continuous solution of the plane
vortex equations lying in the affine field space `A_m^k` for every `k`. Then there is a bounded
operator `Q` on `L²(ℂ; ℝ⁴)` such that

* `Q f` is a weak solution of `L_x y = f` for every `f ∈ L²`;
* `Q f` is orthogonal to the weak kernel of `L_x`;
* `Q` maps `H^k` into `H^(k+1)` for every `k`.

In particular `L_x : H^(k+1) → H^k` is surjective in the weak sense for every `k`: the cokernel of
`L_x` vanishes on the Sobolev scale. This extends to every `k` the case `k = 0`,
`exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields_add_one
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k)
    (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) ∧
      (∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q f z, u z⟫ = 0) ∧
      ∀ (k : ℕ) (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume),
        (f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields k →
          (Q f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) := by
  have hxs := contDiff_of_forall_mem_framedFieldSpace hx hmem
  have hlim := tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) (hxs.of_le (by exact_mod_cast le_top)) hsol hlim
  refine ⟨Q, hQ, hQK, fun k f hf ↦ ?_⟩
  exact mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hxs
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    (Lp.memLp _) hf fun η hη hηc ↦ hQ f η (hη.of_le (by norm_cast)) hηc

/-- **Classical surjectivity at a vortex.** Let `x` be a continuous solution of the plane vortex
equations lying in the affine field space `A_m^k` for every `k`. Every continuous field `f` lying
in every `H^k` is `L_x y` for a smooth field `y` lying in every `H^k`. -/
theorem exists_contDiff_gaugeFixedOperator_eq_of_forall_mem_framedFieldSpace (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k) (hsol : ∀ z, equation x z = 0)
    (hf : ∀ k : ℕ, f ∈ sobolevFields k) (hfc : Continuous f) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ (∀ k : ℕ, y ∈ sobolevFields k) ∧
      ∀ z, gaugeFixedOperator x y z = f z := by
  obtain ⟨Q, hQ, -⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields_add_one
      hx hmem hsol
  have hfL : MemLp f 2 volume := by simpa using hf 0
  obtain ⟨y, hy, -, hyk, heq⟩ := exists_contDiff_ae_eq_of_integral_inner_gaugeFixedAdjoint_eq
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    (Lp.memLp (Q (hfL.toLp f))) hf hfc fun η hη hηc ↦ by
      rw [hQ _ η (hη.of_le (by norm_cast)) hηc]
      exact integral_congr_ae (hfL.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
  exact ⟨y, hy, hyk, heq⟩

/-- **The kernel of `L_x` at a smooth field in `A_m^s` (`s > 1`) has real dimension `2 m`.** Let `x`
be a smooth field in `framedFieldSpace ρ m s` (`s > 1`) satisfying the holomorphicity rows
`∂bar_a α = 0`. Then `gaugeFixedKernel x` has real dimension `2 m`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace {s : ℝ} (hs : 1 < s)
    (hx : x ∈ framedFieldSpace ρ m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul hxs hhol
    (tendsto_sectionValue_mul_inv_pow hs hx hxs.continuous)

/-- **The weak `L²` kernel of `L_x` at a field in every `A_m^k` has real dimension `2 m`.** Let `x`
be a continuous field lying in `framedFieldSpace ρ m k` for every `k : ℕ` and satisfying the
holomorphicity rows `∂bar_a α = 0`. Then `weakGaugeFixedKernel x` has real dimension `2 m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m :=
  finrank_weakGaugeFixedKernel_eq_two_mul (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    hhol (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx)

/-- **Real dimension `2 m` of the classical kernel at a Coulomb-gauge vortex.** Let `x ∈ A_m^k`
(`k ≥ 2`) be a `C¹` solution of the vortex equation in Coulomb gauge `d₀*_{x₀}(x - x₀) = 0`
relative to a `C¹` field `x₀` lying in every `A_m^j`. Then `gaugeFixedKernel x` has real dimension
`2 m`. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero {k : ℕ} (hk : 1 < k)
    {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)} (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace ρ m j)
    (hx₀c : ContDiff ℝ 1 x₀) (hx : x ∈ framedFieldSpace ρ m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ z, equation x z = 0) (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace (by exact_mod_cast hk) hx
    (contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge)
    fun w ↦ ⟨by simp [heq w], by simp [heq w]⟩

/-- **Real dimension `2 m` of the weak `L²` kernel at a Coulomb-gauge vortex.** Let `x ∈ A_m^k`
(`k ≥ 2`) be a `C¹` solution of the vortex equation in Coulomb gauge `d₀*_{x₀}(x - x₀) = 0`
relative to a `C¹` field `x₀` lying in every `A_m^j`. Then `weakGaugeFixedKernel x` has real
dimension `2 m`. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero {k : ℕ} (hk : 1 < k)
    {x₀ : ℂ → EuclideanSpace ℝ (Fin 4)} (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace ρ m j)
    (hx₀c : ContDiff ℝ 1 x₀) (hx : x ∈ framedFieldSpace ρ m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ z, equation x z = 0) (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m :=
  finrank_weakGaugeFixedKernel_eq_two_mul_of_forall_mem_framedFieldSpace hxc.continuous
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge)
    fun w ↦ ⟨by simp [heq w], by simp [heq w]⟩

end TauCeti.Vortex
