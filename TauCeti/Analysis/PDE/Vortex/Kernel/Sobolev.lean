/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.PDE.Vortex.Bootstrap

/-!
# Sobolev regularity and weak-classical equivalence for the vortex kernel

At a smooth plane vortex `x`, the gauge-fixed linearization `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) acts classically on `C²` square-integrable fields with kernel
`TauCeti.Vortex.gaugeFixedKernel`, and weakly on `L²(ℂ; ℝ⁴)` by pairing against its formal adjoint
`L_x*` (`TauCeti.Vortex.gaugeFixedAdjoint`) on compactly supported test fields. The right-inverse
construction in `TauCeti.Analysis.PDE.Vortex.RightInverse` splits `L²` orthogonally to this weak
kernel, while the principal-part isomorphism in `TauCeti.Analysis.PDE.Vortex.Kernel.Dimension`
computes the dimension of the classical kernel. This file identifies the weak and classical kernels
and shows that the kernel of `L_x` is independent of the Sobolev scale `H^s(ℂ; ℝ⁴)` and has real
dimension `2m` at every framed degree-`m` vortex.

**From weak to classical solutions.** For a continuous background `x` and a `C¹` variation `y`,
integration by parts against compactly supported test fields shows that `L_x y` vanishes as a
distribution whenever `∫ ⟪y, L_x* η⟫ = 0` for all smooth compactly supported `η`. By the
fundamental lemma of the calculus of variations (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`)
and continuity of `L_x y`, it follows that `L_x y = 0` everywhere
(`TauCeti.Vortex.gaugeFixedOperator_eq_zero_of_integral_inner_gaugeFixedAdjoint_eq_zero`).

**Weak-classical equivalence.** When `x` is smooth with bounded derivatives through order `3`, the
elliptic bootstrap
(`TauCeti.Vortex.mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`)
places every element `u` of the weak `L²` kernel `TauCeti.Vortex.gaugeFixedWeakKernel` in `H⁴`.
Sobolev embedding (`2 + 1 < 4`) produces a `C²` representative `y` of `u`, which then solves
`L_x y = 0` classically. Thus the natural inclusion `TauCeti.Vortex.toGaugeFixedWeakKernel` is a
real-linear equivalence (`TauCeti.Vortex.gaugeFixedKernelWeakEquiv`), and testing against `C_c^∞`
fields is equivalent to testing against `C_c^n` fields for any `1 ≤ n ≤ ∞`
(`TauCeti.Vortex.mem_gaugeFixedWeakKernel_iff_forall_contDiff`).

**Scale invariance and framed vortices.** When all derivatives of `x` are bounded, iterating the
bootstrap shows that every kernel element lies in `sobolevFields s` for all `s : ℝ` and has
iterated derivatives vanishing at infinity, so the Sobolev kernel does not depend on `s`
(`TauCeti.Vortex.mem_gaugeFixedKernel_iff_mem_sobolevFields`). Combining these results with the
nonlinear Coulomb-slice bootstrap (`TauCeti.Analysis.PDE.Vortex.Bootstrap`) shows that at any `C¹`
solution `x ∈ A_m^k` (`k ≥ 2`) of the vortex equation in the Coulomb slice, both the classical and
weak kernels of `L_x` have real dimension `2m`.

## Main definitions and results

All declarations are in the `TauCeti.Vortex` namespace:

* `gaugeFixedWeakKernel`: the closed `L²` subspace of weak solutions of `L_x u = 0`.
* `toGaugeFixedWeakKernel`, `gaugeFixedKernelWeakEquiv`: the inclusion of `gaugeFixedKernel x` into
  `gaugeFixedWeakKernel hx` and its promotion to a linear equivalence when `x` has bounded
  derivatives through order `3`.
* `mem_gaugeFixedWeakKernel_iff_forall_contDiff`: equivalence of weak-kernel membership against
  `C_c^∞` and `C_c^n` (`1 ≤ n ≤ ∞`) test fields.
* `finrank_gaugeFixedWeakKernel_eq_two_mul_card`, `finrank_gaugeFixedWeakKernel`: the weak `L²`
  kernel has real dimension `2 |D|`, and `2m` under degree-`m` end framing.
* `mem_sobolevFields_of_mem_gaugeFixedKernel`, `mem_gaugeFixedKernel_iff_mem_sobolevFields`:
  every kernel element lies in `H^s` for all `s : ℝ`, so the kernel is independent of `s`.
* `finrank_gaugeFixedKernel_of_mem_framedFieldSpace`,
  `finrank_gaugeFixedWeakKernel_of_mem_framedFieldSpace`: dimension `2m` on `A_m^s`.
* `finrank_gaugeFixedKernel_of_equation_eq_zero`,
  `finrank_gaugeFixedWeakKernel_of_equation_eq_zero`: dimension `2m` at any `C¹` vortex in `A_m^k`
  (`k ≥ 2`) on a Coulomb slice.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179, §3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory
open scoped ContDiff RealInnerProductSpace Topology

/-! ### Classical solutions from weak solutions and the weak `L²` kernel -/

/-- **Classical solutions from weak solutions.** Let `x` be a continuous field and `y` be a `C¹`
field on the plane. If `∫ ⟪y, L_x* η⟫ = 0` for every smooth compactly supported test field `η`,
then `L_x y = 0` pointwise everywhere. -/
theorem gaugeFixedOperator_eq_zero_of_integral_inner_gaugeFixedAdjoint_eq_zero
    {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (hy : ContDiff ℝ 1 y)
    (h : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) (z : ℂ) :
    gaugeFixedOperator x y z = 0 := by
  have hcont : Continuous (gaugeFixedOperator x y) := continuous_gaugeFixedOperator hx hy
  have hcoord (i : Fin 4) : ∀ᵐ w ∂μ, gaugeFixedOperator x y w i = 0 := by
    let e : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single i 1
    have hf : Continuous fun w ↦ gaugeFixedOperator x y w i :=
      (EuclideanSpace.proj i).continuous.comp hcont
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable fun g hg hgc ↦ ?_
    let η : ℂ → EuclideanSpace ℝ (Fin 4) := fun w ↦ g w • e
    have hη : ContDiff ℝ ∞ η := hg.smul contDiff_const
    have hηc : HasCompactSupport η := hgc.smul_right
    have hpair (w : ℂ) : g w • gaugeFixedOperator x y w i = ⟪gaugeFixedOperator x y w, η w⟫ := by
      simp [η, e, PiLp.inner_apply, PiLp.single_apply]
    simp_rw [hpair]
    rw [integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx hy (hη.of_le (by simp)) hηc]
    exact h η hη hηc
  have hae : gaugeFixedOperator x y =ᵐ[μ] 0 := by
    filter_upwards [ae_all_iff.2 hcoord] with w hw
    ext i
    exact hw i
  exact congrFun ((hcont.ae_eq_iff_eq μ continuous_const).1 hae) z

private theorem memLp_gaugeFixedAdjoint_of_contDiff {x η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    MemLp (gaugeFixedAdjoint x η) 2 (volume : Measure ℂ) :=
  (continuous_gaugeFixedAdjoint hx hη).memLp_of_hasCompactSupport
    (hasCompactSupport_gaugeFixedAdjoint hηc)

/-- The weak `L²` kernel of the gauge-fixed vortex operator `L_x`: the subspace of `L²(ℂ; ℝ⁴)`
consisting of fields `u` that satisfy `∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly supported
test field `η`. -/
def gaugeFixedWeakKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) where
  carrier := {u | ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
    ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0}
  add_mem' {u v} hu hv η hη hηc := by
    have hm := memLp_gaugeFixedAdjoint_of_contDiff hx (hη.of_le (by simp)) hηc
    rw [← L2.inner_toLp (u + v) hm, inner_add_left, L2.inner_toLp u hm, L2.inner_toLp v hm,
      hu η hη hηc, hv η hη hηc, add_zero]
  zero_mem' η hη hηc := by
    have hm := memLp_gaugeFixedAdjoint_of_contDiff hx (hη.of_le (by simp)) hηc
    rw [← L2.inner_toLp 0 hm, inner_zero_left]
  smul_mem' c u hu η hη hηc := by
    have hm := memLp_gaugeFixedAdjoint_of_contDiff hx (hη.of_le (by simp)) hηc
    rw [← L2.inner_toLp (c • u) hm, real_inner_smul_left, L2.inner_toLp u hm, hu η hη hηc,
      mul_zero]

@[simp]
theorem mem_gaugeFixedWeakKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)} {hx : Continuous x}
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ gaugeFixedWeakKernel hx ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 :=
  Iff.rfl

/-- The weak `L²` kernel `gaugeFixedWeakKernel hx` is a closed subspace of `L²(ℂ; ℝ⁴)`. -/
theorem isClosed_gaugeFixedWeakKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) :
    IsClosed (gaugeFixedWeakKernel hx :
      Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ))) := by
  have heq : (gaugeFixedWeakKernel hx : Set _) =
      ⋂ (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η),
        {u | ⟪u, (memLp_gaugeFixedAdjoint_of_contDiff hx (hη.of_le (by simp)) hηc).toLp
          (gaugeFixedAdjoint x η)⟫ = 0} := by
    ext u
    simp only [SetLike.mem_coe, mem_gaugeFixedWeakKernel, Set.mem_iInter, Set.mem_ofPred_eq]
    refine forall₃_congr fun η hη hηc ↦ ?_
    rw [L2.inner_toLp]
  rw [heq]
  exact isClosed_iInter fun η ↦ isClosed_iInter fun hη ↦ isClosed_iInter fun hηc ↦
    isClosed_eq (continuous_id.inner continuous_const) continuous_const

/-- Inclusion of the classical `C²` square-integrable kernel `gaugeFixedKernel x` into the weak
`L²` kernel `gaugeFixedWeakKernel hx`, sending a classical kernel element to its `L²` class. -/
def toGaugeFixedWeakKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) :
    gaugeFixedKernel x →ₗ[ℝ] gaugeFixedWeakKernel hx where
  toFun y := ⟨(mem_gaugeFixedKernel.1 y.2).2.1.toLp y, fun η hη hηc ↦ by
    obtain ⟨hy, hy₂, hyk⟩ := mem_gaugeFixedKernel.1 y.2
    have hcongr : ∫ z, ⟪(hy₂.toLp (y : ℂ → EuclideanSpace ℝ (Fin 4))) z,
        gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪(y : ℂ → EuclideanSpace ℝ (Fin 4)) z,
          gaugeFixedAdjoint x η z⟫ :=
      integral_congr_ae (hy₂.coeFn_toLp.mono fun z hz ↦ by dsimp only; rw [hz])
    rw [hcongr, ← integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx
      (hy.of_le (by simp)) (hη.of_le (by simp)) hηc]
    simp [hyk]⟩
  map_add' y₁ y₂ := Subtype.ext <| by
    simpa using (mem_gaugeFixedKernel.1 y₁.2).2.1.toLp_add (mem_gaugeFixedKernel.1 y₂.2).2.1
  map_smul' c y := Subtype.ext <| by
    simpa using (mem_gaugeFixedKernel.1 y.2).2.1.toLp_const_smul c

/-- The `L²` class `toGaugeFixedWeakKernel hx y` agrees almost everywhere with `y`. -/
theorem coeFn_toGaugeFixedWeakKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x)
    (y : gaugeFixedKernel x) :
    ((toGaugeFixedWeakKernel hx y :
      Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) : ℂ → EuclideanSpace ℝ (Fin 4))
      =ᵐ[volume] (y : ℂ → EuclideanSpace ℝ (Fin 4)) :=
  (mem_gaugeFixedKernel.1 y.2).2.1.coeFn_toLp

/-- The inclusion of the classical kernel into the weak `L²` kernel is injective. -/
theorem toGaugeFixedWeakKernel_injective {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) :
    Function.Injective (toGaugeFixedWeakKernel hx) := by
  intro y₁ y₂ h
  have hae : (y₁ : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] (y₂ : ℂ → EuclideanSpace ℝ (Fin 4)) :=
    (coeFn_toGaugeFixedWeakKernel hx y₁).symm.trans
      (by rw [congrArg Subtype.val h]; exact coeFn_toGaugeFixedWeakKernel hx y₂)
  exact Subtype.ext (((mem_gaugeFixedKernel.1 y₁.2).1.continuous.ae_eq_iff_eq volume
    (mem_gaugeFixedKernel.1 y₂.2).1.continuous).1 hae)

/-! ### Elliptic regularity and weak-classical equivalence -/

/-- **Bootstrap regularity for the weak kernel.** When `x` is smooth with bounded derivatives
through order `k`, every element of `gaugeFixedWeakKernel hx.continuous` lies in
`sobolevFields (k + 1)`. -/
theorem coeFn_mem_sobolevFields_of_mem_gaugeFixedWeakKernel {k : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hu : u ∈ gaugeFixedWeakKernel hx.continuous) :
    (u : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx hbound
    (Lp.memLp u) (zero_mem _) fun η hη hηc ↦ by simp [mem_gaugeFixedWeakKernel.1 hu η hη hηc]

/-- **Bootstrap regularity for classical solutions.** When `x` is smooth with bounded derivatives
through order `k`, every `C¹` square-integrable solution of `L_x y = 0` lies in
`sobolevFields (k + 1)`. -/
theorem mem_sobolevFields_natCast_add_one_of_gaugeFixedOperator_eq_zero {k : ℕ}
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : ContDiff ℝ 1 y) (hy₂ : MemLp y 2 volume) (hyk : ∀ z, gaugeFixedOperator x y z = 0) :
    y ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx hbound hy₂
    (zero_mem _) fun η hη hηc ↦ by
      rw [← integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx.continuous hy
        (hη.of_le (by simp)) hηc]
      simp [hyk]

/-- **Every weak kernel element has a unique classical representative.** When `x` is smooth with
bounded derivatives through order `3`, every `u ∈ gaugeFixedWeakKernel hx.continuous` agrees almost
everywhere with a unique `y ∈ gaugeFixedKernel x`. -/
theorem existsUnique_mem_gaugeFixedKernel_ae_eq {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)}
    (hu : u ∈ gaugeFixedWeakKernel hx.continuous) :
    ∃! y, y ∈ gaugeFixedKernel x ∧ (u : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] y := by
  have hus : (u : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields ((3 : ℕ) + 1) :=
    coeFn_mem_sobolevFields_of_mem_gaugeFixedWeakKernel hx hbound hu
  obtain ⟨y, hy, huy⟩ := exists_contDiff_ae_eq_of_mem_sobolevFields (k := 2) (by norm_num) hus
  have hyk : ∀ z, gaugeFixedOperator x y z = 0 :=
    gaugeFixedOperator_eq_zero_of_integral_inner_gaugeFixedAdjoint_eq_zero (μ := volume)
      hx.continuous (hy.of_le (by simp)) fun η hη hηc ↦ by
        have hcongr : ∫ z, ⟪(u : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ =
            ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
          integral_congr_ae (huy.mono fun z hz ↦ by dsimp only; rw [hz])
        rw [← hcongr]
        exact mem_gaugeFixedWeakKernel.1 hu η hη hηc
  refine ⟨y, ⟨mem_gaugeFixedKernel.2 ⟨hy, (Lp.memLp u).ae_eq huy, hyk⟩, huy⟩, ?_⟩
  rintro y' ⟨hy', huy'⟩
  exact ((mem_gaugeFixedKernel.1 hy').1.continuous.ae_eq_iff_eq volume hy.continuous).1
    (huy'.symm.trans huy)

private theorem toGaugeFixedWeakKernel_bijective {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    Function.Bijective (toGaugeFixedWeakKernel hx.continuous) := by
  refine ⟨toGaugeFixedWeakKernel_injective hx.continuous, fun u ↦ ?_⟩
  obtain ⟨y, ⟨hy, huy⟩, -⟩ := existsUnique_mem_gaugeFixedKernel_ae_eq hx hbound u.2
  refine ⟨⟨y, hy⟩, Subtype.ext (Lp.ext ?_)⟩
  exact (coeFn_toGaugeFixedWeakKernel hx.continuous ⟨y, hy⟩).trans huy.symm

/-- **Equivalence between the classical and weak kernels of `L_x`.** When `x` is smooth with
bounded derivatives through order `3`, the inclusion `toGaugeFixedWeakKernel` is a real-linear
equivalence `gaugeFixedKernel x ≃ₗ[ℝ] gaugeFixedWeakKernel hx.continuous`. -/
def gaugeFixedKernelWeakEquiv {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    gaugeFixedKernel x ≃ₗ[ℝ] gaugeFixedWeakKernel hx.continuous :=
  LinearEquiv.ofBijective (toGaugeFixedWeakKernel hx.continuous)
    (toGaugeFixedWeakKernel_bijective hx hbound)

@[simp]
theorem gaugeFixedKernelWeakEquiv_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelWeakEquiv hx hbound y = toGaugeFixedWeakKernel hx.continuous y := by
  rw [gaugeFixedKernelWeakEquiv, LinearEquiv.ofBijective_apply]

/-- **Test-field regularity invariance of the weak kernel.** When `x` is smooth with bounded
derivatives through order `3`, membership in `gaugeFixedWeakKernel hx.continuous` (defined against
`C_c^∞` test fields) is equivalent to vanishing against all compactly supported `C^n` test fields
for any `1 ≤ n ≤ ∞`, including the `C_c^2` test fields used in `RightInverse`. -/
theorem mem_gaugeFixedWeakKernel_iff_forall_contDiff {n : WithTop ℕ∞} (hn : 1 ≤ n) (hn' : n ≤ ∞)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ m ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ m (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ gaugeFixedWeakKernel hx.continuous ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ n η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  refine ⟨fun hu η hη hηc ↦ ?_, fun h ↦ mem_gaugeFixedWeakKernel.2 fun η hη hηc ↦
    h η (hη.of_le hn') hηc⟩
  obtain ⟨y, ⟨hy, huy⟩, -⟩ := existsUnique_mem_gaugeFixedKernel_ae_eq hx hbound hu
  obtain ⟨hyc, -, hyk⟩ := mem_gaugeFixedKernel.1 hy
  have hcongr : ∫ z, ⟪(u : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ =
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
    integral_congr_ae (huy.mono fun z hz ↦ by dsimp only; rw [hz])
  rw [hcongr, ← integral_inner_gaugeFixedOperator_of_hasCompactSupport_right hx.continuous
    (hyc.of_le (by simp)) (hη.of_le hn) hηc]
  simp [hyk]

/-- **The weak `L²` kernel of `L_x` is finite dimensional.** At a smooth field `x` with bounded
derivatives through order `3`, vanishing holomorphicity rows, and `|α|² → 1` at infinity,
`gaugeFixedWeakKernel hx.continuous` is finite dimensional. -/
theorem finiteDimensional_gaugeFixedWeakKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    FiniteDimensional ℝ (gaugeFixedWeakKernel hx.continuous) := by
  have := finiteDimensional_gaugeFixedKernel_of_tendsto_normSq (hx.of_le (by simp)) hhol hlim
  exact (gaugeFixedKernelWeakEquiv hx hbound).finiteDimensional

/-- **The weak `L²` kernel of `L_x` has real dimension `2 |D|`.** At a smooth field `x` with
bounded derivatives through order `3`, vanishing holomorphicity rows, `|α|² → 1` at infinity, and
zero divisor `D`, the weak kernel `gaugeFixedWeakKernel hx.continuous` has real dimension
`2 |D|`. -/
theorem finrank_gaugeFixedWeakKernel_eq_two_mul_card {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (gaugeFixedWeakKernel hx.continuous) = 2 * Multiset.card D := by
  rw [← (gaugeFixedKernelWeakEquiv hx hbound).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD]

/-- **The weak `L²` kernel at a framed degree-`m` vortex has real dimension `2m`.** Let `x` be a
smooth field with bounded derivatives through order `3`, satisfying `∂bar_a α = 0` and the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then `gaugeFixedWeakKernel hx.continuous` has real
dimension `2m`. -/
theorem finrank_gaugeFixedWeakKernel {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (gaugeFixedWeakKernel hx.continuous) = 2 * m := by
  rw [← (gaugeFixedKernelWeakEquiv hx hbound).finrank_eq, finrank_gaugeFixedKernel hx hhol hframe]

/-! ### Independence of the Sobolev scale -/

/-- **Kernel elements lie in every Sobolev space.** When `x` is smooth with bounded derivatives of
all orders, every element of `gaugeFixedKernel x` lies in `sobolevFields s` for every `s : ℝ`. -/
theorem mem_sobolevFields_of_mem_gaugeFixedKernel {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : y ∈ gaugeFixedKernel x) (s : ℝ) :
    y ∈ sobolevFields s := by
  obtain ⟨hyc, hy₂, hyk⟩ := mem_gaugeFixedKernel.1 hy
  let k : ℕ := ⌈s⌉₊
  have hk : y ∈ sobolevFields ((k : ℝ) + 1) :=
    mem_sobolevFields_natCast_add_one_of_gaugeFixedOperator_eq_zero hx
      (fun i n _ ↦ hbound i n) (hyc.of_le (by simp)) hy₂ hyk
  exact sobolevFields_mono (by linarith [Nat.le_ceil s]) hk

/-- **Iterated derivatives of kernel elements vanish at infinity.** When `x` is smooth with bounded
derivatives of all orders, every iterated derivative of each coordinate of `y ∈ gaugeFixedKernel x`
tends to zero at infinity. -/
theorem tendsto_iteratedFDeriv_cocompact_of_mem_gaugeFixedKernel_apply
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : y ∈ gaugeFixedKernel x) (j : ℕ) (i : Fin 4) :
    Tendsto (iteratedFDeriv ℝ j fun z ↦ y z i) (cocompact ℂ) (𝓝 0) :=
  tendsto_iteratedFDeriv_cocompact_of_mem_sobolevFields_apply (s := (j : ℝ) + 2) (by linarith)
    (mem_sobolevFields_of_mem_gaugeFixedKernel hx hbound hy ((j : ℝ) + 2))
    (mem_gaugeFixedKernel.1 hy).1.continuous i

/-- **Sobolev scale invariance of `gaugeFixedKernel x`.** When `x` is smooth with bounded
derivatives of all orders, a `C¹` field solving `L_x y = 0` belongs to `gaugeFixedKernel x` if and
only if it belongs to `sobolevFields s`, independently of the Sobolev exponent `s : ℝ`. -/
theorem mem_gaugeFixedKernel_iff_mem_sobolevFields {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) (s : ℝ) :
    y ∈ gaugeFixedKernel x ↔
      ContDiff ℝ 1 y ∧ y ∈ sobolevFields s ∧ ∀ z, gaugeFixedOperator x y z = 0 := by
  refine ⟨fun hy ↦ ⟨(mem_gaugeFixedKernel.1 hy).1.of_le (by simp),
    mem_sobolevFields_of_mem_gaugeFixedKernel hx hbound hy s, (mem_gaugeFixedKernel.1 hy).2.2⟩, ?_⟩
  rintro ⟨hy₁, hys, hyk⟩
  have hy₂ : MemLp y 2 volume := memLp_of_mem_sobolevFields hys
  have hy₄ : y ∈ sobolevFields ((3 : ℕ) + 1) :=
    mem_sobolevFields_natCast_add_one_of_gaugeFixedOperator_eq_zero hx
      (fun i n _ ↦ hbound i n) hy₁ hy₂ hyk
  exact mem_gaugeFixedKernel.2
    ⟨contDiff_of_mem_sobolevFields (k := 2) (by norm_num) hy₄ hy₁.continuous, hy₂, hyk⟩

/-- For `s > 2`, Sobolev embedding supplies `C¹` regularity automatically, so `gaugeFixedKernel x`
consists precisely of the continuous `H^s` fields solving `L_x y = 0`. -/
theorem mem_gaugeFixedKernel_iff_continuous_and_mem_sobolevFields {s : ℝ} (hs : 2 < s)
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    y ∈ gaugeFixedKernel x ↔
      Continuous y ∧ y ∈ sobolevFields s ∧ ∀ z, gaugeFixedOperator x y z = 0 := by
  rw [mem_gaugeFixedKernel_iff_mem_sobolevFields hx hbound s]
  refine ⟨fun ⟨hy₁, hys, hyk⟩ ↦ ⟨hy₁.continuous, hys, hyk⟩, fun ⟨hyc, hys, hyk⟩ ↦
    ⟨contDiff_of_mem_sobolevFields (k := 1) (by push_cast; linarith) hys hyc, hys, hyk⟩⟩

/-! ### Framed fields in `A_m^s` and Coulomb-slice vortices -/

/-- At any `C²` field `x ∈ framedFieldSpace f m s`, `s > 1`, satisfying `∂bar_a α = 0`, the
classical kernel `gaugeFixedKernel x` is finite dimensional. -/
theorem finiteDimensional_gaugeFixedKernel_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} {s : ℝ} (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hx₂ : ContDiff ℝ 2 x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    FiniteDimensional ℝ (gaugeFixedKernel x) :=
  finiteDimensional_gaugeFixedKernel hx₂ hhol
    (tendsto_sectionValue_mul_inv_pow hs hx hx₂.continuous)

/-- **Kernel dimension `2m` on `A_m^s`.** At any smooth field `x ∈ framedFieldSpace f m s`,
`s > 1`, satisfying `∂bar_a α = 0`, the classical kernel `gaugeFixedKernel x` has real dimension
`2m`. -/
theorem finrank_gaugeFixedKernel_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {s : ℝ} (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel hxs hhol (tendsto_sectionValue_mul_inv_pow hs hx hxs.continuous)

/-- At any smooth field `x ∈ framedFieldSpace f m s`, `s > 4`, satisfying `∂bar_a α = 0`, the weak
`L²` kernel `gaugeFixedWeakKernel hxs.continuous` is finite dimensional. -/
theorem finiteDimensional_gaugeFixedWeakKernel_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} {s : ℝ} (hs : 4 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    FiniteDimensional ℝ (gaugeFixedWeakKernel hxs.continuous) := by
  refine finiteDimensional_gaugeFixedWeakKernel hxs (fun i n hn ↦ ?_) hhol
    (tendsto_normSq_of_mem_framedFieldSpace (by linarith) hx hxs.continuous)
  have hns : (n : ℝ) + 1 < s := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  exact exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace hns hx hxs.continuous i

/-- **Weak kernel dimension `2m` on `A_m^s`.** At any smooth field `x ∈ framedFieldSpace f m s`,
`s > 4`, satisfying `∂bar_a α = 0`, the weak `L²` kernel `gaugeFixedWeakKernel hxs.continuous` has
real dimension `2m`. -/
theorem finrank_gaugeFixedWeakKernel_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {s : ℝ} (hs : 4 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (gaugeFixedWeakKernel hxs.continuous) = 2 * m := by
  refine finrank_gaugeFixedWeakKernel hxs (fun i n hn ↦ ?_) hhol
    (tendsto_sectionValue_mul_inv_pow (by linarith) hx hxs.continuous)
  have hns : (n : ℝ) + 1 < s := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  exact exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace hns hx hxs.continuous i

private theorem exists_norm_iteratedFDeriv_apply_le_of_equation_eq_zero
    {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) (i : Fin 4) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C := by
  have hxj : x ∈ framedFieldSpace f m ((n + 2 : ℕ) : ℝ) :=
    mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge (n + 2)
  exact exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace
    (by push_cast; linarith) hxj hxc.continuous i

/-- **Kernel regularity at a Coulomb-slice vortex.** Let `x ∈ A_m^k`, `k ≥ 2`, be a `C¹` solution
of the vortex equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` relative to a `C¹` base field
`x₀` lying in every `A_m^j`. Then every `y ∈ gaugeFixedKernel x` is smooth and lies in
`sobolevFields s` for all `s : ℝ`. -/
theorem contDiff_and_mem_sobolevFields_of_mem_gaugeFixedKernel_of_equation_eq_zero
    {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (hk : 1 < k) {x₀ x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ ∞ y ∧ ∀ s : ℝ, y ∈ sobolevFields s := by
  have hxs : ContDiff ℝ ∞ x := contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge
  have hhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [heq w]
  have hlim := tendsto_normSq_of_mem_framedFieldSpace (by exact_mod_cast hk) hx hxc.continuous
  exact ⟨contDiff_of_mem_gaugeFixedKernel hxs hhol hlim hy,
    mem_sobolevFields_of_mem_gaugeFixedKernel hxs
      (exists_norm_iteratedFDeriv_apply_le_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) hy⟩

/-- At any `C¹` Coulomb-slice vortex `x ∈ A_m^k`, `k ≥ 2`, relative to a `C¹` base field `x₀` lying
in every `A_m^j`, `gaugeFixedKernel x` is finite dimensional. -/
theorem finiteDimensional_gaugeFixedKernel_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)}
    {m k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    FiniteDimensional ℝ (gaugeFixedKernel x) :=
  finiteDimensional_gaugeFixedKernel_of_mem_framedFieldSpace (by exact_mod_cast hk) hx
    ((contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge).of_le (by simp))
    fun w ↦ by simp [heq w]

/-- **Classical kernel dimension `2m` at a Coulomb-slice vortex.** Let `x ∈ A_m^k`, `k ≥ 2`, be a
`C¹` solution of the vortex equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` relative to a
`C¹` base field `x₀` lying in every `A_m^j`. Then `gaugeFixedKernel x` has real dimension `2m`. -/
theorem finrank_gaugeFixedKernel_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_of_mem_framedFieldSpace (by exact_mod_cast hk) hx
    (contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) fun w ↦ by simp [heq w]

/-- At any `C¹` Coulomb-slice vortex `x ∈ A_m^k`, `k ≥ 2`, relative to a `C¹` base field `x₀` lying
in every `A_m^j`, `gaugeFixedWeakKernel hxc.continuous` is finite dimensional. -/
theorem finiteDimensional_gaugeFixedWeakKernel_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)}
    {m k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    FiniteDimensional ℝ (gaugeFixedWeakKernel hxc.continuous) :=
  finiteDimensional_gaugeFixedWeakKernel_of_mem_framedFieldSpace (s := (5 : ℕ)) (by norm_num)
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge 5)
    (contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) fun w ↦ by simp [heq w]

/-- **Weak kernel dimension `2m` at a Coulomb-slice vortex.** Let `x ∈ A_m^k`, `k ≥ 2`, be a `C¹`
solution of the vortex equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` relative to a `C¹`
base field `x₀` lying in every `A_m^j`. Then `gaugeFixedWeakKernel hxc.continuous` has real
dimension `2m`. -/
theorem finrank_gaugeFixedWeakKernel_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (gaugeFixedWeakKernel hxc.continuous) = 2 * m :=
  finrank_gaugeFixedWeakKernel_of_mem_framedFieldSpace (s := (5 : ℕ)) (by norm_num)
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge 5)
    (contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) fun w ↦ by simp [heq w]

end TauCeti.Vortex
