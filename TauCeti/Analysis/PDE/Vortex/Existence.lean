/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Asymptotics
public import TauCeti.Analysis.PDE.Vortex.Divisor
public import TauCeti.Analysis.PDE.Vortex.EulerLagrange
public import TauCeti.Analysis.PDE.Vortex.Minimizer
public import TauCeti.Analysis.PDE.Vortex.Regularity
public import TauCeti.Analysis.PDE.Vortex.Smoothness
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Existence of framed plane vortices with prescribed zeros

A smooth plane vortex with the degree-`m` end framing is a smooth field `x` on `ℂ` solving the
vortex equations `TauCeti.Vortex.equation x = 0` whose section satisfies
`α(z) (z / |z|)⁻ᵐ → 1` at infinity. Its zeros, counted with multiplicity, form a point of
`Sym ℂ m` (`TauCeti.Vortex.exists_sym_sectionValue_eq_pow_count_mul`), and two such vortices
differ by a smooth framed gauge exactly when their divisors agree
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_eq_iff`). This file proves Taubes's existence
theorem: every effective divisor of degree `m`, repeated points included, is the divisor of a
smooth framed vortex. Together with uniqueness this identifies the framed gauge orbits of smooth
framed degree-`m` vortices with `Sym ℂ m`.

Existence follows Taubes's variational argument, whose steps are already available.

1. For a polynomial `P` of degree `m ≥ 1` the reduced functional has a minimizer `u ∈ H¹(ℂ)`
   (`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`), which solves the reduced
   equation weakly (`TauCeti.Vortex.integral_inner_gradient_add_integral_mul_eq_zero`).
2. Weak solutions agree almost everywhere with `C²` classical solutions `w`
   (`TauCeti.Vortex.exists_contDiff_two_ae_eq_and_laplacian_eq`); Green's identity turns the
   classical equation back into a distributional one, so `w` is smooth
   (`TauCeti.Vortex.contDiffOn_of_forall_integral_laplacian_mul_eq_reduced`).
3. Since `w ∈ L²(ℂ)`, it tends to zero at infinity
   (`TauCeti.Vortex.tendsto_cocompact_of_memLp_of_laplacian_eq`), so for monic `P` the field
   with amplitude `u₀ + w` and section `exp(u₀ + w) P`, `u₀` the background amplitude, is a vortex
   with the degree-`m` end framing
   (`TauCeti.Vortex.equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp`).

For `D ∈ Sym ℂ m` take `P = ∏_{a ∈ D} (X - a)`; its section `exp(u₀ + w) P` has zero divisor
`D`. For `m = 0` the vacuum, with section `1` and zero connection, is the vortex.

## Main results

All in the namespace `TauCeti.Vortex`:

* `exists_contDiff_memLp_laplacian_eq_reduced`: for a polynomial of positive degree, the reduced
  vortex equation has a smooth square-integrable solution tending to zero at infinity.
* `exists_contDiff_equation_eq_zero_isZeroMultiplicity`: every `D ∈ Sym ℂ m` is the zero divisor
  of a smooth vortex with the degree-`m` end framing.
* `framedVortexSubMulAction`: the smooth framed degree-`m` vortices, preserved by smooth framed
  gauges.
* `framedVortexDivisor`: the zero divisor of a smooth framed degree-`m` vortex, a point of
  `Sym ℂ m`, characterized by `framedVortexDivisor_eq_iff`.
* `framedVortexModuliEquiv`: the framed gauge orbits of smooth framed degree-`m` vortices are in
  bijection with `Sym ℂ m` through the divisor.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open Complex Filter Topology InnerProductSpace Laplacian MeasureTheory Polynomial
open scoped ContDiff RealInnerProductSpace Gradient

namespace TauCeti.Vortex

/-! ### The reduced equation -/

/-- **Existence for the reduced vortex equation.** For a complex polynomial `P` of positive
degree there is a smooth function `w ∈ L²(ℂ)` with `w → 0` at infinity solving Taubes's reduced
equation `Δw = (exp (2w) h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²` at every point, where
`h = ‖P‖² / (1 + ‖P‖²)` is `TauCeti.Vortex.backgroundWeight P.eval`. -/
theorem exists_contDiff_memLp_laplacian_eq_reduced {P : ℂ[X]} (hm : 0 < P.natDegree) :
    ∃ w : ℂ → ℝ, ContDiff ℝ ∞ w ∧ MemLp w 2 ∧ Tendsto w (cocompact ℂ) (𝓝 0) ∧
      ∀ z, Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
        2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
  have hP : Differentiable ℂ P.eval := P.differentiable
  -- A minimizer of Taubes's functional is a weak solution.
  obtain ⟨u, hu⟩ := exists_forall_sobolevReducedFunctional_le hm
  have hweak (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
      (∫ z, ⟪W1p.gradient u z, ∇ φ z⟫) +
        ∫ z, (backgroundWeight P.eval z * (Real.exp (2 * W1p.value u z) - 1) / 8 +
          backgroundSource P.eval z) * φ z = 0 := by
    rw [← integral_inner_gradient_add_integral_mul_eq_zero hm hu (hφ.of_le (by simp)) hφc]
    congr 2 with z
    rw [backgroundSource_def, backgroundWeight_def, Polynomial.deriv]
    ring
  -- It agrees almost everywhere with a classical solution `w`.
  obtain ⟨w, hw, huw, hΔ⟩ := exists_contDiff_two_ae_eq_and_laplacian_eq
    Complex.finrank_real_complex (contDiff_backgroundWeight (hP.contDiff.restrict_scalars ℝ))
    (contDiff_backgroundSource hP) hweak
  have heq (z : ℂ) : Δ w z = (Real.exp (2 * w z) * backgroundWeight P.eval z - 1) / 8 +
      2 * ‖deriv P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 := by
    rw [hΔ z, backgroundSource_def]
    ring
  have hwp : MemLp w 2 := (W1p.memLp_value u).ae_eq huw
  -- Green's identity makes the classical solution a distributional one, hence smooth.
  have hsmooth : ContDiff ℝ ∞ w := by
    have h := contDiffOn_of_forall_integral_laplacian_mul_eq_reduced (U := ⊤) (f := P.eval)
      (fun z _ ↦ hP.analyticAt z) hw.continuous.continuousOn fun φ ↦ by
        have hgreen := (hw.contDiffOn (s := ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ))
          ).integral_laplacian_smul_eq_integral_smul_laplacian (μ := volume) φ
        simp only [smul_eq_mul] at hgreen
        rw [hgreen]
        simp only [heq]
    exact contDiffOn_univ.1 (by simpa using h)
  exact ⟨w, hsmooth, hwp, tendsto_cocompact_of_memLp_of_laplacian_eq
    (.of_forall fun _ ↦ hw.contDiffAt) hwp one_le_two ENNReal.ofNat_ne_top (.of_forall heq), heq⟩

/-! ### Vortices with prescribed zeros -/

/-- **Existence of framed plane vortices with prescribed zeros** (Taubes). For every effective
divisor `D ∈ Sym ℂ m`, repeated points allowed, there is a smooth solution `x` of the vortex
equations on `ℂ` whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` and
vanishes exactly at the points of `D`, to the order of their multiplicities. -/
theorem exists_contDiff_equation_eq_zero_isZeroMultiplicity {m : ℕ} (D : Sym ℂ m) :
    ∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  set f : ℂ → ℂ := fun w ↦ ((D : Multiset ℂ).map fun a ↦ w - a).prod with hf
  set P : ℂ[X] := ((D : Multiset ℂ).map fun a ↦ X - C a).prod with hP
  have hPf : P.eval = f := funext fun w ↦ by simp [hP, hf, eval_multiset_prod, Multiset.map_map]
  have hdeg : P.natDegree = m := by
    rw [hP, natDegree_multiset_prod_X_sub_C_eq_card]
    exact D.2
  have hfc : ContDiff ℝ ∞ f := hPf ▸ (P.differentiable.contDiff).restrict_scalars ℝ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- The vacuum: amplitude zero and section `1`.
    have hf1 : f = 1 := by
      rw [hf, Sym.eq_nil_of_card_zero D]
      funext w
      simp
    refine ⟨amplitudeField 0 f, contDiff_amplitudeField (n := ⊤) contDiff_const hfc,
      fun z ↦ ?_, ?_, isZeroMultiplicity_sectionValue_amplitudeField_prod_sub continuous_const _⟩
    · rw [equation_amplitudeField_eq_zero_iff (u := 0) (f := f) contDiffAt_const
        (hPf ▸ P.differentiable z)]
      simp [hf1, Pi.zero_def]
    · simp [sectionValue_amplitudeField, hf1]
  · -- A degree-`m` vortex from the solution of the reduced equation for `P`.
    have hm' : 0 < P.natDegree := by omega
    obtain ⟨w, hw, hwp, -, hΔ⟩ := exists_contDiff_memLp_laplacian_eq_reduced hm'
    obtain ⟨hsol, hfr⟩ := equation_amplitudeField_eq_zero_and_tendsto_sectionValue_of_memLp
      (monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a) hm'
      (hw.of_le (by simp)) hwp one_le_two ENNReal.ofNat_ne_top hΔ
    rw [hPf, hdeg] at hfr
    rw [hPf] at hsol
    have hu : ContDiff ℝ ∞ fun z ↦ backgroundAmplitude f z + w z :=
      (contDiff_backgroundAmplitude hfc).add hw
    exact ⟨_, contDiff_amplitudeField (n := ⊤) (hu.of_le (by simp)) hfc, hsol, hfr,
      isZeroMultiplicity_sectionValue_amplitudeField_prod_sub hu.continuous _⟩

/-! ### The moduli of framed vortices -/

/-- **Smooth framed vortices of degree `m`.** The smooth solutions `x` of the vortex equations on
`ℂ` whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Smooth framed gauges
preserve them. -/
def framedVortexSubMulAction (m : ℕ) :
    SubMulAction framedGaugeGroup (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {x | ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
    Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)}
  smul_mem' u x := by
    rintro ⟨hx, hsol, hfr⟩
    obtain ⟨hu, hu1⟩ := (mem_framedGaugeGroup _).1 u.2
    simp only [Set.mem_ofPred_eq, framedGaugeGroup_smul]
    refine ⟨contDiff_gaugeTransform hu hx, fun z ↦ ?_, tendsto_sectionValue_gaugeTransform hu1 hfr⟩
    rw [equation_gaugeTransform_eq_zero_iff (hu.contDiffAt.of_le (by simp)) fun i ↦
      (((contDiff_piLp 2).1 hx i).differentiable (by simp)).differentiableAt]
    exact hsol z

/-- The members of `framedVortexSubMulAction m` are the smooth framed degree-`m` vortices. -/
@[simp]
theorem mem_framedVortexSubMulAction {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    x ∈ framedVortexSubMulAction m ↔ ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) :=
  Iff.rfl

variable {m : ℕ}

/-- The zeros of a smooth framed degree-`m` vortex form an effective divisor of degree `m`. -/
private theorem exists_sym_isZeroMultiplicity_of_mem_framedVortexSubMulAction
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedVortexSubMulAction m) :
    ∃ D : Sym ℂ m, IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  obtain ⟨hx, hsol, hfr⟩ := hx
  have hxi (i : Fin 4) : ContDiff ℝ ∞ fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hd (i : Fin 4) : Differentiable ℝ fun w ↦ x w i := (hxi i).differentiable (by simp)
  obtain ⟨D, hD⟩ := exists_sym_sectionValue_eq_pow_count_mul (k := ⊤) le_top (hxi 0) (hxi 1)
    (hd 2) (hd 3) (fun w ↦ by simp [hsol w]) hfr
  exact ⟨D, isZeroMultiplicity_iff.2 fun z ↦
    let ⟨v, hv, hv₀, hfac⟩ := hD z
    ⟨v, hv.continuousAt, hv₀, hfac⟩⟩

/-- **The zero divisor of a smooth framed degree-`m` vortex**, the point of `Sym ℂ m` listing the
zeros of its section with multiplicity. It is characterized by `framedVortexDivisor_eq_iff`. -/
def framedVortexDivisor (x : framedVortexSubMulAction m) : Sym ℂ m :=
  (exists_sym_isZeroMultiplicity_of_mem_framedVortexSubMulAction x.2).choose

/-- The section of a smooth framed vortex vanishes at the points of its divisor, to the order of
their multiplicities. -/
theorem isZeroMultiplicity_sectionValue_framedVortexDivisor (x : framedVortexSubMulAction m) :
    IsZeroMultiplicity (sectionValue x) fun z ↦ (framedVortexDivisor x : Multiset ℂ).count z :=
  (exists_sym_isZeroMultiplicity_of_mem_framedVortexSubMulAction x.2).choose_spec

/-- **Characterization of the divisor.** The divisor of a smooth framed vortex is the unique
`D ∈ Sym ℂ m` whose counts are the zero multiplicities of its section. -/
theorem framedVortexDivisor_eq_iff {x : framedVortexSubMulAction m} {D : Sym ℂ m} :
    framedVortexDivisor x = D ↔
      IsZeroMultiplicity (sectionValue x) fun z ↦ (D : Multiset ℂ).count z := by
  refine ⟨fun h ↦ h ▸ isZeroMultiplicity_sectionValue_framedVortexDivisor x, fun h ↦ ?_⟩
  exact Sym.coe_injective <| Multiset.ext.2 fun z ↦
    congrFun ((isZeroMultiplicity_sectionValue_framedVortexDivisor x).unique h) z

/-- Smooth framed gauges do not change the divisor. -/
@[simp]
theorem framedVortexDivisor_smul (u : framedGaugeGroup) (x : framedVortexSubMulAction m) :
    framedVortexDivisor (u • x) = framedVortexDivisor x := by
  rw [framedVortexDivisor_eq_iff, SubMulAction.val_smul]
  exact isZeroMultiplicity_sectionValue_framedGaugeGroup_smul
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x) u

/-- **Taubes's uniqueness theorem.** Two smooth framed degree-`m` vortices have the same divisor
exactly when they differ by a smooth framed gauge. -/
theorem framedVortexDivisor_eq_framedVortexDivisor_iff {x y : framedVortexSubMulAction m} :
    framedVortexDivisor x = framedVortexDivisor y ↔ ∃ u : framedGaugeGroup, u • y = x := by
  obtain ⟨hx, hxsol, hxfr⟩ := x.2
  obtain ⟨hy, hysol, hyfr⟩ := y.2
  -- The inverse winding phase has modulus one away from the origin.
  have hphase : Tendsto (fun z : ℂ ↦ ‖((z / (‖z‖ : ℂ)) ^ m)⁻¹‖) (cocompact ℂ) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
    simp [Set.mem_compl_singleton_iff.1 hz]
  rw [← Sym.coe_inj, ← exists_framedGaugeGroup_smul_eq_iff hx hy hxsol hysol hphase hxfr hyfr
    (isZeroMultiplicity_sectionValue_framedVortexDivisor x)
    (isZeroMultiplicity_sectionValue_framedVortexDivisor y)]
  simp only [Subtype.ext_iff, SubMulAction.val_smul]

/-- **Taubes's existence theorem.** Every effective divisor of degree `m` is the divisor of a
smooth framed degree-`m` vortex. -/
theorem framedVortexDivisor_surjective (m : ℕ) :
    Function.Surjective (framedVortexDivisor (m := m)) := fun D ↦ by
  obtain ⟨x, hx, hsol, hfr, hD⟩ := exists_contDiff_equation_eq_zero_isZeroMultiplicity D
  exact ⟨⟨x, hx, hsol, hfr⟩, framedVortexDivisor_eq_iff.2 hD⟩

/-- **The moduli space of framed plane vortices is `Sym ℂ m`** (Taubes). The divisor identifies
the orbits of the smooth framed gauge group on the smooth framed degree-`m` vortices with the
effective divisors of degree `m`. -/
def framedVortexModuliEquiv (m : ℕ) :
    MulAction.orbitRel.Quotient framedGaugeGroup (framedVortexSubMulAction m) ≃ Sym ℂ m :=
  Equiv.ofBijective
    (Quotient.lift framedVortexDivisor fun x y h ↦ by
      obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
      exact framedVortexDivisor_smul u y)
    ⟨fun a b ↦ Quotient.inductionOn₂ a b fun x y h ↦ Quotient.sound <|
        MulAction.orbitRel_apply.2 <| MulAction.mem_orbit_iff.2 <|
          framedVortexDivisor_eq_framedVortexDivisor_iff.1 h,
      fun D ↦ (framedVortexDivisor_surjective m D).elim fun x hx ↦ ⟨Quotient.mk'' x, hx⟩⟩

/-- The class of a smooth framed vortex goes to its divisor. -/
@[simp]
theorem framedVortexModuliEquiv_mk (x : framedVortexSubMulAction m) :
    framedVortexModuliEquiv m (Quotient.mk'' x) = framedVortexDivisor x :=
  (rfl)

end TauCeti.Vortex
