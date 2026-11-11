/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Integral
public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature
import TauCeti.Analysis.InnerProductSpace.Comass

/-!
# An `r`-independent mass bound for the curvature current

Let `(a, α, β)` be a solution of Taubes's large-parameter Seiberg–Witten equations at parameter
`r`, with curvature `F_a` on the twisting line and vacuum defect `w₊ = max (1 - |α|²) 0`. Its
curvature current is

`T_r(ζ) = (2π)⁻¹ ∫ i F_a ∧ ζ`,

a current of degree `n` in dimension `2 + n`, with `n = 2` for a four-manifold. The scaled `L²`
bound `r⁻¹ ‖F_a‖₂² ≤ C` only gives `‖F_a‖₂ = O(√r)`, which does not bound the mass of `T_r`
uniformly in `r`. The pointwise curvature bounds do: the self-dual and anti-self-dual bounds add
up to

`|F_a| ≤ (r / (2 √2)) w₊ + O(1)`

(`TauCeti.SeibergWitten.norm_le_of_add_hodgeStar_eq`), so `F_a` is of size `r` only on the
region where `|α|` is small. The `L¹` defect bound `r ∫ |1 - |α|² - |β|²| ≤ C` and the bound
`|β|² ≤ (C / r) w₊ + C / r²` make the integral of `r w₊` bounded
(`TauCeti.SeibergWitten.integral_le_of_le_mul_max_one_sub`). Hence `∫ |F_a|` is bounded
independently of `r` and of the solution, and so is the mass of `T_r`:

* `Module.Basis.exists_abs_integral_wedge_le_of_le_mul_max_one_sub`: if `‖ω‖ ≤ C r w₊ + C` on a
  set `K` of finite volume carrying the two defect bounds, then
  `|∫ ω ∧ ζ| ≤ M sup ‖ζ‖ C (C + Vol K)` for every form `ζ` vanishing outside `K`, with `M`
  depending only on the basis used to integrate;
* `Module.Basis.exists_mass_integral_wedge_le_of_le_mul_max_one_sub`: the same bound for the mass
  (`Distribution.mass`) of the current `ζ ↦ ∫ ω ∧ ζ` on test forms on an open set of finite
  volume;
* `exists_mass_integral_wedge_le_of_add_hodgeStar_eq`: for solutions of the large-parameter
  curvature equation in a constant unitary frame, the mass of `ζ ↦ ∫ i F_a ∧ ζ` on test forms on
  an open set `Ω` of finite volume is bounded by a constant depending only on `Ω`, the basis used
  to integrate, the constants in the coarse bounds, the forcing bound and the lower bound on the
  Hermitian part of `i F_a`, once `r` is large.

A uniform mass bound is the input for extracting weak limits of the currents `T_{r_n}` as
`r_n → ∞` (`Distribution.isCompact_image_coe_mass_le`). The two general bounds are stated for a
form `ω` of any degree `k` in dimension `k + n`; for the curvature current `k = 2` and `ω` is the
real form `i F_a`, with the operator norm, which is the comass on an inner product space. When `ω`
is the form `⟪F, · ∧ ·⟫` of a two-vector `F`, its comass is at most the inner product norm of `F`
(`TauCeti.norm_alternatingFormEquiv_le`), so the pointwise bound of
`TauCeti.SeibergWitten.norm_le_of_add_hodgeStar_eq`, computed in a unitary frame, supplies the
hypothesis `‖ω‖ ≤ C r w₊ + C` once `C` dominates its constants. As in
`TauCeti.Analysis.PDE.SeibergWitten.CurvatureComparison`, top-degree coefficients are taken on a
basis `e` and integrated against its Haar measure.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap MeasureTheory TopologicalSpace
open scoped Distributions

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B] {k n : ℕ}

/-- **The `r`-independent bound on the curvature current against a form.** There is a constant
`M`, depending only on the basis `e`, with the following property. Let `K` be a measurable set of
finite volume on which `r ∫_K |1 - |α|² - |β|²| ≤ C` and, almost everywhere,
`|β|² ≤ (C / r) w₊ + C / r²`, where `w₊ = max (1 - |α|²) 0` and `2 C ≤ r`. If a `k`-form `ω`
satisfies `‖ω‖ ≤ C r w₊ + C` on `K`, then for every form `ζ` of degree `n` vanishing outside `K`
with `‖ζ‖ ≤ Z`,

`|∫ ω ∧ ζ| ≤ M Z C (C + Vol K)`.

The right side does not depend on `r`. Top-degree coefficients are taken on `e` and integrated
against its Haar measure. -/
theorem _root_.Module.Basis.exists_abs_integral_wedge_le_of_le_mul_max_one_sub
    (e : Module.Basis (Fin (k + n)) ℝ E) :
    ∃ M, 0 ≤ M ∧ ∀ ⦃ω : E → E [⋀^Fin k]→L[ℝ] ℝ⦄ ⦃ζ : E → E [⋀^Fin n]→L[ℝ] ℝ⦄
      ⦃α : E → A⦄ ⦃β : E → B⦄ ⦃K : Set E⦄ ⦃r C Z : ℝ⦄,
      MeasurableSet K → e.addHaar K ≠ ⊤ → 0 < r → 0 ≤ C → 2 * C ≤ r →
      IntegrableOn (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) K e.addHaar →
      r * ∫ x in K, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂e.addHaar ≤ C →
      (∀ᵐ x ∂e.addHaar.restrict K, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) →
      AEStronglyMeasurable ω (e.addHaar.restrict K) →
      (∀ x ∈ K, ‖ω x‖ ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C) →
      (∀ x ∉ K, ζ x = 0) → (∀ x, ‖ζ x‖ ≤ Z) →
      |∫ x, wedge (ω x) (ζ x) e ∂e.addHaar| ≤ M * (Z * (C * (C + e.addHaar.real K))) := by
  obtain ⟨M, hM, hI⟩ := e.exists_abs_integral_wedge_le
  refine ⟨2 * M, by positivity, ?_⟩
  intro ω ζ α β K r C Z hK hKfin hr hC hCr hδ hL1 hβ hω hωK hζK hζZ
  have : IsFiniteMeasure (e.addHaar.restrict K) := isFiniteMeasure_restrict.2 hKfin
  have hZ : 0 ≤ Z := (norm_nonneg _).trans (hζZ 0)
  -- Since `w₊ ≤ 1`, the form is bounded on `K`, hence integrable there.
  have hωint : IntegrableOn (fun x ↦ ‖ω x‖) K e.addHaar := by
    refine IntegrableOn.of_bound hKfin.lt_top hω.norm (C * r + C)
      ((ae_restrict_iff' hK).2 (Filter.Eventually.of_forall fun x hx ↦ ?_))
    have hm : max (1 - ‖α x‖ ^ 2) 0 ≤ 1 := max_le (by nlinarith [sq_nonneg ‖α x‖]) zero_le_one
    rw [norm_norm]
    calc ‖ω x‖ ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C := hωK x hx
      _ ≤ C * r * 1 + C := by gcongr
      _ = C * r + C := by ring
  -- The coarse integrated bound gives `∫_K ‖ω‖ ≤ 2 C (C + Vol K)`.
  have hL : ∫ x in K, ‖ω x‖ ∂e.addHaar ≤ 2 * C * (C + e.addHaar.real K) := by
    rw [← measureReal_restrict_apply_univ]
    exact integral_le_of_le_mul_max_one_sub hr hC hCr hδ hL1 hβ
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
      ((ae_restrict_iff' hK).2 (Filter.Eventually.of_forall hωK))
  calc |∫ x, wedge (ω x) (ζ x) e ∂e.addHaar|
      ≤ M * (Z * ∫ x in K, ‖ω x‖ ∂e.addHaar) :=
        hI hK hζK hωint (fun x _ ↦ le_rfl) hζZ
    _ ≤ M * (Z * (2 * C * (C + e.addHaar.real K))) := by gcongr
    _ = 2 * M * (Z * (C * (C + e.addHaar.real K))) := by ring

/-- **The `r`-independent mass bound for the curvature current.** There is a constant `M`,
depending only on the basis `e`, with the following property. Let `Ω` be an open set of finite
volume on which `r ∫_Ω |1 - |α|² - |β|²| ≤ C` and, almost everywhere,
`|β|² ≤ (C / r) w₊ + C / r²`, where `w₊ = max (1 - |α|²) 0` and `2 C ≤ r`. If a `k`-form `ω`
satisfies `‖ω‖ ≤ C r w₊ + C` on `Ω`, then the current `ζ ↦ ∫ ω ∧ ζ` on test forms of degree `n`
on `Ω` has mass at most `M C (C + Vol Ω)`, independently of `r`. -/
theorem _root_.Module.Basis.exists_mass_integral_wedge_le_of_le_mul_max_one_sub
    (e : Module.Basis (Fin (k + n)) ℝ E) :
    ∃ M, 0 ≤ M ∧ ∀ ⦃Ω : Opens E⦄ ⦃ω : E → E [⋀^Fin k]→L[ℝ] ℝ⦄ ⦃α : E → A⦄ ⦃β : E → B⦄
      ⦃r C : ℝ⦄, e.addHaar Ω ≠ ⊤ → 0 < r → 0 ≤ C → 2 * C ≤ r →
      IntegrableOn (fun x ↦ 1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) Ω e.addHaar →
      r * ∫ x in Ω, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂e.addHaar ≤ C →
      (∀ᵐ x ∂e.addHaar.restrict Ω, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) →
      AEStronglyMeasurable ω (e.addHaar.restrict Ω) →
      (∀ x ∈ Ω, ‖ω x‖ ≤ C * r * max (1 - ‖α x‖ ^ 2) 0 + C) → ∀ m : ℕ∞,
      Distribution.mass (fun ζ : 𝓓^{m}(Ω, E [⋀^Fin n]→L[ℝ] ℝ) ↦
          ∫ x, wedge (ω x) (ζ x) e ∂e.addHaar) ≤
        ENNReal.ofReal (M * (C * (C + e.addHaar.real Ω))) := by
  obtain ⟨M, hM, hI⟩ := e.exists_abs_integral_wedge_le_of_le_mul_max_one_sub (A := A) (B := B)
  refine ⟨M, hM, ?_⟩
  intro Ω ω α β r C hΩ hr hC hCr hδ hL1 hβ hω hωΩ m
  refine Distribution.mass_le_iff.2 fun ζ hζ ↦ ?_
  have hζΩ (x : E) (hx : x ∉ (Ω : Set E)) : ζ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (ζ.tsupport_subset h)
  have h := hI Ω.isOpen.measurableSet hΩ hr hC hCr hδ hL1 hβ hω hωΩ hζΩ hζ
  rw [one_mul] at h
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal h

/-! ### Solutions of the large-parameter equations in a unitary frame -/

section Solution

open CliffordAlgebra Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  [MeasurableSpace V] [BorelSpace V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

attribute [local instance] finiteDimensional_of_finrank_four

/-- **The curvature current of large-parameter solutions has `r`-independent mass.** Work on an
open set `Ω` of finite volume in an oriented four-dimensional inner product space with a constant
unitary frame `e`, `J e₀ = e₁`, `J e₂ = e₃`, and Kähler two-vector `ω`. Fix constants `K`, `C`
and `N`. There are `M` and `r₀` such that for every `r ≥ r₀` and every solution of the
large-parameter curvature equation

`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`

on `Ω`, with `φ` in the canonical line and `β` in its complement, the coarse bounds
`|φ|² + |β|² ≤ 1 + K / r`, `|β|² ≤ (K / r) w₊ + K / r²` and `r ∫_Ω |1 - |φ|² - |β|²| ≤ K`, the
bound `|η| ≤ N` on the forcing and the lower bound `B ≥ -C g` on the Hermitian part of `F`, the
current `ζ ↦ ∫ F ∧ ζ` on test two-forms on `Ω` has mass at most `M`. Here `F` is the real form
`i F_a`, acting on test forms through `⟪F, · ∧ ·⟫`, and the top-degree coefficients are taken on
a basis `b` and integrated against its Haar measure. -/
theorem exists_mass_integral_wedge_le_of_add_hodgeStar_eq (h₀ : J (e 0) = e 1)
    (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
    (he : e.toBasis.orientation = o) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) (b : Module.Basis (Fin (2 + 2)) ℝ V)
    {Ω : Opens V} (hΩ : b.addHaar Ω ≠ ⊤) (K C N : ℝ) :
    ∃ M r₀, ∀ ⦃r : ℝ⦄ ⦃F η : V → ⋀[ℝ]^2 V⦄ ⦃φ β : V → positiveHalfSpinors o ρ⦄, r₀ ≤ r →
      AEStronglyMeasurable F (b.addHaar.restrict Ω) →
      IntegrableOn (fun x ↦ 1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2) Ω b.addHaar →
      r * ∫ x in Ω, |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| ∂b.addHaar ≤ K →
      (∀ x ∈ Ω, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ Ω, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ Ω, ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2) →
      (∀ x ∈ Ω, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r) → (∀ x ∈ Ω, ‖η x‖ ≤ N) →
      (∀ x ∈ Ω, ∀ v, -C * ‖v‖ ^ 2 ≤ J.hermitianForm (F x) v v) →
      (∀ x ∈ Ω, F x + o.hodgeStar hkl (F x) = (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 V) - η x) →
      ∀ m : ℕ∞, Distribution.mass (fun ζ : 𝓓^{m}(Ω, V [⋀^Fin 2]→L[ℝ] ℝ) ↦
          ∫ x, wedge (alternatingFormEquiv V 2 (F x)) (ζ x) b ∂b.addHaar) ≤ ENNReal.ofReal M := by
  obtain ⟨M, -, hM⟩ :=
    b.exists_mass_integral_wedge_le_of_le_mul_max_one_sub (A := positiveHalfSpinors o ρ)
      (B := positiveHalfSpinors o ρ)
  -- A single constant `C'` dominating every constant of the pointwise curvature bound.
  set c₀ := (2 * K + 1) / (2 * √2) + N + √2 * C
  set C' := max (max K 1) c₀
  have hKC : K ≤ C' := (le_max_left _ _).trans (le_max_left _ _)
  have h1C : 1 ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  have hcC : c₀ ≤ C' := le_max_right _ _
  refine ⟨M * (C' * (C' + b.addHaar.real Ω)), max 1 (2 * C'), ?_⟩
  intro r F η φ β hr hF hδ hL1 hφ hβ hβK hφβ hη hH hFeq m
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hs2 : 1 ≤ 2 * √2 := by linarith [Real.one_lt_sqrt_two]
  refine hM hΩ hr0 (by linarith) ((le_max_right _ _).trans hr) hδ (hL1.trans hKC)
    ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall fun x hx ↦ ?_))
    ((LinearMap.continuous_of_finiteDimensional
      (alternatingFormEquiv V 2).toLinearMap).comp_aestronglyMeasurable hF) (fun x hx ↦ ?_) m
  · calc ‖β x‖ ^ 2 ≤ K / r * max (1 - ‖φ x‖ ^ 2) 0 + K / r ^ 2 := hβK x hx
      _ ≤ C' / r * max (1 - ‖φ x‖ ^ 2) 0 + C' / r ^ 2 := by gcongr
  · have hm : 0 ≤ max (1 - ‖φ x‖ ^ 2) 0 := le_max_right _ _
    have hFx := norm_le_of_add_hodgeStar_eq h₀ h₂₃ hQ hkl he (hφ x hx) (hβ x hx) hρ h₂ hr1
      (hβK x hx) (hφβ x hx) (hFeq x hx) (hH x hx)
    have hr' : r / (2 * √2) ≤ C' * r := by
      rw [div_le_iff₀ (by positivity)]
      have h := mul_le_mul h1C hs2 zero_le_one (by linarith)
      nlinarith
    calc ‖alternatingFormEquiv V 2 (F x)‖ ≤ ‖F x‖ := norm_alternatingFormEquiv_le _
      _ ≤ r / (2 * √2) * max (1 - ‖φ x‖ ^ 2) 0 + (2 * K + 1) / (2 * √2) + ‖η x‖ + √2 * C := hFx
      _ ≤ C' * r * max (1 - ‖φ x‖ ^ 2) 0 + c₀ := by
          have := hη x hx
          have := mul_le_mul_of_nonneg_right hr' hm
          simp only [c₀]
          linarith
      _ ≤ C' * r * max (1 - ‖φ x‖ ^ 2) 0 + C' := by gcongr

end Solution

end TauCeti.SeibergWitten
