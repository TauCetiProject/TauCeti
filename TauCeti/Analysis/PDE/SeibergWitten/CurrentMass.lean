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
# `r`-independent mass bounds for the curvature and cutoff currents

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

The same bounds control the **cutoff current** `Θ = i F_a + d(χ(|α|²) τ)`
(`TauCeti.SeibergWitten.cutoffCurrent`), whose weak limits are the currents of the limiting
pseudoholomorphic curves. Pointwise it is
`Θ(u, w) = (1 - χ(|α|²)) i F_a(u, w) + 2 χ'(|α|²) Im (conj (∇_u α) ∇_w α)`
(`TauCeti.SeibergWitten.cutoffCurrent_apply_pair`), so `‖Θ‖ ≤ ‖F_a‖ + 2 sup χ' |∇_a α|²`. Here
only the coarse anti-self-dual bound `|F_a⁻| ≤ (r / (4 √2)) (1 + C r^(-1/2)) w₊ + C` is used,
together with the coarse gradient bound `|∇_a α|² ≤ C r w₊ + C`; no lower bound on the Hermitian
part of `i F_a` enters. Both terms are then at most `C' r w₊ + C'`, and the cutoff current has
`r`-independent mass:

* `norm_le_mul_max_one_sub_add_of_inner_ιMulti_eq`: the pointwise bound `‖Θ‖ ≤ C' r w₊ + C'`
  with `C' = 2 + 2 C + N + 2 M C`, where `N` bounds the forcing and `M` bounds `χ'`;
* `integral_norm_le_of_inner_ιMulti_eq`: on a finite measure space, `∫ ‖Θ‖ ≤ 2 C' (C' + Vol X)`;
* `exists_mass_integral_wedge_le_of_inner_ιMulti_eq`: on an open set `Ω` of finite volume in a
  chart, the current `ζ ↦ ∫ Θ ∧ ζ` has mass bounded independently of `r` and of the solution.

Together with the `O(r^(-1/2))` bound on the integrated distance of `Θ` to the cone of positive
`(1,1)`-forms (`TauCeti.SeibergWitten.integral_infDist_positiveCone_le`), this is the coarse
estimate from which weak limits of `Θ / 2π` are positive `(1,1)`-currents of bounded mass.

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
  rw [Real.eNorm_eq_ofReal_abs]
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

/-! ### The cutoff current -/

section Cutoff

open CliffordAlgebra Module Set _root_.exteriorPower
open scoped RealInnerProductSpace ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  {χ : ℝ → ℝ} {r C M N : ℝ}

attribute [local instance] finiteDimensional_of_finrank_four

include h₀ h₂₃ hQ he hρ h₂

/-- **The cutoff current is of size `r` only where `|α|` is small.** Work at one point, in a
unitary frame `e` with `J e₀ = e₁`, `J e₂ = e₃`. Let `F = i F_a` solve the large-parameter
curvature equation `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` with `‖η‖ ≤ N`, and let `Θ` be the
cutoff current,
`Θ(u, w) = (1 - χ(|φ|²)) F(u, w) + 2 χ'(|φ|²) Im (conj (Dα u) Dα w)`, for a cutoff `χ` with values
in `[0, 1]` and `0 ≤ χ' ≤ M`, where `Dα = ∇_a α`. Assume the coarse bounds, with `C ≥ 0` and
`w₊ = max (1 - |φ|²) 0`: `|φ|² + |β|² ≤ 1 + C / r`, `|β|² ≤ (C / r) w₊ + C / r²`,
`|Dα|² ≤ C r w₊ + C`, and the coarse anti-self-dual bound
`|F⁻| ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`. Then for `r ≥ 1`

`‖Θ‖ ≤ C' r w₊ + C'`,  `C' = 2 + 2 C + N + 2 M C`.

No lower bound on the Hermitian part of `F` is needed. -/
theorem norm_le_mul_max_one_sub_add_of_inner_ιMulti_eq {Θ F η : ⋀[ℝ]^2 V}
    {φ β : positiveHalfSpinors o ρ} {Dα : V →L[ℝ] ℂ} (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hχ : ∀ s, χ s ∈ Icc 0 1) (hχ' : ∀ s, deriv χ s ∈ Icc 0 M)
    (hφ : cliffordProjection o ρ J.kahlerForm φ = φ)
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0)
    (hF : F + o.hodgeStar hkl F = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η)
    (hη : ‖η‖ ≤ N)
    (hFm : ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ‖ ^ 2) 0 + C)
    (hΘ : ∀ u w, ⟪Θ, ιMulti ℝ 2 ![u, w]⟫ =
      (1 - χ (‖φ‖ ^ 2)) * ⟪F, ιMulti ℝ 2 ![u, w]⟫ +
        2 * deriv χ (‖φ‖ ^ 2) * (conj (Dα u) * Dα w).im)
    (hφβ : ‖φ‖ ^ 2 + ‖β‖ ^ 2 ≤ 1 + C / r)
    (hβK : ‖β‖ ^ 2 ≤ C / r * max (1 - ‖φ‖ ^ 2) 0 + C / r ^ 2)
    (hDα : ‖Dα‖ ^ 2 ≤ C * r * max (1 - ‖φ‖ ^ 2) 0 + C) :
    ‖Θ‖ ≤ (2 + 2 * C + N + 2 * M * C) * r * max (1 - ‖φ‖ ^ 2) 0 +
      (2 + 2 * C + N + 2 * M * C) := by
  have hM : 0 ≤ M := (hχ' 0).1.trans (hχ' 0).2
  have hN : 0 ≤ N := (norm_nonneg η).trans hη
  -- The self-dual part is controlled by the curvature equation.
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := by
    rw [AlmostComplexStructure.norm_kahlerForm_sq
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃),
      Fact.out (p := finrank ℝ V = 4)]
    norm_num
  have hplus := norm_smul_add_hodgeStar_le hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he) hω₂ hφ hβ hρ h₂ hr hβK hφβ hF
  have hsplit :
      F = (2⁻¹ : ℝ) • (F + o.hodgeStar hkl F) + (2⁻¹ : ℝ) • (F - o.hodgeStar hkl F) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ F, smul_smul]
    norm_num
  have hFn : ‖F‖ ≤
      ‖(2⁻¹ : ℝ) • (F + o.hodgeStar hkl F)‖ + ‖(2⁻¹ : ℝ) • (F - o.hodgeStar hkl F)‖ := by
    nth_rewrite 1 [hsplit]
    exact norm_add_le _ _
  -- The cutoff current is `(1 - χ(|φ|²)) F + 2 χ'(|φ|²) p₁ ∧ p₂`.
  have hΘ' : Θ = (1 - χ (‖φ‖ ^ 2)) • F + (2 * deriv χ (‖φ‖ ^ 2)) • Dα.gradientWedge :=
    ext_inner_ιMulti_two fun u w ↦ by
      rw [hΘ, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        Dα.inner_gradientWedge_ιMulti]
  have hΘn : ‖Θ‖ ≤ ‖F‖ + 2 * M * ‖Dα‖ ^ 2 := by
    rw [hΘ']
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 (hχ _).2),
      Real.norm_of_nonneg (mul_nonneg zero_le_two (hχ' _).1)]
    have h1 : (1 - χ (‖φ‖ ^ 2)) * ‖F‖ ≤ ‖F‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hχ (‖φ‖ ^ 2)).1])
    have h2 : 2 * deriv χ (‖φ‖ ^ 2) * ‖Dα.gradientWedge‖ ≤ 2 * M * ‖Dα‖ ^ 2 :=
      mul_le_mul (by linarith [(hχ' (‖φ‖ ^ 2)).2]) Dα.norm_gradientWedge_le (norm_nonneg _)
        (by positivity)
    linarith
  -- The arithmetic: every coefficient is dominated by `C'`, using `√r ≤ r` for `r ≥ 1`.
  have hw : 0 ≤ max (1 - ‖φ‖ ^ 2) 0 := le_max_right _ _
  generalize max (1 - ‖φ‖ ^ 2) 0 = w at hw hplus hFm hDα ⊢
  have hs2 : 1 ≤ √2 := Real.one_le_sqrt.2 one_le_two
  have hq1 : 1 ≤ √r := Real.one_le_sqrt.2 hr
  have hqq : √r * √r = r := Real.mul_self_sqrt (by linarith)
  have hqr : √r ≤ r := by nlinarith
  have hrw : 0 ≤ r * w := mul_nonneg (by linarith) hw
  have e1 : r / (4 * √2) * w ≤ r * w :=
    calc r / (4 * √2) * w = r * w / (4 * √2) := by ring
      _ ≤ r * w := div_le_self hrw (by linarith)
  have e2 : (C + 1) / (2 * √2) ≤ C + 1 := div_le_self (by linarith) (by linarith)
  have e3 : r / (4 * √2) * (1 + C / √r) * w ≤ r * w + C * (r * w) := by
    have hrC : r * (C / √r) = C * √r := by
      rw [mul_div_assoc', div_eq_iff (by positivity)]
      linear_combination -C * hqq
    have hCq : C * √r * w ≤ C * (r * w) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqr hw) hC
    calc r / (4 * √2) * (1 + C / √r) * w = (r + r * (C / √r)) * w / (4 * √2) := by ring
      _ = (r * w + C * √r * w) / (4 * √2) := by rw [hrC]; ring
      _ ≤ r * w + C * √r * w := div_le_self (by positivity) (by linarith)
      _ ≤ r * w + C * (r * w) := by linarith
  have hMD : 2 * M * ‖Dα‖ ^ 2 ≤ 2 * M * (C * r * w + C) :=
    mul_le_mul_of_nonneg_left hDα (by positivity)
  have hCrw : 0 ≤ C * (r * w) := mul_nonneg hC hrw
  have _ : 0 ≤ M * (C * (r * w)) := mul_nonneg hM hCrw
  have hNrw : 0 ≤ N * (r * w) := mul_nonneg hN hrw
  nlinarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **The cutoff current has `r`-independent `L¹` norm.** On a finite measure space `X`,
consider at each point, written in a unitary frame `e` with `J e₀ = e₁`, `J e₂ = e₃`, the fields
of a solution of the large-parameter Seiberg–Witten equations as in
`TauCeti.SeibergWitten.norm_le_mul_max_one_sub_add_of_inner_ιMulti_eq`: the curvature equation
for `F = i F_a` with forcing `‖η‖ ≤ N`, the cutoff current `Θ` of a cutoff `χ` with values in
`[0, 1]` and `0 ≤ χ' ≤ M`, and Taubes's coarse bounds with constant `C ≥ 0`, including
`r ∫ |1 - |φ|² - |β|²| ≤ C` and the coarse anti-self-dual bound. Put
`C' = 2 + 2 C + N + 2 M C`. If `r ≥ 2 C'`, then

`∫ ‖Θ‖ ≤ 2 C' (C' + Vol X)`,

independently of `r` and of the solution. -/
theorem integral_norm_le_of_inner_ιMulti_eq [IsFiniteMeasure μ] {F η Θ : X → ⋀[ℝ]^2 V}
    {φ β : X → positiveHalfSpinors o ρ} {Dα : X → V →L[ℝ] ℂ}
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hCr : 2 * (2 + 2 * C + N + 2 * M * C) ≤ r)
    (hχ : ∀ s, χ s ∈ Icc 0 1) (hχ' : ∀ s, deriv χ s ∈ Icc 0 M)
    (hφ : ∀ᵐ x ∂μ, cliffordProjection o ρ J.kahlerForm (φ x) = φ x)
    (hβ : ∀ᵐ x ∂μ, cliffordProjection o ρ J.kahlerForm (β x) = 0)
    (hF : ∀ᵐ x ∂μ, F x + o.hodgeStar hkl (F x) = (r / 4) • J.kahlerForm -
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 V) - η x)
    (hη : ∀ᵐ x ∂μ, ‖η x‖ ≤ N)
    (hFm : ∀ᵐ x ∂μ, ‖(2⁻¹ : ℝ) • (F x - o.hodgeStar hkl (F x))‖ ≤
      r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C)
    (hΘ : ∀ᵐ x ∂μ, ∀ u w, ⟪Θ x, ιMulti ℝ 2 ![u, w]⟫ =
      (1 - χ (‖φ x‖ ^ 2)) * ⟪F x, ιMulti ℝ 2 ![u, w]⟫ +
        2 * deriv χ (‖φ x‖ ^ 2) * (conj (Dα x u) * Dα x w).im)
    (hδ : Integrable (fun x ↦ 1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2) μ)
    (hL1 : r * ∫ x, |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| ∂μ ≤ C)
    (hφβ : ∀ᵐ x ∂μ, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + C / r)
    (hβK : ∀ᵐ x ∂μ, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖φ x‖ ^ 2) 0 + C / r ^ 2)
    (hDα : ∀ᵐ x ∂μ, ‖Dα x‖ ^ 2 ≤ C * r * max (1 - ‖φ x‖ ^ 2) 0 + C) :
    ∫ x, ‖Θ x‖ ∂μ ≤
      2 * (2 + 2 * C + N + 2 * M * C) * ((2 + 2 * C + N + 2 * M * C) + μ.real univ) := by
  have hM : 0 ≤ M := (hχ' 0).1.trans (hχ' 0).2
  have hr : 1 ≤ r := by nlinarith
  have hr0 : 0 < r := by linarith
  have hCC : C ≤ 2 + 2 * C + N + 2 * M * C := by nlinarith
  refine integral_le_of_le_mul_max_one_sub hr0 (by positivity) hCr hδ (hL1.trans hCC) ?_
    (.of_forall fun x ↦ norm_nonneg _) ?_
  · filter_upwards [hβK] with x hx
    have _ : 0 ≤ max (1 - ‖φ x‖ ^ 2) 0 := le_max_right _ _
    calc ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖φ x‖ ^ 2) 0 + C / r ^ 2 := hx
      _ ≤ _ := by gcongr
  · filter_upwards [hφ, hβ, hF, hη, hFm, hΘ, hφβ, hβK, hDα] with x hφx hβx hFx hηx hFmx hΘx
      hφβx hβKx hDαx
    exact norm_le_mul_max_one_sub_add_of_inner_ιMulti_eq h₀ h₂₃ hQ hkl he hρ h₂ hr hC hχ hχ'
      hφx hβx hFx hηx hFmx hΘx hφβx hβKx hDαx

/-- **The cutoff current of large-parameter solutions has `r`-independent mass.** Work on an
open set `Ω` of finite volume in an oriented four-dimensional inner product space with a constant
unitary frame `e`, `J e₀ = e₁`, `J e₂ = e₃`. Fix constants `C, N ≥ 0` and a cutoff `χ` with
values in `[0, 1]` and `0 ≤ χ' ≤ M`. There are `A` and `r₀` such that for every `r ≥ r₀` and
every solution of the large-parameter curvature equation
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η` on `Ω` satisfying the coarse bounds of
`TauCeti.SeibergWitten.norm_le_mul_max_one_sub_add_of_inner_ιMulti_eq` and
`r ∫_Ω |1 - |φ|² - |β|²| ≤ C`, the current `ζ ↦ ∫ Θ ∧ ζ` of the cutoff current `Θ` on test
two-forms on `Ω` has mass at most `A`. The top-degree coefficients are taken on a basis `b` and
integrated against its Haar measure. Unlike
`TauCeti.SeibergWitten.exists_mass_integral_wedge_le_of_add_hodgeStar_eq`, only the coarse
anti-self-dual bound is assumed. -/
theorem exists_mass_integral_wedge_le_of_inner_ιMulti_eq [MeasurableSpace V] [BorelSpace V]
    (b : Module.Basis (Fin (2 + 2)) ℝ V) {Ω : Opens V} (hΩ : b.addHaar Ω ≠ ⊤) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hχ : ∀ s, χ s ∈ Icc 0 1) (hχ' : ∀ s, deriv χ s ∈ Icc 0 M) :
    ∃ A r₀, ∀ ⦃r : ℝ⦄ ⦃F η Θ : V → ⋀[ℝ]^2 V⦄ ⦃φ β : V → positiveHalfSpinors o ρ⦄
      ⦃Dα : V → V →L[ℝ] ℂ⦄, r₀ ≤ r →
      AEStronglyMeasurable Θ (b.addHaar.restrict Ω) →
      IntegrableOn (fun x ↦ 1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2) Ω b.addHaar →
      r * ∫ x in Ω, |1 - ‖φ x‖ ^ 2 - ‖β x‖ ^ 2| ∂b.addHaar ≤ C →
      (∀ x ∈ Ω, cliffordProjection o ρ J.kahlerForm (φ x) = φ x) →
      (∀ x ∈ Ω, cliffordProjection o ρ J.kahlerForm (β x) = 0) →
      (∀ x ∈ Ω, F x + o.hodgeStar hkl (F x) = (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ x + β x)) : ⋀[ℝ]^2 V) - η x) →
      (∀ x ∈ Ω, ‖η x‖ ≤ N) →
      (∀ x ∈ Ω, ‖(2⁻¹ : ℝ) • (F x - o.hodgeStar hkl (F x))‖ ≤
        r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      (∀ x ∈ Ω, ∀ u w, ⟪Θ x, ιMulti ℝ 2 ![u, w]⟫ =
        (1 - χ (‖φ x‖ ^ 2)) * ⟪F x, ιMulti ℝ 2 ![u, w]⟫ +
          2 * deriv χ (‖φ x‖ ^ 2) * (conj (Dα x u) * Dα x w).im) →
      (∀ x ∈ Ω, ‖φ x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + C / r) →
      (∀ x ∈ Ω, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖φ x‖ ^ 2) 0 + C / r ^ 2) →
      (∀ x ∈ Ω, ‖Dα x‖ ^ 2 ≤ C * r * max (1 - ‖φ x‖ ^ 2) 0 + C) →
      ∀ m : ℕ∞, Distribution.mass (fun ζ : 𝓓^{m}(Ω, V [⋀^Fin 2]→L[ℝ] ℝ) ↦
          ∫ x, wedge (alternatingFormEquiv V 2 (Θ x)) (ζ x) b ∂b.addHaar) ≤ ENNReal.ofReal A := by
  obtain ⟨A, -, hA⟩ :=
    b.exists_mass_integral_wedge_le_of_le_mul_max_one_sub (A := positiveHalfSpinors o ρ)
      (B := positiveHalfSpinors o ρ)
  set C' := 2 + 2 * C + N + 2 * M * C
  have hM : 0 ≤ M := (hχ' 0).1.trans (hχ' 0).2
  have hCC : C ≤ C' := by nlinarith
  refine ⟨A * (C' * (C' + b.addHaar.real Ω)), 2 * C', ?_⟩
  intro r F η Θ φ β Dα hr hΘm hδ hL1 hφ hβ hF hη hFm hΘ hφβ hβK hDα m
  have hr1 : 1 ≤ r := by nlinarith
  refine hA hΩ (by linarith) (by positivity) hr hδ (hL1.trans hCC)
    ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (Filter.Eventually.of_forall fun x hx ↦ ?_))
    ((LinearMap.continuous_of_finiteDimensional
      (alternatingFormEquiv V 2).toLinearMap).comp_aestronglyMeasurable hΘm) (fun x hx ↦ ?_) m
  · have _ : 0 ≤ max (1 - ‖φ x‖ ^ 2) 0 := le_max_right _ _
    calc ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖φ x‖ ^ 2) 0 + C / r ^ 2 := hβK x hx
      _ ≤ C' / r * max (1 - ‖φ x‖ ^ 2) 0 + C' / r ^ 2 := by gcongr
  · exact (norm_alternatingFormEquiv_le _).trans
      (norm_le_mul_max_one_sub_add_of_inner_ιMulti_eq h₀ h₂₃ hQ hkl he hρ h₂ hr1 hC hχ hχ'
        (hφ x hx) (hβ x hx) (hF x hx) (hη x hx) (hFm x hx) (hΘ x hx) (hφβ x hx) (hβK x hx)
        (hDα x hx))

end Cutoff

end TauCeti.SeibergWitten
