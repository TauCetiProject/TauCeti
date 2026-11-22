/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.FlatLimit
public import TauCeti.Analysis.PDE.SeibergWitten.HolomorphicGauge
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.PDE.SeibergWitten.LogModulusRatio
import TauCeti.Data.Fin.VecNotation

/-!
# Confined flat limits are plane vortices

Rescaling a large-parameter Seiberg–Witten solution near a pseudoholomorphic curve at the scale
`h = (2 r)^(-1/2)` produces, in the limit, a solution of the flat equations on
`V = ℂ_base × ℂ_normal` with parameter `r = 1 / 2`. With the spinor on the canonical line,
`χ = α u₀`, and the connection `a = i b` on the line `E`, these equations read

`∑ₖ c(eₖ) ∇_{eₖ} (α u₀) = 0`,  `F + ⋆F = ω / 8 - q(α u₀) / 2`,  `F = i F_a = -db`,

the case `r = 1 / 2` of `TauCeti.Analysis.PDE.SeibergWitten.FlatLimit`, in a positively oriented
unitary frame `e` whose vectors `e₂`, `e₃` span the normal factor. The pullbacks of normalized plane
vortices (`TauCeti.Vortex.equation`) along the normal coordinate `z` solve them
(`TauCeti.SeibergWitten.sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff`). This
file proves Taubes's classification of the solutions arising as such limits: a smooth solution whose
section tends to the vacuum `|α| → 1` as `|z| → ∞`, uniformly along the base, and whose normal
curvature component `db(e₂, e₃)` is bounded, is the gauge transform of the pullback of a smooth
framed plane vortex by a smooth unimodular function
(`TauCeti.SeibergWitten.exists_vortex_norm_eq_one_and_eq_normalConnection_sub_phaseForm`). In
particular it does not depend on the base coordinates up to gauge, and its zero set is the product
of the base with the zero divisor of the vortex.

The proof assembles three steps.

* **Holomorphic gauge.** The Dirac equation is `∂bar_a α = 0`
  (`TauCeti.SeibergWitten.sum_covariantDeriv_smul_ι_apply_eq_zero_iff`) and the curvature equation
  makes `db` invariant under `J`
  (`TauCeti.SeibergWitten.extDeriv_apply_apply_eq_of_add_hodgeStar_eq_smul`).
  Read in the complex coordinates `(z_base, z_normal)` of the frame, where `J` is multiplication by
  `i`, `α` becomes holomorphic in a complex gauge, and its zeros, confined to a bounded normal disc
  by the vacuum condition, are those of the pulled-back section `α'` of a smooth framed plane vortex
  with the same transverse divisor: `α = h · (α' ∘ z)` for a smooth nowhere vanishing `h`
  (`TauCeti.SeibergWitten.exists_vortex_eq_mul_sectionValue_normalCoord`, from
  `TauCeti.SeibergWitten.exists_vortex_contDiff_eq_mul_sectionValue_of_covariantDBar_eq_zero`).
* **Boundedness of the log-modulus ratio.** The curvature of the pulled-back vortex is
  `(|α'|² - 1) / 8`, which lies in `[-1 / 8, 0]`, so the normal curvature components of the two
  connections differ by a bounded function, and both sections satisfy the transverse vacuum
  condition. Hence `log |h|²` is bounded
  (`TauCeti.SeibergWitten.isBounded_range_log_norm_sq_of_eq_mul_sectionValue_normalCoord`, from
  `TauCeti.SeibergWitten.isBounded_range_log_norm_sq_of_abs_extDeriv_sub_le`).
* **Comparison.** Taubes's maximum principle for the log-modulus ratio then gives `|h| = 1` and
  `b = b' - Im (h⁻¹ dh)` for the pulled-back connection `b'` of the vortex
  (`TauCeti.SeibergWitten.norm_eq_one_and_eq_normalConnection_sub_phaseForm`).

The extraction of such a limit from actual large-parameter solutions, with its curvature and
vacuum bounds, is not treated here.

## Main results

* `TauCeti.SeibergWitten.exists_vortex_eq_mul_sectionValue_normalCoord`: a section with
  `∂bar_a α = 0`, for a smooth connection of `J`-invariant curvature, with zeros confined to a
  bounded normal disc, is a smooth nowhere vanishing multiple of the pulled-back section of a
  smooth framed plane vortex with the same transverse divisor.
* `TauCeti.SeibergWitten.isBounded_range_log_norm_sq_of_eq_mul_sectionValue_normalCoord`: the
  log-modulus ratio of such a section to the vortex section is bounded under a bound on the normal
  curvature and the transverse vacuum condition.
* `TauCeti.SeibergWitten.exists_vortex_norm_eq_one_and_eq_normalConnection_sub_phaseForm`: the
  classification of confined flat limits as gauge transforms of pulled-back plane vortices.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 4.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

open exteriorPower

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Complex Filter
open scoped RealInnerProductSpace InnerProductSpace Topology ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

/-! ### Complex coordinates of a unitary frame -/

variable (e) in
/-- The real-linear map `ℂ_base × ℂ_normal → V`,
`(z, w) ↦ Re z e₀ + Im z e₁ + Re w e₂ + Im w e₃`. -/
private def frameMap : ℂ × ℂ →L[ℝ] V :=
  (reCLM.smulRight (e 0) + imCLM.smulRight (e 1)).comp (.fst ℝ ℂ ℂ) +
    (reCLM.smulRight (e 2) + imCLM.smulRight (e 3)).comp (.snd ℝ ℂ ℂ)

private theorem frameMap_apply (p : ℂ × ℂ) :
    frameMap e p = p.1.re • e 0 + p.1.im • e 1 + (p.2.re • e 2 + p.2.im • e 3) := by
  simp [frameMap]

variable (e) in
/-- The inverse coordinates `y ↦ (⟪e₀, y⟫ + i ⟪e₁, y⟫, z(y))` of `frameMap`. -/
private def frameCoord : V →L[ℝ] ℂ × ℂ :=
  ((innerSL ℝ (e 0)).smulRight (1 : ℂ) + (innerSL ℝ (e 1)).smulRight I).prod (normalCoord e)

/-- The second coordinate of `frameCoord e` is the normal coordinate. -/
private theorem frameCoord_apply_snd (y : V) : (frameCoord e y).2 = normalCoord e y :=
  (rfl)

private theorem frameMap_frameCoord (y : V) : frameMap e (frameCoord e y) = y := by
  conv_rhs => rw [← e.sum_repr' y]
  simp [frameMap_apply, frameCoord, Fin.sum_univ_four, add_assoc]

/-- The normal coordinate of `frameMap e (z, w)` is `w`. -/
private theorem normalCoord_frameMap (p : ℂ × ℂ) : normalCoord e (frameMap e p) = p.2 := by
  apply Complex.ext <;> simp [frameMap_apply]

/-- In a unitary frame, `frameMap e` intertwines multiplication by `i` with `J`. -/
private theorem frameMap_I_smul (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (p : ℂ × ℂ) :
    frameMap e (I • p) = J (frameMap e p) := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂₃, J.apply_apply]
  simp only [frameMap_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_re, mul_im, I_re,
    I_im, map_add, map_smul, h₀, h₁, h₂₃, h₃]
  module

/-! ### The holomorphic gauge in a unitary frame -/

section HolomorphicGauge

variable [FiniteDimensional ℝ V] {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : V → ℂ}

/-- **A flat pair with confined zeros is a multiple of a pulled-back plane vortex.** Let `J` have
a unitary frame `e`, `J e₀ = e₁` and `J e₂ = e₃`, let `b` be a smooth connection form whose
curvature is `J`-invariant, `db(J u, J w) = db(u, w)`, and let `α` be a real-differentiable section
with `∂bar_a α = 0`. If `α y ≠ 0` whenever the normal coordinate satisfies `K ≤ |z(y)|`, then there
are a multiset `s` of points of norm less than `K`, a smooth plane vortex `x` with the
degree-`card s` end framing whose section `α'` vanishes exactly at the points of `s`, with their
multiplicities, and a smooth nowhere vanishing `h` with `α = h · (α' ∘ z)`. -/
theorem exists_vortex_eq_mul_sectionValue_normalCoord (h₀ : J (e 0) = e 1)
    (h₂₃ : J (e 2) = e 3) (hb : ContDiff ℝ ∞ b)
    (hJF : ∀ y u w, extDeriv b y ![J u, J w] = extDeriv b y ![u, w])
    (hα : Differentiable ℝ α) (hD : ∀ y, covariantDBar J b α y = 0) {K : ℝ}
    (hK : ∀ y, K ≤ ‖normalCoord e y‖ → α y ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧ ∃ x : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ x ∧ (∀ z, Vortex.equation x z = 0) ∧
      Tendsto (fun z ↦ Vortex.sectionValue x z * ((z / (‖z‖ : ℂ)) ^ Multiset.card s)⁻¹)
        (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (Vortex.sectionValue x) (fun z ↦ s.count z) ∧
      ∃ h : V → ℂ, ContDiff ℝ ∞ h ∧ (∀ y, h y ≠ 0) ∧
        α = h * (Vortex.sectionValue x ∘ normalCoord e) := by
  set Φ := frameMap e
  have hΦJ (v : ℂ × ℂ) : Φ (AlmostComplexStructure.ofComplexModule (ℂ × ℂ) v) = J (Φ v) := by
    rw [AlmostComplexStructure.ofComplexModule_apply, frameMap_I_smul h₀ h₂₃]
  -- Read the pair in the complex coordinates `(z_base, z_normal)` of the frame.
  have hpull : (fun p ↦ (b (Φ p)).compContinuousLinearMap (fderiv ℝ Φ p)) =
      fun p ↦ (b (Φ p)).compContinuousLinearMap Φ := by
    simp only [Φ.fderiv]
  obtain ⟨s, hsK, x, hx, hsol, hframe, hzero, h, hh, hh₀, hαh⟩ :=
    exists_vortex_contDiff_eq_mul_sectionValue_of_covariantDBar_eq_zero
      (b := fun p ↦ (b (Φ p)).compContinuousLinearMap Φ) (α := α ∘ Φ)
      (contDiff_iff_contDiffAt.2 fun p ↦
        contDiffAt_pullback_continuousLinearMap Φ hb.contDiffAt)
      (fun p v w ↦ by
        rw [Φ.extDeriv_pullback (hb.differentiable (by simp) _),
          ContinuousAlternatingMap.compContinuousLinearMap_apply,
          ContinuousAlternatingMap.compContinuousLinearMap_apply, Matrix.comp_vec2,
          Matrix.comp_vec2, frameMap_I_smul h₀ h₂₃, frameMap_I_smul h₀ h₂₃, hJF])
      (hα.comp Φ.differentiable)
      (fun p ↦ by
        rw [← hpull, covariantDBar_comp J _ (hα _) Φ.differentiableAt
          (fun v ↦ by rw [Φ.fderiv]; exact hΦJ v), hD, ContinuousLinearMap.zero_comp])
      (fun y w hw ↦ hK _ (by rwa [normalCoord_frameMap]))
  refine ⟨s, hsK, x, hx, hsol, hframe, hzero, fun y ↦ h (frameCoord e y),
    hh.comp (frameCoord e).contDiff, fun y ↦ hh₀ _, funext fun y ↦ ?_⟩
  have hy := hαh (frameCoord e y)
  rw [Function.comp_apply, frameMap_frameCoord, frameCoord_apply_snd] at hy
  rw [hy, Pi.mul_apply, Function.comp_apply]

end HolomorphicGauge

/-! ### The log-modulus ratio to a pulled-back vortex -/

section LogModulusRatio

variable [FiniteDimensional ℝ V] {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : V → ℂ}
  {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- **The log-modulus ratio to a pulled-back vortex is bounded.** Let `J` have a unitary frame
`e`, `J e₀ = e₁` and `J e₂ = e₃`, and let `(b, α)` satisfy `∂bar_a α = 0` with a differentiable
connection form whose normal curvature component is bounded, `|db(e₂, e₃)| ≤ C`, and with the
transverse vacuum condition `|α| → 1` as `|z| → ∞`, uniformly along the base. Let `x` be a `C²`
plane vortex whose section `α'` satisfies `|α'| → 1` at infinity and is nonzero on a dense set. If
`α = h · (α' ∘ z)` for a nowhere vanishing `C²` function `h`, then the log-modulus ratio `log |h|²`
is bounded. -/
theorem isBounded_range_log_norm_sq_of_eq_mul_sectionValue_normalCoord (h₀ : J (e 0) = e 1)
    (h₂₃ : J (e 2) = e 3) (hb : Differentiable ℝ b) (hD : ∀ y, covariantDBar J b α y = 0)
    {C : ℝ} (hC : ∀ y, |extDeriv b y ![e 2, e 3]| ≤ C)
    (hlim : Tendsto (fun y ↦ ‖α y‖) (comap (fun y ↦ ‖normalCoord e y‖) atTop) (𝓝 1))
    (hx : ContDiff ℝ 2 x) (hsol : ∀ z, Vortex.equation x z = 0)
    (hframe : Tendsto (fun z ↦ ‖Vortex.sectionValue x z‖) (cocompact ℂ) (𝓝 1))
    (hdense : Dense {z | Vortex.sectionValue x z ≠ 0}) {h : V → ℂ} (hh : ContDiff ℝ 2 h)
    (hh₀ : ∀ y, h y ≠ 0) (hα : α = h * (Vortex.sectionValue x ∘ normalCoord e)) :
    Bornology.IsBounded (Set.range fun y ↦ Real.log (‖h y‖ ^ 2)) := by
  have hxd : Differentiable ℝ x := hx.differentiable (by norm_num)
  have hα' : Differentiable ℝ (Vortex.sectionValue x ∘ normalCoord e) := fun y ↦
    (Vortex.differentiableAt_sectionValue_of_differentiableAt (hxd _)).comp y
      (normalCoord e).differentiableAt
  -- The curvature of the vortex is `(|α'|² - 1) / 8`, which lies in `[-1 / 8, 0]`.
  have hcurv (z : ℂ) : |Vortex.curvature x z| ≤ 1 / 8 := by
    have h0 := congrArg (· 0) (hsol z)
    have h1 := Vortex.normSq_le_one_of_tendsto ((contDiff_piLp 2).1 hx 2)
      ((contDiff_piLp 2).1 hx 3) hsol
      (by simpa only [Vortex.sq_norm_sectionValue, one_pow] using hframe.pow 2) z
    simp only [Vortex.equation_apply_zero, PiLp.zero_apply] at h0
    rw [Vortex.curvature_apply, abs_le]
    constructor <;> nlinarith [sq_nonneg (x z 2), sq_nonneg (x z 3)]
  -- Transverse limits along the normal plane are limits as `|z| → ∞`.
  have hfilter : comap (fun y ↦ ‖(Submodule.span ℝ {e 2, J (e 2)}).starProjection y‖) atTop =
      comap (fun y ↦ ‖normalCoord e y‖) atTop := by
    simp only [h₂₃, norm_normalCoord]
  have hz : Tendsto (normalCoord e) (comap (fun y ↦ ‖normalCoord e y‖) atTop) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    exact tendsto_comap
  refine isBounded_range_log_norm_sq_of_abs_extDeriv_sub_le
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃) (e.orthonormal.1 2)
    (C := C + 1 / 8) hb (fun y ↦ differentiableAt_normalConnection (hxd _)) hh hα' hh₀ hα
    (hdense.preimage ((normalCoord e).isOpenMap normalCoord_surjective)) hD
    (fun y ↦ (covariantDBar_normalConnection_eq_zero_iff h₀ h₂₃ (hxd _)).2
      ⟨by simp [hsol], by simp [hsol]⟩)
    (fun y ↦ ?_) (hfilter ▸ hlim) (hfilter ▸ (hframe.comp hz))
  rw [h₂₃, extDeriv_normalConnection_apply_two_three (hxd _)]
  exact (abs_sub _ _).trans (add_le_add (hC y) (hcurv _))

end LogModulusRatio

/-! ### The classification of confined flat limits -/

section Classification

variable [Fact (finrank ℝ V = 4)]

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1)
  (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
  (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
  {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {α : V → ℂ}

include hkl he h₀ h₂₃ hQ h₂ hρ hu₀ hu₀₁ in
/-- **Confined flat limits are plane vortices up to gauge.** Let `e` be a positively oriented
unitary frame of `V = ℂ_base × ℂ_normal`, `J e₀ = e₁` and `J e₂ = e₃`, and `u₀` a unit spinor of
the canonical line. Let `(b, α u₀)` be a smooth solution of the flat limiting equations

`∑ₖ c(eₖ) ∇_{eₖ} (α u₀) = 0`,  `F + ⋆F = ω / 8 - q(α u₀) / 2`,  `F = -db`,

whose normal curvature component is bounded, `|db(e₂, e₃)| ≤ C`, and whose section satisfies the
transverse vacuum condition `|α| → 1` as `|z| → ∞`, uniformly along the base. Then there are a
multiset `s` and a smooth plane vortex `x` with the degree-`card s` end framing, whose section `α'`
vanishes exactly at the points of `s`, with their multiplicities, and a smooth function `h` with
`|h| = 1` such that `α = h · (α' ∘ z)` and `b = b' - Im (h⁻¹ dh)`, where `b'` is the connection of
`x` pulled back along the normal coordinate `z`: the solution is the gauge transform by `h` of the
base-independent pullback of a plane vortex. -/
theorem exists_vortex_norm_eq_one_and_eq_normalConnection_sub_phaseForm (hb : ContDiff ℝ ∞ b)
    (hα : Differentiable ℝ α)
    (hD : ∀ y, ∑ k, covariantDeriv b α y (e k) • ρ (ι Q (e k)) u₀ = 0)
    (hF : ∀ y, (alternatingFormEquiv V 2).symm (-extDeriv b y) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b y)) =
      (1 / 8 : ℝ) • J.kahlerForm -
        (1 / 2 : ℝ) • (quadraticTwoForm o ρ hkl (α y • u₀) : ⋀[ℝ]^2 V))
    {C : ℝ} (hC : ∀ y, |extDeriv b y ![e 2, e 3]| ≤ C)
    (hlim : Tendsto (fun y ↦ ‖α y‖) (comap (fun y ↦ ‖normalCoord e y‖) atTop) (𝓝 1)) :
    ∃ s : Multiset ℂ, ∃ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x ∧
      (∀ z, Vortex.equation x z = 0) ∧
      Tendsto (fun z ↦ Vortex.sectionValue x z * ((z / (‖z‖ : ℂ)) ^ Multiset.card s)⁻¹)
        (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (Vortex.sectionValue x) (fun z ↦ s.count z) ∧
      ∃ h : V → ℂ, ContDiff ℝ ∞ h ∧ (∀ y, ‖h y‖ = 1) ∧
        α = h * (Vortex.sectionValue x ∘ normalCoord e) ∧
        b = normalConnection e x - phaseForm h := by
  have hu₀' : (u₀ : W) ≠ 0 := by
    have hu : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀₁
    simpa using hu
  -- The curvature equation in the form of `FlatLimit`, at `r = 1 / 2`.
  have hF' (y : V) : (alternatingFormEquiv V 2).symm (-extDeriv b y) +
      o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b y)) =
        ((1 / 2 : ℝ) / 4) • J.kahlerForm -
          (quadraticTwoForm o ρ hkl (((√(1 / 2 : ℝ) : ℝ) : ℂ) • (α y • u₀)) : ⋀[ℝ]^2 V) := by
    rw [quadraticTwoForm_sqrt_smul o ρ hkl (by norm_num), Submodule.coe_smul, hF y]
    norm_num
  have hdbar (y : V) : covariantDBar J b α y = 0 :=
    (sum_covariantDeriv_smul_ι_apply_eq_zero_iff hQ hkl he h₀ h₂₃ hρ hu₀ hu₀' b α y).1 (hD y)
  -- The curvature is `J`-invariant, since its self-dual part is a multiple of `ω`.
  have hJF (y u w : V) : extDeriv b y ![J u, J w] = extDeriv b y ![u, w] := by
    have hP : cliffordProjection o ρ J.kahlerForm (α y • u₀) = α y • u₀ := by
      rw [map_smul, hu₀]
    have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
    exact extDeriv_apply_apply_eq_of_add_hodgeStar_eq_smul hkl he h₀ h₂₃
      ((add_hodgeStar_eq_sub_quadraticTwoForm_iff hQ hkl hω h₂ hρ (by norm_num) hP _).1
        (hF' y)) u w
  -- The vacuum condition confines the zeros of `α` to a bounded normal disc.
  obtain ⟨R, -, hR⟩ := (atTop_basis.comap fun y ↦ ‖normalCoord e y‖).tendsto_left_iff.1 hlim
    (Metric.ball 1 1) (Metric.ball_mem_nhds 1 one_pos)
  obtain ⟨s, -, x, hx, hsol, hframe, hzero, h, hh, hh₀, hαh⟩ :=
    exists_vortex_eq_mul_sectionValue_normalCoord h₀ h₂₃ hb hJF hα hdbar (K := R)
      fun y hy hαy ↦ by simpa [hαy] using hR (Set.mem_Ici.2 hy)
  -- The vortex section tends to unit modulus at infinity.
  have hnorm : Tendsto (fun z ↦ ‖Vortex.sectionValue x z‖) (cocompact ℂ) (𝓝 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp
      (Vortex.tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
    rw [Real.sqrt_one] at h
    refine h.congr fun z ↦ ?_
    rw [Function.comp_apply, ← Vortex.sq_norm_sectionValue, Real.sqrt_sq (norm_nonneg _)]
  have hdense : Dense {z | Vortex.sectionValue x z ≠ 0} := by
    classical
    refine (dense_univ.sdiff_finset s.toFinset).mono fun z hz ↦ ?_
    simpa [← hzero.eq_zero_iff, Multiset.count_eq_zero] using hz
  have hbdd := isBounded_range_log_norm_sq_of_eq_mul_sectionValue_normalCoord h₀ h₂₃
    (hb.differentiable (by simp)) hdbar hC hlim (hx.of_le (by simp)) hsol hnorm hdense
    (hh.of_le (by simp)) hh₀ hαh
  obtain ⟨h1, hbh⟩ := norm_eq_one_and_eq_normalConnection_sub_phaseForm hkl he h₀ h₂₃ hQ h₂ hρ hu₀
    hu₀₁ (by norm_num) (hb.differentiable (by simp)) hD hF' (hx.differentiable (by simp))
    (fun z ↦ by norm_num [hsol z]) hdense hnorm
    (hh.of_le (by simp)) hh₀ hαh hbdd hlim
  exact ⟨s, x, hx, hsol, hframe, hzero, h, hh, h1, hαh, hbh⟩

end Classification

end TauCeti.SeibergWitten
