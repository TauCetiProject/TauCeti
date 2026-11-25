/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.Analysis.Distribution.TestFunction.Lp
public import TauCeti.LinearAlgebra.LinearPMap.Shift
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointMaximal
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The momentum operator on the half-line

For a real `ℏ`, the momentum operator `P φ = iℏ φ'` on the Hilbert space `L²(0, ∞)`, with domain
the test functions `C_c^∞(0, ∞)`, is `TauCeti.halfLineMomentum ℏ`. It is densely defined and, by
integration by parts, symmetric. For `ℏ > 0` it is the standard example of a symmetric operator
whose deficiency indices differ. Writing `P†` for its adjoint, the deficiency spaces are

* `ker (P† - i) = 0`: a solution of `iℏ u' = i u` is `u = e^{q/ℏ} v`, which is not
  square-integrable on `(0, ∞)` unless `v = 0`;
* `ker (P† + i) = ℂ e^{-q/ℏ}`: the solutions of `iℏ u' = -i u` are square-integrable.

So the deficiency indices are `(0, 1)`. A self-adjoint extension `B` of `P` would satisfy
`B ≤ P†`, and the surjectivity of `i - B` would force the two deficiency spaces to vanish together
(`IsSelfAdjoint.ker_subScalar_adjoint_conj_eq_bot`). Hence `P` has no self-adjoint extension; in
particular its closure is not self-adjoint, that is, `P` is not essentially self-adjoint.

The elements of the domain of `P†` are only `L²` functions. Tested against real test functions,
the equation `P† u = c ℏ i u` says that `u` is a distributional solution of `u' = c u` on `(0, ∞)`,
and the du Bois-Reymond lemma identifies these solutions with the functions `e^{c q} v`.

In geometric quantization with the prequantum operators `Q_f = iℏ ∇_{X_f} + f`, the operator `P`
is the momentum `p` acting on the vertically polarized sections over the cotangent bundle of the
half-line, written as functions of the position `q > 0`. The Hamiltonian flow of `p` translates
`q` and leaves the half-line in finite time, and `P` shows that essential self-adjointness of
prequantum operators can fail when the Hamiltonian flow is incomplete.

## Main declarations

* `TauCeti.halfLineMomentum ℏ`: the operator `φ ↦ iℏ φ'` on `L²(0, ∞)` with domain `C_c^∞(0, ∞)`.
* `TauCeti.mem_domain_halfLineMomentum_iff`, `TauCeti.halfLineMomentum_apply` and
  `TauCeti.coeFn_halfLineMomentum_apply`: its domain and values.
* `TauCeti.dense_domain_halfLineMomentum`, `TauCeti.isFormalAdjoint_halfLineMomentum`: it is
  densely defined and symmetric.
* `TauCeti.ker_subScalar_I_adjoint_halfLineMomentum_eq_bot`: the deficiency space `ker (P† - i)`
  is `0`.
* `TauCeti.halfLineMomentumDeficiencyVector`: the class of `e^{-q/ℏ}` in `L²(0, ∞)`, with
  squared norm `ℏ / 2` (`TauCeti.norm_halfLineMomentumDeficiencyVector_sq`).
* `TauCeti.mem_ker_subScalar_neg_I_adjoint_halfLineMomentum_iff`,
  `TauCeti.ker_subScalar_neg_I_adjoint_halfLineMomentum_eq_span` and
  `TauCeti.finrank_ker_subScalar_neg_I_adjoint_halfLineMomentum`: the deficiency space
  `ker (P† + i)` consists of the multiples of `e^{-q/ℏ}`, and is a line.
* `TauCeti.not_isSelfAdjoint_of_halfLineMomentum_le` and
  `TauCeti.not_isSelfAdjoint_closure_halfLineMomentum`: `P` has no self-adjoint extension, and is
  not essentially self-adjoint.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*, Academic Press (1975), Section X.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set Filter TopologicalSpace Complex
open scoped ContDiff Distributions InnerProductSpace ComplexConjugate LinearPMap LineDeriv

/-- The open half-line `(0, ∞)`, as an open subset of `ℝ`. -/
local notation "Ω₊" => Opens.mk (Ioi (0 : ℝ)) isOpen_Ioi

/-- The Hilbert space `L²(0, ∞)`. -/
local notation "L²₊" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- The class in `L²(0, ∞)` of a test function on `(0, ∞)`, as a `ℂ`-linear map. -/
local notation "ι₊" =>
  ((TestFunction.ambientToLp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) : 𝓓(Ω₊, ℂ) →L[ℂ] L²₊) :
    𝓓(Ω₊, ℂ) →ₗ[ℂ] L²₊)

/-! ### Test functions on the half-line in `L²` -/

/-- The `L²(0, ∞)` pairing with the class of a test function. -/
private theorem inner_ambientToLp_Ioi (φ : 𝓓(Ω₊, ℂ)) (u : L²₊) :
    ⟪ι₊ φ, u⟫_ℂ = ∫ x in Ioi 0, conj (φ x) * u x := by
  rw [ContinuousLinearMap.coe_coe, TestFunction.inner_ambientToLp_left]
  simp_rw [RCLike.inner_apply']

/-- Pairing with a real function vanishing off `(0, ∞)` is an integral over the whole line. -/
private theorem setIntegral_conj_ofReal_mul {h : ℝ → ℝ} (hh : ∀ x ∉ Ioi (0 : ℝ), h x = 0)
    (f : ℝ → ℂ) : ∫ x in Ioi 0, conj ((h x : ℂ)) * f x = ∫ x, h x • f x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [hh x hx]]
  simp_rw [conj_ofReal, real_smul]

/-- A real test function on `(0, ∞)`, viewed as a complex test function, has the same values. -/
private theorem postcompCLM_ofRealCLM_apply (g : 𝓓(Ω₊, ℝ)) (x : ℝ) :
    TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM g x = g x := by
  rw [TestFunction.postcompCLM_apply, Function.comp_apply, ofRealCLM_apply]

/-! ### The operator -/

/-- The operator `φ ↦ iℏ φ'` on the test functions on `(0, ∞)`. -/
private def momentumTest (ℏ : ℝ) : 𝓓(Ω₊, ℂ) →ₗ[ℂ] 𝓓(Ω₊, ℂ) :=
  (I * ℏ) • (TestFunction.lineDerivCLM ℂ (1 : ℝ) : 𝓓(Ω₊, ℂ) →L[ℂ] 𝓓(Ω₊, ℂ)).toLinearMap

private theorem momentumTest_apply (ℏ : ℝ) (φ : 𝓓(Ω₊, ℂ)) :
    momentumTest ℏ φ = (I * ℏ) • ∂_{(1 : ℝ)} φ :=
  (rfl)

private theorem momentumTest_apply_apply (ℏ : ℝ) (φ : 𝓓(Ω₊, ℂ)) (x : ℝ) :
    momentumTest ℏ φ x = I * ℏ * deriv φ x := by
  rw [momentumTest_apply, smul_apply, TestFunction.lineDerivOp_one_apply_eq_deriv,
    smul_eq_mul]

/-- **The momentum operator on the half-line**: the operator `φ ↦ iℏ φ'` on `L²(0, ∞)`, with
domain the classes of the test functions on `(0, ∞)`. -/
def halfLineMomentum (ℏ : ℝ) : L²₊ →ₗ.[ℂ] L²₊ where
  domain := LinearMap.range ι₊
  toFun := ι₊ ∘ₗ momentumTest ℏ ∘ₗ
    (LinearEquiv.ofInjective ι₊ TestFunction.ambientToLp_restrict_injective).symm.toLinearMap

variable {ℏ : ℝ}

/-- The domain of the half-line momentum consists of the classes of test functions on
`(0, ∞)`. -/
theorem mem_domain_halfLineMomentum_iff {u : L²₊} :
    u ∈ (halfLineMomentum ℏ).domain ↔
      ∃ φ : 𝓓(Ω₊, ℂ), TestFunction.ambientToLp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) φ = u := by
  simp only [halfLineMomentum, LinearMap.mem_range, ContinuousLinearMap.coe_coe]

/-- The class of a test function on `(0, ∞)` lies in the domain of the half-line momentum. -/
@[simp]
theorem ambientToLp_mem_domain_halfLineMomentum (φ : 𝓓(Ω₊, ℂ)) :
    TestFunction.ambientToLp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) φ ∈ (halfLineMomentum ℏ).domain :=
  mem_domain_halfLineMomentum_iff.2 ⟨φ, rfl⟩

private theorem mem_domain_halfLineMomentum_iff_ι {u : L²₊} :
    u ∈ (halfLineMomentum ℏ).domain ↔ ∃ φ : 𝓓(Ω₊, ℂ), ι₊ φ = u :=
  Iff.rfl

private theorem halfLineMomentum_ambientToLp (φ : 𝓓(Ω₊, ℂ)) :
    halfLineMomentum ℏ ⟨ι₊ φ, ⟨φ, rfl⟩⟩ = ι₊ (momentumTest ℏ φ) := by
  have h : (LinearEquiv.ofInjective ι₊ TestFunction.ambientToLp_restrict_injective).symm
      ⟨ι₊ φ, ⟨φ, rfl⟩⟩ = φ :=
    (LinearEquiv.ofInjective ι₊ TestFunction.ambientToLp_restrict_injective).symm_apply_apply φ
  simp only [halfLineMomentum, LinearPMap.mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, h]

private theorem halfLineMomentum_eq {x : (halfLineMomentum ℏ).domain} {φ : 𝓓(Ω₊, ℂ)}
    (hx : (x : L²₊) = ι₊ φ) : halfLineMomentum ℏ x = ι₊ (momentumTest ℏ φ) := by
  obtain ⟨x, hx'⟩ := x
  subst hx
  exact halfLineMomentum_ambientToLp φ

/-- The half-line momentum sends the class of a test function `φ` to the class of `iℏ φ'`. -/
@[simp]
theorem halfLineMomentum_apply (φ : 𝓓(Ω₊, ℂ)) :
    halfLineMomentum ℏ ⟨_, ambientToLp_mem_domain_halfLineMomentum φ⟩ =
      TestFunction.ambientToLp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) ((I * ℏ) • ∂_{(1 : ℝ)} φ) := by
  rw [halfLineMomentum_eq (φ := φ) (by simp), ContinuousLinearMap.coe_coe, momentumTest_apply]

/-- A representative of the half-line momentum of the class of a test function `φ` is
`q ↦ iℏ φ'(q)`. -/
theorem coeFn_halfLineMomentum_apply (φ : 𝓓(Ω₊, ℂ)) :
    halfLineMomentum ℏ ⟨_, ambientToLp_mem_domain_halfLineMomentum φ⟩ =ᵐ[volume.restrict
      (Ioi (0 : ℝ))] fun q ↦ I * ℏ * deriv φ q := by
  filter_upwards [TestFunction.coeFn_ambientToLp (𝕜 := ℂ) (p := 2) (momentumTest ℏ φ)] with q hq
  rw [← momentumTest_apply_apply, ← hq, halfLineMomentum_eq (φ := φ) (by simp),
    ContinuousLinearMap.coe_coe]

/-- The half-line momentum is densely defined: an `L²(0, ∞)` function orthogonal to every test
function vanishes. -/
theorem dense_domain_halfLineMomentum :
    Dense ((halfLineMomentum ℏ).domain : Set L²₊) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  refine Lp.eq_zero_iff_ae_eq_zero.mpr <| (ae_restrict_iff' measurableSet_Ioi).mpr <|
    isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (Lp.locallyIntegrableOn u (by norm_num)) fun g hg hgc hgs ↦ ?_
  set φ : 𝓓(Ω₊, ℂ) := TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM ⟨g, hg, hgc, hgs⟩
  have hφ (x : ℝ) : φ x = g x := postcompCLM_ofRealCLM_apply _ x
  have h := (Submodule.mem_orthogonal _ _).mp hu (ι₊ φ) ⟨_, rfl⟩
  simp only [inner_ambientToLp_Ioi, hφ] at h
  rwa [setIntegral_conj_ofReal_mul fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs h)] at h

/-! ### Symmetry -/

/-- **Integration by parts against a test function on `(0, ∞)`.** -/
private theorem setIntegral_conj_deriv_mul (φ : 𝓓(Ω₊, ℂ)) {h h' : ℝ → ℂ}
    (hh : ∀ x, HasDerivAt h (h' x) x) (hh' : Continuous h') :
    ∫ x in Ioi 0, conj (deriv φ x) * h x = -∫ x in Ioi 0, conj (φ x) * h' x := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun x ↦ (hh x).continuousAt
  have hdc : Continuous (deriv φ) := φ.contDiff.continuous_deriv (by simp)
  have hcφ (x : ℝ) : HasDerivAt (fun x ↦ conj (φ x)) (conj (deriv φ x)) x :=
    (φ.contDiff.differentiable (by simp) x).hasDerivAt.star
  have hs : HasCompactSupport fun x ↦ conj (φ x) := φ.hasCompactSupport.comp_left (map_zero _)
  have hs' : HasCompactSupport fun x ↦ conj (deriv φ x) :=
    φ.hasCompactSupport.deriv.comp_left (map_zero _)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (u' := h')
    (v := fun x ↦ conj (φ x)) (v' := fun x ↦ conj (deriv φ x)) (fun x _ ↦ hh x)
    (fun x _ ↦ hcφ x)
    ((hhc.mul (continuous_conj.comp hdc)).integrable_of_hasCompactSupport hs'.mul_left)
    ((hh'.mul (continuous_conj.comp φ.continuous)).integrable_of_hasCompactSupport hs.mul_left)
    ((hhc.mul (continuous_conj.comp φ.continuous)).integrable_of_hasCompactSupport hs.mul_left)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp [deriv_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)]]
  simpa only [mul_comm (h _), mul_comm (h' _)] using key

private theorem inner_ambientToLp_Ioi_ambientToLp (φ ψ : 𝓓(Ω₊, ℂ)) :
    ⟪ι₊ φ, ι₊ ψ⟫_ℂ = ∫ x in Ioi 0, conj (φ x) * ψ x := by
  rw [inner_ambientToLp_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [TestFunction.coeFn_ambientToLp (𝕜 := ℂ) (p := 2) ψ] with x hx
  rw [ContinuousLinearMap.coe_coe, hx]

/-- The half-line momentum is symmetric, by integration by parts. -/
theorem isFormalAdjoint_halfLineMomentum :
    (halfLineMomentum ℏ).IsFormalAdjoint (halfLineMomentum ℏ) := by
  rintro ⟨_, hφ⟩ ⟨_, hψ⟩
  obtain ⟨φ, rfl⟩ := mem_domain_halfLineMomentum_iff_ι.mp hφ
  obtain ⟨ψ, rfl⟩ := mem_domain_halfLineMomentum_iff_ι.mp hψ
  simp only [halfLineMomentum_ambientToLp, inner_ambientToLp_Ioi_ambientToLp,
    momentumTest_apply_apply, map_mul, conj_I, conj_ofReal]
  have hψ (x : ℝ) : HasDerivAt ψ (deriv ψ x) x :=
    (ψ.contDiff.differentiable (by simp) x).hasDerivAt
  have hparts := setIntegral_conj_deriv_mul φ hψ (ψ.contDiff.continuous_deriv (by simp))
  calc ∫ x in Ioi 0, -I * ℏ * conj (deriv φ x) * ψ x
      = -I * ℏ * ∫ x in Ioi 0, conj (deriv φ x) * ψ x := by
        rw [← integral_const_mul]; simp only [mul_assoc]
    _ = ∫ x in Ioi 0, conj (φ x) * (I * ℏ * deriv ψ x) := by
        rw [hparts, ← integral_neg, ← integral_const_mul]
        congr 1; ext x; ring

/-! ### The deficiency spaces -/

/-- If `P† u = c ℏ i u`, then `u` is a distributional solution of `u' = c u` on `(0, ∞)`. -/
private theorem integral_deriv_add_mul_smul_eq_zero (hℏ : ℏ ≠ 0) {c : ℝ} {u : L²₊}
    (hu : u ∈ (halfLineMomentum ℏ)†.domain)
    (hAu : (halfLineMomentum ℏ)† ⟨u, hu⟩ = ((c : ℂ) * ℏ * I) • u) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioi 0) :
    ∫ x, (deriv g x + c * g x) • u x = 0 := by
  set φ : 𝓓(Ω₊, ℂ) := TestFunction.postcompCLM (𝕜 := ℝ) ofRealCLM ⟨g, hg, hgc, hgs⟩
  have hφg (x : ℝ) : φ x = g x := postcompCLM_ofRealCLM_apply _ x
  have hsymm : ⟪ι₊ (momentumTest ℏ φ), u⟫_ℂ = ⟪ι₊ φ, ((c : ℂ) * ℏ * I) • u⟫_ℂ := by
    rw [← halfLineMomentum_ambientToLp, ← hAu]
    exact (LinearPMap.adjoint_isFormalAdjoint dense_domain_halfLineMomentum).symm
      ⟨ι₊ φ, ⟨φ, rfl⟩⟩ ⟨u, hu⟩
  -- The class of `iℏ (φ' + c φ)` is orthogonal to `u`.
  have h0 : ⟪ι₊ (momentumTest ℏ φ + ((I * ℏ * c : ℂ)) • φ), u⟫_ℂ = 0 := by
    rw [map_add, map_smul, inner_add_left, inner_smul_left, hsymm, inner_smul_right]
    simp only [map_mul, conj_I, conj_ofReal]
    ring
  have hφ (x : ℝ) : deriv φ x = deriv g x :=
    ((hg.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  rw [inner_ambientToLp_Ioi] at h0
  have hval (x : ℝ) : conj ((momentumTest ℏ φ + ((I * ℏ * c : ℂ)) • φ) x) * u x =
      -I * ℏ * (conj (((deriv g x + c * g x : ℝ)) : ℂ) * u x) := by
    rw [add_apply, smul_apply, momentumTest_apply_apply, hφ]
    simp only [hφg, smul_eq_mul, map_add, map_mul, conj_I, conj_ofReal, ofReal_add,
      ofReal_mul]
    ring
  simp_rw [hval] at h0
  rw [integral_const_mul, setIntegral_conj_ofReal_mul fun x hx ↦ by
    simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgs h),
      deriv_of_notMem_tsupport fun h ↦ hx (hgs h)]] at h0
  exact (mul_eq_zero.mp h0).resolve_left (by simp [hℏ])

/-- **The deficiency space `ker (P† - i)` of the half-line momentum vanishes.** A solution of
`iℏ u' = i u` on `(0, ∞)` is a multiple of `e^{q/ℏ}`, which is square-integrable only if it is
zero. -/
theorem ker_subScalar_I_adjoint_halfLineMomentum_eq_bot (hℏ : 0 < ℏ) :
    ((halfLineMomentum ℏ)†.subScalar I).ker = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  obtain ⟨hu, hAu⟩ := LinearPMap.mem_ker_subScalar_iff.mp hu
  obtain ⟨v, hv⟩ := (Lp.locallyIntegrableOn u (by norm_num)
    ).exists_ae_eq_exp_smul_Ioi_of_integral_deriv_add_mul_smul_eq_zero ℏ⁻¹
      (integral_deriv_add_mul_smul_eq_zero hℏ.ne' hu (by
        rw [hAu, ofReal_inv, inv_mul_cancel₀ (ofReal_ne_zero.2 hℏ.ne'), one_mul]))
  have hv0 : v = 0 := by
    by_contra hne
    have hmem : MemLp (fun _ : ℝ ↦ v) 2 (volume.restrict (Ioi (0 : ℝ))) := by
      refine (Lp.memLp u).mono aestronglyMeasurable_const ?_
      filter_upwards [hv, ae_restrict_mem measurableSet_Ioi] with x hx hx0
      rw [hx, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact le_mul_of_one_le_left (norm_nonneg v)
        (Real.one_le_exp (mul_nonneg (inv_nonneg.2 hℏ.le) (le_of_lt hx0)))
    rw [memLp_const_iff two_ne_zero ENNReal.ofNat_ne_top] at hmem
    simp [hne, Real.volume_Ioi] at hmem
  refine Lp.eq_zero_iff_ae_eq_zero.mpr (hv.trans (Eventually.of_forall fun x ↦ ?_))
  simp [hv0]

/-- The decaying exponential `q ↦ e^{-q/ℏ}` and its derivative. -/
private theorem hasDerivAt_ofReal_exp_neg_div (x : ℝ) :
    HasDerivAt (fun q : ℝ ↦ (Real.exp (-q / ℏ) : ℂ)) (-ℏ⁻¹ * Real.exp (-x / ℏ) : ℝ) x := by
  exact ((hasDerivAt_neg x).div_const ℏ).exp.ofReal_comp.congr_deriv (by congr 1; ring)

/-- Pairing the momentum of a test function with a multiple of `e^{-q/ℏ}`: integration by parts
turns `⟪iℏ φ', e^{-q/ℏ} v⟫` into `⟪φ, -i e^{-q/ℏ} v⟫`. -/
private theorem inner_ambientToLp_Ioi_momentumTest_of_ae_eq (hℏ : ℏ ≠ 0) {u : L²₊} {v : ℂ}
    (hv : u =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun q ↦ Real.exp (-q / ℏ) • v)
    (φ : 𝓓(Ω₊, ℂ)) : ⟪ι₊ (momentumTest ℏ φ), u⟫_ℂ = ⟪ι₊ φ, (-I) • u⟫_ℂ := by
  rw [inner_smul_right, inner_ambientToLp_Ioi, inner_ambientToLp_Ioi]
  have hparts := setIntegral_conj_deriv_mul φ hasDerivAt_ofReal_exp_neg_div
    (continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_neg.div_const ℏ))))
  have h1 : ∫ x in Ioi 0, conj (momentumTest ℏ φ x) * u x =
      -I * ℏ * v * ∫ x in Ioi 0, conj (deriv φ x) * (Real.exp (-x / ℏ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hv] with x hx
    rw [hx, momentumTest_apply_apply, real_smul]
    simp only [map_mul, conj_I, conj_ofReal]
    ring
  have h2 : ∫ x in Ioi 0, conj (φ x) * u x =
      v * ∫ x in Ioi 0, conj (φ x) * (Real.exp (-x / ℏ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hv] with x hx
    rw [hx, real_smul]
    ring
  have h3 : ∫ x in Ioi 0, conj (φ x) * ((-ℏ⁻¹ * Real.exp (-x / ℏ) : ℝ) : ℂ) =
      -ℏ⁻¹ * ∫ x in Ioi 0, conj (φ x) * (Real.exp (-x / ℏ) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    ext x
    push_cast
    ring
  have hℏ' : (ℏ : ℂ) ≠ 0 := ofReal_ne_zero.2 hℏ
  rw [h1, h2, hparts, h3]
  push_cast
  field_simp

/-- **The deficiency space `ker (P† + i)` of the half-line momentum** consists of the multiples
of the square-integrable function `e^{-q/ℏ}`, the solutions of `iℏ u' = -i u` on `(0, ∞)`. -/
theorem mem_ker_subScalar_neg_I_adjoint_halfLineMomentum_iff (hℏ : 0 < ℏ) {u : L²₊} :
    u ∈ ((halfLineMomentum ℏ)†.subScalar (-I)).ker ↔
      ∃ v : ℂ, u =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun q ↦ Real.exp (-q / ℏ) • v := by
  constructor
  · intro hu
    obtain ⟨hu, hAu⟩ := LinearPMap.mem_ker_subScalar_iff.mp hu
    obtain ⟨v, hv⟩ := (Lp.locallyIntegrableOn u (by norm_num)
      ).exists_ae_eq_exp_smul_Ioi_of_integral_deriv_add_mul_smul_eq_zero (-ℏ⁻¹)
        (integral_deriv_add_mul_smul_eq_zero hℏ.ne' hu (by
          rw [hAu, ofReal_neg, ofReal_inv, neg_mul, inv_mul_cancel₀ (ofReal_ne_zero.2 hℏ.ne'),
            neg_one_mul]))
    refine ⟨v, hv.trans (Eventually.of_forall fun q ↦ ?_)⟩
    beta_reduce
    rw [show -ℏ⁻¹ * q = -q / ℏ by ring]
  · rintro ⟨v, hv⟩
    have hcond : ∀ x : (halfLineMomentum ℏ).domain,
        ⟪(-I) • u, (x : L²₊)⟫_ℂ = ⟪u, halfLineMomentum ℏ x⟫_ℂ := by
      rintro ⟨_, hφ⟩
      obtain ⟨φ, rfl⟩ := mem_domain_halfLineMomentum_iff_ι.mp hφ
      rw [halfLineMomentum_ambientToLp, ← inner_conj_symm,
        ← inner_ambientToLp_Ioi_momentumTest_of_ae_eq hℏ.ne' hv, inner_conj_symm]
    have hdom : u ∈ (halfLineMomentum ℏ)†.domain :=
      LinearPMap.mem_adjoint_domain_of_exists u ⟨_, hcond⟩
    exact LinearPMap.mem_ker_subScalar_iff.mpr
      ⟨hdom, LinearPMap.adjoint_apply_eq dense_domain_halfLineMomentum _ hcond⟩

private theorem memLp_ofReal_exp_neg_div (hℏ : 0 < ℏ) :
    MemLp (fun q : ℝ ↦ (Real.exp (-q / ℏ) : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).2 ?_
  refine (exp_neg_integrableOn_Ioi 0 (by positivity : (0 : ℝ) < 2 / ℏ)).congr_fun
    (fun x _ ↦ ?_) measurableSet_Ioi
  beta_reduce
  rw [norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
  congr 1
  ring

/-- **The deficiency vector of the half-line momentum**: for `ℏ > 0`, the class in `L²(0, ∞)` of
the decaying exponential `q ↦ e^{-q/ℏ}`, which spans the deficiency space `ker (P† + i)`. -/
def halfLineMomentumDeficiencyVector (hℏ : 0 < ℏ) : L²₊ :=
  (memLp_ofReal_exp_neg_div hℏ).toLp _

/-- A representative of the deficiency vector of the half-line momentum is `q ↦ e^{-q/ℏ}`. -/
theorem coeFn_halfLineMomentumDeficiencyVector (hℏ : 0 < ℏ) :
    halfLineMomentumDeficiencyVector hℏ =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun q ↦ (Real.exp (-q / ℏ) : ℂ) :=
  (memLp_ofReal_exp_neg_div hℏ).coeFn_toLp

/-- The squared `L²(0, ∞)` norm of the deficiency vector `e^{-q/ℏ}` of the half-line momentum
is `ℏ / 2`. -/
theorem norm_halfLineMomentumDeficiencyVector_sq (hℏ : 0 < ℏ) :
    ‖halfLineMomentumDeficiencyVector hℏ‖ ^ 2 = ℏ / 2 := by
  rw [halfLineMomentumDeficiencyVector, MemLp.norm_toLp_sq]
  have h (x : ℝ) : ‖(Real.exp (-x / ℏ) : ℂ)‖ ^ 2 = Real.exp (-(2 / ℏ) * x) := by
    rw [norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
    congr 1
    ring
  simp_rw [h]
  rw [integral_exp_mul_Ioi (by simpa using hℏ) 0]
  field_simp
  simp

/-- The deficiency vector of the half-line momentum is nonzero. -/
theorem halfLineMomentumDeficiencyVector_ne_zero (hℏ : 0 < ℏ) :
    halfLineMomentumDeficiencyVector hℏ ≠ 0 := by
  intro he0
  have h := (coeFn_halfLineMomentumDeficiencyVector hℏ).symm.trans
    (Lp.eq_zero_iff_ae_eq_zero.mp he0)
  have : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot :=
    ae_restrict_neBot.2 (by simp [Real.volume_Ioi])
  obtain ⟨x, hx⟩ := h.exists
  exact ofReal_ne_zero.2 (Real.exp_pos _).ne' hx

/-- **The deficiency space `ker (P† + i)` of the half-line momentum** is the line spanned by the
deficiency vector `e^{-q/ℏ}`. -/
theorem ker_subScalar_neg_I_adjoint_halfLineMomentum_eq_span (hℏ : 0 < ℏ) :
    ((halfLineMomentum ℏ)†.subScalar (-I)).ker = ℂ ∙ halfLineMomentumDeficiencyVector hℏ := by
  ext u
  rw [mem_ker_subScalar_neg_I_adjoint_halfLineMomentum_iff hℏ, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, Lp.ext ?_⟩
    filter_upwards [Lp.coeFn_smul v (halfLineMomentumDeficiencyVector hℏ),
      coeFn_halfLineMomentumDeficiencyVector hℏ, hv] with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2, h3, smul_eq_mul, real_smul, mul_comm]
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    filter_upwards [Lp.coeFn_smul v (halfLineMomentumDeficiencyVector hℏ),
      coeFn_halfLineMomentumDeficiencyVector hℏ] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, real_smul, mul_comm]

/-- **The deficiency space `ker (P† + i)` of the half-line momentum is a line.** Together with
`ker_subScalar_I_adjoint_halfLineMomentum_eq_bot`, the deficiency indices are `(0, 1)`. -/
theorem finrank_ker_subScalar_neg_I_adjoint_halfLineMomentum (hℏ : 0 < ℏ) :
    Module.finrank ℂ ((halfLineMomentum ℏ)†.subScalar (-I)).ker = 1 := by
  rw [ker_subScalar_neg_I_adjoint_halfLineMomentum_eq_span hℏ,
    finrank_span_singleton (halfLineMomentumDeficiencyVector_ne_zero hℏ)]

/-- **The half-line momentum has no self-adjoint extension**: its deficiency spaces
`ker (P† - i) = 0` and `ker (P† + i) ≅ ℂ` would have to vanish together. -/
theorem not_isSelfAdjoint_of_halfLineMomentum_le (hℏ : 0 < ℏ) {B : L²₊ →ₗ.[ℂ] L²₊}
    (hB : halfLineMomentum ℏ ≤ B) : ¬ IsSelfAdjoint B := fun hBs ↦ by
  have h := hBs.ker_subScalar_adjoint_conj_eq_bot hB dense_domain_halfLineMomentum (c := I)
    (by simp) (ker_subScalar_I_adjoint_halfLineMomentum_eq_bot hℏ)
  have h1 := finrank_ker_subScalar_neg_I_adjoint_halfLineMomentum hℏ
  rw [← conj_I, h, finrank_bot] at h1
  exact zero_ne_one h1

/-- **The half-line momentum is not essentially self-adjoint**: its closure is not
self-adjoint. -/
theorem not_isSelfAdjoint_closure_halfLineMomentum (hℏ : 0 < ℏ) :
    ¬ IsSelfAdjoint (halfLineMomentum ℏ).closure :=
  not_isSelfAdjoint_of_halfLineMomentum_le hℏ (halfLineMomentum ℏ).le_closure

end TauCeti
