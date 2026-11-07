/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
public import TauCeti.LinearAlgebra.CliffordAlgebra.Kahler
import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor

/-!
# Clifford multiplication on the canonical line of an almost Hermitian four-space

Let `V` be an oriented real inner product space of dimension four with an orthogonal complex
structure `J` inducing the orientation, witnessed by a positively oriented unitary frame
`(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and `J e₂ = e₃`, and let `ω` be its Kähler form. Let `W` be a
Hermitian Clifford module, `c(v) = ρ (ι Q v)` with `Q v = -‖v‖²`, and `W⁺` its positive
half-spinors. Taubes writes a positive spinor as `ψ = α u₀ + β`, where `u₀` spans the
`-2i`-eigenline of `c₂(ω)` in `W⁺`, the range of the projection `P_α`
(`TauCeti.SeibergWitten.cliffordProjection`), and `β` lies in the complementary `2i`-eigenline.

On the canonical line, Clifford multiplication turns `J` into multiplication by `i`: if
`P_α ψ = ψ` then `c(J v) ψ = i c(v) ψ`, while on the complementary line `c(J v) β = -i c(v) β`.
Both follow from the commutator `⁅c₂(ω), c(v)⁆ = 2 c(J v)`
(`TauCeti.AlmostComplexStructure.bivectorExterior_kahlerForm_lie_ι`) and the vanishing of the
self-dual form `ω` on the negative half-spinors, where `c(v) ψ` lies. Consequently
`⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`, so `v ↦ c(v) ψ` is a complex-linear map from
`(V, J)` to the negative half-spinors, isometric up to the factor `‖ψ‖`.

This is the pointwise symbol of Taubes's identity `D_A(α u₀) = √2 ∂bar_a α + α D_A u₀`. Write the
symbol of the Dirac operator on a complex-valued covector with components `x_k`, such as the
covariant derivative `x_k = (∇_a α)(e_k)`, as `∑ₖ x_k c(e_k) ψ`. Then

`∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ`,
`‖∑ₖ x_k c(e_k) ψ‖² = (|x₀ + i x₁|² + |x₂ + i x₃|²) ‖ψ‖²`.

The factors `x₀ + i x₁` and `x₂ + i x₃` are twice the `∂bar`-derivatives in the complex
coordinates of the planes `⟨e₀, e₁⟩` and `⟨e₂, e₃⟩`. In particular, for `ψ ≠ 0` the symbol
vanishes exactly when the real-linear covector `L` with `x_k = L e_k` is complex linear,
`L (J v) = i L v`: Clifford multiplication of `α u₀` sees only `∂bar_a α`. This is the pointwise
algebra by which, for fields on `ℂ × ℂ` that depend only on the normal factor `⟨e₂, e₃⟩`, the
Dirac equation on the canonical line becomes the holomorphicity equation `∂bar_a α = 0` of the
plane vortex equations, in the convention `∂bar_a α = (∇₁ α + i ∇₂ α) / 2` of
`TauCeti.Vortex.equation`. No differential operator is constructed here.

## Main results

* `TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`: `c(J v) ψ = i c(v) ψ`
  for `P_α ψ = ψ`, and `TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_zero`:
  `c(J v) β = -i c(v) β` for `P_α β = 0`.
* `TauCeti.SeibergWitten.inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self`:
  `⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_of_cliffordProjection_apply_eq_self`: the Dirac symbol
  on the canonical line in terms of the two `∂bar`-components.
* `TauCeti.SeibergWitten.norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self`: its
  norm.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self` and
  `TauCeti.SeibergWitten.sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self`:
  it vanishes exactly when both `∂bar`-components vanish, that is when the covector is complex
  linear.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-! ### `J` acts by `±i` on the two lines -/

omit [FiniteDimensional ℂ W] in
include hQ hkl he h₀ h₂ in
/-- On a `μ`-eigenvector `ψ ∈ W⁺` of `c₂(ω)`, Clifford multiplication intertwines `J` with the
scalar `-μ / 2`: `2 c(J v) ψ = -μ c(v) ψ`. Indeed `c(v) ψ` is a negative half-spinor, on which
the self-dual form `ω` acts by zero, so `⁅c₂(ω), c(v)⁆ = 2 c(J v)` gives
`2 c(J v) ψ = -c(v) c₂(ω) ψ`. -/
private theorem two_smul_ι_apply_apply_of_bivectorExterior_apply {ψ : positiveHalfSpinors o ρ}
    {μ : ℂ} (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = μ • (ψ : W)) (v : V) :
    (2 : ℂ) • ρ (ι Q (J v)) ψ = -μ • ρ (ι Q v) ψ := by
  -- `c(v) ψ` is a negative half-spinor.
  have hneg : ρ (chirality Q o) (ρ (ι Q v) ψ) = -ρ (ι Q v) ψ := by
    simpa using map_ι_apply_mem_eigenspace_chirality_neg o (ε := 1)
      (by simpa using mem_positiveHalfSpinors.1 ψ.2) v
  -- The self-dual form `ω` annihilates it.
  have hzero : ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q v) ψ) = 0 := by
    have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he
    have h : ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q v) ψ) =
        -ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q v) ψ) := by
      conv_lhs => rw [← bivectorExterior_mul_chirality_of_hodgeStar_eq_self o hQ hkl hω, map_mul,
        mul_apply_eq_comp, hneg, map_neg]
    rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ, smul_eq_zero] at h
    exact h.resolve_left two_ne_zero
  have h := congrArg (fun a ↦ ρ a ψ)
    (AlmostComplexStructure.bivectorExterior_kahlerForm_lie_ι hQ h₀ h₂ v)
  simp only [Ring.lie_def, map_sub, map_mul, LinearMap.sub_apply, mul_apply_eq_comp, hψ,
    hzero, map_smul, LinearMap.smul_apply] at h
  linear_combination (norm := module) -h

include hQ hkl he h₀ h₂ in
/-- **On the canonical line, Clifford multiplication turns `J` into `i`**: if `P_α ψ = ψ`, then
`c(J v) ψ = i c(v) ψ`. -/
theorem ι_apply_apply_of_cliffordProjection_apply_eq_self {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (v : V) :
    ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ := by
  have h := two_smul_ι_apply_apply_of_bivectorExterior_apply hQ hkl he h₀ h₂
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hψ) v
  linear_combination (norm := module) (2⁻¹ : ℂ) • h

include hQ hkl he h₀ h₂ in
/-- On the complementary line, Clifford multiplication turns `J` into `-i`: if `P_α β = 0`, then
`c(J v) β = -i c(v) β`. -/
theorem ι_apply_apply_of_cliffordProjection_apply_eq_zero {β : positiveHalfSpinors o ρ}
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0) (v : V) :
    ρ (ι Q (J v)) β = -Complex.I • ρ (ι Q v) β := by
  -- `C(iω) β = -2 β` says `c₂(ω) β = 2 i β`.
  have hc := congrArg Subtype.val ((cliffordProjection_apply_eq_zero_iff o ρ).1 hβ)
  rw [coe_cliffordRestriction_apply, Submodule.coe_smul] at hc
  have hω : ρ (bivectorExterior Q J.kahlerForm) β = (2 * Complex.I) • (β : W) := by
    calc ρ (bivectorExterior Q J.kahlerForm) β =
          (-Complex.I) • (Complex.I • ρ (bivectorExterior Q J.kahlerForm) β) := by
          rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      _ = (2 * Complex.I) • (β : W) := by
          rw [hc, smul_smul]
          congr 1
          ring
  have h := two_smul_ι_apply_apply_of_bivectorExterior_apply hQ hkl he h₀ h₂ hω v
  linear_combination (norm := module) (2⁻¹ : ℂ) • h

/-! ### The Hermitian structure of `v ↦ c(v) ψ` -/

include hQ hkl he h₀ h₂ in
/-- On the canonical line, `v ↦ c(v) ψ` is a complex-linear isometric map from `(V, J)` up to the
factor `‖ψ‖`: `⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`. -/
theorem inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (v w : V) :
    ⟪ρ (ι Q v) ψ, ρ (ι Q w) ψ⟫_ℂ = ((⟪v, w⟫ : ℂ) - ⟪v, J w⟫ * Complex.I) * ‖(ψ : W)‖ ^ 2 := by
  have hre (v w : V) : (⟪ρ (ι Q v) ψ, ρ (ι Q w) ψ⟫_ℂ).re = ⟪v, w⟫ * ‖(ψ : W)‖ ^ 2 := by
    rw [re_inner_map_ι_apply_map_ι_apply hρ]
    simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
    ring
  -- The imaginary part is the real part for `J w`, since `c(J w) ψ = i c(w) ψ`.
  have him : (⟪ρ (ι Q v) ψ, ρ (ι Q w) ψ⟫_ℂ).im = -⟪v, J w⟫ * ‖(ψ : W)‖ ^ 2 := by
    have h := hre v (J w)
    rw [ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hψ, inner_smul_right,
      Complex.mul_re, Complex.I_re, Complex.I_im] at h
    linarith
  apply Complex.ext <;> simp [hre, him, ← Complex.ofReal_pow]

/-! ### The Dirac symbol on the canonical line -/

include hQ hkl he h₀ h₂ in
/-- **Clifford multiplication of a complex covector on the canonical line**: if `P_α ψ = ψ`, then
`∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ`. Only the two `∂bar`-components
`x₀ + i x₁` and `x₂ + i x₃` of the covector survive. -/
theorem sum_smul_ι_apply_of_cliffordProjection_apply_eq_self {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (x : Fin 4 → ℂ) :
    ∑ k, x k • ρ (ι Q (e k)) ψ =
      (x 0 + Complex.I * x 1) • ρ (ι Q (e 0)) ψ + (x 2 + Complex.I * x 3) • ρ (ι Q (e 2)) ψ := by
  have h₁ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hψ (e 0)
  have h₃ := ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hψ (e 2)
  rw [h₀] at h₁
  rw [h₂] at h₃
  rw [Fin.sum_univ_four, h₁, h₃]
  module

include hQ hkl he h₀ h₂ in
/-- The norm of the Dirac symbol on the canonical line:
`‖∑ₖ x_k c(e_k) ψ‖² = (|x₀ + i x₁|² + |x₂ + i x₃|²) ‖ψ‖²`. -/
theorem norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (x : Fin 4 → ℂ) :
    ‖∑ k, x k • ρ (ι Q (e k)) ψ‖ ^ 2 =
      (‖x 0 + Complex.I * x 1‖ ^ 2 + ‖x 2 + Complex.I * x 3‖ ^ 2) * ‖(ψ : W)‖ ^ 2 := by
  -- `c(e₀) ψ` and `c(e₂) ψ` are orthogonal of norm `‖ψ‖`.
  have horth : ⟪ρ (ι Q (e 0)) ψ, ρ (ι Q (e 2)) ψ⟫_ℂ = 0 := by
    rw [inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hψ, h₂,
      e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
    simp
  have hnorm (k : Fin 4) : ‖ρ (ι Q (e k)) ψ‖ = ‖(ψ : W)‖ := by
    rw [norm_map_ι_apply hQ hρ, e.orthonormal.1 k, one_mul]
  rw [sum_smul_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hψ,
    norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, horth]
  simp only [mul_zero, RCLike.zero_re, add_zero, norm_smul, hnorm]
  ring

include hQ hkl he h₀ h₂ in
/-- **The Dirac symbol on the canonical line vanishes exactly on `∂bar`-closed covectors**: for
`P_α ψ = ψ`, `∑ₖ x_k c(e_k) ψ = 0` if and only if `ψ = 0` or `x₀ + i x₁ = x₂ + i x₃ = 0`. -/
theorem sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (x : Fin 4 → ℂ) :
    ∑ k, x k • ρ (ι Q (e k)) ψ = 0 ↔
      (ψ : W) = 0 ∨ (x 0 + Complex.I * x 1 = 0 ∧ x 2 + Complex.I * x 3 = 0) := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff,
    norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hψ,
    mul_eq_zero, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp only [sq_eq_zero_iff, norm_eq_zero]
  tauto

include hQ hkl he h₀ h₂ in
/-- **The Dirac symbol on the canonical line sees only `∂bar`**: for `P_α ψ = ψ` and a real-linear
complex covector `L`, such as a covariant derivative `∇_a α` at a point,
`∑ₖ L(e_k) c(e_k) ψ = 0` if and only if `ψ = 0` or `L` is complex linear for `J`,
`L (J v) = i L v`. -/
theorem sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (L : V →ₗ[ℝ] ℂ) :
    ∑ k, L (e k) • ρ (ι Q (e k)) ψ = 0 ↔ (ψ : W) = 0 ∨ ∀ v, L (J v) = Complex.I * L v := by
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (e 3) = -e 2 := by rw [← h₂, J.apply_apply]
  rw [sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hψ
    (fun k ↦ L (e k))]
  refine or_congr_right ⟨fun ⟨h01, h23⟩ v ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · -- `L` commutes with `J` on the frame, hence everywhere.
    have key (i : Fin 4) : L (J (e i)) = Complex.I * L (e i) := by
      fin_cases i
      · simp only [Fin.zero_eta, h₀]
        linear_combination (-Complex.I) * h01 + L (e 1) * Complex.I_sq
      · simp only [Fin.mk_one, h₁, map_neg]
        linear_combination -h01
      · simp only [Fin.reduceFinMk, h₂]
        linear_combination (-Complex.I) * h23 + L (e 3) * Complex.I_sq
      · simp only [Fin.reduceFinMk, h₃, map_neg]
        linear_combination -h23
    have hv := e.sum_repr' v
    calc L (J v) = ∑ i, ⟪e i, v⟫ • L (J (e i)) := by
          conv_lhs => rw [← hv]
          simp only [map_sum, map_smul]
      _ = Complex.I * L v := by
          conv_rhs => rw [← hv]
          simp only [map_sum, map_smul, key, Finset.mul_sum, Complex.real_smul, mul_left_comm]
  · have h0 := h (e 0)
    rw [h₀] at h0
    linear_combination Complex.I * h0 + L (e 0) * Complex.I_sq
  · have h2 := h (e 2)
    rw [h₂] at h2
    linear_combination Complex.I * h2 + L (e 2) * Complex.I_sq

end TauCeti.SeibergWitten
