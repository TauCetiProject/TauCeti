/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
public import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
public import TauCeti.LinearAlgebra.CliffordAlgebra.Kahler
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Clifford multiplication on the canonical line of an almost Hermitian four-space

Let `V` be an oriented real inner product space of dimension four with an orthogonal complex
structure `J` inducing the orientation, witnessed by a positively oriented unitary frame
`(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and `J e₂ = e₃`, and let `ω` be its Kähler form. Let `W` be a
Hermitian Clifford module, `c(v) = ρ (ι Q v)` with `Q v = -‖v‖²`, and `W⁺` its positive
half-spinors. Taubes writes a positive spinor as `ψ = α u₀ + β`, where `u₀` spans the
`-2i`-eigenspace of `c₂(ω)` in `W⁺`, the range of the projection `P_α`
(`TauCeti.SeibergWitten.cliffordProjection`), and `β` lies in the complementary `2i`-eigenspace.
When `W` is a spin module, so that `W⁺` has complex dimension two, both eigenspaces are lines: the
canonical line and its complement. The results below hold on the eigenspaces of any Hermitian
Clifford module.

On the `-2i`-eigenspace, Clifford multiplication turns `J` into multiplication by `i`: if
`P_α ψ = ψ` then `c(J v) ψ = i c(v) ψ`, while on the complementary eigenspace
`c(J v) β = -i c(v) β`.
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

In addition, given a canonical half-spinor `u₀`, this file constructs the anti-canonical partner
`v₀ = c(e₀) c(e₂) u₀` (`TauCeti.SeibergWitten.antiCanonicalSpinor`), verifies its `W⁺` Clifford,
projection, orthogonality, and basis expansion identities, proves the diagonal and cross-term
polarization identities for `quadraticTwoFormPolar` on `(u₀, v₀)`, and records the orthogonal frame
`(c(e₂) u₀, c(e₀) u₀)` of `W⁻`.

## Main results

* `TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`: `c(J v) ψ = i c(v) ψ`
  for `P_α ψ = ψ`, and `TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_zero`:
  `c(J v) β = -i c(v) β` for `P_α β = 0`.
* `TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_self_iff` and
  `TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_zero_iff`: conversely, these
  relations cut out the two eigenspaces.
* `TauCeti.SeibergWitten.inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self`:
  `⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_of_cliffordProjection_apply_eq_self`: the Dirac symbol
  on the canonical eigenspace in terms of the two `∂bar`-components.
* `TauCeti.SeibergWitten.norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self`: its
  norm.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self` and
  `TauCeti.SeibergWitten.sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self`:
  it vanishes exactly when both `∂bar`-components vanish, that is when the covector is complex
  linear.
* `TauCeti.SeibergWitten.antiCanonicalSpinor`: `v₀ = c(e₀) c(e₂) u₀ ∈ W⁺`, with norm preservation
  (`norm_antiCanonicalSpinor`), eigenvalue `2i` (`bivectorExterior_kahlerForm_antiCanonicalSpinor`),
  orthogonality (`inner_antiCanonicalSpinor_eq_zero`), action of `cliffordRestriction` on
  `antiInvariantSelfDual₁` and `antiInvariantSelfDual₂`, and orthogonal expansion in `W⁺`
  (`eq_inner_smul_add_inner_antiCanonicalSpinor_smul`).
* `TauCeti.SeibergWitten.smul_quadraticTwoFormPolar_smul_smul_of_cliffordProjection_apply_eq_self`
  and `TauCeti.SeibergWitten.smul_quadraticTwoFormPolar_smul_antiCanonicalSpinor`: diagonal and
  cross-term polarization identities along `(u₀, v₀)`.
* `TauCeti.SeibergWitten.inner_halfSpinCliffordMul_two_zero` and
  `TauCeti.SeibergWitten.eq_inner_halfSpinCliffordMul`: orthogonality and expansion along the `W⁻`
  frame `(c(e₂) u₀, c(e₀) u₀)`.

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

open CliffordAlgebra Module exteriorPower
open scoped RealInnerProductSpace InnerProductSpace

section CanonicalEigenspace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-! ### `J` acts by `±i` on the two eigenspaces -/

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
      (by simpa using mem_positiveHalfSpinors.1 ψ.property) v
  -- The self-dual form `ω` annihilates it, for the Clifford action on `W` through `ρ`.
  have hzero : ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q v) ψ) = 0 :=
    letI := Module.compHom W ρ.toRingHom
    bivectorExterior_smul_eq_zero_of_hodgeStar_eq_self o hQ hkl
      (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he) hneg
  have h := congrArg (fun a ↦ ρ a ψ) (AlmostComplexStructure.bivectorExterior_kahlerForm_lie_ι hQ
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) v)
  simp only [Ring.lie_def, map_sub, map_mul, LinearMap.sub_apply, mul_apply_eq_comp, hψ,
    hzero, map_smul, LinearMap.smul_apply] at h
  linear_combination (norm := module) -h

include hQ hkl he h₀ h₂ in
/-- **On the canonical eigenspace, Clifford multiplication turns `J` into `i`**: if
`P_α ψ = ψ`, then `c(J v) ψ = i c(v) ψ`. -/
theorem ι_apply_apply_of_cliffordProjection_apply_eq_self {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (v : V) :
    ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ := by
  have h := two_smul_ι_apply_apply_of_bivectorExterior_apply hQ hkl he h₀ h₂
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hψ) v
  linear_combination (norm := module) (2⁻¹ : ℂ) • h

include hQ hkl he h₀ h₂ in
/-- On the complementary eigenspace, Clifford multiplication turns `J` into `-i`: if
`P_α β = 0`, then `c(J v) β = -i c(v) β`. -/
theorem ι_apply_apply_of_cliffordProjection_apply_eq_zero {β : positiveHalfSpinors o ρ}
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0) (v : V) :
    ρ (ι Q (J v)) β = -Complex.I • ρ (ι Q v) β := by
  have h := two_smul_ι_apply_apply_of_bivectorExterior_apply hQ hkl he h₀ h₂
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_zero o ρ hβ) v
  linear_combination (norm := module) (2⁻¹ : ℂ) • h

/-! ### The Hermitian structure of `v ↦ c(v) ψ` -/

include hQ hkl he h₀ h₂ in
/-- On the canonical eigenspace, `v ↦ c(v) ψ` is a complex-linear isometric map from `(V, J)` up
to the factor `‖ψ‖`: `⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`. -/
theorem inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (v w : V) :
    ⟪ρ (ι Q v) ψ, ρ (ι Q w) ψ⟫_ℂ = ((⟪v, w⟫ : ℂ) - ⟪v, J w⟫ * Complex.I) * ‖(ψ : W)‖ ^ 2 := by
  have hre (v w : V) : (⟪ρ (ι Q v) ψ, ρ (ι Q w) ψ⟫_ℂ).re = ⟪v, w⟫ * ‖(ψ : W)‖ ^ 2 := by
    rw [re_inner_map_ι_apply_map_ι_apply hρ, QuadraticMap.polar_eq_neg_two_inner hQ]
    ring
  -- The imaginary part is the real part for `J w`, since `c(J w) ψ = i c(w) ψ`.
  have him : (⟪ρ (ι Q v) ψ, ρ (ι Q w) ψ⟫_ℂ).im = -⟪v, J w⟫ * ‖(ψ : W)‖ ^ 2 := by
    have h := hre v (J w)
    rw [ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hψ, inner_smul_right,
      Complex.mul_re, Complex.I_re, Complex.I_im] at h
    linarith
  apply Complex.ext <;> simp [hre, him, ← Complex.ofReal_pow]

/-! ### The Dirac symbol on the canonical eigenspace -/

include hQ hkl he h₀ h₂ in
/-- **Clifford multiplication of a complex covector on the canonical eigenspace**: if
`P_α ψ = ψ`, then `∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ`. Only the two
`∂bar`-components `x₀ + i x₁` and `x₂ + i x₃` of the covector survive. -/
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
/-- The norm of the Dirac symbol on the canonical eigenspace:
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
/-- **The Dirac symbol on the canonical eigenspace vanishes exactly on `∂bar`-closed
covectors**: for `P_α ψ = ψ`, `∑ₖ x_k c(e_k) ψ = 0` if and only if `ψ = 0` or
`x₀ + i x₁ = x₂ + i x₃ = 0`. -/
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
/-- **The Dirac symbol on the canonical eigenspace sees only `∂bar`**: for `P_α ψ = ψ` and a
real-linear complex covector `L`, such as a covariant derivative `∇_a α` at a point,
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

/-! ### The eigenspaces are cut out by `J` -/

include hQ he h₀ h₂ in
/-- Splitting `ψ = P_α ψ + (ψ - P_α ψ)` along the two eigenspaces, on which `J` acts by `i` and
`-i`: `c(J e₀) ψ = i c(e₀) (P_α ψ) - i c(e₀) (ψ - P_α ψ)`. -/
private theorem ι_apply_apply_eq_sub_of_cliffordProjection (ψ : positiveHalfSpinors o ρ) :
    ρ (ι Q (J (e 0))) ψ =
      Complex.I • ρ (ι Q (e 0)) (cliffordProjection o ρ J.kahlerForm ψ) -
        Complex.I • ρ (ι Q (e 0))
          (ψ - cliffordProjection o ρ J.kahlerForm ψ : positiveHalfSpinors o ρ) := by
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  set P := cliffordProjection o ρ J.kahlerForm
  have hP : IsIdempotentElem P := isIdempotentElem_cliffordProjection o ρ hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he)
    (AlmostComplexStructure.norm_kahlerForm_sq_eq_two
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂))
  have hφ : P (P ψ) = P ψ := by rw [← mul_apply_eq_comp, hP.eq]
  have hβ : P (ψ - P ψ) = 0 := by rw [map_sub, hφ, sub_self]
  have hψ : (ψ : W) = (P ψ : W) + ((ψ - P ψ : positiveHalfSpinors o ρ) : W) := by simp
  conv_lhs => rw [hψ]
  rw [map_add, ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hφ (e 0),
    ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂ hβ (e 0), neg_smul,
    ← sub_eq_add_neg]

omit [FiniteDimensional ℂ W] in
include hQ in
/-- Clifford multiplication by the unit vector `e₀` is injective: `(2i) c(e₀) φ = 0` forces
`φ = 0`. -/
private theorem eq_zero_of_two_mul_I_smul_ι_apply_eq_zero {φ : positiveHalfSpinors o ρ}
    (h : (2 * Complex.I) • ρ (ι Q (e 0)) φ = 0) : φ = 0 :=
  Submodule.coe_eq_zero.1 ((injective_iff_map_eq_zero _).1
    (map_ι_injective ρ (Q := Q) (v := e 0) (by simp [hQ, e.orthonormal.1 0])) _
    ((smul_eq_zero.1 h).resolve_left (by simp)))

include hQ he h₀ h₂ in
/-- **The canonical eigenspace is cut out by `J`**: a positive half-spinor `ψ` is fixed by `P_α`
exactly when Clifford multiplication turns `J` into `i` on it, `c(J v) ψ = i c(v) ψ` for every
`v`. -/
theorem cliffordProjection_kahlerForm_apply_eq_self_iff {ψ : positiveHalfSpinors o ρ} :
    cliffordProjection o ρ J.kahlerForm ψ = ψ ↔
      ∀ v, ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ := by
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  refine ⟨fun hψ ↦ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hψ,
    fun h ↦ ?_⟩
  -- `c(e₀)` kills the component `ψ - P_α ψ` in the complementary eigenspace.
  have h0 : ψ - cliffordProjection o ρ J.kahlerForm ψ = 0 := by
    refine eq_zero_of_two_mul_I_smul_ι_apply_eq_zero hQ (e := e) ?_
    have h₃ := ι_apply_apply_eq_sub_of_cliffordProjection hQ he h₀ h₂ ψ
    rw [h (e 0)] at h₃
    simp only [Submodule.coe_sub, map_sub] at h₃ ⊢
    linear_combination (norm := module) h₃
  exact (sub_eq_zero.1 h0).symm

include hQ he h₀ h₂ in
/-- **The complementary eigenspace is cut out by `J`**: a positive half-spinor `β` is killed by
`P_α` exactly when Clifford multiplication turns `J` into `-i` on it, `c(J v) β = -i c(v) β` for
every `v`. -/
theorem cliffordProjection_kahlerForm_apply_eq_zero_iff {β : positiveHalfSpinors o ρ} :
    cliffordProjection o ρ J.kahlerForm β = 0 ↔
      ∀ v, ρ (ι Q (J v)) β = -Complex.I • ρ (ι Q v) β := by
  have hkl : 2 + 2 = finrank ℝ V := (Fact.out : finrank ℝ V = 4).symm
  refine ⟨fun hβ ↦ ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂ hβ,
    fun h ↦ ?_⟩
  -- `c(e₀)` kills the component `P_α β` in the canonical eigenspace.
  refine eq_zero_of_two_mul_I_smul_ι_apply_eq_zero hQ (e := e) ?_
  have h₃ := ι_apply_apply_eq_sub_of_cliffordProjection hQ he h₀ h₂ β
  rw [h (e 0)] at h₃
  simp only [Submodule.coe_sub, map_sub] at h₃
  linear_combination (norm := module) -h₃

end CanonicalEigenspace

/-! ### The anti-canonical spinor `v₀ = c(e₀) c(e₂) u₀` and half-spinor frames -/

section SpinorFrame

open Complex
open scoped ComplexConjugate

section AntiCanonicalAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V}

attribute [local instance] finiteDimensional_of_finrank_four

variable (o ρ e) in
/-- The **anti-canonical positive half-spinor** `v₀ = c(e₀) c(e₂) u₀` associated to `u₀ ∈ W⁺`. -/
def antiCanonicalSpinor (u₀ : positiveHalfSpinors o ρ) : positiveHalfSpinors o ρ :=
  ⟨ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀), by
    rw [mem_positiveHalfSpinors]
    have h₁ := map_ι_apply_mem_eigenspace_chirality_neg o (ε := 1)
      (Module.End.mem_eigenspace_iff.2 (by simpa using mem_positiveHalfSpinors.1 u₀.property))
        (e 2)
    simpa using Module.End.mem_eigenspace_iff.1
      (map_ι_apply_mem_eigenspace_chirality_neg o (ε := -1) h₁ (e 0))⟩

/-- Ambient Clifford-module value of `antiCanonicalSpinor`. -/
@[simp]
theorem coe_antiCanonicalSpinor (u₀ : positiveHalfSpinors o ρ) :
    (antiCanonicalSpinor o ρ e u₀ : W) = ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) :=
  (rfl)

/-- Clifford action of `e₀` on `v₀ = c(e₀) c(e₂) u₀`: `c(e₀) v₀ = -c(e₂) u₀`. -/
theorem ι_apply_zero_antiCanonicalSpinor (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 0)) (antiCanonicalSpinor o ρ e u₀) = -ρ (ι Q (e 2)) u₀ := by
  rw [coe_antiCanonicalSpinor, map_ι_apply_map_ι_apply_of_norm_eq_one hQ (e.orthonormal.1 0)]

/-- Clifford action of `e₂` on `v₀ = c(e₀) c(e₂) u₀`: `c(e₂) v₀ = c(e₀) u₀`. -/
theorem ι_apply_two_antiCanonicalSpinor (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 2)) (antiCanonicalSpinor o ρ e u₀) = ρ (ι Q (e 0)) u₀ := by
  rw [coe_antiCanonicalSpinor,
    map_ι_apply_comm_of_inner_eq_zero hQ (e.orthonormal.2 (by decide : (2 : Fin 4) ≠ 0)),
    map_ι_apply_map_ι_apply_of_norm_eq_one hQ (e.orthonormal.1 2), map_neg, neg_neg]

end AntiCanonicalAlgebra

section CliffordRelations

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)

attribute [local instance] finiteDimensional_of_finrank_four

include hQ

/-- `antiCanonicalSpinor` preserves the norm when vector Clifford action is skew-adjoint. -/
theorem norm_antiCanonicalSpinor (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (u₀ : positiveHalfSpinors o ρ) :
    ‖antiCanonicalSpinor o ρ e u₀‖ = ‖u₀‖ := by
  rw [← Submodule.norm_coe, coe_antiCanonicalSpinor, norm_map_ι_apply hQ hρ, norm_map_ι_apply hQ hρ,
    e.orthonormal.1 0, e.orthonormal.1 2, one_mul, one_mul, Submodule.norm_coe]

/-- Polarization of `quadraticTwoForm` along a unit canonical spinor `u₀`: pairing `α • u₀` with
`δα • u₀` gives `(Re(conj α * δα) / 4) • ω_u`. -/
theorem smul_quadraticTwoFormPolar_smul_smul_of_cliffordProjection_apply_eq_self
    {hkl : 2 + 2 = finrank ℝ V} (hω : o.hodgeStar hkl J.kahlerForm = J.kahlerForm)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (α δα : ℂ) :
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (α • u₀) (δα • u₀) =
      ((conj α * δα).re / 4) • J.kahlerSelfDual o hkl hω := by
  have hq (c : ℂ) : ((√2 / 4 : ℝ) • quadraticTwoForm o ρ hkl (c • u₀) : ⋀[ℝ]^2 V) =
      (‖c‖ ^ 2 / 8) • (J.kahlerSelfDual o hkl hω : ⋀[ℝ]^2 V) := by
    rw [coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω h₂ hρ
      (by rw [map_smul, hu₀]), norm_smul, hu₀₁, mul_one,
      AlmostComplexStructure.coe_kahlerSelfDual, smul_smul, smul_smul]
    congr 1; ring
  have hpol : quadraticTwoFormPolar o ρ hkl (α • u₀) (δα • u₀) =
      quadraticTwoForm o ρ hkl ((α + δα) • u₀) -
        quadraticTwoForm o ρ hkl (α • u₀) - quadraticTwoForm o ρ hkl (δα • u₀) := by
    rw [add_smul, quadraticTwoForm_add]; abel
  apply Subtype.ext
  rw [hpol]
  simp only [smul_sub, Submodule.coe_sub, Submodule.coe_smul, hq, ← sub_smul]; congr 1
  simp [← normSq_eq_norm_sq, normSq_apply]; ring

variable (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
include hkl he h₀ h₂₃

/-- Clifford action of `e₁` on a canonical spinor `u₀`: `c(e₁) u₀ = i c(e₀) u₀`. -/
theorem ι_apply_one_of_cliffordProjection_apply_eq_self {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) u₀ = I • ρ (ι Q (e 0)) u₀ :=
  h₀ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 0)

/-- Clifford action of `e₃` on a canonical spinor `u₀`: `c(e₃) u₀ = i c(e₂) u₀`. -/
theorem ι_apply_three_of_cliffordProjection_apply_eq_self {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 3)) u₀ = I • ρ (ι Q (e 2)) u₀ :=
  h₂₃ ▸ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀ (e 2)

private theorem ι_one_ι_two_canonical {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 2)) u₀) = I • (antiCanonicalSpinor o ρ e u₀ : W) := by
  rw [map_ι_apply_comm_of_inner_eq_zero hQ (e.orthonormal.2 (by decide : (1 : Fin 4) ≠ 2)),
    ι_apply_one_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀, map_smul,
    map_ι_apply_comm_of_inner_eq_zero hQ (e.orthonormal.2 (by decide : (2 : Fin 4) ≠ 0))]
  simp [coe_antiCanonicalSpinor]

private theorem ι_one_ι_three_canonical {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 3)) u₀) = -(antiCanonicalSpinor o ρ e u₀ : W) := by
  rw [ι_apply_three_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀, map_smul,
    ι_one_ι_two_canonical hQ hkl he h₀ h₂₃ hu₀]
  simp [smul_smul]

/-- The Kähler bivector acts on the anti-canonical spinor `v₀` with eigenvalue `2i`. -/
theorem bivectorExterior_kahlerForm_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (bivectorExterior Q J.kahlerForm) (antiCanonicalSpinor o ρ e u₀) =
      (2 * I) • (antiCanonicalSpinor o ρ e u₀ : W) := by
  have ha : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (antiCanonicalSpinor o ρ e u₀)) =
      I • (antiCanonicalSpinor o ρ e u₀ : W) := by
    conv_lhs => rw [coe_antiCanonicalSpinor]
    rw [map_ι_apply_map_ι_apply_map_ι_apply_of_inner_eq_zero hQ (e.orthonormal.1 0)
        (e.orthonormal.2 (by decide : (0 : Fin 4) ≠ 1)),
      ι_one_ι_two_canonical hQ hkl he h₀ h₂₃ hu₀]
  have hb : ρ (ι Q (e 2)) (ρ (ι Q (e 3)) (antiCanonicalSpinor o ρ e u₀)) =
      I • (antiCanonicalSpinor o ρ e u₀ : W) := by
    conv_lhs =>
      rw [coe_antiCanonicalSpinor,
        map_ι_apply_comm_of_inner_eq_zero hQ (e.orthonormal.2 (by decide : (0 : Fin 4) ≠ 2))]
    simp only [map_neg]
    rw [map_ι_apply_map_ι_apply_map_ι_apply_of_inner_eq_zero hQ (e.orthonormal.1 2)
        (e.orthonormal.2 (by decide : (2 : Fin 4) ≠ 3)),
      map_ι_apply_comm_of_inner_eq_zero hQ (e.orthonormal.2 (by decide : (3 : Fin 4) ≠ 0)),
      ι_apply_three_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀]
    simp [coe_antiCanonicalSpinor]
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂₃]
  simp only [map_add, map_mul, LinearMap.add_apply, mul_apply_eq_comp, ha, hb]
  module

/-- The canonical Kähler Clifford projection annihilates `v₀`. -/
@[simp]
theorem cliffordProjection_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ J.kahlerForm (antiCanonicalSpinor o ρ e u₀) = 0 :=
  cliffordProjection_apply_eq_zero_of_bivectorExterior_apply o ρ
    (bivectorExterior_kahlerForm_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀)

/-- The complementary Kähler Clifford projection fixes `v₀`. -/
@[simp]
theorem cliffordProjection_neg_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ (-J.kahlerForm) (antiCanonicalSpinor o ρ e u₀) =
      antiCanonicalSpinor o ρ e u₀ := by
  rw [cliffordProjection_neg_apply,
    cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, sub_zero]

/-- Clifford action of `e₁` on `v₀`: `c(e₁) v₀ = i c(e₂) u₀`. -/
theorem ι_apply_one_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) (antiCanonicalSpinor o ρ e u₀) = I • ρ (ι Q (e 2)) u₀ := by
  rw [← h₀, ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂₃
    (cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀),
    ι_apply_zero_antiCanonicalSpinor hQ, smul_neg, neg_smul, neg_neg]

/-- Clifford action of `e₃` on `v₀`: `c(e₃) v₀ = -i c(e₀) u₀`. -/
theorem ι_apply_three_antiCanonicalSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 3)) (antiCanonicalSpinor o ρ e u₀) = -I • ρ (ι Q (e 0)) u₀ := by
  rw [← h₂₃, ι_apply_apply_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂₃
    (cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀),
    ι_apply_two_antiCanonicalSpinor hQ]

/-- A canonical spinor `u₀` and its anti-canonical partner `v₀` are orthogonal in `W⁺`. -/
theorem inner_antiCanonicalSpinor_eq_zero (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ⟪u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ = 0 :=
  calc ⟪u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ
      = ⟪cliffordProjection o ρ J.kahlerForm u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ := by rw [hu₀]
    _ = ⟪u₀, cliffordProjection o ρ J.kahlerForm (antiCanonicalSpinor o ρ e u₀)⟫_ℂ :=
        (isSelfAdjoint_cliffordProjection o J.kahlerForm hρ).isSymmetric _ _
    _ = 0 := by
        rw [cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, inner_zero_right]

/-- Action of `cliffordRestriction` at `ρ₁` on a canonical spinor `u₀`:
`C(i ρ₁) u₀ = i √2 v₀`. -/
theorem cliffordRestriction_antiInvariantSelfDual₁_apply {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordRestriction o ρ (AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he) u₀ =
      (I * (√2 : ℂ)) • antiCanonicalSpinor o ρ e u₀ := Subtype.ext <| by
  rw [AlmostComplexStructure.coe_antiInvariantSelfDual₁, map_smul, map_sub, smul_apply, sub_apply,
    Submodule.coe_smul_of_tower, Submodule.coe_sub,
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (0 : Fin 4) ≠ 2)),
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (1 : Fin 4) ≠ 3))]
  simp only [map_mul, mul_apply_eq_comp, ι_one_ι_three_canonical hQ hkl he h₀ h₂₃ hu₀,
    ← coe_antiCanonicalSpinor, Submodule.coe_smul, ← Complex.coe_smul]
  push_cast; module

/-- Action of `cliffordRestriction` at `ρ₂` on a canonical spinor `u₀`:
`C(i ρ₂) u₀ = -√2 v₀`. -/
theorem cliffordRestriction_antiInvariantSelfDual₂_apply {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordRestriction o ρ (AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he) u₀ =
      (-(√2 : ℂ)) • antiCanonicalSpinor o ρ e u₀ := Subtype.ext <| by
  rw [AlmostComplexStructure.coe_antiInvariantSelfDual₂, map_smul, map_add, smul_apply, add_apply,
    Submodule.coe_smul_of_tower, Submodule.coe_add,
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (0 : Fin 4) ≠ 3)),
    coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ
      (e.orthonormal.2 (by decide : (1 : Fin 4) ≠ 2))]
  simp only [map_mul, mul_apply_eq_comp,
    ι_apply_three_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hu₀, map_smul,
    ι_one_ι_two_canonical hQ hkl he h₀ h₂₃ hu₀, ← coe_antiCanonicalSpinor, Submodule.coe_smul,
    ← Complex.coe_smul, smul_smul, I_mul_I]
  push_cast; module

/-- Orthogonal decomposition of any `ζ ∈ W⁺` along the orthonormal frame `(u₀, v₀)`. -/
theorem eq_inner_smul_add_inner_antiCanonicalSpinor_smul
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (ζ : positiveHalfSpinors o ρ) :
    ζ = ⟪u₀, ζ⟫_ℂ • u₀ +
      ⟪antiCanonicalSpinor o ρ e u₀, ζ⟫_ℂ • antiCanonicalSpinor o ρ e u₀ := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hnegω : o.hodgeStar hkl (-J.kahlerForm) = -J.kahlerForm := by rw [map_neg, hω]
  have hv₀₁ : ‖antiCanonicalSpinor o ρ e u₀‖ = 1 := (norm_antiCanonicalSpinor hQ hρ u₀).trans hu₀₁
  have hα := cliffordProjection_apply_eq_inner_smul o hQ hkl hω hρ h₂ hu₀ hu₀₁ ζ
  have hβ := cliffordProjection_apply_eq_inner_smul o hQ hkl hnegω hρ h₂
    (cliffordProjection_neg_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀) hv₀₁ ζ
  rw [cliffordProjection_neg_apply] at hβ; rw [← hα, ← hβ]; abel

/-- **Cross-term polarization identity**: `(√2 / 4) q'(α u₀, β v₀)` lies in the anti-`J`-invariant
plane `span(ρ₁, ρ₂)` with coefficients `(Im(conj α * β) / 4, -Re(conj α * β) / 4)`. -/
theorem smul_quadraticTwoFormPolar_smul_antiCanonicalSpinor
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (α β : ℂ) :
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiCanonicalSpinor o ρ e u₀) =
      ((conj α * β).im / 4) • AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he -
        ((conj α * β).re / 4) • AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he := by
  have hω_sd := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hv₀_in : ⟪antiCanonicalSpinor o ρ e u₀, antiCanonicalSpinor o ρ e u₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), (norm_antiCanonicalSpinor hQ hρ u₀).trans hu₀₁]
    norm_num
  have hpair (η : Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1) :
      ⟪η, quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiCanonicalSpinor o ρ e u₀)⟫ =
        (⟪cliffordRestriction o ρ η (α • u₀), β • antiCanonicalSpinor o ρ e u₀⟫_ℂ).re / 2 := by
    rw [real_inner_comm, Submodule.coe_inner, quadraticTwoFormPolar_apply, Submodule.coe_smul,
      real_inner_smul_left, ← Submodule.coe_inner,
      inner_cliffordRestrictionAdjoint_left o ρ hkl _ η,
      trace_quadraticEndPolar_mul_of_mem_traceFreeSelfAdjoint
        (cliffordRestriction_mem_traceFreeSelfAdjoint o hQ hρ η)]; simp; ring
  have hω : ⟪J.kahlerSelfDual o hkl hω_sd,
      quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiCanonicalSpinor o ρ e u₀)⟫ = 0 := by
    rw [real_inner_comm, Submodule.coe_inner, AlmostComplexStructure.coe_kahlerSelfDual,
      real_inner_smul_right,
      inner_quadraticTwoFormPolar_of_cliffordProjection o hQ hkl hω_sd hρ
        (by rw [map_smul, hu₀])
        (by rw [map_smul, cliffordProjection_antiCanonicalSpinor hQ hkl he h₀ h₂₃ hu₀, smul_zero]),
      mul_zero]
  have hρ₁ : ⟪AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he,
      quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiCanonicalSpinor o ρ e u₀)⟫ =
      (√2 / 2) * (conj α * β).im := by
    rw [hpair, map_smul, cliffordRestriction_antiInvariantSelfDual₁_apply hQ hkl he h₀ h₂₃ hu₀,
      smul_smul, inner_smul_left, inner_smul_right, hv₀_in]; simp; ring
  have hρ₂ : ⟪AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he,
      quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiCanonicalSpinor o ρ e u₀)⟫ =
      -(√2 / 2) * (conj α * β).re := by
    rw [hpair, map_smul, cliffordRestriction_antiInvariantSelfDual₂_apply hQ hkl he h₀ h₂₃ hu₀,
      smul_smul, inner_smul_left, inner_smul_right, hv₀_in]; simp; ring
  have hs : (√2 / 4 : ℝ) * (√2 / 2) = 1 / 4 := by
    linear_combination (1 / 8 : ℝ) * Real.mul_self_sqrt zero_le_two
  conv_lhs =>
    rw [AlmostComplexStructure.eq_inner_kahlerSelfDual_add_antiInvariantSelfDual
      (e := e) (he := he) (h₀ := h₀) (h₂ := h₂₃) hω_sd
      (quadraticTwoFormPolar o ρ hkl (α • u₀) (β • antiCanonicalSpinor o ρ e u₀))]
  rw [hω, hρ₁, hρ₂, zero_smul, zero_add, smul_add, smul_smul, smul_smul]
  simp only [neg_mul, mul_neg, ← mul_assoc, hs]; module

/-- The negative half-spinors `c(e₂) u₀` and `c(e₀) u₀` are orthogonal in `W⁻`. -/
theorem inner_halfSpinCliffordMul_two_zero (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ⟪halfSpinCliffordMul o ρ 1 (e 2)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ) u₀),
      halfSpinCliffordMul o ρ 1 (e 0)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ) u₀)⟫_ℂ = 0 := by
  rw [← inner_conj_symm, Submodule.coe_inner, coe_halfSpinCliffordMul_apply_apply,
    coe_halfSpinCliffordMul_apply_apply, LinearEquiv.coe_ofEq_apply,
    inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃ hρ hu₀,
    h₂₃, e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
  simp

/-- Orthogonal decomposition of any negative half-spinor `ν ∈ W⁻` along `(c(e₂) u₀, c(e₀) u₀)`. -/
theorem eq_inner_halfSpinCliffordMul (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (ν : Module.End.eigenspace (ρ (chirality Q o)) (-1)) :
    let ePos := LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ)
    ν = ⟪halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀), ν⟫_ℂ •
          halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀) +
        ⟪halfSpinCliffordMul o ρ 1 (e 0) (ePos u₀), ν⟫_ℂ •
          halfSpinCliffordMul o ρ 1 (e 0) (ePos u₀) := by
  intro ePos
  have hv : Q (e 0) ≠ 0 := by rw [hQ, e.orthonormal.1 0]; norm_num
  let φ : positiveHalfSpinors o ρ := ePos.symm ((halfSpinCliffordMulEquiv o ρ 1 hv).symm ν)
  have hνφ : halfSpinCliffordMul o ρ 1 (e 0) (ePos φ) = ν := by
    dsimp only [φ]
    rw [ePos.apply_symm_apply, ← halfSpinCliffordMulEquiv_toLinearMap o ρ 1 hv]
    exact (halfSpinCliffordMulEquiv o ρ 1 hv).apply_symm_apply ν
  have h0v : halfSpinCliffordMul o ρ 1 (e 0) (ePos (antiCanonicalSpinor o ρ e u₀)) =
      -halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀) :=
    Subtype.ext <| by
      rw [Submodule.coe_neg, coe_halfSpinCliffordMul_apply_apply,
        coe_halfSpinCliffordMul_apply_apply, LinearEquiv.coe_ofEq_apply,
        LinearEquiv.coe_ofEq_apply]
      exact ι_apply_zero_antiCanonicalSpinor (e := e) hQ u₀
  have hexp : ν = (-⟪antiCanonicalSpinor o ρ e u₀, φ⟫_ℂ) •
        halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀) +
      ⟪u₀, φ⟫_ℂ • halfSpinCliffordMul o ρ 1 (e 0) (ePos u₀) := by
    rw [← hνφ]
    conv_lhs =>
      rw [eq_inner_smul_add_inner_antiCanonicalSpinor_smul hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ φ]
    simp only [map_add, map_smul, h0v, smul_neg, neg_smul]
    exact add_comm _ _
  have hn (i : Fin 4) : ‖halfSpinCliffordMul o ρ 1 (e i) (ePos u₀)‖ = 1 := by
    rw [norm_halfSpinCliffordMul_apply o hQ hρ 1 (e i), e.orthonormal.1 i, one_mul,
      ← Submodule.norm_coe, LinearEquiv.coe_ofEq_apply, Submodule.norm_coe, hu₀₁]
  have hw₂₀ := inner_halfSpinCliffordMul_two_zero hQ hkl he h₀ h₂₃ hρ hu₀
  conv_rhs => rw [hexp]
  rw [inner_smul_add_smul_of_inner_eq_zero_left (hn 2) hw₂₀,
    inner_smul_add_smul_of_inner_eq_zero_right (hn 0) hw₂₀, ← hexp]

end CliffordRelations

end SpinorFrame

end TauCeti.SeibergWitten
