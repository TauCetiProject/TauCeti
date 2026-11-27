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
import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Pairing
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Clifford multiplication on the canonical line of an almost Hermitian four-space

Let `V` be an oriented real inner product space of dimension four with an orthogonal complex
structure `J`, and let `ω` be its Kähler form. Let `W` be a Hermitian Clifford module,
`c(v) = ρ (ι Q v)` with `Q v = -‖v‖²`, and `W⁺` its positive half-spinors. Taubes writes a positive
spinor as `ψ = α u₀ + β`, where `u₀` spans the `-2i`-eigenspace of `c₂(ω)` in `W⁺`, the range of
the projection `P_α` (`TauCeti.SeibergWitten.cliffordProjection`), and `β` lies in the
complementary `2i`-eigenspace. When `W` is a spin module, so that `W⁺` has complex dimension two,
both eigenspaces are lines: the canonical line and its complement. The results below hold on the
eigenspaces of any Hermitian Clifford module, without assuming that `J` induces the orientation `o`.

On the `-2i`-eigenspace, Clifford multiplication turns `J` into multiplication by `i`: if
`P_α ψ = ψ` then `c(J v) ψ = i c(v) ψ`, while on the complementary eigenspace
`c(J v) β = -i c(v) β`. Conversely, these relations cut out the two eigenspaces
(`TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_self_iff`,
`TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_zero_iff`): both directions follow
algebraically from `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)` in any unitary frame `(e₀, e₁, e₂, e₃)`
with `J e₀ = e₁` and `J e₂ = e₃`
(`TauCeti.AlmostComplexStructure.two_smul_ι_apply_apply_of_bivectorExterior_apply_eq_smul`).
Consequently, when the Clifford generators are skew-adjoint,
`⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`, so `v ↦ c(v) ψ` is a complex-linear map from
`(V, J)` to the negative half-spinors, isometric up to the factor `‖ψ‖`.

This is the pointwise symbol of Taubes's identity `D_A(α u₀) = √2 ∂bar_a α + α D_A u₀`. Write the
symbol of the Dirac operator on a complex-valued covector with components `x_k`, such as the
covariant derivative `x_k = (∇_a α)(e_k)`, as `∑ₖ x_k c(e_k) ψ`. In a unitary frame,

`∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ`,
`‖∑ₖ x_k c(e_k) ψ‖² = (|x₀ + i x₁|² + |x₂ + i x₃|²) ‖ψ‖²`.

The factors `x₀ + i x₁` and `x₂ + i x₃` are twice the `∂bar`-derivatives in the complex
coordinates of the planes `⟨e₀, e₁⟩` and `⟨e₂, e₃⟩`. In particular, for `ψ ≠ 0` the symbol
vanishes exactly when the real-linear covector `L` with `x_k = L e_k` is complex linear,
`L (J v) = i L v`, for any orthonormal basis `e` and without skew-adjointness of `ρ`: Clifford
multiplication of `α u₀` sees only `∂bar_a α`. This is the pointwise algebra by which, for fields
on `ℂ × ℂ` that depend only on the normal factor `⟨e₂, e₃⟩`, the Dirac equation on the canonical
line becomes the holomorphicity equation `∂bar_a α = 0` of the plane vortex equations, in the
convention `∂bar_a α = (∇₁ α + i ∇₂ α) / 2` of `TauCeti.Vortex.equation`. No differential operator
is constructed here.

Two Clifford multiplications carry the canonical eigenspace back to `W⁺`. These formulas hold for
every `ψ ∈ W` with `c₂(ω) ψ = -2i ψ`, with no chirality or orientation assumption: there
`c(e₀) c(e₁)` and `c(e₂) c(e₃)` both act by `-i`. In the basis `(e₀, e₂)` of the complex vector
space `(V, J)`, with coordinates `z₀(v) = ⟪e₀, v⟫ + i ⟪e₁, v⟫` and `z₂(v) = ⟪e₂, v⟫ + i ⟪e₃, v⟫`,
one has `c(v) ψ = z₀(v) c(e₀) ψ + z₂(v) c(e₂) ψ` and

`c(v) c(w) ψ = (z₀(v) z₂(w) - z₂(v) z₀(w)) c(e₀) c(e₂) ψ - (⟪v, w⟫ - i ⟪v, J w⟫) ψ`,

where `c(e₀) c(e₂) ψ` lies in the complementary eigenspace. So the component of `c(v) c(w) ψ` in the
complementary eigenspace is the complex determinant of `v, w`, a complex bilinear alternating form
of `(V, J)`, and its component along `ψ` is minus the Hermitian product of `v, w`. This is the
Clifford algebra behind the splitting `W⁺ = Λ⁰'⁰ ⊕ Λ⁰'²` of the canonical `Spinᶜ` structure.

The **paired spinor** `β₀ = c(e₂) c(e₀) u₀` of a canonical spinor `u₀` is orthogonal to `u₀` and
has its norm, so `(u₀, β₀)` is a unitary frame of `W⁺` when `W⁺` has rank two. Clifford
multiplication of a complex covector on `β₀` sees only its `∂`-components,

`∑ₖ y_k c(e_k) β₀ = (y₀ - i y₁) c(e₂) u₀ - (y₂ - i y₃) c(e₀) u₀`,

and the Clifford map sends `u₀` to `u₀`, `-i β₀` and `β₀` along `e₀ ∧ e₁`, `e₀ ∧ e₂` and
`e₀ ∧ e₃`. This file also verifies its `2i`-eigenvalue, orthogonal expansion in `W⁺`, the frame
coordinates, diagonal, and cross-term polarization identities for `quadraticTwoFormPolar` on
`(u₀, β₀)`, and the orthogonal frame `(c(e₂) u₀, c(e₀) u₀)` of `W⁻`.

## Main results

The formulas for Clifford multiplication on any eigenvector of `c₂(ω)`, in particular
`TauCeti.AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply` (`c(J v) ψ = i c(v) ψ`),
`TauCeti.AlmostComplexStructure.sum_smul_ι_apply_of_bivectorExterior_apply` (the Dirac symbol) and
`TauCeti.AlmostComplexStructure.ι_apply_ι_apply_of_bivectorExterior_apply` (`c(v) c(w) ψ`), are in
`TauCeti.LinearAlgebra.CliffordAlgebra.Kahler`. This file applies them to the eigenspaces of
`P_α` in `W⁺`.

* `TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_self_iff` and
  `TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_zero_iff`: `P_α ψ = ψ` iff
  `c(J v) ψ = i c(v) ψ` for all `v`, and `P_α β = 0` iff `c(J v) β = -i c(v) β` for all `v`,
  with forward implications
  `TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self` and
  `TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_zero`.
* `TauCeti.SeibergWitten.inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self`:
  `⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`.
* `TauCeti.SeibergWitten.norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self`: the
  norm of the Dirac symbol on the canonical eigenspace.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self` and
  `TauCeti.SeibergWitten.sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self`:
  it vanishes exactly when both `∂bar`-components vanish, that is when the covector is complex
  linear.
* `TauCeti.SeibergWitten.pairedSpinor`, `TauCeti.SeibergWitten.norm_pairedSpinor`,
  `TauCeti.SeibergWitten.norm_pairedSpinor_eq_one`,
  `TauCeti.SeibergWitten.inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self`,
  `TauCeti.SeibergWitten.bivectorExterior_kahlerForm_pairedSpinor`, and
  `TauCeti.SeibergWitten.eq_inner_smul_add_inner_pairedSpinor_smul`: the paired spinor completes
  `u₀` to a unitary frame of `W⁺`.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_pairedSpinor_of_cliffordProjection_apply_eq_self`: the
  Dirac symbol on the paired spinor in terms of the two `∂`-components.
* `cliffordRestriction_ιMulti_zero_one_apply_of_cliffordProjection_apply_eq_self`,
  `cliffordRestriction_ιMulti_zero_two_apply`, and
  `cliffordRestriction_ιMulti_zero_three_apply_of_cliffordProjection_apply_eq_self` (all in
  `TauCeti.SeibergWitten`): the Clifford map along `e₀ ∧ e₁`, `e₀ ∧ e₂`, and `e₀ ∧ e₃` on `u₀`.
* `TauCeti.SeibergWitten.inner_quadraticTwoFormPolar_ιMulti_zero_one`, `_zero_two`, `_zero_three`,
  `TauCeti.SeibergWitten.smul_quadraticTwoFormPolar_smul_smul_of_cliffordProjection_apply_eq_self`,
  and `TauCeti.SeibergWitten.smul_quadraticTwoFormPolar_smul_pairedSpinor`: frame coordinates,
  diagonal, and cross-term polarization identities along `(u₀, β₀)`.
* `TauCeti.SeibergWitten.norm_halfSpinCliffordMul_ofEq_eq_one`,
  `TauCeti.SeibergWitten.inner_halfSpinCliffordMul_two_zero`, and
  `TauCeti.SeibergWitten.eq_inner_halfSpinCliffordMul`: unit norms, orthogonality, and expansion
  along the `W⁻` frame `(c(e₂) u₀, c(e₀) u₀)`.

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

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-! ### `J` acts by `±i` on the two eigenspaces -/

section Orthogonal

variable {J : AlmostComplexStructure V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
include hQ hJ

/-- **The canonical eigenspace is cut out by `J`**: a positive half-spinor `ψ` is fixed by `P_α`
exactly when Clifford multiplication turns `J` into `i` on it, `c(J v) ψ = i c(v) ψ` for every
`v`. -/
theorem cliffordProjection_kahlerForm_apply_eq_self_iff {ψ : positiveHalfSpinors o ρ} :
    cliffordProjection o ρ J.kahlerForm ψ = ψ ↔
      ∀ v, ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ := by
  obtain ⟨e₀, he₀⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) 2
    ((Fact.out : finrank ℝ V = 4).trans (by norm_num))
  let e : OrthonormalBasis (Fin 4) ℝ V := e₀.reindex (finCongr (by norm_num))
  have h₀ : J (e 0) = e 1 := by simpa [e] using (he₀ 0).symm
  have h₂ : J (e 2) = e 3 := by simpa [e] using (he₀ 1).symm
  refine ⟨fun hψ ↦ AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply hQ h₀ h₂
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hψ), fun h ↦
    cliffordProjection_apply_eq_self_of_bivectorExterior_apply o ρ
      (AlmostComplexStructure.bivectorExterior_apply_eq_smul_of_ι_one_apply_of_ι_three_apply
        hQ h₀ h₂ (h₀ ▸ h (e 0)) (h₂ ▸ h (e 2)))⟩

/-- **On the canonical eigenspace, Clifford multiplication turns `J` into `i`**: if
`P_α ψ = ψ`, then `c(J v) ψ = i c(v) ψ`
(`AlmostComplexStructure.ι_apply_apply_of_bivectorExterior_apply`). -/
theorem ι_apply_apply_of_cliffordProjection_apply_eq_self {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (v : V) :
    ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ :=
  (cliffordProjection_kahlerForm_apply_eq_self_iff hQ hJ).1 hψ v

/-- **The complementary eigenspace is cut out by `J`**: a positive half-spinor `β` is killed by
`P_α` exactly when Clifford multiplication turns `J` into `-i` on it, `c(J v) β = -i c(v) β` for
every `v`. -/
theorem cliffordProjection_kahlerForm_apply_eq_zero_iff {β : positiveHalfSpinors o ρ} :
    cliffordProjection o ρ J.kahlerForm β = 0 ↔
      ∀ v, ρ (ι Q (J v)) β = -Complex.I • ρ (ι Q v) β := by
  obtain ⟨e₀, he₀⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) 2
    ((Fact.out : finrank ℝ V = 4).trans (by norm_num))
  let e : OrthonormalBasis (Fin 4) ℝ V := e₀.reindex (finCongr (by norm_num))
  have h₀ : J (e 0) = e 1 := by simpa [e] using (he₀ 0).symm
  have h₂ : J (e 2) = e 3 := by simpa [e] using (he₀ 1).symm
  refine ⟨fun hβ v ↦ ?_, fun h ↦ ?_⟩
  · have h := AlmostComplexStructure.two_smul_ι_apply_apply_of_bivectorExterior_apply_eq_smul
      hQ h₀ h₂ (by simp) (bivectorExterior_apply_of_cliffordProjection_apply_eq_zero o ρ hβ) v
    linear_combination (norm := module) (2⁻¹ : ℂ) • h
  · have hβ := AlmostComplexStructure.bivectorExterior_apply_eq_smul_of_ι_one_apply_of_ι_three_apply
      hQ h₀ h₂ (h₀ ▸ h (e 0)) (h₂ ▸ h (e 2))
    rw [neg_mul_neg] at hβ
    exact cliffordProjection_apply_eq_zero_of_bivectorExterior_apply o ρ hβ

/-- On the complementary eigenspace, Clifford multiplication turns `J` into `-i`: if
`P_α β = 0`, then `c(J v) β = -i c(v) β`
(`AlmostComplexStructure.two_smul_ι_apply_apply_of_bivectorExterior_apply_eq_smul`). -/
theorem ι_apply_apply_of_cliffordProjection_apply_eq_zero {β : positiveHalfSpinors o ρ}
    (hβ : cliffordProjection o ρ J.kahlerForm β = 0) (v : V) :
    ρ (ι Q (J v)) β = -Complex.I • ρ (ι Q v) β :=
  (cliffordProjection_kahlerForm_apply_eq_zero_iff hQ hJ).1 hβ v

/-! ### The Hermitian structure of `v ↦ c(v) ψ` -/

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
    rw [ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hJ hψ, inner_smul_right,
      Complex.mul_re, Complex.I_re, Complex.I_im] at h
    linarith
  apply Complex.ext <;> simp [hre, him, ← Complex.ofReal_pow]

end Orthogonal

/-! ### The Dirac symbol on the canonical eigenspace -/

section DiracSymbol

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
include hQ h₀ h₂

/-- The norm of the Dirac symbol on the canonical eigenspace
(`AlmostComplexStructure.sum_smul_ι_apply_of_bivectorExterior_apply`):
`‖∑ₖ x_k c(e_k) ψ‖² = (|x₀ + i x₁|² + |x₂ + i x₃|²) ‖ψ‖²`. -/
theorem norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (x : Fin 4 → ℂ) :
    ‖∑ k, x k • ρ (ι Q (e k)) ψ‖ ^ 2 =
      (‖x 0 + Complex.I * x 1‖ ^ 2 + ‖x 2 + Complex.I * x 3‖ ^ 2) * ‖(ψ : W)‖ ^ 2 := by
  -- `c(e₀) ψ` and `c(e₂) ψ` are orthogonal of norm `‖ψ‖`.
  have horth : ⟪ρ (ι Q (e 0)) ψ, ρ (ι Q (e 2)) ψ⟫_ℂ = 0 := by
    rw [inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ
        (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) hρ hψ, h₂,
      e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
    simp
  have hnorm (k : Fin 4) : ‖ρ (ι Q (e k)) ψ‖ = ‖(ψ : W)‖ := by
    rw [norm_map_ι_apply hQ hρ, e.orthonormal.1 k, one_mul]
  rw [AlmostComplexStructure.sum_smul_ι_apply_of_bivectorExterior_apply hQ h₀ h₂
      (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hψ),
    norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, horth]
  simp only [mul_zero, RCLike.zero_re, add_zero, norm_smul, hnorm]
  ring

/-- **The Dirac symbol on the canonical eigenspace vanishes exactly on `∂bar`-closed
covectors**: for `P_α ψ = ψ`, `∑ₖ x_k c(e_k) ψ = 0` if and only if `ψ = 0` or
`x₀ + i x₁ = x₂ + i x₃ = 0`
(`AlmostComplexStructure.sum_smul_ι_apply_eq_zero_iff_of_bivectorExterior_apply`). -/
theorem sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self
    {ψ : positiveHalfSpinors o ρ} (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ)
    (x : Fin 4 → ℂ) :
    ∑ k, x k • ρ (ι Q (e k)) ψ = 0 ↔
      (ψ : W) = 0 ∨ (x 0 + Complex.I * x 1 = 0 ∧ x 2 + Complex.I * x 3 = 0) :=
  AlmostComplexStructure.sum_smul_ι_apply_eq_zero_iff_of_bivectorExterior_apply hQ h₀ h₂
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hψ) x

end DiracSymbol

/-- **The Dirac symbol on the canonical eigenspace sees only `∂bar`**: for `P_α ψ = ψ`, any
orthonormal basis `e` of `V`, and a real-linear complex covector `L`, such as a covariant
derivative `∇_a α` at a point, `∑ₖ L(e_k) c(e_k) ψ = 0` if and only if `ψ = 0` or `L` is complex
linear for `J`, `L (J v) = i L v`. -/
theorem sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self
    {J : AlmostComplexStructure V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} {κ : Type*} [Fintype κ]
    {e : OrthonormalBasis κ ℝ V} {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (L : V →ₗ[ℝ] ℂ) :
    ∑ k, L (e k) • ρ (ι Q (e k)) ψ = 0 ↔ (ψ : W) = 0 ∨ ∀ v, L (J v) = Complex.I * L v := by
  obtain ⟨b₀, hb₀⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) 2
    ((Fact.out : finrank ℝ V = 4).trans (by norm_num))
  let b : OrthonormalBasis (Fin 4) ℝ V := b₀.reindex (finCongr (by norm_num))
  have h₀ : J (b 0) = b 1 := by simpa [b] using (hb₀ 0).symm
  have h₂ : J (b 2) = b 3 := by simpa [b] using (hb₀ 1).symm
  -- The contraction `∑ₖ L(eₖ) c(eₖ) ψ` is the metric trace of `ρ.cliffordPairing (v ↦ L v • ψ)`,
  -- hence independent of the orthonormal basis `e`.
  have hsum : ∑ k, L (e k) • ρ (ι Q (e k)) ψ = ∑ j, L (b j) • ρ (ι Q (b j)) ψ := by
    let B : LinearMap.BilinMap ℝ V W :=
      ρ.cliffordPairing (((LinearMap.toSpanSingleton ℂ W (ψ : W)).restrictScalars ℝ).comp L)
    simpa only [B, AlgHom.cliffordPairing_apply, LinearMap.comp_apply,
      LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, map_smul] using
      (B.metricTrace_eq_sum e).symm.trans (B.metricTrace_eq_sum b)
  have h₁ : J (b 1) = -b 0 := by rw [← h₀, J.apply_apply]
  have h₃ : J (b 3) = -b 2 := by rw [← h₂, J.apply_apply]
  rw [hsum, sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hψ
    (fun k ↦ L (b k))]
  refine or_congr_right ⟨fun ⟨h01, h23⟩ v ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · -- `L` commutes with `J` on the frame, hence everywhere.
    have key (i : Fin 4) : L (J (b i)) = Complex.I * L (b i) := by
      fin_cases i
      · simp only [Fin.zero_eta, h₀]
        linear_combination (-Complex.I) * h01 + L (b 1) * Complex.I_sq
      · simp only [Fin.mk_one, h₁, map_neg]
        linear_combination -h01
      · simp only [Fin.reduceFinMk, h₂]
        linear_combination (-Complex.I) * h23 + L (b 3) * Complex.I_sq
      · simp only [Fin.reduceFinMk, h₃, map_neg]
        linear_combination -h23
    exact LinearMap.congr_fun
      (b.toBasis.ext (f₁ := L.comp J.toLinearMap) (f₂ := (LinearMap.mulLeft ℝ Complex.I).comp L)
        fun i ↦ by simpa using key i) v
  · have h0 := h (b 0)
    rw [h₀] at h0
    linear_combination Complex.I * h0 + L (b 0) * Complex.I_sq
  · have h2 := h (b 2)
    rw [h₂] at h2
    linear_combination Complex.I * h2 + L (b 2) * Complex.I_sq

/-! ### The paired spinor -/

section PairedSpinor

open Complex _root_.exteriorPower

section Algebraic

variable {K W : Type*} [CommRing K] [Algebra ℝ K] [AddCommGroup W] [Module K W] [Module ℝ W]
  [IsScalarTower ℝ K W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End K W}
  {e : OrthonormalBasis (Fin 4) ℝ V}

variable (e) in
/-- The **paired spinor** `c(e₂) c(e₀) u₀` of a positive spinor `u₀`, for an orthonormal frame
`e`. When `u₀` spans the canonical eigenspace, it spans the complementary eigenspace of `W⁺`, and
together with `u₀` it gives a unitary frame of `W⁺` when `W⁺` has rank two (`norm_pairedSpinor`,
`inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self`). -/
def pairedSpinor (u₀ : positiveHalfSpinors o ρ) : positiveHalfSpinors o ρ :=
  ⟨ρ (ι Q (e 2)) (ρ (ι Q (e 0)) u₀), by
    simpa [map_mul, mul_apply_eq_comp] using
      mapsTo_positiveHalfSpinors o ρ
        (commute_chirality_of_mem_even o (ι_mul_ι_mem_evenOdd_zero Q (e 2) (e 0))) u₀ u₀.property⟩

/-- The paired spinor as a vector of `W`. -/
@[simp]
theorem coe_pairedSpinor (u₀ : positiveHalfSpinors o ρ) :
    (pairedSpinor e u₀ : W) = ρ (ι Q (e 2)) (ρ (ι Q (e 0)) u₀) :=
  (rfl)

/-- `c(e₀) β₀ = c(e₂) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`. -/
theorem ι_zero_apply_pairedSpinor (hQ : ∀ v, Q v = -‖v‖ ^ 2) (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 0)) (pairedSpinor e u₀ : W) = ρ (ι Q (e 2)) u₀ := by
  rw [coe_pairedSpinor, e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide),
    e.map_ι_apply_map_ι_apply hQ ρ, map_neg, neg_neg]

/-- `c(e₂) β₀ = -c(e₀) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`. -/
theorem ι_two_apply_pairedSpinor (hQ : ∀ v, Q v = -‖v‖ ^ 2) (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 2)) (pairedSpinor e u₀ : W) = -ρ (ι Q (e 0)) u₀ := by
  rw [coe_pairedSpinor, e.map_ι_apply_map_ι_apply hQ ρ]

end Algebraic

section Hermitian

variable {e : OrthonormalBasis (Fin 4) ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
include hQ

/-- `C(i e₀ ∧ e₂) ψ = -i β` for a positive spinor `ψ` and its paired spinor `β`. -/
theorem cliffordRestriction_ιMulti_zero_two_apply (ψ : positiveHalfSpinors o ρ) :
    cliffordRestriction o ρ (ιMulti ℝ 2 ![e 0, e 2]) ψ = -I • pairedSpinor e ψ := by
  apply Subtype.ext
  rw [coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ (e.orthonormal.2 (by decide)),
    map_mul, mul_apply_eq_comp, Submodule.coe_smul, coe_pairedSpinor,
    e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), smul_neg, neg_smul]

/-- The paired spinor has the norm of `u₀`. -/
theorem norm_pairedSpinor (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (u₀ : positiveHalfSpinors o ρ) : ‖pairedSpinor e u₀‖ = ‖u₀‖ := by
  rw [← Submodule.norm_coe, coe_pairedSpinor, norm_map_ι_apply hQ hρ, norm_map_ι_apply hQ hρ,
    e.orthonormal.1 2, e.orthonormal.1 0, one_mul, one_mul, Submodule.norm_coe]

/-- The paired spinor of a unit positive half-spinor has unit norm. -/
theorem norm_pairedSpinor_eq_one (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀₁ : ‖u₀‖ = 1) :
    ‖pairedSpinor e u₀‖ = 1 :=
  (norm_pairedSpinor hQ hρ u₀).trans hu₀₁

section Canonical

variable {J : AlmostComplexStructure V} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
include h₀ h₂

/-- The paired spinor of a canonical spinor `u₀` is orthogonal to `u₀`. -/
theorem inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ⟪u₀, pairedSpinor e u₀⟫_ℂ = 0 := by
  rw [Submodule.coe_inner, coe_pairedSpinor, ← LinearMap.adjoint_inner_left, hρ,
    LinearMap.neg_apply, inner_neg_left,
    inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂) hρ hu₀, h₀,
    e.orthonormal.2 (by decide : (2 : Fin 4) ≠ 0), e.orthonormal.2 (by decide : (2 : Fin 4) ≠ 1)]
  simp

variable {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
include hu₀

/-- `c(e₁) β₀ = -i c(e₂) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`
(`AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply`). -/
theorem ι_one_apply_pairedSpinor_of_cliffordProjection_apply_eq_self :
    ρ (ι Q (e 1)) (pairedSpinor e u₀ : W) = -I • ρ (ι Q (e 2)) u₀ := by
  rw [coe_pairedSpinor, e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide),
    map_neg,
    (AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂
      (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu₀)).1, neg_smul]

/-- `c(e₃) β₀ = i c(e₀) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`
(`AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply`). -/
theorem ι_three_apply_pairedSpinor_of_cliffordProjection_apply_eq_self :
    ρ (ι Q (e 3)) (pairedSpinor e u₀ : W) = I • ρ (ι Q (e 0)) u₀ := by
  rw [coe_pairedSpinor, e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide),
    map_neg,
    (AlmostComplexStructure.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂
      (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu₀)).2, neg_smul, neg_neg]

/-- **The Dirac symbol on the paired spinor**: for the paired spinor `β₀ = c(e₂) c(e₀) u₀` of a
canonical spinor `u₀`,
`∑ₖ y_k c(e_k) β₀ = (y₀ - i y₁) c(e₂) u₀ - (y₂ - i y₃) c(e₀) u₀`. Only the two `∂`-components
`y₀ - i y₁` and `y₂ - i y₃` survive, and they land on the two frame vectors `c(e₂) u₀` and
`c(e₀) u₀` of `W⁻` in the opposite order from the canonical eigenspace
(`AlmostComplexStructure.sum_smul_ι_apply_of_bivectorExterior_apply`). -/
theorem sum_smul_ι_apply_pairedSpinor_of_cliffordProjection_apply_eq_self (y : Fin 4 → ℂ) :
    ∑ k, y k • ρ (ι Q (e k)) (pairedSpinor e u₀ : W) =
      (y 0 - I * y 1) • ρ (ι Q (e 2)) u₀ - (y 2 - I * y 3) • ρ (ι Q (e 0)) u₀ := by
  rw [Fin.sum_univ_four, ι_zero_apply_pairedSpinor hQ,
    ι_one_apply_pairedSpinor_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hu₀,
    ι_two_apply_pairedSpinor hQ,
    ι_three_apply_pairedSpinor_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hu₀]
  module

/-- `C(i e₀ ∧ e₁) u₀ = u₀` for a canonical spinor `u₀`. -/
theorem cliffordRestriction_ιMulti_zero_one_apply_of_cliffordProjection_apply_eq_self :
    cliffordRestriction o ρ (ιMulti ℝ 2 ![e 0, e 1]) u₀ = u₀ := by
  apply Subtype.ext
  obtain ⟨h₁, -⟩ := AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply
    hQ h₀ h₂ (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu₀)
  rw [coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ (e.orthonormal.2 (by decide)),
    map_mul, mul_apply_eq_comp, h₁, map_smul, smul_smul, I_mul_I]
  simp [hQ, e.orthonormal.1 0]

/-- `C(i e₀ ∧ e₃) u₀ = β₀` for a canonical spinor `u₀` and its paired spinor `β₀`. -/
theorem cliffordRestriction_ιMulti_zero_three_apply_of_cliffordProjection_apply_eq_self :
    cliffordRestriction o ρ (ιMulti ℝ 2 ![e 0, e 3]) u₀ = pairedSpinor e u₀ := by
  apply Subtype.ext
  obtain ⟨-, h₃⟩ := AlmostComplexStructure.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply
    hQ h₀ h₂ (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu₀)
  rw [coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ (e.orthonormal.2 (by decide)),
    map_mul, mul_apply_eq_comp, h₃, map_smul, smul_smul, I_mul_I,
    coe_pairedSpinor, e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide),
    neg_smul, one_smul, neg_neg]

end Canonical

end Hermitian

end PairedSpinor

end CanonicalEigenspace

/-! ### Half-spinor frames and quadratic two-form polarization along `(u₀, β₀)` -/

section SpinorFrame

open Complex
open scoped ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2)

attribute [local instance] finiteDimensional_of_finrank_four

include hQ

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
include h₀ h₂₃

/-- The Kähler bivector acts on the paired spinor `β₀ = c(e₂) c(e₀) u₀` with eigenvalue `2i`. -/
theorem bivectorExterior_kahlerForm_pairedSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (bivectorExterior Q J.kahlerForm) (pairedSpinor e u₀) =
      (2 * I) • (pairedSpinor e u₀ : W) := by
  have ha : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (pairedSpinor e u₀ : W)) =
      I • (pairedSpinor e u₀ : W) := by
    rw [ι_one_apply_pairedSpinor_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hu₀,
      map_smul, neg_smul,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide : (0 : Fin 4) ≠ 2), ← coe_pairedSpinor]
    module
  have hb : ρ (ι Q (e 2)) (ρ (ι Q (e 3)) (pairedSpinor e u₀ : W)) =
      I • (pairedSpinor e u₀ : W) := by
    rw [ι_three_apply_pairedSpinor_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hu₀,
      map_smul, ← coe_pairedSpinor]
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂₃]
  simp only [map_add, map_mul, LinearMap.add_apply, mul_apply_eq_comp, ha, hb]
  module

/-- The canonical Kähler Clifford projection annihilates `pairedSpinor e u₀`. -/
@[simp]
theorem cliffordProjection_pairedSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ J.kahlerForm (pairedSpinor e u₀) = 0 :=
  cliffordProjection_apply_eq_zero_of_bivectorExterior_apply o ρ
    (bivectorExterior_kahlerForm_pairedSpinor hQ h₀ h₂₃ hu₀)

/-- The complementary Kähler Clifford projection fixes `pairedSpinor e u₀`. -/
@[simp]
theorem cliffordProjection_neg_pairedSpinor {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    cliffordProjection o ρ (-J.kahlerForm) (pairedSpinor e u₀) = pairedSpinor e u₀ := by
  rw [cliffordProjection_neg_apply,
    cliffordProjection_pairedSpinor hQ h₀ h₂₃ hu₀, sub_zero]

include hkl he in
/-- Orthogonal decomposition of any `ζ ∈ W⁺` along the orthonormal frame `(u₀, β₀)`. -/
theorem eq_inner_smul_add_inner_pairedSpinor_smul
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (ζ : positiveHalfSpinors o ρ) :
    ζ = ⟪u₀, ζ⟫_ℂ • u₀ + ⟪pairedSpinor e u₀, ζ⟫_ℂ • pairedSpinor e u₀ := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hnegω : o.hodgeStar hkl (-J.kahlerForm) = -J.kahlerForm := by rw [map_neg, hω]
  have hβ₀₁ : ‖pairedSpinor e u₀‖ = 1 := norm_pairedSpinor_eq_one hQ hρ hu₀₁
  have hα := cliffordProjection_apply_eq_inner_smul o hQ hkl hω hρ h₂ hu₀ hu₀₁ ζ
  have hβ := cliffordProjection_apply_eq_inner_smul o hQ hkl hnegω hρ h₂
    (cliffordProjection_neg_pairedSpinor hQ h₀ h₂₃ hu₀) hβ₀₁ ζ
  rw [cliffordProjection_neg_apply] at hβ; rw [← hα, ← hβ]; abel

include hkl in
/-- **The quadratic term along `e₀ ∧ e₁`**: for a unit canonical spinor `u₀` with paired spinor
`β₀`, `⟪q'(α u₀, f u₀ + g β₀), e₀ ∧ e₁⟫ = Re(conj α f) / 2`. -/
theorem inner_quadraticTwoFormPolar_ιMulti_zero_one
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (α f g : ℂ) :
    ⟪(quadraticTwoFormPolar o ρ hkl (α • u₀) (f • u₀ + g • pairedSpinor e u₀) : ⋀[ℝ]^2 V),
        ιMulti ℝ 2 ![e 0, e 1]⟫ = (conj α * f).re / 2 := by
  have h0 := inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hρ hu₀
  rw [inner_quadraticTwoFormPolar_eq_re_inner o hQ hkl hρ, map_smul,
    cliffordRestriction_ιMulti_zero_one_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hu₀,
    inner_add_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hu₀₁, ← inner_conj_symm, h0]
  simp [mul_comm]

include hkl in
/-- **The quadratic term along `e₀ ∧ e₂`**: for a unit canonical spinor `u₀` with paired spinor
`β₀`, `⟪q'(α u₀, f u₀ + g β₀), e₀ ∧ e₂⟫ = Im(α conj g) / 2`. -/
theorem inner_quadraticTwoFormPolar_ιMulti_zero_two
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (α f g : ℂ) :
    ⟪(quadraticTwoFormPolar o ρ hkl (α • u₀) (f • u₀ + g • pairedSpinor e u₀) : ⋀[ℝ]^2 V),
        ιMulti ℝ 2 ![e 0, e 2]⟫ = (α * conj g).im / 2 := by
  have h0 := inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hρ hu₀
  have h1 : ‖pairedSpinor e u₀‖ = 1 := norm_pairedSpinor_eq_one hQ hρ hu₀₁
  rw [inner_quadraticTwoFormPolar_eq_re_inner o hQ hkl hρ, map_smul,
    cliffordRestriction_ιMulti_zero_two_apply hQ, inner_add_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, h1, h0]
  simp [mul_comm]

include hkl in
/-- **The quadratic term along `e₀ ∧ e₃`**: for a unit canonical spinor `u₀` with paired spinor
`β₀`, `⟪q'(α u₀, f u₀ + g β₀), e₀ ∧ e₃⟫ = Re(α conj g) / 2`. -/
theorem inner_quadraticTwoFormPolar_ιMulti_zero_three
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (α f g : ℂ) :
    ⟪(quadraticTwoFormPolar o ρ hkl (α • u₀) (f • u₀ + g • pairedSpinor e u₀) : ⋀[ℝ]^2 V),
        ιMulti ℝ 2 ![e 0, e 3]⟫ = (α * conj g).re / 2 := by
  have h0 := inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hρ hu₀
  have h1 : ‖pairedSpinor e u₀‖ = 1 := norm_pairedSpinor_eq_one hQ hρ hu₀₁
  rw [inner_quadraticTwoFormPolar_eq_re_inner o hQ hkl hρ, map_smul,
    cliffordRestriction_ιMulti_zero_three_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂₃ hu₀,
    inner_add_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, h1, h0]
  simp [mul_comm]

include hkl he in
/-- **Cross-term polarization identity**: `(√2 / 4) q'(α u₀, β β₀)` lies in the anti-`J`-invariant
plane `span(ρ₁, ρ₂)` with coefficients `(-Im(conj α * β) / 4, Re(conj α * β) / 4)`. -/
theorem smul_quadraticTwoFormPolar_smul_pairedSpinor
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1) (α β : ℂ) :
    (√2 / 4 : ℝ) • quadraticTwoFormPolar o ρ hkl (α • u₀) (β • pairedSpinor e u₀) =
      (-((conj α * β).im / 4)) • AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he +
        ((conj α * β).re / 4) • AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he := by
  have hω_sd := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  set q := quadraticTwoFormPolar o ρ hkl (α • u₀) (β • pairedSpinor e u₀)
  have hq : β • pairedSpinor e u₀ = (0 : ℂ) • u₀ + β • pairedSpinor e u₀ := by simp
  have hq_sd : o.hodgeStar hkl (q : ⋀[ℝ]^2 V) = q :=
    o.hodgeStar_coe_of_mem_eigenspace_one hkl q
  have hω : ⟪J.kahlerSelfDual o hkl hω_sd, q⟫ = 0 := by
    rw [Submodule.coe_inner,
      AlmostComplexStructure.kahlerSelfDual_eq_selfDualWedge he h₀ h₂₃ hω_sd,
      o.inner_selfDualWedge_left_of_hodgeStar_eq_self hkl hq_sd, real_inner_comm]
    dsimp only [q]
    rw [hq, inner_quadraticTwoFormPolar_ιMulti_zero_one hQ hkl h₀ h₂₃ hρ hu₀ hu₀₁]
    simp
  have hρ₁ : ⟪AlmostComplexStructure.antiInvariantSelfDual₁ o e hkl he, q⟫ =
      √2 * ((α * conj β).im / 2) := by
    rw [Submodule.coe_inner, AlmostComplexStructure.antiInvariantSelfDual₁_eq_selfDualWedge,
      o.inner_selfDualWedge_left_of_hodgeStar_eq_self hkl hq_sd, real_inner_comm]
    dsimp only [q]
    rw [hq, inner_quadraticTwoFormPolar_ιMulti_zero_two hQ hkl h₀ h₂₃ hρ hu₀ hu₀₁]
  have hρ₂ : ⟪AlmostComplexStructure.antiInvariantSelfDual₂ o e hkl he, q⟫ =
      √2 * ((α * conj β).re / 2) := by
    rw [Submodule.coe_inner, AlmostComplexStructure.antiInvariantSelfDual₂_eq_selfDualWedge,
      o.inner_selfDualWedge_left_of_hodgeStar_eq_self hkl hq_sd, real_inner_comm]
    dsimp only [q]
    rw [hq, inner_quadraticTwoFormPolar_ιMulti_zero_three hQ hkl h₀ h₂₃ hρ hu₀ hu₀₁]
  have him : (α * conj β).im = -(conj α * β).im := by simp [mul_comm]
  have hre : (α * conj β).re = (conj α * β).re := by simp [mul_comm]
  conv_lhs =>
    rw [AlmostComplexStructure.eq_inner_kahlerSelfDual_add_antiInvariantSelfDual
      (e := e) (he := he) (h₀ := h₀) (h₂ := h₂₃) hω_sd q]
  rw [hω, hρ₁, hρ₂, him, hre, zero_smul, zero_add, smul_add, smul_smul, smul_smul]
  congr 2
  · linear_combination -((conj α * β).im / 8) * Real.mul_self_sqrt zero_le_two
  · linear_combination ((conj α * β).re / 8) * Real.mul_self_sqrt zero_le_two

omit h₀ h₂₃ in
/-- Clifford multiplication by a unit vector `v` maps a unit positive half-spinor `u₀` to a unit
negative half-spinor. -/
theorem norm_halfSpinCliffordMul_ofEq_eq_one
    (hρ : ∀ w, LinearMap.adjoint (ρ (ι Q w)) = -ρ (ι Q w)) {v : V} (hv : ‖v‖ = 1)
    {u₀ : positiveHalfSpinors o ρ} (hu₀₁ : ‖u₀‖ = 1) :
    ‖halfSpinCliffordMul o ρ 1 v
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ) u₀)‖ = 1 := by
  rw [norm_halfSpinCliffordMul_apply o hQ hρ 1 v, hv, one_mul,
    ← Submodule.norm_coe, LinearEquiv.coe_ofEq_apply, Submodule.norm_coe, hu₀₁]

/-- The negative half-spinors `c(e₂) u₀` and `c(e₀) u₀` are orthogonal in `W⁻`. -/
theorem inner_halfSpinCliffordMul_two_zero (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ⟪halfSpinCliffordMul o ρ 1 (e 2)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ) u₀),
      halfSpinCliffordMul o ρ 1 (e 0)
        (LinearEquiv.ofEq _ _ (positiveHalfSpinors_eq_eigenspace o ρ) u₀)⟫_ℂ = 0 := by
  rw [← inner_conj_symm, Submodule.coe_inner, coe_halfSpinCliffordMul_apply_apply,
    coe_halfSpinCliffordMul_apply_apply, LinearEquiv.coe_ofEq_apply,
    inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃) hρ hu₀,
    h₂₃, e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
  simp

include hkl he in
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
  have h0β : halfSpinCliffordMul o ρ 1 (e 0) (ePos (pairedSpinor e u₀)) =
      halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀) :=
    Subtype.ext <| by
      rw [coe_halfSpinCliffordMul_apply_apply, coe_halfSpinCliffordMul_apply_apply,
        LinearEquiv.coe_ofEq_apply, LinearEquiv.coe_ofEq_apply]
      exact ι_zero_apply_pairedSpinor hQ u₀
  have hexp : ν = ⟪pairedSpinor e u₀, φ⟫_ℂ •
        halfSpinCliffordMul o ρ 1 (e 2) (ePos u₀) +
      ⟪u₀, φ⟫_ℂ • halfSpinCliffordMul o ρ 1 (e 0) (ePos u₀) := by
    rw [← hνφ]
    conv_lhs =>
      rw [eq_inner_smul_add_inner_pairedSpinor_smul hQ hkl he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ φ]
    simp only [map_add, map_smul, h0β]
    exact add_comm _ _
  have hw₂₀ := inner_halfSpinCliffordMul_two_zero hQ h₀ h₂₃ hρ hu₀
  conv_rhs => rw [hexp]
  rw [inner_smul_add_smul_of_inner_eq_zero_left
      (norm_halfSpinCliffordMul_ofEq_eq_one hQ hρ (e.orthonormal.1 2) hu₀₁) hw₂₀,
    inner_smul_add_smul_of_inner_eq_zero_right
      (norm_halfSpinCliffordMul_ofEq_eq_one hQ hρ (e.orthonormal.1 0) hu₀₁) hw₂₀, ← hexp]

end SpinorFrame

end TauCeti.SeibergWitten
