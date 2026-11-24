/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.LinearAlgebra.CliffordAlgebra.Kahler
import TauCeti.LinearAlgebra.CliffordAlgebra.HalfSpinor
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
Both are the case `β = ω` of an identity for every self-dual two-vector `β` and positive
half-spinor `ψ`: `c(v) c₂(β) ψ = -2 c(v ⌟ β) ψ`
(`Orientation.ι_apply_bivectorExterior_apply_of_hodgeStar_eq_self`), where `v ⌟ ω = J v`. It
follows from the commutator `⁅c₂(β), c(v)⁆ = 2 c(v ⌟ β)`
(`TauCeti.bivectorExterior_lie_ι_of_eq_neg_norm_sq`) and the vanishing of the self-dual form `β`
on the negative half-spinors, where `c(v) ψ` lies. Consequently
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
`e₀ ∧ e₃`.

## Main results

* `TauCeti.SeibergWitten.ι_apply_apply_of_bivectorExterior_apply`: `c(J v) ψ = i c(v) ψ` for
  `c₂(ω) ψ = -2i ψ`, in particular for `P_α ψ = ψ`
  (`TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_self`), and
  `TauCeti.SeibergWitten.ι_apply_apply_of_cliffordProjection_apply_eq_zero`:
  `c(J v) β = -i c(v) β` for `P_α β = 0`.
* `TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_self_iff` and
  `TauCeti.SeibergWitten.cliffordProjection_kahlerForm_apply_eq_zero_iff`: conversely, these
  relations cut out the two eigenspaces.
* `TauCeti.SeibergWitten.ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply`:
  `c(e₁) ψ = i c(e₀) ψ` and `c(e₃) ψ = i c(e₂) ψ` for `c₂(ω) ψ = -2i ψ`, with the resulting
  frame products `TauCeti.SeibergWitten.ι_apply_ι_zero_apply_of_bivectorExterior_apply`,
  `TauCeti.SeibergWitten.ι_apply_ι_two_apply_of_bivectorExterior_apply` and
  `TauCeti.SeibergWitten.ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply`.
* `TauCeti.SeibergWitten.ι_apply_of_bivectorExterior_apply`:
  `c(v) ψ = z₀(v) c(e₀) ψ + z₂(v) c(e₂) ψ` for `c₂(ω) ψ = -2i ψ`, with
  `z₀(v) = ⟪e₀, v⟫ + i ⟪e₁, v⟫` and `z₂(v) = ⟪e₂, v⟫ + i ⟪e₃, v⟫` the coordinates of `v` in the
  basis `(e₀, e₂)` of `(V, J)`.
* `TauCeti.SeibergWitten.ι_apply_ι_apply_of_bivectorExterior_apply`:
  `c(v) c(w) ψ = (z₀(v) z₂(w) - z₂(v) z₀(w)) c(e₀) c(e₂) ψ - (⟪v, w⟫ - i ⟪v, J w⟫) ψ`.
* `bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply`:
  `c(e₀) c(e₂) ψ` lies in the complementary eigenspace.
* `TauCeti.SeibergWitten.inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self`:
  `⟪c(v) ψ, c(w) ψ⟫ = (⟪v, w⟫ - i ⟪v, J w⟫) ‖ψ‖²`.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_of_bivectorExterior_apply`: the Dirac symbol on the
  canonical eigenspace in terms of the two `∂bar`-components.
* `TauCeti.SeibergWitten.norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self`: its
  norm.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self` and
  `TauCeti.SeibergWitten.sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self`:
  it vanishes exactly when both `∂bar`-components vanish, that is when the covector is complex
  linear.
* `TauCeti.SeibergWitten.pairedSpinor`, `TauCeti.SeibergWitten.norm_pairedSpinor` and
  `TauCeti.SeibergWitten.inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self`: the
  paired spinor completes `u₀` to a unitary frame.
* `TauCeti.SeibergWitten.sum_smul_ι_apply_pairedSpinor_of_cliffordProjection_apply_eq_self`: the
  Dirac symbol on the paired spinor in terms of the two `∂`-components.
* `cliffordRestriction_ιMulti_zero_one_apply_of_cliffordProjection_apply_eq_self`,
  `cliffordRestriction_ιMulti_zero_two_apply` and
  `cliffordRestriction_ιMulti_zero_three_apply_of_cliffordProjection_apply_eq_self` (all in
  `TauCeti.SeibergWitten`): the Clifford map along `e₀ ∧ e₁`, `e₀ ∧ e₂`, `e₀ ∧ e₃` on the frame
  `(u₀, β₀)`.

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
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-! ### Two Clifford multiplications on the canonical eigenspace

These formulas are purely algebraic: they hold on any complex Clifford module, with no Hermitian
structure or finite dimensionality on `W`. -/

section ComplexModule

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

include hQ h₀ h₂ in
/-- `c₂(ω) x = c(e₀) c(e₁) x + c(e₂) c(e₃) x` in a unitary frame
(`AlmostComplexStructure.bivectorExterior_kahlerForm`). -/
private theorem map_bivectorExterior_kahlerForm_apply (x : W) :
    ρ (bivectorExterior Q J.kahlerForm) x =
      ρ (ι Q (e 0)) (ρ (ι Q (e 1)) x) + ρ (ι Q (e 2)) (ρ (ι Q (e 3)) x) := by
  rw [AlmostComplexStructure.bivectorExterior_kahlerForm hQ h₀ h₂, map_add, map_mul, map_mul,
    LinearMap.add_apply, mul_apply_eq_comp, mul_apply_eq_comp]

include hQ h₀ h₂ in
/-- On a `-2i`-eigenvector `ψ ∈ W` of `c₂(ω) = c(e₀) c(e₁) + c(e₂) c(e₃)`, the commuting square
roots of `-1` `c(e₀) c(e₁)` and `c(e₂) c(e₃)` both act by `-i`, so `c(e₁) ψ = i c(e₀) ψ` and
`c(e₃) ψ = i c(e₂) ψ`. No chirality or orientation is needed. A positive half-spinor fixed by
`P_α` is such an eigenvector (`bivectorExterior_apply_of_cliffordProjection_apply_eq_self`). -/
theorem ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) ψ = Complex.I • ρ (ι Q (e 0)) ψ ∧
      ρ (ι Q (e 3)) ψ = Complex.I • ρ (ι Q (e 2)) ψ := by
  -- Write `a = c(e₀) c(e₁) ψ` and `b = c(e₂) c(e₃) ψ`, so that `a + b = -2i ψ`.
  have hab : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ) + ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ) =
      (-2 * Complex.I) • ψ := by
    rwa [map_bivectorExterior_kahlerForm_apply hQ h₀ h₂] at hψ
  have hsq (i j : Fin 4) (hij : i ≠ j) (x : W) :
      ρ (ι Q (e i)) (ρ (ι Q (e j)) (ρ (ι Q (e i)) (ρ (ι Q (e j)) x))) = -x := by
    rw [e.map_ι_apply_map_ι_apply_comm hQ ρ hij.symm, map_neg,
      e.map_ι_apply_map_ι_apply hQ ρ, e.map_ι_apply_map_ι_apply hQ ρ, neg_neg]
  have hcomm : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) (ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ))) =
      ρ (ι Q (e 2)) (ρ (ι Q (e 3)) (ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ))) := by
    simp only [e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 2) (by decide),
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 0) (j := 2) (by decide),
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 1) (j := 3) (by decide),
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 0) (j := 3) (by decide), map_neg, neg_neg]
  -- Applying `c(e₀) c(e₁)` and `c(e₂) c(e₃)` to `a + b = -2i ψ` gives `2i (a - b) = 0`.
  have ha := congrArg (fun x ↦ ρ (ι Q (e 0)) (ρ (ι Q (e 1)) x)) hab
  have hb := congrArg (fun x ↦ ρ (ι Q (e 2)) (ρ (ι Q (e 3)) x)) hab
  simp only [map_add, map_smul, hsq 0 1 (by decide), hsq 2 3 (by decide)] at ha hb
  have hdiff : (2 * Complex.I) • (ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ) -
      ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ)) = 0 := by
    linear_combination (norm := module) ha - hb - hcomm
  have heq := sub_eq_zero.1 ((smul_eq_zero.1 hdiff).resolve_left (by simp))
  -- So `a = b = -i ψ`, and multiplying by `c(e₀)`, resp. `c(e₂)`, gives the claim.
  have h01 := congrArg (ρ (ι Q (e 0))) (show ρ (ι Q (e 0)) (ρ (ι Q (e 1)) ψ) =
    (-Complex.I) • ψ by linear_combination (norm := module) (2⁻¹ : ℂ) • (hab + heq))
  have h23 := congrArg (ρ (ι Q (e 2))) (show ρ (ι Q (e 2)) (ρ (ι Q (e 3)) ψ) =
    (-Complex.I) • ψ by linear_combination (norm := module) (2⁻¹ : ℂ) • (hab - heq))
  rw [e.map_ι_apply_map_ι_apply hQ ρ, map_smul] at h01 h23
  exact ⟨by linear_combination (norm := module) -h01, by linear_combination (norm := module) -h23⟩

include hQ h₀ h₂ in
/-- **Clifford multiplication of a complex covector on the canonical eigenspace**: if
`c₂(ω) ψ = -2i ψ`, then `∑ₖ x_k c(e_k) ψ = (x₀ + i x₁) c(e₀) ψ + (x₂ + i x₃) c(e₂) ψ`. Only the two
`∂bar`-components `x₀ + i x₁` and `x₂ + i x₃` of the covector survive. A positive half-spinor fixed
by `P_α` is such an eigenvector (`bivectorExterior_apply_of_cliffordProjection_apply_eq_self`). -/
theorem sum_smul_ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (x : Fin 4 → ℂ) :
    ∑ k, x k • ρ (ι Q (e k)) ψ =
      (x 0 + Complex.I * x 1) • ρ (ι Q (e 0)) ψ + (x 2 + Complex.I * x 3) • ρ (ι Q (e 2)) ψ := by
  obtain ⟨h₁, h₃⟩ := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  rw [Fin.sum_univ_four, h₁, h₃]
  module

include hQ h₀ h₂ in
/-- **Clifford multiplication on the canonical eigenspace in complex coordinates**: if
`c₂(ω) ψ = -2i ψ`, then `c(v) ψ = z₀(v) c(e₀) ψ + z₂(v) c(e₂) ψ`, where
`z₀(v) = ⟪e₀, v⟫ + i ⟪e₁, v⟫` and `z₂(v) = ⟪e₂, v⟫ + i ⟪e₃, v⟫` are the coordinates of `v` in the
basis `(e₀, e₂)` of the complex vector space `(V, J)`
(`AlmostComplexStructure.basisOfOrthonormalBasisFinFour`). A positive half-spinor fixed by `P_α`
is such an eigenvector (`bivectorExterior_apply_of_cliffordProjection_apply_eq_self`). -/
theorem ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (v : V) :
    letI := J.complexModule
    ρ (ι Q v) ψ =
      (AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂).repr v 0 • ρ (ι Q (e 0)) ψ +
        (AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂).repr v 1 •
          ρ (ι Q (e 2)) ψ := by
  rw [e.map_ι_apply_eq_sum ρ v ψ]
  simp only [← Complex.coe_smul, sum_smul_ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ,
    AlmostComplexStructure.basisOfOrthonormalBasisFinFour_repr_apply_zero,
    AlmostComplexStructure.basisOfOrthonormalBasisFinFour_repr_apply_one]

include hQ h₀ h₂ in
/-- **On the canonical eigenspace, Clifford multiplication turns `J` into `i`**: if
`c₂(ω) ψ = -2i ψ`, then `c(J v) ψ = i c(v) ψ`, because the complex coordinates of `J v` are `i`
times those of `v` (`ι_apply_of_bivectorExterior_apply`). -/
theorem ι_apply_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (v : V) :
    ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ := by
  let := J.complexModule
  rw [ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ (J v),
    ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ v, ← J.complexModule_I_smul v, map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul, smul_add, smul_smul]

include hQ h₀ h₂ in
/-- Clifford multiplication by the frame on `c(e₀) ψ`, for a `-2i`-eigenvector `ψ` of `c₂(ω)`:
`c(e₁) c(e₀) ψ = i ψ` and `c(e₃) c(e₀) ψ = -i c(e₀) c(e₂) ψ`. -/
theorem ι_apply_ι_zero_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 0)) ψ) = Complex.I • ψ ∧
      ρ (ι Q (e 3)) (ρ (ι Q (e 0)) ψ) = -(Complex.I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) := by
  obtain ⟨h₁, h₃⟩ := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  constructor
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₁, map_smul,
      e.map_ι_apply_map_ι_apply hQ ρ, smul_neg, neg_neg]
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₃, map_smul]

include hQ h₀ h₂ in
/-- Clifford multiplication by the frame on `c(e₂) ψ`, for a `-2i`-eigenvector `ψ` of `c₂(ω)`:
`c(e₁) c(e₂) ψ = i c(e₀) c(e₂) ψ` and `c(e₃) c(e₂) ψ = i ψ`. -/
theorem ι_apply_ι_two_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 2)) ψ) = Complex.I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) ∧
      ρ (ι Q (e 3)) (ρ (ι Q (e 2)) ψ) = Complex.I • ψ := by
  obtain ⟨h₁, h₃⟩ := ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  constructor
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₁, map_smul,
      e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide), smul_neg, neg_neg]
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), h₃, map_smul,
      e.map_ι_apply_map_ι_apply hQ ρ, smul_neg, neg_neg]

include hQ h₀ h₂ in
/-- Clifford multiplication by the frame on `c(e₀) c(e₂) ψ`, for a `-2i`-eigenvector `ψ` of
`c₂(ω)`: `c(e₁) c(e₀) c(e₂) ψ = i c(e₂) ψ` and `c(e₃) c(e₀) c(e₂) ψ = -i c(e₀) ψ`. -/
theorem ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (ι Q (e 1)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) = Complex.I • ρ (ι Q (e 2)) ψ ∧
      ρ (ι Q (e 3)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) = (-Complex.I) • ρ (ι Q (e 0)) ψ := by
  obtain ⟨p12, p32⟩ := ι_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  constructor
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), p12, map_smul,
      e.map_ι_apply_map_ι_apply hQ ρ, smul_neg, neg_neg]
  · rw [e.map_ι_apply_map_ι_apply_comm hQ ρ (by decide), p32, map_smul, neg_smul]

include hQ h₀ h₂ in
/-- **Two Clifford multiplications on the canonical eigenspace**: if `c₂(ω) ψ = -2i ψ`, then
`c(v) c(w) ψ = (z₀(v) z₂(w) - z₂(v) z₀(w)) c(e₀) c(e₂) ψ - (⟪v, w⟫ - i ⟪v, J w⟫) ψ`,
where `z₀(v) = ⟪e₀, v⟫ + i ⟪e₁, v⟫` and `z₂(v) = ⟪e₂, v⟫ + i ⟪e₃, v⟫` are the coordinates of `v` in
the basis `(e₀, e₂)` of the complex vector space `(V, J)`. The first coefficient is the complex
determinant of `v, w` in this basis, and `⟪v, w⟫ - i ⟪v, J w⟫` is the Hermitian product of
`(V, J)`. -/
theorem ι_apply_ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) (v w : V) :
    letI := J.complexModule
    ρ (ι Q v) (ρ (ι Q w) ψ) =
      ((AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂).repr v 0 *
            (AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂).repr w 1 -
          (AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂).repr v 1 *
            (AlmostComplexStructure.basisOfOrthonormalBasisFinFour h₀ h₂).repr w 0) •
        ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) -
      ((⟪v, w⟫ : ℂ) - ⟪v, J w⟫ * Complex.I) • ψ := by
  obtain ⟨p10, p30⟩ := ι_apply_ι_zero_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  obtain ⟨p12, p32⟩ := ι_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  have p20 := e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide) ψ
  -- The inner products of `(V, J)` in the frame.
  have hvw : ⟪v, w⟫ = ⟪e 0, v⟫ * ⟪e 0, w⟫ + ⟪e 1, v⟫ * ⟪e 1, w⟫ + ⟪e 2, v⟫ * ⟪e 2, w⟫ +
      ⟪e 3, v⟫ * ⟪e 3, w⟫ := by
    rw [← e.sum_inner_mul_inner v w, Fin.sum_univ_four]
    simp only [real_inner_comm v]
  have hvJw : ⟪v, J w⟫ = -⟪e 0, v⟫ * ⟪e 1, w⟫ + ⟪e 1, v⟫ * ⟪e 0, w⟫ - ⟪e 2, v⟫ * ⟪e 3, w⟫ +
      ⟪e 3, v⟫ * ⟪e 2, w⟫ := by
    rw [← e.sum_inner_mul_inner v (J w), Fin.sum_univ_four]
    simp only [real_inner_comm v, ← e.repr_apply_apply,
      AlmostComplexStructure.repr_apply h₀ h₂]
    simp only [e.repr_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [ι_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ w]
  simp only [map_add, map_smul, e.map_ι_apply_eq_sum ρ v, Fin.sum_univ_four, p10, p20, p30, p12,
    p32, e.map_ι_apply_map_ι_apply hQ ρ, hvw, hvJw,
    AlmostComplexStructure.basisOfOrthonormalBasisFinFour_repr_apply_zero,
    AlmostComplexStructure.basisOfOrthonormalBasisFinFour_repr_apply_one, ← Complex.coe_smul]
  push_cast
  match_scalars
  · linear_combination (⟪e 1, v⟫ * ⟪e 1, w⟫ + ⟪e 3, v⟫ * ⟪e 3, w⟫ : ℂ) * Complex.I_sq
  · ring

include hQ h₀ h₂ in
/-- **`c(e₀) c(e₂)` carries the canonical eigenspace into the complementary one**: if
`c₂(ω) ψ = -2i ψ`, then `c₂(ω) (c(e₀) c(e₂) ψ) = 2i c(e₀) c(e₂) ψ`. -/
theorem bivectorExterior_kahlerForm_apply_ι_apply_ι_apply_of_bivectorExterior_apply {ψ : W}
    (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = (-2 * Complex.I) • ψ) :
    ρ (bivectorExterior Q J.kahlerForm) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ)) =
      (2 * Complex.I) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) ψ) := by
  obtain ⟨h1, h3⟩ := ι_apply_ι_zero_apply_ι_two_apply_of_bivectorExterior_apply hQ h₀ h₂ hψ
  rw [map_bivectorExterior_kahlerForm_apply hQ h₀ h₂, h1, h3, map_smul, map_smul,
    e.map_ι_apply_map_ι_apply_comm hQ ρ (i := 2) (j := 0) (by decide)]
  module

end ComplexModule

section HermitianModule

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-! ### `J` acts by `±i` on the two eigenspaces -/

omit [FiniteDimensional ℂ W] in
include hQ hkl he h₀ h₂ in
/-- On a `μ`-eigenvector `ψ ∈ W⁺` of `c₂(ω)`, Clifford multiplication intertwines `J` with the
scalar `-μ / 2`: `2 c(J v) ψ = -μ c(v) ψ`. This is
`Orientation.ι_apply_bivectorExterior_apply_of_hodgeStar_eq_self` for the self-dual `ω`, whose
contraction is `v ⌟ ω = J v`. -/
private theorem two_smul_ι_apply_apply_of_bivectorExterior_apply {ψ : positiveHalfSpinors o ρ}
    {μ : ℂ} (hψ : ρ (bivectorExterior Q J.kahlerForm) ψ = μ • (ψ : W)) (v : V) :
    (2 : ℂ) • ρ (ι Q (J v)) ψ = -μ • ρ (ι Q v) ψ := by
  have h := o.ι_apply_bivectorExterior_apply_of_hodgeStar_eq_self hQ hkl
    (AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂ hkl he) ψ v
  rw [hψ, map_smul, AlmostComplexStructure.twoVectorContraction_kahlerForm
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂)] at h
  linear_combination (norm := module) h

include hQ h₀ h₂ in
/-- **On the canonical eigenspace, Clifford multiplication turns `J` into `i`**: if
`P_α ψ = ψ`, then `c(J v) ψ = i c(v) ψ` (`ι_apply_apply_of_bivectorExterior_apply`). -/
theorem ι_apply_apply_of_cliffordProjection_apply_eq_self {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (v : V) :
    ρ (ι Q (J v)) ψ = Complex.I • ρ (ι Q v) ψ :=
  ι_apply_apply_of_bivectorExterior_apply hQ h₀ h₂
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hψ) v

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

include hQ h₀ h₂ in
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
    rw [ι_apply_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hψ, inner_smul_right,
      Complex.mul_re, Complex.I_re, Complex.I_im] at h
    linarith
  apply Complex.ext <;> simp [hre, him, ← Complex.ofReal_pow]

/-! ### The Dirac symbol on the canonical eigenspace -/

include hQ h₀ h₂ in
/-- The norm of the Dirac symbol on the canonical eigenspace
(`sum_smul_ι_apply_of_bivectorExterior_apply`):
`‖∑ₖ x_k c(e_k) ψ‖² = (|x₀ + i x₁|² + |x₂ + i x₃|²) ‖ψ‖²`. -/
theorem norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (x : Fin 4 → ℂ) :
    ‖∑ k, x k • ρ (ι Q (e k)) ψ‖ ^ 2 =
      (‖x 0 + Complex.I * x 1‖ ^ 2 + ‖x 2 + Complex.I * x 3‖ ^ 2) * ‖(ψ : W)‖ ^ 2 := by
  -- `c(e₀) ψ` and `c(e₂) ψ` are orthogonal of norm `‖ψ‖`.
  have horth : ⟪ρ (ι Q (e 0)) ψ, ρ (ι Q (e 2)) ψ⟫_ℂ = 0 := by
    rw [inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hρ hψ, h₂,
      e.orthonormal.2 (by decide), e.orthonormal.2 (by decide)]
    simp
  have hnorm (k : Fin 4) : ‖ρ (ι Q (e k)) ψ‖ = ‖(ψ : W)‖ := by
    rw [norm_map_ι_apply hQ hρ, e.orthonormal.1 k, one_mul]
  rw [sum_smul_ι_apply_of_bivectorExterior_apply hQ h₀ h₂
      (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hψ),
    norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, horth]
  simp only [mul_zero, RCLike.zero_re, add_zero, norm_smul, hnorm]
  ring

include hQ h₀ h₂ in
/-- **The Dirac symbol on the canonical eigenspace vanishes exactly on `∂bar`-closed
covectors**: for `P_α ψ = ψ`, `∑ₖ x_k c(e_k) ψ = 0` if and only if `ψ = 0` or
`x₀ + i x₁ = x₂ + i x₃ = 0`. -/
theorem sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) (x : Fin 4 → ℂ) :
    ∑ k, x k • ρ (ι Q (e k)) ψ = 0 ↔
      (ψ : W) = 0 ∨ (x 0 + Complex.I * x 1 = 0 ∧ x 2 + Complex.I * x 3 = 0) := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff,
    norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hρ hψ,
    mul_eq_zero, add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)]
  simp only [sq_eq_zero_iff, norm_eq_zero]
  tauto

include hQ h₀ h₂ in
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
  rw [sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hρ hψ
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

/-! ### The paired spinor -/

section PairedSpinor

open Complex exteriorPower

omit [FiniteDimensional ℂ W] in
variable (e) in
/-- The **paired spinor** `c(e₂) c(e₀) u₀` of a positive spinor `u₀`, for an orthonormal frame
`e`. When `u₀` spans the canonical eigenspace, it spans the complementary eigenspace of `W⁺`, and
together with `u₀` it gives a unitary frame of `W⁺` when `W⁺` has rank two (`norm_pairedSpinor`,
`inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self`). -/
def pairedSpinor (u₀ : positiveHalfSpinors o ρ) : positiveHalfSpinors o ρ :=
  ⟨ρ (ι Q (e 2)) (ρ (ι Q (e 0)) u₀), by
    have h := map_ι_apply_mem_eigenspace_chirality_neg o
      (map_ι_apply_mem_eigenspace_chirality_neg o (ε := 1)
        (by simpa using mem_positiveHalfSpinors.1 u₀.property) (e 0)) (e 2)
    exact mem_positiveHalfSpinors.2 (by simpa using Module.End.mem_eigenspace_iff.1 h)⟩

omit [FiniteDimensional ℂ W] in
/-- The paired spinor as a vector of `W`. -/
@[simp]
theorem coe_pairedSpinor (u₀ : positiveHalfSpinors o ρ) :
    (pairedSpinor e u₀ : W) = ρ (ι Q (e 2)) (ρ (ι Q (e 0)) u₀) :=
  (rfl)

omit [FiniteDimensional ℂ W] in
include hQ in
/-- `c(e₀) β₀ = c(e₂) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`. -/
theorem ι_zero_apply_pairedSpinor (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 0)) (pairedSpinor e u₀ : W) = ρ (ι Q (e 2)) u₀ := by
  rw [coe_pairedSpinor,
    map_ι_apply_map_ι_apply_comm_of_isOrtho ρ (e.isOrtho_apply hQ (by decide : (0 : Fin 4) ≠ 2))]
  simp [hQ, e.orthonormal.1 0]

omit [FiniteDimensional ℂ W] in
include hQ in
/-- `c(e₂) β₀ = -c(e₀) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`. -/
theorem ι_two_apply_pairedSpinor (u₀ : positiveHalfSpinors o ρ) :
    ρ (ι Q (e 2)) (pairedSpinor e u₀ : W) = -ρ (ι Q (e 0)) u₀ := by
  simp [hQ, e.orthonormal.1 2]

include hQ in
/-- `C(i e₀ ∧ e₂) ψ = -i β` for a positive spinor `ψ` and its paired spinor `β`. -/
theorem cliffordRestriction_ιMulti_zero_two_apply (ψ : positiveHalfSpinors o ρ) :
    cliffordRestriction o ρ (ιMulti ℝ 2 ![e 0, e 2]) ψ = -I • pairedSpinor e ψ := by
  apply Subtype.ext
  rw [coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ (e.orthonormal.2 (by decide)),
    map_mul, mul_apply_eq_comp, Submodule.coe_smul, coe_pairedSpinor,
    map_ι_apply_map_ι_apply_comm_of_isOrtho ρ (e.isOrtho_apply hQ (by decide : (0 : Fin 4) ≠ 2)),
    smul_neg, neg_smul]

variable (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))

include hQ hρ in
/-- The paired spinor has the norm of `u₀`. -/
theorem norm_pairedSpinor (u₀ : positiveHalfSpinors o ρ) : ‖pairedSpinor e u₀‖ = ‖u₀‖ := by
  rw [← Submodule.norm_coe, coe_pairedSpinor, norm_map_ι_apply hQ hρ, norm_map_ι_apply hQ hρ,
    e.orthonormal.1 2, e.orthonormal.1 0, one_mul, one_mul, Submodule.norm_coe]

variable {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)

include hQ h₀ h₂ hρ hu₀ in
/-- The paired spinor of a canonical spinor `u₀` is orthogonal to `u₀`. -/
theorem inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self :
    ⟪u₀, pairedSpinor e u₀⟫_ℂ = 0 := by
  rw [Submodule.coe_inner, coe_pairedSpinor, ← LinearMap.adjoint_inner_left, hρ,
    LinearMap.neg_apply, inner_neg_left,
    inner_ι_apply_ι_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hρ hu₀, h₀,
    e.orthonormal.2 (by decide : (2 : Fin 4) ≠ 0), e.orthonormal.2 (by decide : (2 : Fin 4) ≠ 1)]
  simp

include hQ h₀ h₂ hu₀

/-- `c(e₁) u₀ = i c(e₀) u₀` and `c(e₃) u₀ = i c(e₂) u₀` for a canonical spinor `u₀`
(`ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply`). -/
private theorem ι_one_apply_and_ι_three_apply_of_cliffordProjection_apply_eq_self :
    ρ (ι Q (e 1)) u₀ = I • ρ (ι Q (e 0)) u₀ ∧ ρ (ι Q (e 3)) u₀ = I • ρ (ι Q (e 2)) u₀ :=
  ι_one_apply_and_ι_three_apply_of_bivectorExterior_apply hQ h₀ h₂
    (bivectorExterior_apply_of_cliffordProjection_apply_eq_self o ρ hu₀)

/-- `c(e₁) β₀ = -i c(e₂) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`. -/
theorem ι_one_apply_pairedSpinor_of_cliffordProjection_apply_eq_self :
    ρ (ι Q (e 1)) (pairedSpinor e u₀ : W) = -I • ρ (ι Q (e 2)) u₀ := by
  obtain ⟨h₁, -⟩ := ι_one_apply_and_ι_three_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hu₀
  rw [coe_pairedSpinor,
    map_ι_apply_map_ι_apply_comm_of_isOrtho ρ (e.isOrtho_apply hQ (by decide : (1 : Fin 4) ≠ 2)),
    map_ι_apply_map_ι_apply_comm_of_isOrtho ρ (e.isOrtho_apply hQ (by decide : (1 : Fin 4) ≠ 0)),
    h₁]
  simp [hQ, e.orthonormal.1 0]

/-- `c(e₃) β₀ = i c(e₀) u₀` for the paired spinor `β₀ = c(e₂) c(e₀) u₀`. -/
theorem ι_three_apply_pairedSpinor_of_cliffordProjection_apply_eq_self :
    ρ (ι Q (e 3)) (pairedSpinor e u₀ : W) = I • ρ (ι Q (e 0)) u₀ := by
  obtain ⟨-, h₃⟩ := ι_one_apply_and_ι_three_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hu₀
  rw [coe_pairedSpinor,
    map_ι_apply_map_ι_apply_comm_of_isOrtho ρ (e.isOrtho_apply hQ (by decide : (3 : Fin 4) ≠ 2)),
    map_ι_apply_map_ι_apply_comm_of_isOrtho ρ (e.isOrtho_apply hQ (by decide : (3 : Fin 4) ≠ 0)),
    h₃]
  simp [map_ι_apply_map_ι_apply_comm_of_isOrtho ρ
    (e.isOrtho_apply hQ (by decide : (0 : Fin 4) ≠ 2)), hQ, e.orthonormal.1 2]

/-- **The Dirac symbol on the paired spinor**: for the paired spinor `β₀ = c(e₂) c(e₀) u₀` of a
canonical spinor `u₀`,
`∑ₖ y_k c(e_k) β₀ = (y₀ - i y₁) c(e₂) u₀ - (y₂ - i y₃) c(e₀) u₀`. Only the two `∂`-components
`y₀ - i y₁` and `y₂ - i y₃` survive, and they land on the two frame vectors `c(e₂) u₀` and
`c(e₀) u₀` of `W⁻` in the opposite order from the canonical eigenspace
(`sum_smul_ι_apply_of_bivectorExterior_apply`). -/
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
  obtain ⟨h₁, -⟩ := ι_one_apply_and_ι_three_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hu₀
  rw [coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ (e.orthonormal.2 (by decide)),
    map_mul, mul_apply_eq_comp, h₁, map_smul, smul_smul, I_mul_I]
  simp [hQ, e.orthonormal.1 0]

/-- `C(i e₀ ∧ e₃) u₀ = β₀` for a canonical spinor `u₀` and its paired spinor `β₀`. -/
theorem cliffordRestriction_ιMulti_zero_three_apply_of_cliffordProjection_apply_eq_self :
    cliffordRestriction o ρ (ιMulti ℝ 2 ![e 0, e 3]) u₀ = pairedSpinor e u₀ := by
  apply Subtype.ext
  obtain ⟨-, h₃⟩ := ι_one_apply_and_ι_three_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hu₀
  rw [coe_cliffordRestriction_ιMulti_apply_of_inner_eq_zero o ρ hQ (e.orthonormal.2 (by decide)),
    map_mul, mul_apply_eq_comp, h₃, map_smul, smul_smul, I_mul_I,
    coe_pairedSpinor,
    map_ι_apply_map_ι_apply_comm_of_isOrtho ρ (e.isOrtho_apply hQ (by decide : (0 : Fin 4) ≠ 2)),
    neg_smul, one_smul, neg_neg]

end PairedSpinor

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
  rw [map_add, ι_apply_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hφ (e 0),
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
  refine ⟨fun hψ ↦ ι_apply_apply_of_cliffordProjection_apply_eq_self hQ h₀ h₂ hψ, fun h ↦ ?_⟩
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

end HermitianModule

end TauCeti.SeibergWitten
