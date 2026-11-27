/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Canonical.Dirac
import Mathlib.Algebra.Order.Chebyshev
import TauCeti.Geometry.Symplectic.Complex.AntilinearPart
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The projected Dirac equation bounds `∂bar_a α`

Let `V` be an oriented real inner product space of dimension four with an orthogonal complex
structure `J`, `W` a Hermitian Clifford module with skew-adjoint generators, `c(v) = ρ (ι Q v)` with
`Q v = -‖v‖²`, and `u₀` a positive half-spinor on the canonical line, `P_α u₀ = u₀`. Taubes writes a
positive spinor as `ψ = α u₀ + β` and, with the canonical connection `A₀`, the Dirac equation
`D_A ψ = 0` as

`D_A (α u₀) = √2 ∂bar_a α + α D_{A₀} u₀ = -D_A β`.

This file proves the pointwise algebra of this identity at one point, with the covariant
derivatives taken as data, and the resulting bound on `∂bar_a α`.

**Clifford multiplication sees only `∂bar`.** Let `L : V → ℂ` be real-linear, such as the covariant
derivative `∇_a α` at a point, and let `g₁` and `p` represent its real and imaginary parts. In every
orthonormal basis `b`,

`∑ᵢ L(bᵢ) c(bᵢ) u₀ = c(g₁ + J p) u₀`

(`TauCeti.SeibergWitten.sum_smul_ι_apply_eq_ι_add_apply_of_cliffordProjection_apply_eq_self`), since
`c(J v) u₀ = i c(v) u₀` on the canonical eigenspace. The vector `g₁ + J p` represents the real part
of `2 ∂bar L`, where `∂bar L v = (L v + i L (J v)) / 2` is the complex-antilinear part of `L`, whose
operator norm is `‖g₁ + J p‖ / 2`
(`TauCeti.AlmostComplexStructure.norm_eq_norm_add_apply_div_two`). Hence

`‖∑ᵢ L(bᵢ) c(bᵢ) u₀‖ = 2 ‖∂bar L‖ ‖u₀‖`

(`TauCeti.SeibergWitten.norm_sum_smul_ι_apply_of_cliffordProjection_apply_eq_self`). With the
Hilbert–Schmidt norm `|∂bar L|² = ∑ᵢ |∂bar L (bᵢ)|² = 2 ‖∂bar L‖²` of
`TauCeti.AlmostComplexStructure.sum_norm_sq_complexAntilinearPart` this is Taubes's factor `√2`.

**The Dirac equation.** If `∑ᵢ c(bᵢ) (L(bᵢ) u₀ + wᵢ) = 0`, then
`2 ‖∂bar L‖ ‖u₀‖ = ‖∑ᵢ c(bᵢ) wᵢ‖`
(`TauCeti.SeibergWitten.two_mul_norm_mul_norm_eq_norm_sum_ι_apply_of_sum_ι_apply_eq_zero`). For the
Dirac equation of `ψ = α u₀ + β` in a unitary frame `(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and
`J e₂ = e₃`, one has `wₖ = α ∇_{eₖ} u₀ + ∇_{eₖ} β`, where `∇_{eₖ} u₀` is the derivative of `u₀` for
the canonical connection, normalized as in `TauCeti.Analysis.PDE.SeibergWitten.Canonical.Dirac`.
There `‖D_{A₀} u₀‖ = ‖dω‖ ‖u₀‖ / 2`, so for a unit spinor `u₀`

`‖∂bar_a α‖ ≤ |α| ‖dω‖ / 4 + |∇β|`,

with `|∇β|² = ∑ₖ ‖∇_{eₖ} β‖²`
(`TauCeti.SeibergWitten.norm_le_norm_mul_sqrt_div_four_add_sqrt_of_sum_ι_apply_eq_zero`). On an
almost Kähler manifold `dω = 0`, and the bound is `‖∂bar_a α‖ ≤ |∇β|`
(`TauCeti.SeibergWitten.norm_le_sqrt_sum_norm_sq_of_sum_ι_apply_eq_zero`). Together with the bound
`|∇β| ≤ C` this gives the pointwise bound `|∂bar_a α| ≤ C` that enters the bounds on the
negative part of the slice measures of the cutoff current.

## Main results

* `TauCeti.SeibergWitten.norm_sum_smul_ι_apply_of_cliffordProjection_apply_eq_self`:
  `‖∑ᵢ L(bᵢ) c(bᵢ) u₀‖ = 2 ‖∂bar L‖ ‖u₀‖`.
* `TauCeti.SeibergWitten.two_mul_norm_mul_norm_eq_norm_sum_ι_apply_of_sum_ι_apply_eq_zero`: the
  Dirac equation determines `‖∂bar L‖`.
* `TauCeti.SeibergWitten.norm_le_norm_mul_sqrt_div_four_add_sqrt_of_sum_ι_apply_eq_zero` and
  `TauCeti.SeibergWitten.norm_le_sqrt_sum_norm_sq_of_sum_ι_apply_eq_zero`: the pointwise bound on
  `∂bar_a α` from the projected Dirac equation.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module _root_.exteriorPower
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} {J : AlmostComplexStructure V}
  {L : V → ℂ} {g₁ p : V} {D : V →L[ℝ] ℂ}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-! ### The Dirac symbol of `α u₀` -/

section Orthogonal

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
  {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ V)
  (h₁ : ∀ v, ⟪g₁, v⟫ = (L v).re) (h₂ : ∀ v, ⟪p, v⟫ = (L v).im)

include hQ hJ h₁ h₂ in
/-- **On the canonical eigenspace the Dirac symbol is Clifford multiplication by `2 ∂bar`.** If
`P_α ψ = ψ` and `g₁`, `p` represent the real and imaginary parts of `L : V → ℂ`, then in every
orthonormal basis `∑ᵢ L(bᵢ) c(bᵢ) ψ = c(g₁ + J p) ψ`. The vector `g₁ + J p` represents the real
part of twice the complex-antilinear part `v ↦ (L v + i L (J v)) / 2` of `L`. -/
theorem sum_smul_ι_apply_eq_ι_add_apply_of_cliffordProjection_apply_eq_self
    {ψ : positiveHalfSpinors o ρ} (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ) :
    ∑ i, L (b i) • ρ (ι Q (b i)) ψ = ρ (ι Q (g₁ + J p)) ψ := by
  rw [b.sum_smul_map_ι_apply_eq_add ρ h₁ h₂, map_add, map_add, LinearMap.add_apply,
    ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hJ hψ]

include hQ hJ h₁ h₂ in
/-- **The norm of the Dirac symbol on the canonical eigenspace.** If `P_α ψ = ψ`, the generators are
skew-adjoint and `D v = (L v + i L (J v)) / 2` is the complex-antilinear part of `L`, then in every
orthonormal basis `‖∑ᵢ L(bᵢ) c(bᵢ) ψ‖ = 2 ‖D‖ ‖ψ‖`, with the operator norm of `D`. -/
theorem norm_sum_smul_ι_apply_of_cliffordProjection_apply_eq_self
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ)
    (hD : ∀ v, D v = (L v + Complex.I * L (J v)) / 2) :
    ‖∑ i, L (b i) • ρ (ι Q (b i)) ψ‖ = 2 * ‖D‖ * ‖(ψ : W)‖ := by
  rw [sum_smul_ι_apply_eq_ι_add_apply_of_cliffordProjection_apply_eq_self hQ hJ b h₁ h₂ hψ,
    norm_map_ι_apply hQ hρ, AlmostComplexStructure.norm_eq_norm_add_apply_div_two hJ h₁ h₂ hD]
  ring

include hQ hJ h₁ h₂ in
/-- **The Dirac equation determines `∂bar`.** If `P_α ψ = ψ`, the generators are skew-adjoint,
`D v = (L v + i L (J v)) / 2` is the complex-antilinear part of `L`, and the spinors `wᵢ` satisfy
`∑ᵢ c(bᵢ) (L(bᵢ) ψ + wᵢ) = 0` in an orthonormal basis `b`, then
`2 ‖D‖ ‖ψ‖ = ‖∑ᵢ c(bᵢ) wᵢ‖`. -/
theorem two_mul_norm_mul_norm_eq_norm_sum_ι_apply_of_sum_ι_apply_eq_zero
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ J.kahlerForm ψ = ψ)
    (hD : ∀ v, D v = (L v + Complex.I * L (J v)) / 2) {w : κ → W}
    (hdirac : ∑ i, ρ (ι Q (b i)) (L (b i) • (ψ : W) + w i) = 0) :
    2 * ‖D‖ * ‖(ψ : W)‖ = ‖∑ i, ρ (ι Q (b i)) (w i)‖ := by
  simp only [map_add, map_smul, Finset.sum_add_distrib] at hdirac
  rw [← norm_sum_smul_ι_apply_of_cliffordProjection_apply_eq_self hQ hJ b h₁ h₂ hρ hψ hD,
    eq_neg_of_add_eq_zero_left hdirac, norm_neg]

end Orthogonal

/-! ### The bound on `∂bar_a α` in a unitary frame -/

section Frame

variable {e : OrthonormalBasis (Fin 4) ℝ V} (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  (hg₁ : ∀ v, ⟪g₁, v⟫ = (L v).re) (hp : ∀ v, ⟪p, v⟫ = (L v).im)

include hQ h₀ h₂ hg₁ hp in
/-- **The projected Dirac equation bounds `∂bar_a α`.** In a unitary frame, `J e₀ = e₁` and
`J e₂ = e₃`, let `u₀` be a unit spinor on the canonical line, `u (eₖ)` the derivatives of `u₀` for
the canonical connection, normalized as in
`TauCeti.SeibergWitten.sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero` through the covariant
derivative `θ` of the Kähler form, `α ∈ ℂ`, and `L` the covariant derivative of `α`, with
complex-antilinear part `D v = (L v + i L (J v)) / 2`. If the Dirac equation
`∑ₖ c(eₖ) (L(eₖ) u₀ + α u(eₖ) + yₖ) = 0` holds, where `yₖ = ∇_{eₖ} β`, then

`‖D‖ ≤ |α| √(∑ dω²) / 4 + √(∑ₖ ‖yₖ‖²)`,

where `∑ dω²` is the sum of the squares of the four frame components `dω_abc`, `a < b < c`, of the
alternating sum of `θ`. -/
theorem norm_le_norm_mul_sqrt_div_four_add_sqrt_of_sum_ι_apply_eq_zero
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    (hu₀₁ : ‖(u₀ : W)‖ = 1) {θ : V → ⋀[ℝ]^2 V}
    (hθ : ∀ v a b, ⟪θ v, ιMulti ℝ 2 ![J a, J b]⟫ = -⟪θ v, ιMulti ℝ 2 ![a, b]⟫)
    {u : V → positiveHalfSpinors o ρ} (hu : ∀ v, cliffordProjection o ρ J.kahlerForm (u v) = 0)
    (hL : ∀ v, ρ (bivectorExterior Q (θ v)) u₀ + ρ (bivectorExterior Q J.kahlerForm) (u v) =
      (-2 * Complex.I) • (u v : W))
    (hD : ∀ v, D v = (L v + Complex.I * L (J v)) / 2) (α : ℂ) {y : Fin 4 → W}
    (hdirac : ∑ k, ρ (ι Q (e k)) (L (e k) • (u₀ : W) + (α • (u (e k) : W) + y k)) = 0) :
    ‖D‖ ≤ ‖α‖ * √(twoVectorAlternatingSum θ (e 0) (e 1) (e 2) ^ 2 +
        twoVectorAlternatingSum θ (e 0) (e 1) (e 3) ^ 2 +
        twoVectorAlternatingSum θ (e 0) (e 2) (e 3) ^ 2 +
        twoVectorAlternatingSum θ (e 1) (e 2) (e 3) ^ 2) / 4 + √(∑ k, ‖y k‖ ^ 2) := by
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂
  set S := twoVectorAlternatingSum θ (e 0) (e 1) (e 2) ^ 2 +
    twoVectorAlternatingSum θ (e 0) (e 1) (e 3) ^ 2 +
    twoVectorAlternatingSum θ (e 0) (e 2) (e 3) ^ 2 +
    twoVectorAlternatingSum θ (e 1) (e 2) (e 3) ^ 2
  -- `‖D_{A₀} u₀‖ = √(∑ dω²) / 2` for the unit spinor `u₀`.
  have hA₀ : ‖∑ k, ρ (ι Q (e k)) (u (e k))‖ = √S / 2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sum_ι_apply_sq_of_cliffordProjection_apply_eq_zero
      hQ h₀ h₂ hρ hu₀ hθ hu hL, hu₀₁, one_pow, mul_one,
      Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq two_pos.le]
  -- Each `c(eₖ)` is an isometry, and Cauchy–Schwarz bounds `∑ₖ ‖yₖ‖` by `2 |∇β|`.
  have hy : ‖∑ k, ρ (ι Q (e k)) (y k)‖ ≤ 2 * √(∑ k, ‖y k‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_map_ι_apply hQ hρ, e.orthonormal.1, one_mul]
    have hcs : (∑ k, ‖y k‖) ^ 2 ≤ 4 * ∑ k, ‖y k‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k ↦ ‖y k‖)
    calc ∑ k, ‖y k‖ ≤ √(4 * ∑ k, ‖y k‖ ^ 2) := Real.le_sqrt_of_sq_le hcs
      _ = 2 * √(∑ k, ‖y k‖ ^ 2) := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq two_pos.le]
  have heq := two_mul_norm_mul_norm_eq_norm_sum_ι_apply_of_sum_ι_apply_eq_zero hQ hJ e hg₁ hp hρ
    hu₀ hD hdirac
  simp only [map_add, map_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hu₀₁, mul_one] at heq
  have := heq.trans_le ((norm_add_le _ _).trans (add_le_add (norm_smul_le _ _) hy))
  rw [hA₀] at this
  linarith

include hQ h₀ h₂ hg₁ hp in
/-- **On an almost Kähler manifold `|∂bar_a α| ≤ |∇β|`.** Under the hypotheses of
`TauCeti.SeibergWitten.norm_le_norm_mul_sqrt_div_four_add_sqrt_of_sum_ι_apply_eq_zero`, if every
alternating sum of `θ` vanishes, as it does for `θ = ∇ω` when `dω = 0`, the Dirac equation
`∑ₖ c(eₖ) (L(eₖ) u₀ + α u(eₖ) + yₖ) = 0` gives `‖D‖ ≤ √(∑ₖ ‖yₖ‖²)`: the complex-antilinear part
of the covariant derivative of `α` is bounded by the covariant derivative of `β`. -/
theorem norm_le_sqrt_sum_norm_sq_of_sum_ι_apply_eq_zero
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    (hu₀₁ : ‖(u₀ : W)‖ = 1) {θ : V → ⋀[ℝ]^2 V}
    (hθ : ∀ v a b, ⟪θ v, ιMulti ℝ 2 ![J a, J b]⟫ = -⟪θ v, ιMulti ℝ 2 ![a, b]⟫)
    (hdθ : ∀ a b c, twoVectorAlternatingSum θ a b c = 0)
    {u : V → positiveHalfSpinors o ρ} (hu : ∀ v, cliffordProjection o ρ J.kahlerForm (u v) = 0)
    (hL : ∀ v, ρ (bivectorExterior Q (θ v)) u₀ + ρ (bivectorExterior Q J.kahlerForm) (u v) =
      (-2 * Complex.I) • (u v : W))
    (hD : ∀ v, D v = (L v + Complex.I * L (J v)) / 2) (α : ℂ) {y : Fin 4 → W}
    (hdirac : ∑ k, ρ (ι Q (e k)) (L (e k) • (u₀ : W) + (α • (u (e k) : W) + y k)) = 0) :
    ‖D‖ ≤ √(∑ k, ‖y k‖ ^ 2) := by
  simpa [hdθ] using norm_le_norm_mul_sqrt_div_four_add_sqrt_of_sum_ι_apply_eq_zero hQ h₀ h₂ hg₁ hp
    hρ hu₀ hu₀₁ hθ hu hL hD α hdirac

end Frame

end TauCeti.SeibergWitten
