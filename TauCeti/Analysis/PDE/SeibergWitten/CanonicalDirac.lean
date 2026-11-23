/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The Dirac operator of the canonical spinor of an almost Hermitian four-manifold

Let `X` be an oriented Riemannian four-manifold with an orthogonal almost complex structure `J`
inducing the orientation and Kähler form `ω`, and let `u₀` be a unit section of the canonical line
of `W⁺`, the `-2i`-eigenline of the Clifford action `c₂(ω)`. Taubes's analysis of the
large-parameter Seiberg–Witten equations uses the canonical connection `A₀` on the determinant
line, characterized by the property that `∇_{A₀} u₀` has no component along `u₀`, and the identity

`D_{A₀} u₀ = 0`  when `dω = 0`,

which makes the Dirac equation `D_A (α u₀ + β) = 0` read `√2 ∂bar_a α = -D_A β`. This file proves
the pointwise algebra behind that identity, at one point of `X`, with the covariant derivatives
taken as data. Fix a positively oriented unitary frame `(e₀, e₁, e₂, e₃)`, `J e₀ = e₁` and
`J e₂ = e₃`, and write `c(v) = ρ (ι Q v)`.

* `θ v = ∇_v ω` is the covariant derivative of the Kähler form for a metric connection. Since `J`
  is orthogonal and squares to `-1`, `∇_v J` anticommutes with `J`, so each `θ v` is
  anti-`J`-invariant: `θ v (J a, J b) = -θ v (a, b)`.
* `u v = ∇_v u₀` is a positive half-spinor. Differentiating `c₂(ω) u₀ = -2i u₀` with a connection
  compatible with Clifford multiplication gives the Leibniz relation
  `c₂(θ v) u₀ + c₂(ω) (u v) = -2i u v`. The defining property of `A₀` is `P_α (u v) = 0`.

The Leibniz relation and `P_α (u v) = 0` determine the derivative: `u v = (i / 4) c₂(θ v) u₀`
(`TauCeti.SeibergWitten.eq_I_div_four_smul_of_cliffordProjection_apply_eq_zero`). On the
canonical eigenspace, `c₂` of a two-form `x` is computed in the frame by
`c₂(x) u₀ = -i (x₀₁ + x₂₃) u₀ + (x₀₂ - x₁₃ + i (x₀₃ + x₁₂)) c(e₀) c(e₂) u₀`, with
`xᵢⱼ = x(eᵢ, eⱼ)`
(`TauCeti.SeibergWitten.bivectorExterior_apply_eq_of_cliffordProjection_apply_eq_self`).
For anti-`J`-invariant `x` the first coefficient vanishes. Summing `c(e_k) (u e_k)` and
collecting terms, the Dirac operator `D_{A₀} u₀ = ∑ₖ c(e_k) ∇_{e_k} u₀` is

`D_{A₀} u₀ = (i / 2) ((dω₁₂₃ - i dω₀₂₃) c(e₀) u₀ + (dω₀₁₃ - i dω₀₁₂) c(e₂) u₀)`

(`TauCeti.SeibergWitten.sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero`), where
`dω_abc = θ(e_a)(e_b, e_c) - θ(e_b)(e_a, e_c) + θ(e_c)(e_a, e_b)` is the alternating sum
`TauCeti.twoVectorAlternatingSum`. For the Levi-Civita connection, which is torsion free, this
alternating sum is the exterior derivative `dω(e_a, e_b, e_c)`. Since `c(e₀) u₀` and `c(e₂) u₀` are
orthogonal of norm `‖u₀‖`, this gives `‖D_{A₀} u₀‖ = ‖dω‖ ‖u₀‖ / 2`
(`TauCeti.SeibergWitten.norm_sum_ι_apply_sq_of_cliffordProjection_apply_eq_zero`). Hence:

* if `dω = 0`, as on an almost Kähler manifold, then `D_{A₀} u₀ = 0`
  (`TauCeti.SeibergWitten.sum_ι_apply_eq_zero_of_twoVectorAlternatingSum_eq_zero`);
* conversely, for `u₀ ≠ 0`, `D_{A₀} u₀` vanishes only where `dω` does
  (`TauCeti.SeibergWitten.sum_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_zero`).

No integrability of `J` is used: the intrinsic torsion `∇ω` of a non-Kähler almost Kähler
structure is nonzero, and only its alternation `dω` enters `D_{A₀} u₀`.

The bundle-level construction of `A₀` and `u₀`, and the identification of `θ` and `u` with
covariant derivatives on an actual manifold, are not done here.

## Main results

* `TauCeti.SeibergWitten.bivectorExterior_apply_eq_of_cliffordProjection_apply_eq_self`: the frame
  formula for `c₂(x) u₀`.
* `TauCeti.SeibergWitten.eq_I_div_four_smul_of_cliffordProjection_apply_eq_zero`: the derivative
  of the canonical spinor for the canonical connection, `∇_v u₀ = (i / 4) c₂(∇_v ω) u₀`.
* `TauCeti.SeibergWitten.sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero`: `D_{A₀} u₀` in terms
  of `dω`.
* `TauCeti.SeibergWitten.sum_ι_apply_eq_zero_of_twoVectorAlternatingSum_eq_zero`:
  `D_{A₀} u₀ = 0` when `dω = 0`.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module _root_.exteriorPower
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

/-! ### The Clifford action of two-forms on the canonical line -/

include hQ hkl he h₀ h₂ in
/-- On the canonical eigenspace, `c(e₁) u₀ = i c(e₀) u₀` and `c(e₃) u₀ = i c(e₂) u₀`. -/
private theorem ι_apply_one_three_of_cliffordProjection_apply_eq_self
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 1)) u₀ = Complex.I • ρ (ι Q (e 0)) u₀ ∧
      ρ (ι Q (e 3)) u₀ = Complex.I • ρ (ι Q (e 2)) u₀ := by
  rw [← h₀, ← h₂]
  exact ⟨ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀ (e 0),
    ι_apply_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀ (e 2)⟩

include hQ hkl he h₀ h₂ in
/-- **The Clifford action of a two-form on the canonical eigenspace, in a unitary frame.** If
`P_α u₀ = u₀`, then with `xᵢⱼ = ⟪x, eᵢ ∧ eⱼ⟫`,
`c₂(x) u₀ = -i (x₀₁ + x₂₃) u₀ + (x₀₂ - x₁₃ + i (x₀₃ + x₁₂)) c(e₀) c(e₂) u₀`. The first term is the
component of `x` along the Kähler form `ω = e₀ ∧ e₁ + e₂ ∧ e₃`, and the vector `c(e₀) c(e₂) u₀`
spans the image of the anti-`J`-invariant forms. -/
theorem bivectorExterior_apply_eq_of_cliffordProjection_apply_eq_self
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    (x : ⋀[ℝ]^2 V) :
    ρ (bivectorExterior Q x) u₀ =
      (-(((⟪x, ιMulti ℝ 2 ![e 0, e 1]⟫ + ⟪x, ιMulti ℝ 2 ![e 2, e 3]⟫ : ℝ) : ℂ) *
          Complex.I)) • (u₀ : W) +
        (((⟪x, ιMulti ℝ 2 ![e 0, e 2]⟫ - ⟪x, ιMulti ℝ 2 ![e 1, e 3]⟫ : ℝ) : ℂ) +
          ((⟪x, ιMulti ℝ 2 ![e 0, e 3]⟫ + ⟪x, ιMulti ℝ 2 ![e 1, e 2]⟫ : ℝ) : ℂ) *
            Complex.I) • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
  obtain ⟨h₁, h₃⟩ := ι_apply_one_three_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀
  have hsq := e.map_ι_apply_map_ι_apply hQ ρ
  have hanti {i j : Fin 4} (hij : i ≠ j) := e.map_ι_apply_map_ι_apply_comm hQ ρ hij
  -- The six products `c(eᵢ) c(eⱼ) u₀`.
  have p01 : ρ (ι Q (e 0)) (ρ (ι Q (e 1)) u₀) = (-Complex.I) • (u₀ : W) := by
    rw [h₁, map_smul, hsq]
    module
  have p23 : ρ (ι Q (e 2)) (ρ (ι Q (e 3)) u₀) = (-Complex.I) • (u₀ : W) := by
    rw [h₃, map_smul, hsq]
    module
  have p03 : ρ (ι Q (e 0)) (ρ (ι Q (e 3)) u₀) =
      Complex.I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [h₃, map_smul]
  have p12 : ρ (ι Q (e 1)) (ρ (ι Q (e 2)) u₀) =
      Complex.I • ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [hanti (by decide), h₁, map_smul, hanti (by decide)]
    module
  have p13 : ρ (ι Q (e 1)) (ρ (ι Q (e 3)) u₀) = -ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀) := by
    rw [h₃, map_smul, p12, smul_smul, Complex.I_mul_I]
    module
  have ho {i j : Fin 4} (hij : i ≠ j) : Q.IsOrtho (e i) (e j) := e.isOrtho_apply hQ hij
  conv_lhs => rw [e.eq_sum_inner_smul_ιMulti_two x]
  simp only [map_add, map_smul, map_mul, LinearMap.add_apply, LinearMap.smul_apply,
    bivectorExterior_apply_ιMulti,
    bivector_eq_ι_mul_ι_of_isOrtho Q (ho (by decide : (0 : Fin 4) ≠ 1)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (ho (by decide : (0 : Fin 4) ≠ 2)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (ho (by decide : (0 : Fin 4) ≠ 3)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (ho (by decide : (1 : Fin 4) ≠ 2)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (ho (by decide : (1 : Fin 4) ≠ 3)),
    bivector_eq_ι_mul_ι_of_isOrtho Q (ho (by decide : (2 : Fin 4) ≠ 3)),
    mul_apply_eq_comp, p01, p23, p03, p12, p13, ← Complex.coe_smul]
  push_cast
  match_scalars <;> ring_nf

/-! ### The derivative of the canonical spinor -/

/-- **The derivative of the canonical spinor for the canonical connection.** Let `u₀` satisfy
`c₂(ω) u₀ = -2i u₀` and let `u` be a positive half-spinor with `P_α u = 0`. If
`c₂(θ) u₀ + c₂(ω) u = -2i u`, the Leibniz rule for the derivative `θ = ∇_v ω`, `u = ∇_v u₀`, then
`u = (i / 4) c₂(θ) u₀`. -/
theorem eq_I_div_four_smul_of_cliffordProjection_apply_eq_zero {u₀ : W}
    {u : positiveHalfSpinors o ρ} {ω θ : ⋀[ℝ]^2 V}
    (hu : cliffordProjection o ρ ω u = 0)
    (hL : ρ (bivectorExterior Q θ) u₀ + ρ (bivectorExterior Q ω) u =
      (-2 * Complex.I) • (u : W)) :
    (u : W) = (Complex.I / 4) • ρ (bivectorExterior Q θ) u₀ := by
  have hθ : ρ (bivectorExterior Q θ) u₀ = (-4 * Complex.I) • (u : W) := by
    linear_combination (norm := module)
      hL - bivectorExterior_apply_of_cliffordProjection_apply_eq_zero o ρ hu
  rw [hθ, smul_smul, show Complex.I / 4 * (-4 * Complex.I) = 1 by
    linear_combination -Complex.I_mul_I, one_smul]

/-! ### The Dirac operator of the canonical spinor -/

include hQ hkl he h₀ h₂ in
/-- Clifford multiplication by the frame on `β₀ = c(e₀) c(e₂) u₀`, for `u₀` in the canonical
eigenspace: `c(e₀) β₀ = -c(e₂) u₀`, `c(e₁) β₀ = i c(e₂) u₀`, `c(e₂) β₀ = c(e₀) u₀` and
`c(e₃) β₀ = -i c(e₀) u₀`. -/
private theorem map_ι_apply_map_ι_apply_map_ι_apply_of_cliffordProjection
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) :
    ρ (ι Q (e 0)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀)) = -ρ (ι Q (e 2)) u₀ ∧
      ρ (ι Q (e 1)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀)) = Complex.I • ρ (ι Q (e 2)) u₀ ∧
      ρ (ι Q (e 2)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀)) = ρ (ι Q (e 0)) u₀ ∧
      ρ (ι Q (e 3)) (ρ (ι Q (e 0)) (ρ (ι Q (e 2)) u₀)) = (-Complex.I) • ρ (ι Q (e 0)) u₀ := by
  obtain ⟨h₁, h₃⟩ := ι_apply_one_three_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀
  have hsq := e.map_ι_apply_map_ι_apply hQ ρ
  have hanti {i j : Fin 4} (hij : i ≠ j) := e.map_ι_apply_map_ι_apply_comm hQ ρ hij
  refine ⟨hsq _ _, ?_, ?_, ?_⟩
  · rw [hanti (i := 1) (j := 0) (by decide), hanti (i := 1) (j := 2) (by decide), h₁]
    simp only [map_neg, map_smul]
    rw [hanti (i := 2) (j := 0) (by decide)]
    simp only [map_neg, hsq]
    module
  · rw [hanti (i := 2) (j := 0) (by decide), hsq]
    simp only [map_neg, neg_neg]
  · rw [hanti (i := 3) (j := 0) (by decide), hanti (i := 3) (j := 2) (by decide), h₃]
    simp only [map_neg, map_smul, hsq]
    module

include hQ hkl he h₀ h₂ in
/-- **Taubes's Dirac operator of the canonical spinor, at a point.** Let `u₀` lie in the
canonical eigenspace, let `θ v = ∇_v ω` be anti-`J`-invariant, and let `u v = ∇_v u₀` be positive
half-spinors with `P_α (u v) = 0`, the defining property of the canonical connection `A₀`,
satisfying the Leibniz relation `c₂(θ v) u₀ + c₂(ω) (u v) = -2i u v`. Then
`D_{A₀} u₀ = ∑ₖ c(e_k) (u e_k)` is
`(i / 2) ((dω₁₂₃ - i dω₀₂₃) c(e₀) u₀ + (dω₀₁₃ - i dω₀₁₂) c(e₂) u₀)`, where
`dω_abc = twoVectorAlternatingSum θ (e a) (e b) (e c)`. -/
theorem sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    {θ : V → ⋀[ℝ]^2 V}
    (hθ : ∀ v a b, ⟪θ v, ιMulti ℝ 2 ![J a, J b]⟫ = -⟪θ v, ιMulti ℝ 2 ![a, b]⟫)
    {u : V → positiveHalfSpinors o ρ} (hu : ∀ v, cliffordProjection o ρ J.kahlerForm (u v) = 0)
    (hL : ∀ v, ρ (bivectorExterior Q (θ v)) u₀ + ρ (bivectorExterior Q J.kahlerForm) (u v) =
      (-2 * Complex.I) • (u v : W)) :
    ∑ k, ρ (ι Q (e k)) (u (e k)) =
      (Complex.I / 2) •
        (((twoVectorAlternatingSum θ (e 1) (e 2) (e 3) : ℂ) -
              twoVectorAlternatingSum θ (e 0) (e 2) (e 3) * Complex.I) • ρ (ι Q (e 0)) u₀ +
          ((twoVectorAlternatingSum θ (e 0) (e 1) (e 3) : ℂ) -
              twoVectorAlternatingSum θ (e 0) (e 1) (e 2) * Complex.I) • ρ (ι Q (e 2)) u₀) := by
  obtain ⟨q0, q1, q2, q3⟩ :=
    map_ι_apply_map_ι_apply_map_ι_apply_of_cliffordProjection hQ hkl he h₀ h₂ hu₀
  set β₀ := ρ (ι Q (e 0)) (ρ (ι Q (e 2)) (u₀ : W)) with hβ₀
  -- Each derivative is `(i / 4) c₂(θ v) u₀`, a multiple of `β₀`.
  have hu' (k : Fin 4) : (u (e k) : W) = (Complex.I / 4) •
      ((((⟪θ (e k), ιMulti ℝ 2 ![e 0, e 2]⟫ - ⟪θ (e k), ιMulti ℝ 2 ![e 1, e 3]⟫ : ℝ) : ℂ) +
        ((⟪θ (e k), ιMulti ℝ 2 ![e 0, e 3]⟫ + ⟪θ (e k), ιMulti ℝ 2 ![e 1, e 2]⟫ : ℝ) : ℂ) *
          Complex.I) • β₀) := by
    obtain ⟨h01, h23, -, -⟩ :=
      AlmostComplexStructure.inner_ιMulti_of_antiinvariant h₀ h₂ (hθ (e k))
    rw [eq_I_div_four_smul_of_cliffordProjection_apply_eq_zero (hu (e k)) (hL (e k)),
      bivectorExterior_apply_eq_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀, h01,
      h23]
    simp [hβ₀]
  -- Rewrite the alternating sums with the coordinates `θ(e_k)(eᵢ, eⱼ)`, `i < j`.
  obtain ⟨-, h23₀, h13₀, h12₀⟩ :=
    AlmostComplexStructure.inner_ιMulti_of_antiinvariant h₀ h₂ (hθ (e 0))
  obtain ⟨-, h23₁, h13₁, h12₁⟩ :=
    AlmostComplexStructure.inner_ιMulti_of_antiinvariant h₀ h₂ (hθ (e 1))
  obtain ⟨h01₂, -, h13₂, h12₂⟩ :=
    AlmostComplexStructure.inner_ιMulti_of_antiinvariant h₀ h₂ (hθ (e 2))
  obtain ⟨h01₃, -, h13₃, h12₃⟩ :=
    AlmostComplexStructure.inner_ιMulti_of_antiinvariant h₀ h₂ (hθ (e 3))
  simp only [twoVectorAlternatingSum_def, h13₀, h12₀, h23₁, h01₂, h13₂, h01₃, h12₃, h23₀]
  simp only [Fin.sum_univ_four, hu', map_smul, q0, q1, q2, q3, h13₀, h12₀, h13₁, h12₁,
    h13₂, h12₂, h13₃, h12₃]
  push_cast
  match_scalars
  · linear_combination
      (Complex.I / 2 * (⟪θ (e 1), ιMulti ℝ 2 ![e 0, e 3]⟫ : ℂ)) * Complex.I_sq
  · linear_combination
      (-Complex.I / 2 * (⟪θ (e 3), ιMulti ℝ 2 ![e 0, e 3]⟫ : ℂ)) * Complex.I_sq

include hQ hkl he h₀ h₂ in
/-- **`D_{A₀} u₀ = 0` when `dω = 0`.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero`, if every alternating
sum of `θ` vanishes, as it does for `θ = ∇ω` on an almost Kähler manifold, the Dirac operator of the
canonical spinor vanishes: `∑ₖ c(e_k) (u e_k) = 0`. -/
theorem sum_ι_apply_eq_zero_of_twoVectorAlternatingSum_eq_zero
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    {θ : V → ⋀[ℝ]^2 V}
    (hθ : ∀ v a b, ⟪θ v, ιMulti ℝ 2 ![J a, J b]⟫ = -⟪θ v, ιMulti ℝ 2 ![a, b]⟫)
    (hdθ : ∀ a b c, twoVectorAlternatingSum θ a b c = 0)
    {u : V → positiveHalfSpinors o ρ} (hu : ∀ v, cliffordProjection o ρ J.kahlerForm (u v) = 0)
    (hL : ∀ v, ρ (bivectorExterior Q (θ v)) u₀ + ρ (bivectorExterior Q J.kahlerForm) (u v) =
      (-2 * Complex.I) • (u v : W)) :
    ∑ k, ρ (ι Q (e k)) (u (e k)) = 0 := by
  rw [sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂ hu₀ hθ hu hL]
  simp [hdθ]

include hQ hkl he h₀ h₂ in
/-- **The norm of `D_{A₀} u₀`.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero`, and for
skew-adjoint generators, `‖D_{A₀} u₀‖² = (‖dω‖² / 4) ‖u₀‖²`, where `‖dω‖²` is the sum of the
squares of the four frame components `dω_abc`, `a < b < c`. -/
theorem norm_sum_ι_apply_sq_of_cliffordProjection_apply_eq_zero
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    {θ : V → ⋀[ℝ]^2 V}
    (hθ : ∀ v a b, ⟪θ v, ιMulti ℝ 2 ![J a, J b]⟫ = -⟪θ v, ιMulti ℝ 2 ![a, b]⟫)
    {u : V → positiveHalfSpinors o ρ} (hu : ∀ v, cliffordProjection o ρ J.kahlerForm (u v) = 0)
    (hL : ∀ v, ρ (bivectorExterior Q (θ v)) u₀ + ρ (bivectorExterior Q J.kahlerForm) (u v) =
      (-2 * Complex.I) • (u v : W)) :
    ‖∑ k, ρ (ι Q (e k)) (u (e k))‖ ^ 2 =
      (twoVectorAlternatingSum θ (e 0) (e 1) (e 2) ^ 2 +
          twoVectorAlternatingSum θ (e 0) (e 1) (e 3) ^ 2 +
          twoVectorAlternatingSum θ (e 0) (e 2) (e 3) ^ 2 +
          twoVectorAlternatingSum θ (e 1) (e 2) (e 3) ^ 2) / 4 * ‖(u₀ : W)‖ ^ 2 := by
  set x : Fin 4 → ℂ := ![(Complex.I / 2) * ((twoVectorAlternatingSum θ (e 1) (e 2) (e 3) : ℂ) -
      twoVectorAlternatingSum θ (e 0) (e 2) (e 3) * Complex.I), 0,
    (Complex.I / 2) * ((twoVectorAlternatingSum θ (e 0) (e 1) (e 3) : ℂ) -
      twoVectorAlternatingSum θ (e 0) (e 1) (e 2) * Complex.I), 0]
  have hx : ∑ k, ρ (ι Q (e k)) (u (e k)) = ∑ k, x k • ρ (ι Q (e k)) u₀ := by
    rw [sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂ hu₀ hθ hu hL,
      Fin.sum_univ_four]
    simp [x, smul_add, smul_smul]
  rw [hx, norm_sum_smul_ι_apply_sq_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hu₀]
  congr 1
  simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, mul_zero, add_zero, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

include hQ hkl he h₀ h₂ in
/-- **`D_{A₀} u₀` vanishes exactly where `dω` does.** Under the hypotheses of
`TauCeti.SeibergWitten.sum_ι_apply_eq_of_cliffordProjection_apply_eq_zero`, and for
skew-adjoint generators, `∑ₖ c(e_k) (u e_k) = 0` if and only if `u₀ = 0` or the four frame
components of `dω` vanish. -/
theorem sum_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_zero
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
    {θ : V → ⋀[ℝ]^2 V}
    (hθ : ∀ v a b, ⟪θ v, ιMulti ℝ 2 ![J a, J b]⟫ = -⟪θ v, ιMulti ℝ 2 ![a, b]⟫)
    {u : V → positiveHalfSpinors o ρ} (hu : ∀ v, cliffordProjection o ρ J.kahlerForm (u v) = 0)
    (hL : ∀ v, ρ (bivectorExterior Q (θ v)) u₀ + ρ (bivectorExterior Q J.kahlerForm) (u v) =
      (-2 * Complex.I) • (u v : W)) :
    ∑ k, ρ (ι Q (e k)) (u (e k)) = 0 ↔
      (u₀ : W) = 0 ∨ (twoVectorAlternatingSum θ (e 0) (e 1) (e 2) = 0 ∧
        twoVectorAlternatingSum θ (e 0) (e 1) (e 3) = 0 ∧
        twoVectorAlternatingSum θ (e 0) (e 2) (e 3) = 0 ∧
        twoVectorAlternatingSum θ (e 1) (e 2) (e 3) = 0) := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff,
    norm_sum_ι_apply_sq_of_cliffordProjection_apply_eq_zero hQ hkl he h₀ h₂ hρ hu₀ hθ hu hL,
    mul_eq_zero, div_eq_zero_iff, sq_eq_zero_iff, norm_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · have h₁ := sq_nonneg (twoVectorAlternatingSum θ (e 0) (e 1) (e 2))
      have h₂ := sq_nonneg (twoVectorAlternatingSum θ (e 0) (e 1) (e 3))
      have h₃ := sq_nonneg (twoVectorAlternatingSum θ (e 0) (e 2) (e 3))
      have h₄ := sq_nonneg (twoVectorAlternatingSum θ (e 1) (e 2) (e 3))
      right
      refine ⟨?_, ?_, ?_, ?_⟩ <;> exact pow_eq_zero_iff two_ne_zero |>.1 (by linarith)
    · norm_num at h
    · exact Or.inl h
  · rintro (h | ⟨h₁, h₂, h₃, h₄⟩)
    · exact Or.inr h
    · left; left
      rw [h₁, h₂, h₃, h₄]
      norm_num

end TauCeti.SeibergWitten
