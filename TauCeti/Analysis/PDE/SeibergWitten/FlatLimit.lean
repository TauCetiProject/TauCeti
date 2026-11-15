/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.Vortex.Deformation
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry

/-!
# The flat limiting Seiberg–Witten equations and plane vortices

Rescaling a large-parameter Seiberg–Witten solution on a symplectic four-manifold by the length
scale `h`, with `h² r = 1 / 2`, at points near its zero set gives, in the limit, fields on the flat
space `V = ℂ_base × ℂ_normal` with a constant orthogonal complex structure `J` and Kähler form
`ω`. Write the normalized spinor as `χ = α u₀ + β`, where `u₀` is a constant unit spinor in the
`-2i`-eigenline of `c₂(ω)` (the range of `TauCeti.SeibergWitten.cliffordProjection`), and the
connection on the line `E` as `a = i b`, with real curvature `F = i F_a = -db`. The flat limiting
equations are the Dirac equation and the curvature equation

`∑ₖ c(eₖ) ∇_{eₖ} χ = 0`,  `F + ⋆F = ω / 8 - q(χ) / 2`,

where `q` is the quadratic two-form `TauCeti.SeibergWitten.quadraticTwoForm`, indexed by real
forms as in `TauCeti.SeibergWitten.LargeParameterCurvature`; the second equation is the
large-parameter curvature equation `F + ⋆F = (r / 4) ω - q(√r χ)` at `r = 1 / 2`.

When the spinor lies on the canonical line, `χ = α u₀`, this file identifies these equations with
the plane vortex equations:

* **Curvature.** Since `q(α u₀) = (|α|² / 4) ω`, the curvature equation says
  `F + ⋆F = ((1 - |α|²) / 8) ω` (`add_hodgeStar_eq_sub_quadraticTwoForm_iff`). In particular the
  self-dual part of `F` is a multiple of `ω`: its `(0,2)` component vanishes.
* **Dirac.** Since `u₀` is constant, `∑ₖ c(eₖ) ∇_{eₖ}(α u₀) = ∑ₖ (∇_a α)(eₖ) c(eₖ) u₀`, and by the
  Clifford algebra of the canonical line this vanishes exactly when `∂bar_a α = 0`
  (`sum_covariantDeriv_smul_ι_apply_eq_zero_iff`).
* **Base-independent fields.** Let `x` be a field of the plane vortex equations
  (`TauCeti.Vortex.equation`), with connection `i (b₁ ds + b₂ dt)` and section `α`, and pull it back
  to `V` along the normal coordinate `z = ⟪e₂, ·⟫ + i ⟪e₃, ·⟫` of a positively oriented unitary
  frame (`normalCoord`, `normalConnection`). The pulled-back pair solves the flat limiting
  equations at a point exactly when `x` solves the plane vortex equations at its normal coordinate
  (`sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff`). The curvature of the
  pulled-back connection is `F = -(∂₁ b₂ - ∂₂ b₁) e₂ ∧ e₃`, so `F + ⋆F = -(∂₁ b₂ - ∂₂ b₁) ω`, and
  `∂bar_a α` in the frame is the pair of complex-equation defects of `x`.

So the base-independent solutions of the flat limiting equations with spinor on the canonical
line and connection along the normal factor are exactly the pullbacks of plane vortices, in the
normalization `∂bar_a α = 0`, `*i F_a = (1 - |α|²) / 8` of `TauCeti.Vortex.equation`. The gauge
fixing row and the derivation of the limiting equations from actual rescaled solutions are not
treated here.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 4.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
-/

public section

noncomputable section

open exteriorPower

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Complex
open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

/-! ### The curvature equation on the canonical line -/

section FourDimensional

variable [Fact (finrank ℝ V = 4)]

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

section Curvature

variable {ω : ⋀[ℝ]^2 V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (hω : o.hodgeStar hkl ω = ω) (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))

include hQ hω h₂ hρ in
/-- **The flat curvature equation on the canonical line**: if `P_α ψ = ψ`, then
`F + ⋆F = ω / 8 - q(ψ) / 2` if and only if `F + ⋆F = ((1 - ‖ψ‖²) / 8) ω`. -/
theorem add_hodgeStar_eq_sub_quadraticTwoForm_iff {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ ω ψ = ψ) (F : ⋀[ℝ]^2 V) :
    F + o.hodgeStar hkl F =
        (8⁻¹ : ℝ) • ω - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V) ↔
      F + o.hodgeStar hkl F = ((1 - ‖ψ‖ ^ 2) / 8) • ω := by
  rw [coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω h₂ hρ hψ, smul_smul,
    ← sub_smul, show (8⁻¹ : ℝ) - 2⁻¹ * (‖ψ‖ ^ 2 / 4) = (1 - ‖ψ‖ ^ 2) / 8 by ring]

end Curvature

/-! ### The Dirac equation on the canonical line -/

section Dirac

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)

include hQ hkl he h₀ h₂₃ in
/-- **The Dirac equation on the canonical line is `∂bar_a α = 0`**: for a constant nonzero spinor
`u₀` with `P_α u₀ = u₀`, the Dirac operator of `α u₀`, `∑ₖ (∇_a α)(eₖ) c(eₖ) u₀`, vanishes at `x`
if and only if `∂bar_a α` vanishes at `x`. -/
theorem sum_covariantDeriv_smul_ι_apply_eq_zero_iff
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀' : (u₀ : W) ≠ 0)
    (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (α : V → ℂ) (x : V) :
    ∑ k, covariantDeriv b α x (e k) • ρ (ι Q (e k)) u₀ = 0 ↔ covariantDBar J b α x = 0 := by
  rw [covariantDBar_eq_zero_iff]
  exact (sum_apply_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂₃
    hρ hu₀ (covariantDeriv b α x : V →ₗ[ℝ] ℂ)).trans (or_iff_right hu₀')

end Dirac

end FourDimensional

/-! ### Base-independent fields pulled back from the plane -/

section Pullback

variable (e) in
/-- The **normal coordinate** `z = ⟪e₂, v⟫ + i ⟪e₃, v⟫` of `V = ℂ_base × ℂ_normal` in the frame `e`,
whose last two vectors span the normal factor. -/
def normalCoord : V →L[ℝ] ℂ :=
  (innerSL ℝ (e 2)).smulRight (1 : ℂ) + (innerSL ℝ (e 3)).smulRight I

@[simp]
theorem normalCoord_re (v : V) : (normalCoord e v).re = ⟪e 2, v⟫ := by
  simp [normalCoord]

@[simp]
theorem normalCoord_im (v : V) : (normalCoord e v).im = ⟪e 3, v⟫ := by
  simp [normalCoord]

theorem normalCoord_apply (v : V) : normalCoord e v = ⟪e 2, v⟫ + ⟪e 3, v⟫ * I := by
  apply Complex.ext <;> simp

/-- The normal coordinate of `e₂` is `1`. -/
@[simp]
theorem normalCoord_apply_two : normalCoord e (e 2) = 1 := by
  apply Complex.ext <;> simp [e.orthonormal.inner_eq_zero (by decide : (3 : Fin 4) ≠ 2)]

/-- In a unitary frame the normal coordinate is complex linear: `z (J v) = i z (v)`. -/
theorem normalCoord_apply_apply (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (v : V) :
    normalCoord e (J v) = I * normalCoord e v := by
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have h₃ : J (e 3) = -e 2 := by rw [← h₂₃, J.apply_apply]
  have h2 : ⟪e 2, J v⟫ = -⟪e 3, v⟫ := by
    rw [← hJ, h₂₃, J.apply_apply, inner_neg_right]
  have h3 : ⟪e 3, J v⟫ = ⟪e 2, v⟫ := by
    rw [← hJ, h₃, J.apply_apply, inner_neg_neg]
  apply Complex.ext <;> simp [h2, h3]

variable (e) in
/-- The **base-independent connection** `b₁(z) ds + b₂(z) dt` on `V = ℂ_base × ℂ_normal` pulled
back from a plane vortex field `x = (b₁, b₂, p, q)` along the normal coordinate
`z = s + i t` (`normalCoord`). Its connection form is `i` times this real one-form. -/
def normalConnection (x : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) : V [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    (x (normalCoord e y) 0 • innerSL ℝ (e 2) + x (normalCoord e y) 1 • innerSL ℝ (e 3))

/-- The pulled-back connection evaluated on a vector `v`: `b₁(z) Re z(v) + b₂(z) Im z(v)`. -/
@[simp]
theorem normalConnection_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) (y v : V) :
    normalConnection e x y (fun _ ↦ v) =
      x (normalCoord e y) 0 * (normalCoord e v).re +
        x (normalCoord e y) 1 * (normalCoord e v).im := by
  simp [normalConnection]

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}

/-- The covariant derivative of the pulled-back section along the pulled-back connection is the
covariant derivative of the plane field in the normal direction. -/
theorem covariantDeriv_normalConnection (hx : DifferentiableAt ℝ x (normalCoord e y)) (v : V) :
    covariantDeriv (normalConnection e x) (Vortex.sectionValue x ∘ normalCoord e) y v =
      Vortex.covariantDerivative x (normalCoord e y) (normalCoord e v) := by
  have hd := ((Vortex.differentiableAt_sectionValue_of_differentiableAt hx).hasFDerivAt.comp y
    (normalCoord e).hasFDerivAt).fderiv
  rw [covariantDeriv_apply, Vortex.covariantDerivative_apply, hd, normalConnection_apply]
  simp

variable [FiniteDimensional ℝ V]

/-- **`∂bar_a α` of a pulled-back field**: in a unitary frame,
`∂bar_a α (v) = conj (z v) (E₁ + i E₂)`, where `z` is the normal coordinate and `E₁`, `E₂` are the
complex-equation defects of the plane field at the normal coordinate of the point. -/
theorem covariantDBar_normalConnection_apply (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (hx : DifferentiableAt ℝ x (normalCoord e y)) (v : V) :
    covariantDBar J (normalConnection e x) (Vortex.sectionValue x ∘ normalCoord e) y v =
      conj (normalCoord e v) * ((Vortex.equation x (normalCoord e y) 1 : ℂ) +
        (Vortex.equation x (normalCoord e y) 2 : ℂ) * I) := by
  have hc (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) (normalCoord e y) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hx
  have h := Vortex.covariantDerivative_one_add_I_mul_covariantDerivative_I (hc 2) (hc 3)
  set z := normalCoord e v
  have hconj : conj z = (z.re : ℂ) - z.im * I := by apply Complex.ext <;> simp
  rw [covariantDBar_apply, covariantDeriv_normalConnection hx, covariantDeriv_normalConnection hx,
    normalCoord_apply_apply h₀ h₂₃, Vortex.covariantDerivative_eq_re_mul_add_im_mul x _ z,
    Vortex.covariantDerivative_eq_re_mul_add_im_mul x _ (I * z), hconj]
  simp only [mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, mul_im, zero_add, ofReal_neg]
  linear_combination ((z.re - z.im * I : ℂ) / 2) * h +
    ((z.im : ℂ) * Vortex.covariantDerivative x (normalCoord e y) I / 2) * I_sq

/-- **The `∂bar`-equation of a pulled-back field**: in a unitary frame, `∂bar_a α = 0` at `y` for
the pulled-back pair if and only if both complex-equation defects of the plane field vanish at
the normal coordinate of `y`. -/
theorem covariantDBar_normalConnection_eq_zero_iff (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    covariantDBar J (normalConnection e x) (Vortex.sectionValue x ∘ normalCoord e) y = 0 ↔
      Vortex.equation x (normalCoord e y) 1 = 0 ∧ Vortex.equation x (normalCoord e y) 2 = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  · have h₂' := congrArg (fun L ↦ L (e 2)) h
    simp only [covariantDBar_normalConnection_apply h₀ h₂₃ hx, normalCoord_apply_two, map_one,
      one_mul, zero_apply] at h₂'
    exact ⟨by simpa using congrArg Complex.re h₂', by simpa using congrArg Complex.im h₂'⟩
  · simp [covariantDBar_normalConnection_apply h₀ h₂₃ hx, h₁, h₂]

/-- **The curvature of the pulled-back connection**: the real curvature `F = i F_a = -db` of
`b = b₁(z) ds + b₂(z) dt`, read as a two-vector, is `-(∂₁ b₂ - ∂₂ b₁) e₂ ∧ e₃`, with the
curvature coefficient `TauCeti.Vortex.curvature` of the plane field at the normal coordinate. -/
theorem alternatingFormEquiv_symm_neg_extDeriv_normalConnection
    (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    (alternatingFormEquiv V 2).symm (-extDeriv (normalConnection e x) y) =
      (-Vortex.curvature x (normalCoord e y)) • ιMulti ℝ 2 ![e 2, e 3] := by
  set π := normalCoord e
  have hc (i : Fin 4) : HasFDerivAt (fun y' ↦ x (π y') i)
      ((fderiv ℝ (fun w ↦ x w i) (π y)).comp π) y :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hx).hasFDerivAt.comp y
      π.hasFDerivAt
  have hb : DifferentiableAt ℝ (normalConnection e x) y := by
    unfold normalConnection
    have h : DifferentiableAt ℝ
        (fun y' ↦ x (π y') 0 • innerSL ℝ (e 2) + x (π y') 1 • innerSL ℝ (e 3)) y :=
      ((hc 0).differentiableAt.smul_const _).add ((hc 1).differentiableAt.smul_const _)
    exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).differentiableAt.comp y h
  -- The derivative of the coefficient `b(w) = b₁(z) Re z(w) + b₂(z) Im z(w)` along `v`.
  have key (v w : V) : fderiv ℝ (fun y' ↦ normalConnection e x y' (fun _ ↦ w)) y v =
      fderiv ℝ (fun z ↦ x z 0) (π y) (π v) * (π w).re +
        fderiv ℝ (fun z ↦ x z 1) (π y) (π v) * (π w).im := by
    simp only [normalConnection_apply]
    rw [fderiv_fun_add ((hc 0).mul_const _).differentiableAt
        ((hc 1).mul_const _).differentiableAt,
      ((hc 0).mul_const _).fderiv, ((hc 1).mul_const _).fderiv]
    simp [π]
    ring
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_alternatingFormEquiv_symm_ιMulti, real_inner_smul_left, inner_ιMulti_two,
    ContinuousAlternatingMap.neg_apply, extDeriv_apply_pair_of_differentiableAt hb, key, key,
    Vortex.curvature_apply]
  -- Expand each derivative of a plane coefficient in the frame `(1, i)`.
  simp only [ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (π u),
    ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (π w), π, normalCoord_re,
    normalCoord_im, smul_eq_mul]
  ring

end Pullback

/-! ### The flat limiting equations of a pulled-back field -/

section Equations

variable [Fact (finrank ℝ V = 4)]

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
  {x : ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}

include hQ he h₀ h₂₃ in
/-- **Base-independent solutions of the flat limiting equations are plane vortices.** Let `x` be a
plane vortex field, differentiable at the normal coordinate `z(y)` of `y`, and pull its connection
`b = b₁ ds + b₂ dt` and section `α` back to `V = ℂ_base × ℂ_normal` along `z`, in a positively
oriented unitary frame. For a unit spinor `u₀` of the canonical line `P_α u₀ = u₀`, the pair
`(b, α u₀)` solves the flat limiting Dirac and curvature equations at `y`,

`∑ₖ (∇_a α)(eₖ) c(eₖ) u₀ = 0`,  `F + ⋆F = ω / 8 - q(α u₀) / 2`,  `F = i F_a = -db`,

if and only if `x` solves the plane vortex equations at `z(y)`. -/
theorem sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    (∑ k, covariantDeriv (normalConnection e x) (Vortex.sectionValue x ∘ normalCoord e) y (e k) •
          ρ (ι Q (e k)) u₀ = 0 ∧
      (alternatingFormEquiv V 2).symm (-extDeriv (normalConnection e x) y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (normalConnection e x) y)) =
        (8⁻¹ : ℝ) • J.kahlerForm - (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl
          (Vortex.sectionValue x (normalCoord e y) • u₀) : ⋀[ℝ]^2 V)) ↔
      Vortex.equation x (normalCoord e y) = 0 := by
  have hu₀' : (u₀ : W) ≠ 0 := by
    have hu : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀₁
    simpa using hu
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hω₀ : J.kahlerForm ≠ 0 := by
    intro h
    have h2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two (J := J)
      (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃)
    rw [h, norm_zero] at h2
    norm_num at h2
  -- The self-dual part of `c e₂ ∧ e₃` is `c ω`, since `⋆(e₂ ∧ e₃) = e₀ ∧ e₁`.
  have hsd (c : ℝ) : c • ιMulti ℝ 2 ![e 2, e 3] + o.hodgeStar hkl (c • ιMulti ℝ 2 ![e 2, e 3]) =
      c • J.kahlerForm := by
    rw [map_smul, o.hodgeStar_ιMulti_two_three hkl he,
      AlmostComplexStructure.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂₃, smul_add, add_comm]
  have hαu₀ : cliffordProjection o ρ J.kahlerForm
      (Vortex.sectionValue x (normalCoord e y) • u₀) =
        Vortex.sectionValue x (normalCoord e y) • u₀ := by
    rw [map_smul, hu₀]
  rw [sum_covariantDeriv_smul_ι_apply_eq_zero_iff hQ hkl he h₀ h₂₃ hρ hu₀ hu₀',
    covariantDBar_normalConnection_eq_zero_iff h₀ h₂₃ hx,
    add_hodgeStar_eq_sub_quadraticTwoForm_iff hQ hkl hω h₂ hρ hαu₀,
    alternatingFormEquiv_symm_neg_extDeriv_normalConnection hx,
    hsd, smul_left_injective ℝ hω₀ |>.eq_iff,
    norm_smul, hu₀₁, mul_one, Vortex.sq_norm_sectionValue]
  have hE : Vortex.equation x (normalCoord e y) = 0 ↔ Vortex.equation x (normalCoord e y) 0 = 0 ∧
      Vortex.equation x (normalCoord e y) 1 = 0 ∧ Vortex.equation x (normalCoord e y) 2 = 0 := by
    refine ⟨fun h ↦ by simp [h], fun ⟨h0, h1, h2⟩ ↦ ?_⟩
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  rw [hE, Vortex.equation_apply_zero, Vortex.curvature_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h0⟩
    exact ⟨by linarith, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h1, h2⟩, by linarith⟩

end Equations

end TauCeti.SeibergWitten
