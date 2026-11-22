/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CanonicalLine
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.Vortex.Dilation.Basic
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
import TauCeti.Analysis.PDE.SeibergWitten.LogModulusRatio

/-!
# The flat large-parameter Seiberg–Witten equations and plane vortices

Let `V = ℂ_base × ℂ_normal` be flat space with a constant orthogonal complex structure `J` and
Kähler form `ω`. Write the normalized spinor as `χ = α u₀ + β`, where `u₀` is a constant unit
spinor in the `-2i`-eigenline of `c₂(ω)` (the range of `TauCeti.SeibergWitten.cliffordProjection`),
and the connection on the line `E` as `a = i b`, with real curvature `F = i F_a = -db`. For a
parameter `r ≥ 0` the flat large-parameter equations are the Dirac equation and the curvature
equation

`∑ₖ c(eₖ) ∇_{eₖ} χ = 0`,  `F + ⋆F = (r / 4) ω - q(√r χ)`,

where `q` is the quadratic two-form `TauCeti.SeibergWitten.quadraticTwoForm`, indexed by real
forms as in `TauCeti.Analysis.PDE.SeibergWitten.LargeParameter.Curvature`; the second equation
is the large-parameter curvature equation of that file with no background curvature and no
forcing. These are the leading-order equations of a large-parameter solution in a flat chart.

When the spinor lies on the canonical line, `χ = α u₀`, this file identifies these equations with
the plane vortex equations, and the parameter `r` with a dilation of the plane:

* **Curvature.** Since `q(√r α u₀) = (r |α|² / 4) ω`, the curvature equation says
  `F + ⋆F = (r (1 - |α|²) / 4) ω` (`add_hodgeStar_eq_sub_quadraticTwoForm_iff`). In particular
  the self-dual part of `F` is a multiple of `ω`: its `(0,2)` component vanishes.
* **Dirac.** Since `u₀` is constant, `∑ₖ c(eₖ) ∇_{eₖ}(α u₀) = ∑ₖ (∇_a α)(eₖ) c(eₖ) u₀`, and by the
  Clifford algebra of the canonical line this vanishes exactly when `∂bar_a α = 0`
  (`sum_covariantDeriv_smul_ι_apply_eq_zero_iff`).
* **Base-independent fields.** Let `x` be a plane vortex field, with connection
  `i (b₁ ds + b₂ dt)` and section `α`, and pull it back to `V` along the normal coordinate
  `z = ⟪e₂, ·⟫ + i ⟪e₃, ·⟫` of a positively oriented unitary frame (`normalCoord`,
  `normalConnection`). The pulled-back pair solves the flat equations at a point exactly when `x`
  solves the plane vortex equations `∂bar_a α = 0`, `*iF_a = r (1 - |α|²) / 4` at its normal
  coordinate (`TauCeti.Vortex.coupledEquation (2 * r)`,
  `sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff`). The curvature of the
  pulled-back connection is `F = -(∂₁ b₂ - ∂₂ b₁) e₂ ∧ e₃`, so `F + ⋆F = -(∂₁ b₂ - ∂₂ b₁) ω`, and
  `∂bar_a α` in the frame is the pair of complex-equation defects of `x`.
* **Flat scaling.** For `r > 0` put `t = √(2r)`. Pulling back the dilated plane field
  `TauCeti.Vortex.dilateField t X` is pulling back `X` and then dilating `V` by `t`
  (`normalConnection_dilateField`), and the pulled-back pair solves the flat equations at `y`
  exactly when `X` solves the normalized plane vortex equations `∂bar_a α = 0`,
  `*iF_a = (1 - |α|²) / 8` (`TauCeti.Vortex.equation`) at `z(t y)`
  (`sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff_equation_eq_zero`). So in the
  coordinate `w = √(2r) z` the curvature coefficient `r / 4` becomes `1 / 8`.
* **Scaled energy.** For a pulled-back field `|F| = |*iF_a|`
  (`norm_alternatingFormEquiv_symm_neg_extDeriv_normalConnection`) and
  `∑ₖ |∇_{eₖ} α|² = |∇₁ α|² + |∇_i α|²` (`sum_norm_covariantDeriv_normalConnection_sq`) at the
  normal coordinate. So for the dilated field the integrand `r⁻¹ |F_a|² + |∇_a α|² + r (1 - |α|²)²`
  of Taubes's scaled energy is a plane expression in the normal coordinate, and its integral over
  the normal plane does not depend on `r`
  (`TauCeti.Vortex.integral_inv_mul_curvature_dilateField_sq_add`).

So the base-independent solutions of the flat equations with spinor on the canonical line and
connection along the normal factor are exactly the pullbacks of plane vortices of coupling `2r`
(curvature coefficient `r / 4`), equivalently of normalized plane vortices in the coordinate
`√(2r) z`.

For a solution `(b, α u₀)` that is not assumed base independent:

* **`J`-invariance.** A two-form whose self-dual part is a multiple of `ω` is `J`-invariant
  (`TauCeti.AlmostComplexStructure.lieMap_eq_zero_of_add_hodgeStar_eq_smul`), so the curvature
  satisfies `db(J u, J w) = db(u, w)`: `F_a` has no `(0,2)`-part
  (`extDeriv_apply_apply_eq_of_add_hodgeStar_eq_smul`).
* **The flat vortex equations.** The `ω`-component of the curvature equation is
  `∑ᵢ db(fᵢ, J fᵢ) = r (|α|² - 1) / 2` in every orthonormal basis `f`
  (`sum_extDeriv_apply_eq_of_add_hodgeStar_eq_sub_quadraticTwoForm`). With `∂bar_a α = 0`, these
  are the flat vortex equations with coupling `κ = r / 2` of
  `TauCeti.Analysis.PDE.SeibergWitten.LogModulusRatio`.
* **Comparison with a pulled-back vortex.** If `α = h · (α' ∘ z)` for the section `α'` of a plane
  vortex of coupling `2r`, a nowhere-vanishing `C²` function `h` and the normal coordinate `z`, if
  the log-modulus ratio `log |h|²` is bounded, and if `|α| → 1` as `|z| → ∞` uniformly along the
  base, then `|h| = 1` and the solution is the gauge transform by `h` of the pullback of the
  vortex (`norm_eq_one_and_eq_normalConnection_sub_phaseForm`). The limit `|z| → ∞` is the
  transverse limit of
  `TauCeti.eq_zero_of_tendsto_comap_norm_starProjection_of_mul_laplacian_nonneg`, since `|z(y)|`
  is the length of the projection of `y` to the normal plane (`norm_normalCoord`).

The boundedness of the log-modulus ratio, and with it the classification of the solutions whose
section tends to the vacuum transversally, are in
`TauCeti.Analysis.PDE.SeibergWitten.ConfinedLimit`. The gauge fixing row and the insertion into a
curved normal tube are not treated here. That rescaled solutions of the large-parameter equations
converge, in the sense of `1`-jets, only to solutions of the flat limiting equations is
`TauCeti.Analysis.PDE.SeibergWitten.Rescaling`.

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

open CliffordAlgebra Module Complex Filter
open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate Topology

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
/-- **The flat curvature equation on the canonical line**: if `P_α ψ = ψ` and `0 ≤ r`, then
`F + ⋆F = (r / 4) ω - q(√r ψ)` if and only if `F + ⋆F = (r (1 - ‖ψ‖²) / 4) ω`. -/
theorem add_hodgeStar_eq_sub_quadraticTwoForm_iff {r : ℝ} (hr : 0 ≤ r)
    {ψ : positiveHalfSpinors o ρ} (hψ : cliffordProjection o ρ ω ψ = ψ) (F : ⋀[ℝ]^2 V) :
    F + o.hodgeStar hkl F =
        (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • ψ) : ⋀[ℝ]^2 V) ↔
      F + o.hodgeStar hkl F = (r * (1 - ‖ψ‖ ^ 2) / 4) • ω := by
  rw [quadraticTwoForm_sqrt_smul o ρ hkl hr, Submodule.coe_smul,
    coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω h₂ hρ hψ, smul_smul,
    ← sub_smul, show r / 4 - r * (‖ψ‖ ^ 2 / 4) = r * (1 - ‖ψ‖ ^ 2) / 4 by ring]

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

/-- The normal coordinate of `e₀` is `0`. -/
@[simp]
theorem normalCoord_apply_zero : normalCoord e (e 0) = 0 := by
  apply Complex.ext <;> simp [e.orthonormal.inner_eq_zero (by decide : (2 : Fin 4) ≠ 0),
    e.orthonormal.inner_eq_zero (by decide : (3 : Fin 4) ≠ 0)]

/-- The normal coordinate of `e₁` is `0`. -/
@[simp]
theorem normalCoord_apply_one : normalCoord e (e 1) = 0 := by
  apply Complex.ext <;> simp [e.orthonormal.inner_eq_zero (by decide : (2 : Fin 4) ≠ 1),
    e.orthonormal.inner_eq_zero (by decide : (3 : Fin 4) ≠ 1)]

/-- The normal coordinate of `e₂` is `1`. -/
@[simp]
theorem normalCoord_apply_two : normalCoord e (e 2) = 1 := by
  apply Complex.ext <;> simp [e.orthonormal.inner_eq_zero (by decide : (3 : Fin 4) ≠ 2)]

/-- The normal coordinate of `e₃` is `i`. -/
@[simp]
theorem normalCoord_apply_three : normalCoord e (e 3) = I := by
  apply Complex.ext <;> simp [e.orthonormal.inner_eq_zero (by decide : (2 : Fin 4) ≠ 3)]

/-- The normal coordinate is onto: `z (Re w • e₂ + Im w • e₃) = w`. -/
theorem normalCoord_surjective : Function.Surjective (normalCoord e) := fun w ↦
  ⟨w.re • e 2 + w.im • e 3, by
    apply Complex.ext <;> simp⟩

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

/-- **Chain rule through the normal coordinate**: the derivative of a function of the normal
coordinate `z` along `v` is its derivative at `z(y)` along `z(v)`. -/
theorem fderiv_comp_normalCoord_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : ℂ → F} {y : V} (hc : DifferentiableAt ℝ c (normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ c (normalCoord e y')) y v =
      fderiv ℝ c (normalCoord e y) (normalCoord e v) := by
  have h : HasFDerivAt (fun y' ↦ c (normalCoord e y'))
      ((fderiv ℝ c (normalCoord e y)).comp (normalCoord e)) y :=
    hc.hasFDerivAt.comp y (normalCoord e).hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply]

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

/-- **Plane dilation is four-dimensional dilation**: the pullback of the dilated plane field
`TauCeti.Vortex.dilateField t x` is the pullback of `x` composed with the dilation `y ↦ t y` of
`V`, with the connection form multiplied by `t`. -/
theorem normalConnection_dilateField (t : ℝ) (x : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    normalConnection e (Vortex.dilateField t x) y = t • normalConnection e x (t • y) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [show v = fun _ ↦ v 0 from funext fun i ↦ by rw [Subsingleton.elim i 0]]
  simp only [ContinuousAlternatingMap.smul_apply, normalConnection_apply,
    Vortex.dilateField_apply, map_smul, smul_eq_mul, real_smul, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, normalCoord_re, normalCoord_im]
  ring

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}

/-- The covariant derivative of the pulled-back section along the pulled-back connection is the
covariant derivative of the plane field in the normal direction. -/
theorem covariantDeriv_normalConnection (hx : DifferentiableAt ℝ x (normalCoord e y)) (v : V) :
    covariantDeriv (normalConnection e x) (Vortex.sectionValue x ∘ normalCoord e) y v =
      Vortex.covariantDerivative x (normalCoord e y) (normalCoord e v) := by
  rw [covariantDeriv_apply, Vortex.covariantDerivative_apply, Function.comp_def,
    fderiv_comp_normalCoord_apply (Vortex.differentiableAt_sectionValue_of_differentiableAt hx),
    normalConnection_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

/-- **The covariant derivative of a pulled-back section has the plane covariant derivative as its
norm**: summed over the frame, `∑ₖ |∇_{eₖ} α|² = |∇₁ α|² + |∇_i α|²` at `z(y)`, since the normal
coordinate kills `e₀` and `e₁` and sends `e₂`, `e₃` to `1`, `i`. -/
theorem sum_norm_covariantDeriv_normalConnection_sq (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    ∑ k, ‖covariantDeriv (normalConnection e x) (Vortex.sectionValue x ∘ normalCoord e) y
        (e k)‖ ^ 2 =
      ‖Vortex.covariantDerivative x (normalCoord e y) 1‖ ^ 2 +
        ‖Vortex.covariantDerivative x (normalCoord e y) I‖ ^ 2 := by
  have h0 : Vortex.covariantDerivative x (normalCoord e y) 0 = 0 := by
    rw [Vortex.covariantDerivative_eq_re_mul_add_im_mul]
    simp
  simp [Fin.sum_univ_four, covariantDeriv_normalConnection hx, h0]

/-- The pulled-back connection is differentiable where the plane field is. -/
theorem differentiableAt_normalConnection (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    DifferentiableAt ℝ (normalConnection e x) y := by
  have hc (i : Fin 4) : DifferentiableAt ℝ (fun y' ↦ x (normalCoord e y') i) y :=
    (differentiableAt_euclidean.1 hx i).comp y (normalCoord e).differentiableAt
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).differentiableAt.comp y (((hc 0).smul_const _).add ((hc 1).smul_const _))

variable [FiniteDimensional ℝ V]

/-- **The normal coordinate measures the normal component**: `|z(y)| = ‖P_K y‖`, where `P_K` is the
orthogonal projection onto the normal plane `K = span {e₂, e₃}`. -/
theorem norm_normalCoord (y : V) :
    ‖normalCoord e y‖ = ‖(Submodule.span ℝ {e 2, e 3}).starProjection y‖ := by
  set K := Submodule.span ℝ {e 2, e 3}
  obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.1 (K.starProjection_apply_mem y)
  have h22 : ⟪e 2, e 2⟫ = 1 := by simp
  have h33 : ⟪e 3, e 3⟫ = 1 := by simp
  have h23 : ⟪e 2, e 3⟫ = 0 := e.orthonormal.inner_eq_zero (by decide)
  have h32 : ⟪e 3, e 2⟫ = 0 := e.orthonormal.inner_eq_zero (by decide)
  -- `⟪eⱼ, P_K y⟫ = ⟪eⱼ, y⟫` for `eⱼ ∈ K`, so `P_K y = ⟪e₂, y⟫ e₂ + ⟪e₃, y⟫ e₃`.
  have hP (j : Fin 4) (hj : e j ∈ K) : ⟪e j, K.starProjection y⟫ = ⟪e j, y⟫ := by
    have h := K.starProjection_inner_eq_zero y (e j) hj
    rw [inner_sub_left, sub_eq_zero] at h
    rw [real_inner_comm, ← h, real_inner_comm]
  have ha := hP 2 (Submodule.subset_span (by simp))
  have hc := hP 3 (Submodule.subset_span (by simp))
  rw [← hac] at ha hc
  simp only [inner_add_right, real_inner_smul_right, h22, h23, h32, h33] at ha hc
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply,
    normalCoord_re, normalCoord_im, ← real_inner_self_eq_norm_sq, ← hac]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h22, h23,
    h32, h33]
  rw [← ha, ← hc]
  ring

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
  have hd (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) (π y) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp _ hx
  have hc (i : Fin 4) : DifferentiableAt ℝ (fun y' ↦ x (π y') i) y :=
    (hd i).comp y π.differentiableAt
  -- The derivative of the coefficient `b(w) = b₁(z) Re z(w) + b₂(z) Im z(w)` along `v`.
  have key (v w : V) : fderiv ℝ (fun y' ↦ normalConnection e x y' (fun _ ↦ w)) y v =
      fderiv ℝ (fun z ↦ x z 0) (π y) (π v) * (π w).re +
        fderiv ℝ (fun z ↦ x z 1) (π y) (π v) * (π w).im := by
    simp only [normalConnection_apply]
    rw [fderiv_fun_add ((hc 0).mul_const _) ((hc 1).mul_const _), fderiv_mul_const (hc 0),
      fderiv_mul_const (hc 1), add_apply, smul_apply, smul_apply,
      fderiv_comp_normalCoord_apply (hd 0), fderiv_comp_normalCoord_apply (hd 1), smul_eq_mul,
      smul_eq_mul]
    ring
  refine ext_inner_ιMulti_two fun u w ↦ ?_
  rw [inner_alternatingFormEquiv_symm_ιMulti, real_inner_smul_left, inner_ιMulti_two,
    ContinuousAlternatingMap.neg_apply, extDeriv_apply_pair_of_differentiableAt
      (differentiableAt_normalConnection hx), key, key,
    Vortex.curvature_apply]
  -- Expand each derivative of a plane coefficient in the frame `(1, i)`.
  simp only [ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (π u),
    ContinuousLinearMap.apply_eq_re_smul_one_add_im_smul_I _ (π w), π, normalCoord_re,
    normalCoord_im, smul_eq_mul]
  ring

/-- **The normal curvature component of the pulled-back connection** is the curvature coefficient
`TauCeti.Vortex.curvature` of the plane field at the normal coordinate:
`db(e₂, e₃) = ∂₁ b₂ - ∂₂ b₁` at `z(y)`. -/
theorem extDeriv_normalConnection_apply_two_three (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    extDeriv (normalConnection e x) y ![e 2, e 3] = Vortex.curvature x (normalCoord e y) := by
  have h := congrArg (⟪·, ιMulti ℝ 2 ![e 2, e 3]⟫)
    (alternatingFormEquiv_symm_neg_extDeriv_normalConnection hx)
  rw [inner_alternatingFormEquiv_symm_ιMulti, real_inner_smul_left, inner_ιMulti_two,
    ContinuousAlternatingMap.neg_apply] at h
  simp [e.orthonormal.inner_eq_zero (by decide : (2 : Fin 4) ≠ 3)] at h
  linarith

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
/-- **Base-independent solutions of the flat equations are plane vortices.** Let `x` be a plane
vortex field, differentiable at the normal coordinate `z(y)` of `y`, and pull its connection
`b = b₁ ds + b₂ dt` and section `α` back to `V = ℂ_base × ℂ_normal` along `z`, in a positively
oriented unitary frame. For `0 ≤ r` and a unit spinor `u₀` of the canonical line `P_α u₀ = u₀`,
the pair `(b, α u₀)` solves the flat Dirac and large-parameter curvature equations at `y`,

`∑ₖ (∇_a α)(eₖ) c(eₖ) u₀ = 0`,  `F + ⋆F = (r / 4) ω - q(√r α u₀)`,  `F = i F_a = -db`,

if and only if `x` solves the plane vortex equations with curvature coefficient `r / 4`,
`∂bar_a α = 0` and `*iF_a = r (1 - |α|²) / 4` (`TauCeti.Vortex.coupledEquation (2 * r)`), at
`z(y)`. -/
theorem sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff {r : ℝ} (hr : 0 ≤ r)
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    (∑ k, covariantDeriv (normalConnection e x) (Vortex.sectionValue x ∘ normalCoord e) y (e k) •
          ρ (ι Q (e k)) u₀ = 0 ∧
      (alternatingFormEquiv V 2).symm (-extDeriv (normalConnection e x) y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv (normalConnection e x) y)) =
        (r / 4) • J.kahlerForm - (quadraticTwoForm o ρ hkl
          (((√r : ℝ) : ℂ) • (Vortex.sectionValue x (normalCoord e y) • u₀)) : ⋀[ℝ]^2 V)) ↔
      Vortex.coupledEquation (2 * r) x (normalCoord e y) = 0 := by
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
    add_hodgeStar_eq_sub_quadraticTwoForm_iff hQ hkl hω h₂ hρ hr hαu₀,
    alternatingFormEquiv_symm_neg_extDeriv_normalConnection hx,
    hsd, smul_left_injective ℝ hω₀ |>.eq_iff,
    norm_smul, hu₀₁, mul_one, Vortex.sq_norm_sectionValue]
  have hE : Vortex.coupledEquation (2 * r) x (normalCoord e y) = 0 ↔
      Vortex.coupledEquation (2 * r) x (normalCoord e y) 0 = 0 ∧
        Vortex.equation x (normalCoord e y) 1 = 0 ∧ Vortex.equation x (normalCoord e y) 2 = 0 := by
    refine ⟨fun h ↦ by simp [h, ← Vortex.coupledEquation_apply_one (2 * r),
      ← Vortex.coupledEquation_apply_two (2 * r)], fun ⟨h0, h1, h2⟩ ↦ ?_⟩
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  rw [hE, Vortex.coupledEquation_apply_zero, Vortex.curvature_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h0⟩
    exact ⟨by linarith, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h1, h2⟩, by linarith⟩

include hQ he h₀ h₂₃ in
/-- **The flat scaling to the plane vortex model.** For `r > 0` put `t = √(2r)`. Let `X` be a
plane vortex field in the coordinate `w = t z`, differentiable at `t z(y) = z(t y)`, and pull the
dilated field `TauCeti.Vortex.dilateField t X`, the field `X` written in the coordinate `z`, back
to `V = ℂ_base × ℂ_normal` as in
`TauCeti.SeibergWitten.sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff`. The
pulled-back pair solves the flat Dirac and large-parameter curvature equations

`∑ₖ (∇_a α)(eₖ) c(eₖ) u₀ = 0`,  `F + ⋆F = (r / 4) ω - q(√r α u₀)`

at `y` if and only if `X` solves the normalized plane vortex equations
`∂bar_a α = 0`, `*iF_a = (1 - |α|²) / 8` (`TauCeti.Vortex.equation`) at `z(t y)`: in the coordinate
`w = √(2r) z` the curvature coefficient `r / 4` becomes `1 / 8`. -/
theorem sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff_equation_eq_zero
    {r : ℝ} (hr : 0 < r) (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
    (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)
    {X : ℂ → EuclideanSpace ℝ (Fin 4)} (hX : DifferentiableAt ℝ X (normalCoord e (√(2 * r) • y))) :
    (∑ k, covariantDeriv (normalConnection e (Vortex.dilateField (√(2 * r)) X))
          (Vortex.sectionValue (Vortex.dilateField (√(2 * r)) X) ∘ normalCoord e) y (e k) •
          ρ (ι Q (e k)) u₀ = 0 ∧
      (alternatingFormEquiv V 2).symm
          (-extDeriv (normalConnection e (Vortex.dilateField (√(2 * r)) X)) y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm
            (-extDeriv (normalConnection e (Vortex.dilateField (√(2 * r)) X)) y)) =
        (r / 4) • J.kahlerForm - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) •
          (Vortex.sectionValue (Vortex.dilateField (√(2 * r)) X) (normalCoord e y) • u₀)) :
            ⋀[ℝ]^2 V)) ↔
      Vortex.equation X (normalCoord e (√(2 * r) • y)) = 0 := by
  have hz : √(2 * r) • normalCoord e y = normalCoord e (√(2 * r) • y) := (map_smul _ _ _).symm
  have hd := Vortex.coupledEquation_dilateField_eq_zero_iff 1 (√(2 * r))
    (Real.sqrt_pos.2 (by positivity)).ne' X (normalCoord e y)
  rw [mul_one, Real.sq_sqrt (by positivity), Vortex.coupledEquation_one, hz] at hd
  rw [sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff hQ hkl he h₀ h₂₃ hr.le h₂
    hρ hu₀ hu₀₁ (Vortex.differentiableAt_dilateField (hz ▸ hX)), hd]

/-! ### The scaled energy density of a pulled-back field -/

include h₀ h₂₃ in
/-- **The curvature of a pulled-back connection has the plane curvature as its norm**:
`|F| = |*iF_a|` at `z(y)`, since `F = (*iF_a) e₂ ∧ e₃` and `e₂ ∧ e₃` is a unit two-vector. -/
theorem norm_alternatingFormEquiv_symm_neg_extDeriv_normalConnection
    (hx : DifferentiableAt ℝ x (normalCoord e y)) :
    ‖(alternatingFormEquiv V 2).symm (-extDeriv (normalConnection e x) y)‖ =
      |Vortex.curvature x (normalCoord e y)| := by
  have h := AlmostComplexStructure.norm_ιMulti_apply_sq
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃) (e 2)
  rw [h₂₃, e.orthonormal.1 2, one_pow, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h
  rw [alternatingFormEquiv_symm_neg_extDeriv_normalConnection hx, norm_smul, h, mul_one,
    Real.norm_eq_abs, abs_neg]

end Equations

/-! ### The flat vortex equations of a flat limit and the comparison with a pulled-back vortex -/

section Comparison

variable [Fact (finrank ℝ V = 4)]

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o) (h₀ : J (e 0) = e 1)
  (h₂₃ : J (e 2) = e 3) {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {y : V} {c : ℝ}

include he h₀ h₂₃ in
/-- **The curvature of a flat limit is `J`-invariant.** If the real curvature `F = -db` of `b` at
`y` has self-dual part a multiple of `ω`, `F + ⋆F = c ω`, as the flat limiting curvature equation
on the canonical line says (`add_hodgeStar_eq_sub_quadraticTwoForm_iff`), then
`db(J u, J w) = db(u, w)`: the curvature `F_a` has no `(0,2)`-part. -/
theorem extDeriv_apply_apply_eq_of_add_hodgeStar_eq_smul
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b y) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b y)) = c • J.kahlerForm)
    (u w : V) : extDeriv b y ![J u, J w] = extDeriv b y ![u, w] := by
  have h := (AlmostComplexStructure.lieMap_eq_zero_iff_forall_inner_ιMulti_apply
    (AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃) _).1
    (AlmostComplexStructure.lieMap_eq_zero_of_add_hodgeStar_eq_smul h₀ h₂₃ hkl he hF) u w
  simpa only [inner_alternatingFormEquiv_symm_ιMulti, ContinuousAlternatingMap.neg_apply,
    neg_inj] using h

include he h₀ h₂₃ in
/-- **The `ω`-trace of the curvature of a flat limit.** If the real curvature `F = -db` of `b` at
`y` satisfies `F + ⋆F = c ω`, then `∑ᵢ db(fᵢ, J fᵢ) = -2 c` in every orthonormal basis `f`. -/
theorem sum_extDeriv_apply_eq_of_add_hodgeStar_eq_smul {ι : Type*} [Fintype ι]
    (f : OrthonormalBasis ι ℝ V)
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b y) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b y)) = c • J.kahlerForm) :
    ∑ i, extDeriv b y ![f i, J (f i)] = -2 * c := by
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  set F := (alternatingFormEquiv V 2).symm (-extDeriv b y)
  have hFv (u w : V) : ⟪F, ιMulti ℝ 2 ![u, w]⟫ = -extDeriv b y ![u, w] := by
    rw [inner_alternatingFormEquiv_symm_ιMulti, ContinuousAlternatingMap.neg_apply]
  -- `⟪ω, F⟫ = c`, since `⟪ω, ⋆F⟫ = ⟪ω, F⟫` and `‖ω‖² = 2`.
  have hω : ⟪J.kahlerForm, F⟫ = c := by
    have h := congrArg (⟪J.kahlerForm, ·⟫) hF
    simp only [inner_add_right, AlmostComplexStructure.inner_kahlerForm_hodgeStar h₀ h₂₃ hkl he,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ] at h
    linarith
  -- `∑ᵢ fᵢ ∧ J fᵢ = 2 ω`.
  have hsum := congrArg (⟪F, ·⟫)
    (AlmostComplexStructure.sum_ιMulti_apply_eq_two_smul_kahlerForm hJ f)
  simp only [inner_sum, hFv, Finset.sum_neg_distrib, real_inner_smul_right] at hsum
  rw [real_inner_comm, hω] at hsum
  linarith

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2) (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) {u₀ : positiveHalfSpinors o ρ}
  (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀) (hu₀₁ : ‖u₀‖ = 1)

include hQ he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ in
/-- **The flat vortex curvature equation of a flat limit.** If `0 ≤ r` and `(b, α u₀)` solves the
flat large-parameter curvature equation `F + ⋆F = (r / 4) ω - q(√r α u₀)` at `y`, for a unit
spinor `u₀` of the canonical line, then `∑ᵢ db(fᵢ, J fᵢ) = r (|α|² - 1) / 2` in every orthonormal
basis `f`: the curvature equation of the flat vortex equations with coupling `κ = r / 2`. -/
theorem sum_extDeriv_apply_eq_of_add_hodgeStar_eq_sub_quadraticTwoForm {ι : Type*} [Fintype ι]
    (f : OrthonormalBasis ι ℝ V) {r : ℝ} (hr : 0 ≤ r) {α : V → ℂ}
    (hF : (alternatingFormEquiv V 2).symm (-extDeriv b y) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b y)) =
      (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (α y • u₀)) : ⋀[ℝ]^2 V)) :
    ∑ i, extDeriv b y ![f i, J (f i)] = r / 2 * (‖α y‖ ^ 2 - 1) := by
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hP : cliffordProjection o ρ J.kahlerForm (α y • u₀) = α y • u₀ := by
    rw [map_smul, hu₀]
  rw [add_hodgeStar_eq_sub_quadraticTwoForm_iff hQ hkl hω h₂ hρ hr hP, norm_smul, hu₀₁,
    mul_one] at hF
  rw [sum_extDeriv_apply_eq_of_add_hodgeStar_eq_smul hkl he h₀ h₂₃ f hF]
  ring

include hQ he h₀ h₂₃ h₂ hρ hu₀ hu₀₁ in
/-- **A flat limit with bounded log-modulus ratio is a pulled-back plane vortex up to gauge.** Let
`0 ≤ r`, let `(b, α u₀)` solve the flat Dirac and large-parameter curvature equations on
`V = ℂ_base × ℂ_normal` everywhere, for a unit spinor `u₀` of the canonical line, and let `x` be a
differentiable plane vortex of coupling `2r` (`TauCeti.Vortex.coupledEquation (2 * r)`) whose
section `α'` is nonzero on a dense set and satisfies `|α'(z)| → 1` as `z → ∞`. Suppose
that `α = h · (α' ∘ z)` for a nowhere-vanishing `C²` function `h`, where `z` is the normal
coordinate, that the log-modulus ratio `log |h|²` is bounded, and that `|α| → 1` as `|z| → ∞`,
uniformly along the base. Then `|h| = 1` and `b = b' - Im (h⁻¹ dh)`, where `b'` is the connection of
`x` pulled back along `z`: the flat limit is the gauge transform by `h` of the base-independent
pullback of `x` (`normalConnection`). -/
theorem norm_eq_one_and_eq_normalConnection_sub_phaseForm {r : ℝ} (hr : 0 ≤ r) {α h : V → ℂ}
    (hb : Differentiable ℝ b) (hD : ∀ y, ∑ k, covariantDeriv b α y (e k) • ρ (ι Q (e k)) u₀ = 0)
    (hF : ∀ y, (alternatingFormEquiv V 2).symm (-extDeriv b y) +
        o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b y)) =
      (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (α y • u₀)) : ⋀[ℝ]^2 V))
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Differentiable ℝ x)
    (hsol : ∀ z, Vortex.coupledEquation (2 * r) x z = 0)
    (hdense : Dense {z | Vortex.sectionValue x z ≠ 0})
    (hframe : Tendsto (fun z ↦ ‖Vortex.sectionValue x z‖) (cocompact ℂ) (𝓝 1))
    (hh : ContDiff ℝ 2 h) (hh₀ : ∀ y, h y ≠ 0)
    (hα : α = h * (Vortex.sectionValue x ∘ normalCoord e))
    (hbdd : Bornology.IsBounded (Set.range fun y ↦ Real.log (‖h y‖ ^ 2)))
    (hlim : Tendsto (fun y ↦ ‖α y‖) (comap (fun y ↦ ‖normalCoord e y‖) atTop) (𝓝 1)) :
    (∀ y, ‖h y‖ = 1) ∧ b = normalConnection e x - phaseForm h := by
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hu₀' : (u₀ : W) ≠ 0 := by
    have hu : u₀ ≠ 0 := by
      rintro rfl
      simp at hu₀₁
    simpa using hu
  set α' := Vortex.sectionValue x ∘ normalCoord e
  have hα' : Differentiable ℝ α' := fun y ↦
    (Vortex.differentiableAt_sectionValue_of_differentiableAt (hx _)).comp y
      (normalCoord e).differentiableAt
  -- The pulled-back vortex solves the flat limiting equations.
  have hflat (y : V) :=
    (sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff hQ hkl he h₀ h₂₃ hr h₂ hρ
      hu₀ hu₀₁ (hx (normalCoord e y))).2 (hsol _)
  have hdirac := sum_covariantDeriv_smul_ι_apply_eq_zero_iff hQ hkl he h₀ h₂₃ hρ hu₀ hu₀'
  -- Transversal limits along the normal plane `K = span {e₂, e₃}` are limits as `|z| → ∞`.
  set K := Submodule.span ℝ {e 2, e 3}
  have hK : K ≠ ⊥ := fun hK ↦ e.orthonormal.ne_zero 2
    ((Submodule.mem_bot ℝ).1 (hK ▸ Submodule.subset_span (by simp)))
  have hfilter : comap (fun y ↦ ‖K.starProjection y‖) atTop =
      comap (fun y ↦ ‖normalCoord e y‖) atTop := by
    simp only [norm_normalCoord, K]
  have hz : Tendsto (normalCoord e) (comap (fun y ↦ ‖normalCoord e y‖) atTop) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    exact tendsto_comap
  refine norm_eq_one_and_eq_sub_phaseForm_of_tendsto hJ e (κ := r / 2) (by positivity) hK hb
    (fun y ↦ differentiableAt_normalConnection (hx _)) hh hα' hh₀ hα
    (hdense.preimage ((normalCoord e).isOpenMap normalCoord_surjective))
    (fun y ↦ (hdirac _ _ _).1 (hD y)) (fun y ↦ (hdirac _ _ _).1 (hflat y).1)
    (fun y ↦ sum_extDeriv_apply_eq_of_add_hodgeStar_eq_sub_quadraticTwoForm hkl he h₀ h₂₃ hQ h₂ hρ
      hu₀ hu₀₁ e hr (hF y))
    (fun y ↦ sum_extDeriv_apply_eq_of_add_hodgeStar_eq_sub_quadraticTwoForm hkl he h₀ h₂₃ hQ h₂ hρ
      hu₀ hu₀₁ e hr (α := α') (hflat y).2) hbdd (hfilter ▸ hlim) (hfilter ▸ hframe.comp hz)

end Comparison

end TauCeti.SeibergWitten
