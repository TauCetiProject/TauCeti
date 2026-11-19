/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.FlatLimit
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry

/-!
# The gauge-fixed normal model at a plane vortex

Near a pseudoholomorphic curve, Taubes's large-parameter Seiberg–Witten solutions are modelled,
after rescaling, on fields on the flat space `V = ℂ_base × ℂ_normal` that are plane vortices in
the normal factor (`TauCeti.Analysis.PDE.SeibergWitten.FlatLimit`). The linearization of the flat
limiting equations, with its gauge-fixing row, is then a first-order operator on eight real
components: the connection variation `b'` (four components) and the spinor variation `ζ ∈ W⁺`
(two complex components). This file decomposes it, at a vortex pulled back from the normal factor
and on variations independent of the base, into the gauge-fixed vortex operator `L_x` and its
adjoint `L_x*` (`TauCeti.Vortex.gaugeFixedOperator`, `TauCeti.Vortex.gaugeFixedAdjoint`).

Fix a positively oriented unitary frame `(e₀, e₁, e₂, e₃)`, `J e₀ = e₁`, `J e₂ = e₃`, with base
plane `⟨e₀, e₁⟩` and normal coordinate `z = ⟪e₂, ·⟫ + i ⟪e₃, ·⟫` (`normalCoord`), and a unit
spinor `u₀` of the canonical line `P_α u₀ = u₀`. The **paired spinor** `β₀ = c(e₂) c(e₀) u₀`
(`pairedSpinor`) is a unit spinor orthogonal to `u₀` (`norm_pairedSpinor`,
`inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self`), so `(u₀, β₀)` is a unitary
frame of `W⁺` when `W⁺` has rank two, and `c(e₀) u₀`, `c(e₂) u₀` are orthonormal in `W⁻`.
Clifford multiplication of a complex covector on `β₀` sees only its `∂`-components
(`sum_smul_ι_apply_pairedSpinor_of_cliffordProjection_apply_eq_self`),

`∑ₖ y_k c(e_k) β₀ = (y₀ - i y₁) c(e₂) u₀ - (y₂ - i y₃) c(e₀) u₀`,

while on `u₀` it sees only the `∂bar`-components
(`sum_smul_ι_apply_of_cliffordProjection_apply_eq_self`). The polarization `q'` of the quadratic
map pairs with a two-form `x` as `⟪q'(ψ, φ), x⟫ = Re⟪φ, C(i x) ψ⟫ / 2`
(`inner_quadraticTwoFormPolar_eq_re_inner`), and on the two lines its coordinates along
`e₀ ∧ e₁`, `e₀ ∧ e₂`, `e₀ ∧ e₃` are `Re(conj α f) / 2`, `Im(α conj g) / 2` and `Re(α conj g) / 2`
for `ψ = α u₀`, `φ = f u₀ + g β₀` (`inner_quadraticTwoFormPolar_ιMulti_zero_one` and its
companions). A self-dual two-form is determined by these three coordinates.

**The operator.** At a pair `(b, ψ)`, with connection `a = i b` and covariant derivative
`∇ = d + i b`, the linearization of the flat limiting equations
`∑ₖ c(eₖ) ∇_{eₖ} ψ = 0`, `F + ⋆F = ω / 8 - q(ψ) / 2`, `F = -db`, together with the gauge-fixing
row, sends a variation `(b', ζ)` to

* `d₀*(b', ζ) = div b' + Re⟪i ψ, ζ⟫ / 4` (`flatDeformationGauge`), the formal adjoint of the
  charge-one gauge action `d₀ f = (-df, i f ψ)` for the coefficient metric `|b'|² + |ζ|² / 4`;
* `F' + ⋆F' + q'(ψ, ζ) / 2`, `F' = -db'` (`flatDeformationCurvature`), a self-dual two-vector
  (`hodgeStar_flatDeformationCurvature`);
* `∑ₖ c(eₖ) (∇_{eₖ} ζ + i b'(eₖ) ψ)` (`flatDeformationDirac`), in `W⁻`.

These are the normalizations of `TauCeti.Vortex.gaugeFixedOperator`: the plane vortex equation
`∂bar_a α = 0`, `*i F_a = (1 - |α|²) / 8` is the flat limiting system at `r = 1 / 2`.

**The normal model.** A pair of plane fields `(ξ, η)` gives the variation
(`normalModelConnection`, `normalModelSpinor`)

`b' = η₀(z) e⁰ - η₁(z) e¹ + ξ₀(z) e² + ξ₁(z) e³`,  `ζ = α_ξ(z) u₀ + α_η(z) β₀`,

with `α_ξ = 2 (ξ₂ + i ξ₃)`. The normal block `ξ` carries a connection along the normal factor and a
section of the canonical line, as for the vortex itself; the paired block `η` carries a
connection along the base and a section of the complementary line. At the pullback
`(b_x, α_x u₀)` of a plane field `x` (the case `(ξ, η) = (x, 0)`, see
`normalModelConnection_zero_right` and `normalModelSpinor_zero_right`), the operator applied to the
normal model of `(ξ, η)` is, at every point `y` and with `L_x`, `L_x*` evaluated at `z(y)`:

* gauge row: `(L_x ξ)₀` (`flatDeformationGauge_normalModel`);
* curvature row: `(L_x ξ)₁` along `e₀ ∧ e₁`, and `-(L_x* η)₀`, `-(L_x* η)₁` along `e₀ ∧ e₂`,
  `e₀ ∧ e₃` (`inner_flatDeformationCurvature_normalModel_zero_one`, `_zero_two`, `_zero_three`);
* Dirac row: `2 ((L_x* η)₂ + i (L_x* η)₃) c(e₀) u₀ + 2 ((L_x ξ)₂ + i (L_x ξ)₃) c(e₂) u₀`
  (`flatDeformationDirac_normalModel`).

So on base-independent variations the eight-component operator is `L_x ⊕ L_x*`, up to the frame
identifications and the scalar factors `1, 1, -1, -1, 2, 2` displayed above, and its kernel at a
point is `ker L_x ⊕ ker L_x*` (`flatDeformation_normalModel_eq_zero_iff`). No regularity of `x`
beyond its values is used, and `x` need not solve the vortex equations. Variations depending on
the base coordinate, whose base derivatives couple the two blocks, are not treated here.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open exteriorPower

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module Complex
open scoped RealInnerProductSpace InnerProductSpace ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

/-! ### The frame values of the quadratic term on the two lines -/

section FrameValues

variable [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)

include hQ hkl he h₀ h₂ hρ hu₀

/-- **The quadratic term along `e₀ ∧ e₁`**: for a unit canonical spinor `u₀` with paired spinor
`β₀`, `⟪q'(α u₀, f u₀ + g β₀), e₀ ∧ e₁⟫ = Re(conj α f) / 2`. -/
theorem inner_quadraticTwoFormPolar_ιMulti_zero_one (hu₀₁ : ‖u₀‖ = 1) (α f g : ℂ) :
    ⟪(quadraticTwoFormPolar o ρ hkl (α • u₀) (f • u₀ + g • pairedSpinor e u₀) : ⋀[ℝ]^2 V),
        ιMulti ℝ 2 ![e 0, e 1]⟫ = (conj α * f).re / 2 := by
  have h0 := inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hu₀
  rw [inner_quadraticTwoFormPolar_eq_re_inner o hQ hkl hρ, map_smul,
    cliffordRestriction_ιMulti_zero_one_apply_of_cliffordProjection_apply_eq_self
      hQ hkl he h₀ h₂ hu₀,
    inner_add_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hu₀₁, ← inner_conj_symm, h0]
  simp [mul_comm]

/-- **The quadratic term along `e₀ ∧ e₂`**: for a unit canonical spinor `u₀` with paired spinor
`β₀`, `⟪q'(α u₀, f u₀ + g β₀), e₀ ∧ e₂⟫ = Im(α conj g) / 2`. -/
theorem inner_quadraticTwoFormPolar_ιMulti_zero_two (hu₀₁ : ‖u₀‖ = 1) (α f g : ℂ) :
    ⟪(quadraticTwoFormPolar o ρ hkl (α • u₀) (f • u₀ + g • pairedSpinor e u₀) : ⋀[ℝ]^2 V),
        ιMulti ℝ 2 ![e 0, e 2]⟫ = (α * conj g).im / 2 := by
  have h0 := inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hu₀
  have h1 : ‖pairedSpinor e u₀‖ = 1 := by rw [norm_pairedSpinor hQ hρ, hu₀₁]
  rw [inner_quadraticTwoFormPolar_eq_re_inner o hQ hkl hρ, map_smul,
    cliffordRestriction_ιMulti_zero_two_apply hQ, inner_add_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, h1, h0]
  simp [mul_comm]

/-- **The quadratic term along `e₀ ∧ e₃`**: for a unit canonical spinor `u₀` with paired spinor
`β₀`, `⟪q'(α u₀, f u₀ + g β₀), e₀ ∧ e₃⟫ = Re(α conj g) / 2`. -/
theorem inner_quadraticTwoFormPolar_ιMulti_zero_three (hu₀₁ : ‖u₀‖ = 1) (α f g : ℂ) :
    ⟪(quadraticTwoFormPolar o ρ hkl (α • u₀) (f • u₀ + g • pairedSpinor e u₀) : ⋀[ℝ]^2 V),
        ιMulti ℝ 2 ![e 0, e 3]⟫ = (α * conj g).re / 2 := by
  have h0 := inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hu₀
  have h1 : ‖pairedSpinor e u₀‖ = 1 := by rw [norm_pairedSpinor hQ hρ, hu₀₁]
  rw [inner_quadraticTwoFormPolar_eq_re_inner o hQ hkl hρ, map_smul,
    cliffordRestriction_ιMulti_zero_three_apply_of_cliffordProjection_apply_eq_self
      hQ hkl he h₀ h₂ hu₀,
    inner_add_left,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, h1, h0]
  simp [mul_comm]

end FrameValues

/-! ### The gauge-fixed linearization of the flat limiting equations -/

section Deformation

variable [Fact (finrank ℝ V = 4)]

variable (e) in
/-- The **gauge-fixing row** of the linearized flat limiting equations at a spinor `ψ`, applied to
a variation `(b', ζ)` of the connection `a = i b` and of the spinor: the formal `L²` adjoint
`d₀*(b', ζ) = div b' + Re⟪i ψ, ζ⟫ / 4` of the charge-one infinitesimal gauge action
`d₀ f = (-df, i f ψ)`, for the coefficient metric `|b'|² + |ζ|² / 4`. -/
def flatDeformationGauge (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ)
    (y : V) : ℝ :=
  ∑ k, fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y (e k) + (⟪I • (ψ y : W), (ζ y : W)⟫_ℂ).re / 4

theorem flatDeformationGauge_def (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationGauge e b' ψ ζ y =
      ∑ k, fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y (e k) +
        (⟪I • (ψ y : W), (ζ y : W)⟫_ℂ).re / 4 :=
  (rfl)

variable [FiniteDimensional ℂ W] (hkl : 2 + 2 = finrank ℝ V)

variable (o ρ) in
/-- The **curvature row** of the linearized flat limiting equations at a spinor `ψ`, applied to a
variation `(b', ζ)`: the derivative `F' + ⋆F' + q'(ψ, ζ) / 2`, `F' = -db'`, of the flat curvature
equation `F + ⋆F = ω / 8 - q(ψ) / 2`
(`sum_covariantDeriv_smul_ι_apply_eq_zero_and_add_hodgeStar_eq_iff`), with the real curvature
`F = -db` read as a two-vector. -/
def flatDeformationCurvature (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ)
    (y : V) : ⋀[ℝ]^2 V :=
  (alternatingFormEquiv V 2).symm (-extDeriv b' y) +
      o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b' y)) +
    (2⁻¹ : ℝ) • (quadraticTwoFormPolar o ρ hkl (ψ y) (ζ y) : ⋀[ℝ]^2 V)

theorem flatDeformationCurvature_def (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationCurvature o ρ hkl b' ψ ζ y =
      (alternatingFormEquiv V 2).symm (-extDeriv b' y) +
          o.hodgeStar hkl ((alternatingFormEquiv V 2).symm (-extDeriv b' y)) +
        (2⁻¹ : ℝ) • (quadraticTwoFormPolar o ρ hkl (ψ y) (ζ y) : ⋀[ℝ]^2 V) :=
  (rfl)

/-- The curvature row is self-dual. -/
theorem hodgeStar_flatDeformationCurvature (b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    o.hodgeStar hkl (flatDeformationCurvature o ρ hkl b' ψ ζ y) =
      flatDeformationCurvature o ρ hkl b' ψ ζ y := by
  rw [flatDeformationCurvature, map_add, map_add, map_smul,
    o.hodgeStar_hodgeStar_of_even even_two hkl, o.hodgeStar_coe_of_mem_eigenspace_one hkl]
  abel

omit [FiniteDimensional ℂ W]

variable (e) in
/-- The **Dirac row** of the linearized flat limiting equations at a pair `(b, ψ)`, applied to a
variation `(b', ζ)`: the derivative `∑ₖ c(eₖ) (∇_{eₖ} ζ + i b'(eₖ) ψ)`, `∇ = d + i b`, of the flat
Dirac operator `∑ₖ c(eₖ) ∇_{eₖ} ψ`. -/
def flatDeformationDirac (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ ζ : V → positiveHalfSpinors o ρ)
    (y : V) : W :=
  ∑ k, ρ (ι Q (e k)) (fderiv ℝ (fun y' ↦ (ζ y' : W)) y (e k) +
    (I * b y (fun _ ↦ e k)) • (ζ y : W) + (I * b' y (fun _ ↦ e k)) • (ψ y : W))

theorem flatDeformationDirac_def (b b' : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ ζ : V → positiveHalfSpinors o ρ) (y : V) :
    flatDeformationDirac e b b' ψ ζ y =
      ∑ k, ρ (ι Q (e k)) (fderiv ℝ (fun y' ↦ (ζ y' : W)) y (e k) +
        (I * b y (fun _ ↦ e k)) • (ζ y : W) + (I * b' y (fun _ ↦ e k)) • (ψ y : W)) :=
  (rfl)

end Deformation

/-! ### Base fields pulled back from the plane -/

section Pullback

variable (e) in
/-- The **paired connection** `η₀(z) e⁰ - η₁(z) e¹` on `V = ℂ_base × ℂ_normal` of a plane field
`η = (η₀, η₁, η₂, η₃)`, pulled back along the normal coordinate `z` (`normalCoord`). It points
along the base factor; together with the section `η₂ + i η₃` on the paired spinor it is the
variation through which the plane vortex adjoint operator enters the normal model. -/
def pairedConnection (η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) : V [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    (η (normalCoord e y) 0 • innerSL ℝ (e 0) - η (normalCoord e y) 1 • innerSL ℝ (e 1))

/-- The paired connection evaluated on a vector `v`: `η₀(z) ⟪e₀, v⟫ - η₁(z) ⟪e₁, v⟫`. -/
@[simp]
theorem pairedConnection_apply (η : ℂ → EuclideanSpace ℝ (Fin 4)) (y v : V) :
    pairedConnection e η y (fun _ ↦ v) =
      η (normalCoord e y) 0 * ⟪e 0, v⟫ - η (normalCoord e y) 1 * ⟪e 1, v⟫ := by
  simp [pairedConnection]

/-- The paired connection is differentiable where the plane field is. -/
theorem differentiableAt_pairedConnection {η : ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}
    (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    DifferentiableAt ℝ (pairedConnection e η) y := by
  have hc (i : Fin 4) : DifferentiableAt ℝ (fun y' ↦ η (normalCoord e y') i) y :=
    (differentiableAt_euclidean.1 hη i).comp y (normalCoord e).differentiableAt
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).differentiableAt.comp y (((hc 0).smul_const _).sub ((hc 1).smul_const _))

/-- The paired connection of the zero plane field vanishes. -/
@[simp]
theorem pairedConnection_zero : pairedConnection e (0 : ℂ → EuclideanSpace ℝ (Fin 4)) = 0 := by
  funext y
  ext v
  simp [pairedConnection]

end Pullback

/-! ### The normal model of a pair of plane fields -/

section NormalModel

variable (e) in
/-- The **connection of the normal model** of a pair of plane fields `(ξ, η)`: the normal
connection `ξ₀(z) e² + ξ₁(z) e³` of `ξ` (`normalConnection`) plus the paired connection
`η₀(z) e⁰ - η₁(z) e¹` of `η` (`pairedConnection`), pulled back along the normal coordinate `z`. -/
def normalModelConnection (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    V [⋀^Fin 1]→L[ℝ] ℝ :=
  normalConnection e ξ y + pairedConnection e η y

/-- The connection of the normal model on a vector:
`b(v) = η₀(z) ⟪e₀, v⟫ - η₁(z) ⟪e₁, v⟫ + ξ₀(z) ⟪e₂, v⟫ + ξ₁(z) ⟪e₃, v⟫`. -/
@[simp]
theorem normalModelConnection_apply (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y v : V) :
    normalModelConnection e ξ η y (fun _ ↦ v) =
      η (normalCoord e y) 0 * ⟪e 0, v⟫ - η (normalCoord e y) 1 * ⟪e 1, v⟫ +
        ξ (normalCoord e y) 0 * ⟪e 2, v⟫ + ξ (normalCoord e y) 1 * ⟪e 3, v⟫ := by
  simp only [normalModelConnection, ContinuousAlternatingMap.add_apply, normalConnection_apply,
    pairedConnection_apply, normalCoord_re, normalCoord_im]
  ring

/-- The connection of the normal model of `(ξ, 0)` is the normal connection of `ξ`. -/
@[simp]
theorem normalModelConnection_zero_right (ξ : ℂ → EuclideanSpace ℝ (Fin 4)) :
    normalModelConnection e ξ 0 = normalConnection e ξ := by
  funext y
  simp [normalModelConnection]

/-- The connection of the normal model on `e₀` is `η₀(z)`. -/
-- These four frame values take priority over the general `normalModelConnection_apply`.
@[simp high]
theorem normalModelConnection_apply_zero (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    normalModelConnection e ξ η y (fun _ ↦ e 0) = η (normalCoord e y) 0 := by
  simp [normalModelConnection_apply, e.inner_eq_ite]

/-- The connection of the normal model on `e₁` is `-η₁(z)`. -/
@[simp high]
theorem normalModelConnection_apply_one (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    normalModelConnection e ξ η y (fun _ ↦ e 1) = -η (normalCoord e y) 1 := by
  simp [normalModelConnection_apply, e.inner_eq_ite]

/-- The connection of the normal model on `e₂` is `ξ₀(z)`. -/
@[simp high]
theorem normalModelConnection_apply_two (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    normalModelConnection e ξ η y (fun _ ↦ e 2) = ξ (normalCoord e y) 0 := by
  simp [normalModelConnection_apply, e.inner_eq_ite]

/-- The connection of the normal model on `e₃` is `ξ₁(z)`. -/
@[simp high]
theorem normalModelConnection_apply_three (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    normalModelConnection e ξ η y (fun _ ↦ e 3) = ξ (normalCoord e y) 1 := by
  simp [normalModelConnection_apply, e.inner_eq_ite]

variable [Fact (finrank ℝ V = 4)]

variable (e) in
/-- The **spinor of the normal model** of a pair of plane fields `(ξ, η)`: the section
`α_ξ = 2 (ξ₂ + i ξ₃)` of `ξ` on the canonical spinor `u₀` plus the section `α_η` of `η` on the
paired spinor `β₀ = c(e₂) c(e₀) u₀` (`pairedSpinor`), pulled back along the normal coordinate. For
`η = 0` this is the pullback `α_ξ u₀` of `TauCeti.SeibergWitten.FlatLimit`. -/
def normalModelSpinor (u₀ : positiveHalfSpinors o ρ) (ξ η : ℂ → EuclideanSpace ℝ (Fin 4))
    (y : V) : positiveHalfSpinors o ρ :=
  Vortex.sectionValue ξ (normalCoord e y) • u₀ +
    Vortex.sectionValue η (normalCoord e y) • pairedSpinor e u₀

theorem normalModelSpinor_apply (u₀ : positiveHalfSpinors o ρ)
    (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    normalModelSpinor e u₀ ξ η y = Vortex.sectionValue ξ (normalCoord e y) • u₀ +
      Vortex.sectionValue η (normalCoord e y) • pairedSpinor e u₀ :=
  (rfl)

/-- The spinor of the normal model as a spinor of `W`. -/
theorem coe_normalModelSpinor (u₀ : positiveHalfSpinors o ρ)
    (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    (normalModelSpinor e u₀ ξ η y : W) = Vortex.sectionValue ξ (normalCoord e y) • (u₀ : W) +
      Vortex.sectionValue η (normalCoord e y) • (pairedSpinor e u₀ : W) :=
  (rfl)

/-- The spinor of the normal model of `(ξ, 0)` is `α_ξ u₀`. -/
@[simp]
theorem normalModelSpinor_zero_right (u₀ : positiveHalfSpinors o ρ)
    (ξ : ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    normalModelSpinor e u₀ ξ 0 y = Vortex.sectionValue ξ (normalCoord e y) • u₀ := by
  simp [normalModelSpinor_apply]

end NormalModel

/-! ### The rows of the normal model -/

section Rows

variable {ξ η : ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}

/-- The derivative along `v` of the coefficient `η₀(z)` of the connection of the normal model on
`e₀`, through the normal coordinate. -/
theorem fderiv_normalModelConnection_apply_zero (hη : DifferentiableAt ℝ η (normalCoord e y))
    (v : V) :
    fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e 0)) y v =
      fderiv ℝ (fun w ↦ η w 0) (normalCoord e y) (normalCoord e v) := by
  simp only [normalModelConnection_apply_zero,
    fderiv_comp_normalCoord_apply (differentiableAt_euclidean.1 hη 0)]

/-- The derivative along `v` of the coefficient `-η₁(z)` of the connection of the normal model on
`e₁`, through the normal coordinate. -/
theorem fderiv_normalModelConnection_apply_one (hη : DifferentiableAt ℝ η (normalCoord e y))
    (v : V) :
    fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e 1)) y v =
      -fderiv ℝ (fun w ↦ η w 1) (normalCoord e y) (normalCoord e v) := by
  simp only [normalModelConnection_apply_one, fderiv_fun_neg, neg_apply,
    fderiv_comp_normalCoord_apply (differentiableAt_euclidean.1 hη 1)]

/-- The derivative along `v` of the coefficient `ξ₀(z)` of the connection of the normal model on
`e₂`, through the normal coordinate. -/
theorem fderiv_normalModelConnection_apply_two (hξ : DifferentiableAt ℝ ξ (normalCoord e y))
    (v : V) :
    fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e 2)) y v =
      fderiv ℝ (fun w ↦ ξ w 0) (normalCoord e y) (normalCoord e v) := by
  simp only [normalModelConnection_apply_two,
    fderiv_comp_normalCoord_apply (differentiableAt_euclidean.1 hξ 0)]

/-- The derivative along `v` of the coefficient `ξ₁(z)` of the connection of the normal model on
`e₃`, through the normal coordinate. -/
theorem fderiv_normalModelConnection_apply_three (hξ : DifferentiableAt ℝ ξ (normalCoord e y))
    (v : V) :
    fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e 3)) y v =
      fderiv ℝ (fun w ↦ ξ w 1) (normalCoord e y) (normalCoord e v) := by
  simp only [normalModelConnection_apply_three,
    fderiv_comp_normalCoord_apply (differentiableAt_euclidean.1 hξ 1)]

/-- The connection of the normal model is differentiable where its plane fields are. -/
theorem differentiableAt_normalModelConnection (hξ : DifferentiableAt ℝ ξ (normalCoord e y))
    (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    DifferentiableAt ℝ (normalModelConnection e ξ η) y :=
  (differentiableAt_normalConnection hξ).add (differentiableAt_pairedConnection hη)

variable [Fact (finrank ℝ V = 4)] [FiniteDimensional ℂ W] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)
  (x : ℂ → EuclideanSpace ℝ (Fin 4))

include hQ hkl he h₀ h₂ hρ hu₀ in
/-- **The gauge-fixing row of the normal model is the gauge row of `L_x`**: at the pullback
`(b_x, α_x u₀)` of a plane field `x`, the gauge-fixing row of the linearized flat limiting
equations, applied to the normal model of `(ξ, η)`, is `d₀* ξ = gaugeAdjoint x ξ` at the normal
coordinate. The paired variation `η` does not enter. -/
theorem flatDeformationGauge_normalModel (hu₀₁ : ‖u₀‖ = 1)
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    flatDeformationGauge e (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
        (normalModelSpinor e u₀ ξ η) y =
      Vortex.gaugeAdjoint x ξ (normalCoord e y) := by
  have hβ : ⟪(u₀ : W), (pairedSpinor e u₀ : W)⟫_ℂ = 0 := by
    rw [← Submodule.coe_inner]
    exact inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hu₀
  have hu : ⟪(u₀ : W), (u₀ : W)⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, Submodule.norm_coe, hu₀₁]
    simp
  have hψ : (normalModelSpinor e u₀ x 0 y : W) =
      Vortex.sectionValue x (normalCoord e y) • (u₀ : W) := by
    rw [normalModelSpinor_zero_right, Submodule.coe_smul]
  simp only [flatDeformationGauge, Fin.sum_univ_four, fderiv_normalModelConnection_apply_zero hη,
    fderiv_normalModelConnection_apply_one hη, fderiv_normalModelConnection_apply_two hξ,
    fderiv_normalModelConnection_apply_three hξ, normalCoord_apply_zero, normalCoord_apply_one,
    normalCoord_apply_two, normalCoord_apply_three, map_zero, neg_zero, zero_add]
  rw [hψ, coe_normalModelSpinor, inner_smul_left, inner_smul_left, inner_add_right,
    inner_smul_right, inner_smul_right, hu, hβ]
  simp only [mul_one, mul_zero, add_zero, conj_I, neg_mul, neg_re, I_mul_re, neg_neg,
    Vortex.conj_sectionValue_mul_sectionValue_im, Vortex.gaugeAdjoint_def]
  ring

omit [FiniteDimensional ℂ W] in
/-- The two-vector `F' = -db'` of the connection of the normal model, paired with a bivector
`u ∧ w`: `∂_w b'(u) - ∂_u b'(w)`. -/
theorem inner_alternatingFormEquiv_symm_neg_extDeriv_normalModelConnection
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y))
    (u w : V) :
    ⟪(alternatingFormEquiv V 2).symm (-extDeriv (normalModelConnection e ξ η) y),
        ιMulti ℝ 2 ![u, w]⟫ =
      fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ u)) y w -
        fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ w)) y u := by
  rw [inner_alternatingFormEquiv_symm_ιMulti, ContinuousAlternatingMap.neg_apply,
    extDeriv_apply_pair_of_differentiableAt (differentiableAt_normalModelConnection hξ hη)]
  ring

/-- The curvature row of the normal model paired with `e₀ ∧ eⱼ`, where `⋆(e₀ ∧ eⱼ) = s eₖ ∧ eₗ`:
the derivative along `eⱼ` of the coefficient on `e₀`, plus `s` times the curl of the coefficients on
`eₖ` and `eₗ`, plus half the `q'`-coordinate. The coefficient on `eⱼ` is constant along `e₀`. -/
private theorem inner_flatDeformationCurvature_normalModel_zero
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y))
    {j k l : Fin 4} {s : ℝ}
    (hj : o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e j]) = s • ιMulti ℝ 2 ![e k, e l]) :
    ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
        (normalModelSpinor e u₀ ξ η) y, ιMulti ℝ 2 ![e 0, e j]⟫ =
      fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e 0)) y (e j) +
        s * (fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e k)) y (e l) -
          fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e l)) y (e k)) +
        2⁻¹ * ⟪(quadraticTwoFormPolar o ρ hkl (normalModelSpinor e u₀ x 0 y)
          (normalModelSpinor e u₀ ξ η y) : ⋀[ℝ]^2 V), ιMulti ℝ 2 ![e 0, e j]⟫ := by
  have hj0 : fderiv ℝ (fun y' ↦ normalModelConnection e ξ η y' (fun _ ↦ e j)) y (e 0) = 0 := by
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      fderiv_normalModelConnection_apply_zero hη, fderiv_normalModelConnection_apply_one hη,
      fderiv_normalModelConnection_apply_two hξ, fderiv_normalModelConnection_apply_three hξ,
      normalCoord_apply_zero, map_zero, neg_zero]
  have hs : ∀ a b : ⋀[ℝ]^2 V, ⟪o.hodgeStar hkl a, b⟫ = ⟪a, o.hodgeStar hkl b⟫ :=
    o.isSymmetric_hodgeStar_of_even even_two hkl
  rw [flatDeformationCurvature, inner_add_left, inner_add_left, real_inner_smul_left, hs, hj,
    real_inner_smul_right,
    inner_alternatingFormEquiv_symm_neg_extDeriv_normalModelConnection hξ hη,
    inner_alternatingFormEquiv_symm_neg_extDeriv_normalModelConnection hξ hη, hj0, sub_zero]

section Curvature

include hQ hkl he h₀ h₂ hρ hu₀

/-- **The curvature row of the normal model along `e₀ ∧ e₁` is the curvature row of `L_x`**: at
the pullback `(b_x, α_x u₀)` of a plane field `x`, the curvature row of the linearized flat
limiting equations, applied to the normal model of `(ξ, η)`, pairs with `e₀ ∧ e₁` to the first
equation row `(L_x ξ)₁` at the normal coordinate. -/
theorem inner_flatDeformationCurvature_normalModel_zero_one (hu₀₁ : ‖u₀‖ = 1)
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
        (normalModelSpinor e u₀ ξ η) y, ιMulti ℝ 2 ![e 0, e 1]⟫ =
      Vortex.gaugeFixedOperator x ξ (normalCoord e y) 1 := by
  rw [inner_flatDeformationCurvature_normalModel_zero hkl x hξ hη
      ((o.hodgeStar_ιMulti_zero_one hkl he).trans (one_smul ℝ _).symm),
    normalModelSpinor_zero_right, normalModelSpinor_apply,
    inner_quadraticTwoFormPolar_ιMulti_zero_one hQ hkl he h₀ h₂ hρ hu₀ hu₀₁]
  simp only [fderiv_normalModelConnection_apply_zero hη, fderiv_normalModelConnection_apply_two hξ,
    fderiv_normalModelConnection_apply_three hξ, normalCoord_apply_one, normalCoord_apply_two,
    normalCoord_apply_three, map_zero, zero_add, one_mul]
  rw [Vortex.conj_sectionValue_mul_sectionValue_re, Vortex.gaugeFixedOperator_apply_one,
    Vortex.linearizedEquation_apply_zero]
  ring

/-- **The curvature row of the normal model along `e₀ ∧ e₂` is minus the gauge row of `L_x*`**:
the curvature row of the linearized flat limiting equations at the pullback of `x`, applied to the
normal model of `(ξ, η)`, pairs with `e₀ ∧ e₂` to `-(L_x* η)₀` at the normal coordinate. -/
theorem inner_flatDeformationCurvature_normalModel_zero_two (hu₀₁ : ‖u₀‖ = 1)
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
        (normalModelSpinor e u₀ ξ η) y, ιMulti ℝ 2 ![e 0, e 2]⟫ =
      -Vortex.gaugeFixedAdjoint x η (normalCoord e y) 0 := by
  rw [inner_flatDeformationCurvature_normalModel_zero hkl x hξ hη
      ((o.hodgeStar_ιMulti_zero_two hkl he).trans (neg_one_smul ℝ _).symm),
    normalModelSpinor_zero_right, normalModelSpinor_apply,
    inner_quadraticTwoFormPolar_ιMulti_zero_two hQ hkl he h₀ h₂ hρ hu₀ hu₀₁]
  simp only [fderiv_normalModelConnection_apply_zero hη, fderiv_normalModelConnection_apply_one hη,
    fderiv_normalModelConnection_apply_three hξ, normalCoord_apply_one, normalCoord_apply_two,
    normalCoord_apply_three, map_zero, sub_zero]
  rw [mul_comm (Vortex.sectionValue x _), Vortex.conj_sectionValue_mul_sectionValue_im,
    Vortex.gaugeFixedAdjoint_apply_zero]
  ring

/-- **The curvature row of the normal model along `e₀ ∧ e₃` is minus the curvature row of
`L_x*`**: the curvature row of the linearized flat limiting equations at the pullback of `x`,
applied to the normal model of `(ξ, η)`, pairs with `e₀ ∧ e₃` to `-(L_x* η)₁` at the normal
coordinate. -/
theorem inner_flatDeformationCurvature_normalModel_zero_three (hu₀₁ : ‖u₀‖ = 1)
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
        (normalModelSpinor e u₀ ξ η) y, ιMulti ℝ 2 ![e 0, e 3]⟫ =
      -Vortex.gaugeFixedAdjoint x η (normalCoord e y) 1 := by
  rw [inner_flatDeformationCurvature_normalModel_zero hkl x hξ hη
      ((o.hodgeStar_ιMulti_zero_three hkl he).trans (one_smul ℝ _).symm),
    normalModelSpinor_zero_right, normalModelSpinor_apply,
    inner_quadraticTwoFormPolar_ιMulti_zero_three hQ hkl he h₀ h₂ hρ hu₀ hu₀₁]
  simp only [fderiv_normalModelConnection_apply_zero hη, fderiv_normalModelConnection_apply_one hη,
    fderiv_normalModelConnection_apply_two hξ, normalCoord_apply_one, normalCoord_apply_two,
    normalCoord_apply_three, map_zero, sub_zero, one_mul]
  rw [mul_comm (Vortex.sectionValue x _), Vortex.conj_sectionValue_mul_sectionValue_re,
    Vortex.gaugeFixedAdjoint_apply_one]
  ring

end Curvature

omit [FiniteDimensional ℂ W] in
/-- The spinor of the normal model is differentiable where its plane fields are. -/
theorem differentiableAt_normalModelSpinor (hξ : DifferentiableAt ℝ ξ (normalCoord e y))
    (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    DifferentiableAt ℝ (fun y' ↦ (normalModelSpinor e u₀ ξ η y' : W)) y := by
  simp only [coe_normalModelSpinor]
  exact (((Vortex.differentiableAt_sectionValue_of_differentiableAt hξ).smul_const _).fun_add
    ((Vortex.differentiableAt_sectionValue_of_differentiableAt hη).smul_const _)).comp y
      (normalCoord e).differentiableAt

omit [FiniteDimensional ℂ W] in
/-- The derivative of the spinor of the normal model along a vector `v`:
`α_ξ'(z v) u₀ + α_η'(z v) β₀`. -/
theorem fderiv_normalModelSpinor_apply (hξ : DifferentiableAt ℝ ξ (normalCoord e y))
    (hη : DifferentiableAt ℝ η (normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ (normalModelSpinor e u₀ ξ η y' : W)) y v =
      fderiv ℝ (Vortex.sectionValue ξ) (normalCoord e y) (normalCoord e v) • (u₀ : W) +
        fderiv ℝ (Vortex.sectionValue η) (normalCoord e y) (normalCoord e v) •
          (pairedSpinor e u₀ : W) := by
  have hf := Vortex.differentiableAt_sectionValue_of_differentiableAt hξ
  have hg := Vortex.differentiableAt_sectionValue_of_differentiableAt hη
  simp only [coe_normalModelSpinor]
  rw [fderiv_comp_normalCoord_apply ((hf.smul_const (u₀ : W)).fun_add
      (hg.smul_const (pairedSpinor e u₀ : W))),
    fderiv_fun_add (hf.smul_const _) (hg.smul_const _), fderiv_smul_const hf, fderiv_smul_const hg,
    add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRight_apply]

omit [FiniteDimensional ℂ W] in
/-- The Dirac row of the normal model, split along the canonical spinor `u₀` and the paired
spinor `β₀`: the `k`-th summand is `c(e_k)` applied to `X_k u₀ + Y_k β₀`, with `X_k` and `Y_k` the
covariant derivatives of the two sections, `X_k` including the connection variation times `α_x`. -/
private theorem flatDeformationDirac_normalModel_eq_sum
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    flatDeformationDirac e (normalModelConnection e x 0) (normalModelConnection e ξ η)
        (normalModelSpinor e u₀ x 0) (normalModelSpinor e u₀ ξ η) y =
      ∑ k, (fderiv ℝ (Vortex.sectionValue ξ) (normalCoord e y) (normalCoord e (e k)) +
          I * normalModelConnection e x 0 y (fun _ ↦ e k) *
            Vortex.sectionValue ξ (normalCoord e y) +
          I * normalModelConnection e ξ η y (fun _ ↦ e k) *
            Vortex.sectionValue x (normalCoord e y)) • ρ (ι Q (e k)) u₀ +
        ∑ k, (fderiv ℝ (Vortex.sectionValue η) (normalCoord e y) (normalCoord e (e k)) +
          I * normalModelConnection e x 0 y (fun _ ↦ e k) *
            Vortex.sectionValue η (normalCoord e y)) •
          ρ (ι Q (e k)) (pairedSpinor e u₀ : W) := by
  rw [flatDeformationDirac_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [fderiv_normalModelSpinor_apply hξ hη, normalModelSpinor_zero_right, coe_normalModelSpinor,
    Submodule.coe_smul]
  simp only [map_add, map_smul]
  module

include hQ hkl he h₀ h₂ hu₀ in
/-- **The Dirac row of the normal model is the `∂bar`-row of `L_x` plus that of `L_x*`**: at the
pullback `(b_x, α_x u₀)` of a plane field `x`, the Dirac row of the linearized flat limiting
equations, applied to the normal model of `(ξ, η)`, is
`2 ((L_x* η)₂ + i (L_x* η)₃) c(e₀) u₀ + 2 ((L_x ξ)₂ + i (L_x ξ)₃) c(e₂) u₀` at the normal
coordinate. The two frame vectors `c(e₀) u₀` and `c(e₂) u₀` of `W⁻` thus carry the paired and the
normal block respectively. -/
theorem flatDeformationDirac_normalModel (hξ : DifferentiableAt ℝ ξ (normalCoord e y))
    (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    flatDeformationDirac e (normalModelConnection e x 0) (normalModelConnection e ξ η)
        (normalModelSpinor e u₀ x 0) (normalModelSpinor e u₀ ξ η) y =
      (2 * ((Vortex.gaugeFixedAdjoint x η (normalCoord e y) 2 : ℂ) +
          Vortex.gaugeFixedAdjoint x η (normalCoord e y) 3 * I)) • ρ (ι Q (e 0)) u₀ +
        (2 * ((Vortex.gaugeFixedOperator x ξ (normalCoord e y) 2 : ℂ) +
          Vortex.gaugeFixedOperator x ξ (normalCoord e y) 3 * I)) • ρ (ι Q (e 2)) u₀ := by
  set f := Vortex.sectionValue ξ (normalCoord e y)
  set g := Vortex.sectionValue η (normalCoord e y)
  set α := Vortex.sectionValue x (normalCoord e y)
  -- The coefficients on `u₀` and on `β₀` of the `k`-th covariant derivative.
  set X : Fin 4 → ℂ := fun k ↦
    fderiv ℝ (Vortex.sectionValue ξ) (normalCoord e y) (normalCoord e (e k)) +
    I * normalModelConnection e x 0 y (fun _ ↦ e k) * f +
    I * normalModelConnection e ξ η y (fun _ ↦ e k) * α with hX
  set Y : Fin 4 → ℂ := fun k ↦
    fderiv ℝ (Vortex.sectionValue η) (normalCoord e y) (normalCoord e (e k)) +
    I * normalModelConnection e x 0 y (fun _ ↦ e k) * g with hY
  have hsum : flatDeformationDirac e (normalModelConnection e x 0) (normalModelConnection e ξ η)
      (normalModelSpinor e u₀ x 0) (normalModelSpinor e u₀ ξ η) y =
        ∑ k, X k • ρ (ι Q (e k)) u₀ + ∑ k, Y k • ρ (ι Q (e k)) (pairedSpinor e u₀ : W) :=
    flatDeformationDirac_normalModel_eq_sum x hξ hη
  rw [hsum, sum_smul_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀,
    sum_smul_ι_apply_pairedSpinor_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀]
  -- Compare the two coefficients, after evaluating `X` and `Y` on the frame.
  have hAB : X 0 + I * X 1 - (Y 2 - I * Y 3) =
        2 * ((Vortex.gaugeFixedAdjoint x η (normalCoord e y) 2 : ℂ) +
          Vortex.gaugeFixedAdjoint x η (normalCoord e y) 3 * I) ∧
      X 2 + I * X 3 + (Y 0 - I * Y 1) =
        2 * ((Vortex.gaugeFixedOperator x ξ (normalCoord e y) 2 : ℂ) +
          Vortex.gaugeFixedOperator x ξ (normalCoord e y) 3 * I) := by
    simp only [hX, hY, f, g, α, normalModelConnection_apply_zero, normalModelConnection_apply_one,
      normalModelConnection_apply_two, normalModelConnection_apply_three, Pi.zero_apply,
      PiLp.zero_apply, normalCoord_apply_zero, normalCoord_apply_one, normalCoord_apply_two,
      normalCoord_apply_three, map_zero, Vortex.sectionValue_apply,
      Vortex.fderiv_sectionValue_apply (differentiableAt_euclidean.1 hξ 2)
        (differentiableAt_euclidean.1 hξ 3),
      Vortex.fderiv_sectionValue_apply (differentiableAt_euclidean.1 hη 2)
        (differentiableAt_euclidean.1 hη 3),
      Vortex.gaugeFixedAdjoint_apply_two, Vortex.gaugeFixedAdjoint_apply_three,
      Vortex.gaugeFixedOperator_apply_two, Vortex.gaugeFixedOperator_apply_three,
      Vortex.linearizedEquation_apply_one, Vortex.linearizedEquation_apply_two]
    push_cast
    constructor <;> grind [I_sq]
  rw [← hAB.1, ← hAB.2]
  module

end Rows

/-! ### The kernel of the normal model at a point -/

section Kernel

variable [Fact (finrank ℝ V = 4)] (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)

variable [FiniteDimensional ℂ W] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)

include hQ hkl he h₀ h₂ hρ hu₀ in
/-- **The kernel of the normal model at a point is `ker L_x ⊕ ker L_x*`**: at the pullback
`(b_x, α_x u₀)` of a plane field `x`, the three rows of the linearized flat limiting equations
vanish at `y` on the normal model of `(ξ, η)` exactly when `L_x ξ` and `L_x* η` vanish at the
normal coordinate of `y`. -/
theorem flatDeformation_normalModel_eq_zero_iff (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {ξ η : ℂ → EuclideanSpace ℝ (Fin 4)} {y : V} (hu₀₁ : ‖u₀‖ = 1)
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    (flatDeformationGauge e (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
          (normalModelSpinor e u₀ ξ η) y = 0 ∧
        flatDeformationCurvature o ρ hkl (normalModelConnection e ξ η)
          (normalModelSpinor e u₀ x 0) (normalModelSpinor e u₀ ξ η) y = 0 ∧
        flatDeformationDirac e (normalModelConnection e x 0) (normalModelConnection e ξ η)
          (normalModelSpinor e u₀ x 0) (normalModelSpinor e u₀ ξ η) y = 0) ↔
      Vortex.gaugeFixedOperator x ξ (normalCoord e y) = 0 ∧
        Vortex.gaugeFixedAdjoint x η (normalCoord e y) = 0 := by
  have hu₀' : (u₀ : W) ≠ 0 := by
    rw [← norm_ne_zero_iff, Submodule.norm_coe, hu₀₁]
    exact one_ne_zero
  -- The Dirac row vanishes exactly when both of its coefficients do.
  have hD (A B : ℂ) : A • ρ (ι Q (e 0)) u₀ + B • ρ (ι Q (e 2)) u₀ = 0 ↔ A = 0 ∧ B = 0 := by
    have h := sum_smul_ι_apply_eq_zero_iff_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂
      hρ hu₀ ![A, 0, B, 0]
    simpa [Fin.sum_univ_four, hu₀'] using h
  have hC (a b : ℝ) : (2 * ((a : ℂ) + b * I) = 0) ↔ a = 0 ∧ b = 0 := by
    constructor
    · intro h
      have hre : 2 * a = 0 := by simpa using congrArg Complex.re h
      have him : 2 * b = 0 := by simpa using congrArg Complex.im h
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨rfl, rfl⟩
      simp
  have hvec (v : EuclideanSpace ℝ (Fin 4)) : v = 0 ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
    refine ⟨fun h ↦ by simp [h], fun ⟨h0, h1, h2, h3⟩ ↦ ?_⟩
    ext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  rw [flatDeformationGauge_normalModel hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hξ hη,
    o.eq_zero_iff_of_hodgeStar_eq_self hkl he (hodgeStar_flatDeformationCurvature hkl _ _ _ _),
    inner_flatDeformationCurvature_normalModel_zero_one hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hξ hη,
    inner_flatDeformationCurvature_normalModel_zero_two hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hξ hη,
    inner_flatDeformationCurvature_normalModel_zero_three hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hξ hη,
    flatDeformationDirac_normalModel hQ hkl he h₀ h₂ hu₀ x hξ hη, hD, hC, hC, hvec, hvec,
    Vortex.gaugeFixedOperator_apply_zero, neg_eq_zero, neg_eq_zero]
  tauto

end Kernel

end TauCeti.SeibergWitten
