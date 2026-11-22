/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.FlatLimit
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import TauCeti.Analysis.Calculus.DifferentialForm.Curl
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry

/-!
# The gauge-fixed normal model at a plane vortex

Near a pseudoholomorphic curve, Taubes's large-parameter Seiberg–Witten solutions are modelled,
after rescaling, on fields on the flat space `V = ℂ_base × ℂ_normal` that are plane vortices in
the normal factor (`TauCeti.Analysis.PDE.SeibergWitten.FlatLimit`). The linearization of the flat
limiting equations, with its gauge-fixing row, is then a first-order operator on eight real
components: the connection variation `b'` (four components) and the spinor variation `ζ ∈ W⁺`
(two complex components). This file decomposes it, at a vortex pulled back from the normal factor,
into the gauge-fixed vortex operator `L_x` and its adjoint `L_x*`
(`TauCeti.Vortex.gaugeFixedOperator`, `TauCeti.Vortex.gaugeFixedAdjoint`), acting along the normal
plane, coupled by a constant-coefficient first-order operator along the base.

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
beyond its values is used, and `x` need not solve the vortex equations.

**Variations depending on the base.** With the base coordinate `w = ⟪e₀, ·⟫ + i ⟪e₁, ·⟫`
(`baseCoord`), a family `(Ξ, Η)` of pairs of plane fields over the base, `Ξ, Η : ℂ × ℂ → ℝ⁴`,
gives the variation whose value at `y` is that of the normal model of the plane fields
`Ξ (w(y), ·)` and `Η (w(y), ·)` (`familyNormalModelConnection`, `familyNormalModelSpinor`). Its
derivatives along `e₀` and `e₁` are the derivatives of the family along the base
(`fderiv_comp_baseCoord_normalCoord_apply`). The operator applied to it is computed by the same
rows (`flatDeformationGauge_familyNormalModel`,
`inner_flatDeformationCurvature_familyNormalModel_zero_one` and its companions,
`flatDeformationDirac_familyNormalModel`), with `L_x` and `L_x*` replaced by

`N = L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)`,  `P = L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)`,

where `D_w Φ : ℂ →L[ℝ] ℝ⁴` is the real derivative of the base slice `w' ↦ Φ (w', z(y))` at `w(y)`
and, for such a base derivative `D`, `normalBaseCoupling D = D 1 + K (D i)` and
`pairedBaseCoupling D = D 1 + K' (D i)` with `K (v₀, v₁, v₂, v₃) = (-v₁, v₀, v₃, -v₂)` and
`K' (v₀, v₁, v₂, v₃) = (-v₁, v₀, -v₃, v₂)`. Writing `w = s + i t`, the two directions are the
partial derivatives `∂_s Φ = D_w Φ 1` and `∂_t Φ = D_w Φ i` along the base. So along the base the
paired family enters the normal rows and the normal family the paired rows, and the operator
vanishes at a point exactly when `N` and `P` do (`flatDeformation_familyNormalModel_eq_zero_iff`).
A family constant along the base has vanishing base couplings, and the results for
base-independent variations are this special case (`familyNormalModelConnection_comp_snd`,
`familyNormalModelSpinor_comp_snd`).

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

/-! ### Families of plane fields over the base -/

section Family

/-! Reindexing the frame by `i ↦ i + 2` swaps its base and normal planes. -/

private theorem reindex_addRight_two_apply_zero : e.reindex (Equiv.addRight 2) 0 = e 2 := by
  simp [show (-2 : Fin 4) = 2 by decide]

private theorem reindex_addRight_two_apply_one : e.reindex (Equiv.addRight 2) 1 = e 3 := by
  simp [show (-2 : Fin 4) = 2 by decide]

private theorem reindex_addRight_two_apply_two : e.reindex (Equiv.addRight 2) 2 = e 0 := by
  simp [show (-2 : Fin 4) = 2 by decide]

private theorem reindex_addRight_two_apply_three : e.reindex (Equiv.addRight 2) 3 = e 1 := by
  simp [show (-2 : Fin 4) = 2 by decide]

variable (e) in
/-- The **base coordinate** `w = ⟪e₀, v⟫ + i ⟪e₁, v⟫` of `V = ℂ_base × ℂ_normal` in the frame `e`,
whose first two vectors span the base factor. It is the normal coordinate (`normalCoord`) of the
frame reindexed by `i ↦ i + 2`, which swaps the base and normal planes. -/
def baseCoord : V →L[ℝ] ℂ :=
  normalCoord (e.reindex (Equiv.addRight 2))

@[simp]
theorem baseCoord_re (v : V) : (baseCoord e v).re = ⟪e 0, v⟫ := by
  rw [baseCoord, normalCoord_re, reindex_addRight_two_apply_two]

@[simp]
theorem baseCoord_im (v : V) : (baseCoord e v).im = ⟪e 1, v⟫ := by
  rw [baseCoord, normalCoord_im, reindex_addRight_two_apply_three]

theorem baseCoord_apply (v : V) : baseCoord e v = ⟪e 0, v⟫ + ⟪e 1, v⟫ * I := by
  apply Complex.ext <;> simp

/-- The base coordinate of `e₀` is `1`. -/
@[simp]
theorem baseCoord_apply_zero : baseCoord e (e 0) = 1 := by
  rw [baseCoord, ← reindex_addRight_two_apply_two]
  exact normalCoord_apply_two

/-- The base coordinate of `e₁` is `i`. -/
@[simp]
theorem baseCoord_apply_one : baseCoord e (e 1) = I := by
  rw [baseCoord, ← reindex_addRight_two_apply_three]
  exact normalCoord_apply_three

/-- The base coordinate of `e₂` is `0`. -/
@[simp]
theorem baseCoord_apply_two : baseCoord e (e 2) = 0 := by
  rw [baseCoord, ← reindex_addRight_two_apply_zero]
  exact normalCoord_apply_zero

/-- The base coordinate of `e₃` is `0`. -/
@[simp]
theorem baseCoord_apply_three : baseCoord e (e 3) = 0 := by
  rw [baseCoord, ← reindex_addRight_two_apply_one]
  exact normalCoord_apply_one

/-- **Chain rule through the base and normal coordinates**: the derivative along `v` of a function
of `(w, z)` is the derivative of its base slice along `w(v)` plus that of its normal slice along
`z(v)`, at `(w(y), z(y))`. -/
theorem fderiv_comp_baseCoord_normalCoord_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : ℂ × ℂ → F} {y : V}
    (hc : DifferentiableAt ℝ c (baseCoord e y, normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ c (baseCoord e y', normalCoord e y')) y v =
      fderiv ℝ (fun w ↦ c (w, normalCoord e y)) (baseCoord e y) (baseCoord e v) +
        fderiv ℝ (fun z ↦ c (baseCoord e y, z)) (normalCoord e y) (normalCoord e v) := by
  have h : HasFDerivAt (fun y' ↦ c (baseCoord e y', normalCoord e y'))
      ((fderiv ℝ c (baseCoord e y, normalCoord e y)).comp ((baseCoord e).prod (normalCoord e)))
      y :=
    hc.hasFDerivAt.comp y ((baseCoord e).prod (normalCoord e)).hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hc]

variable (e) in
/-- The **connection of the normal model of a family** `(Ξ, Η)` of pairs of plane fields over the
base, `Ξ (w, ·)` and `Η (w, ·)` being the plane fields over the base point `w`: at `y`, the
connection of the normal model (`normalModelConnection`) of the plane fields over the base point
`w(y)` (`baseCoord`). On a vector it is
`Η₀ ⟪e₀, v⟫ - Η₁ ⟪e₁, v⟫ + Ξ₀ ⟪e₂, v⟫ + Ξ₁ ⟪e₃, v⟫`, evaluated at `(w(y), z(y))`. For families
independent of the base point it is the connection of the normal model
(`familyNormalModelConnection_comp_snd`). -/
def familyNormalModelConnection (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    V [⋀^Fin 1]→L[ℝ] ℝ :=
  normalModelConnection e (fun z ↦ Ξ (baseCoord e y, z)) (fun z ↦ Η (baseCoord e y, z)) y

/-- The connection of the normal model of a family constant along the base is the connection of
the normal model. -/
@[simp]
theorem familyNormalModelConnection_comp_snd (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    familyNormalModelConnection e (ξ ∘ Prod.snd) (η ∘ Prod.snd) = normalModelConnection e ξ η :=
  (rfl)

/-- The connection of the normal model of a family on a vector. -/
@[simp]
theorem familyNormalModelConnection_apply (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y v : V) :
    familyNormalModelConnection e Ξ Η y (fun _ ↦ v) =
      Η (baseCoord e y, normalCoord e y) 0 * ⟪e 0, v⟫ -
          Η (baseCoord e y, normalCoord e y) 1 * ⟪e 1, v⟫ +
        Ξ (baseCoord e y, normalCoord e y) 0 * ⟪e 2, v⟫ +
          Ξ (baseCoord e y, normalCoord e y) 1 * ⟪e 3, v⟫ := by
  simp [familyNormalModelConnection]

/-- The connection of the normal model of a family on `e₀` is `Η₀`. -/
-- These four frame values take priority over the general `familyNormalModelConnection_apply`.
@[simp high]
theorem familyNormalModelConnection_apply_zero (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    familyNormalModelConnection e Ξ Η y (fun _ ↦ e 0) = Η (baseCoord e y, normalCoord e y) 0 := by
  simp [familyNormalModelConnection]

/-- The connection of the normal model of a family on `e₁` is `-Η₁`. -/
@[simp high]
theorem familyNormalModelConnection_apply_one (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    familyNormalModelConnection e Ξ Η y (fun _ ↦ e 1) = -Η (baseCoord e y, normalCoord e y) 1 := by
  simp [familyNormalModelConnection]

/-- The connection of the normal model of a family on `e₂` is `Ξ₀`. -/
@[simp high]
theorem familyNormalModelConnection_apply_two (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    familyNormalModelConnection e Ξ Η y (fun _ ↦ e 2) = Ξ (baseCoord e y, normalCoord e y) 0 := by
  simp [familyNormalModelConnection]

/-- The connection of the normal model of a family on `e₃` is `Ξ₁`. -/
@[simp high]
theorem familyNormalModelConnection_apply_three (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    familyNormalModelConnection e Ξ Η y (fun _ ↦ e 3) = Ξ (baseCoord e y, normalCoord e y) 1 := by
  simp [familyNormalModelConnection]

/-- The connection of the normal model of a family is the pointwise covector of its values. -/
private theorem familyNormalModelConnection_eq_ofSubsingletonLIE
    (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    familyNormalModelConnection e Ξ Η y = ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
      (Η (baseCoord e y, normalCoord e y) 0 • innerSL ℝ (e 0) -
          Η (baseCoord e y, normalCoord e y) 1 • innerSL ℝ (e 1) +
        Ξ (baseCoord e y, normalCoord e y) 0 • innerSL ℝ (e 2) +
          Ξ (baseCoord e y, normalCoord e y) 1 • innerSL ℝ (e 3)) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [show v = fun _ ↦ v 0 from funext fun i ↦ by rw [Subsingleton.elim i 0]]
  simp

variable {Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}

/-- The connection of the normal model of a family is differentiable where the family is. -/
theorem differentiableAt_familyNormalModelConnection
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    DifferentiableAt ℝ (familyNormalModelConnection e Ξ Η) y := by
  have hc {Φ : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)}
      (hΦ : DifferentiableAt ℝ Φ (baseCoord e y, normalCoord e y)) (i : Fin 4) :
      DifferentiableAt ℝ (fun y' ↦ Φ (baseCoord e y', normalCoord e y') i) y :=
    DifferentiableAt.comp (g := fun p : ℂ × ℂ ↦ Φ p i) y (differentiableAt_euclidean.1 hΦ i)
      ((baseCoord e).prod (normalCoord e)).differentiableAt
  simp_rw [funext (familyNormalModelConnection_eq_ofSubsingletonLIE (e := e) Ξ Η)]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).differentiableAt.comp y (((((hc hΗ 0).smul_const _).sub
      ((hc hΗ 1).smul_const _)).add ((hc hΞ 0).smul_const _)).add ((hc hΞ 1).smul_const _))

/-- The derivative along `v` of the coefficient `Η₀` of the connection of the normal model of a
family on `e₀`: its derivative along the base in the direction `w(v)` plus its derivative along the
normal plane in the direction `z(v)`. -/
theorem fderiv_familyNormalModelConnection_apply_zero
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ familyNormalModelConnection e Ξ Η y' (fun _ ↦ e 0)) y v =
      fderiv ℝ (fun w ↦ Η (w, normalCoord e y) 0) (baseCoord e y) (baseCoord e v) +
        fderiv ℝ (fun z ↦ Η (baseCoord e y, z) 0) (normalCoord e y) (normalCoord e v) := by
  simp only [familyNormalModelConnection_apply_zero]
  exact fderiv_comp_baseCoord_normalCoord_apply (c := fun p ↦ Η p 0)
    (differentiableAt_euclidean.1 hΗ 0) v

/-- The derivative along `v` of the coefficient `-Η₁` of the connection of the normal model of a
family on `e₁`. -/
theorem fderiv_familyNormalModelConnection_apply_one
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ familyNormalModelConnection e Ξ Η y' (fun _ ↦ e 1)) y v =
      -(fderiv ℝ (fun w ↦ Η (w, normalCoord e y) 1) (baseCoord e y) (baseCoord e v) +
        fderiv ℝ (fun z ↦ Η (baseCoord e y, z) 1) (normalCoord e y) (normalCoord e v)) := by
  simp only [familyNormalModelConnection_apply_one, fderiv_fun_neg, neg_apply]
  rw [fderiv_comp_baseCoord_normalCoord_apply (c := fun p ↦ Η p 1)
    (differentiableAt_euclidean.1 hΗ 1) v]

/-- The derivative along `v` of the coefficient `Ξ₀` of the connection of the normal model of a
family on `e₂`. -/
theorem fderiv_familyNormalModelConnection_apply_two
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ familyNormalModelConnection e Ξ Η y' (fun _ ↦ e 2)) y v =
      fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y) 0) (baseCoord e y) (baseCoord e v) +
        fderiv ℝ (fun z ↦ Ξ (baseCoord e y, z) 0) (normalCoord e y) (normalCoord e v) := by
  simp only [familyNormalModelConnection_apply_two]
  exact fderiv_comp_baseCoord_normalCoord_apply (c := fun p ↦ Ξ p 0)
    (differentiableAt_euclidean.1 hΞ 0) v

/-- The derivative along `v` of the coefficient `Ξ₁` of the connection of the normal model of a
family on `e₃`. -/
theorem fderiv_familyNormalModelConnection_apply_three
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ familyNormalModelConnection e Ξ Η y' (fun _ ↦ e 3)) y v =
      fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y) 1) (baseCoord e y) (baseCoord e v) +
        fderiv ℝ (fun z ↦ Ξ (baseCoord e y, z) 1) (normalCoord e y) (normalCoord e v) := by
  simp only [familyNormalModelConnection_apply_three]
  exact fderiv_comp_baseCoord_normalCoord_apply (c := fun p ↦ Ξ p 1)
    (differentiableAt_euclidean.1 hΞ 1) v

variable [Fact (finrank ℝ V = 4)]

variable (e) in
/-- The **spinor of the normal model of a family** `(Ξ, Η)` of pairs of plane fields over the
base: at `y`, the spinor of the normal model (`normalModelSpinor`) of the plane fields over the base
point `w(y)` (`baseCoord`), that is `α_Ξ u₀ + α_Η β₀` evaluated at `(w(y), z(y))`. -/
def familyNormalModelSpinor (u₀ : positiveHalfSpinors o ρ)
    (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) : positiveHalfSpinors o ρ :=
  normalModelSpinor e u₀ (fun z ↦ Ξ (baseCoord e y, z)) (fun z ↦ Η (baseCoord e y, z)) y

/-- The spinor of the normal model of a family constant along the base is the spinor of the
normal model. -/
@[simp]
theorem familyNormalModelSpinor_comp_snd (u₀ : positiveHalfSpinors o ρ)
    (ξ η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    familyNormalModelSpinor e u₀ (ξ ∘ Prod.snd) (η ∘ Prod.snd) = normalModelSpinor e u₀ ξ η :=
  (rfl)

/-- The spinor of the normal model of a family at `y`: `α_Ξ u₀ + α_Η β₀` at `(w(y), z(y))`. -/
theorem familyNormalModelSpinor_apply (u₀ : positiveHalfSpinors o ρ)
    (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    familyNormalModelSpinor e u₀ Ξ Η y =
      Vortex.sectionValue (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) • u₀ +
        Vortex.sectionValue (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) • pairedSpinor e u₀ :=
  (rfl)

/-- The spinor of the normal model of a family as a spinor of `W`. -/
theorem coe_familyNormalModelSpinor (u₀ : positiveHalfSpinors o ρ)
    (Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) (y : V) :
    (familyNormalModelSpinor e u₀ Ξ Η y : W) =
      Vortex.sectionValue (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) • (u₀ : W) +
        Vortex.sectionValue (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) •
          (pairedSpinor e u₀ : W) :=
  (rfl)

omit [Fact (finrank ℝ V = 4)] in
/-- The section `α_Ξ (w, z) = 2 (Ξ₂ + i Ξ₃)` of a family, as a function of `(w, z)`, is
differentiable where the family is. -/
private theorem differentiableAt_familySectionValue {Φ : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)}
    {p : ℂ × ℂ} (hΦ : DifferentiableAt ℝ Φ p) :
    DifferentiableAt ℝ (fun q : ℂ × ℂ ↦ Vortex.sectionValue (fun z ↦ Φ (q.1, z)) q.2) p := by
  simp only [Vortex.sectionValue_apply]
  exact (((ofRealCLM.differentiableAt.comp p (differentiableAt_euclidean.1 hΦ 2)).add
    ((ofRealCLM.differentiableAt.comp p (differentiableAt_euclidean.1 hΦ 3)).mul_const I)).const_mul
      2 :)

/-- The spinor of the normal model of a family is differentiable where the family is. -/
theorem differentiableAt_familyNormalModelSpinor (u₀ : positiveHalfSpinors o ρ)
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    DifferentiableAt ℝ (fun y' ↦ (familyNormalModelSpinor e u₀ Ξ Η y' : W)) y := by
  simp only [coe_familyNormalModelSpinor]
  exact (((differentiableAt_familySectionValue hΞ).smul_const (u₀ : W)).fun_add
    ((differentiableAt_familySectionValue hΗ).smul_const (pairedSpinor e u₀ : W))).comp y
      ((baseCoord e).prod (normalCoord e)).differentiableAt

/-- The derivative of the spinor of the normal model of a family along a vector `v`: the
derivatives of the sections `α_Ξ` and `α_Η` along the base, in the direction `w(v)`, plus those
along the normal plane, in the direction `z(v)`, on `u₀` and on `β₀`. -/
theorem fderiv_familyNormalModelSpinor_apply (u₀ : positiveHalfSpinors o ρ)
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) (v : V) :
    fderiv ℝ (fun y' ↦ (familyNormalModelSpinor e u₀ Ξ Η y' : W)) y v =
      (fderiv ℝ (Vortex.sectionValue (fun w ↦ Ξ (w, normalCoord e y))) (baseCoord e y)
          (baseCoord e v) +
        fderiv ℝ (Vortex.sectionValue (fun z ↦ Ξ (baseCoord e y, z))) (normalCoord e y)
          (normalCoord e v)) • (u₀ : W) +
      (fderiv ℝ (Vortex.sectionValue (fun w ↦ Η (w, normalCoord e y))) (baseCoord e y)
          (baseCoord e v) +
        fderiv ℝ (Vortex.sectionValue (fun z ↦ Η (baseCoord e y, z))) (normalCoord e y)
          (normalCoord e v)) • (pairedSpinor e u₀ : W) := by
  have hf := differentiableAt_familySectionValue hΞ
  have hg := differentiableAt_familySectionValue hΗ
  -- The spinor as a function of the pair `(w(y'), z(y'))`, in the shape of the chain rule
  -- `fderiv_comp_baseCoord_normalCoord_apply`.
  have hsum : (fun y' ↦ (familyNormalModelSpinor e u₀ Ξ Η y' : W)) =
      fun y' ↦ Vortex.sectionValue (fun z ↦ Ξ ((baseCoord e y', normalCoord e y').1, z))
            (baseCoord e y', normalCoord e y').2 • (u₀ : W) +
          Vortex.sectionValue (fun z ↦ Η ((baseCoord e y', normalCoord e y').1, z))
            (baseCoord e y', normalCoord e y').2 • (pairedSpinor e u₀ : W) :=
    funext fun y' ↦ coe_familyNormalModelSpinor u₀ Ξ Η y'
  rw [hsum, fderiv_comp_baseCoord_normalCoord_apply ((hf.smul_const (u₀ : W)).fun_add
      (hg.smul_const (pairedSpinor e u₀ : W)))]
  have hfw := hf.hasFDerivAt_slice_fst.differentiableAt
  have hgw := hg.hasFDerivAt_slice_fst.differentiableAt
  have hfz := hf.hasFDerivAt_slice_snd.differentiableAt
  have hgz := hg.hasFDerivAt_slice_snd.differentiableAt
  rw [fderiv_fun_add (hfw.smul_const _) (hgw.smul_const _),
    fderiv_fun_add (hfz.smul_const _) (hgz.smul_const _), fderiv_smul_const hfw,
    fderiv_smul_const hgw, fderiv_smul_const hfz, fderiv_smul_const hgz]
  -- The base slice of the section of a family is the section of the base slice.
  have hsw (Φ : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)) :
      (fun w ↦ Vortex.sectionValue (fun z ↦ Φ (w, z)) (normalCoord e y)) =
        Vortex.sectionValue (fun w ↦ Φ (w, normalCoord e y)) :=
    funext fun w ↦ by simp only [Vortex.sectionValue_apply]
  rw [hsw Ξ, hsw Η]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, add_smul]
  abel

end Family

/-! ### The base couplings -/

section Coupling

/-- The **base coupling of the normal rows**: the linear map `D ↦ D 1 + K (D i)`, with
`K (v₀, v₁, v₂, v₃) = (-v₁, v₀, v₃, -v₂)`, through which the derivative `D` of the paired
family along the base enters the normal rows of the normal model. -/
def normalBaseCoupling :
    (ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun D := !₂[D 1 0 - D I 1, D 1 1 + D I 0, D 1 2 + D I 3, D 1 3 - D I 2]
  map_add' D D' := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c D := by
    ext i
    fin_cases i <;> simp <;> ring

/-- The **base coupling of the paired rows**: the linear map `D ↦ D 1 + K' (D i)`, with
`K' (v₀, v₁, v₂, v₃) = (-v₁, v₀, -v₃, v₂)`, through which the derivative `D` of the normal family
along the base enters the paired rows of the normal model. -/
def pairedBaseCoupling :
    (ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun D := !₂[D 1 0 - D I 1, D 1 1 + D I 0, D 1 2 - D I 3, D 1 3 + D I 2]
  map_add' D D' := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c D := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem normalBaseCoupling_apply_zero (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    normalBaseCoupling D 0 = D 1 0 - D I 1 := (rfl)

@[simp]
theorem normalBaseCoupling_apply_one (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    normalBaseCoupling D 1 = D 1 1 + D I 0 := (rfl)

@[simp]
theorem normalBaseCoupling_apply_two (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    normalBaseCoupling D 2 = D 1 2 + D I 3 := (rfl)

@[simp]
theorem normalBaseCoupling_apply_three (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    normalBaseCoupling D 3 = D 1 3 - D I 2 := (rfl)

@[simp]
theorem pairedBaseCoupling_apply_zero (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    pairedBaseCoupling D 0 = D 1 0 - D I 1 := (rfl)

@[simp]
theorem pairedBaseCoupling_apply_one (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    pairedBaseCoupling D 1 = D 1 1 + D I 0 := (rfl)

@[simp]
theorem pairedBaseCoupling_apply_two (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    pairedBaseCoupling D 2 = D 1 2 - D I 3 := (rfl)

@[simp]
theorem pairedBaseCoupling_apply_three (D : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4)) :
    pairedBaseCoupling D 3 = D 1 3 + D I 2 := (rfl)

end Coupling

/-! ### The rows of the normal model -/

section Rows

variable {ξ η : ℂ → EuclideanSpace ℝ (Fin 4)} {Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)} {y : V}

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
/-- **The gauge-fixing row of the normal model of a family**: at the pullback `(b_x, α_x u₀)` of a
plane field `x`, the gauge-fixing row of the linearized flat limiting equations, applied to the
normal model of a family `(Ξ, Η)`, is the gauge row of `L_x` on the plane field `Ξ (w, ·)` over the
base point `w = w(y)`, plus the gauge row `∂_s Η₀ - ∂_t Η₁` (`w = s + i t`) of the base coupling
of the paired family (`normalBaseCoupling`), at the normal coordinate. -/
theorem flatDeformationGauge_familyNormalModel (hu₀₁ : ‖u₀‖ = 1)
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    flatDeformationGauge e (familyNormalModelConnection e Ξ Η) (normalModelSpinor e u₀ x 0)
        (familyNormalModelSpinor e u₀ Ξ Η) y =
      (Vortex.gaugeFixedOperator x (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
        normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, normalCoord e y)) (baseCoord e y))) 0 := by
  have hβ : ⟪(u₀ : W), (pairedSpinor e u₀ : W)⟫_ℂ = 0 := by
    rw [← Submodule.coe_inner]
    exact inner_pairedSpinor_eq_zero_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hρ hu₀
  have hu : ⟪(u₀ : W), (u₀ : W)⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, Submodule.norm_coe, hu₀₁]
    simp
  have hψ : (normalModelSpinor e u₀ x 0 y : W) =
      Vortex.sectionValue x (normalCoord e y) • (u₀ : W) := by
    rw [normalModelSpinor_zero_right, Submodule.coe_smul]
  simp only [flatDeformationGauge, Fin.sum_univ_four,
    fderiv_familyNormalModelConnection_apply_zero hΗ,
    fderiv_familyNormalModelConnection_apply_one hΗ,
    fderiv_familyNormalModelConnection_apply_two hΞ,
    fderiv_familyNormalModelConnection_apply_three hΞ]
  rw [hψ, coe_familyNormalModelSpinor, inner_smul_left, inner_smul_left, inner_add_right,
    inner_smul_right, inner_smul_right, hu, hβ]
  simp [Vortex.gaugeAdjoint_def,
    ← hΗ.hasFDerivAt_slice_fst.differentiableAt.fderiv_piLp_apply]
  ring

/-- The curvature row of a variation `(b', ζ)` paired with `e₀ ∧ eⱼ`, where
`⋆(e₀ ∧ eⱼ) = s eₖ ∧ eₗ`: the curl of `b'` along `e₀ ∧ eⱼ`, plus `s` times its curl along
`eₖ ∧ eₗ`, plus half the `q'`-coordinate. -/
private theorem inner_flatDeformationCurvature_ιMulti_zero {b' : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    (hb' : DifferentiableAt ℝ b' y) (ψ ζ : V → positiveHalfSpinors o ρ) {j k l : Fin 4} {s : ℝ}
    (hj : o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e j]) = s • ιMulti ℝ 2 ![e k, e l]) :
    ⟪flatDeformationCurvature o ρ hkl b' ψ ζ y, ιMulti ℝ 2 ![e 0, e j]⟫ =
      fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e 0)) y (e j) -
          fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e j)) y (e 0) +
        s * (fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e k)) y (e l) -
          fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ e l)) y (e k)) +
        2⁻¹ * ⟪(quadraticTwoFormPolar o ρ hkl (ψ y) (ζ y) : ⋀[ℝ]^2 V), ιMulti ℝ 2 ![e 0, e j]⟫ := by
  have hs : ∀ a b : ⋀[ℝ]^2 V, ⟪o.hodgeStar hkl a, b⟫ = ⟪a, o.hodgeStar hkl b⟫ :=
    o.isSymmetric_hodgeStar_of_even even_two hkl
  rw [flatDeformationCurvature, inner_add_left, inner_add_left, real_inner_smul_left, hs, hj,
    real_inner_smul_right, inner_alternatingFormEquiv_symm_neg_extDeriv hb',
    inner_alternatingFormEquiv_symm_neg_extDeriv hb']

section Curvature

include hQ hkl he h₀ h₂ hρ hu₀

/-- **The curvature row of the normal model of a family along `e₀ ∧ e₁`**: at the pullback
`(b_x, α_x u₀)` of a plane field `x`, the curvature row of the linearized flat limiting equations,
applied to the normal model of a family `(Ξ, Η)`, pairs with `e₀ ∧ e₁` to the first equation row of
`L_x` on `Ξ (w, ·)`, plus the corresponding row `∂_s Η₁ + ∂_t Η₀` (`w = s + i t`) of the base
coupling of the paired family, at the normal coordinate. -/
theorem inner_flatDeformationCurvature_familyNormalModel_zero_one (hu₀₁ : ‖u₀‖ = 1)
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (familyNormalModelConnection e Ξ Η)
        (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ Η) y,
        ιMulti ℝ 2 ![e 0, e 1]⟫ =
      (Vortex.gaugeFixedOperator x (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
        normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, normalCoord e y)) (baseCoord e y))) 1 := by
  rw [inner_flatDeformationCurvature_ιMulti_zero hkl
      (differentiableAt_familyNormalModelConnection hΞ hΗ) _ _
      ((o.hodgeStar_ιMulti_zero_one hkl he).trans (one_smul ℝ _).symm),
    normalModelSpinor_zero_right, familyNormalModelSpinor_apply,
    inner_quadraticTwoFormPolar_ιMulti_zero_one hQ hkl he h₀ h₂ hρ hu₀ hu₀₁,
    Vortex.conj_sectionValue_mul_sectionValue_re]
  simp only [fderiv_familyNormalModelConnection_apply_zero hΗ,
    fderiv_familyNormalModelConnection_apply_one hΗ,
    fderiv_familyNormalModelConnection_apply_two hΞ,
    fderiv_familyNormalModelConnection_apply_three hΞ]
  simp [Vortex.gaugeFixedOperator_apply_one, Vortex.linearizedEquation_apply_zero,
    ← hΗ.hasFDerivAt_slice_fst.differentiableAt.fderiv_piLp_apply]
  ring

/-- **The curvature row of the normal model of a family along `e₀ ∧ e₂`**: the curvature row of the
linearized flat limiting equations at the pullback of `x`, applied to the normal model of a family
`(Ξ, Η)`, pairs with `e₀ ∧ e₂` to minus the gauge row of `L_x*` on `Η (w, ·)`, minus the
corresponding row `∂_s Ξ₀ - ∂_t Ξ₁` (`w = s + i t`) of the base coupling of the normal family, at
the normal coordinate. -/
theorem inner_flatDeformationCurvature_familyNormalModel_zero_two (hu₀₁ : ‖u₀‖ = 1)
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (familyNormalModelConnection e Ξ Η)
        (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ Η) y,
        ιMulti ℝ 2 ![e 0, e 2]⟫ =
      -(Vortex.gaugeFixedAdjoint x (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) +
        pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y)) (baseCoord e y))) 0 := by
  rw [inner_flatDeformationCurvature_ιMulti_zero hkl
      (differentiableAt_familyNormalModelConnection hΞ hΗ) _ _
      ((o.hodgeStar_ιMulti_zero_two hkl he).trans (neg_one_smul ℝ _).symm),
    normalModelSpinor_zero_right, familyNormalModelSpinor_apply,
    inner_quadraticTwoFormPolar_ιMulti_zero_two hQ hkl he h₀ h₂ hρ hu₀ hu₀₁,
    mul_comm (Vortex.sectionValue x _), Vortex.conj_sectionValue_mul_sectionValue_im]
  simp only [fderiv_familyNormalModelConnection_apply_zero hΗ,
    fderiv_familyNormalModelConnection_apply_one hΗ,
    fderiv_familyNormalModelConnection_apply_two hΞ,
    fderiv_familyNormalModelConnection_apply_three hΞ]
  simp [Vortex.gaugeFixedAdjoint_apply_zero,
    ← hΞ.hasFDerivAt_slice_fst.differentiableAt.fderiv_piLp_apply]
  ring

/-- **The curvature row of the normal model of a family along `e₀ ∧ e₃`**: the curvature row of the
linearized flat limiting equations at the pullback of `x`, applied to the normal model of a family
`(Ξ, Η)`, pairs with `e₀ ∧ e₃` to minus the curvature row of `L_x*` on `Η (w, ·)`, minus the
corresponding row `∂_s Ξ₁ + ∂_t Ξ₀` (`w = s + i t`) of the base coupling of the normal family, at
the normal coordinate. -/
theorem inner_flatDeformationCurvature_familyNormalModel_zero_three (hu₀₁ : ‖u₀‖ = 1)
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (familyNormalModelConnection e Ξ Η)
        (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ Η) y,
        ιMulti ℝ 2 ![e 0, e 3]⟫ =
      -(Vortex.gaugeFixedAdjoint x (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) +
        pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y)) (baseCoord e y))) 1 := by
  rw [inner_flatDeformationCurvature_ιMulti_zero hkl
      (differentiableAt_familyNormalModelConnection hΞ hΗ) _ _
      ((o.hodgeStar_ιMulti_zero_three hkl he).trans (one_smul ℝ _).symm),
    normalModelSpinor_zero_right, familyNormalModelSpinor_apply,
    inner_quadraticTwoFormPolar_ιMulti_zero_three hQ hkl he h₀ h₂ hρ hu₀ hu₀₁,
    mul_comm (Vortex.sectionValue x _), Vortex.conj_sectionValue_mul_sectionValue_re]
  simp only [fderiv_familyNormalModelConnection_apply_zero hΗ,
    fderiv_familyNormalModelConnection_apply_one hΗ,
    fderiv_familyNormalModelConnection_apply_two hΞ,
    fderiv_familyNormalModelConnection_apply_three hΞ]
  simp [Vortex.gaugeFixedAdjoint_apply_one,
    ← hΞ.hasFDerivAt_slice_fst.differentiableAt.fderiv_piLp_apply]
  ring

end Curvature

omit [FiniteDimensional ℂ W] in
/-- The Dirac row of the normal model of a family, split along the canonical spinor `u₀` and the
paired spinor `β₀`: the `k`-th summand is `c(e_k)` applied to `X_k u₀ + Y_k β₀`, with `X_k` and
`Y_k` the covariant derivatives of the two sections, along the base and the normal plane, `X_k`
including the connection variation times `α_x`. -/
private theorem flatDeformationDirac_familyNormalModel_eq_sum
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    flatDeformationDirac e (normalModelConnection e x 0) (familyNormalModelConnection e Ξ Η)
        (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ Η) y =
      ∑ k, (fderiv ℝ (Vortex.sectionValue (fun w ↦ Ξ (w, normalCoord e y))) (baseCoord e y)
            (baseCoord e (e k)) +
          fderiv ℝ (Vortex.sectionValue (fun z ↦ Ξ (baseCoord e y, z))) (normalCoord e y)
            (normalCoord e (e k)) +
          I * normalModelConnection e x 0 y (fun _ ↦ e k) *
            Vortex.sectionValue (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
          I * familyNormalModelConnection e Ξ Η y (fun _ ↦ e k) *
            Vortex.sectionValue x (normalCoord e y)) • ρ (ι Q (e k)) u₀ +
        ∑ k, (fderiv ℝ (Vortex.sectionValue (fun w ↦ Η (w, normalCoord e y))) (baseCoord e y)
            (baseCoord e (e k)) +
          fderiv ℝ (Vortex.sectionValue (fun z ↦ Η (baseCoord e y, z))) (normalCoord e y)
            (normalCoord e (e k)) +
          I * normalModelConnection e x 0 y (fun _ ↦ e k) *
            Vortex.sectionValue (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y)) •
          ρ (ι Q (e k)) (pairedSpinor e u₀ : W) := by
  rw [flatDeformationDirac_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [fderiv_familyNormalModelSpinor_apply u₀ hΞ hΗ, normalModelSpinor_zero_right,
    coe_familyNormalModelSpinor, Submodule.coe_smul]
  simp only [map_add, map_smul]
  module

include hQ hkl he h₀ h₂ hu₀ in
/-- **The Dirac row of the normal model of a family**: at the pullback `(b_x, α_x u₀)` of a plane
field `x`, the Dirac row of the linearized flat limiting equations, applied to the normal model of
a family `(Ξ, Η)`, is `2 (P₂ + i P₃) c(e₀) u₀ + 2 (N₂ + i N₃) c(e₂) u₀` at the normal coordinate,
where `N = L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)` and
`P = L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)`, `D_w Φ` being the real derivative of the base
slice `Φ (·, z(y))` at `w = w(y)`. Along the base, the paired family thus enters
the normal rows and the normal family the paired rows. -/
theorem flatDeformationDirac_familyNormalModel
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    flatDeformationDirac e (normalModelConnection e x 0) (familyNormalModelConnection e Ξ Η)
        (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ Η) y =
      (2 * (((Vortex.gaugeFixedAdjoint x (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) +
            pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y)) (baseCoord e y))) 2 :
              ℂ) +
          (Vortex.gaugeFixedAdjoint x (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) +
            pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y)) (baseCoord e y))) 3 *
              I)) • ρ (ι Q (e 0)) u₀ +
        (2 * (((Vortex.gaugeFixedOperator x (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
            normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, normalCoord e y)) (baseCoord e y))) 2 :
              ℂ) +
          (Vortex.gaugeFixedOperator x (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
            normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, normalCoord e y)) (baseCoord e y))) 3 *
              I)) • ρ (ι Q (e 2)) u₀ := by
  set N := Vortex.gaugeFixedOperator x (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
    normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, normalCoord e y)) (baseCoord e y)) with hN
  set P := Vortex.gaugeFixedAdjoint x (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) +
    pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y)) (baseCoord e y)) with hP
  -- `X k`, `Y k`: the coefficients on `u₀` and `β₀` of the `k`-th covariant derivative.
  set X : Fin 4 → ℂ := fun k ↦
    fderiv ℝ (Vortex.sectionValue (fun w ↦ Ξ (w, normalCoord e y))) (baseCoord e y)
      (baseCoord e (e k)) + fderiv ℝ (Vortex.sectionValue (fun z ↦ Ξ (baseCoord e y, z)))
      (normalCoord e y) (normalCoord e (e k)) + I * normalModelConnection e x 0 y (fun _ ↦ e k) *
      Vortex.sectionValue (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
    I * familyNormalModelConnection e Ξ Η y (fun _ ↦ e k) *
      Vortex.sectionValue x (normalCoord e y) with hX
  set Y : Fin 4 → ℂ := fun k ↦
    fderiv ℝ (Vortex.sectionValue (fun w ↦ Η (w, normalCoord e y))) (baseCoord e y)
      (baseCoord e (e k)) + fderiv ℝ (Vortex.sectionValue (fun z ↦ Η (baseCoord e y, z)))
      (normalCoord e y) (normalCoord e (e k)) + I * normalModelConnection e x 0 y (fun _ ↦ e k) *
      Vortex.sectionValue (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) with hY
  rw [flatDeformationDirac_familyNormalModel_eq_sum x hΞ hΗ,
    sum_smul_ι_apply_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀,
    sum_smul_ι_apply_pairedSpinor_of_cliffordProjection_apply_eq_self hQ hkl he h₀ h₂ hu₀]
  have hΞw := hΞ.hasFDerivAt_slice_fst.differentiableAt
  have hΗw := hΗ.hasFDerivAt_slice_fst.differentiableAt
  have hΞz := differentiableAt_euclidean.1 hΞ.hasFDerivAt_slice_snd.differentiableAt
  have hΗz := differentiableAt_euclidean.1 hΗ.hasFDerivAt_slice_snd.differentiableAt
  have hAB : X 0 + I * X 1 - (Y 2 - I * Y 3) = 2 * ((P 2 : ℂ) + P 3 * I) ∧
      X 2 + I * X 3 + (Y 0 - I * Y 1) = 2 * ((N 2 : ℂ) + N 3 * I) := by
    simp [hX, hY, hN, hP, Vortex.sectionValue_apply,
      Vortex.fderiv_sectionValue_apply (differentiableAt_euclidean.1 hΞw 2)
        (differentiableAt_euclidean.1 hΞw 3),
      Vortex.fderiv_sectionValue_apply (differentiableAt_euclidean.1 hΗw 2)
        (differentiableAt_euclidean.1 hΗw 3),
      Vortex.fderiv_sectionValue_apply (hΞz 2) (hΞz 3),
      Vortex.fderiv_sectionValue_apply (hΗz 2) (hΗz 3), Vortex.gaugeFixedAdjoint_apply_two,
      Vortex.gaugeFixedAdjoint_apply_three, Vortex.gaugeFixedOperator_apply_two,
      Vortex.gaugeFixedOperator_apply_three, Vortex.linearizedEquation_apply_one,
      Vortex.linearizedEquation_apply_two, ← hΞw.fderiv_piLp_apply, ← hΗw.fderiv_piLp_apply]
    constructor <;> grind [I_sq]
  rw [← hAB.1, ← hAB.2]
  module

/-! The rows of the normal model of base-independent plane fields are the case of a family
constant along the base, for which both base couplings vanish. -/

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
  simpa using flatDeformationGauge_familyNormalModel hQ hkl he h₀ h₂ hρ hu₀ x
    (Ξ := ξ ∘ Prod.snd) (Η := η ∘ Prod.snd) hu₀₁ (differentiableAt_comp_snd_iff.2 hξ)
    (differentiableAt_comp_snd_iff.2 hη)

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
  simpa using inner_flatDeformationCurvature_familyNormalModel_zero_one hQ hkl he h₀ h₂ hρ hu₀ x
    (Ξ := ξ ∘ Prod.snd) (Η := η ∘ Prod.snd) hu₀₁ (differentiableAt_comp_snd_iff.2 hξ)
    (differentiableAt_comp_snd_iff.2 hη)

/-- **The curvature row of the normal model along `e₀ ∧ e₂` is minus the gauge row of `L_x*`**:
the curvature row of the linearized flat limiting equations at the pullback of `x`, applied to the
normal model of `(ξ, η)`, pairs with `e₀ ∧ e₂` to `-(L_x* η)₀` at the normal coordinate. -/
theorem inner_flatDeformationCurvature_normalModel_zero_two (hu₀₁ : ‖u₀‖ = 1)
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
        (normalModelSpinor e u₀ ξ η) y, ιMulti ℝ 2 ![e 0, e 2]⟫ =
      -Vortex.gaugeFixedAdjoint x η (normalCoord e y) 0 := by
  simpa using inner_flatDeformationCurvature_familyNormalModel_zero_two hQ hkl he h₀ h₂ hρ hu₀ x
    (Ξ := ξ ∘ Prod.snd) (Η := η ∘ Prod.snd) hu₀₁ (differentiableAt_comp_snd_iff.2 hξ)
    (differentiableAt_comp_snd_iff.2 hη)

/-- **The curvature row of the normal model along `e₀ ∧ e₃` is minus the curvature row of
`L_x*`**: the curvature row of the linearized flat limiting equations at the pullback of `x`,
applied to the normal model of `(ξ, η)`, pairs with `e₀ ∧ e₃` to `-(L_x* η)₁` at the normal
coordinate. -/
theorem inner_flatDeformationCurvature_normalModel_zero_three (hu₀₁ : ‖u₀‖ = 1)
    (hξ : DifferentiableAt ℝ ξ (normalCoord e y)) (hη : DifferentiableAt ℝ η (normalCoord e y)) :
    ⟪flatDeformationCurvature o ρ hkl (normalModelConnection e ξ η) (normalModelSpinor e u₀ x 0)
        (normalModelSpinor e u₀ ξ η) y, ιMulti ℝ 2 ![e 0, e 3]⟫ =
      -Vortex.gaugeFixedAdjoint x η (normalCoord e y) 1 := by
  simpa using inner_flatDeformationCurvature_familyNormalModel_zero_three hQ hkl he h₀ h₂ hρ hu₀ x
    (Ξ := ξ ∘ Prod.snd) (Η := η ∘ Prod.snd) hu₀₁ (differentiableAt_comp_snd_iff.2 hξ)
    (differentiableAt_comp_snd_iff.2 hη)

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
  simpa using flatDeformationDirac_familyNormalModel hQ hkl he h₀ h₂ hu₀ x
    (Ξ := ξ ∘ Prod.snd) (Η := η ∘ Prod.snd) (differentiableAt_comp_snd_iff.2 hξ)
    (differentiableAt_comp_snd_iff.2 hη)

end Rows

/-! ### The kernel of the normal model at a point -/

section Kernel

variable [Fact (finrank ℝ V = 4)] (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)

variable [FiniteDimensional ℂ W] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  {u₀ : positiveHalfSpinors o ρ} (hu₀ : cliffordProjection o ρ J.kahlerForm u₀ = u₀)

include hQ hkl he h₀ h₂ hρ hu₀ in
/-- **The kernel of the normal model of a family at a point**: at the pullback `(b_x, α_x u₀)` of
a plane field `x`, the three rows of the linearized flat limiting equations vanish at `y` on the
normal model of a family `(Ξ, Η)` exactly when, at the base point `w = w(y)` and the normal
coordinate `z = z(y)`, `L_x Ξ (w, ·) + normalBaseCoupling (D_w Η)` and
`L_x* Η (w, ·) + pairedBaseCoupling (D_w Ξ)` vanish, `D_w Φ` being the real derivative of the base
slice `Φ (·, z)` at `w`. -/
theorem flatDeformation_familyNormalModel_eq_zero_iff (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {Ξ Η : ℂ × ℂ → EuclideanSpace ℝ (Fin 4)} {y : V} (hu₀₁ : ‖u₀‖ = 1)
    (hΞ : DifferentiableAt ℝ Ξ (baseCoord e y, normalCoord e y))
    (hΗ : DifferentiableAt ℝ Η (baseCoord e y, normalCoord e y)) :
    (flatDeformationGauge e (familyNormalModelConnection e Ξ Η) (normalModelSpinor e u₀ x 0)
          (familyNormalModelSpinor e u₀ Ξ Η) y = 0 ∧
        flatDeformationCurvature o ρ hkl (familyNormalModelConnection e Ξ Η)
          (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ Η) y = 0 ∧
        flatDeformationDirac e (normalModelConnection e x 0) (familyNormalModelConnection e Ξ Η)
          (normalModelSpinor e u₀ x 0) (familyNormalModelSpinor e u₀ Ξ Η) y = 0) ↔
      Vortex.gaugeFixedOperator x (fun z ↦ Ξ (baseCoord e y, z)) (normalCoord e y) +
          normalBaseCoupling (fderiv ℝ (fun w ↦ Η (w, normalCoord e y)) (baseCoord e y)) = 0 ∧
        Vortex.gaugeFixedAdjoint x (fun z ↦ Η (baseCoord e y, z)) (normalCoord e y) +
          pairedBaseCoupling (fderiv ℝ (fun w ↦ Ξ (w, normalCoord e y)) (baseCoord e y)) = 0 := by
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
  rw [flatDeformationGauge_familyNormalModel hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hΞ hΗ,
    o.eq_zero_iff_of_hodgeStar_eq_self hkl he (hodgeStar_flatDeformationCurvature hkl _ _ _ _),
    inner_flatDeformationCurvature_familyNormalModel_zero_one hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hΞ hΗ,
    inner_flatDeformationCurvature_familyNormalModel_zero_two hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hΞ hΗ,
    inner_flatDeformationCurvature_familyNormalModel_zero_three hQ hkl he h₀ h₂ hρ hu₀ x hu₀₁ hΞ
      hΗ,
    flatDeformationDirac_familyNormalModel hQ hkl he h₀ h₂ hu₀ x hΞ hΗ, hD, hC, hC, hvec, hvec,
    neg_eq_zero, neg_eq_zero]
  tauto

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
  simpa using flatDeformation_familyNormalModel_eq_zero_iff hkl he hQ h₀ h₂ hρ hu₀ x
    (Ξ := ξ ∘ Prod.snd) (Η := η ∘ Prod.snd) hu₀₁ (differentiableAt_comp_snd_iff.2 hξ)
    (differentiableAt_comp_snd_iff.2 hη)

end Kernel

end TauCeti.SeibergWitten
