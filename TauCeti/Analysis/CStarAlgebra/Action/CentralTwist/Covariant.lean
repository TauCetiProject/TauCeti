/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralTwist.Convolution
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Integrated
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# Twisted covariant pairs and their vector-valued integrated forms

Given a point-norm continuous action `α` of a topological group `G` on a possibly nonunital
C⋆-algebra `A` and a normalized continuous central multiplier cocycle `ω : CentralCocycle α`, a
*twisted covariant pair* `(π, U)` on a Hilbert space `H` consists of a nondegenerate
`⋆`-representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` together with a strongly continuous unitary family
`U : G → unitary (H →L[ℂ] H)` satisfying `U 1 = 1`, the covariance identity
`U_s π(a) U_s* = π(α_s(a))`, and the projective law `U_s U_t = π'(ω(s, t)) U_{s * t}`, where `π'` is
the unique multiplier extension `NonUnitalStarAlgHom.multiplierExtension`. Unless `π'(ω)` is
trivial, `U` is not a group homomorphism.

For a compactly supported continuous coefficient function `f : C_c(G, A)` and a measure `μ` finite
on compacts, the *integrated form* is the bounded operator defined by Hilbert-space vector
integration

`P.integratedOperator μ f v = ∫ s, P.pi (f s) (U_s v) ∂μ`,

bounded in operator norm by `∫ s, ‖f s‖ ∂μ`. No operator-norm continuity of `U`, unitality of `A`,
separability, second countability, or σ-finiteness of `μ` is assumed. When `μ` is left-invariant,
covariance and the projective law yield `P.pi (f r) U_r P.pi (g t) U_t = P.pi (f r * α_r(g t) *
ω(r, t)) U_{r * t}`, and compact-support Fubini together with left-translation invariance makes
`P.integratedOperator μ` multiplicative for `twistedConvolution`
(`centralIntegrated_twistedConvolution`). Against any Haar measure, the modular factor in
`ω.involution` cancels Haar inversion so that `P.integratedOperator μ` sends `ω.involution` to the
operator adjoint.

For the trivial cocycle `ω = 1`, `CentralCovariantPair H α 1` corresponds bijectively to
nondegenerate `CovariantRepresentation α H` with matching integrated forms, while
`CentralCovariantPair.ofScalar` constructs twisted covariant pairs for genuinely nontrivial scalar
`unitary ℂ`-valued `2`-cocycles.

## Main definitions

* `TauCeti.CStarAction.CentralCovariantPair`: twisted covariant pair `(π, U)` for `(α, ω)`.
* `TauCeti.CStarAction.CentralCovariantPair.comp`: pullback along `ContinuousMonoidHom`.
* `TauCeti.CStarAction.CentralCovariantPair.toCovariantRepresentation` and
  `TauCeti.CStarAction.CovariantRepresentation.toCentralCovariantPair`: comparison with untwisted
  covariant representations at `ω = 1`.
* `TauCeti.CStarAction.CentralCovariantPair.ofScalar`: twisted covariant pair from a scalar
  projective unitary representation.
* `TauCeti.CStarAction.CentralCovariantPair.integratedOperator`: vector-valued integrated form on
  `C_c(G, A)`.

## Main statements

* `TauCeti.CStarAction.CentralCovariantPair.norm_integratedOperator_le`:
  `‖P.integratedOperator μ f‖ ≤ ∫ s, ‖f s‖ ∂μ`.
* `TauCeti.CStarAction.CentralCovariantPair.integratedOperator_convolution` and
  `TauCeti.CStarAction.centralIntegrated_twistedConvolution`: multiplicativity under
  `twistedConvolution` for left-invariant `μ`.
* `TauCeti.CStarAction.CentralCovariantPair.integratedOperator_involution`:
  `P.integratedOperator μ (ω.involution f) = star (P.integratedOperator μ f)` for Haar `μ`.

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc.
  Cambridge Philos. Soc. 106 (1989), 293–311, Section 2 and Proposition 2.7.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported InnerProductSpace MultiplierAlgebra CStarAlgebra

namespace TauCeti.CStarAction

/-- A twisted covariant pair for a central cocycle: a nondegenerate representation `π` of `A` and a
strongly continuous family of unitaries `U` with `U_e = 1`, the covariance identity, and the
projective law `U_s U_t = π'(ω(s, t)) U_{s * t}`, where `π'` is
`NonUnitalStarAlgHom.multiplierExtension`. `U` is not a group representation unless the represented
cocycle is trivial. -/
structure CentralCovariantPair {G A : Type*} (H : Type*) [Group G] [TopologicalSpace G]
    [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (α : CStarAction G A) (ω : CentralCocycle α) where
  /-- The coefficient representation. -/
  pi : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  /-- Nondegeneracy of the coefficient representation. -/
  nondegenerate : pi.IsNondegenerate
  /-- The projective unitary family. -/
  unitaryMap : G → unitary (H →L[ℂ] H)
  /-- Normalization at the identity. -/
  at_one : unitaryMap 1 = 1
  /-- Strong continuity of the unitary family. -/
  strong_continuous : ∀ ξ : H, Continuous fun s => (unitaryMap s : H →L[ℂ] H) ξ
  /-- Covariance `U_s π(a) U_s* = π(α_s(a))`. -/
  covariance : ∀ s a,
    (unitaryMap s : H →L[ℂ] H) * pi a * star (unitaryMap s : H →L[ℂ] H) =
      pi (α s a)
  /-- The projective law `U_s U_t = π'(ω(s, t)) U_{s * t}`. -/
  projective : ∀ s t,
    (unitaryMap s : H →L[ℂ] H) * (unitaryMap t : H →L[ℂ] H) =
      pi.multiplierExtension nondegenerate (ω.value s t : 𝓜(ℂ, A)) *
        (unitaryMap (s * t) : H →L[ℂ] H)

namespace CentralCovariantPair

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {ω : CentralCocycle α}

/-- The coefficient representation and unitary family determine a twisted covariant pair. -/
@[ext]
theorem ext {P Q : CentralCovariantPair H α ω}
    (hπ : P.pi = Q.pi) (hU : P.unitaryMap = Q.unitaryMap) : P = Q := by
  cases P
  cases Q
  cases hπ
  cases hU
  rfl

@[simp]
theorem unitaryMap_one (P : CentralCovariantPair H α ω) : P.unitaryMap 1 = 1 :=
  P.at_one

/-- Covariance written as `U_s * π(a) = π(α_s(a)) * U_s`. -/
@[simp]
theorem unitaryMap_mul_pi (P : CentralCovariantPair H α ω) (s : G) (a : A) :
    (P.unitaryMap s : H →L[ℂ] H) * P.pi a =
      P.pi (α s a) * (P.unitaryMap s : H →L[ℂ] H) := by
  calc (P.unitaryMap s : H →L[ℂ] H) * P.pi a
      = (P.unitaryMap s : H →L[ℂ] H) * P.pi a * star (P.unitaryMap s : H →L[ℂ] H) *
          (P.unitaryMap s : H →L[ℂ] H) := by
        rw [mul_assoc (_ * _), Unitary.coe_star_mul_self, mul_one]
    _ = P.pi (α s a) * (P.unitaryMap s : H →L[ℂ] H) := by rw [P.covariance]

/-- Pointwise vector form of covariance: `U_s (π a ξ) = π (α_s a) (U_s ξ)`. -/
theorem unitaryMap_apply_pi_apply (P : CentralCovariantPair H α ω) (s : G) (a : A) (ξ : H) :
    (P.unitaryMap s : H →L[ℂ] H) (P.pi a ξ) =
      P.pi (α s a) ((P.unitaryMap s : H →L[ℂ] H) ξ) :=
  congr($(P.unitaryMap_mul_pi s a) ξ)

/-- Combined covariance and projective product identity:
`π(a) U_r π(b) U_t = π(a α_r(b) ω(r, t)) U_{r * t}`. -/
theorem pi_mul_unitaryMap_mul (P : CentralCovariantPair H α ω) (r t : G) (a b : A) :
    P.pi a * (P.unitaryMap r : H →L[ℂ] H) * (P.pi b * (P.unitaryMap t : H →L[ℂ] H)) =
      P.pi ((ω.value r t : 𝓜(ℂ, A)).snd (a * α r b)) *
        (P.unitaryMap (r * t) : H →L[ℂ] H) := by
  calc P.pi a * (P.unitaryMap r : H →L[ℂ] H) * (P.pi b * (P.unitaryMap t : H →L[ℂ] H))
      = P.pi a * ((P.unitaryMap r : H →L[ℂ] H) * P.pi b) *
          (P.unitaryMap t : H →L[ℂ] H) := by
        simp only [mul_assoc]
    _ = (P.pi a * P.pi (α r b)) *
          ((P.unitaryMap r : H →L[ℂ] H) * (P.unitaryMap t : H →L[ℂ] H)) := by
        rw [P.unitaryMap_mul_pi]
        simp only [mul_assoc]
    _ = (P.pi (a * α r b) *
          P.pi.multiplierExtension P.nondegenerate (ω.value r t : 𝓜(ℂ, A))) *
            (P.unitaryMap (r * t) : H →L[ℂ] H) := by
        rw [← map_mul, P.projective, mul_assoc]
    _ = P.pi ((ω.value r t : 𝓜(ℂ, A)).snd (a * α r b)) *
          (P.unitaryMap (r * t) : H →L[ℂ] H) := by
        rw [P.pi.mul_multiplierExtension_eq_snd]

/-- The adjoint of `U_{s⁻¹}` differs from `U_s` by the represented cocycle factor `ω(s, s⁻¹)*`. -/
theorem star_unitaryMap_inv (P : CentralCovariantPair H α ω) (s : G) :
    star (P.unitaryMap s⁻¹ : H →L[ℂ] H) =
      P.pi.multiplierExtension P.nondegenerate (star (ω.value s s⁻¹ : 𝓜(ℂ, A))) *
        (P.unitaryMap s : H →L[ℂ] H) := by
  have hproj : (P.unitaryMap s : H →L[ℂ] H) * (P.unitaryMap s⁻¹ : H →L[ℂ] H) =
      P.pi.multiplierExtension P.nondegenerate (ω.value s s⁻¹ : 𝓜(ℂ, A)) := by
    simpa using P.projective s s⁻¹
  calc star (P.unitaryMap s⁻¹ : H →L[ℂ] H)
      = (star (P.unitaryMap s⁻¹ : H →L[ℂ] H) * star (P.unitaryMap s : H →L[ℂ] H)) *
          (P.unitaryMap s : H →L[ℂ] H) := by
        rw [mul_assoc, Unitary.coe_star_mul_self, mul_one]
    _ = P.pi.multiplierExtension P.nondegenerate (star (ω.value s s⁻¹ : 𝓜(ℂ, A))) *
          (P.unitaryMap s : H →L[ℂ] H) := by
        rw [← star_mul, hproj, map_star]

/-- Pull back a twisted covariant pair along a continuous group homomorphism. -/
def comp {G' : Type*} [Group G'] [TopologicalSpace G'] (P : CentralCovariantPair H α ω)
    (φ : ContinuousMonoidHom G' G) : CentralCovariantPair H (α.comp φ) (ω.comp φ) where
  pi := P.pi
  nondegenerate := P.nondegenerate
  unitaryMap s' := P.unitaryMap (φ s')
  at_one := by simp
  strong_continuous ξ := (P.strong_continuous ξ).comp φ.continuous
  covariance s' a := by simpa using P.covariance (φ s') a
  projective s' t' := by simpa [map_mul] using P.projective (φ s') (φ t')

@[simp]
theorem comp_pi {G' : Type*} [Group G'] [TopologicalSpace G'] (P : CentralCovariantPair H α ω)
    (φ : ContinuousMonoidHom G' G) : (P.comp φ).pi = P.pi :=
  (rfl)

@[simp]
theorem comp_unitaryMap {G' : Type*} [Group G'] [TopologicalSpace G']
    (P : CentralCovariantPair H α ω) (φ : ContinuousMonoidHom G' G) (s' : G') :
    (P.comp φ).unitaryMap s' = P.unitaryMap (φ s') :=
  (rfl)

/-- A twisted covariant pair for the trivial cocycle `1` gives an untwisted
`CovariantRepresentation`, since `U_s U_t = U_{s * t}` when `ω = 1`. -/
def toCovariantRepresentation (P : CentralCovariantPair H α 1) :
    CovariantRepresentation α H where
  coefficient := P.pi
  group := .ofMonoidHom
    { toFun s := (P.unitaryMap s : H →L[ℂ] H)
      map_one' := by simp
      map_mul' s t := by simpa using (P.projective s t).symm }
  isUnitary := (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun s => (P.unitaryMap s).2
  continuous_orbit := P.strong_continuous
  covariance s a v := P.unitaryMap_apply_pi_apply s a v

@[simp]
theorem toCovariantRepresentation_coefficient (P : CentralCovariantPair H α 1) :
    P.toCovariantRepresentation.coefficient = P.pi :=
  (rfl)

@[simp]
theorem toCovariantRepresentation_group_apply (P : CentralCovariantPair H α 1) (s : G) :
    P.toCovariantRepresentation.group s = (P.unitaryMap s : H →L[ℂ] H) :=
  (rfl)

/-- Construct a twisted covariant pair for a scalar cocycle `CentralCocycle.scalar α c ...` from a
nondegenerate representation `π` and a strongly continuous `c`-projective unitary family `U`
satisfying `U s * U t = c s t • U (s * t)`. -/
def ofScalar (α : CStarAction G A) (c : G → G → unitary ℂ)
    (hone_left : ∀ s, c 1 s = 1) (hone_right : ∀ s, c s 1 = 1)
    (hcocycle : ∀ r s t, c s t * c r (s * t) = c r s * c (r * s) t)
    (hcont : Continuous (Function.uncurry c))
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate)
    (U : G → unitary (H →L[ℂ] H)) (hU1 : U 1 = 1)
    (hUcont : ∀ ξ : H, Continuous fun s => (U s : H →L[ℂ] H) ξ)
    (hcov : ∀ s a, (U s : H →L[ℂ] H) * π a * star (U s : H →L[ℂ] H) = π (α s a))
    (hproj : ∀ s t, U s * U t = c s t • U (s * t)) :
    CentralCovariantPair H α (CentralCocycle.scalar α c hone_left hone_right hcocycle hcont) where
  pi := π
  nondegenerate := hπ
  unitaryMap := U
  at_one := hU1
  strong_continuous := hUcont
  covariance := hcov
  projective s t := by
    have h := congrArg Subtype.val (hproj s t)
    rw [Submonoid.coe_mul, Unitary.coe_smul, Submonoid.smul_def] at h
    rw [h, CentralCocycle.scalar_value, Unitary.coe_smul, Submonoid.coe_one, Submonoid.smul_def,
      map_smul, map_one, smul_mul_assoc, one_mul]

@[simp]
theorem ofScalar_pi (α : CStarAction G A) (c : G → G → unitary ℂ)
    (hone_left : ∀ s, c 1 s = 1) (hone_right : ∀ s, c s 1 = 1)
    (hcocycle : ∀ r s t, c s t * c r (s * t) = c r s * c (r * s) t)
    (hcont : Continuous (Function.uncurry c))
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate)
    (U : G → unitary (H →L[ℂ] H)) (hU1 : U 1 = 1)
    (hUcont : ∀ ξ : H, Continuous fun s => (U s : H →L[ℂ] H) ξ)
    (hcov : ∀ s a, (U s : H →L[ℂ] H) * π a * star (U s : H →L[ℂ] H) = π (α s a))
    (hproj : ∀ s t, U s * U t = c s t • U (s * t)) :
    (ofScalar α c hone_left hone_right hcocycle hcont π hπ U hU1 hUcont hcov hproj).pi = π :=
  (rfl)

@[simp]
theorem ofScalar_unitaryMap (α : CStarAction G A) (c : G → G → unitary ℂ)
    (hone_left : ∀ s, c 1 s = 1) (hone_right : ∀ s, c s 1 = 1)
    (hcocycle : ∀ r s t, c s t * c r (s * t) = c r s * c (r * s) t)
    (hcont : Continuous (Function.uncurry c))
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate)
    (U : G → unitary (H →L[ℂ] H)) (hU1 : U 1 = 1)
    (hUcont : ∀ ξ : H, Continuous fun s => (U s : H →L[ℂ] H) ξ)
    (hcov : ∀ s a, (U s : H →L[ℂ] H) * π a * star (U s : H →L[ℂ] H) = π (α s a))
    (hproj : ∀ s t, U s * U t = c s t • U (s * t)) :
    (ofScalar α c hone_left hone_right hcocycle hcont π hπ U hU1 hUcont hcov hproj).unitaryMap =
      U :=
  (rfl)

/-! ### Vector-valued integrated form -/

section Integrated

variable [MeasurableSpace G] [OpensMeasurableSpace G] (P : CentralCovariantPair H α ω)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The Hilbert-space integrand of the integrated form is continuous. -/
@[fun_prop]
theorem continuous_integrand (f : C_c(G, A)) (v : H) :
    Continuous fun s => P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) v) :=
  (map_continuous P.pi |>.comp f.continuous).clm_apply (P.strong_continuous v)

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The Hilbert-space integrand vanishes outside the support of `f`. -/
theorem hasCompactSupport_integrand (f : C_c(G, A)) (v : H) :
    HasCompactSupport fun s => P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) v) :=
  f.hasCompactSupport.mono fun _ hg hzero => hg (by simp [hzero])

/-- Compact support makes every Hilbert-space integrand integrable. -/
theorem integrable_integrand (f : C_c(G, A)) (v : H) :
    Integrable (fun s => P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) v)) μ :=
  (P.continuous_integrand f v).integrable_of_hasCompactSupport (P.hasCompactSupport_integrand f v)

private theorem norm_integral_le (f : C_c(G, A)) (v : H) :
    ‖∫ s, P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) v) ∂μ‖ ≤ (∫ s, ‖f s‖ ∂μ) * ‖v‖ := by
  calc
    _ ≤ ∫ s, ‖f s‖ * ‖v‖ ∂μ := by
      refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun s => ?_)
      calc
        _ ≤ ‖P.pi (f s)‖ * ‖(P.unitaryMap s : H →L[ℂ] H) v‖ := (P.pi (f s)).le_opNorm _
        _ ≤ ‖f s‖ * ‖v‖ := by
          rw [Unitary.norm_map]
          exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- The vector-valued integrated form `v ↦ ∫ s, P.pi (f s) (U_s v) ∂μ` on `C_c(G, A)`. -/
def integratedOperator : C_c(G, A) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun f := LinearMap.mkContinuous
    { toFun v := ∫ s, P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) v) ∂μ
      map_add' v w := by
        simp_rw [map_add]
        exact integral_add (P.integrable_integrand μ f v) (P.integrable_integrand μ f w)
      map_smul' c v := by
        simp_rw [map_smul]
        exact integral_smul c _ }
    (∫ s, ‖f s‖ ∂μ) (P.norm_integral_le μ f)
  map_add' f g := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.add_apply, map_add,
      add_apply]
    exact integral_add (P.integrable_integrand μ f v) (P.integrable_integrand μ g v)
  map_smul' c f := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.smul_apply, map_smul,
      smul_apply, RingHom.id_apply]
    exact integral_smul c _

/-- Defining vector formula for `CentralCovariantPair.integratedOperator`. -/
theorem integratedOperator_apply (f : C_c(G, A)) (v : H) :
    P.integratedOperator μ f v = ∫ s, P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) v) ∂μ :=
  (rfl)

/-- The operator norm of `P.integratedOperator μ f` is bounded by `∫ s, ‖f s‖ ∂μ`. Neither
covariance nor the projective law is used in this estimate. -/
theorem norm_integratedOperator_le (f : C_c(G, A)) :
    ‖P.integratedOperator μ f‖ ≤ ∫ s, ‖f s‖ ∂μ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun v => ?_
  rw [integratedOperator_apply]
  exact P.norm_integral_le μ f v

/-- Matrix coefficients of `P.integratedOperator μ f` are integrals of pointwise matrix
coefficients. -/
theorem inner_integratedOperator_apply (f : C_c(G, A)) (w v : H) :
    ⟪w, P.integratedOperator μ f v⟫_ℂ =
      ∫ s, ⟪w, P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) v)⟫_ℂ ∂μ := by
  rw [integratedOperator_apply, integral_inner (P.integrable_integrand μ f v)]

/-- Left multiplication of `f` by `a : A` becomes left multiplication by `P.pi a`. -/
@[simp]
theorem integratedOperator_smul (a : A) (f : C_c(G, A)) :
    P.integratedOperator μ (a • f) = P.pi a * P.integratedOperator μ f := by
  ext v
  simp only [integratedOperator_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
    map_mul, mul_apply_eq_comp]
  exact (P.pi a).integral_comp_comm (P.integrable_integrand μ f v)

/-- A represented coefficient on the right moves inside the integral with the action twist. -/
theorem integratedOperator_pi_apply (f : C_c(G, A)) (a : A) (v : H) :
    P.integratedOperator μ f (P.pi a v) =
      ∫ s, P.pi (f s * α s a) ((P.unitaryMap s : H →L[ℂ] H) v) ∂μ := by
  rw [integratedOperator_apply]
  simp_rw [P.unitaryMap_apply_pi_apply, map_mul, mul_apply_eq_comp]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- Vector evaluation of `P.pi` commutes with Bochner integration. -/
theorem integral_pi_apply {X : Type*} [MeasurableSpace X] {ν : Measure X} {F : X → A}
    (hF : Integrable F ν) (w : H) :
    ∫ x, P.pi (F x) w ∂ν = P.pi (∫ x, F x ∂ν) w := by
  let L : A →L[ℂ] H := (ContinuousLinearMap.apply ℂ H w).comp
    { toLinearMap := (P.pi : A →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous _ }
  have hL (a : A) : L a = P.pi a w := rfl
  simpa only [hL] using L.integral_comp_comm hF

/-- For `ω = 1`, the integrated form agrees with `CovariantRepresentation.integratedOperator`. -/
@[simp]
theorem toCovariantRepresentation_integratedOperator (P : CentralCovariantPair H α 1) :
    P.toCovariantRepresentation.integratedOperator μ = P.integratedOperator μ := by
  ext f v
  simp [CovariantRepresentation.integratedOperator_apply, integratedOperator_apply]

/-! ### Multiplicativity and involution preservation -/

section Convolution

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Against a left-invariant measure, the integrated form of a twisted covariant pair is
multiplicative for cocycle-twisted convolution:
`P.integratedOperator μ (ω.convolution μ f g) =
  P.integratedOperator μ f * P.integratedOperator μ g`. -/
@[simp]
theorem integratedOperator_convolution (f g : C_c(G, A)) :
    P.integratedOperator μ (ω.convolution μ f g) =
      P.integratedOperator μ f * P.integratedOperator μ g := by
  ext v
  set Ψ : G → G → H := fun s r =>
    P.pi ((ω.value r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))))
      ((P.unitaryMap s : H →L[ℂ] H) v)
  have hcont : Continuous (Function.uncurry Ψ) := by
    rw [Function.uncurry_def]
    refine ((map_continuous P.pi).comp ?_).clm_apply ((P.strong_continuous v).comp continuous_fst)
    exact ω.continuous_snd_apply continuous_snd (continuous_snd.inv.mul continuous_fst)
      (by fun_prop)
  have hsupp : HasCompactSupport (Function.uncurry Ψ) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
      fun s r h => ⟨subset_tsupport _ fun hf => h (by simp [Ψ, hf]),
        subset_tsupport _ fun hg => h (by simp [Ψ, hg])⟩
  calc P.integratedOperator μ (ω.convolution μ f g) v
      = ∫ s, ∫ r, Ψ s r ∂μ ∂μ := by
        rw [integratedOperator_apply]
        congr 1 with s
        rw [CentralCocycle.convolution_apply,
          ← P.integral_pi_apply (ω.integrable_integrand μ f g s)]
    _ = ∫ r, ∫ s, Ψ s r ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hcont hsupp
    _ = ∫ r, (P.pi (f r) * (P.unitaryMap r : H →L[ℂ] H)) (P.integratedOperator μ g v) ∂μ := by
        congr 1 with r
        rw [← integral_mul_left_eq_self (Ψ · r) r, integratedOperator_apply,
          ← ContinuousLinearMap.integral_comp_comm _ (P.integrable_integrand μ g v)]
        congr 1 with t
        simpa [Ψ, mul_apply_eq_comp] using
          congr($((P.pi_mul_unitaryMap_mul r t (f r) (g t)).symm) v)
    _ = (P.integratedOperator μ f * P.integratedOperator μ g) v := by
        simp [integratedOperator_apply]

end Convolution

end Integrated

section Involution

variable [IsTopologicalGroup G] [LocallyCompactSpace G] (P : CentralCovariantPair H α ω)

/-- Operator-level adjoint identity behind `integratedOperator_involution`:
`π(f^{*_ω}(s)) U_s = c(s) • (π(f(s⁻¹)) U_{s⁻¹})*`. -/
theorem pi_involution_mul_unitaryMap (f : C_c(G, A)) (s : G) :
    P.pi (ω.involution f s) * (P.unitaryMap s : H →L[ℂ] H) =
      ((Measure.modularCharacter s : ℝ) : ℂ) •
        star (P.pi (f s⁻¹) * (P.unitaryMap s⁻¹ : H →L[ℂ] H)) := by
  rw [CentralCocycle.involution_apply, map_smul, smul_mul_assoc]
  congr 1
  rw [← P.pi.multiplierExtension_mul_eq_fst P.nondegenerate, mul_assoc, ← P.unitaryMap_mul_pi,
    ← mul_assoc, ← P.star_unitaryMap_inv, map_star, ← star_mul]

/-- Against any Haar measure, the integrated form of a twisted covariant pair sends the
cocycle-twisted involution `ω.involution` to the operator adjoint. -/
@[simp]
theorem integratedOperator_involution [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (f : C_c(G, A)) :
    P.integratedOperator μ (ω.involution f) = star (P.integratedOperator μ f) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v w => ?_
  rw [← inner_conj_symm _ w, P.inner_integratedOperator_apply,
    P.inner_integratedOperator_apply, ← integral_conj]
  calc
    (∫ s, starRingEnd ℂ ⟪w, P.pi (ω.involution f s) ((P.unitaryMap s : H →L[ℂ] H) v)⟫_ℂ ∂μ) =
        ∫ s, (Measure.modularCharacter s : ℝ) •
          ⟪v, P.pi (f s⁻¹) ((P.unitaryMap s⁻¹ : H →L[ℂ] H) w)⟫_ℂ ∂μ := by
      congr 1 with s
      rw [inner_conj_symm, ← mul_apply_eq_comp, P.pi_involution_mul_unitaryMap, smul_apply,
        inner_smul_left, Complex.conj_ofReal, ← Complex.real_smul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
        mul_apply_eq_comp]
    _ = ∫ s, ⟪v, P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) w)⟫_ℂ ∂μ :=
      integral_modularCharacter_smul_inv_eq_self (μ := μ)
        (f := fun s => ⟪v, P.pi (f s) ((P.unitaryMap s : H →L[ℂ] H) w)⟫_ℂ)
        (continuous_const.inner (P.continuous_integrand f w))
        ((P.hasCompactSupport_integrand f w).comp_left (inner_zero_right v))

end Involution

end CentralCovariantPair

/-- Multiplicativity of the vector-valued integrated form of a twisted covariant pair: for
compactly supported continuous `f` and `g` and a left-invariant measure finite on compacts (in
particular any left Haar measure), `T_{f *_ω g} ξ = T_f (T_g ξ)`, where
`T_f ξ = ∫ s, P.pi (f s) (U_s ξ) ∂μ`. -/
theorem centralIntegrated_twistedConvolution {G A H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
    [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (α : CStarAction G A) (ω : CentralCocycle α) (P : CentralCovariantPair H α ω)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (f g : C_c(G, A)) (ξ : H) :
    ∫ s, P.pi (twistedConvolution ω μ f g s) ((P.unitaryMap s : H →L[ℂ] H) ξ) ∂μ =
      ∫ r, P.pi (f r) ((P.unitaryMap r : H →L[ℂ] H)
        (∫ t, P.pi (g t) ((P.unitaryMap t : H →L[ℂ] H) ξ) ∂μ)) ∂μ := by
  have h := congr($(P.integratedOperator_convolution μ f g) ξ)
  simpa only [CentralCovariantPair.integratedOperator_apply, CentralCocycle.coe_convolution,
    mul_apply_eq_comp, Function.comp_apply] using h

namespace CovariantRepresentation

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {α : CStarAction G A}

/-- Every nondegenerate `CovariantRepresentation` defines a `CentralCovariantPair` for the trivial
cocycle `1`. -/
def toCentralCovariantPair (P : CovariantRepresentation α H) (hπ : P.coefficient.IsNondegenerate) :
    CentralCovariantPair H α 1 where
  pi := P.coefficient
  nondegenerate := hπ
  unitaryMap s := ⟨P.group s, P.isUnitary.mem_unitary s⟩
  at_one := Subtype.ext (map_one P.group)
  strong_continuous := P.continuous_orbit
  covariance s a := by
    rw [P.group_mul_coefficient, mul_assoc,
      Unitary.mul_star_self_of_mem (P.isUnitary.mem_unitary s), mul_one]
  projective s t := by simp [map_mul]

@[simp]
theorem toCentralCovariantPair_pi (P : CovariantRepresentation α H)
    (hπ : P.coefficient.IsNondegenerate) :
    (P.toCentralCovariantPair hπ).pi = P.coefficient :=
  (rfl)

@[simp]
theorem coe_toCentralCovariantPair_unitaryMap (P : CovariantRepresentation α H)
    (hπ : P.coefficient.IsNondegenerate) (s : G) :
    ((P.toCentralCovariantPair hπ).unitaryMap s : H →L[ℂ] H) = P.group s :=
  (rfl)

/-- Converting a nondegenerate `CovariantRepresentation` to a `CentralCovariantPair` at `ω = 1` and
back recovers `P`. -/
@[simp]
theorem toCovariantRepresentation_toCentralCovariantPair (P : CovariantRepresentation α H)
    (hπ : P.coefficient.IsNondegenerate) :
    (P.toCentralCovariantPair hπ).toCovariantRepresentation = P := by
  refine CovariantRepresentation.ext (by simp) ?_
  apply DFunLike.coe_injective
  funext s
  simp

/-- Viewing a nondegenerate `CovariantRepresentation` as a `CentralCovariantPair` at `ω = 1`
preserves its vector-valued integrated form. -/
@[simp]
theorem toCentralCovariantPair_integratedOperator [MeasurableSpace G] [OpensMeasurableSpace G]
    (P : CovariantRepresentation α H) (hπ : P.coefficient.IsNondegenerate)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] :
    (P.toCentralCovariantPair hπ).integratedOperator μ = P.integratedOperator μ := by
  ext f v
  simp [CentralCovariantPair.integratedOperator_apply,
    CovariantRepresentation.integratedOperator_apply]

end CovariantRepresentation

namespace CentralCovariantPair

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {α : CStarAction G A}

/-- Converting a `CentralCovariantPair` at `ω = 1` to a `CovariantRepresentation` and back recovers
`P`. -/
@[simp]
theorem toCentralCovariantPair_toCovariantRepresentation (P : CentralCovariantPair H α 1)
    (hπ : P.toCovariantRepresentation.coefficient.IsNondegenerate) :
    P.toCovariantRepresentation.toCentralCovariantPair hπ = P := by
  refine CentralCovariantPair.ext (by simp) ?_
  funext s
  apply Subtype.ext
  simp

end CentralCovariantPair

end TauCeti.CStarAction
