/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CentralCocycle.Algebra
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Star
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Twisted covariant pairs and their vector-valued integrated representations

For a point-norm continuous action `α` of a topological group `G` on a C⋆-algebra `A` and a
normalized continuous central multiplier cocycle `ω : CentralCocycle α`, a twisted covariant pair
(`CentralCovariantPair ω H`) on a complex Hilbert space `H` consists of:
* a nondegenerate representation `coefficient : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`,
* a strongly continuous unitary family `unitaryMap : G → unitary (H →L[ℂ] H)` with `U_1 = 1`,
* the covariance identity `U_s π(a) U_s* = π(α_s(a))`, and
* the projective law `U_s U_t = M(π)(ω(s, t)) U_{st}`, where
  `M(π) = coefficient.multiplierExtension isNondegenerate : 𝓜(ℂ, A) →⋆ₐ[ℂ] (H →L[ℂ] H)`.

For a compactly supported continuous function `f : C_c(G, A)`, the integrated form is defined by
the Hilbert-space vector integral

`(P.integratedOperator μ f) v = ∫ s, P.coefficient (f s) (P.unitaryMap s v) ∂μ`.

We prove:
* `norm_integratedOperator_le`: `‖P.integratedOperator μ f‖ ≤ ∫ s, ‖f s‖ ∂μ` for any measure
  finite on compact sets.
* `integratedOperator_twistedConvolution`: for a left-invariant measure, `P.integratedOperator μ`
  sends `ω.twistedConvolution μ f g` to `P.integratedOperator μ f * P.integratedOperator μ g`,
  combining covariance, the projective law, `mul_multiplierExtension_eq_snd`, compact-support
  Fubini, and left invariance.
* `integratedOperator_twistedInvolution`: for a Haar measure on a locally compact group,
  `P.integratedOperator μ (ω.twistedInvolution f) = star (P.integratedOperator μ f)`.
* Bundled contractive extensions `integratedOperatorCLM`, `integratedNonUnitalAlgHom`,
  `integratedStarAlgHom`, `integratedOperatorL1`, and
  `integratedStarAlgHomL1 : Completion (TwistedConvolutionAlgebra ω μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H)`.
* At `ω = 1`, `equivCovariantRepresentation` identifies `CentralCovariantPair 1 H` with
  nondegenerate `CovariantRepresentation α H`, preserving `integratedOperator`.

## References

* Judith A. Packer and Iain Raeburn, *Twisted crossed products of C*-algebras*, Math. Proc.
  Cambridge Philos. Soc. 106 (1989), 293–311, Section 2.
* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported CStarAlgebra InnerProductSpace MultiplierAlgebra

namespace TauCeti.CStarAction

variable {G A H : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A twisted covariant pair for a central multiplier cocycle `ω : CentralCocycle α` on a complex
Hilbert space `H`: a nondegenerate representation `π` of `A` together with a strongly continuous
unitary map `U : G → unitary (H →L[ℂ] H)` satisfying `U_1 = 1`, `U_s π(a) U_s* = π(α_s(a))`, and
`U_s U_t = M(π)(ω(s, t)) U_{st}`. -/
structure CentralCovariantPair {α : CStarAction G A} (ω : CentralCocycle α) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The coefficient representation of `A` on `H`. -/
  coefficient : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  /-- Nondegeneracy of the coefficient representation. -/
  isNondegenerate : coefficient.IsNondegenerate
  /-- The projective unitary family on `H`. -/
  unitaryMap : G → unitary (H →L[ℂ] H)
  /-- Normalization at the group identity. -/
  map_one' : unitaryMap 1 = 1
  /-- Strong continuity of every group orbit in `H`. -/
  continuous_orbit' : ∀ v : H, Continuous fun g => (unitaryMap g : H →L[ℂ] H) v
  /-- Covariance `U_g π(a) U_g* = π(α_g(a))`. -/
  covariance' : ∀ g (a : A),
    (unitaryMap g : H →L[ℂ] H) * coefficient a * star (unitaryMap g : H →L[ℂ] H) =
      coefficient (α g a)
  /-- Projective multiplication law `U_s U_t = M(π)(ω(s, t)) U_{st}`. -/
  mul_projective' : ∀ s t,
    (unitaryMap s : H →L[ℂ] H) * (unitaryMap t : H →L[ℂ] H) =
      coefficient.multiplierExtension isNondegenerate (ω s t : 𝓜(ℂ, A)) *
        (unitaryMap (s * t) : H →L[ℂ] H)

namespace CentralCovariantPair

variable {α : CStarAction G A} {ω : CentralCocycle α} (P : CentralCovariantPair ω H)

/-- The coefficient representation and unitary family determine a twisted covariant pair. -/
@[ext]
theorem ext {P Q : CentralCovariantPair ω H}
    (hπ : P.coefficient = Q.coefficient) (hU : P.unitaryMap = Q.unitaryMap) : P = Q := by
  cases P
  cases Q
  cases hπ
  cases hU
  rfl

@[simp]
theorem unitaryMap_one : P.unitaryMap 1 = 1 :=
  P.map_one'

theorem coe_unitaryMap_one : (P.unitaryMap 1 : H →L[ℂ] H) = 1 := by
  simp

/-- Strong continuity of each orbit `g ↦ U_g v`. -/
@[fun_prop]
theorem continuous_orbit (v : H) : Continuous fun g => (P.unitaryMap g : H →L[ℂ] H) v :=
  P.continuous_orbit' v

/-- Covariance in conjugation form: `U_g π(a) U_g* = π(α_g(a))`. -/
theorem covariance_conj (g : G) (a : A) :
    (P.unitaryMap g : H →L[ℂ] H) * P.coefficient a * star (P.unitaryMap g : H →L[ℂ] H) =
      P.coefficient (α g a) :=
  P.covariance' g a

/-- Covariance in intertwining form: `U_g * π(a) = π(α_g(a)) * U_g`. -/
@[simp]
theorem unitaryMap_mul_coefficient (g : G) (a : A) :
    (P.unitaryMap g : H →L[ℂ] H) * P.coefficient a =
      P.coefficient (α g a) * (P.unitaryMap g : H →L[ℂ] H) := by
  calc (P.unitaryMap g : H →L[ℂ] H) * P.coefficient a
      = ((P.unitaryMap g : H →L[ℂ] H) * P.coefficient a *
          star (P.unitaryMap g : H →L[ℂ] H)) * (P.unitaryMap g : H →L[ℂ] H) := by
        rw [mul_assoc (_ * _), (Unitary.mem_iff.mp (P.unitaryMap g).prop).1, mul_one]
    _ = P.coefficient (α g a) * (P.unitaryMap g : H →L[ℂ] H) := by
        rw [P.covariance_conj]

/-- Vector form of covariance: `U_g (π(a) v) = π(α_g(a)) (U_g v)`. -/
theorem covariance_apply (g : G) (a : A) (v : H) :
    (P.unitaryMap g : H →L[ℂ] H) (P.coefficient a v) =
      P.coefficient (α g a) ((P.unitaryMap g : H →L[ℂ] H) v) :=
  congr($(P.unitaryMap_mul_coefficient g a) v)

/-- The projective multiplication law `U_s * U_t = M(π)(ω(s, t)) * U_{st}`. -/
theorem mul_projective (s t : G) :
    (P.unitaryMap s : H →L[ℂ] H) * (P.unitaryMap t : H →L[ℂ] H) =
      P.coefficient.multiplierExtension P.isNondegenerate (ω s t : 𝓜(ℂ, A)) *
        (P.unitaryMap (s * t) : H →L[ℂ] H) :=
  P.mul_projective' s t

/-- Moving `U_g` across the inner product yields `star U_g` on the right. -/
theorem inner_unitaryMap_left (g : G) (v w : H) :
    ⟪(P.unitaryMap g : H →L[ℂ] H) v, w⟫_ℂ =
      ⟪v, (star (P.unitaryMap g : H →L[ℂ] H)) w⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- Each operator `U_g` preserves the Hilbert-space inner product. -/
@[simp]
theorem inner_unitaryMap_self (g : G) (v w : H) :
    ⟪(P.unitaryMap g : H →L[ℂ] H) v, (P.unitaryMap g : H →L[ℂ] H) w⟫_ℂ = ⟪v, w⟫_ℂ := by
  rw [P.inner_unitaryMap_left, ← mul_apply_eq_comp,
    (Unitary.mem_iff.mp (P.unitaryMap g).prop).1, one_apply_eq_self]

/-- Each operator `U_g` is an isometry on `H`. -/
@[simp]
theorem norm_unitaryMap_apply (g : G) (v : H) :
    ‖(P.unitaryMap g : H →L[ℂ] H) v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) ((P.unitaryMap g : H →L[ℂ] H) v),
    norm_eq_sqrt_re_inner (𝕜 := ℂ) v, P.inner_unitaryMap_self]

/-- Inverse formula for the projective unitary family: `U_{g⁻¹} = U_g* M(π)(ω(g, g⁻¹))`. -/
theorem unitaryMap_inv_eq (g : G) :
    (P.unitaryMap g⁻¹ : H →L[ℂ] H) =
      star (P.unitaryMap g : H →L[ℂ] H) *
        P.coefficient.multiplierExtension P.isNondegenerate (ω g g⁻¹ : 𝓜(ℂ, A)) := by
  have hproj := P.mul_projective g g⁻¹
  rw [mul_inv_cancel, P.coe_unitaryMap_one, mul_one] at hproj
  calc (P.unitaryMap g⁻¹ : H →L[ℂ] H)
      = (star (P.unitaryMap g : H →L[ℂ] H) * (P.unitaryMap g : H →L[ℂ] H)) *
          (P.unitaryMap g⁻¹ : H →L[ℂ] H) := by
        rw [(Unitary.mem_iff.mp (P.unitaryMap g).prop).1, one_mul]
    _ = star (P.unitaryMap g : H →L[ℂ] H) *
          P.coefficient.multiplierExtension P.isNondegenerate (ω g g⁻¹ : 𝓜(ℂ, A)) := by
        rw [mul_assoc, hproj]

/-- Adjoint formula for `U_{g⁻¹}`: `(U_{g⁻¹})* = M(π)(ω(g, g⁻¹)*) * U_g`. -/
theorem star_unitaryMap_inv_eq (g : G) :
    star (P.unitaryMap g⁻¹ : H →L[ℂ] H) =
      P.coefficient.multiplierExtension P.isNondegenerate (star (ω g g⁻¹ : 𝓜(ℂ, A))) *
        (P.unitaryMap g : H →L[ℂ] H) := by
  rw [P.unitaryMap_inv_eq, star_mul, star_star, map_star]

/-- Key operator identity combining covariance, the projective law, and
`mul_multiplierExtension_eq_snd`:
`π(a) U_r π(b) U_t = π((ω r t).snd (a * α_r(b))) U_{r * t}`. -/
theorem coefficient_mul_unitaryMap_mul (a b : A) (r t : G) :
    P.coefficient a * (P.unitaryMap r : H →L[ℂ] H) *
        (P.coefficient b * (P.unitaryMap t : H →L[ℂ] H)) =
      P.coefficient ((ω r t : 𝓜(ℂ, A)).snd (a * α r b)) *
        (P.unitaryMap (r * t) : H →L[ℂ] H) := by
  calc P.coefficient a * (P.unitaryMap r : H →L[ℂ] H) *
          (P.coefficient b * (P.unitaryMap t : H →L[ℂ] H))
      = P.coefficient a * ((P.unitaryMap r : H →L[ℂ] H) * P.coefficient b) *
          (P.unitaryMap t : H →L[ℂ] H) := by simp only [mul_assoc]
    _ = (P.coefficient a * P.coefficient (α r b)) *
          ((P.unitaryMap r : H →L[ℂ] H) * (P.unitaryMap t : H →L[ℂ] H)) := by
        rw [P.unitaryMap_mul_coefficient]
        simp only [mul_assoc]
    _ = (P.coefficient (a * α r b) *
          P.coefficient.multiplierExtension P.isNondegenerate (ω r t : 𝓜(ℂ, A))) *
          (P.unitaryMap (r * t) : H →L[ℂ] H) := by
        rw [← map_mul, P.mul_projective, mul_assoc]
    _ = P.coefficient ((ω r t : 𝓜(ℂ, A)).snd (a * α r b)) *
          (P.unitaryMap (r * t) : H →L[ℂ] H) := by
        rw [NonUnitalStarAlgHom.mul_multiplierExtension_eq_snd]

/-! ### Vector-valued integrated form -/

section Integrated

variable [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The vector integrand `g ↦ π(f g) (U_g v)` is continuous. -/
@[fun_prop]
theorem continuous_integrand (f : C_c(G, A)) (v : H) :
    Continuous fun g => P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v) :=
  ((map_continuous P.coefficient).comp f.continuous).clm_apply (P.continuous_orbit v)

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The vector integrand vanishes outside the support of `f`. -/
theorem hasCompactSupport_integrand (f : C_c(G, A)) (v : H) :
    HasCompactSupport fun g => P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v) :=
  f.hasCompactSupport.mono fun _ hg hz => hg (by simp [hz])

/-- Compact support makes every vector integrand integrable against `μ`. -/
theorem integrable_integrand (f : C_c(G, A)) (v : H) :
    Integrable (fun g => P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v)) μ :=
  (P.continuous_integrand f v).integrable_of_hasCompactSupport (P.hasCompactSupport_integrand f v)

private theorem norm_integral_le (f : C_c(G, A)) (v : H) :
    ‖∫ g, P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ‖ ≤
      (∫ g, ‖f g‖ ∂μ) * ‖v‖ := by
  calc ‖∫ g, P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ‖
      ≤ ∫ g, ‖f g‖ * ‖v‖ ∂μ := by
        refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun g => ?_)
        calc ‖P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v)‖
            ≤ ‖P.coefficient (f g)‖ * ‖(P.unitaryMap g : H →L[ℂ] H) v‖ :=
              (P.coefficient (f g)).le_opNorm _
          _ ≤ ‖f g‖ * ‖v‖ := by
              rw [P.norm_unitaryMap_apply]
              exact mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _)
                (norm_nonneg _)
    _ = (∫ g, ‖f g‖ ∂μ) * ‖v‖ := integral_mul_const _ _

/-- The vector-valued integrated form on `C_c(G, A)`, sending `f` to the bounded operator
`v ↦ ∫ g, π(f g) (U_g v) ∂μ`. -/
def integratedOperator : C_c(G, A) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun f := LinearMap.mkContinuous
    { toFun v := ∫ g, P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ
      map_add' v w := by
        simp_rw [map_add]
        exact integral_add (P.integrable_integrand μ f v) (P.integrable_integrand μ f w)
      map_smul' c v := by
        simp_rw [map_smul]
        exact integral_smul c _ }
    (∫ g, ‖f g‖ ∂μ) (P.norm_integral_le μ f)
  map_add' f h := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.add_apply, map_add,
      add_apply]
    exact integral_add (P.integrable_integrand μ f v) (P.integrable_integrand μ h v)
  map_smul' c f := by
    ext v
    simp only [LinearMap.mkContinuous_apply, CompactlySupportedContinuousMap.smul_apply, map_smul,
      smul_apply, RingHom.id_apply]
    exact integral_smul c _

/-- Defining vector formula for `P.integratedOperator μ f`. -/
theorem integratedOperator_apply (f : C_c(G, A)) (v : H) :
    P.integratedOperator μ f v =
      ∫ g, P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v) ∂μ :=
  (rfl)

/-- The operator norm of `P.integratedOperator μ f` is bounded by the `L¹` norm of `f`. -/
theorem norm_integratedOperator_le (f : C_c(G, A)) :
    ‖P.integratedOperator μ f‖ ≤ ∫ g, ‖f g‖ ∂μ :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
    (P.norm_integral_le μ f)

/-- Matrix coefficients of `P.integratedOperator μ f` are integrals of vector matrix
coefficients. -/
theorem inner_integratedOperator_apply (f : C_c(G, A)) (w v : H) :
    ⟪w, P.integratedOperator μ f v⟫_ℂ =
      ∫ g, ⟪w, P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) v)⟫_ℂ ∂μ := by
  rw [integratedOperator_apply, integral_inner (P.integrable_integrand μ f v)]

/-- Left multiplication by a coefficient in `A` goes to left multiplication by `P.coefficient a`. -/
@[simp]
theorem integratedOperator_smul (a : A) (f : C_c(G, A)) :
    P.integratedOperator μ (a • f) = P.coefficient a * P.integratedOperator μ f := by
  ext v
  simp only [integratedOperator_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
    map_mul, mul_apply_eq_comp]
  exact (P.coefficient a).integral_comp_comm (P.integrable_integrand μ f v)

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- Vector evaluation of `P.coefficient` commutes with Bochner integration. -/
theorem integral_coefficient_apply {X : Type*} [MeasurableSpace X] {ν : Measure X} {F : X → A}
    (hF : Integrable F ν) (w : H) :
    ∫ x, P.coefficient (F x) w ∂ν = P.coefficient (∫ x, F x ∂ν) w := by
  let L : A →L[ℂ] H := (ContinuousLinearMap.apply ℂ H w).comp
    { toLinearMap := (P.coefficient : A →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous _ }
  have hL (a : A) : L a = P.coefficient a w := rfl
  simpa only [hL] using L.integral_comp_comm hF

/-- The integrated form bundled as a contractive continuous linear map on
`TwistedConvolutionAlgebra ω μ`. -/
def integratedOperatorCLM : TwistedConvolutionAlgebra ω μ →L[ℂ] (H →L[ℂ] H) :=
  ((P.integratedOperator μ).comp
      (TwistedConvolutionAlgebra.linearEquiv ω μ).toLinearMap).mkContinuous
    1 fun f => by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        TwistedConvolutionAlgebra.linearEquiv_apply, one_mul,
        TwistedConvolutionAlgebra.norm_eq_integral_norm] using
        P.norm_integratedOperator_le μ f.ofConv

@[simp]
theorem integratedOperatorCLM_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorCLM μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedOperatorCLM]

theorem norm_integratedOperatorCLM_le : ‖P.integratedOperatorCLM μ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simpa only [integratedOperatorCLM_apply, one_mul,
    TwistedConvolutionAlgebra.norm_eq_integral_norm] using
    P.norm_integratedOperator_le μ f.ofConv

/-! ### Multiplicativity under cocycle-twisted convolution -/

section Multiplication

variable [IsTopologicalGroup G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The integrated form of a twisted covariant pair is multiplicative for `ω`-twisted convolution
with respect to a left-invariant measure: `(π ⋊ U)(f *_ω g) = (π ⋊ U)(f) * (π ⋊ U)(g)`. -/
@[simp]
theorem integratedOperator_twistedConvolution (f g : C_c(G, A)) :
    P.integratedOperator μ (ω.twistedConvolution μ f g) =
      P.integratedOperator μ f * P.integratedOperator μ g := by
  ext v
  set Ψ : G → G → H := fun s r =>
    P.coefficient ((ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s))))
      ((P.unitaryMap s : H →L[ℂ] H) v)
  have hcont_coeff : Continuous (Function.uncurry fun s r =>
      (ω r (r⁻¹ * s) : 𝓜(ℂ, A)).snd (f r * α r (g (r⁻¹ * s)))) := by
    rw [Function.uncurry_def]
    exact ω.continuous_snd_apply _root_.continuous_snd
      (_root_.continuous_snd.inv.mul _root_.continuous_fst) (by fun_prop)
  have hcont : Continuous (Function.uncurry Ψ) := by
    rw [Function.uncurry_def]
    exact ((map_continuous P.coefficient).comp hcont_coeff).clm_apply
      ((P.continuous_orbit v).comp _root_.continuous_fst)
  have hsupp : HasCompactSupport (Function.uncurry Ψ) :=
    hasCompactSupport_uncurry_of_inv_mul_mem f.hasCompactSupport g.hasCompactSupport
      fun s r h => ⟨subset_tsupport _ fun hf => h (by simp [Ψ, hf]),
        subset_tsupport _ fun hg => h (by simp [Ψ, hg])⟩
  calc P.integratedOperator μ (ω.twistedConvolution μ f g) v
      = ∫ s, ∫ r, Ψ s r ∂μ ∂μ := by
        rw [integratedOperator_apply]
        congr 1 with s
        rw [CentralCocycle.twistedConvolution_apply,
          ← P.integral_coefficient_apply (ω.integrable_twistedIntegrand f g μ s)]
    _ = ∫ r, ∫ s, Ψ s r ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hcont hsupp
    _ = ∫ r, (P.coefficient (f r) * (P.unitaryMap r : H →L[ℂ] H))
          (P.integratedOperator μ g v) ∂μ := by
        congr 1 with r
        rw [← integral_mul_left_eq_self (Ψ · r) r, integratedOperator_apply,
          ← ContinuousLinearMap.integral_comp_comm _ (P.integrable_integrand μ g v)]
        congr 1 with t
        have hop := congr($(P.coefficient_mul_unitaryMap_mul (f r) (g t) r t) v)
        simpa only [Ψ, inv_mul_cancel_left, mul_apply_eq_comp] using hop.symm
    _ = (P.integratedOperator μ f * P.integratedOperator μ g) v := by
        simp [integratedOperator_apply]

/-- The integrated form as a nonunital algebra homomorphism on `TwistedConvolutionAlgebra ω μ`. -/
def integratedNonUnitalAlgHom : TwistedConvolutionAlgebra ω μ →ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integratedOperatorCLM μ
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' f g := by simp

@[simp]
theorem integratedNonUnitalAlgHom_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedNonUnitalAlgHom μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedNonUnitalAlgHom]

@[fun_prop]
theorem continuous_integratedNonUnitalAlgHom : Continuous (P.integratedNonUnitalAlgHom μ) :=
  (P.integratedOperatorCLM μ).continuous

/-- Extension by continuity of the integrated form to the cocycle-twisted `L¹` Banach algebra
`Completion (TwistedConvolutionAlgebra ω μ)`. -/
def integratedOperatorL1 :
    Completion (TwistedConvolutionAlgebra ω μ) →ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := (P.integratedOperatorCLM μ).fromCompletion
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f g => simp only [← Completion.coe_mul', ContinuousLinearMap.fromCompletion_apply_coe,
        integratedOperatorCLM_apply, TwistedConvolutionAlgebra.ofConv_mul,
        integratedOperator_twistedConvolution]

@[simp]
theorem integratedOperatorL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedOperatorL1 μ f = P.integratedOperator μ f.ofConv := by
  simp [integratedOperatorL1]

@[fun_prop]
theorem continuous_integratedOperatorL1 : Continuous (P.integratedOperatorL1 μ) :=
  (P.integratedOperatorCLM μ).fromCompletion.continuous

theorem norm_integratedOperatorL1_le (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    ‖P.integratedOperatorL1 μ x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih f =>
    simpa only [integratedOperatorL1_coe, Completion.norm_coe, one_mul,
      integratedOperatorCLM_apply] using (P.integratedOperatorCLM μ).le_of_opNorm_le
        (P.norm_integratedOperatorCLM_le μ) f

end Multiplication

end Integrated

/-! ### Star preservation under cocycle-twisted involution -/

section Star

variable [MeasurableSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The vector-valued integrated form sends `ω.twistedInvolution f` to the operator adjoint
`star (P.integratedOperator μ f)`. -/
@[simp]
theorem integratedOperator_twistedInvolution (f : C_c(G, A)) :
    P.integratedOperator μ (ω.twistedInvolution f) = star (P.integratedOperator μ f) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v w => ?_
  rw [← inner_conj_symm _ w, P.inner_integratedOperator_apply,
    P.inner_integratedOperator_apply, ← integral_conj]
  have hop (g : G) :
      P.coefficient ((star (ω g g⁻¹ : 𝓜(ℂ, A))).fst (α g (star (f g⁻¹)))) *
          (P.unitaryMap g : H →L[ℂ] H) =
        star (P.coefficient (f g⁻¹) * (P.unitaryMap g⁻¹ : H →L[ℂ] H)) := by
    calc P.coefficient ((star (ω g g⁻¹ : 𝓜(ℂ, A))).fst (α g (star (f g⁻¹)))) *
            (P.unitaryMap g : H →L[ℂ] H)
        = P.coefficient.multiplierExtension P.isNondegenerate (star (ω g g⁻¹ : 𝓜(ℂ, A))) *
            (P.coefficient (α g (star (f g⁻¹))) * (P.unitaryMap g : H →L[ℂ] H)) := by
          rw [← NonUnitalStarAlgHom.multiplierExtension_mul_eq_fst P.isNondegenerate, mul_assoc]
      _ = (P.coefficient.multiplierExtension P.isNondegenerate (star (ω g g⁻¹ : 𝓜(ℂ, A))) *
            (P.unitaryMap g : H →L[ℂ] H)) * star (P.coefficient (f g⁻¹)) := by
          rw [← P.unitaryMap_mul_coefficient, map_star P.coefficient, mul_assoc]
      _ = star (P.unitaryMap g⁻¹ : H →L[ℂ] H) * star (P.coefficient (f g⁻¹)) := by
          rw [P.star_unitaryMap_inv_eq]
      _ = star (P.coefficient (f g⁻¹) * (P.unitaryMap g⁻¹ : H →L[ℂ] H)) := (star_mul _ _).symm
  calc (∫ g, starRingEnd ℂ
          ⟪w, P.coefficient (ω.twistedInvolution f g) ((P.unitaryMap g : H →L[ℂ] H) v)⟫_ℂ ∂μ)
      = ∫ g, (Measure.modularCharacter g : ℝ) •
          ⟪v, P.coefficient (f g⁻¹) ((P.unitaryMap g⁻¹ : H →L[ℂ] H) w)⟫_ℂ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        rw [inner_conj_symm]
        calc ⟪P.coefficient (ω.twistedInvolution f g) ((P.unitaryMap g : H →L[ℂ] H) v), w⟫_ℂ
            = (Measure.modularCharacter g : ℝ) •
                ⟪(P.coefficient ((star (ω g g⁻¹ : 𝓜(ℂ, A))).fst (α g (star (f g⁻¹)))) *
                  (P.unitaryMap g : H →L[ℂ] H)) v, w⟫_ℂ := by
              simp only [CentralCocycle.twistedInvolution_apply, map_smul, smul_apply,
                mul_apply_eq_comp]
              exact inner_smul_real_left _ _ _
          _ = (Measure.modularCharacter g : ℝ) •
                ⟪(star (P.coefficient (f g⁻¹) * (P.unitaryMap g⁻¹ : H →L[ℂ] H))) v, w⟫_ℂ := by
              rw [hop g]
          _ = (Measure.modularCharacter g : ℝ) •
                ⟪v, P.coefficient (f g⁻¹) ((P.unitaryMap g⁻¹ : H →L[ℂ] H) w)⟫_ℂ := by
              rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
                mul_apply_eq_comp]
    _ = ∫ g, ⟪v, P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) w)⟫_ℂ ∂μ :=
        integral_modularCharacter_smul_inv_eq_self (μ := μ)
          (f := fun g => ⟪v, P.coefficient (f g) ((P.unitaryMap g : H →L[ℂ] H) w)⟫_ℂ)
          (continuous_const.inner (P.continuous_integrand f w))
          ((P.hasCompactSupport_integrand f w).comp_left (inner_zero_right v))

/-- The integrated form as a nonunital complex ⋆-algebra homomorphism on
`TwistedConvolutionAlgebra ω μ`. -/
def integratedStarAlgHom : TwistedConvolutionAlgebra ω μ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun f := P.integratedOperator μ f.ofConv
  map_zero' := by simp
  map_add' f g := by simp
  map_mul' f g := by simp
  map_smul' c f := by simp
  map_star' f := by simp

@[simp]
theorem integratedStarAlgHom_apply (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedStarAlgHom μ f = P.integratedOperator μ f.ofConv :=
  (rfl)

theorem norm_integratedStarAlgHom_le_norm (f : TwistedConvolutionAlgebra ω μ) :
    ‖P.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  simpa [TwistedConvolutionAlgebra.norm_eq_integral_norm] using
    P.norm_integratedOperator_le μ f.ofConv

/-- Extension by continuity of the integrated ⋆-representation to the cocycle-twisted `L¹` Banach
⋆-algebra `Completion (TwistedConvolutionAlgebra ω μ)`. -/
def integratedStarAlgHomL1 :
    Completion (TwistedConvolutionAlgebra ω μ) →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integratedOperatorL1 μ
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := map_mul _
  map_star' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih f => simp only [← Completion.coe_star, integratedOperatorL1_coe,
        TwistedConvolutionAlgebra.ofConv_star, integratedOperator_twistedInvolution]

@[simp]
theorem integratedStarAlgHomL1_coe (f : TwistedConvolutionAlgebra ω μ) :
    P.integratedStarAlgHomL1 μ f = P.integratedOperator μ f.ofConv :=
  P.integratedOperatorL1_coe μ f

@[fun_prop]
theorem continuous_integratedStarAlgHomL1 : Continuous (P.integratedStarAlgHomL1 μ) :=
  P.continuous_integratedOperatorL1 μ

theorem norm_integratedStarAlgHomL1_le (x : Completion (TwistedConvolutionAlgebra ω μ)) :
    ‖P.integratedStarAlgHomL1 μ x‖ ≤ ‖x‖ :=
  P.norm_integratedOperatorL1_le μ x

end Star

/-! ### Comparison with untwisted covariant representations at `ω = 1` -/

section Untwisted

/-- Turn a `CentralCovariantPair` for the trivial cocycle `1` into an untwisted
`CovariantRepresentation`. -/
def toCovariantRepresentation (P : CentralCovariantPair (1 : CentralCocycle α) H) :
    CovariantRepresentation α H where
  coefficient := P.coefficient
  group :=
    { toMonoidHom :=
        { toFun g := (P.unitaryMap g : H →L[ℂ] H)
          map_one' := P.coe_unitaryMap_one
          map_mul' s t := by simpa using (P.mul_projective s t).symm } }
  isUnitary := (ContRepresentation.isUnitary_iff_norm_map _).mpr P.norm_unitaryMap_apply
  continuous_orbit := P.continuous_orbit
  covariance g a v := P.covariance_apply g a v

@[simp]
theorem toCovariantRepresentation_coefficient (P : CentralCovariantPair (1 : CentralCocycle α) H) :
    P.toCovariantRepresentation.coefficient = P.coefficient :=
  (rfl)

@[simp]
theorem toCovariantRepresentation_group_apply
    (P : CentralCovariantPair (1 : CentralCocycle α) H) (g : G) :
    P.toCovariantRepresentation.group g = (P.unitaryMap g : H →L[ℂ] H) :=
  (rfl)

/-- Turn a nondegenerate `CovariantRepresentation` into a `CentralCovariantPair` for the trivial
cocycle `1`. -/
def ofCovariantRepresentation (Q : CovariantRepresentation α H)
    (hQ : Q.coefficient.IsNondegenerate) : CentralCovariantPair (1 : CentralCocycle α) H where
  coefficient := Q.coefficient
  isNondegenerate := hQ
  unitaryMap g := ⟨Q.group g, Q.isUnitary.mem_unitary g⟩
  map_one' := Subtype.ext (map_one Q.group)
  continuous_orbit' := Q.continuous_orbit
  covariance' g a := by
    rw [ContinuousLinearMap.star_eq_adjoint, Q.isUnitary.adjoint_eq_inv, ← Q.coefficient_action]
  mul_projective' s t := by simp [← map_mul]

@[simp]
theorem ofCovariantRepresentation_coefficient (Q : CovariantRepresentation α H)
    (hQ : Q.coefficient.IsNondegenerate) :
    (ofCovariantRepresentation Q hQ).coefficient = Q.coefficient :=
  (rfl)

@[simp]
theorem coe_ofCovariantRepresentation_unitaryMap (Q : CovariantRepresentation α H)
    (hQ : Q.coefficient.IsNondegenerate) (g : G) :
    ((ofCovariantRepresentation Q hQ).unitaryMap g : H →L[ℂ] H) = Q.group g :=
  (rfl)

/-- `CentralCovariantPair 1 H` is canonically equivalent to nondegenerate
`CovariantRepresentation α H`. -/
def equivCovariantRepresentation :
    CentralCovariantPair (1 : CentralCocycle α) H ≃
      {Q : CovariantRepresentation α H // Q.coefficient.IsNondegenerate} where
  toFun P := ⟨P.toCovariantRepresentation, P.isNondegenerate⟩
  invFun Q := ofCovariantRepresentation Q.1 Q.2
  left_inv _ := ext rfl (funext fun _ => Subtype.ext rfl)
  right_inv _ := Subtype.ext <| CovariantRepresentation.ext rfl (DFunLike.ext _ _ fun _ => rfl)

@[simp]
theorem toCovariantRepresentation_integratedOperator [MeasurableSpace G] [OpensMeasurableSpace G]
    (P : CentralCovariantPair (1 : CentralCocycle α) H) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] :
    P.toCovariantRepresentation.integratedOperator μ = P.integratedOperator μ := by
  ext f v
  rw [CovariantRepresentation.integratedOperator_apply, integratedOperator_apply]
  rfl

@[simp]
theorem ofCovariantRepresentation_integratedOperator [MeasurableSpace G] [OpensMeasurableSpace G]
    (Q : CovariantRepresentation α H) (hQ : Q.coefficient.IsNondegenerate) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] :
    (ofCovariantRepresentation Q hQ).integratedOperator μ = Q.integratedOperator μ := by
  rw [← toCovariantRepresentation_integratedOperator]
  rfl

end Untwisted

end CentralCovariantPair

end TauCeti.CStarAction
