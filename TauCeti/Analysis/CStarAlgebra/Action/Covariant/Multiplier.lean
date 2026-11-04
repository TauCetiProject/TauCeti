/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Comap
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Representation.GNS
import TauCeti.MeasureTheory.Integral.PeakFunction

/-!
# Multiplier-valued covariant homomorphisms and their integrated forms

A *covariant multiplier homomorphism* of a C⋆-dynamical system `(A, G, α)` into a possibly
nonunital C⋆-algebra `B` consists of a ⋆-homomorphism `π : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` and a group
homomorphism `u : G →* unitary 𝓜(ℂ, B)` whose left centralizers have norm-continuous orbits
`r ↦ u_r b` for every `b : B` and which satisfy `u_r π(a) = π(α_r(a)) u_r`. On a topological group,
right strict continuity `r ↦ b u_r` follows automatically from left strict continuity by taking
adjoints.

Composing `(π, u)` with the multiplier extension of any nondegenerate Hilbert-space representation
`ρ` of `B` yields a Hilbert-space `CovariantRepresentation`, and composing with the multiplier
extension of any nondegenerate `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)` pushes `(π, u)` forward to `C`.

For a measure `μ` finite on compact sets, every `f : C_c(G, A)` integrates strictly to a multiplier
`CovariantMultiplierHom.integratedMultiplier` acting by the Bochner integrals
`b ↦ ∫ r, (π(f r) u_r).fst b ∂μ` and `b ↦ ∫ r, (π(f r) u_r).snd b ∂μ` in `B`. Every nondegenerate
Hilbert-space representation of `B` sends this multiplier to the vector-valued integrated operator
of the induced covariant representation. Since nondegenerate representations separate points of
`𝓜(ℂ, B)` (`DoubleCentralizer.eq_iff_forall_multiplierExtension_eq`), multiplicativity under
twisted convolution, preservation of the twisted involution on a Haar measure, and functoriality
under nondegenerate multiplier homomorphisms transfer directly from the Hilbert-space theory.

Peak-function approximation at any group element `r₀` shows that the integrated multipliers
generate the same closed essential subspace of `B` as `π`, and that nondegenerate covariant
multiplier homomorphisms (as well as nondegenerate Hilbert-space covariant representations) are
uniquely determined by their integrated forms.

## Main definitions

* `TauCeti.CStarAction.CovariantMultiplierHom`: covariant homomorphisms into `𝓜(ℂ, B)`.
* `TauCeti.CStarAction.CovariantMultiplierHom.toCovariantRepresentation`: transport to a
  Hilbert-space covariant representation along a nondegenerate representation of `B`.
* `TauCeti.CStarAction.CovariantMultiplierHom.map` and
  `TauCeti.CStarAction.CovariantMultiplierHom.comap`: pushforward along a nondegenerate multiplier
  homomorphism and pullback along an equivariant coefficient homomorphism.
* `TauCeti.CStarAction.CovariantMultiplierHom.integratedMultiplier` and
  `TauCeti.CStarAction.CovariantMultiplierHom.integratedStarAlgHom`: the strict Bochner integrated
  form on `C_c(G, A)` and as a ⋆-homomorphism on `ConvolutionAlgebra α μ`.

## Main statements

* `TauCeti.CStarAction.CovariantMultiplierHom.multiplierExtension_integratedMultiplier`:
  compatibility with Hilbert-space vector integration.
* `TauCeti.CStarAction.CovariantMultiplierHom.topologicalClosure_span_integratedMultiplier` and
  `TauCeti.CStarAction.CovariantMultiplierHom.dense_span_integratedMultiplier_iff`: preservation
  and reflection of multiplier nondegeneracy.
* `TauCeti.CStarAction.CovariantMultiplierHom.eq_of_integratedMultiplier_eq` and
  `TauCeti.CStarAction.CovariantRepresentation.eq_of_integratedOperator_eq`: uniqueness of
  nondegenerate covariant pairs from their integrated forms.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, Proposition 2.39 and Corollary 2.40.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped CompactlySupported CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction

section Basic

variable {G A B C : Type*} [Group G] [TopologicalSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- A covariant homomorphism from a C⋆-dynamical system `(A, G, α)` into the multiplier algebra of
a possibly nonunital C⋆-algebra `B`. Coefficient nondegeneracy is not built into the structure so
that integrated forms and nondegeneracy equivalences apply uniformly. -/
structure CovariantMultiplierHom (α : CStarAction G A) (B : Type*)
    [NonUnitalCStarAlgebra B] where
  /-- The coefficient ⋆-homomorphism into `𝓜(ℂ, B)`. -/
  coefficient : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)
  /-- The group homomorphism into the unitary group of `𝓜(ℂ, B)`. -/
  group : G →* unitary 𝓜(ℂ, B)
  /-- Strict left continuity of the group homomorphism: `r ↦ u_r b` is norm continuous. -/
  continuous_group_fst (b : B) : Continuous fun r => (group r : 𝓜(ℂ, B)).fst b
  /-- Covariance of the coefficient and group multiplier maps. -/
  covariance (r : G) (a : A) :
    (group r : 𝓜(ℂ, B)) * coefficient a = coefficient (α r a) * group r

namespace CovariantMultiplierHom

variable {α : CStarAction G A}

/-- The coefficient and group homomorphisms determine a covariant multiplier homomorphism. -/
@[ext]
theorem ext {M N : CovariantMultiplierHom α B}
    (hπ : M.coefficient = N.coefficient) (hu : M.group = N.group) : M = N := by
  cases M
  cases N
  cases hπ
  cases hu
  rfl

/-- Covariance as an equality in `𝓜(ℂ, B)`. -/
@[simp]
theorem group_mul_coefficient (M : CovariantMultiplierHom α B) (r : G) (a : A) :
    (M.group r : 𝓜(ℂ, B)) * M.coefficient a = M.coefficient (α r a) * M.group r :=
  M.covariance r a

/-- Moving a group multiplier to the left of a coefficient twists by the inverse group element. -/
theorem coefficient_mul_group (M : CovariantMultiplierHom α B) (r : G) (a : A) :
    M.coefficient a * (M.group r : 𝓜(ℂ, B)) = (M.group r : 𝓜(ℂ, B)) * M.coefficient (α r⁻¹ a) := by
  calc M.coefficient a * (M.group r : 𝓜(ℂ, B))
      = M.coefficient (α r (α r⁻¹ a)) * M.group r := by simp
    _ = (M.group r : 𝓜(ℂ, B)) * M.coefficient (α r⁻¹ a) := (M.group_mul_coefficient r _).symm

/-- Conjugation by `M.group r` implements the action `α r` on coefficients. -/
theorem coefficient_action (M : CovariantMultiplierHom α B) (r : G) (a : A) :
    M.coefficient (α r a) = (M.group r : 𝓜(ℂ, B)) * M.coefficient a * (M.group r⁻¹ : 𝓜(ℂ, B)) := by
  rw [M.group_mul_coefficient, mul_assoc, ← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one,
    OneMemClass.coe_one, mul_one]

/-- Every unitary multiplier in the image of `M.group` has norm at most `1`, without assuming `B`
nontrivial. -/
theorem norm_group_le_one (M : CovariantMultiplierHom α B) (r : G) :
    ‖(M.group r : 𝓜(ℂ, B))‖ ≤ 1 := by
  by_cases h : Nontrivial 𝓜(ℂ, B)
  · exact (CStarRing.norm_coe_unitary (M.group r)).le
  · have := not_nontrivial_iff_subsingleton.1 h
    simp [Subsingleton.elim (M.group r : 𝓜(ℂ, B)) 0]

/-- On a topological group, strict right continuity `r ↦ b u_r` follows from strict left
continuity by taking stars and inverting the group variable. -/
theorem continuous_group_snd [IsTopologicalGroup G] (M : CovariantMultiplierHom α B) (b : B) :
    Continuous fun r => (M.group r : 𝓜(ℂ, B)).snd b := by
  have heq (r : G) :
      (M.group r : 𝓜(ℂ, B)).snd b = star ((M.group r⁻¹ : 𝓜(ℂ, B)).fst (star b)) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star, DoubleCentralizer.star_fst, star_star,
      star_star]
  simp_rw [heq]
  exact ((M.continuous_group_fst (star b)).comp continuous_inv).star

/-- Compose a covariant multiplier homomorphism into `𝓜(ℂ, B)` with the multiplier extension of a
nondegenerate Hilbert-space representation of `B` to obtain a `CovariantRepresentation`. -/
def toCovariantRepresentation (M : CovariantMultiplierHom α B) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) : CovariantRepresentation α H where
  coefficient := (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp M.coefficient
  group := .ofMonoidHom
    (((ρ.multiplierExtension hρ : 𝓜(ℂ, B) →* (H →L[ℂ] H)).comp
      (Submonoid.subtype (unitary 𝓜(ℂ, B)))).comp M.group)
  isUnitary := (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun r =>
    Unitary.map_mem (ρ.multiplierExtension hρ) (M.group r).prop
  continuous_orbit v :=
    ρ.continuous_multiplierExtension_apply hρ M.continuous_group_fst M.norm_group_le_one v
  covariance r a v := by
    have hcov := congr($(congrArg (ρ.multiplierExtension hρ) (M.covariance r a)) v)
    rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp] at hcov
    exact hcov

@[simp]
theorem toCovariantRepresentation_coefficient (M : CovariantMultiplierHom α B) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    (M.toCovariantRepresentation hρ).coefficient =
      (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom.comp M.coefficient :=
  (rfl)

@[simp]
theorem toCovariantRepresentation_group_apply (M : CovariantMultiplierHom α B) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) (r : G) :
    (M.toCovariantRepresentation hρ).group r = ρ.multiplierExtension hρ (M.group r) :=
  (rfl)

/-- Push a covariant multiplier homomorphism into `𝓜(ℂ, B)` forward along a nondegenerate
multiplier homomorphism `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)`. -/
def map (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) : CovariantMultiplierHom α C where
  coefficient := (ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp M.coefficient
  group := (Unitary.map (StarMonoidHom.ofClass (ψ.extendToMultiplier hψ))).toMonoidHom.comp M.group
  continuous_group_fst c :=
    ψ.continuous_extendToMultiplier_fst_apply hψ M.continuous_group_fst M.norm_group_le_one c
  covariance r a := by
    have hcov := congrArg (ψ.extendToMultiplier hψ) (M.covariance r a)
    rw [map_mul, map_mul] at hcov
    exact hcov

@[simp]
theorem map_coefficient (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) :
    (M.map hψ).coefficient =
      (ψ.extendToMultiplier hψ).toNonUnitalStarAlgHom.comp M.coefficient :=
  (rfl)

@[simp]
theorem coe_map_group (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) (r : G) :
    ((M.map hψ).group r : 𝓜(ℂ, C)) = ψ.extendToMultiplier hψ (M.group r) :=
  (rfl)

/-- Pushing forward along `ψ` and then applying a nondegenerate representation `π` of `C` agrees
with applying the composite nondegenerate representation `(π.multiplierExtension hπ) ∘ ψ`. -/
@[simp]
theorem toCovariantRepresentation_map (M : CovariantMultiplierHom α B) {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate) :
    (M.map hψ).toCovariantRepresentation hπ =
      M.toCovariantRepresentation (hπ.multiplierExtension_comp hψ) := by
  apply CovariantRepresentation.ext
  · ext a v
    exact congr($(DFunLike.congr_fun
      (NonUnitalStarAlgHom.multiplierExtension_comp_extendToMultiplier hπ hψ).symm
      (M.coefficient a)) v)
  · refine DFunLike.ext _ _ fun r => ?_
    exact DFunLike.congr_fun
      (NonUnitalStarAlgHom.multiplierExtension_comp_extendToMultiplier hπ hψ).symm
      (M.group r : 𝓜(ℂ, B))

/-- Pull back a covariant multiplier homomorphism along an equivariant coefficient map. -/
def comap {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) : CovariantMultiplierHom α' B where
  coefficient := M.coefficient.comp φ.toNonUnitalStarAlgHom
  group := M.group
  continuous_group_fst := M.continuous_group_fst
  covariance r a := by
    simpa only [NonUnitalStarAlgHom.comp_apply, Hom.coe_toNonUnitalStarAlgHom, φ.map_action]
      using M.covariance r (φ a)

@[simp]
theorem comap_coefficient {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) :
    (M.comap φ).coefficient = M.coefficient.comp φ.toNonUnitalStarAlgHom :=
  (rfl)

@[simp]
theorem comap_group {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (M : CovariantMultiplierHom α B) (φ : Hom α' α) :
    (M.comap φ).group = M.group :=
  (rfl)

@[simp]
theorem toCovariantRepresentation_comap {A' : Type*} [NonUnitalCStarAlgebra A']
    {α' : CStarAction G A'} (M : CovariantMultiplierHom α B) (φ : Hom α' α) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hρ : ρ.IsNondegenerate) :
    (M.comap φ).toCovariantRepresentation hρ = (M.toCovariantRepresentation hρ).comap φ := by
  apply CovariantRepresentation.ext
  · ext a v
    simp
  · refine DFunLike.ext _ _ fun r => ?_
    simp

end CovariantMultiplierHom

end Basic

/-! ### Strict Bochner integration of covariant multiplier homomorphisms -/

namespace CovariantMultiplierHom

section Integrated

variable {G A B C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} (M : CovariantMultiplierHom α B)
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The left centralizer integrand `r ↦ (π(f r) u_r).fst b` is norm continuous in `B`. -/
@[fun_prop]
theorem continuous_integrand_fst (f : C_c(G, A)) (b : B) :
    Continuous fun r => (M.coefficient (f r) * M.group r).fst b := by
  simp only [DoubleCentralizer.mul_fst, mul_apply_eq_comp]
  exact ((DoubleCentralizer.continuous_toProd.fst.comp
    ((map_continuous M.coefficient).comp f.continuous))).clm_apply (M.continuous_group_fst b)

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The right centralizer integrand `r ↦ (π(f r) u_r).snd b` is norm continuous in `B`, rewritten
using covariance so that the norm-continuous coefficient map acts on the outside. -/
@[fun_prop]
theorem continuous_integrand_snd (f : C_c(G, A)) (b : B) :
    Continuous fun r => (M.coefficient (f r) * M.group r).snd b := by
  simp_rw [M.coefficient_mul_group, DoubleCentralizer.mul_snd, mul_apply_eq_comp]
  have hα : Continuous fun r => α r⁻¹ (f r) := α.continuous_apply continuous_inv f.continuous
  exact ((DoubleCentralizer.continuous_toProd.snd.comp
    ((map_continuous M.coefficient).comp hα))).clm_apply (M.continuous_group_snd b)

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The left centralizer integrand vanishes outside the support of `f`. -/
theorem hasCompactSupport_integrand_fst (f : C_c(G, A)) (b : B) :
    HasCompactSupport fun r => (M.coefficient (f r) * M.group r).fst b :=
  f.hasCompactSupport.mono fun _ hg hzero => hg (by simp [hzero])

omit [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The right centralizer integrand vanishes outside the support of `f`. -/
theorem hasCompactSupport_integrand_snd (f : C_c(G, A)) (b : B) :
    HasCompactSupport fun r => (M.coefficient (f r) * M.group r).snd b :=
  f.hasCompactSupport.mono fun _ hg hzero => hg (by simp [hzero])

omit [IsTopologicalGroup G] in
/-- The left centralizer integrand is Bochner integrable. -/
theorem integrable_integrand_fst (f : C_c(G, A)) (b : B) :
    Integrable (fun r => (M.coefficient (f r) * M.group r).fst b) μ :=
  (M.continuous_integrand_fst f b).integrable_of_hasCompactSupport
    (M.hasCompactSupport_integrand_fst f b)

/-- The right centralizer integrand is Bochner integrable. -/
theorem integrable_integrand_snd (f : C_c(G, A)) (b : B) :
    Integrable (fun r => (M.coefficient (f r) * M.group r).snd b) μ :=
  (M.continuous_integrand_snd f b).integrable_of_hasCompactSupport
    (M.hasCompactSupport_integrand_snd f b)

omit [IsTopologicalGroup G] in
private theorem norm_integral_fst_le (f : C_c(G, A)) (b : B) :
    ‖∫ r, (M.coefficient (f r) * M.group r).fst b ∂μ‖ ≤ (∫ r, ‖f r‖ ∂μ) * ‖b‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun r => ?_)
  calc ‖(M.coefficient (f r) * M.group r).fst b‖
      ≤ ‖(M.coefficient (f r) * M.group r).fst‖ * ‖b‖ :=
        ((M.coefficient (f r) * M.group r).fst).le_opNorm b
    _ = ‖M.coefficient (f r)‖ * ‖b‖ := by
        rw [DoubleCentralizer.norm_fst, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖f r‖ * ‖b‖ :=
        mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg b)

omit [IsTopologicalGroup G] in
private theorem norm_integral_snd_le (f : C_c(G, A)) (b : B) :
    ‖∫ r, (M.coefficient (f r) * M.group r).snd b ∂μ‖ ≤ (∫ r, ‖f r‖ ∂μ) * ‖b‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (f.integrable.norm.mul_const _) (.of_forall fun r => ?_)
  calc ‖(M.coefficient (f r) * M.group r).snd b‖
      ≤ ‖(M.coefficient (f r) * M.group r).snd‖ * ‖b‖ :=
        ((M.coefficient (f r) * M.group r).snd).le_opNorm b
    _ = ‖M.coefficient (f r)‖ * ‖b‖ := by
        rw [DoubleCentralizer.norm_snd, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖f r‖ * ‖b‖ :=
        mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg b)

omit [IsTopologicalGroup G] in
private def integratedFst (f : C_c(G, A)) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun b := ∫ r, (M.coefficient (f r) * M.group r).fst b ∂μ
      map_add' b c := by
        simp_rw [map_add]
        exact integral_add (M.integrable_integrand_fst μ f b) (M.integrable_integrand_fst μ f c)
      map_smul' z b := by
        simp_rw [map_smul]
        exact integral_smul z _ }
    (∫ r, ‖f r‖ ∂μ) (M.norm_integral_fst_le μ f)

private def integratedSnd (f : C_c(G, A)) : B →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun b := ∫ r, (M.coefficient (f r) * M.group r).snd b ∂μ
      map_add' b c := by
        simp_rw [map_add]
        exact integral_add (M.integrable_integrand_snd μ f b) (M.integrable_integrand_snd μ f c)
      map_smul' z b := by
        simp_rw [map_smul]
        exact integral_smul z _ }
    (∫ r, ‖f r‖ ∂μ) (M.norm_integral_snd_le μ f)

/-- The strict Bochner integrated form of a covariant multiplier homomorphism on `C_c(G, A)`. -/
def integratedMultiplier : C_c(G, A) →ₗ[ℂ] 𝓜(ℂ, B) where
  toFun f :=
    { toProd := (M.integratedFst μ f, M.integratedSnd μ f)
      central x y := by
        dsimp only [integratedFst, integratedSnd, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
          AddHom.coe_mk]
        have hl := (ContinuousLinearMap.mul ℂ B x).integral_comp_comm
          (M.integrable_integrand_fst μ f y)
        have hr := ((ContinuousLinearMap.mul ℂ B).flip y).integral_comp_comm
          (M.integrable_integrand_snd μ f x)
        simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hl hr
        rw [← hl, ← hr]
        congr 1 with r
        exact (M.coefficient (f r) * M.group r).central x y }
  map_add' f g := DoubleCentralizer.ext_fst fun b => by
    simp only [DoubleCentralizer.add_fst, add_apply]
    dsimp only [integratedFst, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [CompactlySupportedContinuousMap.add_apply, map_add, add_mul,
      DoubleCentralizer.add_fst, add_apply]
    exact integral_add (M.integrable_integrand_fst μ f b) (M.integrable_integrand_fst μ g b)
  map_smul' z f := DoubleCentralizer.ext_fst fun b => by
    simp only [DoubleCentralizer.smul_fst, smul_apply, RingHom.id_apply]
    dsimp only [integratedFst, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [CompactlySupportedContinuousMap.smul_apply, map_smul, smul_mul_assoc,
      DoubleCentralizer.smul_fst, smul_apply]
    exact integral_smul z _

/-- Left action of the integrated multiplier as a Bochner integral in `B`. -/
@[simp]
theorem integratedMultiplier_fst_apply (f : C_c(G, A)) (b : B) :
    (M.integratedMultiplier μ f).fst b = ∫ r, (M.coefficient (f r) * M.group r).fst b ∂μ :=
  (rfl)

/-- Right action of the integrated multiplier as a Bochner integral in `B`. -/
@[simp]
theorem integratedMultiplier_snd_apply (f : C_c(G, A)) (b : B) :
    (M.integratedMultiplier μ f).snd b = ∫ r, (M.coefficient (f r) * M.group r).snd b ∂μ :=
  (rfl)

/-- The integrated multiplier is bounded in norm by the L¹ norm of `f`. -/
theorem norm_integratedMultiplier_le (f : C_c(G, A)) :
    ‖M.integratedMultiplier μ f‖ ≤ ∫ r, ‖f r‖ ∂μ := by
  rw [← DoubleCentralizer.norm_fst]
  exact LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => norm_nonneg _)
    (M.norm_integral_fst_le μ f)

/-- Applying the multiplier extension of any nondegenerate Hilbert-space representation of `B` to
`M.integratedMultiplier μ f` yields the vector-integrated operator of the corresponding
`CovariantRepresentation`. -/
@[simp]
theorem multiplierExtension_integratedMultiplier {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (f : C_c(G, A)) :
    ρ.multiplierExtension hρ (M.integratedMultiplier μ f) =
      (M.toCovariantRepresentation hρ).integratedOperator μ f := by
  symm
  refine (ρ.eq_multiplierExtension_iff hρ).2 fun b => ContinuousLinearMap.ext fun v => ?_
  rw [mul_apply_eq_comp, CovariantRepresentation.integratedOperator_apply,
    integratedMultiplier_fst_apply]
  let L : B →L[ℂ] H :=
    LinearMap.mkContinuous
      { toFun x := ρ x v
        map_add' x y := by simp
        map_smul' c x := by simp }
      ‖v‖ fun x => ((ρ x).le_opNorm v).trans <|
        (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ρ x)
          (norm_nonneg v)).trans_eq (mul_comm _ _)
  have hL := L.integral_comp_comm (M.integrable_integrand_fst μ f b)
  simp only [L, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] at hL
  rw [← hL]
  congr 1 with r
  simp [DoubleCentralizer.mul_fst, mul_apply_eq_comp]

/-- Pushing `M` forward along a nondegenerate `ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)` commutes with strict
Bochner integration. -/
@[simp]
theorem extendToMultiplier_integratedMultiplier {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) (f : C_c(G, A)) :
    ψ.extendToMultiplier hψ (M.integratedMultiplier μ f) = (M.map hψ).integratedMultiplier μ f := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ π hπ => ?_
  have hcomp : π.multiplierExtension hπ (ψ.extendToMultiplier hψ (M.integratedMultiplier μ f)) =
      ((π.multiplierExtension hπ).toNonUnitalStarAlgHom.comp ψ).multiplierExtension
        (hπ.multiplierExtension_comp hψ) (M.integratedMultiplier μ f) :=
    DFunLike.congr_fun (NonUnitalStarAlgHom.multiplierExtension_comp_extendToMultiplier hπ hψ).symm
      (M.integratedMultiplier μ f)
  rw [hcomp, M.multiplierExtension_integratedMultiplier,
    (M.map hψ).multiplierExtension_integratedMultiplier, M.toCovariantRepresentation_map]

/-- Left multiplication of `f` by `a : A` becomes left multiplication by `M.coefficient a`. -/
@[simp]
theorem integratedMultiplier_smul (a : A) (f : C_c(G, A)) :
    M.integratedMultiplier μ (a • f) = M.coefficient a * M.integratedMultiplier μ f := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ ρ hρ => ?_
  simp

section LeftInvariant

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Strict Bochner integration is multiplicative for twisted convolution with respect to a
left-invariant measure. -/
@[simp]
theorem integratedMultiplier_convolution (f g : C_c(G, A)) :
    M.integratedMultiplier μ (α.convolution μ f g) =
      M.integratedMultiplier μ f * M.integratedMultiplier μ g := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ ρ hρ => ?_
  simp

/-- Twisted left translation on `C_c(G, A)` becomes left multiplication by `M.group r`. -/
@[simp]
theorem integratedMultiplier_translate (r : G) (f : C_c(G, A)) :
    M.integratedMultiplier μ (α.translate r f) =
      (M.group r : 𝓜(ℂ, B)) * M.integratedMultiplier μ f := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ ρ hρ => ?_
  simp

end LeftInvariant

section PeakApproximation

variable [LocallyCompactSpace G] [R1Space G] [μ.IsOpenPosMeasure]

/-- Peak-function approximation at any group element `r₀ : G`: every vector
`(π a * u_{r₀}).fst b` in `B` can be approximated in norm within `ε > 0` by
`(M.integratedMultiplier μ f).fst b` for a scalar peak multiple `f = φ • a : C_c(G, A)`. -/
theorem exists_norm_integratedMultiplier_fst_sub_le (r₀ : G) (a : A) (b : B) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ f : C_c(G, A),
      ‖(M.integratedMultiplier μ f).fst b - (M.coefficient a * M.group r₀).fst b‖ ≤ ε := by
  set ψ : G → B := fun r => (M.coefficient a * M.group r).fst b
  have hψ : Continuous ψ := by
    simp only [ψ, DoubleCentralizer.mul_fst, mul_apply_eq_comp]
    exact (M.coefficient a).fst.continuous.comp (M.continuous_group_fst b)
  have hU : {r : G | ‖ψ r - ψ r₀‖ ≤ ε} ∈ 𝓝 r₀ :=
    (continuous_norm.comp (hψ.sub continuous_const)).continuousAt.preimage_mem_nhds
      (ge_mem_nhds (by simpa [ψ] using hε))
  obtain ⟨φ, hφ0, hφU, hφ1⟩ := exists_nonneg_tsupport_subset_integral_eq_one μ hU
  let f : C_c(G, A) := φ.compLeft (ContinuousLinearMap.toSpanSingleton ℝ a)
  refine ⟨f, ?_⟩
  have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hae := hφi.coeFn_toL1
  have hnorm : ‖hφi.toL1 φ‖ = 1 := by
    rw [L1.norm_eq_integral_norm, ← hφ1]
    exact integral_congr_ae (hae.mono fun r hr =>
      (congrArg norm hr).trans (Real.norm_of_nonneg (hφ0 r)))
  have hf_int : (M.integratedMultiplier μ f).fst b = ∫ r, (hφi.toL1 φ) r • ψ r ∂μ := by
    rw [integratedMultiplier_fst_apply]
    refine integral_congr_ae (hae.mono fun r hr => ?_)
    have hfr : f r = (φ r : ℂ) • a := by
      simp [f, CompactlySupportedContinuousMap.compLeft_apply]
    dsimp only [ψ]
    rw [hfr, map_smul, smul_mul_assoc, DoubleCentralizer.smul_fst, smul_apply, hr]
    simp
  have haesm : AEStronglyMeasurable (fun r => (hφi.toL1 φ) r • ψ r) μ :=
    ((((map_continuous φ).smul hψ).integrable_of_hasCompactSupport
      φ.hasCompactSupport.smul_right).aestronglyMeasurable).congr
        (hae.mono fun r hr => by dsimp only [Pi.smul_apply']; rw [hr])
  have hbound := norm_integral_smul_sub_le (𝕜 := ℝ) (f := hφi.toL1 φ) (U := tsupport φ)
    (φ := ψ) (y := ψ r₀) ((integral_congr_ae hae).trans hφ1)
    (hae.mono fun r hr hrU => hr.trans (image_eq_zero_of_notMem_tsupport hrU))
    haesm (fun r hr => hφU hr)
  rwa [← hf_int, hnorm, mul_one] at hbound

/-- The integrated multipliers on `C_c(G, A)` generate the exact same closed essential subspace of
`B` as `M.coefficient`. -/
theorem topologicalClosure_span_integratedMultiplier :
    (Submodule.span ℂ
      (⋃ f : C_c(G, A), Set.range (M.integratedMultiplier μ f).fst)).topologicalClosure =
      (Submodule.span ℂ (⋃ a : A, Set.range (M.coefficient a).fst)).topologicalClosure := by
  set S₁ := Submodule.span ℂ (⋃ f : C_c(G, A), Set.range (M.integratedMultiplier μ f).fst)
  set S₂ := Submodule.span ℂ (⋃ a : A, Set.range (M.coefficient a).fst)
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      S₂.isClosed_topologicalClosure
    rintro _ ⟨_, ⟨f, rfl⟩, b, rfl⟩
    set W := S₂.topologicalClosure
    have : CompleteSpace W := S₂.isClosed_topologicalClosure.completeSpace_coe
    have hmem (r : G) : (M.coefficient (f r) * M.group r).fst b ∈ W :=
      Submodule.le_topologicalClosure S₂ <| Submodule.subset_span <|
        Set.mem_iUnion.2 ⟨f r, (M.group r : 𝓜(ℂ, B)).fst b, rfl⟩
    let F : G → W := Set.codRestrict (fun r => (M.coefficient (f r) * M.group r).fst b) W hmem
    have hF_cont : Continuous F := (M.continuous_integrand_fst f b).codRestrict hmem
    have hF_supp : HasCompactSupport F :=
      (M.hasCompactSupport_integrand_fst f b).mono fun r hr h0 =>
        hr (Subtype.ext (h0.trans Submodule.coe_zero.symm))
    have hF_int : Integrable F μ := hF_cont.integrable_of_hasCompactSupport hF_supp
    have hcomm := W.subtypeL.integral_comp_comm hF_int
    rw [integratedMultiplier_fst_apply]
    exact hcomm.symm ▸ (∫ r, F r ∂μ).prop
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      S₁.isClosed_topologicalClosure
    rintro _ ⟨_, ⟨a, rfl⟩, b, rfl⟩
    rw [Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨f, hf⟩ := M.exists_norm_integratedMultiplier_fst_sub_le μ 1 a b (half_pos hε)
    rw [map_one, OneMemClass.coe_one, mul_one] at hf
    refine ⟨(M.integratedMultiplier μ f).fst b,
      Submodule.subset_span (Set.mem_iUnion.2 ⟨f, b, rfl⟩), ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact hf.trans_lt (half_lt_self hε)

/-- Multiplier nondegeneracy is preserved and reflected by the strict integrated form on
`C_c(G, A)`. -/
theorem dense_span_integratedMultiplier_iff :
    Dense (Submodule.span ℂ
      (⋃ f : C_c(G, A), Set.range (M.integratedMultiplier μ f).fst) : Set B) ↔
      M.coefficient.IsMultiplierNondegenerate := by
  rw [NonUnitalStarAlgHom.isMultiplierNondegenerate_iff_dense,
    Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.dense_iff_topologicalClosure_eq_top,
    M.topologicalClosure_span_integratedMultiplier μ]

end PeakApproximation

end Integrated

end CovariantMultiplierHom

/-! ### Uniqueness of covariant pairs from their integrated forms -/

namespace CovariantRepresentation

section Uniqueness

variable {G A H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [LocallyCompactSpace G] [R1Space G]
  [NonUnitalCStarAlgebra A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {α : CStarAction G A} {P Q : CovariantRepresentation α H}
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

omit [LocallyCompactSpace G] [R1Space G] [μ.IsOpenPosMeasure] in
private theorem norm_integratedOperator_compLeft_sub_le (P : CovariantRepresentation α H)
    (r₀ : G) (a : A) (v : H) {ε : ℝ} {φ : C_c(G, ℝ)} (hφ0 : 0 ≤ φ) (hφ1 : ∫ r, φ r ∂μ = 1)
    (hφU : ∀ r ∈ tsupport φ,
      ‖P.coefficient a (P.group r v) - P.coefficient a (P.group r₀ v)‖ ≤ ε) :
    ‖P.integratedOperator μ (φ.compLeft (ContinuousLinearMap.toSpanSingleton ℝ a)) v -
      P.coefficient a (P.group r₀ v)‖ ≤ ε := by
  set ψ : G → H := fun r => P.coefficient a (P.group r v)
  have hψ : Continuous ψ := (P.coefficient a).continuous.comp (P.continuous_orbit v)
  have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hae := hφi.coeFn_toL1
  have hnorm : ‖hφi.toL1 φ‖ = 1 := by
    rw [L1.norm_eq_integral_norm, ← hφ1]
    exact integral_congr_ae (hae.mono fun r hr =>
      (congrArg norm hr).trans (Real.norm_of_nonneg (hφ0 r)))
  have hf_int :
      P.integratedOperator μ (φ.compLeft (ContinuousLinearMap.toSpanSingleton ℝ a)) v =
        ∫ r, (hφi.toL1 φ) r • ψ r ∂μ := by
    rw [integratedOperator_apply]
    refine integral_congr_ae (hae.mono fun r hr => ?_)
    have hfr : (φ.compLeft (ContinuousLinearMap.toSpanSingleton ℝ a)) r = (φ r : ℂ) • a := by
      simp [CompactlySupportedContinuousMap.compLeft_apply]
    dsimp only [ψ]
    rw [hfr, map_smul, smul_apply, hr]
    simp
  have haesm : AEStronglyMeasurable (fun r => (hφi.toL1 φ) r • ψ r) μ :=
    ((((map_continuous φ).smul hψ).integrable_of_hasCompactSupport
      φ.hasCompactSupport.smul_right).aestronglyMeasurable).congr
        (hae.mono fun r hr => by dsimp only [Pi.smul_apply']; rw [hr])
  have hbound := norm_integral_smul_sub_le (𝕜 := ℝ) (f := hφi.toL1 φ) (U := tsupport φ)
    (φ := ψ) (y := ψ r₀) ((integral_congr_ae hae).trans hφ1)
    (hae.mono fun r hr hrU => hr.trans (image_eq_zero_of_notMem_tsupport hrU))
    haesm hφU
  rwa [← hf_int, hnorm, mul_one] at hbound

/-- Two Hilbert-space covariant representations with the same integrated operators satisfy
`P.coefficient a * P.group r = Q.coefficient a * Q.group r` for every `a` and `r`, without any
nondegeneracy assumption. -/
theorem coefficient_mul_group_eq_of_integratedOperator_eq
    (h : ∀ f : C_c(G, A), P.integratedOperator μ f = Q.integratedOperator μ f)
    (a : A) (r₀ : G) :
    P.coefficient a * P.group r₀ = Q.coefficient a * Q.group r₀ := by
  ext v
  simp only [mul_apply_eq_comp]
  refine eq_of_sub_eq_zero <| norm_le_zero_iff.1 <| le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  have hPcont : Continuous fun r => P.coefficient a (P.group r v) :=
    (P.coefficient a).continuous.comp (P.continuous_orbit v)
  have hQcont : Continuous fun r => Q.coefficient a (Q.group r v) :=
    (Q.coefficient a).continuous.comp (Q.continuous_orbit v)
  have hUP : {r : G | ‖P.coefficient a (P.group r v) - P.coefficient a (P.group r₀ v)‖ ≤ ε / 2} ∈
      𝓝 r₀ :=
    (continuous_norm.comp (hPcont.sub continuous_const)).continuousAt.preimage_mem_nhds
      (ge_mem_nhds (by simpa using half_pos hε))
  have hUQ : {r : G | ‖Q.coefficient a (Q.group r v) - Q.coefficient a (Q.group r₀ v)‖ ≤ ε / 2} ∈
      𝓝 r₀ :=
    (continuous_norm.comp (hQcont.sub continuous_const)).continuousAt.preimage_mem_nhds
      (ge_mem_nhds (by simpa using half_pos hε))
  obtain ⟨φ, hφ0, hφU, hφ1⟩ :=
    exists_nonneg_tsupport_subset_integral_eq_one μ (Filter.inter_mem hUP hUQ)
  set f : C_c(G, A) := φ.compLeft (ContinuousLinearMap.toSpanSingleton ℝ a)
  have hbP := norm_integratedOperator_compLeft_sub_le μ P r₀ a v hφ0 hφ1 fun r hr => (hφU hr).1
  have hbQ := norm_integratedOperator_compLeft_sub_le μ Q r₀ a v hφ0 hφ1 fun r hr => (hφU hr).2
  have hPQ : P.integratedOperator μ f v = Q.integratedOperator μ f v := congr($(h f) v)
  calc ‖P.coefficient a (P.group r₀ v) - Q.coefficient a (Q.group r₀ v)‖
      ≤ ‖P.coefficient a (P.group r₀ v) - P.integratedOperator μ f v‖ +
          ‖Q.integratedOperator μ f v - Q.coefficient a (Q.group r₀ v)‖ := by
        rw [← hPQ]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 + ε / 2 := by
        rw [norm_sub_rev]
        exact add_le_add hbP hbQ
    _ = ε := add_halves ε

/-- Two covariant representations with the same integrated operators have the same coefficient
representation. -/
theorem coefficient_eq_of_integratedOperator_eq
    (h : ∀ f : C_c(G, A), P.integratedOperator μ f = Q.integratedOperator μ f) :
    P.coefficient = Q.coefficient := by
  ext a v
  simpa using congr($(coefficient_mul_group_eq_of_integratedOperator_eq μ h a 1) v)

/-- Nondegenerate Hilbert-space covariant representations are uniquely determined by their
integrated operators on `C_c(G, A)`. -/
theorem eq_of_integratedOperator_eq (hP : P.coefficient.IsNondegenerate)
    (h : ∀ f : C_c(G, A), P.integratedOperator μ f = Q.integratedOperator μ f) :
    P = Q := by
  have hcoef := coefficient_eq_of_integratedOperator_eq μ h
  refine CovariantRepresentation.ext hcoef (DFunLike.ext _ _ fun r => ?_)
  refine hP.ext fun a => ?_
  rw [P.group_mul_coefficient, coefficient_mul_group_eq_of_integratedOperator_eq μ h (α r a) r,
    ← Q.group_mul_coefficient, ← hcoef]

end Uniqueness

end CovariantRepresentation

namespace CovariantMultiplierHom

section Uniqueness

variable {G A B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [LocallyCompactSpace G] [R1Space G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {M N : CovariantMultiplierHom α B}
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- Two covariant multiplier homomorphisms with the same integrated multipliers satisfy
`M.coefficient a * M.group r = N.coefficient a * N.group r` for every `a` and `r`. -/
theorem coefficient_mul_group_eq_of_integratedMultiplier_eq
    (h : ∀ f : C_c(G, A), M.integratedMultiplier μ f = N.integratedMultiplier μ f)
    (a : A) (r : G) :
    M.coefficient a * (M.group r : 𝓜(ℂ, B)) = N.coefficient a * (N.group r : 𝓜(ℂ, B)) := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ ρ hρ => ?_
  have hint (f : C_c(G, A)) :
      (M.toCovariantRepresentation hρ).integratedOperator μ f =
        (N.toCovariantRepresentation hρ).integratedOperator μ f := by
    rw [← M.multiplierExtension_integratedMultiplier μ hρ,
      ← N.multiplierExtension_integratedMultiplier μ hρ, h f]
  simpa [map_mul] using
    CovariantRepresentation.coefficient_mul_group_eq_of_integratedOperator_eq μ hint a r

/-- Two covariant multiplier homomorphisms with the same integrated multipliers have the same
coefficient homomorphism. -/
theorem coefficient_eq_of_integratedMultiplier_eq
    (h : ∀ f : C_c(G, A), M.integratedMultiplier μ f = N.integratedMultiplier μ f) :
    M.coefficient = N.coefficient := by
  ext a : 1
  simpa using coefficient_mul_group_eq_of_integratedMultiplier_eq μ h a 1

/-- Nondegenerate covariant multiplier homomorphisms are uniquely determined by their strict
integrated forms on `C_c(G, A)`. -/
theorem eq_of_integratedMultiplier_eq (hM : M.coefficient.IsMultiplierNondegenerate)
    (h : ∀ f : C_c(G, A), M.integratedMultiplier μ f = N.integratedMultiplier μ f) :
    M = N := by
  have hcoef := coefficient_eq_of_integratedMultiplier_eq μ h
  refine ext hcoef ?_
  ext r : 1
  refine Subtype.ext (hM.ext_mul_left fun a => ?_)
  rw [coefficient_mul_group_eq_of_integratedMultiplier_eq μ h a r, hcoef]

end Uniqueness

section Haar

variable {G A B C : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  {α : CStarAction G A} (M : CovariantMultiplierHom α B)
  (μ : Measure G) [μ.IsHaarMeasure]

/-- With respect to a left Haar measure, strict Bochner integration sends the twisted involution on
`C_c(G, A)` to the adjoint in `𝓜(ℂ, B)`. -/
@[simp]
theorem integratedMultiplier_twistedInvolution (f : C_c(G, A)) :
    M.integratedMultiplier μ (α.twistedInvolution f) = star (M.integratedMultiplier μ f) := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ ρ hρ => ?_
  simp [map_star]

/-- The strict integrated form of a covariant multiplier homomorphism as a ⋆-homomorphism out of
the twisted convolution algebra `ConvolutionAlgebra α μ`. -/
def integratedStarAlgHom : ConvolutionAlgebra α μ →⋆ₙₐ[ℂ] 𝓜(ℂ, B) where
  toFun f := M.integratedMultiplier μ f.ofConv
  map_zero' := by simp
  map_add' f g := by simp
  map_mul' f g := by simp
  map_smul' z f := by simp
  map_star' f := by simp

@[simp]
theorem integratedStarAlgHom_apply (f : ConvolutionAlgebra α μ) :
    M.integratedStarAlgHom μ f = M.integratedMultiplier μ f.ofConv :=
  (rfl)

/-- The integrated ⋆-homomorphism is contractive for the L¹ norm on `ConvolutionAlgebra α μ`. -/
theorem norm_integratedStarAlgHom_le_norm (f : ConvolutionAlgebra α μ) :
    ‖M.integratedStarAlgHom μ f‖ ≤ ‖f‖ := by
  simpa [ConvolutionAlgebra.norm_eq_integral_norm] using M.norm_integratedMultiplier_le μ f.ofConv

@[simp]
theorem multiplierExtension_integratedStarAlgHom {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hρ : ρ.IsNondegenerate) (f : ConvolutionAlgebra α μ) :
    ρ.multiplierExtension hρ (M.integratedStarAlgHom μ f) =
      (M.toCovariantRepresentation hρ).integratedStarAlgHom μ f := by
  simp [integratedStarAlgHom_apply]

@[simp]
theorem extendToMultiplier_integratedStarAlgHom {ψ : B →⋆ₙₐ[ℂ] 𝓜(ℂ, C)}
    (hψ : ψ.IsMultiplierNondegenerate) (f : ConvolutionAlgebra α μ) :
    ψ.extendToMultiplier hψ (M.integratedStarAlgHom μ f) =
      (M.map hψ).integratedStarAlgHom μ f := by
  simp [integratedStarAlgHom_apply]

theorem integratedStarAlgHom_comap {A' : Type*} [NonUnitalCStarAlgebra A'] {α' : CStarAction G A'}
    (φ : Hom α' α) (f : ConvolutionAlgebra α' μ) :
    (M.comap φ).integratedStarAlgHom μ f = M.integratedStarAlgHom μ (φ.convolutionMap μ f) := by
  refine DoubleCentralizer.eq_iff_forall_multiplierExtension_eq.2 fun H _ _ _ ρ hρ => ?_
  simpa using (M.toCovariantRepresentation hρ).integratedOperator_comap φ μ f

/-- Nondegenerate covariant multiplier homomorphisms are uniquely determined by their integrated
⋆-homomorphisms on `ConvolutionAlgebra α μ`. -/
theorem eq_of_integratedStarAlgHom_eq {N : CovariantMultiplierHom α B}
    (hM : M.coefficient.IsMultiplierNondegenerate)
    (h : M.integratedStarAlgHom μ = N.integratedStarAlgHom μ) : M = N :=
  eq_of_integratedMultiplier_eq μ hM fun f => by
    simpa using congr($h (ConvolutionAlgebra.toConv f))

end Haar

end CovariantMultiplierHom

end TauCeti.CStarAction
