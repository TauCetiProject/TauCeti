/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.GNS
public import TauCeti.Analysis.CStarAlgebra.Action.Generator.Basic
public import TauCeti.Analysis.CStarAlgebra.Action.GroundState.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.OneParameter
import TauCeti.Analysis.CStarAlgebra.Action.Generator.Resolvent
import TauCeti.Analysis.CStarAlgebra.GNS
import TauCeti.Analysis.Semigroups.Group.Resolvent

/-!
# Ground states and the positivity of the GNS generator

Let `α` be a point-norm continuous real action on a possibly nonunital C⋆-algebra `A`, and let
`f` be a positive functional invariant under `α`. The GNS implementing group `U_t [b] = [α_t b]`
is a unitary C₀-group on the GNS Hilbert space, `CStarAction.gnsStronglyContinuousGroup`. Its
self-adjoint Stone generator `H`, normalized by `U_t = exp (i t H)`, is the *GNS generator*
`CStarAction.gnsStoneGenerator`. For `a` in the domain of the generator `δ` of the dynamics, the
class `[a]` lies in the domain of `H` and `H [a] = -i [δ a]`,
`CStarAction.gnsStoneGenerator_toPreGNS`; thus `⟪[a], H [a]⟫ = -i f (a⋆ δ(a))`.

The main result, `CStarAction.forall_inner_gnsStoneGenerator_nonneg_iff`, says that `H` is
nonnegative exactly when `f` satisfies the generator inequality `-i f (a⋆ δ(a)) ≥ 0` on the
domain of `δ`. One direction is the formula above. For the other, the resolvent
`R = (1 - i H)⁻¹` of the complex generator `i H` is bounded, so the function
`ζ ↦ -i ⟪R ζ, R ζ - ζ⟫` is continuous. On a class `ζ = [a]` it equals `-i f (b⋆ δ(b))` for
`b = (1 - δ)⁻¹ a`, because `R [a] = [b]` and `[b] - [a] = [δ b]`; hence it is nonnegative on the
dense set of classes, so everywhere. Every `ξ` in the domain of `H` is `R ζ` for
`ζ = ξ - i H ξ`, and then the function takes the value `⟪ξ, H ξ⟫`.

Ground states are invariant and satisfy the generator inequality, so a state is a ground state
exactly when it is invariant and its GNS generator is nonnegative,
`CStarAction.isGroundState_iff_exists_forall_inner_gnsStoneGenerator_nonneg`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, second edition,
Section 5.3.1, Proposition 5.3.19, for the characterization of ground states by the
positivity of the GNS generator.
-/

public section

noncomputable section

open Complex PositiveLinearMap UniformSpace TauCeti.Semigroups
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.CStarAction

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAction (Multiplicative ℝ) A) {f : A →ₚ[ℂ] ℂ} (hf : ∀ g a, f (α g a) = f a)

/-- The GNS implementing group of a positive functional `f` invariant under a real action, as a
strongly continuous one-parameter group on the GNS Hilbert space: `U_t [b] = [α_t b]`. -/
def gnsStronglyContinuousGroup : StronglyContinuousGroup f.GNS :=
  (α.gnsImplementingGroup hf).toStronglyContinuousGroup (α.continuous_gnsImplementingGroup_apply hf)

@[simp]
theorem gnsStronglyContinuousGroup_apply (t : ℝ) (v : f.GNS) :
    α.gnsStronglyContinuousGroup hf t v = α.gnsImplementingGroup hf (Multiplicative.ofAdd t) v :=
  ContRepresentation.toStronglyContinuousGroup_apply _ _ t v

/-- The GNS implementing group of a real action is a unitary C₀-group. -/
theorem isUnitary_gnsStronglyContinuousGroup : (α.gnsStronglyContinuousGroup hf).IsUnitary :=
  ContRepresentation.isUnitary_toStronglyContinuousGroup (α.isUnitary_gnsImplementingGroup hf) _

/-- The **GNS generator** of a positive functional `f` invariant under a real action: the
self-adjoint Stone generator `H` of the GNS implementing group, normalized by
`U_t = exp (i t H)`. -/
def gnsStoneGenerator : f.GNS →ₗ.[ℂ] f.GNS :=
  (α.gnsStronglyContinuousGroup hf).stoneGenerator (α.isUnitary_gnsStronglyContinuousGroup hf)

/-- The GNS generator is the Stone generator of the GNS implementing group. -/
theorem gnsStoneGenerator_def :
    α.gnsStoneGenerator hf = (α.gnsStronglyContinuousGroup hf).stoneGenerator
      (α.isUnitary_gnsStronglyContinuousGroup hf) :=
  (rfl)

/-- The orbit of the class of a domain element is differentiable at `0`, with derivative the
class of its generator value. -/
private theorem hasDerivAt_gnsStronglyContinuousGroup_toPreGNS (a : α.generator.domain) :
    HasDerivAt (fun t : ℝ => α.gnsStronglyContinuousGroup hf t (f.toPreGNS a))
      (f.toPreGNS (α.generator a) : f.GNS) 0 := by
  -- the class map `A → f.GNS` is continuous and complex linear
  let J : A →L[ℂ] f.GNS :=
    Completion.toComplL.comp ⟨f.toPreGNS.toLinearMap, f.continuous_toPreGNS⟩
  simpa [J, Function.comp_def] using
    (J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (α.hasDerivAt_zero a)

/-- The class of a domain element lies in the domain of the complex generator `i H`. -/
private theorem toPreGNS_mem_complexGenerator_domain (a : α.generator.domain) :
    (f.toPreGNS a : f.GNS) ∈ ((α.gnsStronglyContinuousGroup hf).complexGenerator
      (α.isUnitary_gnsStronglyContinuousGroup hf)).domain := by
  rw [StronglyContinuousGroup.complexGenerator_domain,
    StronglyContinuousGroup.mem_complexDomain_iff]
  exact (α.gnsStronglyContinuousGroup hf).mem_domain_of_hasDerivAt_zero
    (α.hasDerivAt_gnsStronglyContinuousGroup_toPreGNS hf a)

/-- The complex generator `i H` sends `[a]` to `[δ a]`. -/
private theorem complexGenerator_toPreGNS (a : α.generator.domain) :
    (α.gnsStronglyContinuousGroup hf).complexGenerator (α.isUnitary_gnsStronglyContinuousGroup hf)
        ⟨_, α.toPreGNS_mem_complexGenerator_domain hf a⟩ =
      (f.toPreGNS (α.generator a) : f.GNS) := by
  rw [StronglyContinuousGroup.complexGenerator_apply]
  exact (α.gnsStronglyContinuousGroup hf).generator_eq_of_hasDerivAt_zero
    (α.hasDerivAt_gnsStronglyContinuousGroup_toPreGNS hf a)

/-- The class of an element of the domain of the generator `δ` lies in the domain of the GNS
generator. -/
theorem toPreGNS_mem_gnsStoneGenerator_domain (a : α.generator.domain) :
    (f.toPreGNS a : f.GNS) ∈ (α.gnsStoneGenerator hf).domain := by
  rw [gnsStoneGenerator_def, StronglyContinuousGroup.stoneGenerator_domain,
    ← StronglyContinuousGroup.complexGenerator_domain]
  exact α.toPreGNS_mem_complexGenerator_domain hf a

/-- **The GNS generator on classes.** For `a` in the domain of the generator `δ` of the
dynamics, `H [a] = -i [δ a]`. -/
@[simp]
theorem gnsStoneGenerator_toPreGNS (a : α.generator.domain) :
    α.gnsStoneGenerator hf ⟨_, α.toPreGNS_mem_gnsStoneGenerator_domain hf a⟩ =
      -I • (f.toPreGNS (α.generator a) : f.GNS) := by
  rw [← α.complexGenerator_toPreGNS hf a]
  exact StronglyContinuousGroup.stoneGenerator_apply _ _ _

/-- Matrix coefficients of the GNS generator between classes:
`⟪[b], H [a]⟫ = -i f (b⋆ δ(a))`. -/
theorem inner_toPreGNS_gnsStoneGenerator_toPreGNS (b : A) (a : α.generator.domain) :
    ⟪(f.toPreGNS b : f.GNS),
        α.gnsStoneGenerator hf ⟨_, α.toPreGNS_mem_gnsStoneGenerator_domain hf a⟩⟫_ℂ =
      -I * f (star b * α.generator a) := by
  rw [gnsStoneGenerator_toPreGNS, inner_smul_right, Completion.inner_coe, preGNS_inner_def]
  rfl

/-- Under the generator inequality, `ζ ↦ -i ⟪R ζ, R ζ - ζ⟫` is nonnegative, where `R` is the
resolvent at `1` of the complex generator `i H`. -/
private theorem neg_I_mul_inner_resolvent_nonneg
    (h : ∀ a : α.generator.domain, 0 ≤ -I * f (star (a : A) * α.generator a))
    (h₁ : (1 : ℂ) ∈ LinearPMap.resolventSet ((α.gnsStronglyContinuousGroup hf).complexGenerator
      (α.isUnitary_gnsStronglyContinuousGroup hf))) (ζ : f.GNS) :
    0 ≤ -I * ⟪LinearPMap.resolvent ((α.gnsStronglyContinuousGroup hf).complexGenerator
        (α.isUnitary_gnsStronglyContinuousGroup hf)) 1 ζ,
      LinearPMap.resolvent ((α.gnsStronglyContinuousGroup hf).complexGenerator
        (α.isUnitary_gnsStronglyContinuousGroup hf)) 1 ζ - ζ⟫_ℂ := by
  set R := LinearPMap.resolvent ((α.gnsStronglyContinuousGroup hf).complexGenerator
    (α.isUnitary_gnsStronglyContinuousGroup hf)) 1
  have hδ₁ : (1 : ℂ) ∈ LinearPMap.resolventSet α.generator :=
    α.mem_resolventSet_generator (z := 1) (by norm_num)
  -- the function is continuous, so it suffices to treat the dense set of classes `[a]`
  induction ζ using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (by fun_prop)
  | ih p =>
    obtain ⟨a, rfl⟩ := f.toPreGNS.surjective p
    -- `b = (1 - δ)⁻¹ a` satisfies `R [a] = [b]` and `[b] - [a] = [δ b]`
    let b : α.generator.domain :=
      ⟨LinearPMap.resolvent α.generator 1 a, LinearPMap.resolvent_mem_domain hδ₁ a⟩
    have hb : (b : A) - α.generator b = a := by
      simpa using LinearPMap.smul_sub_apply_resolvent hδ₁ a
    have hRa : R (f.toPreGNS a) = (f.toPreGNS b : f.GNS) := by
      have := LinearPMap.resolvent_smul_sub_apply h₁
        ⟨_, α.toPreGNS_mem_complexGenerator_domain hf b⟩
      rwa [one_smul, complexGenerator_toPreGNS, ← Completion.coe_sub, ← map_sub, hb] at this
    have hsub : (f.toPreGNS b : f.GNS) - (f.toPreGNS a : f.GNS) =
        (f.toPreGNS (α.generator b) : f.GNS) := by
      rw [← Completion.coe_sub, ← map_sub, ← hb, sub_sub_cancel]
    rw [hRa, hsub, Completion.inner_coe, preGNS_inner_def]
    exact h b

/-- **Positivity of the GNS generator.** The GNS generator `H` of an invariant positive
functional `f` is nonnegative exactly when `f` satisfies the generator inequality
`-i f (a⋆ δ(a)) ≥ 0` for every `a` in the domain of the generator `δ` of the dynamics. -/
theorem forall_inner_gnsStoneGenerator_nonneg_iff :
    (∀ ξ : (α.gnsStoneGenerator hf).domain,
        0 ≤ ⟪(ξ : f.GNS), α.gnsStoneGenerator hf ξ⟫_ℂ) ↔
      ∀ a : α.generator.domain, 0 ≤ -I * f (star (a : A) * α.generator a) := by
  refine ⟨fun h a => ?_, fun h ξ => ?_⟩
  · rw [← α.inner_toPreGNS_gnsStoneGenerator_toPreGNS hf]
    exact h ⟨_, α.toPreGNS_mem_gnsStoneGenerator_domain hf a⟩
  set U := α.gnsStronglyContinuousGroup hf
  have hU := α.isUnitary_gnsStronglyContinuousGroup hf
  set D := U.complexGenerator hU
  have h₁ : (1 : ℂ) ∈ LinearPMap.resolventSet D := by
    simpa only [D, U.complexGenerator_def hU] using
      U.mem_resolventSet_complexGenerator hU.isComplexLinear hU.hasGrowthBound_zero_one
        (z := 1) (by norm_num)
  -- `ξ` is `R ζ` for `ζ = ξ - D ξ`, and then `-i ⟪R ζ, R ζ - ζ⟫ = ⟪ξ, -i D ξ⟫ = ⟪ξ, H ξ⟫`
  have hξ : (ξ : f.GNS) ∈ D.domain := by
    rw [StronglyContinuousGroup.complexGenerator_domain, ← U.stoneGenerator_domain hU]
    exact ξ.property
  have hR := LinearPMap.resolvent_smul_sub_apply h₁ ⟨_, hξ⟩
  rw [one_smul] at hR
  have hH : α.gnsStoneGenerator hf ξ = -I • D ⟨_, hξ⟩ :=
    StronglyContinuousGroup.stoneGenerator_apply U hU ξ
  have := α.neg_I_mul_inner_resolvent_nonneg hf h h₁ ((ξ : f.GNS) - D ⟨_, hξ⟩)
  rwa [hR, sub_sub_cancel, ← inner_smul_right, ← hH] at this

/-- **Ground states have nonnegative GNS generator.** If `ω` is a ground state, then the GNS
generator `H` of `ω` satisfies `⟪ξ, H ξ⟫ ≥ 0` on its domain. -/
theorem IsGroundState.inner_gnsStoneGenerator_nonneg {ω : A →P[ℂ] ℂ} (hω : α.IsGroundState ω)
    (ξ : (α.gnsStoneGenerator (f := ω.toPositiveLinearMap) hω.apply_action).domain) :
    0 ≤ ⟪(ξ : ω.toPositiveLinearMap.GNS), α.gnsStoneGenerator _ ξ⟫_ℂ :=
  (α.forall_inner_gnsStoneGenerator_nonneg_iff _).mpr
    hω.neg_I_mul_apply_star_mul_generator_nonneg ξ

/-- **Ground states are the invariant states with nonnegative GNS generator.** A positive
functional `ω` is a ground state exactly when it has norm one, it is invariant under the
dynamics, and its GNS generator `H` satisfies `⟪ξ, H ξ⟫ ≥ 0` on its domain. -/
theorem isGroundState_iff_exists_forall_inner_gnsStoneGenerator_nonneg {ω : A →P[ℂ] ℂ} :
    α.IsGroundState ω ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 ∧ ∃ hω : ∀ t a, ω (α t a) = ω a,
      ∀ ξ : (α.gnsStoneGenerator (f := ω.toPositiveLinearMap) hω).domain,
        0 ≤ ⟪(ξ : ω.toPositiveLinearMap.GNS), α.gnsStoneGenerator _ ξ⟫_ℂ := by
  refine ⟨fun hω => ⟨hω.norm_eq_one, hω.apply_action, hω.inner_gnsStoneGenerator_nonneg⟩,
    fun ⟨hnorm, hω, h⟩ => ?_⟩
  exact isGroundState_iff_neg_I_mul_apply_star_mul_generator_nonneg.mpr
    ⟨hnorm, (α.forall_inner_gnsStoneGenerator_nonneg_iff hω).mp h⟩

end TauCeti.CStarAction
