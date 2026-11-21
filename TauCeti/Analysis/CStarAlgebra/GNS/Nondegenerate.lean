/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Unitization
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Basic

/-!
# Nondegeneracy and faithfulness of GNS representations

The GNS representation of every positive functional on a possibly nonunital C⋆-algebra is
nondegenerate, and its multiplier extension acts on classes `[b]` as `[m.fst b]`
(`PositiveLinearMap.multiplierExtension_gnsNonUnitalStarAlgHom_toGNS`). If the functional is
faithful, in the sense that `f (a⋆a) = 0` forces `a = 0`, its GNS representation is injective.
These results allow faithful positive functionals to produce faithful nondegenerate representations
without assuming a unit or a canonical cyclic vector.

For a positive continuous linear functional `ω : A →P[ℂ] ℂ` extended canonically to
`Unitization ℂ A`, the GNS classes `[e]` along any increasing approximate unit `e` of `A` converge
in norm to the cyclic vector `[1]` of `ω.extendUnitization`
(`PositiveContinuousLinearMap.tendsto_toGNS_inr_extendUnitization`), so restricting the GNS
representation of `ω.extendUnitization` to `A` remains nondegenerate
(`PositiveContinuousLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom_extendUnitization_comp_inr`),
and its vector functional at `gnsVector` recovers `ω`
(`PositiveContinuousLinearMap.inner_gnsVector_gnsNonUnitalStarAlgHom_extendUnitization_comp_inr`).

The zero functional is included: its GNS Hilbert space is zero and the representation is
still nondegenerate. Faithfulness is sufficient, not necessary, for injectivity of the GNS
representation.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

noncomputable section

open Filter Topology Unitization
open scoped CStarAlgebra ComplexOrder InnerProductSpace MultiplierAlgebra

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The GNS representation is nondegenerate, also when the algebra has no unit. -/
theorem isNondegenerate_gnsNonUnitalStarAlgHom (f : A →ₚ[ℂ] ℂ) :
    f.gnsNonUnitalStarAlgHom.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense]
  intro ξ
  refine f.denseRange_toGNS.induction_on ξ isClosed_closure fun a => ?_
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  refine mem_closure_of_tendsto
    (f.toGNS.continuous.tendsto a |>.comp (hl.tendsto_mul_right a)) ?_
  exact .of_forall fun e => Submodule.subset_span <|
    Set.mem_iUnion.mpr ⟨e, f.toGNS a, by simp⟩

/-- The multiplier extension of the GNS representation sends `f.toGNS b` to `f.toGNS (m.fst b)`. -/
theorem multiplierExtension_gnsNonUnitalStarAlgHom_toGNS (f : A →ₚ[ℂ] ℂ) (m : 𝓜(ℂ, A)) (b : A) :
    f.gnsNonUnitalStarAlgHom.multiplierExtension f.isNondegenerate_gnsNonUnitalStarAlgHom m
      (f.toGNS b) = f.toGNS (m.fst b) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hcont : Continuous fun x : A => f.toGNS (m.fst x) := by fun_prop
  exact tendsto_nhds_unique (f.gnsNonUnitalStarAlgHom.tendsto_multiplierExtension_apply
    f.isNondegenerate_gnsNonUnitalStarAlgHom hl.eventually_norm hl.tendsto_mul_right m (f.toGNS b))
    (((hcont.tendsto b).comp (hl.tendsto_mul_right b)).congr fun e => by
      simp [DoubleCentralizer.fst_mul])

/-- On representatives `f.toPreGNS b`, the multiplier extension of the GNS representation acts as
`f.toPreGNS (m.fst b)`. -/
@[simp]
theorem multiplierExtension_gnsNonUnitalStarAlgHom_apply_coe (f : A →ₚ[ℂ] ℂ) (m : 𝓜(ℂ, A))
    (b : A) :
    f.gnsNonUnitalStarAlgHom.multiplierExtension f.isNondegenerate_gnsNonUnitalStarAlgHom m
      (f.toPreGNS b : f.GNS) = (f.toPreGNS (m.fst b) : f.GNS) := by
  simpa only [toGNS_apply] using f.multiplierExtension_gnsNonUnitalStarAlgHom_toGNS m b

/-- A faithful positive functional has an injective GNS representation. No unit or
normalization is needed. -/
theorem gnsNonUnitalStarAlgHom_injective (f : A →ₚ[ℂ] ℂ)
    (hf : ∀ a, f (star a * a) = 0 → a = 0) :
    Function.Injective f.gnsNonUnitalStarAlgHom := by
  have hclass : Function.Injective f.toGNS :=
    (injective_iff_map_eq_zero f.toGNS).mpr fun a ha => hf a ((f.toGNS_eq_zero_iff a).mp ha)
  refine (injective_iff_map_eq_zero f.gnsNonUnitalStarAlgHom).mpr fun a ha => ?_
  have hzero : f.toGNS (a * star a) = 0 := by
    simpa [toGNS_apply] using DFunLike.congr_fun ha (f.toGNS (star a))
  have hmul : a * star a = 0 := hclass (by simpa using hzero)
  exact mul_star_self_eq_zero.mp hmul

end PositiveLinearMap

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Along any increasing approximate unit `e` of `A`, the GNS classes `[e]` converge in norm to
the cyclic GNS vector `[1]` of `ω.extendUnitization`. -/
theorem tendsto_toGNS_inr_extendUnitization (ω : A →P[ℂ] ℂ) {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e : A => ω.extendUnitization.toPositiveLinearMap.toGNS (e : Unitization ℂ A)) l
      (𝓝 ω.extendUnitization.toPositiveLinearMap.gnsVector) := by
  set f := ω.extendUnitization.toPositiveLinearMap
  rw [tendsto_iff_norm_sub_tendsto_zero]
  suffices hsq : Tendsto (fun e : A => ‖f.toGNS (e : A⁺¹) - f.gnsVector‖ ^ 2) l (𝓝 0) by
    have h := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Real.sqrt_zero, Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h
  have hval : ∀ᶠ e : A in l,
      (‖f.toGNS (e : A⁺¹) - f.gnsVector‖ ^ 2 : ℂ) =
        ω (e * e) - 2 * ω e + (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
    filter_upwards [hl.eventually_nonneg] with e he
    have hdiff : f.toGNS (e : A⁺¹) - f.gnsVector = f.toGNS ((e : A⁺¹) - 1) := by
      simp only [map_sub, PositiveLinearMap.gnsVector_def, PositiveLinearMap.toGNS_apply]
    rw [hdiff, f.norm_toGNS_sq]
    have hstar : star ((e : A⁺¹) - 1) = (e : A⁺¹) - 1 := by
      rw [star_sub, star_one, ← Unitization.inr_star, he.isSelfAdjoint.star_eq]
    rw [hstar]
    have hexp : ((e : A⁺¹) - 1) * ((e : A⁺¹) - 1) =
        ((e * e : A) : A⁺¹) - (2 : ℂ) • (e : A⁺¹) + 1 := by
      rw [Unitization.inr_mul, two_smul]
      noncomm_ring
    rw [hexp, map_add, map_sub, map_smul]
    simp [f]
  have hlimC : Tendsto (fun e : A => (‖f.toGNS (e : A⁺¹) - f.gnsVector‖ ^ 2 : ℂ)) l (𝓝 0) := by
    refine Tendsto.congr' (hval.mono fun _ h => h.symm) ?_
    have h := ((ω.tendsto_mul_self_nhds_opNorm hl).sub
      ((ω.tendsto_nhds_opNorm hl).const_mul 2)).add
      (tendsto_const_nhds (x := (‖(ω : A →L[ℂ] ℂ)‖ : ℂ)))
    have h0 : (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) - 2 * ↑‖(ω : A →L[ℂ] ℂ)‖ + ↑‖(ω : A →L[ℂ] ℂ)‖ = 0 := by
      ring
    rwa [h0] at h
  simpa [Function.comp_def, ← Complex.ofReal_pow] using
    (Complex.continuous_re.tendsto 0).comp hlimC

/-- Restricting the GNS representation of `ω.extendUnitization` to `A` yields a nondegenerate
representation on `ω.extendUnitization.toPositiveLinearMap.GNS`. -/
theorem isNondegenerate_gnsNonUnitalStarAlgHom_extendUnitization_comp_inr (ω : A →P[ℂ] ℂ) :
    (ω.extendUnitization.toPositiveLinearMap.gnsNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)).IsNondegenerate := by
  set f := ω.extendUnitization.toPositiveLinearMap
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_forall_apply_eq_zero]
  intro ξ hξ
  have hinner_inr : ∀ a : A, ⟪f.toGNS (a : A⁺¹), ξ⟫_ℂ = 0 := fun a => by
    have h := hξ (star a)
    simp only [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply] at h
    rw [PositiveLinearMap.toGNS_apply, ← f.gnsNonUnitalStarAlgHom_apply_gnsVector,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, ← Unitization.inr_star, h, inner_zero_right]
  have hinner_one : ⟪f.gnsVector, ξ⟫_ℂ = 0 := by
    have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have hlim := ((innerSL ℂ ξ).continuous.tendsto _).comp
      (ω.tendsto_toGNS_inr_extendUnitization hl)
    have hlim' : Tendsto (fun e : A => ⟪f.toGNS (e : A⁺¹), ξ⟫_ℂ)
        (CStarAlgebra.approximateUnit A) (𝓝 ⟪f.gnsVector, ξ⟫_ℂ) := by
      have hconj := (continuous_star.tendsto _).comp hlim
      simpa [Function.comp_def] using hconj
    exact tendsto_nhds_unique hlim' <|
      (tendsto_const_nhds (x := (0 : ℂ))).congr fun e => (hinner_inr e).symm
  have hinner_all : ∀ x : A⁺¹, ⟪f.toGNS x, ξ⟫_ℂ = 0 := fun x => by
    nth_rw 1 [← Unitization.inl_fst_add_inr_snd_eq x]
    have hinl : Unitization.inl x.fst = x.fst • (1 : A⁺¹) := by
      rw [← Unitization.algebraMap_eq_inl, Algebra.algebraMap_eq_smul_one]
    rw [hinl, map_add, map_smul, inner_add_left, inner_smul_left,
      PositiveLinearMap.toGNS_apply, ← PositiveLinearMap.gnsVector_def, hinner_one,
      hinner_inr, mul_zero, add_zero]
  refine ext_inner_left ℂ fun η => ?_
  rw [inner_zero_right]
  refine f.denseRange_toGNS.induction_on η ?_ hinner_all
  exact isClosed_eq ((continuous_star.comp (innerSL ℂ ξ).continuous).congr fun v => by simp)
    continuous_const

/-- In the restricted GNS representation of `ω.extendUnitization`, the vector functional at
`gnsVector` recovers `ω`. -/
theorem inner_gnsVector_gnsNonUnitalStarAlgHom_extendUnitization_comp_inr (ω : A →P[ℂ] ℂ)
    (b : A) :
    ⟪ω.extendUnitization.toPositiveLinearMap.gnsVector,
      (ω.extendUnitization.toPositiveLinearMap.gnsNonUnitalStarAlgHom.comp
        (Unitization.inrNonUnitalStarAlgHom ℂ A)) b
        ω.extendUnitization.toPositiveLinearMap.gnsVector⟫_ℂ = ω b := by
  rw [NonUnitalStarAlgHom.comp_apply, Unitization.inrNonUnitalStarAlgHom_apply,
    PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector,
    PositiveLinearMap.inner_gnsVector_coe,
    PositiveContinuousLinearMap.coe_toPositiveLinearMap,
    ω.extendUnitization_inr]

end PositiveContinuousLinearMap

end
