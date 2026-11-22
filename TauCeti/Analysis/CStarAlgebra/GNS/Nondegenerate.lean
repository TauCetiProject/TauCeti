/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Unitization
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.Algebra.Algebra.Unitization
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
(`PositiveContinuousLinearMap.tendsto_toGNS_inr_extendUnitization`), so `gnsVector` remains
cyclic (`PositiveContinuousLinearMap.denseRange_gnsInr_gnsVector`) and the restricted GNS
representation `PositiveContinuousLinearMap.gnsInr ω` remains nondegenerate
(`PositiveContinuousLinearMap.isNondegenerate_gnsInr`), while its vector functional at `gnsVector`
recovers `ω` (`PositiveContinuousLinearMap.inner_gnsVector_gnsInr`).

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

/-- The restriction to `A` of the GNS representation of `ω.extendUnitization` on
`ω.extendUnitization.toPositiveLinearMap.GNS`. -/
def gnsInr (ω : A →P[ℂ] ℂ) :
    A →⋆ₙₐ[ℂ]
      (ω.extendUnitization.toPositiveLinearMap.GNS →L[ℂ]
        ω.extendUnitization.toPositiveLinearMap.GNS) :=
  ω.extendUnitization.toPositiveLinearMap.gnsNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

/-- Definitional characterization of `ω.gnsInr` as the restriction of the GNS representation of
`ω.extendUnitization` along `Unitization.inrNonUnitalStarAlgHom ℂ A`. -/
theorem gnsInr_def (ω : A →P[ℂ] ℂ) :
    ω.gnsInr =
      ω.extendUnitization.toPositiveLinearMap.gnsNonUnitalStarAlgHom.comp
        (Unitization.inrNonUnitalStarAlgHom ℂ A) :=
  (rfl)

/-- Evaluation of `ω.gnsInr` at `a : A` as the GNS operator of `(a : Unitization ℂ A)`. -/
@[simp]
theorem gnsInr_apply (ω : A →P[ℂ] ℂ) (a : A) :
    ω.gnsInr a = ω.extendUnitization.toPositiveLinearMap.gnsNonUnitalStarAlgHom (a : A⁺¹) :=
  (rfl)

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
    simp only [f, PositiveContinuousLinearMap.coe_toPositiveLinearMap,
      PositiveContinuousLinearMap.extendUnitization_inr,
      PositiveContinuousLinearMap.extendUnitization_one, smul_eq_mul]
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

/-- The designated GNS vector `gnsVector` of `ω.extendUnitization` is cyclic for the restricted
GNS representation `ω.gnsInr`. -/
theorem denseRange_gnsInr_gnsVector (ω : A →P[ℂ] ℂ) :
    DenseRange (fun a : A => ω.gnsInr a ω.extendUnitization.toPositiveLinearMap.gnsVector) := by
  set f := ω.extendUnitization.toPositiveLinearMap
  have heq : (fun a : A => ω.gnsInr a f.gnsVector) = fun a : A => f.toGNS (a : A⁺¹) := by
    ext a
    rw [gnsInr_apply, f.gnsNonUnitalStarAlgHom_apply_gnsVector, PositiveLinearMap.toGNS_apply]
  rw [heq, denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro ξ
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hx : ∀ x : A⁺¹, f.toGNS x ∈ closure (Set.range fun a : A => f.toGNS (a : A⁺¹)) := fun x => by
    have hlim : Tendsto (fun e : A => f.toGNS ((x.fst • e + x.snd : A) : A⁺¹))
        (CStarAlgebra.approximateUnit A) (𝓝 (f.toGNS x)) := by
      have h' := ((ω.tendsto_toGNS_inr_extendUnitization hl).const_smul x.fst).add
        (tendsto_const_nhds (x := f.toGNS (x.snd : A⁺¹)))
      have hlin : (fun e : A => f.toGNS ((x.fst • e + x.snd : A) : A⁺¹)) =
          fun e : A => x.fst • f.toGNS (e : A⁺¹) + f.toGNS (x.snd : A⁺¹) := by
        ext e
        rw [Unitization.inr_add, Unitization.inr_smul, map_add, map_smul]
      rw [hlin]
      have hlim_eq : x.fst • f.gnsVector + f.toGNS (x.snd : A⁺¹) = f.toGNS x := by
        rw [PositiveLinearMap.gnsVector_def, ← PositiveLinearMap.toGNS_apply, ← map_smul, ← map_add,
          Unitization.fst_smul_one_add_inr_snd]
      rwa [hlim_eq] at h'
    exact mem_closure_of_tendsto hlim (.of_forall fun e => ⟨x.fst • e + x.snd, rfl⟩)
  exact f.denseRange_toGNS.induction_on ξ isClosed_closure hx

/-- Restricting the GNS representation of `ω.extendUnitization` to `A` yields a nondegenerate
representation on `ω.extendUnitization.toPositiveLinearMap.GNS`. -/
theorem isNondegenerate_gnsInr (ω : A →P[ℂ] ℂ) : ω.gnsInr.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense]
  refine ω.denseRange_gnsInr_gnsVector.mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span <| Set.mem_iUnion.mpr ⟨a, _, rfl⟩

/-- In the restricted GNS representation `ω.gnsInr`, the vector functional at `gnsVector` recovers
`ω`. -/
theorem inner_gnsVector_gnsInr (ω : A →P[ℂ] ℂ) (b : A) :
    ⟪ω.extendUnitization.toPositiveLinearMap.gnsVector,
      ω.gnsInr b ω.extendUnitization.toPositiveLinearMap.gnsVector⟫_ℂ = ω b := by
  rw [gnsInr_apply, PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector,
    PositiveLinearMap.inner_gnsVector_coe,
    PositiveContinuousLinearMap.coe_toPositiveLinearMap,
    ω.extendUnitization_inr]

end PositiveContinuousLinearMap

end
