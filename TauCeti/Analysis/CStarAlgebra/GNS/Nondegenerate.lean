/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# Nondegeneracy and faithfulness of GNS representations

The GNS representation of every positive functional on a possibly nonunital C⋆-algebra is
nondegenerate, and its multiplier extension acts on classes `[b]` as `[m.fst b]`
(`PositiveLinearMap.multiplierExtension_gnsNonUnitalStarAlgHom_toGNS`). If the functional is
faithful, in the sense that `f (a⋆a) = 0` forces `a = 0`, its GNS representation is injective.
These results allow faithful positive functionals to produce faithful nondegenerate representations
without assuming a unit or a canonical cyclic vector.

The zero functional is included: its GNS Hilbert space is zero and the representation is
still nondegenerate. Faithfulness is sufficient, not necessary, for injectivity of the GNS
representation.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra ComplexOrder MultiplierAlgebra

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

end
