/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Adjointable operators on complex Hilbert spaces

When the coefficient algebra is `A = ℂ`, a complex Hilbert space `H` is a Hilbert C⋆-module over
`ℂ` via `WithCStarModule.instCStarModuleComplex`, and every continuous linear map `H →L[ℂ] F`
between complex Hilbert spaces is adjointable. This file constructs the isometric `ℂ`-linear
equivalence `L_ℂ(H, F) ≃ₗᵢ[ℂ] (H →L[ℂ] F)` (`equivContinuousLinearMapComplex`) and the isometric
`⋆`-algebra isomorphism `L_ℂ(H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` (`starAlgEquivContinuousLinearMapComplex`),
together with compatibility with adjoints, operator norm, and the Loewner / spectral orders.

## Main declarations

* `TauCeti.AdjointableMap.equivContinuousLinearMapComplex`: isometric `ℂ`-linear equivalence
  `AdjointableMap ℂ H F ≃ₗᵢ[ℂ] (H →L[ℂ] F)`.
* `TauCeti.AdjointableMap.starAlgEquivContinuousLinearMapComplex`: `⋆`-algebra isomorphism
  `AdjointableMap ℂ H H ≃⋆ₐ[ℂ] (H →L[ℂ] H)`, isometric via
  `norm_starAlgEquivContinuousLinearMapComplex` and order-preserving via
  `starAlgEquivContinuousLinearMapComplex_le_iff`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

namespace TauCeti

namespace AdjointableMap

section ComplexHilbertSpace

open ComplexOrder

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- On complex Hilbert spaces (viewed as `CStarModule ℂ` via
`WithCStarModule.instCStarModuleComplex`), every continuous linear map is adjointable, giving an
isometric `ℂ`-linear equivalence `L_ℂ(H, F) ≃ₗᵢ[ℂ] (H →L[ℂ] F)`. -/
noncomputable def equivContinuousLinearMapComplex :
    AdjointableMap ℂ H F ≃ₗᵢ[ℂ] (H →L[ℂ] F) :=
  LinearIsometryEquiv.ofLinearIsometry
    toContinuousLinearMapₗᵢ
    { toFun := fun f =>
        ⟨f, ContinuousLinearMap.adjoint f,
          fun x y => (ContinuousLinearMap.adjoint_inner_right f x y).symm⟩
      map_add' := fun _ _ => ext fun _ => by simp
      map_smul' := fun _ _ => ext fun _ => by simp }
    (LinearMap.ext fun _ => by simp)
    (LinearMap.ext fun _ => ext fun _ => by simp)

@[simp]
theorem equivContinuousLinearMapComplex_apply (T : AdjointableMap ℂ H F) :
    equivContinuousLinearMapComplex T = T.toContinuousLinearMap :=
  toContinuousLinearMapₗᵢ_apply T

@[simp]
theorem equivContinuousLinearMapComplex_symm_apply (f : H →L[ℂ] F) (x : H) :
    equivContinuousLinearMapComplex.symm f x = f x := (rfl)

@[simp]
theorem adjoint_equivContinuousLinearMapComplex_symm (f : H →L[ℂ] F) :
    (equivContinuousLinearMapComplex.symm f).adjoint =
      equivContinuousLinearMapComplex.symm (ContinuousLinearMap.adjoint f) :=
  ext fun x => by
    rw [← toContinuousLinearMap_apply (equivContinuousLinearMapComplex.symm f).adjoint,
      ← adjoint'_eq]
    rfl

/-- For a complex Hilbert space `H`, `L_ℂ(H)` is `⋆`-isomorphic to `H →L[ℂ] H`. Its underlying map
agrees with `equivContinuousLinearMapComplex`, so it is isometric
(`norm_starAlgEquivContinuousLinearMapComplex`) and preserves positivity and the Loewner order
(`starAlgEquivContinuousLinearMapComplex_nonneg_iff`,
`starAlgEquivContinuousLinearMapComplex_le_iff`). -/
noncomputable def starAlgEquivContinuousLinearMapComplex :
    AdjointableMap ℂ H H ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
  StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.ofLinearEquiv equivContinuousLinearMapComplex.toLinearEquiv
      (by simp) (by simp))
    fun T => ContinuousLinearMap.ext fun y => CStarModule.ext_inner_left (A := ℂ) fun x => by
      simp only [AlgEquiv.ofLinearEquiv_apply, LinearIsometryEquiv.coe_toLinearEquiv,
        equivContinuousLinearMapComplex_apply, star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
      exact (T.adjoint_inner_right x y).trans
        (ContinuousLinearMap.adjoint_inner_right T.toContinuousLinearMap x y).symm

@[simp]
theorem starAlgEquivContinuousLinearMapComplex_apply (T : AdjointableMap ℂ H H) :
    starAlgEquivContinuousLinearMapComplex T = T.toContinuousLinearMap :=
  equivContinuousLinearMapComplex_apply T

@[simp]
theorem starAlgEquivContinuousLinearMapComplex_symm_apply (f : H →L[ℂ] H) (x : H) :
    starAlgEquivContinuousLinearMapComplex.symm f x = f x := (rfl)

theorem norm_starAlgEquivContinuousLinearMapComplex (T : AdjointableMap ℂ H H) :
    ‖starAlgEquivContinuousLinearMapComplex T‖ = ‖T‖ := by
  rw [starAlgEquivContinuousLinearMapComplex_apply, norm_toContinuousLinearMap]

/-- On a complex Hilbert space `H`, `T ∈ L_ℂ(H)` is positive in the spectral order if and only if
its underlying bounded operator `T.toContinuousLinearMap` is positive in the Loewner order. -/
@[simp]
theorem toContinuousLinearMap_nonneg_iff (T : AdjointableMap ℂ H H) :
    0 ≤ T.toContinuousLinearMap ↔ 0 ≤ T := by
  refine ⟨fun h => nonneg_iff_forall_inner_nonneg.mpr fun x =>
      (ContinuousLinearMap.nonneg_iff_isPositive.mp h).inner_nonneg_right x, fun hT => ?_⟩
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff']
  refine ⟨by
      simpa only [starAlgEquivContinuousLinearMapComplex_apply] using
        hT.isSelfAdjoint.map starAlgEquivContinuousLinearMapComplex, fun x => ?_⟩
  rw [toContinuousLinearMap_apply, (isSelfAdjoint_iff_forall_inner_eq T).mp hT.isSelfAdjoint x x]
  exact nonneg_iff_forall_inner_nonneg.mp hT x

/-- On a complex Hilbert space `H`, the forgetful map `L_ℂ(H) → (H →L[ℂ] H)` preserves and reflects
the spectral / Loewner partial orders. -/
@[simp]
theorem toContinuousLinearMap_le_iff (S T : AdjointableMap ℂ H H) :
    S.toContinuousLinearMap ≤ T.toContinuousLinearMap ↔ S ≤ T := by
  rw [← sub_nonneg, ← toContinuousLinearMap_sub, toContinuousLinearMap_nonneg_iff, sub_nonneg]

/-- The `⋆`-isomorphism `L_ℂ(H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` identifies the spectral order on `L_ℂ(H)`
with positivity (`ContinuousLinearMap.IsPositive`) on `H →L[ℂ] H`. -/
theorem starAlgEquivContinuousLinearMapComplex_nonneg_iff (T : AdjointableMap ℂ H H) :
    0 ≤ starAlgEquivContinuousLinearMapComplex T ↔ 0 ≤ T := by
  simp

/-- The `⋆`-isomorphism `L_ℂ(H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` preserves and reflects the spectral / Loewner
partial orders. -/
theorem starAlgEquivContinuousLinearMapComplex_le_iff (S T : AdjointableMap ℂ H H) :
    starAlgEquivContinuousLinearMapComplex S ≤ starAlgEquivContinuousLinearMapComplex T ↔
      S ≤ T := by
  simp

end ComplexHilbertSpace

end AdjointableMap

end TauCeti
