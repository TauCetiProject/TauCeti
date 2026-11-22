/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.LocallyConvex.WeakDual.SelfAdjoint
public import TauCeti.Analysis.Normed.Order.OrderUnit.State

/-!
# Correspondence between C⋆-algebra states and order-unit states

For a unital C⋆-algebra `A`, its self-adjoint part `selfAdjoint A` is a real order-unit space
with order unit `1`, and restriction of complex-linear functionals to `selfAdjoint A` induces a
weak-star homeomorphism between the C⋆-algebra state space `TauCeti.stateSpace A` and the
order-unit state space `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`.

## Main definitions and results

* `TauCeti.OrderUnit.mapsTo_restrictToSelfAdjoint_stateSpace`,
  `TauCeti.OrderUnit.mapsTo_extendFromSelfAdjoint_stateSpace`: restriction and complex-linear
  extension preserve state spaces.
* `TauCeti.OrderUnit.extendFromSelfAdjoint_restrictToSelfAdjoint_of_mem_stateSpace`: every
  C⋆-algebra state is recovered by extending its restriction to `selfAdjoint A`.
* `TauCeti.OrderUnit.cstarStateSpaceHomeomorph`: weak-star homeomorphism between
  `TauCeti.stateSpace A` and `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`.
* `TauCeti.OrderUnit.cstarPositiveLinearMapEquivStateSpace`: bijection between normalized positive
  continuous complex-linear functionals `{ω : A →P[ℂ] ℂ // ω 1 = 1}` and
  `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set WeakDual
open scoped ComplexOrder ComplexStarModule

namespace TauCeti.OrderUnit

/-! ### Correspondence with states of a unital C⋆-algebra -/

section CStarCorrespondence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Restricting a C⋆-algebra state to `selfAdjoint A` yields an order-unit state. -/
theorem mapsTo_restrictToSelfAdjoint_stateSpace :
    MapsTo (restrictToSelfAdjoint (A := A))
      (TauCeti.stateSpace A) (stateSpace (1 : selfAdjoint A)) := by
  intro φ hφ
  rw [mem_stateSpace_iff_map_nonneg]
  refine ⟨fun a ha => ?_, ?_⟩
  · have hpos : 0 ≤ φ (a : A) := TauCeti.map_nonneg_of_mem_stateSpace hφ ha
    simpa using (Complex.le_def.mp hpos).1
  · simp [TauCeti.map_one_of_mem_stateSpace hφ]

/-- Extending an order-unit state of `selfAdjoint A` by complex linearity yields a C⋆-algebra
state of `A`. -/
theorem mapsTo_extendFromSelfAdjoint_stateSpace :
    MapsTo (extendFromSelfAdjoint (A := A))
      (stateSpace (1 : selfAdjoint A)) (TauCeti.stateSpace A) := by
  intro ψ hψ
  rw [TauCeti.mem_stateSpace_iff_map_one]
  refine ⟨fun a ha => ?_, ?_⟩
  · let a' : selfAdjoint A := ⟨a, IsSelfAdjoint.of_nonneg ha⟩
    have ha' : (0 : selfAdjoint A) ≤ a' := ha
    have hre : ℜ a = a' := selfAdjoint.realPart_coe (x := a')
    have him : ℑ a = 0 := selfAdjoint.imaginaryPart_coe (x := a')
    rw [extendFromSelfAdjoint_apply, hre, him, map_zero, Complex.ofReal_zero, mul_zero, add_zero]
    exact Complex.le_def.mpr ⟨map_nonneg_of_mem_stateSpace hψ ha', rfl⟩
  · have hre : ℜ (1 : A) = (1 : selfAdjoint A) :=
      selfAdjoint.realPart_coe (x := (1 : selfAdjoint A))
    have him : ℑ (1 : A) = 0 := selfAdjoint.imaginaryPart_coe (x := (1 : selfAdjoint A))
    rw [extendFromSelfAdjoint_apply, hre, him, map_zero, Complex.ofReal_zero, mul_zero, add_zero,
      map_unit_of_mem_stateSpace hψ, Complex.ofReal_one]

/-- On any C⋆-algebra state `φ`, extending the restriction to `selfAdjoint A` recovers `φ`. -/
theorem extendFromSelfAdjoint_restrictToSelfAdjoint_of_mem_stateSpace {φ : WeakDual ℂ A}
    (hφ : φ ∈ TauCeti.stateSpace A) :
    extendFromSelfAdjoint (restrictToSelfAdjoint φ) = φ := by
  refine extendFromSelfAdjoint_restrictToSelfAdjoint fun a => ?_
  let ω : A →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun _ => TauCeti.map_nonneg_of_mem_stateSpace hφ
  have hstar : star (ω (a : A)) = ω (a : A) := by
    rw [← map_star, a.2.star_eq]
  exact Complex.conj_eq_iff_im.mp hstar

/-- **C⋆-algebra state correspondence.** Restriction to `selfAdjoint A` and complex-linear
extension define a weak-star homeomorphism between `TauCeti.stateSpace A` and
`OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
noncomputable def cstarStateSpaceHomeomorph :
    TauCeti.stateSpace A ≃ₜ stateSpace (1 : selfAdjoint A) where
  toFun φ := ⟨restrictToSelfAdjoint φ.1, mapsTo_restrictToSelfAdjoint_stateSpace φ.2⟩
  invFun ψ := ⟨extendFromSelfAdjoint ψ.1, mapsTo_extendFromSelfAdjoint_stateSpace ψ.2⟩
  left_inv φ := Subtype.ext (extendFromSelfAdjoint_restrictToSelfAdjoint_of_mem_stateSpace φ.2)
  right_inv ψ := Subtype.ext (restrictToSelfAdjoint_extendFromSelfAdjoint ψ.1)
  continuous_toFun :=
    (restrictToSelfAdjoint.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (extendFromSelfAdjoint.continuous.comp continuous_subtype_val).subtype_mk _

/-- Evaluating `cstarStateSpaceHomeomorph` takes the real part on self-adjoint elements. -/
@[simp]
theorem cstarStateSpaceHomeomorph_apply (φ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateSpaceHomeomorph φ).1 a = (φ.1 (a : A)).re := by
  simp [cstarStateSpaceHomeomorph]

/-- Evaluating the inverse of `cstarStateSpaceHomeomorph` recovers the complex-linear extension. -/
@[simp]
theorem cstarStateSpaceHomeomorph_symm_apply (ψ : stateSpace (1 : selfAdjoint A)) (a : A) :
    (cstarStateSpaceHomeomorph.symm ψ).1 a = (ψ.1 (ℜ a) : ℂ) + Complex.I * (ψ.1 (ℑ a) : ℂ) := by
  simp [cstarStateSpaceHomeomorph]

/-- The bijection between normalized positive continuous complex-linear functionals
`{ω : A →P[ℂ] ℂ // ω 1 = 1}` and `OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
noncomputable def cstarPositiveLinearMapEquivStateSpace :
    {ω : A →P[ℂ] ℂ // ω 1 = 1} ≃ stateSpace (1 : selfAdjoint A) where
  toFun ω := cstarStateSpaceHomeomorph
    ⟨StrongDual.toWeakDual (ω.1 : A →L[ℂ] ℂ),
      TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ ha => ω.1.map_nonneg ha, ω.2⟩⟩
  invFun ψ :=
    let φ := cstarStateSpaceHomeomorph.symm ψ
    ⟨PositiveContinuousLinearMap.mk₀ (toStrongDual φ.1)
      (fun _ ha => TauCeti.map_nonneg_of_mem_stateSpace φ.2 ha),
      TauCeti.map_one_of_mem_stateSpace φ.2⟩
  left_inv ω := by
    refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    have h := congrArg (fun x : TauCeti.stateSpace A => x.1 a)
      (cstarStateSpaceHomeomorph.left_inv
        ⟨StrongDual.toWeakDual (ω.1 : A →L[ℂ] ℂ),
          TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ ha => ω.1.map_nonneg ha, ω.2⟩⟩)
    exact h
  right_inv ψ := by
    refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    have h := congrArg (fun x : stateSpace (1 : selfAdjoint A) => x.1 a)
      (cstarStateSpaceHomeomorph.right_inv ψ)
    exact h

/-- Evaluating `cstarPositiveLinearMapEquivStateSpace` restricts `ω` to `selfAdjoint A`. -/
@[simp]
theorem cstarPositiveLinearMapEquivStateSpace_apply (ω : {ω : A →P[ℂ] ℂ // ω 1 = 1})
    (a : selfAdjoint A) :
    (cstarPositiveLinearMapEquivStateSpace ω).1 a = (ω.1 (a : A)).re := by
  simp [cstarPositiveLinearMapEquivStateSpace]

/-- Evaluating the inverse of `cstarPositiveLinearMapEquivStateSpace` gives the complex-linear
extension of `ψ`. -/
@[simp]
theorem cstarPositiveLinearMapEquivStateSpace_symm_apply (ψ : stateSpace (1 : selfAdjoint A))
    (a : A) :
    (cstarPositiveLinearMapEquivStateSpace.symm ψ).1 a =
      (ψ.1 (ℜ a) : ℂ) + Complex.I * (ψ.1 (ℑ a) : ℂ) :=
  cstarStateSpaceHomeomorph_symm_apply ψ a

end CStarCorrespondence

end TauCeti.OrderUnit
