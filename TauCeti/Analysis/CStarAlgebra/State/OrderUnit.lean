/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.LocallyConvex.WeakDual.SelfAdjoint
public import TauCeti.Analysis.Normed.Order.OrderUnit.State.Basic

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
* `TauCeti.OrderUnit.cstarStateSpaceHomeomorph`,
  `TauCeti.OrderUnit.cstarStateSpaceHomeomorph_convexCombo`,
  `TauCeti.OrderUnit.cstarStateSpaceHomeomorph_symm_convexCombo`: weak-star homeomorphism between
  `TauCeti.stateSpace A` and `TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`, preserving convex
  combinations.
* `TauCeti.OrderUnit.cstarPositiveContinuousLinearMapEquivStateSpace`: bijection between normalized
  positive continuous complex-linear functionals `{ω : A →P[ℂ] ℂ // ω 1 = 1}` and
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
    rw [show a = (a' : A) from rfl, extendFromSelfAdjoint_apply_coe]
    exact Complex.le_def.mpr ⟨map_nonneg_of_mem_stateSpace hψ ha', rfl⟩
  · rw [show (1 : A) = ((1 : selfAdjoint A) : A) from rfl, extendFromSelfAdjoint_apply_coe,
      map_unit_of_mem_stateSpace hψ, Complex.ofReal_one]

/-- On any C⋆-algebra state `φ`, extending the restriction to `selfAdjoint A` recovers `φ`. -/
theorem extendFromSelfAdjoint_restrictToSelfAdjoint_of_mem_stateSpace {φ : WeakDual ℂ A}
    (hφ : φ ∈ TauCeti.stateSpace A) :
    extendFromSelfAdjoint (restrictToSelfAdjoint φ) = φ := by
  refine extendFromSelfAdjoint_restrictToSelfAdjoint fun a => ?_
  let ω : A →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun _ => TauCeti.map_nonneg_of_mem_stateSpace hφ
  have hstar : star (ω (a : A)) = ω (a : A) := by
    rw [← map_star, a.property.star_eq]
  exact Complex.conj_eq_iff_im.mp hstar

/-- **C⋆-algebra state correspondence.** Restriction to `selfAdjoint A` and complex-linear
extension define a weak-star homeomorphism between `TauCeti.stateSpace A` and
`OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
noncomputable def cstarStateSpaceHomeomorph :
    TauCeti.stateSpace A ≃ₜ stateSpace (1 : selfAdjoint A) where
  toFun φ := ⟨restrictToSelfAdjoint φ.val, mapsTo_restrictToSelfAdjoint_stateSpace φ.property⟩
  invFun ψ := ⟨extendFromSelfAdjoint ψ.val, mapsTo_extendFromSelfAdjoint_stateSpace ψ.property⟩
  left_inv φ :=
    Subtype.ext (extendFromSelfAdjoint_restrictToSelfAdjoint_of_mem_stateSpace φ.property)
  right_inv ψ := Subtype.ext (restrictToSelfAdjoint_extendFromSelfAdjoint ψ.val)
  continuous_toFun :=
    (restrictToSelfAdjoint.continuous.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun :=
    (extendFromSelfAdjoint.continuous.comp continuous_subtypeVal).subtype_mk _

/-- Evaluating `cstarStateSpaceHomeomorph` takes the real part on self-adjoint elements. -/
@[simp]
theorem cstarStateSpaceHomeomorph_apply (φ : TauCeti.stateSpace A) (a : selfAdjoint A) :
    (cstarStateSpaceHomeomorph φ).val a = (φ.val (a : A)).re := by
  simp [cstarStateSpaceHomeomorph]

/-- Evaluating the inverse of `cstarStateSpaceHomeomorph` recovers the complex-linear extension. -/
@[simp]
theorem cstarStateSpaceHomeomorph_symm_apply (ψ : stateSpace (1 : selfAdjoint A)) (a : A) :
    (cstarStateSpaceHomeomorph.symm ψ).val a =
      (ψ.val (ℜ a) : ℂ) + Complex.I * (ψ.val (ℑ a) : ℂ) := by
  simp [cstarStateSpaceHomeomorph]

/-- `cstarStateSpaceHomeomorph` preserves convex combinations of states. -/
theorem cstarStateSpaceHomeomorph_convexCombo {φ₁ φ₂ : TauCeti.stateSpace A}
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    cstarStateSpaceHomeomorph
        ⟨s • φ₁.val + t • φ₂.val, TauCeti.convex_stateSpace φ₁.property φ₂.property hs ht hst⟩ =
      ⟨s • (cstarStateSpaceHomeomorph φ₁).val + t • (cstarStateSpaceHomeomorph φ₂).val,
        convex_stateSpace (cstarStateSpaceHomeomorph φ₁).property
          (cstarStateSpaceHomeomorph φ₂).property hs ht hst⟩ :=
  Subtype.ext (by simp [cstarStateSpaceHomeomorph])

/-- The inverse of `cstarStateSpaceHomeomorph` preserves convex combinations of states. -/
theorem cstarStateSpaceHomeomorph_symm_convexCombo
    {ψ₁ ψ₂ : stateSpace (1 : selfAdjoint A)} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) :
    cstarStateSpaceHomeomorph.symm
        ⟨s • ψ₁.val + t • ψ₂.val, convex_stateSpace ψ₁.property ψ₂.property hs ht hst⟩ =
      ⟨s • (cstarStateSpaceHomeomorph.symm ψ₁).val +
          t • (cstarStateSpaceHomeomorph.symm ψ₂).val,
        TauCeti.convex_stateSpace (cstarStateSpaceHomeomorph.symm ψ₁).property
          (cstarStateSpaceHomeomorph.symm ψ₂).property hs ht hst⟩ :=
  Subtype.ext (by simp [cstarStateSpaceHomeomorph])

/-- The bijection between normalized positive continuous complex-linear functionals
`{ω : A →P[ℂ] ℂ // ω 1 = 1}` and `OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
noncomputable def cstarPositiveContinuousLinearMapEquivStateSpace :
    {ω : A →P[ℂ] ℂ // ω 1 = 1} ≃ stateSpace (1 : selfAdjoint A) where
  toFun ω := cstarStateSpaceHomeomorph
    ⟨StrongDual.toWeakDual (ω.val : A →L[ℂ] ℂ),
      TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ ha => ω.val.map_nonneg ha, ω.property⟩⟩
  invFun ψ :=
    let φ := cstarStateSpaceHomeomorph.symm ψ
    ⟨PositiveContinuousLinearMap.mk₀ (toStrongDual φ.val)
      (fun _ ha => TauCeti.map_nonneg_of_mem_stateSpace φ.property ha),
      TauCeti.map_one_of_mem_stateSpace φ.property⟩
  left_inv ω := by
    refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    have h := congrArg (fun x : TauCeti.stateSpace A => x.val a)
      (cstarStateSpaceHomeomorph.left_inv
        ⟨StrongDual.toWeakDual (ω.val : A →L[ℂ] ℂ),
          TauCeti.mem_stateSpace_iff_map_one.mpr ⟨fun _ ha => ω.val.map_nonneg ha, ω.property⟩⟩)
    exact h
  right_inv ψ := by
    refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    have h := congrArg (fun x : stateSpace (1 : selfAdjoint A) => x.val a)
      (cstarStateSpaceHomeomorph.right_inv ψ)
    exact h

/-- Evaluating `cstarPositiveContinuousLinearMapEquivStateSpace` restricts `ω` to
`selfAdjoint A`. -/
@[simp]
theorem cstarPositiveContinuousLinearMapEquivStateSpace_apply (ω : {ω : A →P[ℂ] ℂ // ω 1 = 1})
    (a : selfAdjoint A) :
    (cstarPositiveContinuousLinearMapEquivStateSpace ω).val a = (ω.val (a : A)).re := by
  simp [cstarPositiveContinuousLinearMapEquivStateSpace]

/-- Evaluating the inverse of `cstarPositiveContinuousLinearMapEquivStateSpace` gives the
complex-linear extension of `ψ`. -/
@[simp]
theorem cstarPositiveContinuousLinearMapEquivStateSpace_symm_apply
    (ψ : stateSpace (1 : selfAdjoint A)) (a : A) :
    (cstarPositiveContinuousLinearMapEquivStateSpace.symm ψ).val a =
      (ψ.val (ℜ a) : ℂ) + Complex.I * (ψ.val (ℑ a) : ℂ) :=
  cstarStateSpaceHomeomorph_symm_apply ψ a

end CStarCorrespondence

end TauCeti.OrderUnit
