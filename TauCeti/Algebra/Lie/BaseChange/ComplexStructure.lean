/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Transported complex structures and Lie brackets

A real Lie equivalence from a complex Lie algebra transports its canonical almost complex
structure through the underlying linear equivalence. The transported structure commutes with
the bracket in both arguments. The construction and square laws are the existing almost
complex structure transport API.

## Main results

* `RestrictScalars.addEquiv_lie`: the additive scalar-restriction identification preserves brackets.
* `LieEquiv.restrictScalarsLinearEquiv`: the underlying equivalence with the canonical
  additive-group parent used by almost complex structures.
* `LieEquiv.transport_ofRestrictScalars_naturality`: complex-linearity through a commuting square.
* `LieEquiv.transport_ofRestrictScalars_lie_left` and
  `LieEquiv.transport_ofRestrictScalars_lie_right`: bracket compatibility of the transported
  canonical complex structure.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1.
-/

public section

/-- The additive identification for scalar restriction preserves the Lie bracket. -/
theorem RestrictScalars.addEquiv_lie {R A L : Type*} [LieRing L]
    (x y : RestrictScalars R A L) :
    RestrictScalars.addEquiv R A L ⁅x, y⁆ =
      ⁅RestrictScalars.addEquiv R A L x, RestrictScalars.addEquiv R A L y⁆ := rfl

open TauCeti

namespace LieEquiv

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing L'] [LieAlgebra ℝ L']
  (e : RestrictScalars ℝ ℂ L ≃ₗ⁅ℝ⁆ L')

/-- The underlying real-linear equivalence, using the canonical additive-group parent of
scalar restriction. -/
noncomputable def restrictScalarsLinearEquiv :
    letI : AddCommMonoid (RestrictScalars ℝ ℂ L) :=
      (instAddCommGroupRestrictScalars ℝ ℂ L).toAddCommMonoid
    letI := RestrictScalars.realModule L
    RestrictScalars ℝ ℂ L ≃ₗ[ℝ] L' := by
  letI : AddCommMonoid (RestrictScalars ℝ ℂ L) :=
      (instAddCommGroupRestrictScalars ℝ ℂ L).toAddCommMonoid
  letI := RestrictScalars.realModule L
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := e.map_smul }

/-- The normalized real-linear comparison has the same forward map as the Lie equivalence. -/
@[simp]
theorem restrictScalarsLinearEquiv_apply (x : RestrictScalars ℝ ℂ L) :
    e.restrictScalarsLinearEquiv x = e x := by
  rfl

/-- The normalized real-linear comparison has the same inverse as the Lie equivalence. -/
@[simp]
theorem restrictScalarsLinearEquiv_symm_apply (x : L') :
    e.restrictScalarsLinearEquiv.symm x = e.symm x := by
  rfl

/-- The transported canonical complex structure on the image of the equivalence. -/
private theorem transport_ofRestrictScalars_apply_image (x : RestrictScalars ℝ ℂ L) :
    (AlmostComplexStructure.ofRestrictScalars L).transport e.restrictScalarsLinearEquiv (e x) =
      e ((RestrictScalars.addEquiv ℝ ℂ L).symm
        (Complex.I • RestrictScalars.addEquiv ℝ ℂ L x)) := by
  rw [AlmostComplexStructure.transport_apply, restrictScalarsLinearEquiv_symm_apply,
    e.symm_apply_apply]
  exact (restrictScalarsLinearEquiv_apply e _).trans
    (congrArg e (AlmostComplexStructure.ofRestrictScalars_apply L x))

/-- A commuting square with a complex-linear map intertwines the transported structures. -/
theorem transport_ofRestrictScalars_naturality
    {N N' : Type*} [LieRing N] [LieAlgebra ℂ N] [LieRing N'] [LieAlgebra ℝ N']
    (e' : RestrictScalars ℝ ℂ N ≃ₗ⁅ℝ⁆ N') (f : L →ₗ[ℂ] N) (g : L' →ₗ[ℝ] N')
    (h : ∀ x, g (e x) = e' ((RestrictScalars.addEquiv ℝ ℂ N).symm
      (f (RestrictScalars.addEquiv ℝ ℂ L x)))) (X : L') :
    g ((AlmostComplexStructure.ofRestrictScalars L).transport e.restrictScalarsLinearEquiv X) =
      (AlmostComplexStructure.ofRestrictScalars N).transport e'.restrictScalarsLinearEquiv
        (g X) := by
  let : AddCommGroup (RestrictScalars ℝ ℂ L) := instAddCommGroupRestrictScalars ℝ ℂ L
  let : AddCommGroup (RestrictScalars ℝ ℂ N) := instAddCommGroupRestrictScalars ℝ ℂ N
  let := RestrictScalars.realModule L
  let := RestrictScalars.realModule N
  let F := e'.restrictScalarsLinearEquiv.symm.toLinearMap ∘ₗ g ∘ₗ
    e.restrictScalarsLinearEquiv.toLinearMap
  have hF_apply (x : RestrictScalars ℝ ℂ L) :
      F x = (RestrictScalars.addEquiv ℝ ℂ N).symm
        (f (RestrictScalars.addEquiv ℝ ℂ L x)) := by
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe,
      restrictScalarsLinearEquiv_apply, restrictScalarsLinearEquiv_symm_apply, h]
    exact e'.symm_apply_apply _
  have hF : IsComplexLinearMap (AlmostComplexStructure.ofRestrictScalars L)
      (AlmostComplexStructure.ofRestrictScalars N) F := by
    rw [isComplexLinearMap_iff_apply]
    intro x
    rw [hF_apply, AlmostComplexStructure.ofRestrictScalars_apply, hF_apply,
      AlmostComplexStructure.ofRestrictScalars_apply, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, f.map_smul]
  have hconj : e.restrictScalarsLinearEquiv.arrowCongr e'.restrictScalarsLinearEquiv F = g := by
    ext x
    simp only [LinearEquiv.arrowCongr_apply, F, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have htransport := hF.arrowCongr e.restrictScalarsLinearEquiv e'.restrictScalarsLinearEquiv
  rw [hconj, isComplexLinearMap_iff_apply] at htransport
  exact htransport X

/-- The transported complex structure commutes with the bracket in its first argument. -/
@[simp]
theorem transport_ofRestrictScalars_lie_left (X Y : L') :
    ⁅(AlmostComplexStructure.ofRestrictScalars L).transport e.restrictScalarsLinearEquiv X, Y⁆ =
      (AlmostComplexStructure.ofRestrictScalars L).transport
        e.restrictScalarsLinearEquiv ⁅X, Y⁆ := by
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective X
  obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective Y
  have hlie (u v : RestrictScalars ℝ ℂ L) : ⁅e u, e v⁆ = e ⁅u, v⁆ :=
    (e.map_lie u v).symm
  simp only [LieEquiv.coe_toLinearEquiv]
  rw [transport_ofRestrictScalars_apply_image, hlie, hlie,
    transport_ofRestrictScalars_apply_image]
  apply congrArg e
  apply (RestrictScalars.addEquiv ℝ ℂ L).injective
  rw [RestrictScalars.addEquiv_lie, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, RestrictScalars.addEquiv_lie, smul_lie]

/-- The transported complex structure commutes with the bracket in its second argument. -/
@[simp]
theorem transport_ofRestrictScalars_lie_right (X Y : L') :
    ⁅X, (AlmostComplexStructure.ofRestrictScalars L).transport e.restrictScalarsLinearEquiv Y⁆ =
      (AlmostComplexStructure.ofRestrictScalars L).transport
        e.restrictScalarsLinearEquiv ⁅X, Y⁆ := by
  rw [← lie_skew X
    ((AlmostComplexStructure.ofRestrictScalars L).transport e.restrictScalarsLinearEquiv Y),
    transport_ofRestrictScalars_lie_left, ← LinearMap.map_neg, lie_skew X Y]

end LieEquiv
