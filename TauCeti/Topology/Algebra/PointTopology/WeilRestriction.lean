/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Basic
public import TauCeti.Topology.Algebra.PointTopology.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The point topology and Weil restriction

For a finite projective `A`-algebra `B` and a finitely presented `B`-algebra `C`, the Weil
restriction adjunction is a homeomorphism on `T`-points when `T` is a topological commutative
`A`-algebra and `B ⊗[A] T` carries its `T`-module topology (`homHomeomorph`).

For a topological ring `A` and `B` with its `A`-module topology, `pointsHomeomorph` specializes
this to a homeomorphism between `A`-points of the Weil restriction and `B`-points of `C`.
This identifies rational point topologies under restriction of scalars, for example for finite
extensions of local fields and for the real points of the Deligne torus.

The comparison uses `TauCeti.Algebra.WeilRestriction.homEquiv` and the right tensor unitor.
The inverse is continuous because the linear coefficients of the universal point generate the
Weil restriction. No basis, Hausdorff assumption, or field hypothesis is needed.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Exercise 2.4, p. 3.
-/

public noncomputable section

open TensorProduct Topology
open scoped TauCeti.PointTopology

namespace TauCeti.Algebra.WeilRestriction

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [Algebra.FinitePresentation B C]

section General

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (T : Type*) [CommRing T] [Algebra A T] [TopologicalSpace T] [IsTopologicalRing T]
  [TopologicalSpace (B ⊗[A] T)] [IsModuleTopology T (B ⊗[A] T)]

/-- The Weil restriction adjunction is a homeomorphism on points over any topological
`A`-algebra `T` when the tensor product has its `T`-module topology (acting on the right factor). -/
def homHomeomorph : (WeilRestriction A B C →ₐ[A] T) ≃ₜ (C →ₐ[B] B ⊗[A] T) where
  toEquiv := homEquiv A B C T
  continuous_toFun := by
    let _ : ContinuousAdd (B ⊗[A] T) := IsModuleTopology.toContinuousAdd T _
    have h (z : B ⊗[A] WeilRestriction A B C) :
        Continuous fun g : WeilRestriction A B C →ₐ[A] T ↦
          Algebra.TensorProduct.lTensor (S := B) B g z := by
      induction z using TensorProduct.inductionOn with
      | tmul b w =>
        have hb := IsModuleTopology.continuous_of_linearMap
          ((Algebra.TensorProduct.commRight A T B).toLinearMap.comp
            ((TensorProduct.AlgebraTensorModule.mk A T T B).flip b))
        simpa [Function.comp_def] using hb.comp (PointTopology.continuous_eval w)
      | add z w hz hw => simpa only [map_add] using hz.fun_add hw
    apply PointTopology.continuous_iff.2
    intro c
    simpa only [Equiv.toFun_as_coe, homEquiv_apply, AlgHom.comp_apply] using
      h (universalPoint A B C c)
  continuous_invFun := by
    apply (PointTopology.isEmbedding_eval_generators
      (adjoin_range_universalCoefficient (A := A) (B := B) (C := C))).isInducing.continuous_iff.2
    apply continuous_pi
    rintro ⟨φ, c⟩
    have hφ := IsModuleTopology.continuous_of_linearMap
      ((((Algebra.linearMap A T).comp φ).liftBaseChange T).comp
        (Algebra.TensorProduct.commRight A T B).symm.toLinearMap)
    convert hφ.comp (PointTopology.continuous_eval (k := B) (A := C) c) using 1
    ext x
    simp only [Equiv.invFun_as_coe, map_universalCoefficient, Equiv.apply_symm_apply,
      Function.comp_apply, LinearMap.comp_apply, LinearMap.tensorComponent_eq_liftBaseChange]
    induction x c using TensorProduct.inductionOn with
    | tmul b t => simp
    | add z w hz hw => simp only [map_add, hz, hw]

/-- The general point homeomorphism is the algebraic Weil restriction adjunction. -/
@[simp]
theorem homHomeomorph_apply (g : WeilRestriction A B C →ₐ[A] T) :
    homHomeomorph A B C T g = homEquiv A B C T g := (rfl)

/-- The inverse adjunction evaluates coefficients by contraction of the original point. -/
@[simp]
theorem homHomeomorph_symm_apply_universalCoefficient (x : C →ₐ[B] B ⊗[A] T)
    (φ : Module.Dual A B) (c : C) :
    (homHomeomorph A B C T).symm x (universalCoefficient φ c) =
      LinearMap.tensorComponent φ (TensorProduct.comm A B T (x c)) := by
  rw [map_universalCoefficient]
  exact congrArg (fun y : C →ₐ[B] B ⊗[A] T ↦
    LinearMap.tensorComponent φ (TensorProduct.comm A B T (y c)))
      ((homEquiv A B C T).apply_symm_apply x)

end General

variable [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsModuleTopology A B]

/-- Restriction of scalars identifies `A`-points of the Weil restriction with `B`-points,
homeomorphically when `B` carries its finite projective `A`-module topology. -/
def pointsHomeomorph : (WeilRestriction A B C →ₐ[A] A) ≃ₜ (C →ₐ[B] B) := by
  letI : TopologicalSpace (B ⊗[A] A) := moduleTopology A (B ⊗[A] A)
  letI : IsModuleTopology A (B ⊗[A] A) := ⟨rfl⟩
  letI : ContinuousAdd B := IsModuleTopology.toContinuousAdd A B
  letI : ContinuousAdd (B ⊗[A] A) := IsModuleTopology.toContinuousAdd A _
  -- For `T = A`, the right-factor scalar action agrees with the usual base-ring action.
  -- Identify them explicitly before specializing the general homeomorphism.
  have hright : (Algebra.TensorProduct.rightAlgebra : Algebra A (B ⊗[A] A)) =
      (inferInstance : Algebra A (B ⊗[A] A)) := by
    apply Algebra.algebra_ext
    intro a
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    simpa using (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A)).commutes a
  letI : @IsModuleTopology A _ (B ⊗[A] A) _
      Algebra.TensorProduct.rightAlgebra.toSMul _ := by
    rw [hright]
    infer_instance
  let e := Algebra.TensorProduct.rid A B B
  let h : (C →ₐ[B] B ⊗[A] A) ≃ₜ (C →ₐ[B] B) :=
    { toEquiv := AlgEquiv.arrowCongr (AlgEquiv.refl : C ≃ₐ[B] C) e
      continuous_toFun := PointTopology.continuous_iff.2 fun c ↦
        by simpa [Function.comp_def, AlgEquiv.arrowCongr_apply] using
            (IsModuleTopology.continuous_of_linearMap
              (e.toLinearEquiv.restrictScalars A).toLinearMap).comp
                (PointTopology.continuous_eval c)
      continuous_invFun := PointTopology.continuous_iff.2 fun c ↦
        by simpa [Function.comp_def, AlgEquiv.arrowCongr_symm, AlgEquiv.arrowCongr_apply] using
            (IsModuleTopology.continuous_of_linearMap
              (e.symm.toLinearEquiv.restrictScalars A).toLinearMap).comp
                (PointTopology.continuous_eval c) }
  exact (homHomeomorph A B C A).trans h

/-- The point comparison is the algebraic adjunction followed by the right tensor unitor. -/
@[simp]
theorem pointsHomeomorph_apply (g : WeilRestriction A B C →ₐ[A] A) (c : C) :
    pointsHomeomorph A B C g c =
      Algebra.TensorProduct.rid A B B (homEquiv A B C A g c) := (rfl)

/-- Under the algebraic adjunction, the inverse comparison is the original point followed by
the inverse right tensor unitor. -/
-- Not a simp lemma: `homEquiv_apply` already expands its left-hand side.
theorem homEquiv_pointsHomeomorph_symm (x : C →ₐ[B] B) :
    homEquiv A B C A ((pointsHomeomorph A B C).symm x) =
      (Algebra.TensorProduct.rid A B B).symm.toAlgHom.comp x := by
  ext c
  apply (Algebra.TensorProduct.rid A B B).injective
  have hx := congrArg (fun y : C →ₐ[B] B ↦ y c)
    ((pointsHomeomorph A B C).apply_symm_apply x)
  rw [pointsHomeomorph_apply] at hx
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using hx

/-- The inverse comparison evaluates a universal coefficient by applying its linear functional
to the corresponding value of the original point. -/
@[simp]
theorem pointsHomeomorph_symm_apply_universalCoefficient (x : C →ₐ[B] B)
    (φ : Module.Dual A B) (c : C) :
    (pointsHomeomorph A B C).symm x (universalCoefficient φ c) = φ (x c) := by
  rw [map_universalCoefficient, homEquiv_pointsHomeomorph_symm]
  simp

end TauCeti.Algebra.WeilRestriction
