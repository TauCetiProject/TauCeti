/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WeilRestriction.Coordinates
public import TauCeti.Topology.Algebra.PointTopology.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The point topology and Weil restriction

Let `B` be a finite projective algebra over a topological commutative ring `A`, equipped with
its `A`-module topology. For a finitely presented `B`-algebra `C`, the natural bijection between
`A`-points of its Weil restriction and `B`-points of `C` is a homeomorphism for the evaluation
topologies. This identifies rational point topologies under restriction of scalars, for example
for finite extensions of local fields and for the real points of the Deligne torus.

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
  [Algebra.FinitePresentation B C] [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsModuleTopology A B]

/-- Restriction of scalars identifies `A`-points of the Weil restriction with `B`-points,
homeomorphically when `B` carries its finite projective `A`-module topology. -/
def pointsHomeomorph : (WeilRestriction A B C →ₐ[A] A) ≃ₜ (C →ₐ[B] B) where
  toEquiv := (homEquiv A B C A).trans
    (AlgEquiv.arrowCongr (AlgEquiv.refl : C ≃ₐ[B] C) (Algebra.TensorProduct.rid A B B))
  continuous_toFun := by
    let _ : ContinuousAdd B := IsModuleTopology.toContinuousAdd A B
    have h (z : B ⊗[A] WeilRestriction A B C) :
        Continuous fun g : WeilRestriction A B C →ₐ[A] A ↦
          Algebra.TensorProduct.rid A B B (Algebra.TensorProduct.lTensor (S := B) B g z) := by
      induction z using TensorProduct.inductionOn with
      | tmul b w =>
        simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.rid_tmul] using
          (PointTopology.continuous_eval w).fun_smul continuous_const
      | add z w hz hw => simpa only [map_add] using hz.fun_add hw
    apply PointTopology.continuous_iff.2
    intro c
    simpa [AlgEquiv.arrowCongr, homEquiv_apply] using h (universalPoint A B C c)
  continuous_invFun := by
    apply (PointTopology.isEmbedding_eval_generators
      (adjoin_range_universalCoefficient (A := A) (B := B) (C := C))).isInducing.continuous_iff.2
    apply continuous_pi
    rintro ⟨φ, c⟩
    have hφ := (IsModuleTopology.continuous_of_linearMap φ).comp
      (PointTopology.continuous_eval (k := B) (A := C) c)
    convert hφ using 1
    ext x
    simp only [Function.comp_apply, Equiv.invFun_as_coe]
    rw [map_universalCoefficient]
    simp [AlgEquiv.arrowCongr, Algebra.TensorProduct.rid_symm_apply]

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
