/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.Opposite

/-!
# Opposite morphisms of differential graded algebras

A DG algebra morphism induces a morphism of Koszul-signed opposite DG algebras, acting by the
original map on underlying elements. Preservation of degrees makes the two multiplication signs
agree, and the unchanged opposite differential commutes with the induced map.

`DGAlgHom.gradedOpposite` preserves identities and composition and is injective on morphisms.
This supplies the functorial algebra construction needed when transporting modules and their
restriction of scalars through graded opposites.

The convention follows B. Keller, *Deriving DG categories*, Section 1, and B. Keller,
*Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti

namespace DGAlgHom

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {G : InternalGrading R A} {H : InternalGrading R B} {K : InternalGrading R C}
  [GradedAlgebra G.piece] [GradedAlgebra H.piece] [GradedAlgebra K.piece]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra G.piece dA} {hB : IsDGAlgebra H.piece dB}
  {hC : IsDGAlgebra K.piece dC}

/-- The morphism of Koszul-signed opposite DG algebras induced by a DG algebra morphism. -/
noncomputable def gradedOpposite (f : DGAlgHom hA hB) :
    DGAlgHom hA.gradedOpposite hB.gradedOpposite where
  toGradedAlgHom := GradedOpposite.map G H f.toGradedAlgHom
  map_d' x := by
    simp only [GradedOpposite.map_apply, coe_toGradedAlgHom,
      GradedOpposite.differential_op, GradedOpposite.differential_unop, map_d]

@[simp]
theorem gradedOpposite_toGradedAlgHom (f : DGAlgHom hA hB) :
    f.gradedOpposite.toGradedAlgHom = GradedOpposite.map G H f.toGradedAlgHom := (rfl)

/-- On underlying elements, the opposite DG morphism is the original morphism. -/
theorem gradedOpposite_apply (f : DGAlgHom hA hB) (x : GradedOpposite G) :
    f.gradedOpposite x = GradedOpposite.op H (f (GradedOpposite.unop G x)) :=
  GradedOpposite.map_apply G H f.toGradedAlgHom x

@[simp]
theorem gradedOpposite_op (f : DGAlgHom hA hB) (a : A) :
    f.gradedOpposite (GradedOpposite.op G a) = GradedOpposite.op H (f a) := by
  rw [gradedOpposite_apply, GradedOpposite.unop_op]

@[simp]
theorem unop_gradedOpposite (f : DGAlgHom hA hB) (x : GradedOpposite G) :
    GradedOpposite.unop H (f.gradedOpposite x) = f (GradedOpposite.unop G x) := by
  rw [gradedOpposite_apply, GradedOpposite.unop_op]

/-- Taking the opposite preserves the identity DG morphism. -/
@[simp]
theorem gradedOpposite_id : (DGAlgHom.id hA).gradedOpposite =
    DGAlgHom.id hA.gradedOpposite := by
  apply toGradedAlgHom_injective
  simp

/-- Taking the opposite preserves composition of DG morphisms. -/
@[simp]
theorem gradedOpposite_comp (g : DGAlgHom hB hC) (f : DGAlgHom hA hB) :
    (g.comp f).gradedOpposite = g.gradedOpposite.comp f.gradedOpposite := by
  apply toGradedAlgHom_injective
  simp

/-- A DG algebra morphism is determined by its opposite. -/
theorem gradedOpposite_injective :
    Function.Injective (gradedOpposite : DGAlgHom hA hB → _) := by
  intro f g h
  apply toGradedAlgHom_injective
  apply GradedOpposite.map_injective G H
  simpa using congrArg toGradedAlgHom h

end DGAlgHom

end TauCeti
