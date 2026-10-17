/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Dual.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Duality on the homotopy category of matrix factorizations

The crossed-transpose dual of potential `w` has potential `-w`. An odd homotopy
`(h₀, h₁)` dualizes to `(-h₁ᵗ, h₀ᵗ)`, whose boundary is the transpose of the original
boundary. Consequently duality preserves null-homotopic maps and induces an additive
contravariant functor `HMF(S,w)ᵒᵖ ⥤ HMF(S,-w)`.

The descent uses the existing morphism-ideal quotient, not a separate presentation of
homotopy classes. Its compatibility with the quotient functor identifies both the objects
and the action on representatives.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
* `TauCeti.Algebra.Homology.Curved.Dual`: the signed dual and its boundary calculation.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Opposite

variable {S : Type u} [CommRing S] {w : S}

/-- Duality carries null-homotopic maps of finite-projective factorizations to
null-homotopic maps of the negated potential. -/
theorem dualMap_mem_nullHomotopic {X Y : MatrixFactorization S w} (f : X ⟶ Y)
    (hf : f ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    dualMap f ∈ (nullHomotopic (S := S) (w := -w)).hom (dual Y) (dual X) := by
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff f).mp hf
  apply (mem_nullHomotopic_iff _).mpr
  refine ⟨-FGModuleCat.dualMap h₁, FGModuleCat.dualMap h₀, ?_⟩
  rw [dualMap_hom, ← hh, CurvedDuplex.dualMap_nullHomotopicMap]
  rfl

private theorem nullHomotopic_le_ker_dualFunctor_rightOp :
    nullHomotopic (S := S) (w := w) ≤
      (dualFunctor ⋙ (nullHomotopic (S := S) (w := -w)).quotientFunctor).rightOp.kerIdeal := by
  intro X Y f hf
  rw [Functor.mem_kerIdeal_hom]
  apply Quiver.Hom.unop_inj
  simp only [Functor.rightOp_map_unop, Functor.comp_map, Limits.unop_zero]
  rw [dualFunctor_map, Functor.map_comp, Functor.map_comp]
  simp only [Quiver.Hom.unop_op]
  rw [(MorphismIdeal.quotientFunctor_map_eq_zero_iff _).mpr (dualMap_mem_nullHomotopic f hf)]
  simp

/-- The contravariant additive duality functor on the matrix-factorization homotopy
categories, sending potential `w` to potential `-w`. -/
noncomputable def homotopyDualFunctor :
    (HomotopyCategory (S := S) (w := w))ᵒᵖ ⥤ HomotopyCategory (S := S) (w := -w) :=
  ((nullHomotopic (S := S) (w := w)).lift
    (dualFunctor ⋙ (nullHomotopic (S := S) (w := -w)).quotientFunctor).rightOp
      nullHomotopic_le_ker_dualFunctor_rightOp).leftOp

instance : (homotopyDualFunctor (S := S) (w := w)).Additive := by
  unfold homotopyDualFunctor
  infer_instance

/-- Duality after passage to homotopy classes agrees with passage to homotopy classes
after duality. -/
theorem quotientFunctor_op_comp_homotopyDualFunctor :
    (nullHomotopic (S := S) (w := w)).quotientFunctor.op ⋙ homotopyDualFunctor =
      dualFunctor ⋙ (nullHomotopic (S := S) (w := -w)).quotientFunctor := by
  refine CategoryTheory.Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
  · simp only [homotopyDualFunctor, Functor.comp_obj, Functor.op_obj, Functor.leftOp_obj,
      MorphismIdeal.lift, CategoryTheory.Quotient.lift_obj_functor_obj,
      Functor.rightOp_obj, op_unop, unop_op]
  · simp only [homotopyDualFunctor, Functor.comp_map, Functor.op_map, Functor.leftOp_map,
      MorphismIdeal.lift, CategoryTheory.Quotient.lift_map_functor_map,
      Functor.rightOp_map, Quiver.Hom.op_unop, Quiver.Hom.unop_op]
    simp

/-- The dual of the class of a factorization is the class of its signed dual. -/
@[simp]
theorem homotopyDualFunctor_obj_quotientFunctor_obj (X : MatrixFactorization S w) :
    homotopyDualFunctor.obj (op ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X)) =
      (nullHomotopic (S := S) (w := -w)).quotientFunctor.obj (dual X) := by
  simpa only [Functor.comp_obj, Functor.op_obj, unop_op, dualFunctor_obj] using
    Functor.congr_obj quotientFunctor_op_comp_homotopyDualFunctor (op X)

/-- On a representative, the homotopy dual functor applies the crossed-transpose dual map.
The transports identify the objects using `homotopyDualFunctor_obj_quotientFunctor_obj`. -/
@[reassoc (attr := simp), simp]
theorem homotopyDualFunctor_map_quotientFunctor_map {X Y : MatrixFactorization S w}
    (f : X ⟶ Y) :
    homotopyDualFunctor.map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map f).op ≫
      eqToHom (homotopyDualFunctor_obj_quotientFunctor_obj X) =
    eqToHom (homotopyDualFunctor_obj_quotientFunctor_obj Y) ≫
      (nullHomotopic (S := S) (w := -w)).quotientFunctor.map (dualMap f) := by
  have h := Functor.congr_hom quotientFunctor_op_comp_homotopyDualFunctor f.op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at h
  rw [h]
  simp [dualFunctor_map, Functor.map_comp, eqToHom_map, Category.assoc]

end TauCeti.MatrixFactorization
