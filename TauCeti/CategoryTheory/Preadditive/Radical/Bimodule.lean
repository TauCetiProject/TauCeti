/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Quotient
public import TauCeti.RingTheory.LocalRing.Residue
-- Non-public: the dimension theory of a module over a division ring is used only inside the
-- proof of the final statement, whose own wording mentions only `Module.rank`.
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# The irreducible morphisms as a bimodule over the residue rings

`TauCeti.irreducibleMorphismSpace k X Y` is the quotient `rad(X, Y) / rad²(X, Y)`, whose nonzero
classes between objects with local endomorphism rings are the irreducible morphisms `X ⟶ Y`. It
carries more structure than the `k`-module structure it is built with: composing on the left with
an endomorphism of `X` and on the right with one of `Y` preserves the radical and its square, and
an endomorphism lying in `rad(End X)` or `rad(End Y)` pushes a radical morphism into `rad²`. So the
two actions descend to the residue rings `End X ⧸ rad(End X)` and `End Y ⧸ rad(End Y)`, and this
file builds them.

That is the structure an **arrow of the Auslander-Reiten quiver** is counted by. An arrow `X → Y`
is a basis vector of `rad(X, Y) / rad²(X, Y)` over the residue **division** rings, which is what
the two endomorphism rings being local makes them
(`TauCeti.IsLocalRing.instDivisionRingQuotientJacobson`); the `k`-dimension computed in
`TauCeti/CategoryTheory/Preadditive/Radical/Quotient.lean` agrees with that count only when the
residue division rings are `k` itself. The closing statement here is the one an arrow set is read
off from: the rank over the residue division ring of the target is positive exactly when an
irreducible morphism exists.

The left action is antimultiplicative — `(a₁ ≫ a₂) ≫ f` is `a₁` applied after `a₂` — so it is
recorded as an action of `(End X)ᵐᵒᵖ`, and it descends to `(End X)ᵐᵒᵖ ⧸ rad((End X)ᵐᵒᵖ)`, which is
again a division ring because the opposite of a local ring is local
(`IsLocalRing.instMulOpposite`).

## Main definitions

* `TauCeti.irreducibleMorphismPostcomp` and `TauCeti.irreducibleMorphismPrecomp`: composing with an
  endomorphism of the target, resp. of the source, as a `k`-linear endomorphism of the space of
  irreducible morphisms.
* `TauCeti.irreducibleMorphismPostcompHom` and `TauCeti.irreducibleMorphismPrecompHom`: those two
  operations as ring homomorphisms out of `End Y` and out of `(End X)ᵐᵒᵖ`.
* `TauCeti.irreducibleMorphismResiduePostcompHom` and
  `TauCeti.irreducibleMorphismResiduePrecompHom`: their descents to the residue rings, and the
  module structures `TauCeti.instModuleResiduePostcomp` and `TauCeti.instModuleResiduePrecomp`
  they induce.

## Main results

* `TauCeti.irreducibleMorphismPostcomp_eq_zero_of_mem_jacobson` and
  `TauCeti.irreducibleMorphismPrecomp_eq_zero_of_mem_jacobson`: a radical endomorphism of either
  end acts by zero, which is what lets the two actions descend.
* `TauCeti.instSMulCommClassResidue`: **the two actions commute**, so the space of irreducible
  morphisms is a genuine bimodule; `TauCeti.instSMulCommClassResiduePostcomp` and
  `TauCeti.instSMulCommClassResiduePrecomp` record that each of them commutes with the base
  scalars.
* `TauCeti.rank_irreducibleMorphismSpace_pos_iff` and
  `TauCeti.rank_irreducibleMorphismSpace_op_pos_iff`: **the arrow multiplicity is positive exactly
  when an irreducible morphism exists** — the rank of the space of irreducible morphisms over the
  residue division ring of the target is positive exactly when there is an irreducible morphism
  `X ⟶ Y`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), V.7 and VII.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1 and VII.1, where the arrows of the
  Auslander-Reiten quiver are counted by the dimensions of `rad / rad²` over the residue division
  rings.
* [Quiver-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md),
  Layer 6, "The AR quiver".
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Actions

variable (k : Type*) [Ring k] [Linear k C] (X Y : C)

/-! ### Composing with an endomorphism of the target -/

/-- **Postcomposition by an endomorphism of the target**, on the radical morphisms `X ⟶ Y`. -/
def jacobsonRadicalPostcomp (g : End Y) :
    jacobsonRadicalSubmodule k X Y →ₗ[k] jacobsonRadicalSubmodule k X Y where
  toFun f := ⟨(f : X ⟶ Y) ≫ g, mem_jacobsonRadicalSubmodule.mpr
    (comp_mem_jacobsonRadical_right (mem_jacobsonRadicalSubmodule.mp f.2) g)⟩
  map_add' _ _ := by ext; simp [Preadditive.add_comp]
  map_smul' _ _ := by ext; simp [Linear.smul_comp]

@[simp]
theorem coe_jacobsonRadicalPostcomp (g : End Y) (f : jacobsonRadicalSubmodule k X Y) :
    (jacobsonRadicalPostcomp k X Y g f : X ⟶ Y) = (f : X ⟶ Y) ≫ g :=
  (rfl)

/-- **Postcomposition by an endomorphism of the target**, on the space of irreducible morphisms.
It is well defined because postcomposition preserves the square of the radical. -/
def irreducibleMorphismPostcomp (g : End Y) :
    irreducibleMorphismSpace k X Y →ₗ[k] irreducibleMorphismSpace k X Y :=
  irreducibleMorphismLift ((irreducibleMorphismMk k X Y).comp (jacobsonRadicalPostcomp k X Y g))
    fun _ hf => by
      simpa using comp_mem_jacobsonRadicalSq_right hf g

@[simp]
theorem irreducibleMorphismPostcomp_irreducibleMorphismMk (g : End Y)
    (f : jacobsonRadicalSubmodule k X Y) :
    irreducibleMorphismPostcomp k X Y g (irreducibleMorphismMk k X Y f) =
      irreducibleMorphismMk k X Y (jacobsonRadicalPostcomp k X Y g f) :=
  irreducibleMorphismLift_irreducibleMorphismMk _ _ f

/-- **Postcomposition as a ring homomorphism** `End Y →+* Module.End k (rad / rad²)`. The
multiplication of `CategoryTheory.End` composes in the opposite order to the arrows, so
postcomposition is multiplicative and not antimultiplicative. -/
def irreducibleMorphismPostcompHom :
    End Y →+* Module.End k (irreducibleMorphismSpace k X Y) where
  toFun := irreducibleMorphismPostcomp k X Y
  map_one' := by
    ext f
    simp only [irreducibleMorphismPostcomp_irreducibleMorphismMk, Module.End.one_apply]
    congr 1
    ext
    simp [End.one_def]
  map_mul' g₁ g₂ := by
    ext f
    simp only [irreducibleMorphismPostcomp_irreducibleMorphismMk, Module.End.mul_apply]
    congr 1
    ext
    simp [End.mul_def]
  map_zero' := by
    ext f
    simp only [irreducibleMorphismPostcomp_irreducibleMorphismMk, LinearMap.zero_apply,
      ← map_zero (irreducibleMorphismMk k X Y)]
    congr 1
    ext
    simp
  map_add' g₁ g₂ := by
    ext f
    simp only [irreducibleMorphismPostcomp_irreducibleMorphismMk, LinearMap.add_apply,
      ← map_add (irreducibleMorphismMk k X Y)]
    congr 1
    ext
    exact Preadditive.comp_add _ _ _ _ _ _

@[simp]
theorem irreducibleMorphismPostcompHom_apply (g : End Y) :
    irreducibleMorphismPostcompHom k X Y g = irreducibleMorphismPostcomp k X Y g :=
  (rfl)

/-- **A radical endomorphism of the target acts by zero**: a radical morphism followed by a radical
endomorphism is a composite of two radical morphisms, hence lies in `rad²`. This is what lets
postcomposition descend to the residue ring of `End Y`. -/
theorem irreducibleMorphismPostcomp_eq_zero_of_mem_jacobson {g : End Y}
    (hg : g ∈ Ring.jacobson (End Y)) : irreducibleMorphismPostcomp k X Y g = 0 := by
  ext f
  simpa using comp_mem_jacobsonRadicalSq (mem_jacobsonRadicalSubmodule.mp f.2)
    (mem_jacobsonRadical_self_iff_mem_jacobson.mpr hg)

/-! ### Composing with an endomorphism of the source -/

/-- **Precomposition by an endomorphism of the source**, on the radical morphisms `X ⟶ Y`. -/
def jacobsonRadicalPrecomp (a : End X) :
    jacobsonRadicalSubmodule k X Y →ₗ[k] jacobsonRadicalSubmodule k X Y where
  toFun f := ⟨a ≫ (f : X ⟶ Y), mem_jacobsonRadicalSubmodule.mpr
    (comp_mem_jacobsonRadical_left a (mem_jacobsonRadicalSubmodule.mp f.2))⟩
  map_add' _ _ := by ext; simp [Preadditive.comp_add]
  map_smul' _ _ := by ext; simp [Linear.comp_smul]

@[simp]
theorem coe_jacobsonRadicalPrecomp (a : End X) (f : jacobsonRadicalSubmodule k X Y) :
    (jacobsonRadicalPrecomp k X Y a f : X ⟶ Y) = a ≫ (f : X ⟶ Y) :=
  (rfl)

/-- **Precomposition by an endomorphism of the source**, on the space of irreducible morphisms. -/
def irreducibleMorphismPrecomp (a : End X) :
    irreducibleMorphismSpace k X Y →ₗ[k] irreducibleMorphismSpace k X Y :=
  irreducibleMorphismLift ((irreducibleMorphismMk k X Y).comp (jacobsonRadicalPrecomp k X Y a))
    fun _ hf => by
      simpa using comp_mem_jacobsonRadicalSq_left a hf

@[simp]
theorem irreducibleMorphismPrecomp_irreducibleMorphismMk (a : End X)
    (f : jacobsonRadicalSubmodule k X Y) :
    irreducibleMorphismPrecomp k X Y a (irreducibleMorphismMk k X Y f) =
      irreducibleMorphismMk k X Y (jacobsonRadicalPrecomp k X Y a f) :=
  irreducibleMorphismLift_irreducibleMorphismMk _ _ f

/-- **Precomposition as a ring homomorphism** `(End X)ᵐᵒᵖ →+* Module.End k (rad / rad²)`. The
opposite is needed because precomposing by `a₁` and then by `a₂` is precomposing by `a₂ ≫ a₁`,
which is `a₁ * a₂` in `CategoryTheory.End`. -/
def irreducibleMorphismPrecompHom :
    (End X)ᵐᵒᵖ →+* Module.End k (irreducibleMorphismSpace k X Y) where
  toFun a := irreducibleMorphismPrecomp k X Y a.unop
  map_one' := by
    ext f
    simp only [irreducibleMorphismPrecomp_irreducibleMorphismMk, Module.End.one_apply]
    congr 1
    ext
    simp [End.one_def]
  map_mul' a₁ a₂ := by
    ext f
    simp only [irreducibleMorphismPrecomp_irreducibleMorphismMk, Module.End.mul_apply]
    congr 1
    ext
    simp [End.mul_def]
  map_zero' := by
    ext f
    simp only [irreducibleMorphismPrecomp_irreducibleMorphismMk, LinearMap.zero_apply,
      ← map_zero (irreducibleMorphismMk k X Y)]
    congr 1
    ext
    simp
  map_add' a₁ a₂ := by
    ext f
    simp only [irreducibleMorphismPrecomp_irreducibleMorphismMk, LinearMap.add_apply,
      ← map_add (irreducibleMorphismMk k X Y)]
    congr 1
    ext
    exact Preadditive.add_comp _ _ _ _ _ _

@[simp]
theorem irreducibleMorphismPrecompHom_apply (a : (End X)ᵐᵒᵖ) :
    irreducibleMorphismPrecompHom k X Y a = irreducibleMorphismPrecomp k X Y a.unop :=
  (rfl)

/-- **A radical endomorphism of the source acts by zero**, the mirror image of
`TauCeti.irreducibleMorphismPostcomp_eq_zero_of_mem_jacobson`. -/
theorem irreducibleMorphismPrecomp_eq_zero_of_mem_jacobson {a : End X}
    (ha : a ∈ Ring.jacobson (End X)) : irreducibleMorphismPrecomp k X Y a = 0 := by
  ext f
  simpa using comp_mem_jacobsonRadicalSq
    (mem_jacobsonRadical_self_iff_mem_jacobson.mpr ha) (mem_jacobsonRadicalSubmodule.mp f.2)

/-- The two actions commute: `a ≫ (f ≫ g)` and `(a ≫ f) ≫ g` are the same morphism. -/
theorem irreducibleMorphismPrecomp_comp_postcomp (a : End X) (g : End Y) :
    (irreducibleMorphismPrecomp k X Y a).comp (irreducibleMorphismPostcomp k X Y g) =
      (irreducibleMorphismPostcomp k X Y g).comp (irreducibleMorphismPrecomp k X Y a) := by
  ext f
  simp [Category.assoc]

end Actions

/-! ### The descent to the residue rings -/

section Residue

variable (k : Type*) [Ring k] [Linear k C] (X Y : C)

/-- **Postcomposition, descended to the residue ring of the target.** -/
def irreducibleMorphismResiduePostcompHom :
    (End Y ⧸ Ring.jacobson (End Y)) →+* Module.End k (irreducibleMorphismSpace k X Y) :=
  Ideal.Quotient.lift _ (irreducibleMorphismPostcompHom k X Y) fun _ hg =>
    irreducibleMorphismPostcomp_eq_zero_of_mem_jacobson k X Y hg

/-- **Precomposition, descended to the residue ring of the source**, which is the opposite
endomorphism ring because the action is antimultiplicative. -/
def irreducibleMorphismResiduePrecompHom :
    ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) →+*
      Module.End k (irreducibleMorphismSpace k X Y) :=
  Ideal.Quotient.lift _ (irreducibleMorphismPrecompHom k X Y) fun _ ha =>
    irreducibleMorphismPrecomp_eq_zero_of_mem_jacobson k X Y
      (Ring.mem_jacobson_mulOpposite_iff.mp ha)

/-- The space of irreducible morphisms is a module over the residue ring of the target. -/
instance instModuleResiduePostcomp :
    Module (End Y ⧸ Ring.jacobson (End Y)) (irreducibleMorphismSpace k X Y) :=
  Module.compHom _ (irreducibleMorphismResiduePostcompHom k X Y)

/-- The space of irreducible morphisms is a module over the residue ring of the opposite
endomorphism ring of the source. -/
instance instModuleResiduePrecomp :
    Module ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (irreducibleMorphismSpace k X Y) :=
  Module.compHom _ (irreducibleMorphismResiduePrecompHom k X Y)

variable {k X Y}

@[simp]
theorem residue_smul_irreducibleMorphismMk (g : End Y) (f : jacobsonRadicalSubmodule k X Y) :
    (Ideal.Quotient.mk (Ring.jacobson (End Y)) g) • irreducibleMorphismMk k X Y f =
      irreducibleMorphismMk k X Y (jacobsonRadicalPostcomp k X Y g f) :=
  irreducibleMorphismPostcomp_irreducibleMorphismMk k X Y g f

@[simp]
theorem residueOp_smul_irreducibleMorphismMk (a : (End X)ᵐᵒᵖ)
    (f : jacobsonRadicalSubmodule k X Y) :
    (Ideal.Quotient.mk (Ring.jacobson (End X)ᵐᵒᵖ) a) • irreducibleMorphismMk k X Y f =
      irreducibleMorphismMk k X Y (jacobsonRadicalPrecomp k X Y a.unop f) :=
  irreducibleMorphismPrecomp_irreducibleMorphismMk k X Y a.unop f

variable (k X Y)

/-- The residue action of the target commutes with the base scalars, postcomposition being
`k`-linear. -/
instance instSMulCommClassResiduePostcomp :
    SMulCommClass k (End Y ⧸ Ring.jacobson (End Y)) (irreducibleMorphismSpace k X Y) where
  smul_comm c g m := ((irreducibleMorphismResiduePostcompHom k X Y g).map_smul c m).symm

/-- The residue action of the source commutes with the base scalars, precomposition being
`k`-linear. -/
instance instSMulCommClassResiduePrecomp :
    SMulCommClass k ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
      (irreducibleMorphismSpace k X Y) where
  smul_comm c a m := ((irreducibleMorphismResiduePrecompHom k X Y a).map_smul c m).symm

/-- **The two residue actions commute**, so the space of irreducible morphisms is a bimodule over
the residue ring of the source and that of the target: `a ≫ (f ≫ g)` and `(a ≫ f) ≫ g` are the
same morphism. -/
instance instSMulCommClassResidue :
    SMulCommClass ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (End Y ⧸ Ring.jacobson (End Y))
      (irreducibleMorphismSpace k X Y) where
  smul_comm A B m := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective A
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective B
    obtain ⟨f, rfl⟩ := irreducibleMorphismMk_surjective m
    simp only [residue_smul_irreducibleMorphismMk, residueOp_smul_irreducibleMorphismMk]
    congr 1
    ext
    simp

end Residue

/-! ### The arrow multiplicity -/

section Rank

variable {k : Type*} [Ring k] [Linear k C] [Limits.HasBinaryBiproducts C]
variable {X Y : C} [IsLocalRing (End X)] [IsLocalRing (End Y)]

/-- **The arrow multiplicity is positive exactly when an irreducible morphism exists.**

The residue ring of a local endomorphism ring is a division ring, so the space of irreducible
morphisms is a vector space over it and has a rank; that rank is the number of arrows `X → Y` of
the Auslander-Reiten quiver, and it is positive exactly when there is an irreducible morphism
`X ⟶ Y`. -/
theorem rank_irreducibleMorphismSpace_pos_iff :
    0 < Module.rank (End Y ⧸ Ring.jacobson (End Y)) (irreducibleMorphismSpace k X Y) ↔
      ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  rw [rank_pos_iff_nontrivial]
  exact nontrivial_irreducibleMorphismSpace_iff

/-- **The arrow multiplicity read on the source side.** The residue ring of the opposite of a local
endomorphism ring is again a division ring, and the rank over it is positive under exactly the same
condition as the rank over the residue ring of the target. -/
theorem rank_irreducibleMorphismSpace_op_pos_iff :
    0 < Module.rank ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
        (irreducibleMorphismSpace k X Y) ↔
      ∃ f : X ⟶ Y, IsIrreducibleMorphism f := by
  rw [rank_pos_iff_nontrivial]
  exact nontrivial_irreducibleMorphismSpace_iff

end Rank

end TauCeti
