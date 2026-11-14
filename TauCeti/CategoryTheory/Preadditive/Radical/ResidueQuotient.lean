/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Multiplicity
public import TauCeti.RingTheory.LocalRing.Residue
-- Non-public: the left-right symmetry of the Jacobson radical and the dimension theory of
-- products and of one-dimensional spaces are used only inside proofs.
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.RingTheory.Jacobson.MulOpposite

/-!
# Morphisms modulo the radical as modules over the residue rings

For objects `X` and `Y` of a `k`-linear category, the quotient `(X ⟶ Y) / rad(X, Y)` of the
morphism space by the radical is a `k`-module. Composing with endomorphisms of either end preserves
the radical, and a radical endomorphism pushes every morphism into the radical, so the quotient is
also a module over the residue ring `F_X = End X / rad(End X)` of the source (acting by
precomposition, through the opposite ring) and over the residue ring `F_Y = End Y / rad(End Y)` of
the target (acting by postcomposition). This file builds these two module structures, mirroring
the bimodule structure of the space of irreducible morphisms in
`TauCeti/CategoryTheory/Preadditive/Radical/Bimodule.lean`.

For an object `X` with a local endomorphism ring, `F_X` is a division ring, and its dimension
counts **Krull–Schmidt multiplicities**: if `P : J → C` is a finite family of objects with local
endomorphism rings, then `(X ⟶ ⨁ P) / rad` and `(⨁ P ⟶ X) / rad` both have dimension over `F_X`
the number of indices `j` with `P j ≅ X`. Unlike the `k`-dimensions of
`TauCeti/CategoryTheory/Preadditive/Radical/Multiplicity.lean`, this needs no finiteness over `k`
and no field: it is the count itself, not the count times `dim_k F_X`. Through almost-split
sequences it identifies the valuations of irreducible morphisms with multiplicities
(`TauCeti/CategoryTheory/AlmostSplit/Valuation.lean`).

## Main definitions

* `TauCeti.instModuleResiduePrecompRadicalQuotient` and
  `TauCeti.instModuleResiduePostcompRadicalQuotient`: the module structures over the residue
  rings of the source and of the target.
* `TauCeti.radicalQuotientCongrRight` and `TauCeti.radicalQuotientCongrLeft`: the induced linear
  equivalences over these residue rings for an isomorphism of the other end.
* `TauCeti.instSMulCommClassResidueRadicalQuotient`: the two residue actions commute, so the
  quotient is a bimodule over the two residue rings; the companion `SMulCommClass` and, over a
  commutative `k`, `IsScalarTower` instances make both actions compatible with the scalars of `k`.

## Main results

* `TauCeti.finrank_residueOp_radicalQuotient_biproduct`: the dimension of
  `(X ⟶ ⨁ P) / rad` over the residue division ring of `X` is the multiplicity of `X` in `P`.
* `TauCeti.finrank_residue_radicalQuotient_biproduct`: the same for `(⨁ P ⟶ X) / rad`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Sections V.7 and VII.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] (k : Type*) [Ring k] [Linear k C]

/-! ### Composition on morphisms modulo the radical -/

/-- **Postcomposition with a morphism of targets**, on morphisms modulo the radical. -/
def radicalQuotientPostcomp (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) →ₗ[k]
      ((X ⟶ Y') ⧸ jacobsonRadicalSubmodule k X Y') :=
  (jacobsonRadicalSubmodule k X Y).mapQ _ (Linear.rightComp k X g) fun _ hf =>
    mem_jacobsonRadicalSubmodule.mpr
      (comp_mem_jacobsonRadical_right (mem_jacobsonRadicalSubmodule.mp hf) g)

@[simp]
theorem radicalQuotientPostcomp_mk (X : C) {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    radicalQuotientPostcomp k X g (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f ≫ g) :=
  (rfl)

/-- **Precomposition with a morphism of sources**, on morphisms modulo the radical. -/
def radicalQuotientPrecomp (Y : C) {X X' : C} (g : X' ⟶ X) :
    ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) →ₗ[k]
      ((X' ⟶ Y) ⧸ jacobsonRadicalSubmodule k X' Y) :=
  (jacobsonRadicalSubmodule k X Y).mapQ _ (Linear.leftComp k Y g) fun _ hf =>
    mem_jacobsonRadicalSubmodule.mpr
      (comp_mem_jacobsonRadical_left g (mem_jacobsonRadicalSubmodule.mp hf))

@[simp]
theorem radicalQuotientPrecomp_mk (Y : C) {X X' : C} (g : X' ⟶ X) (f : X ⟶ Y) :
    radicalQuotientPrecomp k Y g (Submodule.Quotient.mk f) = Submodule.Quotient.mk (g ≫ f) :=
  (rfl)

/-- **A finite product of lines and zero spaces** over a division ring has dimension the number of
lines. -/
private theorem finrank_pi_eq_card_of_finrank_eq_one {D : Type*} [DivisionRing D] {J : Type*}
    [Finite J] (M : J → Type*) [∀ j, AddCommGroup (M j)] [∀ j, Module D (M j)] (p : J → Prop)
    (h₁ : ∀ j, p j → finrank D (M j) = 1) (h₀ : ∀ j, ¬p j → Subsingleton (M j)) :
    finrank D (Π j, M j) = Nat.card {j // p j} := by
  classical
  have := Fintype.ofFinite J
  have (j : J) : Module.Finite D (M j) := by
    by_cases h : p j
    · exact Module.finite_of_finrank_eq_succ (h₁ j h)
    · have := h₀ j h
      infer_instance
  have hdim (j : J) : finrank D (M j) = if p j then 1 else 0 := by
    split_ifs with h
    · exact h₁ j h
    · have := h₀ j h
      exact finrank_zero_of_subsingleton
  rw [Module.finrank_pi_fintype]
  simp [hdim, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ### The residue ring of the source -/

section Precomp

variable (X Y : C)

/-- **Precomposition as a ring homomorphism** out of the opposite endomorphism ring of the source,
precomposing by `a₁` and then by `a₂` being precomposing by `a₂ ≫ a₁`. -/
def radicalQuotientPrecompHom :
    (End X)ᵐᵒᵖ →+* Module.End k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) where
  toFun a := radicalQuotientPrecomp k Y a.unop.asHom
  map_one' := by ext; simp [End.one_asHom]
  map_mul' _ _ := by ext; simp [End.mul_asHom]
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Preadditive.add_comp]

@[simp]
theorem radicalQuotientPrecompHom_apply (a : (End X)ᵐᵒᵖ) :
    radicalQuotientPrecompHom k X Y a = radicalQuotientPrecomp k Y a.unop.asHom :=
  (rfl)

/-- **Precomposition, descended to the residue ring of the source**: a radical endomorphism of the
source pushes every morphism into the radical. -/
def radicalQuotientResiduePrecompHom :
    ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) →+*
      Module.End k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) :=
  Ideal.Quotient.lift _ (radicalQuotientPrecompHom k X Y) fun a ha => by
    ext f
    simpa [mem_jacobsonRadicalSubmodule] using
      comp_mem_jacobsonRadical_right (mem_jacobsonRadical_self_iff_mem_jacobson.mpr
        (Ring.mem_jacobson_mulOpposite_iff.mp ha)) f

/-- Morphisms modulo the radical form a module over the residue ring of the opposite endomorphism
ring of the source. -/
instance instModuleResiduePrecompRadicalQuotient :
    Module ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
      ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) :=
  Module.compHom _ (radicalQuotientResiduePrecompHom k X Y)

/-- **Precomposition by a residue class** is precomposition by any representative of it. -/
@[simp]
theorem radicalQuotientResiduePrecompHom_mk (a : (End X)ᵐᵒᵖ) :
    radicalQuotientResiduePrecompHom k X Y (Ideal.Quotient.mk (Ring.jacobson (End X)ᵐᵒᵖ) a) =
      radicalQuotientPrecomp k Y a.unop.asHom :=
  (rfl)

variable {k X Y}

/-- **The residue action of the source is precomposition** by a representative. -/
@[simp]
theorem radicalQuotient_residueOp_smul_mk (a : (End X)ᵐᵒᵖ) (f : X ⟶ Y) :
    Ideal.Quotient.mk (Ring.jacobson (End X)ᵐᵒᵖ) a •
        (Submodule.Quotient.mk f : (X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) =
      Submodule.Quotient.mk (a.unop.asHom ≫ f) :=
  (rfl)

variable (k X) {Y' : C}

/-- **Postcomposition with a morphism of targets**, on morphisms modulo the radical, as a linear
map over the residue ring of the source. -/
def radicalQuotientMapRight (g : Y ⟶ Y') :
    ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) →ₗ[(End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ]
      ((X ⟶ Y') ⧸ jacobsonRadicalSubmodule k X Y') where
  toFun := radicalQuotientPostcomp k X g
  map_add' := map_add _
  map_smul' d q := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    induction q using Submodule.Quotient.induction_on
    simp

@[simp]
theorem radicalQuotientMapRight_mk (g : Y ⟶ Y') (f : X ⟶ Y) :
    radicalQuotientMapRight k X g (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f ≫ g) :=
  (rfl)

/-- **An isomorphism of targets** induces a linear equivalence of morphisms modulo the radical over
the residue ring of the source. -/
def radicalQuotientCongrRight (e : Y ≅ Y') :
    ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) ≃ₗ[(End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ]
      ((X ⟶ Y') ⧸ jacobsonRadicalSubmodule k X Y') :=
  .ofLinearMap (radicalQuotientMapRight k X e.hom) (radicalQuotientMapRight k X e.inv)
    (LinearMap.ext fun q => by induction q using Submodule.Quotient.induction_on; simp)
    (LinearMap.ext fun q => by induction q using Submodule.Quotient.induction_on; simp)

@[simp]
theorem radicalQuotientCongrRight_mk (e : Y ≅ Y') (f : X ⟶ Y) :
    radicalQuotientCongrRight k X e (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (f ≫ e.hom) :=
  (rfl)

@[simp]
theorem radicalQuotientCongrRight_symm_mk (e : Y ≅ Y') (f : X ⟶ Y') :
    (radicalQuotientCongrRight k X e).symm (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (f ≫ e.inv) :=
  (rfl)

/-- **Morphisms into a finite biproduct, modulo the radical, decompose** over the residue ring of
the source, by composing with the projections. -/
private theorem bijective_radicalQuotientMapRight_pi {J : Type*} [Finite J] (P : J → C)
    [HasBiproduct P] :
    Function.Bijective (LinearMap.pi fun j => radicalQuotientMapRight k X (biproduct.π P j)) := by
  refine ⟨fun q₁ q₂ h => ?_, fun q => ?_⟩
  · induction q₁ using Submodule.Quotient.induction_on with | _ f₁
    induction q₂ using Submodule.Quotient.induction_on with | _ f₂
    simp only [funext_iff, LinearMap.pi_apply, radicalQuotientMapRight_mk,
      Submodule.Quotient.eq, mem_jacobsonRadicalSubmodule, ← Preadditive.sub_comp] at h
    rw [Submodule.Quotient.eq, mem_jacobsonRadicalSubmodule,
      mem_jacobsonRadical_biproduct_right_iff]
    exact h
  · choose f hf using fun j => Submodule.Quotient.mk_surjective _ (q j)
    exact ⟨Submodule.Quotient.mk (biproduct.lift f), funext fun j => by simp [hf]⟩

variable [IsLocalRing (End X)]

/-- **An object with a local endomorphism ring has multiplicity one in itself**: modulo the
radical, its endomorphisms form a one-dimensional space over its residue division ring, spanned
by the class of the identity. -/
theorem finrank_residueOp_radicalQuotient_self :
    finrank ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
      ((X ⟶ X) ⧸ jacobsonRadicalSubmodule k X X) = 1 := by
  refine (finrank_eq_one_iff_of_ne_zero' (Submodule.Quotient.mk (𝟙 X)) ?_).mpr fun q => ?_
  · rw [Ne, Submodule.Quotient.mk_eq_zero, mem_jacobsonRadicalSubmodule,
      mem_jacobsonRadical_iff_not_isIso, not_not]
    infer_instance
  · induction q using Submodule.Quotient.induction_on with | _ f
    exact ⟨Ideal.Quotient.mk _ (.op (End.of f)), by simp⟩

/-- **The multiplicity of an object in a finite biproduct, from the source side**: for objects with
local endomorphism rings, the dimension of `(X ⟶ ⨁ P) / rad` over the residue division ring of `X`
is the number of indices `j` with `P j ≅ X`. -/
theorem finrank_residueOp_radicalQuotient_biproduct {J : Type*} [Finite J] (P : J → C)
    [HasBiproduct P] [∀ j, IsLocalRing (End (P j))] :
    finrank ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
        ((X ⟶ ⨁ P) ⧸ jacobsonRadicalSubmodule k X (⨁ P)) =
      Nat.card {j // Nonempty (P j ≅ X)} := by
  rw [(LinearEquiv.ofBijective _ (bijective_radicalQuotientMapRight_pi k X P)).finrank_eq]
  refine finrank_pi_eq_card_of_finrank_eq_one _ _ (fun j ⟨e⟩ => ?_) fun j h =>
    subsingleton_quotient_jacobsonRadicalSubmodule k ⟨fun e => h ⟨e.symm⟩⟩
  rw [(radicalQuotientCongrRight k X e).finrank_eq, finrank_residueOp_radicalQuotient_self]

end Precomp

/-! ### The residue ring of the target -/

section Postcomp

variable (X Y : C)

/-- **Postcomposition as a ring homomorphism** out of the endomorphism ring of the target. -/
def radicalQuotientPostcompHom :
    End Y →+* Module.End k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) where
  toFun g := radicalQuotientPostcomp k X g.asHom
  map_one' := by ext; simp [End.one_asHom]
  map_mul' _ _ := by ext; simp [End.mul_asHom]
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Preadditive.comp_add]

@[simp]
theorem radicalQuotientPostcompHom_apply (g : End Y) :
    radicalQuotientPostcompHom k X Y g = radicalQuotientPostcomp k X g.asHom :=
  (rfl)

/-- **Postcomposition, descended to the residue ring of the target**: a radical endomorphism of the
target pushes every morphism into the radical. -/
def radicalQuotientResiduePostcompHom :
    (End Y ⧸ Ring.jacobson (End Y)) →+*
      Module.End k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) :=
  Ideal.Quotient.lift _ (radicalQuotientPostcompHom k X Y) fun g hg => by
    ext f
    simpa [mem_jacobsonRadicalSubmodule] using
      comp_mem_jacobsonRadical_left f (mem_jacobsonRadical_self_iff_mem_jacobson.mpr hg)

/-- Morphisms modulo the radical form a module over the residue ring of the endomorphism ring of
the target. -/
instance instModuleResiduePostcompRadicalQuotient :
    Module (End Y ⧸ Ring.jacobson (End Y)) ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) :=
  Module.compHom _ (radicalQuotientResiduePostcompHom k X Y)

/-- **Postcomposition by a residue class** is postcomposition by any representative of it. -/
@[simp]
theorem radicalQuotientResiduePostcompHom_mk (g : End Y) :
    radicalQuotientResiduePostcompHom k X Y (Ideal.Quotient.mk (Ring.jacobson (End Y)) g) =
      radicalQuotientPostcomp k X g.asHom :=
  (rfl)

variable {k X Y}

/-- **The residue action of the target is postcomposition** by a representative. -/
@[simp]
theorem radicalQuotient_residue_smul_mk (g : End Y) (f : X ⟶ Y) :
    Ideal.Quotient.mk (Ring.jacobson (End Y)) g •
        (Submodule.Quotient.mk f : (X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) =
      Submodule.Quotient.mk (f ≫ g.asHom) :=
  (rfl)

variable (k Y) {X' : C}

/-- **Precomposition with a morphism of sources**, on morphisms modulo the radical, as a linear
map over the residue ring of the target. -/
def radicalQuotientMapLeft (g : X' ⟶ X) :
    ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) →ₗ[End Y ⧸ Ring.jacobson (End Y)]
      ((X' ⟶ Y) ⧸ jacobsonRadicalSubmodule k X' Y) where
  toFun := radicalQuotientPrecomp k Y g
  map_add' := map_add _
  map_smul' d q := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    induction q using Submodule.Quotient.induction_on
    simp

@[simp]
theorem radicalQuotientMapLeft_mk (g : X' ⟶ X) (f : X ⟶ Y) :
    radicalQuotientMapLeft k Y g (Submodule.Quotient.mk f) = Submodule.Quotient.mk (g ≫ f) :=
  (rfl)

/-- **An isomorphism of sources** induces a linear equivalence of morphisms modulo the radical over
the residue ring of the target. -/
def radicalQuotientCongrLeft (e : X ≅ X') :
    ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) ≃ₗ[End Y ⧸ Ring.jacobson (End Y)]
      ((X' ⟶ Y) ⧸ jacobsonRadicalSubmodule k X' Y) :=
  .ofLinearMap (radicalQuotientMapLeft k Y e.inv) (radicalQuotientMapLeft k Y e.hom)
    (LinearMap.ext fun q => by induction q using Submodule.Quotient.induction_on; simp)
    (LinearMap.ext fun q => by induction q using Submodule.Quotient.induction_on; simp)

@[simp]
theorem radicalQuotientCongrLeft_mk (e : X ≅ X') (f : X ⟶ Y) :
    radicalQuotientCongrLeft k Y e (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (e.inv ≫ f) :=
  (rfl)

@[simp]
theorem radicalQuotientCongrLeft_symm_mk (e : X ≅ X') (f : X' ⟶ Y) :
    (radicalQuotientCongrLeft k Y e).symm (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (e.hom ≫ f) :=
  (rfl)

/-- **Morphisms out of a finite biproduct, modulo the radical, decompose** over the residue ring of
the target, by composing with the inclusions. -/
private theorem bijective_radicalQuotientMapLeft_pi {J : Type*} [Finite J] (P : J → C)
    [HasBiproduct P] :
    Function.Bijective (LinearMap.pi fun j => radicalQuotientMapLeft k Y (biproduct.ι P j)) := by
  refine ⟨fun q₁ q₂ h => ?_, fun q => ?_⟩
  · induction q₁ using Submodule.Quotient.induction_on with | _ f₁
    induction q₂ using Submodule.Quotient.induction_on with | _ f₂
    simp only [funext_iff, LinearMap.pi_apply, radicalQuotientMapLeft_mk,
      Submodule.Quotient.eq, mem_jacobsonRadicalSubmodule, ← Preadditive.comp_sub] at h
    rw [Submodule.Quotient.eq, mem_jacobsonRadicalSubmodule,
      mem_jacobsonRadical_biproduct_left_iff]
    exact h
  · choose f hf using fun j => Submodule.Quotient.mk_surjective _ (q j)
    exact ⟨Submodule.Quotient.mk (biproduct.desc f), funext fun j => by simp [hf]⟩

variable [IsLocalRing (End Y)]

/-- **An object with a local endomorphism ring has multiplicity one in itself**, over the residue
division ring acting by postcomposition. -/
theorem finrank_residue_radicalQuotient_self :
    finrank (End Y ⧸ Ring.jacobson (End Y)) ((Y ⟶ Y) ⧸ jacobsonRadicalSubmodule k Y Y) = 1 := by
  refine (finrank_eq_one_iff_of_ne_zero' (Submodule.Quotient.mk (𝟙 Y)) ?_).mpr fun q => ?_
  · rw [Ne, Submodule.Quotient.mk_eq_zero, mem_jacobsonRadicalSubmodule,
      mem_jacobsonRadical_iff_not_isIso, not_not]
    infer_instance
  · induction q using Submodule.Quotient.induction_on with | _ f
    exact ⟨Ideal.Quotient.mk _ (End.of f), by simp⟩

/-- **The multiplicity of an object in a finite biproduct, from the target side**: for objects with
local endomorphism rings, the dimension of `(⨁ P ⟶ Y) / rad` over the residue division ring of `Y`
is the number of indices `j` with `P j ≅ Y`. -/
theorem finrank_residue_radicalQuotient_biproduct {J : Type*} [Finite J] (P : J → C)
    [HasBiproduct P] [∀ j, IsLocalRing (End (P j))] :
    finrank (End Y ⧸ Ring.jacobson (End Y)) ((⨁ P ⟶ Y) ⧸ jacobsonRadicalSubmodule k (⨁ P) Y) =
      Nat.card {j // Nonempty (P j ≅ Y)} := by
  rw [(LinearEquiv.ofBijective _ (bijective_radicalQuotientMapLeft_pi k Y P)).finrank_eq]
  refine finrank_pi_eq_card_of_finrank_eq_one _ _ (fun j ⟨e⟩ => ?_) fun j h =>
    subsingleton_quotient_jacobsonRadicalSubmodule k ⟨fun e => h ⟨e⟩⟩
  rw [(radicalQuotientCongrLeft k Y e).finrank_eq, finrank_residue_radicalQuotient_self]

end Postcomp

/-! ### Compatibility of the two residue actions -/

section Bimodule

variable (X Y : C)

/-- The residue action of the source commutes with the base scalars, precomposition being
`k`-linear. -/
instance instSMulCommClassResiduePrecompRadicalQuotient :
    SMulCommClass k ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
      ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) where
  smul_comm c a q := ((radicalQuotientResiduePrecompHom k X Y a).map_smul c q).symm

/-- The residue action of the target commutes with the base scalars, postcomposition being
`k`-linear. -/
instance instSMulCommClassResiduePostcompRadicalQuotient :
    SMulCommClass k (End Y ⧸ Ring.jacobson (End Y)) ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) where
  smul_comm c g q := ((radicalQuotientResiduePostcompHom k X Y g).map_smul c q).symm

/-- **The two residue actions commute**, so morphisms modulo the radical form a bimodule over the
residue ring of the source and that of the target: `a ≫ (f ≫ g)` and `(a ≫ f) ≫ g` are the same
morphism. -/
instance instSMulCommClassResidueRadicalQuotient :
    SMulCommClass ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) (End Y ⧸ Ring.jacobson (End Y))
      ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) where
  smul_comm A B q := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective A
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective B
    induction q using Submodule.Quotient.induction_on
    simp

end Bimodule

/-! ### Compatibility with the base scalars -/

section Scalars

variable (k : Type*) [CommRing k] [Linear k C] (X Y : C)

/-- The residue action of the source is compatible with the base scalars:
`k → F_X → (X ⟶ Y) / rad` is a scalar tower. -/
instance instIsScalarTowerResiduePrecompRadicalQuotient :
    IsScalarTower k ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ)
      ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) where
  smul_assoc c A q := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective A
    induction q using Submodule.Quotient.induction_on
    rw [← Ideal.Quotient.mkₐ_eq_mk k, ← map_smul, Ideal.Quotient.mkₐ_eq_mk]
    simp [End.smul_asHom, ← Submodule.Quotient.mk_smul]

/-- The residue action of the target is compatible with the base scalars:
`k → F_Y → (X ⟶ Y) / rad` is a scalar tower. -/
instance instIsScalarTowerResiduePostcompRadicalQuotient :
    IsScalarTower k (End Y ⧸ Ring.jacobson (End Y)) ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) where
  smul_assoc c G q := by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective G
    induction q using Submodule.Quotient.induction_on
    rw [← Ideal.Quotient.mkₐ_eq_mk k, ← map_smul, Ideal.Quotient.mkₐ_eq_mk]
    simp [End.smul_asHom, ← Submodule.Quotient.mk_smul]

end Scalars

end TauCeti
