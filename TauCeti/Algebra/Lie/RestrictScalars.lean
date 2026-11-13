/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Restriction of scalars for Lie ideals and quotients

`LieAlgebra.restrictScalars` equips a compatible scalar action with its restricted
Lie algebra structure. Lie subalgebras inherit this structure, and Lie
submodules restrict scalars on the same carrier. In particular, an ideal of
an `S`-Lie algebra remains an ideal for a compatible `R`-Lie algebra structure.
The quotient by the restricted ideal is canonically isomorphic to the scalar
restriction of the original quotient. Lie homomorphisms also restrict scalars,
and the quotient comparison commutes with the canonical quotient maps.

The quotient comparison refines Mathlib's
`Submodule.Quotient.restrictScalarsEquiv` by retaining the Lie bracket.

Adapted from `Mei/Algebra/Lie/RestrictScalars.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

/-- A Lie algebra remains a Lie algebra over any compatible restricted scalar action.
Install this structure locally when the smaller scalar action has been supplied. -/
@[instance_reducible]
def LieAlgebra.restrictScalars (R S L : Type*) [CommRing R] [CommRing S]
    [LieRing L] [LieAlgebra S L] [Module R L] [SMul R S] [IsScalarTower R S L] :
    LieAlgebra R L where
  lie_smul r x y := by
    rw [← smul_one_smul S r y, lie_smul, smul_one_smul]

namespace LieSubalgebra

variable {R S L : Type*} [CommRing R] [CommRing S] [LieRing L]
  [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]

/-- A Lie subalgebra retains the ambient Lie algebra structure over restricted scalars. -/
instance instLieAlgebraRestrictScalars (K : LieSubalgebra S L) : LieAlgebra R K where
  lie_smul r x y := Subtype.ext (lie_smul r (x : L) (y : L))

end LieSubalgebra

namespace LieModule

/-- A Lie module remains linear over any compatible restricted scalar action. -/
theorem restrictScalars (R S L M : Type*) [CommRing R] [CommRing S]
    [LieRing L] [LieAlgebra S L] [LieAlgebra R L]
    [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S L] [IsScalarTower R S M]
    [LieRingModule L M] [LieModule S L M] : LieModule R L M where
  smul_lie r x m := by
    rw [← smul_one_smul S r x, smul_lie, smul_one_smul]
  lie_smul r x m := by
    rw [← smul_one_smul S r m, lie_smul, smul_one_smul]

end LieModule

namespace LieSubmodule

variable {R S L M : Type*} [CommRing R] [CommRing S] [LieRing L]
  [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
  [IsScalarTower R S M] [LieRingModule L M]

/-- Regard a Lie submodule over `S` as a Lie submodule over `R` on the same carrier. -/
def restrictScalars (N : LieSubmodule S L M) (R : Type*) [CommRing R]
    [Module R M] [SMul R S] [IsScalarTower R S M] : LieSubmodule R L M where
  toSubmodule := N.toSubmodule.restrictScalars R
  lie_mem := N.lie_mem

/-- Restricting a Lie submodule restricts its underlying submodule. -/
@[simp]
theorem restrictScalars_toSubmodule (N : LieSubmodule S L M) :
    (N.restrictScalars R).toSubmodule = N.toSubmodule.restrictScalars R := (rfl)

/-- Scalar restriction preserves membership in a Lie submodule. -/
@[simp]
theorem mem_restrictScalars (N : LieSubmodule S L M) (x : M) :
    x ∈ N.restrictScalars R ↔ x ∈ N := Iff.rfl

/-- Scalar restriction does not identify distinct Lie submodules. -/
theorem restrictScalars_injective :
    Function.Injective (fun N : LieSubmodule S L M => N.restrictScalars R) := by
  intro N N' h
  ext x
  exact Iff.of_eq (congrArg (fun P : LieSubmodule R L M => x ∈ P) h)

/-- Restricting scalars to the original ring fixes a Lie submodule. -/
@[simp]
theorem restrictScalars_self (N : LieSubmodule S L M) : N.restrictScalars S = N := by
  ext x
  rfl

/-- Successive compatible scalar restrictions agree with direct restriction. -/
@[simp]
theorem restrictScalars_restrictScalars {T : Type*} [CommRing T] [Module T M]
    [SMul T S] [SMul R T] [IsScalarTower T S M] [IsScalarTower R T M]
    (N : LieSubmodule S L M) :
    (N.restrictScalars T).restrictScalars R = N.restrictScalars R := by
  ext x
  rfl

/-- A Lie module quotient retains compatibility between its original and restricted scalars. -/
instance Quotient.instIsScalarTower (N : LieSubmodule S L M) : IsScalarTower R S (M ⧸ N) :=
  inferInstanceAs (IsScalarTower R S (M ⧸ N.toSubmodule))

end LieSubmodule

namespace LieHom

variable {R S L L' L'' : Type*} [CommRing R] [CommRing S]
  [LieRing L] [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]
  [LieRing L'] [LieAlgebra S L'] [LieAlgebra R L'] [IsScalarTower R S L']
  [LieRing L''] [LieAlgebra S L''] [LieAlgebra R L''] [IsScalarTower R S L'']

/-- Restrict the scalars of a Lie homomorphism along compatible scalar actions. -/
def restrictScalars (f : L →ₗ⁅S⁆ L') (R : Type*) [CommRing R]
    [LieAlgebra R L] [LieAlgebra R L'] [SMul R S]
    [IsScalarTower R S L] [IsScalarTower R S L'] : L →ₗ⁅R⁆ L' where
  toLinearMap := f.toLinearMap.restrictScalars R
  map_lie' {x y} := f.map_lie x y

/-- The underlying linear map is Mathlib's restriction of scalars. -/
@[simp]
theorem restrictScalars_toLinearMap (f : L →ₗ⁅S⁆ L') :
    (f.restrictScalars R).toLinearMap = f.toLinearMap.restrictScalars R := (rfl)

/-- Scalar restriction leaves the values of a Lie homomorphism unchanged. -/
@[simp]
theorem restrictScalars_apply (f : L →ₗ⁅S⁆ L') (x : L) :
    f.restrictScalars R x = f x := (rfl)

/-- Scalar restriction preserves the identity homomorphism. -/
@[simp]
theorem restrictScalars_id :
    (LieHom.id : L →ₗ⁅S⁆ L).restrictScalars R = LieHom.id := by
  ext x
  rfl

/-- Scalar restriction preserves composition of Lie homomorphisms. -/
@[simp]
theorem restrictScalars_comp (g : L' →ₗ⁅S⁆ L'') (f : L →ₗ⁅S⁆ L') :
    (g.comp f).restrictScalars R = (g.restrictScalars R).comp (f.restrictScalars R) := by
  ext x
  rfl

end LieHom

namespace LieIdeal

variable {R S L : Type*} [CommRing R] [CommRing S] [LieRing L]
  [LieAlgebra S L] [LieAlgebra R L] [SMul R S] [IsScalarTower R S L]

/-- A Lie quotient retains every compatible scalar action on its ambient Lie algebra. -/
instance instLieAlgebraQuotientRestrictScalars (I : LieIdeal S L) :
    LieAlgebra R (L ⧸ I) where
  toModule := LieSubmodule.Quotient.module' (N := I)
  lie_smul t x y := by
    induction x using Submodule.Quotient.induction_on with | _ x
    induction y using Submodule.Quotient.induction_on with | _ y
    rw [← Submodule.Quotient.mk_smul, ← LieSubmodule.Quotient.mk_bracket,
      lie_smul, ← LieSubmodule.Quotient.mk_bracket I x y]
    exact Submodule.Quotient.mk_smul I.toSubmodule t ⁅x, y⁆

/-- Quotienting by a Lie ideal commutes with restriction of scalars. -/
def quotientRestrictScalarsEquiv (I : LieIdeal S L) (R : Type*) [CommRing R]
    [LieAlgebra R L] [SMul R S] [IsScalarTower R S L] :
    (L ⧸ I.restrictScalars R) ≃ₗ⁅R⁆ L ⧸ I where
  -- Restricting a Lie ideal restricts its underlying submodule definitionally.
  __ := Submodule.Quotient.restrictScalarsEquiv R I.toSubmodule
  map_lie' {x y} := by
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    -- The underlying equivalence preserves representatives definitionally.
    rfl

/-- The comparison sends the class of `x` to its class in the original quotient. -/
@[simp]
theorem quotientRestrictScalarsEquiv_mk (I : LieIdeal S L) (x : L) :
    I.quotientRestrictScalarsEquiv R (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  Submodule.Quotient.restrictScalarsEquiv_mk R I.toSubmodule x

/-- The inverse comparison also preserves representatives. -/
@[simp]
theorem quotientRestrictScalarsEquiv_symm_mk (I : LieIdeal S L) (x : L) :
    (I.quotientRestrictScalarsEquiv R).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  Submodule.Quotient.restrictScalarsEquiv_symm_mk R I.toSubmodule x

/-- The comparison intertwines the two canonical quotient homomorphisms. -/
@[simp]
theorem quotientRestrictScalarsEquiv_comp_mkQ (I : LieIdeal S L) :
    (I.quotientRestrictScalarsEquiv R).toLieHom.comp (LieIdeal.mkQ (I.restrictScalars R)) =
      I.mkQ.restrictScalars R := by
  apply LieHom.ext
  intro x
  exact I.quotientRestrictScalarsEquiv_mk (R := R) x

end LieIdeal
