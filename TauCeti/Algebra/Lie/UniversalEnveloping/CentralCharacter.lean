/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.CenterEigenspace
public import TauCeti.RingTheory.Semisimple.CentralCharacter

/-!
# Central characters of Lie modules

Let `M` be a module over a Lie algebra `L` over a commutative ring `R`, and let
`Z(U(L)) = Subalgebra.center R (UniversalEnvelopingAlgebra R L)`. Viewing `M` as a `U(L)`-module
(`TauCeti.UniversalEnvelopingAlgebra.asModule`), the centre acts through the `R`-algebra
homomorphism `TauCeti.centerToEnd : Z(U(L)) →ₐ[R] End_{U(L)}(M)`, and
`TauCeti.UniversalEnvelopingAlgebra.lieModuleHomEquiv` identifies `End_{U(L)}(M)` with the Lie
module endomorphisms `End_L(M)`. The image lies in the centre of the commutant
(`TauCeti.centerToCenterEnd`). For an irreducible module the commutant is a division algebra, so
this centre is a field, but it need not consist of scalars: on the real circle rotation module
`ℝ²` of the abelian Lie algebra `ℝ`, the central generator acts by a rotation `J` with `J² = -1`.

When `R` acts faithfully on `M` and every Lie module endomorphism of `M` commuting with all others
is a scalar, the centre acts by scalars, and reading off the scalar is an `R`-algebra homomorphism
`Z(U(L)) →ₐ[R] R` (`TauCeti.UniversalEnvelopingAlgebra.centralCharacterOfForallExistsSmul`). Over a
field this covers absolutely irreducible finite-dimensional modules, whose endomorphisms are all
scalars, and also modules whose commutant is a central division algebra, as for the quaternionic
real irreducible modules. The hypothesis says that the commutant `End_{U(L)}(M)` is a central
`R`-algebra (`TauCeti.UniversalEnvelopingAlgebra.isCentral_end_of_forall_exists_smul`), which makes
`R → Z(End_{U(L)}(M))` bijective (`TauCeti.bijective_algebraMap_center_end_of_isCentral`).

Over an algebraically closed field `K`, Schur's lemma makes
every endomorphism of a finite-dimensional irreducible module a scalar. The centre then acts by
scalars, and reading off the scalar is a `K`-algebra homomorphism `Z(U(L)) →ₐ[K] K`, the
**central character** of the module (`TauCeti.UniversalEnvelopingAlgebra.centralCharacter`). It
is the central character `TauCeti.centralCharacter` of `M` as a simple module over `U(L)`, read
through the enveloping-algebra dictionary of `TauCeti/Algebra/Lie/UniversalEnveloping/Module.lean`.
Equivalent modules have the same central character.

The central character of a highest weight module, which may be infinite-dimensional, is
`TauCeti.vermaCentralCharacter`; there the scalar comes from the one-dimensional top weight space,
not from Schur's lemma.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.centralCharacterOfForallExistsSmul`: the central character
  of a faithful module all of whose central Lie module endomorphisms are scalars.
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter`: the central character of a
  finite-dimensional irreducible module over an algebraically closed field.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.representation_eq_centralCharacterOfForallExistsSmul_smul`:
  a central element acts by its central character, which is the only scalar doing so
  (`centralCharacterOfForallExistsSmul_eq_of_representation_eq_smul`) and its eigenvalue on any
  nonzero vector (`centralCharacterOfForallExistsSmul_eq_of_ne_zero_of_representation_eq_smul`).
  It is `TauCeti.centralCharacterOfBijectiveAlgebraMap` of `M` as a `U(L)`-module
  (`centralCharacterOfForallExistsSmul_eq_centralCharacterOfBijectiveAlgebraMap`), so equivalent
  modules have the same central character (`centralCharacterOfForallExistsSmul_congr`).
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter_eq_centralCharacterOfForallExistsSmul`: over
  an algebraically closed field the two constructions agree.
* `TauCeti.UniversalEnvelopingAlgebra.representation_eq_centralCharacter_smul`: a central element
  acts by its central character.
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter_eq_of_ne_zero_of_representation_eq_smul`:
  the central character is the eigenvalue on any nonzero vector.
* `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace_centralCharacter`: the whole module is the
  centre eigenspace of its central character.
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter_congr`: equivalent modules have the same
  central character.

## References

* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §29 (absolutely irreducible modules have scalar commutant).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.2.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Section V.5.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

local notation "U" => _root_.UniversalEnvelopingAlgebra

section Scalar

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] [FaithfulSMul R M]

attribute [local instance] asModule isScalarTower_asModule

/-- **The central character** of a faithful Lie module all of whose central Lie module
endomorphisms are scalars: a central element of `U(L)` then acts by a scalar, and taking that
scalar is an `R`-algebra homomorphism `Z(U(L)) →ₐ[R] R`.

For a finite-dimensional irreducible module over a field the hypothesis holds when the module is
absolutely irreducible, and more generally when its commutant is a central division algebra. It
holds over an algebraically closed field by Schur's lemma, where this is
`TauCeti.UniversalEnvelopingAlgebra.centralCharacter`, but fails for the real circle rotation
module, on which the centre acts through `ℂ`. -/
noncomputable def centralCharacterOfForallExistsSmul
    (h : ∀ f : M →ₗ⁅R,L⁆ M, (∀ g : M →ₗ⁅R,L⁆ M, f.comp g = g.comp f) →
      ∃ c : R, ∀ m, f m = c • m) :
    Subalgebra.center R (U R L) →ₐ[R] R :=
  haveI := isCentral_end_of_forall_exists_smul (asModule_ι_smul R L M) h
  centralCharacterOfBijectiveAlgebraMap R (U R L) M
    (bijective_algebraMap_center_end_of_isCentral R (U R L) M)

variable (h : ∀ f : M →ₗ⁅R,L⁆ M, (∀ g : M →ₗ⁅R,L⁆ M, f.comp g = g.comp f) →
  ∃ c : R, ∀ m, f m = c • m)

/-- **A central element acts by its central character.** -/
theorem representation_eq_centralCharacterOfForallExistsSmul_smul
    (z : Subalgebra.center R (U R L)) (m : M) :
    representation R L M (z : U R L) m = centralCharacterOfForallExistsSmul R L M h z • m :=
  (asModule_smul_def R L M (z : U R L) m).symm.trans
    (smul_eq_centralCharacterOfBijectiveAlgebraMap_smul R (U R L) M _ z m)

variable {R L M h}

/-- The central character is the unique scalar by which a central element acts. -/
theorem centralCharacterOfForallExistsSmul_eq_of_representation_eq_smul
    {z : Subalgebra.center R (U R L)} {c : R}
    (hc : ∀ m : M, representation R L M (z : U R L) m = c • m) :
    centralCharacterOfForallExistsSmul R L M h z = c :=
  centralCharacterOfBijectiveAlgebraMap_eq_of_smul_eq fun m =>
    (asModule_smul_def R L M (z : U R L) m).trans (hc m)

/-- The central character is the eigenvalue of a central element on any nonzero vector. -/
theorem centralCharacterOfForallExistsSmul_eq_of_ne_zero_of_representation_eq_smul
    [IsCancelMulZero R] [Module.IsTorsionFree R M]
    {z : Subalgebra.center R (U R L)} {c : R} {m : M} (hm : m ≠ 0)
    (hc : representation R L M (z : U R L) m = c • m) :
    centralCharacterOfForallExistsSmul R L M h z = c :=
  centralCharacterOfBijectiveAlgebraMap_eq_of_ne_zero_of_smul_eq hm
    ((asModule_smul_def R L M (z : U R L) m).trans hc)

variable (R L M h) in
/-- The whole module is the centre eigenspace of its central character. -/
@[simp]
theorem centerEigenspace_centralCharacterOfForallExistsSmul :
    centerEigenspace R L M (centralCharacterOfForallExistsSmul R L M h) = ⊤ :=
  centerEigenspace_eq_top_iff.2 (representation_eq_centralCharacterOfForallExistsSmul_smul R L M h)

/-- The central character of `M` is `TauCeti.centralCharacterOfBijectiveAlgebraMap` of `M` as a
`U(L)`-module. -/
theorem centralCharacterOfForallExistsSmul_eq_centralCharacterOfBijectiveAlgebraMap
    (hb : Function.Bijective (algebraMap R (Subalgebra.center R (Module.End (U R L) M)))) :
    centralCharacterOfForallExistsSmul R L M h =
      centralCharacterOfBijectiveAlgebraMap R (U R L) M hb := by
  ext z
  exact (centralCharacterOfBijectiveAlgebraMap_eq_of_smul_eq fun m =>
    (asModule_smul_def R L M (z : U R L) m).trans
      (representation_eq_centralCharacterOfForallExistsSmul_smul R L M h z m)).symm

/-- **Equivalent modules have the same central character.** This is
`TauCeti.centralCharacterOfBijectiveAlgebraMap_congr`, read through the enveloping-algebra
dictionary for equivalences. -/
theorem centralCharacterOfForallExistsSmul_congr {N : Type x} [AddCommGroup N] [Module R N]
    [LieRingModule L N] [LieModule R L N] [FaithfulSMul R N]
    {hN : ∀ f : N →ₗ⁅R,L⁆ N, (∀ g : N →ₗ⁅R,L⁆ N, f.comp g = g.comp f) →
      ∃ c : R, ∀ n, f n = c • n}
    (e : M ≃ₗ⁅R,L⁆ N) :
    centralCharacterOfForallExistsSmul R L M h = centralCharacterOfForallExistsSmul R L N hN := by
  have := isCentral_end_of_forall_exists_smul (asModule_ι_smul R L M) h
  have := isCentral_end_of_forall_exists_smul (asModule_ι_smul R L N) hN
  rw [centralCharacterOfForallExistsSmul_eq_centralCharacterOfBijectiveAlgebraMap
      (bijective_algebraMap_center_end_of_isCentral R (U R L) M),
    centralCharacterOfForallExistsSmul_eq_centralCharacterOfBijectiveAlgebraMap
      (bijective_algebraMap_center_end_of_isCentral R (U R L) N)]
  exact centralCharacterOfBijectiveAlgebraMap_congr
    (lieModuleEquivEquivLinearEquiv (asModule_ι_smul R L M) (asModule_ι_smul R L N) e)

end Scalar

section IsAlgClosed

variable (K : Type u) (L : Type v) (M : Type w)
variable [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] [LieModule.IsIrreducible K L M]

attribute [local instance] asModule isScalarTower_asModule

/-- An irreducible Lie module is a simple module over the enveloping algebra; this is the instance
through which `centralCharacter` applies Schur's lemma. -/
private instance : IsSimpleModule (U K L) M :=
  (isIrreducible_iff_isSimpleModule (asModule_ι_smul K L M)).mp inferInstance

/-- **The central character** of a finite-dimensional irreducible Lie module over an algebraically
closed field: by Schur's lemma a central element of `U(L)` acts by a scalar, and taking that scalar
is a `K`-algebra homomorphism `Z(U(L)) →ₐ[K] K`. It is the central character
`TauCeti.centralCharacter` of `M` as a simple module over `U(L)`. -/
noncomputable def centralCharacter : Subalgebra.center K (U K L) →ₐ[K] K :=
  _root_.TauCeti.centralCharacter K (U K L) M

/-- **A central element acts by its central character.** -/
@[simp]
theorem representation_eq_centralCharacter_smul (z : Subalgebra.center K (U K L)) (m : M) :
    representation K L M (z : U K L) m = centralCharacter K L M z • m :=
  (asModule_smul_def K L M (z : U K L) m).symm.trans
    (smul_eq_centralCharacter_smul K (U K L) M z m)

variable {K L M}

/-- The central character is the eigenvalue of a central element on any nonzero vector. -/
theorem centralCharacter_eq_of_ne_zero_of_representation_eq_smul
    {z : Subalgebra.center K (U K L)} {c : K} {m : M} (hm : m ≠ 0)
    (h : representation K L M (z : U K L) m = c • m) :
    centralCharacter K L M z = c :=
  smul_left_injective K hm ((representation_eq_centralCharacter_smul K L M z m).symm.trans h)

variable (K L M) in
/-- The whole module is the centre eigenspace of its central character. -/
@[simp]
theorem centerEigenspace_centralCharacter :
    centerEigenspace K L M (centralCharacter K L M) = ⊤ :=
  centerEigenspace_eq_top_iff.2 (representation_eq_centralCharacter_smul K L M)

/-- The central character of `M` is `TauCeti.centralCharacterOfBijectiveAlgebraMap` of `M` as a
`U(L)`-module. -/
theorem centralCharacter_eq_centralCharacterOfBijectiveAlgebraMap
    (hb : Function.Bijective (algebraMap K (Subalgebra.center K (Module.End (U K L) M)))) :
    centralCharacter K L M = centralCharacterOfBijectiveAlgebraMap K (U K L) M hb := by
  ext z
  exact (centralCharacterOfBijectiveAlgebraMap_eq_of_smul_eq fun m =>
    (asModule_smul_def K L M (z : U K L) m).trans
      (representation_eq_centralCharacter_smul K L M z m)).symm

/-- **Equivalent modules have the same central character.** This is
`TauCeti.centralCharacterOfBijectiveAlgebraMap_congr`, read through the enveloping-algebra
dictionary for equivalences. -/
theorem centralCharacter_congr {N : Type x} [AddCommGroup N] [Module K N] [LieRingModule L N]
    [LieModule K L N] [FiniteDimensional K N] [LieModule.IsIrreducible K L N]
    (e : M ≃ₗ⁅K,L⁆ N) : centralCharacter K L M = centralCharacter K L N := by
  rw [centralCharacter_eq_centralCharacterOfBijectiveAlgebraMap
      (bijective_algebraMap_center_of_bijective
        (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := U K L) (V := M))),
    centralCharacter_eq_centralCharacterOfBijectiveAlgebraMap
      (bijective_algebraMap_center_of_bijective
        (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := U K L) (V := N)))]
  exact centralCharacterOfBijectiveAlgebraMap_congr
    (lieModuleEquivEquivLinearEquiv (asModule_ι_smul K L M) (asModule_ι_smul K L N) e)

/-- Over an algebraically closed field, the central character of a finite-dimensional irreducible
module is its central character as a module with scalar central endomorphisms. -/
theorem centralCharacter_eq_centralCharacterOfForallExistsSmul [FaithfulSMul K M]
    (h : ∀ f : M →ₗ⁅K,L⁆ M, (∀ g : M →ₗ⁅K,L⁆ M, f.comp g = g.comp f) →
      ∃ c : K, ∀ m, f m = c • m) :
    centralCharacter K L M = centralCharacterOfForallExistsSmul K L M h := by
  ext z
  exact (centralCharacterOfForallExistsSmul_eq_of_representation_eq_smul
    (representation_eq_centralCharacter_smul K L M z)).symm

end IsAlgClosed

end TauCeti.UniversalEnvelopingAlgebra
