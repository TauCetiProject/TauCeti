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
module endomorphisms `End_L(M)`. For an irreducible module the commutant is a division algebra,
which need not consist of scalars: on the real circle rotation module `ℝ²` of the abelian Lie
algebra `ℝ`, the central generator acts by a rotation `J` with `J² = -1`.

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

* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter`: the central character of a
  finite-dimensional irreducible module over an algebraically closed field.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.representation_eq_centralCharacter_smul`: a central element
  acts by its central character.
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter_eq_of_ne_zero_of_representation_eq_smul`:
  the central character is the eigenvalue on any nonzero vector.
* `TauCeti.UniversalEnvelopingAlgebra.centerEigenspace_centralCharacter`: the whole module is the
  centre eigenspace of its central character.
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter_congr`: equivalent modules have the same
  central character.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.2.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser, 2002, Section V.5.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

local notation "U" => _root_.UniversalEnvelopingAlgebra

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

/-- **Equivalent modules have the same central character.** -/
theorem centralCharacter_congr {N : Type x} [AddCommGroup N] [Module K N] [LieRingModule L N]
    [LieModule K L N] [FiniteDimensional K N] [LieModule.IsIrreducible K L N]
    (e : M ≃ₗ⁅K,L⁆ N) : centralCharacter K L M = centralCharacter K L N := by
  have _i : Nontrivial M := LieModule.nontrivial_of_isIrreducible K L M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  ext z
  refine (centralCharacter_eq_of_ne_zero_of_representation_eq_smul (m := e m)
    (by simpa using e.injective.ne hm) ?_).symm
  have h := map_representation K L M N (e : M →ₗ⁅K,L⁆ N) (z : U K L) m
  rw [representation_eq_centralCharacter_smul K L M z m, map_smul] at h
  simpa using h.symm

end IsAlgClosed

end TauCeti.UniversalEnvelopingAlgebra
