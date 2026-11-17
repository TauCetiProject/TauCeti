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

When every Lie module endomorphism of a nonzero module `M` is a scalar, as for an absolutely
irreducible finite-dimensional module, the centre acts by scalars, and reading off the scalar is a
`K`-algebra homomorphism `Z(U(L)) →ₐ[K] K`
(`TauCeti.UniversalEnvelopingAlgebra.scalarCentralCharacter`). This applies over any field, in
particular to real absolutely irreducible modules.

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

* `TauCeti.UniversalEnvelopingAlgebra.scalarCentralCharacter`: the central character of a nonzero
  module all of whose Lie module endomorphisms are scalars, over any field.
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter`: the central character of a
  finite-dimensional irreducible module over an algebraically closed field.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.representation_eq_scalarCentralCharacter_smul`: a central
  element acts by its central character, which is its eigenvalue on any nonzero vector
  (`scalarCentralCharacter_eq_of_ne_zero_of_representation_eq_smul`).
* `TauCeti.UniversalEnvelopingAlgebra.centralCharacter_eq_scalarCentralCharacter`: over an
  algebraically closed field the two constructions agree.

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

variable (K : Type u) (L : Type v) (M : Type w)
variable [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

attribute [local instance] asModule isScalarTower_asModule

/-- If every Lie module endomorphism of a nonzero module is a scalar, then the structure map from
`K` to the `U(L)`-linear endomorphisms is bijective. -/
private theorem algebraMap_end_bijective_of_forall_exists_smul [Nontrivial M]
    (h : ∀ f : M →ₗ⁅K,L⁆ M, ∃ c : K, ∀ m, f m = c • m) :
    Function.Bijective (algebraMap K (Module.End (U K L) M)) := by
  refine ⟨fun a b hab => ?_, fun f => ?_⟩
  · obtain ⟨m, hm⟩ := exists_ne (0 : M)
    exact smul_left_injective K hm (by simpa using LinearMap.congr_fun hab m)
  · obtain ⟨c, hc⟩ := h ((lieModuleHomEquiv (asModule_ι_smul K L M) (asModule_ι_smul K L M)).symm f)
    exact ⟨c, LinearMap.ext fun m => by simpa using (hc m).symm⟩

/-- **The central character** of a nonzero Lie module all of whose Lie module endomorphisms are
scalars, over any field: a central element of `U(L)` then acts by a scalar, and taking that scalar
is a `K`-algebra homomorphism `Z(U(L)) →ₐ[K] K`.

For a finite-dimensional irreducible module the hypothesis says that the module is absolutely
irreducible. It holds over an algebraically closed field by Schur's lemma, where this is
`TauCeti.UniversalEnvelopingAlgebra.centralCharacter`, but fails for the real circle rotation
module, on which the centre acts through `ℂ`. -/
noncomputable def scalarCentralCharacter [Nontrivial M]
    (h : ∀ f : M →ₗ⁅K,L⁆ M, ∃ c : K, ∀ m, f m = c • m) :
    Subalgebra.center K (U K L) →ₐ[K] K :=
  centralCharacterOfBijective K (U K L) M (algebraMap_end_bijective_of_forall_exists_smul K L M h)

variable [Nontrivial M] (h : ∀ f : M →ₗ⁅K,L⁆ M, ∃ c : K, ∀ m, f m = c • m)

/-- **A central element acts by its central character.** -/
@[simp]
theorem representation_eq_scalarCentralCharacter_smul (z : Subalgebra.center K (U K L)) (m : M) :
    representation K L M (z : U K L) m = scalarCentralCharacter K L M h z • m :=
  (asModule_smul_def K L M (z : U K L) m).symm.trans
    (smul_eq_centralCharacterOfBijective_smul K (U K L) M _ z m)

variable {K L M h}

/-- The central character is the eigenvalue of a central element on any nonzero vector. -/
theorem scalarCentralCharacter_eq_of_ne_zero_of_representation_eq_smul
    {z : Subalgebra.center K (U K L)} {c : K} {m : M} (hm : m ≠ 0)
    (hc : representation K L M (z : U K L) m = c • m) :
    scalarCentralCharacter K L M h z = c :=
  smul_left_injective K hm
    ((representation_eq_scalarCentralCharacter_smul K L M h z m).symm.trans hc)

variable (K L M h) in
/-- The whole module is the centre eigenspace of its central character. -/
@[simp]
theorem centerEigenspace_scalarCentralCharacter :
    centerEigenspace K L M (scalarCentralCharacter K L M h) = ⊤ :=
  centerEigenspace_eq_top_iff.2 (representation_eq_scalarCentralCharacter_smul K L M h)

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

/-- Over an algebraically closed field, the central character of a finite-dimensional irreducible
module is its central character as a module with scalar endomorphisms. -/
theorem centralCharacter_eq_scalarCentralCharacter [Nontrivial M]
    (h : ∀ f : M →ₗ⁅K,L⁆ M, ∃ c : K, ∀ m, f m = c • m) :
    centralCharacter K L M = scalarCentralCharacter K L M h := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  ext z
  exact (scalarCentralCharacter_eq_of_ne_zero_of_representation_eq_smul hm
    (representation_eq_centralCharacter_smul K L M z m)).symm

end IsAlgClosed

end TauCeti.UniversalEnvelopingAlgebra
