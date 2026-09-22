/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Lie.CartanCriterion
public import TauCeti.Algebra.Lie.Killing.BaseChange
public import TauCeti.Algebra.Lie.Nilradical

/-!
# Solvability, nilpotency and semisimplicity under extension of scalars

Let `L` be a Lie algebra over a commutative ring `R` and let `A` be an `R`-algebra.  Mathlib's
`LieSubmodule.baseChange` extends an ideal `I` of `L` to the ideal `I.baseChange A` of `A ⊗[R] L`,
and `LieAlgebra.derivedSeriesOfIdeal_baseChange` computes the derived series of an extended ideal
by extending the derived series term by term.  This file records the same statement for the series
`L ≥ ⁅I, L⁆ ≥ ⁅I, ⁅I, L⁆⁆ ≥ ⋯` that measures nilpotency of an ideal, and reads both series off as
transfer principles:

```text
IsSolvable ↥(I.baseChange A) ↔ IsSolvable ↥I,   IsNilpotent ↥(I.baseChange A) ↔ IsNilpotent ↥I
```

The forward implications ask nothing of `A`.  The reverse implications are exactly where faithful
flatness enters, through `Module.FaithfullyFlat.one_tmul_eq_zero_iff`: a term of either series can
vanish after extending scalars only if it vanished already.  Applied to the two largest ideals,
the forward implications give

```text
(radical R L).baseChange A ≤ radical A (A ⊗[R] L),
(nilradical R L).baseChange A ≤ nilradical A (A ⊗[R] L).
```

Neither containment is forced to be an equality by the transfer principles, because an ideal of
`A ⊗[R] L` need not be extended from `L` at all, and nothing above bounds the ideals that are
not.  The case where both sides are `⊥` is settled here, and it is the case a structural argument
over an algebraic closure rests on: `LieAlgebra.hasTrivialRadical_baseChange_iff` says that over
a field of characteristic zero a finite-dimensional Lie algebra has trivial radical exactly when
some field extension of it does, so extending scalars can neither destroy nor *create* a solvable
ideal of a semisimple algebra.  That equivalence is not a formal consequence of the transfer
principles above; it runs through Cartan's criterion, which converts triviality of the radical
into nondegeneracy of the Killing form, a property `TauCeti.isKilling_baseChange_iff` does
transport in both directions.

## Main results

* `LieIdeal.lcs_baseChange`: the series `⁅I, ⁅I, … ⁅I, M⁆…⁆⁆` commutes with extension of scalars.
* `LieIdeal.isSolvable_baseChange_iff` and `LieIdeal.isNilpotent_baseChange_iff`: **an ideal is
  solvable, respectively nilpotent, exactly when its faithfully flat extension of scalars is.**
* `LieAlgebra.baseChange_radical_le` and `LieAlgebra.baseChange_nilradical_le`: the extension of
  the radical, respectively of the nilradical, lands in the radical, respectively the nilradical,
  of the extended algebra.
* `LieAlgebra.hasTrivialRadical_baseChange_iff`: **in characteristic zero a finite-dimensional Lie
  algebra has trivial radical exactly when its extension to a field extension does.**

## Roadmap

This is part of the "scalar extension and descent" milestone of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/AdoIwasawa/README.md`, which asks for the behaviour of `nil`
and `radical` under base change to an algebraic closure so that a containment of ideals may be
checked after extension and descended.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975], Chapter I, §5 and §6,
  for solvability, nilpotency and the radical under extension of scalars.
-/

public section

open TensorProduct

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- **A faithfully flat extension of scalars detects the zero submodule.**  Over a general
`R`-algebra the extension of a nonzero submodule can collapse; faithful flatness is exactly what
rules that out. -/
@[simp]
theorem baseChange_eq_bot_iff [Module.FaithfullyFlat R A] (N : LieSubmodule R L M) :
    N.baseChange A = ⊥ ↔ N = ⊥ := by
  refine ⟨fun h ↦ _root_.eq_bot_iff.mpr fun x hx ↦ ?_, fun h ↦ by rw [h, baseChange_bot]⟩
  have hx' : (1 : A) ⊗ₜ[R] x ∈ N.baseChange A := tmul_mem_baseChange_of_mem 1 hx
  rw [h, mem_bot, Module.FaithfullyFlat.one_tmul_eq_zero_iff] at hx'
  rw [mem_bot, hx']

end LieSubmodule

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (A : Type*) [CommRing A] [Algebra R A]

section Module

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The series `⁅I, ⁅I, … ⁅I, M⁆…⁆⁆` commutes with extension of scalars.**  This is the
nilpotency counterpart of Mathlib's `LieAlgebra.derivedSeriesOfIdeal_baseChange`, and as there the
whole content is that `LieSubmodule.lie_baseChange` extends a bracket of submodules. -/
@[simp]
theorem lcs_baseChange (I : LieIdeal R L) (k : ℕ) :
    lcs (I.baseChange A) (A ⊗[R] M) k = (I.lcs M k).baseChange A := by
  induction k with
  | zero => simp
  | succ k ih => rw [lcs_succ, ih, lcs_succ, LieSubmodule.lie_baseChange]

end Module

variable (I : LieIdeal R L)

/-- The extension of scalars of a solvable ideal is solvable.  No hypothesis on the coefficient
algebra is needed in this direction. -/
theorem isSolvable_baseChange [LieAlgebra.IsSolvable I] :
    LieAlgebra.IsSolvable (I.baseChange A) := by
  obtain ⟨k, hk⟩ := (LieAlgebra.isSolvable_iff R ↥I).mp inferInstance
  rw [derivedSeries_eq_bot_iff] at hk
  refine (LieAlgebra.isSolvable_iff A ↥(I.baseChange A)).mpr ⟨k, ?_⟩
  rw [derivedSeries_eq_bot_iff, LieAlgebra.derivedSeriesOfIdeal_baseChange, hk,
    LieSubmodule.baseChange_bot]

/-- The extension of scalars of a nilpotent ideal is nilpotent.  No hypothesis on the coefficient
algebra is needed in this direction. -/
theorem isNilpotent_baseChange [LieRing.IsNilpotent I] :
    LieRing.IsNilpotent (I.baseChange A) := by
  obtain ⟨k, hk⟩ := (isNilpotent_iff_exists_lcs_eq_bot I).mp inferInstance
  exact (isNilpotent_iff_exists_lcs_eq_bot _).mpr
    ⟨k, by rw [lcs_baseChange, hk, LieSubmodule.baseChange_bot]⟩

/-- **An ideal is solvable exactly when its faithfully flat extension of scalars is solvable.** -/
theorem isSolvable_baseChange_iff [Module.FaithfullyFlat R A] :
    LieAlgebra.IsSolvable (I.baseChange A) ↔ LieAlgebra.IsSolvable I := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isSolvable_baseChange A I⟩
  obtain ⟨k, hk⟩ := (LieAlgebra.isSolvable_iff A ↥(I.baseChange A)).mp h
  rw [derivedSeries_eq_bot_iff, LieAlgebra.derivedSeriesOfIdeal_baseChange,
    LieSubmodule.baseChange_eq_bot_iff] at hk
  exact (LieAlgebra.isSolvable_iff R ↥I).mpr ⟨k, (derivedSeries_eq_bot_iff I k).mpr hk⟩

/-- **An ideal is nilpotent exactly when its faithfully flat extension of scalars is nilpotent.** -/
theorem isNilpotent_baseChange_iff [Module.FaithfullyFlat R A] :
    LieRing.IsNilpotent (I.baseChange A) ↔ LieRing.IsNilpotent I := by
  rw [isNilpotent_iff_exists_lcs_eq_bot, isNilpotent_iff_exists_lcs_eq_bot]
  simp only [lcs_baseChange, LieSubmodule.baseChange_eq_bot_iff]

end LieIdeal

namespace LieAlgebra

section Noetherian

open TauCeti.LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- **The extension of scalars of the solvable radical lands in the solvable radical.**  The
containment is not an equality for formal reasons, since an ideal of `A ⊗[R] L` need not be
extended from `L`; `LieAlgebra.hasTrivialRadical_baseChange_iff` settles the case where both
sides vanish. -/
theorem baseChange_radical_le [IsNoetherian R L] [IsNoetherian A (A ⊗[R] L)] :
    (radical R L).baseChange A ≤ radical A (A ⊗[R] L) :=
  (LieIdeal.solvable_iff_le_radical A (A ⊗[R] L) _).mp
    (LieIdeal.isSolvable_baseChange A (radical R L))

/-- **The extension of scalars of the nilradical lands in the nilradical.** -/
theorem baseChange_nilradical_le [IsNoetherian R L] :
    (nilradical R L).baseChange A ≤ nilradical A (A ⊗[R] L) :=
  LieIdeal.le_nilradical A (A ⊗[R] L) _ (LieIdeal.isNilpotent_baseChange A (nilradical R L))

end Noetherian

section CharZero

variable (K L A : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Field A] [Algebra K A]

/-- **Triviality of the radical is insensitive to a field extension.**  In characteristic zero a
finite-dimensional Lie algebra has trivial radical exactly when its extension of scalars to a
field extension does.

The `←` direction is the substantive one: it says that extending scalars cannot *create* a
solvable ideal.  Neither direction follows from `LieIdeal.isSolvable_baseChange_iff`, which only
speaks of ideals extended from `L`.  Both run through Cartan's criterion instead, which trades
triviality of the radical for nondegeneracy of the Killing form, and nondegeneracy is a statement
about a Gram determinant, so `TauCeti.isKilling_baseChange_iff` transports it in both directions.

Characteristic zero is not decoration: the passage from a trivial radical to a nondegenerate
Killing form fails over fields of positive characteristic. -/
@[simp]
theorem hasTrivialRadical_baseChange_iff :
    HasTrivialRadical A (A ⊗[K] L) ↔ HasTrivialRadical K L := by
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [hasTrivialRadical_iff_isKilling, hasTrivialRadical_iff_isKilling]
  exact TauCeti.isKilling_baseChange_iff K A L

end CharZero

end LieAlgebra
