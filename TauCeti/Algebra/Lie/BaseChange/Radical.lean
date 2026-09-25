/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Lie.CartanCriterion
public import TauCeti.Algebra.Lie.Killing.BaseChange
public import TauCeti.Algebra.Lie.BaseChange.Quotient
public import TauCeti.Algebra.Lie.BaseChange.Range
public import TauCeti.Algebra.Lie.Nilradical
public import TauCeti.Algebra.Lie.Solvable

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

Ascent — transferring either property from `I` to `I.baseChange A` — asks nothing of `A`.  Descent,
the `→` direction of the equivalences as displayed, is exactly where faithful flatness enters,
through `Submodule.baseChange_inj`: a term of either series can vanish after extending scalars
only if it vanished already.  Applied to the two largest ideals, ascent gives

```text
(radical R L).baseChange A ≤ radical A (A ⊗[R] L),
(nilradical R L).baseChange A ≤ nilradical A (A ⊗[R] L).
```

Neither containment is forced to be an equality by the transfer principles, because an ideal of
`A ⊗[R] L` need not be extended from `L` at all, and nothing above bounds the ideals that are
not.  The case where both sides are `⊥` is the separate statement
`LieAlgebra.hasTrivialRadical_baseChange_iff`: over a field of characteristic zero a
finite-dimensional Lie algebra has trivial radical exactly when some field extension of it does,
so extending scalars can neither destroy nor *create* a solvable ideal of a semisimple algebra.

For a finite-dimensional Lie algebra over a field of characteristic zero the containment is an
equality: `LieAlgebra.radical_baseChange` says the radical commutes with a field extension, and
`LieAlgebra.one_tmul_mem_radical_baseChange_iff` reads that as a criterion, so membership in the
radical may be tested after extending scalars.  The corresponding statement for the nilradical is
*not* proved here and does not follow, since `L ⧸ nilradical K L` need not have trivial
nilradical.

## Main results

* `LieIdeal.lcs_baseChange`: the series `⁅I, ⁅I, … ⁅I, M⁆…⁆⁆` commutes with extension of scalars.
* `LieIdeal.isSolvable_baseChange_iff` and `LieIdeal.isNilpotent_baseChange_iff`: **an ideal is
  solvable, respectively nilpotent, exactly when its faithfully flat extension of scalars is.**
* `LieAlgebra.baseChange_radical_le` and `LieAlgebra.baseChange_nilradical_le`: the extension of
  the radical, respectively of the nilradical, lands in the radical, respectively the nilradical,
  of the extended algebra.
* `LieAlgebra.hasTrivialRadical_baseChange_iff`: **in characteristic zero a finite-dimensional Lie
  algebra has trivial radical exactly when its extension to a field extension does.**
* `LieAlgebra.radical_baseChange`: **in characteristic zero the solvable radical of a
  finite-dimensional Lie algebra commutes with a field extension**, with
  `LieAlgebra.one_tmul_mem_radical_baseChange_iff` reading it as a membership criterion that may
  be checked after extending scalars.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975], Chapter I, §5 and §6,
  for solvability, nilpotency and the radical under extension of scalars.
-/

public section

open TensorProduct

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (A : Type*) [CommRing A] [Algebra R A]

section Module

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The series `⁅I, ⁅I, … ⁅I, M⁆…⁆⁆` commutes with extension of scalars.**  This is the
nilpotency counterpart of Mathlib's `LieAlgebra.derivedSeriesOfIdeal_baseChange`. -/
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
@[simp]
theorem isSolvable_baseChange_iff [Module.FaithfullyFlat R A] :
    LieAlgebra.IsSolvable (I.baseChange A) ↔ LieAlgebra.IsSolvable I := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isSolvable_baseChange A I⟩
  obtain ⟨k, hk⟩ := (LieAlgebra.isSolvable_iff A ↥(I.baseChange A)).mp h
  rw [derivedSeries_eq_bot_iff, LieAlgebra.derivedSeriesOfIdeal_baseChange,
    ← LieSubmodule.toSubmodule_eq_bot, LieSubmodule.coe_baseChange,
    ← Submodule.baseChange_bot (R := R) (M := L) (A := A), Submodule.baseChange_inj,
    LieSubmodule.toSubmodule_eq_bot] at hk
  exact (LieAlgebra.isSolvable_iff R ↥I).mpr ⟨k, (derivedSeries_eq_bot_iff I k).mpr hk⟩

/-- **An ideal is nilpotent exactly when its faithfully flat extension of scalars is nilpotent.** -/
@[simp]
theorem isNilpotent_baseChange_iff [Module.FaithfullyFlat R A] :
    LieRing.IsNilpotent (I.baseChange A) ↔ LieRing.IsNilpotent I := by
  rw [isNilpotent_iff_exists_lcs_eq_bot, isNilpotent_iff_exists_lcs_eq_bot]
  refine exists_congr fun k ↦ ?_
  rw [lcs_baseChange, ← LieSubmodule.toSubmodule_eq_bot, LieSubmodule.coe_baseChange,
    ← Submodule.baseChange_bot (R := R) (M := L) (A := A), Submodule.baseChange_inj,
    LieSubmodule.toSubmodule_eq_bot]

end LieIdeal

namespace LieAlgebra

section Noetherian

open TauCeti.LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- **The extension of scalars of the solvable radical lands in the solvable radical.**  Nothing
formal makes the containment an equality, since an ideal of `A ⊗[R] L` need not be extended from
`L`; over a field of characteristic zero it is one, which is `LieAlgebra.radical_baseChange`. -/
theorem baseChange_radical_le [IsNoetherian R L] :
    (radical R L).baseChange A ≤ radical A (A ⊗[R] L) :=
  le_sSup (LieIdeal.isSolvable_baseChange A (radical R L))

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
speaks of ideals extended from `L`.  Characteristic zero is a genuine hypothesis here, not a
convenience. -/
@[simp]
theorem hasTrivialRadical_baseChange_iff :
    HasTrivialRadical A (A ⊗[K] L) ↔ HasTrivialRadical K L := by
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [hasTrivialRadical_iff_isKilling, hasTrivialRadical_iff_isKilling]
  exact TauCeti.isKilling_baseChange_iff K A L

/-- **In characteristic zero the solvable radical commutes with a field extension.**  For a
finite-dimensional Lie algebra `L` over a field `K` of characteristic zero and a field extension
`A` of `K`, the radical of `A ⊗[K] L` is the extension of scalars of the radical of `L`.

Characteristic zero is a genuine hypothesis, not a convenience.  The equality determines the
radical of `A ⊗[K] L` completely, although it says nothing about individual solvable ideals of
`A ⊗[K] L`, which need not themselves be extended from `L`; as a test for membership in the
radical it is `LieAlgebra.one_tmul_mem_radical_baseChange_iff`. -/
@[simp]
theorem radical_baseChange :
    radical A (A ⊗[K] L) = (radical K L).baseChange A := by
  -- the extension of `L ⧸ radical K L` has trivial radical, ...
  have _ : HasTrivialRadical A (A ⊗[K] (L ⧸ radical K L)) :=
    (hasTrivialRadical_baseChange_iff K (L ⧸ radical K L) A).mpr inferInstance
  have _ : IsSolvable ↥((radical K L).baseChange A) :=
    LieIdeal.isSolvable_baseChange A (radical K L)
  -- ... and extension of scalars identifies it with the quotient by the extended radical, ...
  have htriv : HasTrivialRadical A ((A ⊗[K] L) ⧸ (radical K L).baseChange A) :=
    hasTrivialRadical_of_equiv (LieIdeal.quotientBaseChangeEquiv A (radical K L)).symm
  -- ... so the extended radical is a solvable ideal whose quotient has trivial radical, and the
  -- radical is the only ideal of that kind.
  exact ((hasTrivialRadical_quotient_iff _).mp htriv).symm

/-- **Membership in the radical may be checked after a field extension.**  In characteristic zero
a vector of a finite-dimensional Lie algebra lies in the solvable radical exactly when its
canonical image in an extension of scalars does. -/
theorem one_tmul_mem_radical_baseChange_iff (x : L) :
    (1 : A) ⊗ₜ[K] x ∈ radical A (A ⊗[K] L) ↔ x ∈ radical K L := by
  rw [radical_baseChange, LieSubmodule.one_tmul_mem_baseChange_iff]

end CharZero

end LieAlgebra
