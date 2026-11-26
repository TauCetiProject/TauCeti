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
public import TauCeti.Algebra.Lie.Solvable.Basic
import TauCeti.Algebra.Lie.BaseChange.Span
import TauCeti.Algebra.TensorProduct.BaseChange

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
through `LieSubmodule.baseChange_inj`: a term of either series can vanish after extending scalars
only if it vanished already. Since extension of scalars preserves suprema of Lie submodules,
ascent applied to all solvable or nilpotent ideals gives, without any Noetherian hypothesis,

```text
(radical R L).baseChange A ≤ radical A (A ⊗[R] L),
(nilradical R L).baseChange A ≤ nilradical A (A ⊗[R] L).
```

Neither containment is forced to be an equality by the transfer principles, because an ideal of
`A ⊗[R] L` need not be extended from `L` at all, and nothing above bounds the ideals that are
not.  The case where both sides are `⊥` is the separate statement
`LieAlgebra.hasTrivialRadical_baseChange_iff`: over a field of characteristic zero a
finite-dimensional Lie algebra has trivial radical exactly when its extension of scalars to a
principal ideal domain does. This includes field extensions: in this setting extension of scalars
preserves and reflects triviality of the radical.

For a finite-dimensional Lie algebra over a field of characteristic zero the containment is an
equality: `LieAlgebra.radical_baseChange` says the radical commutes with extension of scalars to
any principal ideal domain, and
`LieAlgebra.one_tmul_mem_radical_baseChange_iff` reads that as a criterion, so membership in the
radical may be tested after extending scalars.  The corresponding equality for the nilradical does
not follow by the same argument, since `L ⧸ nilradical K L` need not have trivial nilradical.
Membership in the nilradical may nevertheless be tested after any faithfully flat extension of
scalars, with no finiteness hypothesis: `LieAlgebra.one_tmul_mem_nilradical_baseChange_iff`.
The nilradical of `A ⊗[R] L` is also stable under `σ ⊗ id` for every algebra automorphism `σ` of
`A`, which is the input for Galois descent of the nilradical.

## Main results

* `LieIdeal.lcs_baseChange`: the series `⁅I, ⁅I, … ⁅I, M⁆…⁆⁆` commutes with extension of scalars.
* `LieIdeal.isSolvable_baseChange_iff` and `LieIdeal.isNilpotent_baseChange_iff`: **an ideal is
  solvable, respectively nilpotent, exactly when its faithfully flat extension of scalars is.**
* `LieAlgebra.baseChange_radical_le` and `LieAlgebra.baseChange_nilradical_le`: the extension of
  the radical, respectively of the nilradical, lands in the radical, respectively the nilradical,
  of the extended algebra.
* `LieAlgebra.one_tmul_mem_nilradical_baseChange_iff`: **membership in the nilradical may be
  checked after a faithfully flat extension of scalars**, with no finiteness hypothesis.
* `AlgEquiv.tensorProduct_map_mem_lieNilradical`: the nilradical of `A ⊗[R] L` is stable under
  `σ ⊗ id` for every algebra automorphism `σ` of `A`.
* `LieAlgebra.hasTrivialRadical_of_baseChange`: triviality of the radical descends along a
  faithfully flat extension, with no finiteness or characteristic hypothesis.
* `LieAlgebra.hasTrivialRadical_baseChange_iff`: **in characteristic zero a finite-dimensional Lie
  algebra has trivial radical exactly when its extension to a field extension, or any principal
  ideal domain, does.**
* `LieAlgebra.radical_baseChange`: **in characteristic zero the solvable radical of a
  finite-dimensional Lie algebra commutes with extension of scalars to a field extension, or any
  principal ideal domain**, with
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
  simp only [LieAlgebra.isSolvable_iff A, LieAlgebra.isSolvable_iff R,
    derivedSeries_eq_bot_iff, LieAlgebra.derivedSeriesOfIdeal_baseChange,
    ← LieSubmodule.baseChange_bot A (R := R) (L := L) (M := L),
    LieSubmodule.baseChange_inj]

/-- **An ideal is nilpotent exactly when its faithfully flat extension of scalars is nilpotent.** -/
@[simp]
theorem isNilpotent_baseChange_iff [Module.FaithfullyFlat R A] :
    LieRing.IsNilpotent (I.baseChange A) ↔ LieRing.IsNilpotent I := by
  simp only [isNilpotent_iff_exists_lcs_eq_bot, lcs_baseChange,
    ← LieSubmodule.baseChange_bot A (R := R) (L := L) (M := L),
    LieSubmodule.baseChange_inj]

end LieIdeal

namespace LieAlgebra

section CommRing

open TauCeti.LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- **The extension of scalars of the solvable radical lands in the solvable radical.**
No Noetherian hypothesis is needed. An ideal of `A ⊗[R] L` need not be extended from `L`, so the
containment need not be an equality; the characteristic-zero equality is
`LieAlgebra.radical_baseChange`. -/
theorem baseChange_radical_le :
    (radical R L).baseChange A ≤ radical A (A ⊗[R] L) := by
  rw [radical, sSup_eq_iSup]
  simp only [LieSubmodule.baseChange_iSup]
  refine iSup_le fun I ↦ iSup_le fun hI ↦ ?_
  have : IsSolvable I := hI
  exact le_sSup (LieIdeal.isSolvable_baseChange A I)

/-- **The extension of scalars of the nilradical lands in the nilradical.**
No Noetherian hypothesis is needed. -/
theorem baseChange_nilradical_le :
    (nilradical R L).baseChange A ≤ nilradical A (A ⊗[R] L) := by
  rw [nilradical_def, sSup_eq_iSup]
  simp only [LieSubmodule.baseChange_iSup]
  refine iSup_le fun I ↦ iSup_le fun hI ↦ ?_
  have : LieRing.IsNilpotent I := hI
  exact LieIdeal.le_nilradical A (A ⊗[R] L) _ (LieIdeal.isNilpotent_baseChange A I)

/-- **Triviality of the radical descends along a faithfully flat extension of scalars.**
No finiteness or characteristic hypothesis is needed: a solvable ideal extends to a solvable
ideal, and faithful flatness reflects its vanishing. -/
theorem hasTrivialRadical_of_baseChange [Module.FaithfullyFlat R A]
    [HasTrivialRadical A (A ⊗[R] L)] : HasTrivialRadical R L := by
  refine hasTrivialRadical_of_no_solvable_ideals fun I hI ↦ ?_
  have : IsSolvable (I.baseChange A) := LieIdeal.isSolvable_baseChange A I
  have hbot := HasTrivialRadical.eq_bot_of_isSolvable (I.baseChange A)
  simpa only [← LieSubmodule.baseChange_bot A (R := R) (L := L) (M := L),
    LieSubmodule.baseChange_inj] using hbot

/-- **Membership in the nilradical may be checked after a faithfully flat extension of scalars**,
such as a field extension. A vector lies in the nilradical exactly when its canonical image in the
extension of scalars does. No finiteness hypothesis is needed. -/
@[simp]
theorem one_tmul_mem_nilradical_baseChange_iff [Module.FaithfullyFlat R A] (x : L) :
    (1 : A) ⊗ₜ[R] x ∈ nilradical A (A ⊗[R] L) ↔ x ∈ nilradical R L := by
  refine ⟨fun hx ↦ ?_, fun hx ↦
    baseChange_nilradical_le R L A (LieSubmodule.tmul_mem_baseChange_of_mem 1 hx)⟩
  -- `1 ⊗ x` lies in a nilpotent ideal `J`, which contains the extension of the ideal generated by
  -- `x`; nilpotency of that extension descends to the ideal itself.
  obtain ⟨J, hJ, hxJ⟩ := exists_isNilpotent_ideal_of_mem_nilradical hx
  have hle : (LieSubmodule.lieSpan R L {x}).baseChange A ≤ J := by
    rw [LieSubmodule.baseChange_lieSpan, Set.image_singleton, LieSubmodule.lieSpan_le]
    simpa using hxJ
  have : LieRing.IsNilpotent (LieSubmodule.lieSpan R L {x}) := by
    rw [← LieIdeal.isNilpotent_baseChange_iff A]
    exact LieIdeal.isNilpotent_of_le hle hJ
  exact LieIdeal.le_nilradical R L _ this (LieSubmodule.subset_lieSpan rfl)

end CommRing

section ScalarAction

open TauCeti.LieAlgebra

variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]

/-- The scalar-factor action of an automorphism preserves brackets. -/
private theorem tensorMap_lie (σ : A ≃ₐ[R] A) (x y : A ⊗[R] L) :
    TensorProduct.map σ.toLinearMap LinearMap.id ⁅x, y⁆ =
      ⁅TensorProduct.map σ.toLinearMap LinearMap.id x,
        TensorProduct.map σ.toLinearMap LinearMap.id y⁆ :=
  -- Mathlib's `ExtendScalars.map σ id` is `σ ⊗ id` by definition.
  (ExtendScalars.map σ.toAlgHom (LieHom.id : L →ₗ⁅R⁆ L)).map_lie x y

/-- The image `(σ ⊗ id) I` of an ideal `I` of `A ⊗[R] L`, described as the preimage of `I` under
`σ⁻¹ ⊗ id`. -/
private noncomputable def galoisTranslate (σ : A ≃ₐ[R] A) (I : LieIdeal A (A ⊗[R] L)) :
    LieIdeal A (A ⊗[R] L) :=
  { (I : Submodule A (A ⊗[R] L)).comap (TauCeti.ScalarAut.semilinearMap σ.symm) with
    lie_mem {x y} hy := by
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Submodule.mem_comap, TauCeti.ScalarAut.semilinearMap_apply,
        ← TauCeti.ScalarAut.tensorProductMap_eq_smul, tensorMap_lie] at hy ⊢
      exact I.lie_mem hy }

private theorem mem_galoisTranslate {σ : A ≃ₐ[R] A} {I : LieIdeal A (A ⊗[R] L)}
    {y : A ⊗[R] L} :
    y ∈ galoisTranslate σ I ↔ TensorProduct.map σ.symm.toLinearMap LinearMap.id y ∈ I := by
  rw [TauCeti.ScalarAut.tensorProductMap_eq_smul, ← TauCeti.ScalarAut.semilinearMap_apply]
  exact Submodule.mem_comap

/-- A translate of a nilpotent ideal under the scalar-factor action is nilpotent. -/
private theorem isNilpotent_galoisTranslate (σ : A ≃ₐ[R] A) (I : LieIdeal A (A ⊗[R] L))
    [LieRing.IsNilpotent I] : LieRing.IsNilpotent (galoisTranslate σ I) := by
  let g : galoisTranslate σ I →+ I :=
    { toFun y := ⟨TensorProduct.map σ.symm.toLinearMap LinearMap.id y,
        mem_galoisTranslate.mp y.property⟩
      map_zero' := by ext; simp
      map_add' y z := by ext; simp }
  let f : galoisTranslate σ I →ₗ⁅ℤ⁆ I :=
    { g.toIntLinearMap with
      map_lie' {y z} := Subtype.ext (tensorMap_lie σ.symm (y : A ⊗[R] L) z) }
  refine Function.Injective.lieAlgebra_isNilpotent (f := f) fun y z h ↦ Subtype.ext ?_
  have h' : TensorProduct.map σ.symm.toLinearMap LinearMap.id (y : A ⊗[R] L) =
      TensorProduct.map σ.symm.toLinearMap LinearMap.id z := congrArg Subtype.val h
  rwa [TauCeti.ScalarAut.tensorProductMap_eq_smul, TauCeti.ScalarAut.tensorProductMap_eq_smul,
    smul_left_cancel_iff] at h'

/-- **The nilradical of an extension of scalars is stable under the scalar-factor action.** For
every algebra automorphism `σ` of `A`, the map `σ ⊗ id` carries the nilradical of `A ⊗[R] L` into
itself. No finiteness hypothesis is needed. -/
theorem _root_.AlgEquiv.tensorProduct_map_mem_lieNilradical (σ : A ≃ₐ[R] A) {x : A ⊗[R] L}
    (hx : x ∈ nilradical A (A ⊗[R] L)) :
    TensorProduct.map σ.toLinearMap LinearMap.id x ∈ nilradical A (A ⊗[R] L) := by
  obtain ⟨I, hI, hxI⟩ := exists_isNilpotent_ideal_of_mem_nilradical hx
  refine LieIdeal.le_nilradical A _ (galoisTranslate σ I) (isNilpotent_galoisTranslate σ I) ?_
  rwa [mem_galoisTranslate, TauCeti.ScalarAut.tensorProductMap_eq_smul,
    TauCeti.ScalarAut.tensorProductMap_eq_smul, ← AlgEquiv.aut_inv, inv_smul_smul]

end ScalarAction

section PrincipalIdealDomain

variable (K L A : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Algebra K A]

/-- **Triviality of the radical is insensitive to extension of scalars to a principal ideal
domain**, such as a field extension.  In characteristic zero a finite-dimensional Lie algebra has
trivial radical exactly when its extension of scalars to such a domain does.

The `←` direction is the substantive one: extending scalars cannot *create* a solvable ideal.
It does not follow from `LieIdeal.isSolvable_baseChange_iff`, which only speaks of ideals extended
from `L`. The `→` direction is the general faithfully flat descent theorem
`LieAlgebra.hasTrivialRadical_of_baseChange`. Characteristic zero is a genuine hypothesis for
ascent, not a convenience. -/
@[simp]
theorem hasTrivialRadical_baseChange_iff :
    HasTrivialRadical A (A ⊗[K] L) ↔ HasTrivialRadical K L := by
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  refine ⟨fun _ ↦ hasTrivialRadical_of_baseChange K L A, fun _ ↦ ?_⟩
  rw [hasTrivialRadical_iff_isKilling, TauCeti.isKilling_baseChange_iff K A L]
  infer_instance

/-- **In characteristic zero the solvable radical commutes with extension of scalars to a
principal ideal domain**, such as a field extension.  For a finite-dimensional Lie algebra `L`
over a field `K` of characteristic zero and a `K`-algebra `A` that is a principal ideal domain,
the radical of `A ⊗[K] L` is the extension of scalars of the radical of `L`.

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

/-- **Membership in the radical may be checked after extending scalars to a principal ideal
domain**, such as a field extension.  In characteristic zero a vector of a finite-dimensional Lie
algebra lies in the solvable radical exactly when its canonical image in such an extension of
scalars does. -/
theorem one_tmul_mem_radical_baseChange_iff (x : L) :
    (1 : A) ⊗ₜ[K] x ∈ radical A (A ⊗[K] L) ↔ x ∈ radical K L := by
  rw [radical_baseChange, LieSubmodule.one_tmul_mem_baseChange_iff]

end PrincipalIdealDomain

end LieAlgebra
