/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Splitting of a prime in the inertia field

Let `L/K` be a finite Galois extension, `B` the integral closure of a Dedekind domain `A` in `L`,
and `P` a maximal ideal of `B` over `p` in `A`, with ramification index `e` and inertia degree `f`.
Hilbert theory describes the splitting of `p` in the tower `K ⊆ D ⊆ E ⊆ L` cut out by the
decomposition and inertia groups of `P`, where `𝓟D` and `𝓟E` are the primes below `P`:

```
degree            ramif. index   inertia deg.
        L      P
 e fᵢ   |      |      e               fᵢ
        E      𝓟E
  fₛ    |      |      1               fₛ
        D      𝓟D
  g     |      |      1               1
        K      p
```

Here `f = fₛ fᵢ` splits the residue degree of `P` over `p` into its separable and inseparable
parts; when the residue extension is separable, `fᵢ = 1` and `fₛ = f`.

Mathlib develops the decomposition and inertia fields and proves that `P` is the only prime
of `B` over `𝓟D`. `TauCeti/NumberTheory/RamificationInertia/HilbertTheory/ResidueDegree.lean`
supplies the field degrees without assuming separability of the residue extension, and proves
that the pair `(e, f)` is unchanged when the base moves from `p` up to `𝓟D`, while `𝓟D` has
ramification index and residue degree `1` over `p`. This file adds the statements over `E`,
which split that pair between the two upper rows: `P` is again the only prime of `B` over `𝓟E`,
all the ramification of `P` over `p` is already ramification over `𝓟E`, its residue degree is the
inseparable part `fᵢ`, and consequently `𝓟E` has ramification index `1` over `p` with separable
residue extension of degree `fₛ`. No separability of the residue extension at `P` is assumed;
the separable case, where the upper residue degree is `1` and the lower one is `f`, is recorded
as a corollary. The prime `𝓟E` is stated as `P.under 𝓞E`, for `𝓞E` a Dedekind domain between
`A` and `B` with fraction field `E`.

The statements over `E` also apply when `B` is any domain finite and torsion-free over `A`
with fraction field `L`, equipped with the compatible Galois action. Only `A` and `𝓞E` need
to be Dedekind domains; integral closedness of `B` is not required.

## Main results

* `TauCeti.IsInertiaField.primesOver_eq_singleton` — `P` is the only prime of `B` over the prime
  of the inertia field below it.
* `TauCeti.IsInertiaField.ramificationIdx_eq` and
  `TauCeti.IsInertiaField.inertiaDeg_eq_finInsepDegree` —
  over the inertia field the ramification index is unchanged and the inertia degree is the
  inseparable residue degree `fᵢ`.
* `TauCeti.IsInertiaField.ramificationIdx_under_eq_one`, `isSeparable_quotient_under` and
  `TauCeti.IsInertiaField.inertiaDeg_under_eq_finSepDegree` — under the inertia field the
  ramification index is `1`, the residue extension is separable, and its degree is `fₛ`.
* `TauCeti.IsInertiaField.inertiaDeg_eq_one` and
  `TauCeti.IsInertiaField.inertiaDeg_under_eq` — the separable case: the inertia degree
  over the inertia field is `1` and under it is the full residue degree of `P` over `p`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Ch. I (9.6).
* The instance construction and prime-transitivity argument adapt Xavier Roblot's
  decomposition-field section of `Mathlib/NumberTheory/RamificationInertia/HilbertTheory.lean`.
-/

public section

open Ideal MulAction Pointwise

namespace TauCeti

namespace IsInertiaField

attribute [local instance] Ideal.Quotient.field

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] (P : Ideal B)
  [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

variable (E 𝓞E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E] [CommRing 𝓞E]
  [Algebra 𝓞E E] [IsFractionRing 𝓞E E] [Algebra 𝓞E B] [Algebra 𝓞E L] [IsScalarTower 𝓞E E L]
  [IsScalarTower 𝓞E B L]

include K L E in
/-- Let `E` be the inertia field of `P` in `L/K`. Then `P` is the only prime of `B` above the
prime `P.under 𝓞E` of `E` below it. -/
theorem primesOver_eq_singleton [hP : P.IsPrime] [Finite (inertia Gal(L/K) P)]
    [IsIntegrallyClosed 𝓞E] [Algebra.IsIntegral 𝓞E B] :
    primesOver (P.under 𝓞E) B = {P} := by
  have := IsGaloisGroup.of_isFractionRing (inertia Gal(L/K) P) 𝓞E B E L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, inferInstance⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (P.under 𝓞E) P Q (inertia Gal(L/K) P)
  exact inertia_le_stabilizer P σ.prop

variable [IsGalois K L] [IsDedekindDomain A] [IsDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞E] [Module.Finite A 𝓞E] [IsScalarTower A 𝓞E B]
  [IsDedekindDomain 𝓞E]

omit [IsGalois K L] in
include K L E P in
private lemma instances [IsGaloisGroup Gal(L/K) K L] :
    Module.Finite 𝓞E B ∧ Module.IsTorsionFree 𝓞E B ∧ Module.IsTorsionFree A 𝓞E ∧
      IsGaloisGroup Gal(L/K) A B ∧ IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := by
  have inst₁ : Module.Finite 𝓞E B := Module.Finite.right A 𝓞E B
  have inst₂ : Module.IsTorsionFree 𝓞E B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : Module.IsTorsionFree A 𝓞E := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have inst₄ : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have inst₅ : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  exact ⟨inst₁, inst₂, inst₃, inst₄, inst₅⟩

variable [FiniteDimensional K L] [P.IsMaximal]

include K L E P in
/-- Over the inertia field, the ramification index of `P` is unchanged, and the residue extension
of `P.under 𝓞E` over `P.under A` is separable. -/
private lemma ramificationIdx_eq_and_isSeparable :
    P.ramificationIdx 𝓞E = P.ramificationIdx A ∧
      Algebra.IsSeparable (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) := by
  -- The inertia group of `P` in `L/K`, acting on `B` over `𝓞E`, has order
  -- `e(P ∣ P.under 𝓞E) · fᵢ(P ∣ P.under 𝓞E)` and also `e(P ∣ P.under A) · fᵢ(P ∣ P.under A)`.
  -- The tower law for inseparable degrees and `e(P ∣ P.under 𝓞E) ≤ e(P ∣ P.under A)` then force
  -- `fᵢ(P.under 𝓞E ∣ P.under A) = 1` and the equality of the ramification indices.
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  let _ : IsScalarTower (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]
      rw [IsScalarTower.algebraMap_apply A 𝓞E B])
  have : Algebra.IsAlgebraic (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) := .of_finite _ _
  -- the inertia group acts trivially on `B ⧸ P`, so its own inertia group at `P` is everything
  have htop : inertia (inertia Gal(L/K) P) P = ⊤ :=
    (AddSubgroup.subgroupOf_inertia _ _).symm.trans (Subgroup.subgroupOf_self _)
  have h₁ := card_inertia_eq_ramificationIdx_mul_finInsepDegree
    (R := 𝓞E) (G := inertia Gal(L/K) P) P
  have h₂ := card_inertia_eq_ramificationIdx_mul_finInsepDegree (R := A) (G := Gal(L/K)) P
  rw [htop, Subgroup.card_top] at h₁
  have htower := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic
    (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) (B ⧸ P)
  have key : P.ramificationIdx 𝓞E = P.ramificationIdx A *
      Field.finInsepDegree (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) := by
    apply Nat.eq_of_mul_eq_mul_right
      (NeZero.pos (Field.finInsepDegree (𝓞E ⧸ P.under 𝓞E) (B ⧸ P)))
    rw [← h₁, h₂, mul_assoc, htower]
  have hle : P.ramificationIdx 𝓞E ≤ P.ramificationIdx A :=
    (P.under 𝓞E).ramificationIdx_above_le P
  have hpos : 0 < P.ramificationIdx A := ramificationIdx_pos A P
  have hins : Field.finInsepDegree (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) = 1 := by
    refine le_antisymm (Nat.le_of_mul_le_mul_left ?_ hpos)
      (NeZero.pos (Field.finInsepDegree (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E)))
    rw [mul_one, ← key]
    exact hle
  exact ⟨by rw [key, hins, mul_one], (isSeparable_iff_finInsepDegree_eq_one _ _).mpr hins⟩

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the ramification index of `P` over
`P.under 𝓞E` is its ramification index over `P.under A`. No separability of the residue
extension is assumed. -/
theorem ramificationIdx_eq : P.ramificationIdx 𝓞E = P.ramificationIdx A :=
  (ramificationIdx_eq_and_isSeparable A K L P E 𝓞E).1

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the residue extension of `P.under 𝓞E` over
`P.under A` is separable: the inertia field carries exactly the separable part of the residue
extension of `P`. -/
theorem isSeparable_quotient_under :
    Algebra.IsSeparable (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) :=
  (ramificationIdx_eq_and_isSeparable A K L P E 𝓞E).2

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the inertia degree of `P` over `P.under 𝓞E`
is the inseparable residue degree of `P` over `P.under A`. -/
theorem inertiaDeg_eq_finInsepDegree :
    P.inertiaDeg 𝓞E = Field.finInsepDegree (A ⧸ P.under A) (B ⧸ P) := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  -- Use the pointwise ideal action induced by the inertia action on `B`, as in the cardinality
  -- formula, rather than the generic restriction of the action on `Ideal B`.
  let _ : MulAction (inertia Gal(L/K) P) (Ideal B) :=
    Ideal.pointwiseDistribMulAction.toMulAction
  -- Every inertia element fixes `P`, so its decomposition group over `𝓞E` is the whole group.
  have htop : stabilizer (inertia Gal(L/K) P) P = ⊤ := by
    apply top_unique
    intro σ _
    exact inertia_le_stabilizer P σ.prop
  have h := card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    (R := 𝓞E) (G := inertia Gal(L/K) P) P
  rw [htop, Subgroup.card_top, ramificationIdx_eq A K L P E 𝓞E,
    card_inertia_eq_ramificationIdx_mul_finInsepDegree (R := A) (G := Gal(L/K)) P] at h
  exact Nat.eq_of_mul_eq_mul_left (ramificationIdx_pos A P) h.symm

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then `P.under 𝓞E` has ramification index `1`
over the prime of `A` below it. No separability of the residue extension is assumed. -/
theorem ramificationIdx_under_eq_one :
    (P.under 𝓞E).ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have h := ramificationIdx_tower (R := A) (P.under 𝓞E) P
  rw [ramificationIdx_eq A K L P E 𝓞E] at h
  exact (right_eq_mul₀ (ramificationIdx_pos A P).ne').mp h

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the inertia degree of `P.under 𝓞E` over
`P.under A` is the separable residue degree of `P` over `P.under A`. -/
theorem inertiaDeg_under_eq_finSepDegree :
    (P.under 𝓞E).inertiaDeg A = Field.finSepDegree (A ⧸ P.under A) (B ⧸ P) := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have h := inertiaDeg_tower (R := A) (P.under 𝓞E) P
  rw [inertiaDeg_eq_finInsepDegree A K L P E 𝓞E, inertiaDeg_eq_of_isMaximal (P.under A) P,
    ← Field.finSepDegree_mul_finInsepDegree] at h
  exact (Nat.eq_of_mul_eq_mul_right
    (NeZero.pos (Field.finInsepDegree (A ⧸ P.under A) (B ⧸ P))) h).symm

section Separable

variable [Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P)]

include A K L E P in
/-- When the residue extension of `P` over `P.under A` is separable, the inertia degree of `P`
over `P.under 𝓞E` is `1`. -/
theorem inertiaDeg_eq_one : P.inertiaDeg 𝓞E = 1 := by
  rw [inertiaDeg_eq_finInsepDegree A K L P E 𝓞E]
  exact (isSeparable_iff_finInsepDegree_eq_one _ _).mp inferInstance

include K L E P in
/-- When the residue extension of `P` over `P.under A` is separable, the inertia degree of
`P.under 𝓞E` over `P.under A` is the full inertia degree of `P` over `P.under A`. -/
theorem inertiaDeg_under_eq : (P.under 𝓞E).inertiaDeg A = P.inertiaDeg A := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  rw [inertiaDeg_under_eq_finSepDegree A K L P E 𝓞E,
    Field.finSepDegree_eq_finrank_of_isSeparable, inertiaDeg_eq_of_isMaximal (P.under A) P]

end Separable

end IsInertiaField

end TauCeti
