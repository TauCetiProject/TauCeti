/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Splitting of a prime in the inertia field

Let `L/K` be a finite Galois extension, `B` the integral closure of a Dedekind domain `A` in `L`,
and `P` a prime of `B` over a prime `p` of `A` with ramification index `e` and inertia degree `f`.
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

Mathlib proves the field degrees of all three steps, and the ideal-theoretic content over the
decomposition field `D`: `P` is the only prime of `B` over `𝓟D`, the pair `(e, f)` is unchanged
when the base moves from `p` up to `𝓟D`, and `𝓟D` is unramified over `p` with trivial residue
extension. This file adds the statements over the inertia field `E`, which split that pair
between the two upper rows: `P` is again the only prime of `B` over `𝓟E`, all the ramification
of `P` over `p` is already ramification over `𝓟E` and its residue extension over `𝓟E` is the
purely inseparable part `fᵢ`, and consequently `𝓟E` is unramified over `p` with separable
residue extension of degree `fₛ`. No separability of the residue extension at `P` is assumed;
the separable case, where the upper residue degree is `1` and the lower one is `f`, is recorded
as a corollary. The prime `𝓟E` is stated as `P.under 𝓞E`, for `𝓞E` a Dedekind domain between
`A` and `B` with fraction field `E`.

## Main results

* `TauCeti.IsInertiaField.primesOver_eq_singleton` — `P` is the only prime of `B` over the prime
  of the inertia field below it.
* `TauCeti.IsInertiaField.ramificationIdxIn_eq`, `ramificationIdx_eq` and
  `TauCeti.IsInertiaField.inertiaDegIn_eq_finInsepDegree`, `inertiaDeg_eq_finInsepDegree` —
  over the inertia field the ramification index is unchanged and the inertia degree is the
  inseparable residue degree `fᵢ`.
* `TauCeti.IsInertiaField.ramificationIdx_eq_one`, `isSeparable_quotient_under` and
  `TauCeti.IsInertiaField.inertiaDeg_eq_finSepDegree` — under the inertia field the ramification
  index is `1`, the residue extension is separable, and its degree is `fₛ`.
* `TauCeti.IsInertiaField.inertiaDegIn_eq_one` and
  `TauCeti.IsInertiaField.inertiaDeg_eq_inertiaDegIn` — the separable case: the inertia degree
  over the inertia field is `1` and under it is the full inertia degree of `p`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Ch. I (9.6).
* X. Roblot, the decomposition-field section of
  `Mathlib/NumberTheory/RamificationInertia/HilbertTheory.lean`.
-/

public section

open Ideal MulAction Pointwise

namespace TauCeti

namespace IsInertiaField

attribute [local instance] Ideal.Quotient.field

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]
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

variable [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞E] [Module.Finite A 𝓞E] [IsScalarTower A 𝓞E B]
  [IsDedekindDomain 𝓞E]

omit [P.LiesOver p] in
include K L E P in
private lemma instances :
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

omit [P.LiesOver p] in
include K L E P in
/-- Over the inertia field, the ramification index of `P` is unchanged, and the residue extension
of `P.under 𝓞E` over `P.under A` is separable. -/
private lemma ramificationIdxIn_eq_and_isSeparable :
    ramificationIdxIn (P.under 𝓞E) B = (P.under A).ramificationIdxIn B ∧
      Algebra.IsSeparable (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) := by
  -- The inertia group of `P` in `L/K`, acting on `B` over `𝓞E`, has order
  -- `e(P ∣ P.under 𝓞E) · fᵢ(P ∣ P.under 𝓞E)` and also `e(P ∣ P.under A) · fᵢ(P ∣ P.under A)`.
  -- The tower law for inseparable degrees and `e(P ∣ P.under 𝓞E) ≤ e(P ∣ P.under A)` then force
  -- `fᵢ(P.under 𝓞E ∣ P.under A) = 1` and the equality of the ramification indices.
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  let _ : (P.under A).IsMaximal := Ideal.IsMaximal.under A P
  let _ : (P.under 𝓞E).IsMaximal := Ideal.IsMaximal.under 𝓞E P
  let _ : IsScalarTower (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]
      rw [IsScalarTower.algebraMap_apply A 𝓞E B])
  have : Algebra.IsAlgebraic (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) := .of_finite _ _
  -- the inertia group acts trivially on `B ⧸ P`, so its own inertia group at `P` is everything
  have htop : inertia (inertia Gal(L/K) P) P = ⊤ :=
    (AddSubgroup.subgroupOf_inertia _ _).symm.trans (Subgroup.subgroupOf_self _)
  have h₁ := card_inertia_eq_ramificationIdxIn_mul_finInsepDegree
    (G := inertia Gal(L/K) P) (P.under 𝓞E) P
  have h₂ := card_inertia_eq_ramificationIdxIn_mul_finInsepDegree (G := Gal(L/K)) (P.under A) P
  rw [htop, Subgroup.card_top] at h₁
  have htower := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic
    (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) (B ⧸ P)
  have key : ramificationIdxIn (P.under 𝓞E) B = (P.under A).ramificationIdxIn B *
      Field.finInsepDegree (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) := by
    apply Nat.eq_of_mul_eq_mul_right
      (NeZero.pos (Field.finInsepDegree (𝓞E ⧸ P.under 𝓞E) (B ⧸ P)))
    rw [← h₁, h₂, mul_assoc, htower]
  have hle : ramificationIdxIn (P.under 𝓞E) B ≤ (P.under A).ramificationIdxIn B := by
    rw [ramificationIdxIn_eq_ramificationIdx (P.under 𝓞E) P (inertia Gal(L/K) P),
      ramificationIdxIn_eq_ramificationIdx (P.under A) P Gal(L/K)]
    exact (P.under 𝓞E).ramificationIdx_above_le P
  have hpos : 0 < (P.under A).ramificationIdxIn B :=
    Nat.pos_of_ne_zero (ramificationIdxIn_ne_zero Gal(L/K))
  have hins : Field.finInsepDegree (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) = 1 := by
    refine le_antisymm (Nat.le_of_mul_le_mul_left ?_ hpos)
      (NeZero.pos (Field.finInsepDegree (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E)))
    rw [mul_one, ← key]
    exact hle
  exact ⟨by rw [key, hins, mul_one], (isSeparable_iff_finInsepDegree_eq_one _ _).mpr hins⟩

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the ramification index of `P.under 𝓞E` in
`L` is the ramification index of `p` in `L`: all the ramification of `P` over `p` already happens
over `P.under 𝓞E`. No separability of the residue extension is assumed. -/
theorem ramificationIdxIn_eq :
    ramificationIdxIn (P.under 𝓞E) B = p.ramificationIdxIn B := by
  obtain rfl := over_def P p
  exact (ramificationIdxIn_eq_and_isSeparable A K L P E 𝓞E).1

omit [P.LiesOver p] in
include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the residue extension of `P.under 𝓞E` over
`P.under A` is separable: the inertia field carries exactly the separable part of the residue
extension of `P`. -/
theorem isSeparable_quotient_under :
    Algebra.IsSeparable (A ⧸ P.under A) (𝓞E ⧸ P.under 𝓞E) :=
  (ramificationIdxIn_eq_and_isSeparable A K L P E 𝓞E).2

include A K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the inertia degree of `P.under 𝓞E` in `L`
is the inseparable residue degree of `P` over `p`: the residue extension of `P` over `P.under 𝓞E`
is the purely inseparable part of the residue extension of `P` over `p`. -/
theorem inertiaDegIn_eq_finInsepDegree :
    inertiaDegIn (P.under 𝓞E) B = Field.finInsepDegree (A ⧸ P.under A) (B ⧸ P) := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have H := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (P.under 𝓞E) B
    (inertia Gal(L/K) P)
  rw [primesOver_eq_singleton K L P E 𝓞E, Set.ncard_singleton, one_mul,
    ramificationIdxIn_eq A K L P E 𝓞E (p := P.under A),
    card_inertia_eq_ramificationIdxIn_mul_finInsepDegree (G := Gal(L/K)) (P.under A) P] at H
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (ramificationIdxIn_ne_zero Gal(L/K))) H

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then `P.under 𝓞E` is unramified over the prime
of `A` below it. No separability of the residue extension is assumed. -/
theorem ramificationIdx_eq_one :
    (P.under 𝓞E).ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have := ramificationIdx_tower (R := A) (P.under 𝓞E) P
  rwa [← ramificationIdxIn_eq_ramificationIdx (P.under 𝓞E) P (inertia Gal(L/K) P),
    ramificationIdxIn_eq A K L P E 𝓞E (p := P.under A),
    ramificationIdxIn_eq_ramificationIdx (P.under A) P Gal(L/K),
    right_eq_mul₀ <| (ramificationIdx_pos A P).ne'] at this

omit [P.LiesOver p] in
include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the ramification index of `P` over
`P.under 𝓞E` is its ramification index over `P.under A`. -/
theorem ramificationIdx_eq : P.ramificationIdx 𝓞E = P.ramificationIdx A := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  rw [← ramificationIdxIn_eq_ramificationIdx (P.under 𝓞E) P (inertia Gal(L/K) P),
    ramificationIdxIn_eq A K L P E 𝓞E (p := P.under A),
    ramificationIdxIn_eq_ramificationIdx (P.under A) P Gal(L/K)]

omit [P.LiesOver p] in
include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the inertia degree of `P` over `P.under 𝓞E`
is the inseparable residue degree of `P` over `P.under A`. -/
theorem inertiaDeg_eq_finInsepDegree :
    P.inertiaDeg 𝓞E = Field.finInsepDegree (A ⧸ P.under A) (B ⧸ P) := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  rw [← inertiaDegIn_eq_inertiaDeg (P.under 𝓞E) P (inertia Gal(L/K) P),
    inertiaDegIn_eq_finInsepDegree A K L P E 𝓞E]

omit [P.LiesOver p] in
include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the inertia degree of `P.under 𝓞E` over
`P.under A` is the separable residue degree of `P` over `P.under A`. -/
theorem inertiaDeg_eq_finSepDegree :
    (P.under 𝓞E).inertiaDeg A = Field.finSepDegree (A ⧸ P.under A) (B ⧸ P) := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have := inertiaDeg_tower (R := A) (P.under 𝓞E) P
  rw [← inertiaDegIn_eq_inertiaDeg (P.under 𝓞E) P (inertia Gal(L/K) P),
    inertiaDegIn_eq_finInsepDegree A K L P E 𝓞E, inertiaDeg_eq_of_isMaximal (P.under A) P,
    ← Field.finSepDegree_mul_finInsepDegree] at this
  exact (Nat.eq_of_mul_eq_mul_right
    (NeZero.pos (Field.finInsepDegree (A ⧸ P.under A) (B ⧸ P))) this).symm

section Separable

variable [Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P)]

include A K L E P in
/-- When the residue extension of `P` over `p` is separable, the inertia degree of `P.under 𝓞E` in
`L` is `1`: the residue extension of `P` over `P.under 𝓞E` is trivial. -/
theorem inertiaDegIn_eq_one :
    inertiaDegIn (P.under 𝓞E) B = 1 := by
  rw [inertiaDegIn_eq_finInsepDegree A K L P E 𝓞E]
  exact (isSeparable_iff_finInsepDegree_eq_one _ _).mp inferInstance

include K L E P in
/-- When the residue extension of `P` over `p` is separable, the inertia degree of `P.under 𝓞E` over
`p` is the inertia degree of `p` in `L`: the whole residue extension of `P` over `p` is already the
residue extension of `P.under 𝓞E`. -/
theorem inertiaDeg_eq_inertiaDegIn :
    (P.under 𝓞E).inertiaDeg A = p.inertiaDegIn B := by
  obtain rfl := over_def P p
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  rw [inertiaDeg_eq_finSepDegree A K L P E 𝓞E, Field.finSepDegree_eq_finrank_of_isSeparable,
    ← inertiaDeg_eq_of_isMaximal (P.under A) P, inertiaDegIn_eq_inertiaDeg (P.under A) P Gal(L/K)]

end Separable

end IsInertiaField

end TauCeti
