/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

/-!
# Splitting of a prime in the inertia field

Let `L/K` be a finite Galois extension, `B` the integral closure of a Dedekind domain `A` in `L`,
and `P` a prime of `B` over a prime `p` of `A` with ramification index `e` and inertia degree `f`.
Hilbert theory describes the splitting of `p` in the tower `K ⊆ D ⊆ E ⊆ L` cut out by the
decomposition and inertia groups of `P`, where `𝓟D` and `𝓟E` are the primes below `P`:

```
degree            ramif. index   inertia deg.
        L      P
  e     |      |      e               1
        E      𝓟E
  f     |      |      1               f
        D      𝓟D
  g     |      |      1               1
        K      p
```

Mathlib proves the field degrees of all three steps, and the ideal-theoretic content over the
decomposition field `D`: `P` is the only prime of `B` over `𝓟D`, the pair `(e, f)` is unchanged
when the base moves from `p` up to `𝓟D`, and `𝓟D` is unramified over `p` with trivial residue
extension. This file adds the statements over the inertia field `E`, which split that pair
between the two upper rows: `P` is again the only prime of `B` over `𝓟E`, all the ramification
of `P` over `p` is already ramification over `𝓟E` and its residue extension over `𝓟E` is
trivial, and consequently `𝓟E` is unramified over `p` with residue degree the full `f`.
The prime `𝓟E` is stated as `P.under 𝓞E`, for `𝓞E` a Dedekind domain between `A` and `B` with
fraction field `E`, and the residue field of `p` is assumed perfect, as it is when it is finite.


## Main results

* `TauCeti.IsInertiaField.primesOver_eq_singleton` — `P` is the only prime of `B` over the prime
  of the inertia field below it.
* `TauCeti.IsInertiaField.ramificationIdxIn_eq` and `TauCeti.IsInertiaField.inertiaDegIn_eq_one` —
  over the inertia field the ramification index is unchanged and the inertia degree is `1`.
* `TauCeti.IsInertiaField.ramificationIdx_eq_one` and
  `TauCeti.IsInertiaField.inertiaDeg_eq_inertiaDegIn` — under the inertia field the ramification
  index is `1` and the inertia degree is the full inertia degree of `p`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Ch. I (9.6).
* X. Roblot, the decomposition-field section of
  `Mathlib/NumberTheory/RamificationInertia/HilbertTheory.lean`.
-/

public section

open Ideal MulAction Pointwise

namespace TauCeti

namespace IsInertiaField

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

variable [FiniteDimensional K L] [P.IsPrime] [PerfectField (P.under A).ResidueField]

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the ramification index of `P.under 𝓞E` in
`L` is the ramification index of `p` in `L`: all the ramification of `P` over `p` already happens
over `P.under 𝓞E`. -/
theorem ramificationIdxIn_eq :
    ramificationIdxIn (P.under 𝓞E) B = p.ramificationIdxIn B := by
  obtain rfl := over_def P p
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) (P.under 𝓞E)
  have : PerfectField (P.under 𝓞E).ResidueField :=
    Algebra.IsAlgebraic.perfectField (P.under A).ResidueField
  -- the inertia group acts trivially on `B ⧸ P`, so its own inertia group at `P` is everything
  have htop : inertia (inertia Gal(L/K) P) P = ⊤ :=
    (AddSubgroup.subgroupOf_inertia _ _).symm.trans (Subgroup.subgroupOf_self _)
  calc ramificationIdxIn (P.under 𝓞E) B
      = Nat.card (inertia (inertia Gal(L/K) P) P) :=
        (card_inertia_eq_ramificationIdxIn (P.under 𝓞E) P).symm
    _ = Nat.card (inertia Gal(L/K) P) := by rw [htop, Subgroup.card_top]
    _ = (P.under A).ramificationIdxIn B := card_inertia_eq_ramificationIdxIn (P.under A) P

include A K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the inertia degree of `P.under 𝓞E` in `L`
is `1`: the residue extension of `P` over `P.under 𝓞E` is trivial. -/
theorem inertiaDegIn_eq_one :
    inertiaDegIn (P.under 𝓞E) B = 1 := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have H := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (P.under 𝓞E) B
    (inertia Gal(L/K) P)
  rw [primesOver_eq_singleton K L P E 𝓞E, Set.ncard_singleton, one_mul,
    ramificationIdxIn_eq A K L P E 𝓞E (p := P.under A),
    card_inertia_eq_ramificationIdxIn (P.under A) P] at H
  exact (mul_right_eq_self₀.mp H).resolve_right (ramificationIdxIn_ne_zero Gal(L/K))

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then `P.under 𝓞E` is unramified over the prime
of `A` below it. -/
theorem ramificationIdx_eq_one :
    (P.under 𝓞E).ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have := ramificationIdx_tower (R := A) (P.under 𝓞E) P
  rwa [← ramificationIdxIn_eq_ramificationIdx (P.under 𝓞E) P (inertia Gal(L/K) P),
    ramificationIdxIn_eq A K L P E 𝓞E (p := P.under A),
    ramificationIdxIn_eq_ramificationIdx (P.under A) P Gal(L/K),
    right_eq_mul₀ <| (ramificationIdx_pos P A).ne'] at this

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K`. Then the inertia degree of `P.under 𝓞E` over `p`
is the inertia degree of `p` in `L`: the whole residue extension of `P` over `p` is already the
residue extension of `P.under 𝓞E`. -/
theorem inertiaDeg_eq_inertiaDegIn :
    (P.under 𝓞E).inertiaDeg A = p.inertiaDegIn B := by
  obtain rfl := over_def P p
  obtain ⟨_, _, _, _, _⟩ := instances A K L P E 𝓞E
  have := inertiaDeg_tower (R := A) (P.under 𝓞E) P
  rw [← inertiaDegIn_eq_inertiaDeg (P.under A) P Gal(L/K),
    ← inertiaDegIn_eq_inertiaDeg (P.under 𝓞E) P (inertia Gal(L/K) P),
    inertiaDegIn_eq_one A K L P E 𝓞E, mul_one] at this
  exact this.symm

end IsInertiaField

end TauCeti
