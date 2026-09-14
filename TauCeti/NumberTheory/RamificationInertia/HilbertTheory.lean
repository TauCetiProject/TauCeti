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
decomposition and inertia groups of `P`:

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


## Main results

* `TauCeti.RamificationInertia.IsInertiaField.primesOver_eq_singleton` — `P` is the only prime of
  `B` over the prime of the inertia field below it.
* `TauCeti.RamificationInertia.IsInertiaField.ramificationIdxIn_eq` and
  `TauCeti.RamificationInertia.IsInertiaField.inertiaDegIn_eq_one` — over the inertia field the
  ramification index is unchanged and the inertia degree is `1`.
* `TauCeti.RamificationInertia.IsInertiaField.ramificationIdx_eq_one` and
  `TauCeti.RamificationInertia.IsInertiaField.inertiaDeg_eq_inertiaDegIn` — under the inertia
  field the ramification index is `1` and the inertia degree is the full inertia degree of `p`.

## Implementation

The inertia group acts trivially on `B ⧸ P`, so the group it cuts out is its own inertia group;
that is the one observation these proofs add to Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn` and its fundamental identity. The bottom two rows then
transfer to the top row by multiplicativity of `e` and of `f` in towers. `A` is asked to have
finite quotients rather than `p.ResidueField` merely to be perfect, matching the hypotheses under
which Mathlib states the decomposition-field row; the primes `P` and `𝓟E` are only asked to be
prime, where Mathlib's row asks for maximality.

The statements and their proofs follow the decomposition-field section of
`Mathlib/NumberTheory/RamificationInertia/HilbertTheory.lean`, with the inertia subgroup of `P` in
place of its stabilizer.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Ch. I (9.6).
-/

public section

open Ideal MulAction Pointwise

namespace TauCeti.RamificationInertia

namespace IsInertiaField

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]
  [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

variable (E 𝓞E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E] [CommRing 𝓞E]
  [Algebra 𝓞E E] [IsFractionRing 𝓞E E] [Algebra 𝓞E B] [Algebra 𝓞E L] [IsScalarTower 𝓞E E L]
  [IsScalarTower 𝓞E B L] (𝓟E : Ideal 𝓞E) [hE : P.LiesOver 𝓟E]

include K L E in
/-- Let `E` be the inertia field of `P` in `L/K` and let `𝓟E` be the prime of `E` below `P`.
Then `P` is the only prime of `B` above `𝓟E`. -/
theorem primesOver_eq_singleton [hP : P.IsPrime] [Finite (inertia Gal(L/K) P)]
    [IsIntegrallyClosed 𝓞E] [Algebra.IsIntegral 𝓞E B] :
    primesOver 𝓟E B = {P} := by
  have := IsGaloisGroup.of_isFractionRing (inertia Gal(L/K) P) 𝓞E B E L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hE⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟E P Q (inertia Gal(L/K) P)
  exact inertia_le_stabilizer P σ.prop

variable [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞E] [Module.Finite A 𝓞E] [IsScalarTower A 𝓞E B]
  [IsDedekindDomain 𝓞E] [𝓟E.LiesOver p]

omit [P.LiesOver p] hE in
include K L E P in
private lemma instances (hp : p ≠ ⊥) :
    Module.Finite 𝓞E B ∧ Module.IsTorsionFree 𝓞E B ∧ Module.IsTorsionFree A 𝓞E ∧
      IsGaloisGroup Gal(L/K) A B ∧ IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B ∧ 𝓟E ≠ ⊥ := by
  have inst₁ : Module.Finite 𝓞E B := Module.Finite.right A 𝓞E B
  have inst₂ : Module.IsTorsionFree 𝓞E B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : Module.IsTorsionFree A 𝓞E := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have inst₄ : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have inst₅ : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  exact ⟨inst₁, inst₂, inst₃, inst₄, inst₅, Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟E⟩

variable [FiniteDimensional K L] [Ring.HasFiniteQuotients A] [𝓟E.IsPrime] [P.IsPrime]

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K` and let `𝓟E` be the prime of `E` below `P`.
Then the ramification index of `𝓟E` in `L` is the ramification index of `p` in `L`: all the
ramification of `P` over `p` already happens over `𝓟E`. -/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟E B = p.ramificationIdxIn B := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P E 𝓞E 𝓟E hp
  have : p.IsPrime := over_def P p ▸ Ideal.IsPrime.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : Ring.HasFiniteQuotients 𝓞E := .of_module_finite A 𝓞E
  have : Finite (𝓞E ⧸ 𝓟E) := Ring.HasFiniteQuotients.finiteQuotient h𝓟
  -- the inertia group acts trivially on `B ⧸ P`, so its own inertia group at `P` is everything
  have htop : inertia (inertia Gal(L/K) P) P = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun σ ↦ Ideal.coe_mem_inertia.1 σ.2
  calc ramificationIdxIn 𝓟E B
      = Nat.card (inertia (inertia Gal(L/K) P) P) :=
        (card_inertia_eq_ramificationIdxIn 𝓟E P).symm
    _ = Nat.card (inertia Gal(L/K) P) := by rw [htop, Subgroup.card_top]
    _ = p.ramificationIdxIn B := card_inertia_eq_ramificationIdxIn p P

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K` and let `𝓟E` be the prime of `E` below `P`.
Then the inertia degree of `𝓟E` in `L` is `1`: the residue extension of `P` over `𝓟E` is
trivial. -/
theorem inertiaDegIn_eq_one (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟E B = 1 := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P E 𝓞E 𝓟E hp
  have : p.IsPrime := over_def P p ▸ Ideal.IsPrime.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have H := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟E B (inertia Gal(L/K) P)
  rw [primesOver_eq_singleton K L P E 𝓞E 𝓟E, Set.ncard_singleton, one_mul,
    ramificationIdxIn_eq A K L P E 𝓞E 𝓟E hp, card_inertia_eq_ramificationIdxIn p P] at H
  exact (mul_right_eq_self₀.mp H).resolve_right (ramificationIdxIn_ne_zero Gal(L/K))

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K` and let `𝓟E` be the prime of `E` below `P`.
Then `𝓟E` is unramified over `p`. -/
theorem ramificationIdx_eq_one (hp : p ≠ ⊥) :
    𝓟E.ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P E 𝓞E 𝓟E hp
  have := ramificationIdx_tower (R := A) 𝓟E P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟E P (inertia Gal(L/K) P),
    ramificationIdxIn_eq A K L P E 𝓞E 𝓟E hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    right_eq_mul₀ <| (ramificationIdx_pos P A).ne'] at this

include K L E P in
/-- Let `E` be the inertia field of `P` in `L/K` and let `𝓟E` be the prime of `E` below `P`.
Then the inertia degree of `𝓟E` over `p` is the inertia degree of `p` in `L`: the whole residue
extension of `P` over `p` is already the residue extension of `𝓟E`. -/
theorem inertiaDeg_eq_inertiaDegIn (hp : p ≠ ⊥) :
    𝓟E.inertiaDeg A = p.inertiaDegIn B := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P E 𝓞E 𝓟E hp
  have := inertiaDeg_tower (R := A) 𝓟E P
  rw [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ← inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P),
    inertiaDegIn_eq_one A K L P E 𝓞E 𝓟E hp, mul_one] at this
  exact this.symm

end IsInertiaField

end TauCeti.RamificationInertia
