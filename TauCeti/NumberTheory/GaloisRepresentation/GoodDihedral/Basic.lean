/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.MaxPrimeFac
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Good-dihedral primes

Let `ρ : G_ℚ → GL₂(K)` be a residual representation of characteristic `p` and conductor `N`.
Khare and Wintenberger call a prime `q ≠ p` *good-dihedral* for `ρ` if

1. the restriction of `ρ` to the inertia group `I_q` is conjugate to `diag(ψ, ψ^q)` for a
   character `ψ` of `I_q` whose order is a positive power `t^a` of a prime `t` with `t ∣ q + 1`
   and `t > max(Q(N/q²), 5, p)`; and
2. `q ≡ 1 (mod 8)` and `q ≡ 1 (mod s)` for every prime `s ≤ max(Q(N/q²), p)`,

where `Q(n)` is the greatest prime factor `Nat.maxPrimeFac n` (with `Q(1) = 1`). The
representation is *locally good-dihedral* if such a prime exists. Since `t ∣ q + 1` and `t > 2`,
`t` does not divide `q - 1`, so `ψ` has niveau two and `ψ^q ≠ ψ`. Khare and Wintenberger
(Lemma 6.3) show that a locally good-dihedral residual Galois representation has non-solvable
image with projective image other than `A₅`; that lemma is not proved here.

The predicates here are algebraic: they take a matrix representation `ρ : G →* GL (Fin 2) K` of
an arbitrary group, a family `ι q : I q →* G` of inertia homomorphisms, the characteristic `p`
and the conductor `N` as parameters. For a residual Galois representation, `p` is the
characteristic of `K`, `N` its Artin conductor away from `p`, and `ι q` the inclusion of the
inertia group at a chosen prime above `q`.

## Main definitions

* `MonoidHom.IsGoodDihedralAt ρ ι p N q`: `q` is a good-dihedral prime for `ρ`.
* `MonoidHom.IsLocallyGoodDihedral ρ ι p N`: some prime is good-dihedral for `ρ`.

## Main statements

* `MonoidHom.IsGoodDihedralAt.mod_eq_one_of_prime_le`,
  `MonoidHom.IsGoodDihedralAt.mod_eq_one`: the congruence conditions, including at the upper
  end `s = p`.
* `MonoidHom.IsGoodDihedralAt.exists_pow_ne_self`: the two inertia characters `ψ` and `ψ^q` are
  distinct.
* `MonoidHom.isGoodDihedralAt_conj_iff`, `MonoidHom.isLocallyGoodDihedral_conj_iff`: both
  predicates are invariant under conjugation by `GL₂(K)`.
* `MonoidHom.not_isGoodDihedralAt_of_forall_eq_one`,
  `MonoidHom.not_isLocallyGoodDihedral_of_forall_eq_one`: a representation trivial on inertia
  is not good-dihedral.

## References

* C. Khare and J.-P. Wintenberger, *Serre's modularity conjecture (I)*, Invent. Math. 178
  (2009), Definition 2.1 and Lemma 6.3.
-/

public section

open Matrix

namespace MonoidHom

variable {G K : Type*} [Group G] [CommSemiring K] {I : ℕ → Type*} [∀ q, Group (I q)]
  {ρ : G →* GL (Fin 2) K} {ι : ∀ q, I q →* G} {p N q : ℕ}

/-- The prime `q` is **good-dihedral** for the representation `ρ : G →* GL₂(K)`, with respect
to the inertia homomorphisms `ι`, the characteristic `p` and the conductor `N` (Khare and
Wintenberger, Definition 2.1): `q` is a prime different from `p`; the restriction of `ρ` along
`ι q` is conjugate to `diag(ψ, ψ^q)` for a character `ψ` of exact order `t^a`, where `a > 0` and
`t` is a prime dividing `q + 1` with `t > max(Q(N/q²), 5, p)`; and `q ≡ 1` modulo `8` and
modulo every prime `s ≤ max(Q(N/q²), p)`. Here `Q` is `Nat.maxPrimeFac`. The bound `t > 5`
makes `t` odd. -/
structure IsGoodDihedralAt (ρ : G →* GL (Fin 2) K) (ι : ∀ q, I q →* G) (p N q : ℕ) : Prop where
  /-- A good-dihedral prime is prime. -/
  prime : q.Prime
  /-- A good-dihedral prime differs from the characteristic. -/
  ne : q ≠ p
  /-- On inertia, `ρ` is conjugate to `diag(ψ, ψ^q)` for a character `ψ` of exact order `t^a`,
  with `a > 0` and `t` a prime dividing `q + 1` that exceeds `max(Q(N/q²), 5, p)`. -/
  inertia : ∃ t a : ℕ, ∃ ψ : I q →* Kˣ, t.Prime ∧ t ∣ q + 1 ∧
    max (max (N / q ^ 2).maxPrimeFac 5) p < t ∧ 0 < a ∧ orderOf ψ = t ^ a ∧
    ∃ B : GL (Fin 2) K, ∀ x, ((B⁻¹ * ρ (ι q x) * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      diagonal ![(ψ x : K), (ψ x : K) ^ q]
  /-- A good-dihedral prime is congruent to `1` modulo `8`. -/
  mod_eight_eq_one : q % 8 = 1
  /-- A good-dihedral prime is congruent to `1` modulo every prime `s ≤ max(Q(N/q²), p)`. -/
  mod_eq_one_of_prime_le : ∀ s : ℕ, s.Prime → s ≤ max (N / q ^ 2).maxPrimeFac p → q % s = 1

/-- The representation `ρ` is **locally good-dihedral** (with respect to the inertia
homomorphisms `ι`, the characteristic `p` and the conductor `N`) if some prime `q` is
good-dihedral for it. -/
def IsLocallyGoodDihedral (ρ : G →* GL (Fin 2) K) (ι : ∀ q, I q →* G) (p N : ℕ) : Prop :=
  ∃ q, ρ.IsGoodDihedralAt ι p N q

/-- The defining condition of `MonoidHom.IsLocallyGoodDihedral`. -/
theorem isLocallyGoodDihedral_iff :
    ρ.IsLocallyGoodDihedral ι p N ↔ ∃ q, ρ.IsGoodDihedralAt ι p N q :=
  Iff.rfl

/-- A good-dihedral prime makes the representation locally good-dihedral. -/
theorem IsGoodDihedralAt.isLocallyGoodDihedral (h : ρ.IsGoodDihedralAt ι p N q) :
    ρ.IsLocallyGoodDihedral ι p N :=
  ⟨q, h⟩

/-- A locally good-dihedral representation has a good-dihedral prime. -/
theorem IsLocallyGoodDihedral.exists_isGoodDihedralAt (h : ρ.IsLocallyGoodDihedral ι p N) :
    ∃ q, ρ.IsGoodDihedralAt ι p N q :=
  h

namespace IsGoodDihedralAt

/-- A good-dihedral prime is congruent to `1` modulo the characteristic `p` when `p` is prime:
the congruence conditions include the upper end `s = p` of their range. -/
theorem mod_eq_one (h : ρ.IsGoodDihedralAt ι p N q) (hp : p.Prime) : q % p = 1 :=
  h.mod_eq_one_of_prime_le p hp (le_max_right _ _)

/-- A good-dihedral prime is congruent to `1` modulo `Q(N/q²)` when this number is prime, that
is, when `N/q² > 1`. -/
theorem mod_maxPrimeFac_eq_one (h : ρ.IsGoodDihedralAt ι p N q)
    (hN : (N / q ^ 2).maxPrimeFac.Prime) : q % (N / q ^ 2).maxPrimeFac = 1 :=
  h.mod_eq_one_of_prime_le _ hN (le_max_left _ _)

/-- At a good-dihedral prime `q`, the two characters `ψ` and `ψ^q` by which inertia acts are
distinct: the order `t^a` of `ψ` does not divide `q - 1`, because the prime `t > 2` divides
`q + 1`. -/
theorem exists_pow_ne_self (h : ρ.IsGoodDihedralAt ι p N q) :
    ∃ ψ : I q →* Kˣ, ψ ^ q ≠ ψ ∧ ∃ B : GL (Fin 2) K, ∀ x,
      ((B⁻¹ * ρ (ι q x) * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        diagonal ![(ψ x : K), (ψ x : K) ^ q] := by
  obtain ⟨t, a, ψ, -, htq, hlt, ha, hψ, hB⟩ := h.inertia
  refine ⟨ψ, fun hψq => ?_, hB⟩
  have hq := h.prime.one_le
  have h5 : 5 < t := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hlt
  -- `ψ ^ q = ψ ^ 1`, so `t ∣ t ^ a ∣ q - 1`; with `t ∣ q + 1` this gives `t ∣ 2`.
  have hdvd : t ∣ q - 1 := (dvd_pow_self t ha.ne').trans <| hψ ▸ (Nat.modEq_iff_dvd' hq).mp
    ((pow_eq_pow_iff_modEq (x := ψ) (m := 1)).mp (by rwa [pow_one])).symm
  have h2 : t ∣ 2 := by
    have := Nat.dvd_sub htq hdvd
    rwa [show q + 1 - (q - 1) = 2 by omega] at this
  have := Nat.le_of_dvd two_pos h2
  omega

end IsGoodDihedralAt

/-- Good-dihedrality transports along conjugation of the representation by `B ∈ GL₂(K)`. -/
theorem IsGoodDihedralAt.conj (h : ρ.IsGoodDihedralAt ι p N q) (B : GL (Fin 2) K) :
    ((MulAut.conj B : GL (Fin 2) K →* GL (Fin 2) K).comp ρ).IsGoodDihedralAt ι p N q := by
  obtain ⟨t, a, ψ, ht, htq, hlt, ha, hψ, B', hB'⟩ := h.inertia
  refine { h with inertia := ⟨t, a, ψ, ht, htq, hlt, ha, hψ, B * B', fun x => ?_⟩ }
  rw [← hB' x]
  congr 1
  simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass, MulAut.conj_apply]
  group

/-- **Good-dihedrality is invariant under conjugation** of the representation by
`B ∈ GL₂(K)`. -/
@[simp]
theorem isGoodDihedralAt_conj_iff (B : GL (Fin 2) K) :
    ((MulAut.conj B : GL (Fin 2) K →* GL (Fin 2) K).comp ρ).IsGoodDihedralAt ι p N q ↔
      ρ.IsGoodDihedralAt ι p N q := by
  refine ⟨fun h => ?_, fun h => h.conj B⟩
  have hρ : (MulAut.conj B⁻¹ : GL (Fin 2) K →* GL (Fin 2) K).comp
      ((MulAut.conj B : GL (Fin 2) K →* GL (Fin 2) K).comp ρ) = ρ := by
    ext1 x
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [hρ] using h.conj B⁻¹

/-- **Local good-dihedrality is invariant under conjugation** of the representation by
`B ∈ GL₂(K)`. -/
@[simp]
theorem isLocallyGoodDihedral_conj_iff (B : GL (Fin 2) K) :
    ((MulAut.conj B : GL (Fin 2) K →* GL (Fin 2) K).comp ρ).IsLocallyGoodDihedral ι p N ↔
      ρ.IsLocallyGoodDihedral ι p N := by
  simp only [isLocallyGoodDihedral_iff, isGoodDihedralAt_conj_iff]

/-- A representation that is trivial on the inertia at `q` is not good-dihedral at `q`: the
inertia character `ψ` would be trivial, but it has order `t^a` with `t` prime and `a > 0`. -/
theorem not_isGoodDihedralAt_of_forall_eq_one (hρ : ∀ x, ρ (ι q x) = 1) :
    ¬ ρ.IsGoodDihedralAt ι p N q := by
  intro h
  obtain ⟨t, a, ψ, ht, -, -, ha, hψ, B, hB⟩ := h.inertia
  have hψ1 : ψ = 1 := by
    ext x
    have := congrFun₂ (hB x) 0 0
    simpa [hρ] using this.symm
  rw [hψ1, orderOf_one] at hψ
  exact (Nat.one_lt_pow ha.ne' ht.one_lt).ne hψ

/-- A representation that is trivial on every inertia group is not locally good-dihedral. -/
theorem not_isLocallyGoodDihedral_of_forall_eq_one (hρ : ∀ q x, ρ (ι q x) = 1) :
    ¬ ρ.IsLocallyGoodDihedral ι p N :=
  fun ⟨q, h⟩ => not_isGoodDihedralAt_of_forall_eq_one (hρ q) h

end MonoidHom
